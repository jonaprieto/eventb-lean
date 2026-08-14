/-
Kernel-facing translation for resolved Event-B formulas.

The parser and POG remain syntax-level. This module is the first checked boundary: a
caller supplies Lean denotations for the visible model symbols, and translation returns
Lean `Expr`s whose types are checked against the inferred Event-B types. Missing
denotations and unsupported constructs are errors, never opaque constants.
-/

import Lean
import EventB.Embedding
import EventB.Typing.Infer

namespace EventB.Embedding

open Lean Meta
open EventB.Formula EventB.Typing

structure KernelSignature where
  carriers : List (String × Expr) := []

structure KernelBinding where
  name : String
  ty : Ty
  value : Expr

structure KernelFunction where
  name : String
  argument : Ty
  result : Ty
  value : Expr

structure KernelPredicate where
  name : String
  argument : Ty
  value : Expr

structure KernelContext where
  theory : Theory.Env := Theory.empty
  roots : List String := []
  signature : KernelSignature := {}
  bindings : List KernelBinding := []
  functions : List KernelFunction := []
  predicates : List KernelPredicate := []

private def semanticValueHash (value : Expr) : String := toString value.hash

def KernelContext.semanticFingerprint (context : KernelContext) : String :=
  String.intercalate "\n"
    ["roots=" ++ String.intercalate "," context.roots
    , "carriers=" ++ String.intercalate ";" (context.signature.carriers.map
        fun (name, value) => name ++ ":" ++ semanticValueHash value)
    , "bindings=" ++ String.intercalate ";" (context.bindings.map
        fun binding => binding.name ++ ":" ++ binding.ty.print ++ ":" ++
          semanticValueHash binding.value)
    , "functions=" ++ String.intercalate ";" (context.functions.map
        fun function => function.name ++ ":" ++ function.argument.print ++ "->" ++
          function.result.print ++ ":" ++ semanticValueHash function.value)
    , "predicates=" ++ String.intercalate ";" (context.predicates.map
        fun predicate => predicate.name ++ ":" ++ predicate.argument.print ++ ":" ++
          semanticValueHash predicate.value)]

structure KernelTerm where
  ty : Ty
  value : Expr

private def propType : Expr := mkSort .zero

private def KernelContext.lookup (context : KernelContext) (name : String) :
    Option KernelBinding := context.bindings.find? (·.name == name)

private def KernelContext.lookupFunction (context : KernelContext) (name : String) :
    Option KernelFunction := context.functions.find? (·.name == name)

private def KernelContext.lookupPredicate (context : KernelContext) (name : String) :
    Option KernelPredicate := context.predicates.find? (·.name == name)

private def KernelSignature.carrier? (signature : KernelSignature) (name : String) :
    Option Expr := signature.carriers.find? (·.1 == name) |>.map (·.2)

def leanType (context : KernelContext) : Ty → MetaM Expr
  | .given name =>
      match context.signature.carrier? name with
      | some type => pure type
      | none => throwError s!"no Lean type is registered for carrier `{name}`"
  | .int => pure (mkConst ``Int)
  | .bool => pure (mkConst ``Bool)
  | .pow type => do
      mkArrow (← leanType context type) propType
  | .prod left right => do
      mkAppM ``Prod #[← leanType context left, ← leanType context right]
  | .mvar index => throwError s!"unresolved Event-B type metavariable `?{index}`"

private abbrev typeExpr := leanType

private def checked (context : KernelContext) (ty : Ty) (value : Expr) : MetaM KernelTerm := do
  let expected ← leanType context ty
  let actual ← inferType value
  unless ← isDefEq actual expected do
    throwError s!"translated term has type {actual}, expected {expected} for {ty.print}"
  pure { ty, value }

private def boolType : Expr := mkConst (Name.mkSimple "Bool")

private def trueProp : Expr := mkConst (Name.mkSimple "True")

/-- Event-B exponentiation is only defined for non-negative exponents. The embedding is
totalized outside that domain; POG emits `0 ≤ exponent` as the corresponding WD premise. -/
private def eventBPow (base exponent : Int) : Int :=
  if 0 ≤ exponent then Int.pow base exponent.toNat else 0

private def mkAnd (left right : Expr) : MetaM Expr := mkAppM ``And #[left, right]
private def mkOr (left right : Expr) : MetaM Expr := mkAppM ``Or #[left, right]
private def mkImp (left right : Expr) : MetaM Expr := mkArrow left right
private def mkNot (value : Expr) : MetaM Expr := mkAppM ``Not #[value]
private def mkEq (left right : Expr) : MetaM Expr := mkAppM ``Eq #[left, right]

private def mkPair (left right : Expr) : MetaM Expr := mkAppM ``Prod.mk #[left, right]

private def mkDisjunction : List Expr → MetaM Expr
  | [] => pure (mkConst ``False)
  | value :: values => values.foldlM mkOr value

private def mkSetExtension (type : Expr) (values : List Expr) : MetaM Expr := do
  withLocalDeclD `x type fun x => do
    let equalities ← values.mapM (mkEq x)
    mkLambdaFVars #[x] (← mkDisjunction equalities)

private def mkExistsAt (type : Expr) (body : Expr → MetaM Expr) : MetaM Expr := do
  withLocalDeclD `x type fun x => do
    let predicate ← mkLambdaFVars #[x] (← body x)
    mkAppM ``Exists #[predicate]

private def mkUnionSet (elementType setOfSets : Expr) : MetaM Expr := do
  let setType ← mkArrow elementType propType
  withLocalDeclD `x elementType fun x => do
    let existsExpr ← mkExistsAt setType fun subset => do
      mkAnd (mkApp setOfSets subset) (mkApp subset x)
    mkLambdaFVars #[x] existsExpr

private def mkIntersectionSet (elementType setOfSets : Expr) : MetaM Expr := do
  let setType ← mkArrow elementType propType
  withLocalDeclD `x elementType fun x => do
    withLocalDeclD `subset setType fun subset => do
      let implication ← mkImp (mkApp setOfSets subset) (mkApp subset x)
      let universal ← mkForallFVars #[subset] implication
      mkLambdaFVars #[x] universal

private def mkUniversalSet (type : Expr) : MetaM Expr := do
  withLocalDeclD `x type fun x => mkLambdaFVars #[x] trueProp

private def mkIntSet (positive : Bool) : MetaM Expr := do
  withLocalDeclD `x (mkConst ``Int) fun x => do
    let zero := mkApp (mkConst ``Int.ofNat) (mkNatLit 0)
    let condition := if positive then
      mkApp2 (mkConst ``Int.lt) zero x
    else
      mkApp2 (mkConst ``Int.le) zero x
    mkLambdaFVars #[x] condition

private def lookupExpr (context : KernelContext) (name : String) : MetaM KernelTerm := do
  match context.lookup name with
  | some binding =>
      if let some expected := Theory.typeIn? context.theory context.roots name then
        unless expected == binding.ty do
          throwError s!"semantic binding `{name}` has Event-B type {binding.ty.print}, " ++
            s!"but the visible theory declares {expected.print}"
      checked context binding.ty binding.value
  | none =>
      if let some (_, _, _) := Theory.constructor? context.theory context.roots name then
        throwError s!"theory constructor `{name}` has no Lean semantic binding"
      else if let some (_, declaration) :=
          Theory.declaration? context.theory context.roots name then
        throwError s!"theory declaration `{declaration.name}` has no Lean semantic binding"
      else if Theory.isIdentifierIn context.theory context.roots name then
        throwError s!"Event-B symbol `{name}` has no Lean semantic binding"
      else
        throwError s!"unknown Event-B identifier `{name}`"

private def validateFunction (context : KernelContext) (function : KernelFunction) :
    MetaM Unit := do
  if let some expected := Theory.typeIn? context.theory context.roots function.name then
    let declared := .pow (.prod function.argument function.result)
    unless expected == declared do
      throwError s!"semantic function `{function.name}` has Event-B type {declared.print}, " ++
        s!"but the visible theory declares {expected.print}"
  let argumentType ← leanType context function.argument
  let resultType ← leanType context function.result
  let actual ← inferType function.value
  unless ← isDefEq actual (← mkArrow argumentType resultType) do
    throwError s!"semantic function `{function.name}` has Lean type {actual}, " ++
      s!"expected {argumentType} → {resultType}"

private def validatePredicate (context : KernelContext) (predicate : KernelPredicate) :
    MetaM Unit := do
  if let some expected := Theory.typeIn? context.theory context.roots predicate.name then
    let declared := .pow (.prod predicate.argument .bool)
    unless expected == declared do
      throwError s!"semantic predicate `{predicate.name}` has Event-B type " ++
        s!"{declared.print}, but the visible theory declares {expected.print}"
  let argumentType ← leanType context predicate.argument
  let actual ← inferType predicate.value
  unless ← isDefEq actual (← mkArrow argumentType propType) do
    throwError s!"semantic predicate `{predicate.name}` has Lean type {actual}, " ++
      s!"expected {argumentType} → Prop"

private def asSet (term : KernelTerm) : MetaM (Ty × Expr) :=
  match term.ty with
  | .pow type => pure (type, term.value)
  | type => throwError s!"expected a set, found {type.print}"

private def sameType (left right : Ty) : MetaM Unit := do
  unless left == right do
    throwError s!"incompatible translated types {left.print} and {right.print}"

private def eventBType : Formula.Term → MetaM Ty
  | .id "ℤ" | .id "ℕ" | .id "ℕ1" => pure .int
  | .id "BOOL" => pure .bool
  | .id name => pure (.given name)
  | .pre "ℙ" type | .pre "ℙ1" type => return .pow (← eventBType type)
  | .bin "×" left right => return .prod (← eventBType left) (← eventBType right)
  | term => throwError s!"unsupported binder type `{Formula.print term}`"

private def withPattern {α : Type} (context : KernelContext) (pattern : Formula.Term)
    (expected : Option Ty)
    (body : KernelContext → List Expr → Expr → Ty → MetaM α) : MetaM α := do
  match pattern with
  | .id name =>
      let ty ← match expected with
        | some ty => pure ty
        | none => match context.lookup name with
          | some binding => pure binding.ty
          | none => throwError s!"binder `{name}` needs an explicit type"
      withLocalDeclD (Name.mkSimple name) (← leanType context ty) fun localVar => do
        let context := { context with bindings :=
          { name, ty, value := localVar } :: context.bindings }
        body context [localVar] localVar ty
  | .bin "⦂" (.id name) typeTerm => do
      let ty ← eventBType typeTerm
      match expected with
      | some expected => let _ ← sameType ty expected
      | none => pure ()
      withPattern context (.id name) (some ty) body
  | .bin "↦" left right => do
      let (leftExpected, rightExpected) ← match expected with
        | some (.prod left right) => pure (some left, some right)
        | some expected => throwError s!"maplet binder needs a product, found {expected.print}"
        | none => pure (none, none)
      withPattern context left leftExpected fun context leftLocals leftValue leftType =>
        withPattern context right rightExpected fun context rightLocals rightValue rightType => do
          let value ← mkPair leftValue rightValue
          body context (leftLocals ++ rightLocals) value (.prod leftType rightType)
  | .bin "," left right =>
      withPattern context left none fun context leftLocals leftValue leftType =>
        withPattern context right none fun context rightLocals rightValue rightType => do
          let value ← mkPair leftValue rightValue
          body context (leftLocals ++ rightLocals) value (.prod leftType rightType)
  | term => throwError s!"unsupported binder pattern `{Formula.print term}`"

private def mkExistsLocals : List Expr → Expr → MetaM Expr
  | [], body => pure body
  | localVar :: locals, body => do
      let body ← mkExistsLocals locals body
      mkAppM ``Exists #[← mkLambdaFVars #[localVar] body]

private def mkForallLocals : List Expr → Expr → MetaM Expr
  | [], body => pure body
  | localVar :: locals, body => do
      let body ← mkForallLocals locals body
      mkForallFVars #[localVar] body

private def isLambda : Formula.Term → Bool
  | .bind "λ" _ _ => true
  | _ => false

private def elementType? : Option Ty → Option Ty
  | some (.pow type) => some type
  | _ => none

private def relationTypes (term : KernelTerm) : MetaM (Ty × Ty) :=
  match term.ty with
  | .pow (.prod left right) => pure (left, right)
  | type => throwError s!"expected a relation, found {type.print}"

private def project (which : Name) (pair : Expr) : MetaM Expr :=
  mkAppM which #[pair]

private def mkSetBinary (op : String) (type left right : Expr) : MetaM Expr := do
  withLocalDeclD `x type fun x => do
    let a := mkApp left x
    let b := mkApp right x
    let body ← match op with
      | "∪" => mkOr a b
      | "∩" => mkAnd a b
      | "∖" => mkAnd a (← mkNot b)
      | _ => throwError s!"unsupported set operator `{op}`"
    mkLambdaFVars #[x] body

private def mkSubset (type left right : Expr) : MetaM Expr := do
  withLocalDeclD `x type fun x => do
    let premise := mkApp left x
    let conclusion := mkApp right x
    mkForallFVars #[x] (← mkImp premise conclusion)

private def mkProductSet (leftType rightType left right : Expr) : MetaM Expr := do
  let pairType ← mkAppM ``Prod #[leftType, rightType]
  withLocalDeclD `pair pairType fun pair => do
    let first ← project ``Prod.fst pair
    let second ← project ``Prod.snd pair
    let body ← mkAnd (mkApp left first) (mkApp right second)
    mkLambdaFVars #[pair] body

private def mkRelationSpace (leftType rightType left right : Expr) : MetaM Expr := do
  let pairType ← mkAppM ``Prod #[leftType, rightType]
  let relationType ← mkArrow pairType propType
  withLocalDeclD `relation relationType fun relation => do
    withLocalDeclD `pair pairType fun pair => do
      let first ← project ``Prod.fst pair
      let second ← project ``Prod.snd pair
      let allowed ← mkAnd (mkApp left first) (mkApp right second)
      let relationAt := mkApp relation pair
      let implication ← mkImp relationAt allowed
      let subset ← mkForallFVars #[pair] implication
      mkLambdaFVars #[relation] subset

private def mkRelationConstraint (kind : String)
    (leftType rightType leftSet rightSet relation : Expr) :
    MetaM Expr := do
  let relationAt (left right : Expr) : MetaM Expr := do
    pure (mkApp relation (← mkPair left right))
  match kind with
  | "functional" =>
      withLocalDeclD `x leftType fun x => do
        withLocalDeclD `y rightType fun y => do
          withLocalDeclD `z rightType fun z => do
            let both ← mkAnd (← relationAt x y) (← relationAt x z)
            mkForallFVars #[x, y, z] (← mkImp both (← mkEq y z))
  | "injective" =>
      withLocalDeclD `x leftType fun x => do
        withLocalDeclD `y leftType fun y => do
          withLocalDeclD `z rightType fun z => do
            let both ← mkAnd (← relationAt x z) (← relationAt y z)
            mkForallFVars #[x, y, z] (← mkImp both (← mkEq x y))
  | "total" =>
      withLocalDeclD `x leftType fun x => do
        let existsExpr ← mkExistsAt rightType fun y => relationAt x y
        mkForallFVars #[x] (← mkImp (mkApp leftSet x) existsExpr)
  | "surjective" =>
      withLocalDeclD `y rightType fun y => do
        let existsExpr ← mkExistsAt leftType fun x => relationAt x y
        mkForallFVars #[y] (← mkImp (mkApp rightSet y) existsExpr)
  | _ => throwError s!"unknown relation constraint `{kind}`"

private def relationConstraints : String → List String
  | "↔" => []
  | "" => ["total"]
  | "" => ["surjective"]
  | "" => ["total", "surjective"]
  | "⇸" => ["functional"]
  | "→" => ["functional", "total"]
  | "⤔" => ["functional", "injective"]
  | "↣" => ["functional", "injective", "total"]
  | "⤀" => ["functional", "surjective"]
  | "↠" => ["functional", "surjective", "total"]
  | "⤖" => ["functional", "injective", "surjective", "total"]
  | _ => []

private def mkRelationArrow (op : String) (leftType rightType left right : Expr) :
    MetaM Expr := do
  let pairType ← mkAppM ``Prod #[leftType, rightType]
  let relationType ← mkArrow pairType propType
  let base ← mkRelationSpace leftType rightType left right
  withLocalDeclD `relation relationType fun relation => do
    let properties := (mkApp base relation) ::
      (← (relationConstraints op).mapM
        (mkRelationConstraint · leftType rightType left right relation))
    let body ← properties.tail.foldlM (init := properties.head!) fun body property =>
      mkAnd body property
    mkLambdaFVars #[relation] body

private def mkPowerSet (type set : Expr) (positive : Bool) : MetaM Expr := do
  let setType ← mkArrow type propType
  withLocalDeclD `subset setType fun subset => do
    withLocalDeclD `x type fun x => do
      let contained := mkApp subset x
      let allowed := mkApp set x
      let implication ← mkImp contained allowed
      let inclusion ← mkForallFVars #[x] implication
      let body ← if positive then
        let existsExpr ← mkExistsAt type fun x => pure (mkApp subset x)
        mkAnd existsExpr inclusion
      else pure inclusion
      mkLambdaFVars #[subset] body

private def mkImage (leftType rightType relation set : Expr) : MetaM Expr := do
  withLocalDeclD `y rightType fun y => do
    let existsExpr ← mkExistsAt leftType fun x => do
      let pair ← mkPair x y
      let related := mkApp relation pair
      let selected := mkApp set x
      mkAnd selected related
    mkLambdaFVars #[y] existsExpr

private def mkInverse (leftType rightType relation : Expr) : MetaM Expr := do
  let sourcePairType ← mkAppM ``Prod #[rightType, leftType]
  withLocalDeclD `pair sourcePairType fun pair => do
    let first ← project ``Prod.fst pair
    let second ← project ``Prod.snd pair
    let originalPair ← mkPair second first
    mkLambdaFVars #[pair] (mkApp relation originalPair)

private def mkProjectionSet (leftType rightType relation : Expr) (first : Bool) :
    MetaM Expr := do
  withLocalDeclD `value (if first then leftType else rightType) fun value => do
    let existsExpr ← if first then
      mkExistsAt rightType fun other => do
        let pair ← mkPair value other
        pure (mkApp relation pair)
    else
      mkExistsAt leftType fun other => do
        let pair ← mkPair other value
        pure (mkApp relation pair)
    mkLambdaFVars #[value] existsExpr

private def mkIdentity (type set : Expr) : MetaM Expr := do
  let pairType ← mkAppM ``Prod #[type, type]
  withLocalDeclD `pair pairType fun pair => do
    let first ← project ``Prod.fst pair
    let second ← project ``Prod.snd pair
    let body ← mkAnd (mkApp set first) (← mkEq first second)
    mkLambdaFVars #[pair] body

private def mkRestriction (relationType set relation : Expr) (domain : Bool) : MetaM Expr := do
  withLocalDeclD `pair relationType fun pair => do
    let endpoint ← if domain then project ``Prod.fst pair else project ``Prod.snd pair
    let restricted := mkApp set endpoint
    let body ← mkAnd restricted (mkApp relation pair)
    mkLambdaFVars #[pair] body

private def mkSubtraction (relationType set relation : Expr) (domain : Bool) : MetaM Expr := do
  withLocalDeclD `pair relationType fun pair => do
    let endpoint ← if domain then project ``Prod.fst pair else project ``Prod.snd pair
    let removed := mkApp set endpoint
    let body ← mkAnd (← mkNot removed) (mkApp relation pair)
    mkLambdaFVars #[pair] body

private def mkComposition (leftType middleType rightType left right : Expr) : MetaM Expr := do
  let pairType ← mkAppM ``Prod #[leftType, rightType]
  withLocalDeclD `pair pairType fun pair => do
    let input ← project ``Prod.fst pair
    let output ← project ``Prod.snd pair
    let existsExpr ← mkExistsAt middleType fun middle => do
      let firstPair ← mkPair input middle
      let secondPair ← mkPair middle output
      mkAnd (mkApp left firstPair) (mkApp right secondPair)
    mkLambdaFVars #[pair] existsExpr

private def mkDirectProduct (leftType middleType rightType p q : Expr) : MetaM Expr := do
  let outputType ← mkAppM ``Prod #[middleType, rightType]
  let pairType ← mkAppM ``Prod #[leftType, outputType]
  withLocalDeclD `pair pairType fun pair => do
    let input ← project ``Prod.fst pair
    let output ← project ``Prod.snd pair
    let first ← project ``Prod.fst output
    let second ← project ``Prod.snd output
    let firstPair ← mkPair input first
    let secondPair ← mkPair input second
    let body ← mkAnd (mkApp p firstPair) (mkApp q secondPair)
    mkLambdaFVars #[pair] body

private def mkParallelProduct (leftType middleType rightType output : Expr) (p q : Expr) :
    MetaM Expr := do
  let inputType ← mkAppM ``Prod #[leftType, middleType]
  let outputType' ← mkAppM ``Prod #[rightType, output]
  let pairType ← mkAppM ``Prod #[inputType, outputType']
  withLocalDeclD `pair pairType fun pair => do
    let input ← project ``Prod.fst pair
    let result ← project ``Prod.snd pair
    let leftInput ← project ``Prod.fst input
    let rightInput ← project ``Prod.snd input
    let leftOutput ← project ``Prod.fst result
    let rightOutput ← project ``Prod.snd result
    let leftPair ← mkPair leftInput leftOutput
    let rightPair ← mkPair rightInput rightOutput
    let body ← mkAnd (mkApp p leftPair) (mkApp q rightPair)
    mkLambdaFVars #[pair] body

private def mkOverride (leftType rightType left right : Expr) : MetaM Expr := do
  let pairType ← mkAppM ``Prod #[leftType, rightType]
  withLocalDeclD `pair pairType fun pair => do
    let input ← project ``Prod.fst pair
    let rightAt := mkApp right pair
    let existsExpr ← mkExistsAt rightType fun output => do
      let rightPair ← mkPair input output
      pure (mkApp right rightPair)
    let body ← mkOr rightAt (← mkAnd (mkApp left pair) (← mkNot existsExpr))
    mkLambdaFVars #[pair] body

private def builtinSet (context : KernelContext) (name : String) : MetaM KernelTerm := do
  match name with
  | "BOOL" => checked context (.pow .bool) (← mkUniversalSet boolType)
  | "ℤ" => checked context (.pow .int) (← mkUniversalSet (mkConst ``Int))
  | "ℕ" => checked context (.pow .int) (← mkIntSet false)
  | "ℕ1" => checked context (.pow .int) (← mkIntSet true)
  | _ => lookupExpr context name

mutual

private def termFuelList : List Formula.Term → Nat
  | [] => 0
  | term :: terms => termFuel term + termFuelList terms

private def termFuel : Formula.Term → Nat
  | .id _ | .num _ => 1
  | .bin _ left right => 1 + termFuel left + termFuel right
  | .pre _ value | .post _ value => 1 + termFuel value
  | .app function argument | .img function argument =>
      1 + termFuel function + termFuel argument
  | .set values => 1 + termFuelList values
  | .bind _ pattern body => 1 + termFuel pattern + termFuel body

end

mutual

private def translateExprList : Nat → KernelContext → List Formula.Term →
    MetaM (List KernelTerm)
  | 0, _, _ => throwError "formula translation recursion limit reached"
  | _ + 1, _, [] => pure []
  | fuel + 1, context, term :: terms => do
      let value ← translateExpr fuel context term
      let rest ← translateExprList fuel context terms
      pure (value :: rest)

private def translateComprehension : Nat → KernelContext → Formula.Term → Formula.Term →
    Option Ty → MetaM KernelTerm
  | fuel, context, pattern, body, expected => do
      withPattern context pattern none fun bodyContext locals patternValue patternType => do
        let (predicateTerm, valueTerm) := match body with
          | .bin "∣" predicate value => (predicate, some value)
          | _ => (.id "⊤", none)
        let predicate ← translatePred fuel bodyContext predicateTerm
        let value ← match valueTerm with
          | some value => translateExprExpected fuel bodyContext (elementType? expected) value
          | none => pure { ty := patternType, value := patternValue }
        let resultType ← match expected with
          | some (.pow type) => do let _ ← sameType type value.ty; pure type
          | some type => throwError s!"set comprehension expects a set, found {type.print}"
          | none => pure value.ty
        withLocalDeclD `value (← leanType context resultType) fun result => do
          let equality ← mkEq result value.value
          let body ← mkExistsLocals locals (← mkAnd predicate equality)
          let set ← mkLambdaFVars #[result] body
          checked context (.pow resultType) set

private def translateLambda : Nat → KernelContext → Formula.Term → Formula.Term → Option Ty →
    MetaM KernelTerm
  | fuel, context, pattern, body, expected => do
      let (inputExpected, outputExpected) ← match expected with
        | some (.pow (.prod input output)) => pure (some input, some output)
        | some type => throwError s!"lambda expects a relation type, found {type.print}"
        | none => pure (none, none)
      withPattern context pattern inputExpected
          fun bodyContext locals patternValue patternType => do
        let relationBody := match body with
          | .bin "∣" _ _ => true
          | _ => false
        let (predicate, value, relationType) ← match body with
          | .bin "∣" predicateTerm valueTerm => do
              let predicate ← translatePred fuel bodyContext predicateTerm
              let value ← translateExprExpected fuel bodyContext outputExpected valueTerm
              let relationType := .prod patternType value.ty
              pure (predicate, value, relationType)
          | _ => do
              let elementExpected := expected.bind fun type => match type with
                | .pow element => some element
                | _ => none
              let value ← translateExprExpected fuel bodyContext elementExpected body
              pure (mkConst ``True, value, value.ty)
        match expected with
        | some (.pow type) => let _ ← sameType type relationType
        | some type => throwError s!"lambda expects a relation type, found {type.print}"
        | none => pure ()
        let relationLeanType ← leanType context relationType
        withLocalDeclD `pair relationLeanType fun pair => do
          let pairValue ← if relationBody then
            mkPair patternValue value.value
          else pure value.value
          let equality ← mkEq pair pairValue
          let body ← mkExistsLocals locals (← mkAnd predicate equality)
          let relation ← mkLambdaFVars #[pair] body
          checked context (.pow relationType) relation

private def translateEquality : Nat → KernelContext → Formula.Term → Formula.Term → Bool →
    MetaM Expr
  | fuel, context, leftTerm, rightTerm, negated => do
      let (left, right) ← if leftTerm == .set [] || isLambda leftTerm then
        let right ← translateExpr fuel context rightTerm
        let left ← translateExprExpected fuel context (some right.ty) leftTerm
        pure (left, right)
      else
        let left ← translateExpr fuel context leftTerm
        let right ← translateExprExpected fuel context (some left.ty) rightTerm
        pure (left, right)
      let _ ← sameType left.ty right.ty
      let equality ← mkEq left.value right.value
      if negated then mkNot equality else pure equality

private def translateExprExpected : Nat → KernelContext → Option Ty → Formula.Term →
    MetaM KernelTerm
  | 0, _, _, _ => throwError "formula translation recursion limit reached"
  | _ + 1, context, some (.pow type), .set [] => do
      let value ← withLocalDeclD `x (← typeExpr context type) fun x =>
        mkLambdaFVars #[x] (mkConst ``False)
      checked context (.pow type) value
  | fuel + 1, context, expected, .bind "{" pattern body =>
      translateComprehension fuel context pattern body expected
  | fuel + 1, context, expected, .bind "λ" pattern body =>
      translateLambda fuel context pattern body expected
  | fuel + 1, context, _, term => translateExpr fuel context term

private def translateApplicationArgument : Nat → KernelContext → Ty → Formula.Term →
    MetaM KernelTerm
  | 0, _, _, _ => throwError "formula translation recursion limit reached"
  | fuel + 1, context, .prod left right, .bin "," first rest => do
      let first ← translateApplicationArgument fuel context left first
      let rest ← translateApplicationArgument fuel context right rest
      checked context (.prod left right) (← mkPair first.value rest.value)
  | _ + 1, _, expected, .bin "," _ _ =>
      throwError s!"comma-separated application needs product type, found {expected.print}"
  | fuel + 1, context, expected, term =>
      translateExprExpected fuel context (some expected) term

private def translateExpr : Nat → KernelContext → Formula.Term → MetaM KernelTerm
  | 0, _, _ => throwError "formula translation recursion limit reached"
  | _ + 1, context, .num value =>
      checked context .int (mkApp (mkConst ``Int.ofNat) (mkNatLit value))
  | _ + 1, context, .id "TRUE" => checked context .bool (mkConst ``Bool.true)
  | _ + 1, context, .id "FALSE" => checked context .bool (mkConst ``Bool.false)
  | _ + 1, context, .id name => builtinSet context name
  | _ + 1, _, .set [] => throwError "empty set needs an expected element type"
  | fuel + 1, context, .set values => do
      match values with
      | [] => throwError "empty set needs an expected element type"
      | firstTerm :: restTerms =>
          let first ← translateExpr fuel context firstTerm
          let rest ← translateExprList fuel context restTerms
          let values := first :: rest
          for value in rest do
            let _ ← sameType first.ty value.ty
          checked context (.pow first.ty)
            (← mkSetExtension (← typeExpr context first.ty) (values.map (·.value)))
  | fuel + 1, context, .pre "−" value => do
      let value ← translateExpr fuel context value
      let _ ← sameType value.ty .int
      checked context .int (mkApp (mkConst ``Int.neg) value.value)
  | fuel + 1, context, .pre op value => do
      unless op == "ℙ" || op == "ℙ1" || op == "⋃" || op == "⋂" do
        throwError s!"unsupported Event-B prefix operator `{op}`"
      let value ← translateExpr fuel context value
      if op == "ℙ" || op == "ℙ1" then
        let (type, set) ← asSet value
        let result ← mkPowerSet (← typeExpr context type) set (op == "ℙ1")
        checked context (.pow (.pow type)) result
      else
        let (setType, setOfSets) ← asSet value
        match setType with
        | .pow elementType =>
            let result ← if op == "⋃" then
              mkUnionSet (← typeExpr context elementType) setOfSets
            else
              mkIntersectionSet (← typeExpr context elementType) setOfSets
            checked context (.pow elementType) result
        | _ => throwError s!"generalized {op} expects a set of sets"
  | fuel + 1, context, Formula.Term.post op value => do
      unless op == "∼" do
        throwError s!"unsupported Event-B postfix operator `{op}`"
      let value ← translateExpr fuel context value
      let (left, right) ← relationTypes value
      checked context (.pow (.prod right left))
        (← mkInverse (← typeExpr context left) (← typeExpr context right) value.value)
  | fuel + 1, context, .img relation set => do
      let relation ← translateExpr fuel context relation
      let set ← translateExpr fuel context set
      let (left, right) ← relationTypes relation
      let (setType, set) ← asSet set
      let _ ← sameType left setType
      checked context (.pow right) (← mkImage (← typeExpr context left)
        (← typeExpr context right) relation.value set)
  | fuel + 1, context, .app function argument => do
      match function with
      | .id "dom" | .id "prj1" =>
          let relation ← translateExpr fuel context argument
          let (leftType, rightType) ← relationTypes relation
          checked context (.pow leftType)
            (← mkProjectionSet (← typeExpr context leftType)
              (← typeExpr context rightType) relation.value true)
      | .id "ran" | .id "prj2" =>
          let relation ← translateExpr fuel context argument
          let (leftType, rightType) ← relationTypes relation
          checked context (.pow rightType)
            (← mkProjectionSet (← typeExpr context leftType)
              (← typeExpr context rightType) relation.value false)
      | .id "id" =>
          let argument ← translateExpr fuel context argument
          let (type, set) ← asSet argument
          checked context (.pow (.prod type type))
            (← mkIdentity (← typeExpr context type) set)
      | .id "union" | .id "inter" =>
          let argument ← translateExpr fuel context argument
          let (setType, setOfSets) ← asSet argument
          match setType with
          | .pow elementType =>
              let result ← if function == .id "union" then
                mkUnionSet (← typeExpr context elementType) setOfSets
              else
                mkIntersectionSet (← typeExpr context elementType) setOfSets
              checked context (.pow elementType) result
          | _ => throwError "union/inter expects a set of sets"
      | .id "succ" | .id "pred" =>
          let argument ← translateExpr fuel context argument
          let _ ← sameType argument.ty .int
          let one := mkApp (mkConst ``Int.ofNat) (mkNatLit 1)
          let functionName := if function == .id "succ" then ``Int.add else ``Int.sub
          checked context .int (← mkAppM functionName #[argument.value, one])
      | .id "bool" =>
          let predicate ← translatePred fuel context argument
          let decidable := mkApp (mkConst ``Classical.propDecidable) predicate
          let value := mkApp (mkApp (mkConst ``decide) predicate) decidable
          checked context .bool value
      | .id name =>
          match context.lookupFunction name with
          | none =>
              throwError s!"function application `{name}` needs a semantic binding"
          | some semantic =>
              let argument ← translateApplicationArgument fuel context semantic.argument argument
              let _ ← sameType argument.ty semantic.argument
              validateFunction context semantic
              checked context semantic.result (mkApp semantic.value argument.value)
      | _ => throwError "function application needs a semantic function binding"
  | fuel + 1, context, .bind "{" pattern body =>
      translateComprehension fuel context pattern body none
  | _ + 1, _, .bind kind _ _ => throwError s!"binder `{kind}` is not an expression here"
  | fuel + 1, context, .bin "↦" left right => do
      let left ← translateExpr fuel context left
      let right ← translateExpr fuel context right
      checked context (.prod left.ty right.ty) (← mkPair left.value right.value)
  | fuel + 1, context, .bin op left right => do
      match op with
      | "∪" | "∩" | "∖" =>
          let left ← translateExpr fuel context left
          let right ← translateExpr fuel context right
          let (leftType, left) ← asSet left
          let (rightType, right) ← asSet right
          let _ ← sameType leftType rightType
          checked context (.pow leftType)
            (← mkSetBinary op (← typeExpr context leftType) left right)
      | "×" =>
          let left ← translateExpr fuel context left
          let right ← translateExpr fuel context right
          let (leftType, left) ← asSet left
          let (rightType, right) ← asSet right
          checked context (.pow (.prod leftType rightType))
            (← mkProductSet (← typeExpr context leftType) (← typeExpr context rightType)
              left right)
      | "◁" | "▷" | "⩤" | "⩥" =>
          let left ← translateExpr fuel context left
          let right ← translateExpr fuel context right
          if op == "◁" || op == "⩤" then
            let (rightLeft, rightRight) ← relationTypes right
            let (leftType, leftSet) ← asSet left
            let _ ← sameType leftType rightLeft
            let builder := if op == "◁" then mkRestriction else mkSubtraction
            checked context right.ty
              (← builder (← typeExpr context (.prod rightLeft rightRight)) leftSet
                right.value true)
          else
            let (leftType, leftRight) ← relationTypes left
            let (rightType, rightSet) ← asSet right
            let _ ← sameType leftRight rightType
            let builder := if op == "▷" then mkRestriction else mkSubtraction
            checked context left.ty
              (← builder (← typeExpr context (.prod leftType leftRight)) rightSet
                left.value false)
      | "↔" | "" | "" | "" | "⇸" | "→" | "⤔" | "↣" | "⤀" | "↠" | "⤖" =>
          let left ← translateExpr fuel context left
          let right ← translateExpr fuel context right
          let (leftType, left) ← asSet left
          let (rightType, right) ← asSet right
          let relation ← mkRelationArrow op (← typeExpr context leftType)
            (← typeExpr context rightType) left right
          checked context (.pow (.pow (.prod leftType rightType))) relation
      | "+" | "−" | "∗" | "÷" | "mod" | "^" =>
          let left ← translateExpr fuel context left
          let right ← translateExpr fuel context right
          let _ ← sameType left.ty .int
          let _ ← sameType right.ty .int
          let function := match op with
            | "+" => ``Int.add
            | "−" => ``Int.sub
            | "∗" => ``Int.mul
            | "÷" => ``Int.ediv
            | "mod" => ``Int.emod
            | _ => ``Int.add
          let result ← if op == "^" then
            mkAppM ``eventBPow #[left.value, right.value]
          else
            mkAppM function #[left.value, right.value]
          checked context .int result
      | "∘" | ";" =>
          let left ← translateExpr fuel context left
          let right ← translateExpr fuel context right
          let (leftInput, leftOutput) ← relationTypes left
          let (rightInput, rightOutput) ← relationTypes right
          if op == ";" then
            let _ ← sameType leftOutput rightInput
            checked context (.pow (.prod leftInput rightOutput))
              (← mkComposition (← typeExpr context leftInput)
                (← typeExpr context leftOutput) (← typeExpr context rightOutput)
                left.value right.value)
          else
            let _ ← sameType rightOutput leftInput
            checked context (.pow (.prod rightInput leftOutput))
              (← mkComposition (← typeExpr context rightInput)
                (← typeExpr context leftInput) (← typeExpr context leftOutput)
                right.value left.value)
      | "" | "" =>
          let left ← translateExpr fuel context left
          let right ← translateExpr fuel context right
          let (leftInput, leftOutput) ← relationTypes left
          let (rightInput, rightOutput) ← relationTypes right
          let _ ← sameType leftInput rightInput
          let _ ← sameType leftOutput rightOutput
          checked context left.ty
            (← mkOverride (← typeExpr context leftInput) (← typeExpr context leftOutput)
              left.value right.value)
      | "⊗" =>
          let left ← translateExpr fuel context left
          let right ← translateExpr fuel context right
          let (leftInput, leftOutput) ← relationTypes left
          let (rightInput, rightOutput) ← relationTypes right
          let _ ← sameType leftInput rightInput
          checked context (.pow (.prod leftInput (.prod leftOutput rightOutput)))
            (← mkDirectProduct (← typeExpr context leftInput) (← typeExpr context leftOutput)
              (← typeExpr context rightOutput) left.value right.value)
      | "∥" =>
          let left ← translateExpr fuel context left
          let right ← translateExpr fuel context right
          let (leftInput, leftOutput) ← relationTypes left
          let (rightInput, rightOutput) ← relationTypes right
          checked context (.pow (.prod (.prod leftInput rightInput)
            (.prod leftOutput rightOutput)))
            (← mkParallelProduct (← typeExpr context leftInput)
              (← typeExpr context rightInput) (← typeExpr context leftOutput)
              (← typeExpr context rightOutput) left.value right.value)
      | "‥" =>
          let left ← translateExpr fuel context left
          let right ← translateExpr fuel context right
          let _ ← sameType left.ty .int
          let _ ← sameType right.ty .int
          withLocalDeclD `x (mkConst ``Int) fun x => do
            let lower := mkApp2 (mkConst ``Int.le) left.value x
            let upper := mkApp2 (mkConst ``Int.le) x right.value
            checked context (.pow .int) (← mkLambdaFVars #[x] (← mkAnd lower upper))
      | _ => throwError s!"unsupported Event-B expression operator `{op}`"

private def translatePred : Nat → KernelContext → Formula.Term → MetaM Expr
  | 0, _, _ => throwError "formula translation recursion limit reached"
  | _ + 1, _, .id "⊤" => pure (mkConst ``True)
  | _ + 1, _, .id "⊥" => pure (mkConst ``False)
  | fuel + 1, context, .pre "¬" value => do
      mkNot (← translatePred fuel context value)
  | fuel + 1, context, .bin "∧" left right => do
      mkAnd (← translatePred fuel context left) (← translatePred fuel context right)
  | fuel + 1, context, .bin "∨" left right => do
      mkOr (← translatePred fuel context left) (← translatePred fuel context right)
  | fuel + 1, context, .bin "⇒" left right => do
      mkImp (← translatePred fuel context left) (← translatePred fuel context right)
  | fuel + 1, context, .bin "⇔" left right => do
      mkAppM ``Iff #[← translatePred fuel context left, ← translatePred fuel context right]
  | fuel + 1, context, .bin "=" leftTerm rightTerm =>
      translateEquality fuel context leftTerm rightTerm false
  | fuel + 1, context, .bin "≠" leftTerm rightTerm =>
      translateEquality fuel context leftTerm rightTerm true
  | fuel + 1, context, .bin op left right => do
      match op with
      | "<" | "≤" | ">" | "≥" =>
          let left ← translateExpr fuel context left
          let right ← translateExpr fuel context right
          let _ ← sameType left.ty .int
          let _ ← sameType right.ty .int
          let (function, arguments) := match op with
            | "<" => (``Int.lt, #[left.value, right.value])
            | "≤" => (``Int.le, #[left.value, right.value])
            | ">" => (``Int.lt, #[right.value, left.value])
            | "≥" => (``Int.le, #[right.value, left.value])
            | _ => (``Int.lt, #[left.value, right.value])
          mkAppM function arguments
      | "∈" | "∉" =>
          let right ← translateExpr fuel context right
          let (rightType, set) ← asSet right
          let left ← translateExprExpected fuel context (some rightType) left
          let _ ← sameType left.ty rightType
          let membership := mkApp set left.value
          if op == "∈" then pure membership else mkNot membership
      | "⊆" | "⊈" | "⊂" | "⊄" =>
          if left == .set [] then
            let right ← translateExpr fuel context right
            let (rightType, right) ← asSet right
            let left ← translateExprExpected fuel context (some (.pow rightType)) (.set [])
            let (leftType, left) ← asSet left
            let _ ← sameType leftType rightType
            let subset ← mkSubset (← typeExpr context leftType) left right
            if op == "⊆" then pure subset
            else if op == "⊈" then mkNot subset
            else do
              let reverse ← mkSubset (← typeExpr context leftType) right left
              let strict ← mkAnd subset (← mkNot reverse)
              if op == "⊂" then pure strict else mkNot strict
          else
            let left ← translateExpr fuel context left
            let (leftType, left) ← asSet left
            let right ← if right == .set [] then
              translateExprExpected fuel context (some (.pow leftType)) right
            else
              translateExpr fuel context right
            let (rightType, right) ← asSet right
            let _ ← sameType leftType rightType
            let subset ← mkSubset (← typeExpr context leftType) left right
            if op == "⊆" then pure subset
            else if op == "⊈" then mkNot subset
            else do
              let reverse ← mkSubset (← typeExpr context leftType) right left
              let strict ← mkAnd subset (← mkNot reverse)
              if op == "⊂" then pure strict else mkNot strict
      | _ => throwError s!"unsupported Event-B predicate operator `{op}`"
  | fuel + 1, context, .app (.id name) value => do
      match context.lookupPredicate name with
      | none =>
          throwError s!"predicate application `{name}` needs a semantic binding"
      | some semantic =>
          let value ← translateExpr fuel context value
          let _ ← sameType value.ty semantic.argument
          validatePredicate context semantic
          let result := mkApp semantic.value value.value
          unless ← isDefEq (← inferType result) propType do
            throwError s!"semantic predicate `{name}` did not produce a proposition"
          pure result
  | fuel + 1, context, .bind kind pattern body => do
      unless kind == "∀" || kind == "∃" do
        throwError s!"unsupported Event-B binder `{kind}`"
      withPattern context pattern none fun bodyContext locals _ _ => do
        let body ← translatePred fuel bodyContext body
        if kind == "∀" then mkForallLocals locals body else mkExistsLocals locals body
  | _ + 1, _, .app _ _ => throwError "predicate application needs a semantic predicate binding"
  | _ + 1, _, term => throwError s!"unsupported Event-B predicate `{Formula.print term}`"

end

def translateExpression (context : KernelContext) (term : Formula.Term) : MetaM KernelTerm :=
  translateExpr (termFuel term + 1) context term

def translatePredicate (context : KernelContext) (term : Formula.Term) : MetaM Expr :=
  translatePred (termFuel term + 1) context term

end EventB.Embedding
