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

structure KernelContext where
  theory : Theory.Env := Theory.empty
  roots : List String := []
  signature : KernelSignature := {}
  bindings : List KernelBinding := []

structure KernelTerm where
  ty : Ty
  value : Expr

private def propType : Expr := mkSort .zero

private def KernelContext.lookup (context : KernelContext) (name : String) :
    Option KernelBinding := context.bindings.find? (·.name == name)

private def KernelSignature.carrier? (signature : KernelSignature) (name : String) :
    Option Expr := signature.carriers.find? (·.1 == name) |>.map (·.2)

private def typeExpr (context : KernelContext) : Ty → MetaM Expr
  | .given name =>
      match context.signature.carrier? name with
      | some type => pure type
      | none => throwError s!"no Lean type is registered for carrier `{name}`"
  | .int => pure (mkConst ``Int)
  | .bool => pure (mkConst ``Bool)
  | .pow type => do
      mkArrow (← typeExpr context type) propType
  | .prod left right => do
      mkAppM ``Prod #[← typeExpr context left, ← typeExpr context right]
  | .mvar index => throwError s!"unresolved Event-B type metavariable `?{index}`"

private def checked (context : KernelContext) (ty : Ty) (value : Expr) : MetaM KernelTerm := do
  let expected ← typeExpr context ty
  let actual ← inferType value
  unless ← isDefEq actual expected do
    throwError s!"translated term has type {actual}, expected {expected} for {ty.print}"
  pure { ty, value }

private def boolType : Expr := mkConst (Name.mkSimple "Bool")

private def trueProp : Expr := mkConst (Name.mkSimple "True")

private def mkAnd (left right : Expr) : MetaM Expr := mkAppM ``And #[left, right]
private def mkOr (left right : Expr) : MetaM Expr := mkAppM ``Or #[left, right]
private def mkImp (left right : Expr) : MetaM Expr := mkArrow left right
private def mkNot (value : Expr) : MetaM Expr := mkAppM ``Not #[value]
private def mkEq (left right : Expr) : MetaM Expr := mkAppM ``Eq #[left, right]

private def mkPair (left right : Expr) : MetaM Expr := mkAppM ``Prod.mk #[left, right]

private def mkExistsAt (type : Expr) (body : Expr → MetaM Expr) : MetaM Expr := do
  withLocalDeclD `x type fun x => do
    let predicate ← mkLambdaFVars #[x] (← body x)
    mkAppM ``Exists #[predicate]

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
  | some binding => checked context binding.ty binding.value
  | none =>
      if Theory.isIdentifierIn context.theory context.roots name then
        throwError s!"Event-B symbol `{name}` has no Lean semantic binding"
      else
        throwError s!"unknown Event-B identifier `{name}`"

private def asSet (term : KernelTerm) : MetaM (Ty × Expr) :=
  match term.ty with
  | .pow type => pure (type, term.value)
  | type => throwError s!"expected a set, found {type.print}"

private def sameType (left right : Ty) : MetaM Unit :=
  unless left == right do
    throwError s!"incompatible translated types {left.print} and {right.print}"

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

private def builtinSet (context : KernelContext) (name : String) : MetaM KernelTerm := do
  match name with
  | "BOOL" => checked context (.pow .bool) (← mkUniversalSet boolType)
  | "ℤ" => checked context (.pow .int) (← mkUniversalSet (mkConst ``Int))
  | "ℕ" => checked context (.pow .int) (← mkIntSet false)
  | "ℕ1" => checked context (.pow .int) (← mkIntSet true)
  | _ => lookupExpr context name

mutual

private def translateExpr (context : KernelContext) : Formula.Term → MetaM KernelTerm
  | .num value => checked context .int (mkApp (mkConst ``Int.ofNat) (mkNatLit value))
  | .id "TRUE" => checked context .bool (mkConst ``Bool.true)
  | .id "FALSE" => checked context .bool (mkConst ``Bool.false)
  | .id name => builtinSet context name
  | .set [] => throwError "empty set needs an expected element type"
  | .set _ => throwError "set extensions are not translated without an expected type"
  | .pre "−" value => do
      let value ← translateExpr context value
      let _ ← sameType value.ty .int
      checked context .int (mkApp (mkConst ``Int.neg) value.value)
  | .pre op value => do
      unless op == "ℙ" || op == "ℙ1" do
        throwError s!"unsupported Event-B prefix operator `{op}`"
      let value ← translateExpr context value
      let (type, set) ← asSet value
      let result ← mkPowerSet (← typeExpr context type) set (op == "ℙ1")
      checked context (.pow (.pow type)) result
  | Formula.Term.post op value => do
      unless op == "∼" do
        throwError s!"unsupported Event-B postfix operator `{op}`"
      let value ← translateExpr context value
      let (left, right) ← relationTypes value
      checked context (.pow (.prod right left))
        (← mkInverse (← typeExpr context left) (← typeExpr context right) value.value)
  | .img relation set => do
      let relation ← translateExpr context relation
      let set ← translateExpr context set
      let (left, right) ← relationTypes relation
      let (setType, set) ← asSet set
      let _ ← sameType left setType
      checked context (.pow right) (← mkImage (← typeExpr context left)
        (← typeExpr context right) relation.value set)
  | .app _ _ => throwError "function application needs a semantic function binding"
  | .bind "{" pattern (.bin "∣" _ _) => do
      match pattern with
      | .id name =>
          throwError s!"set comprehension binder `{name}` needs an explicit type"
      | _ => throwError "only simple set-comprehension binders are translated"
  | .bind kind _ _ => throwError s!"binder `{kind}` is not an expression here"
  | .bin "↦" left right => do
      let left ← translateExpr context left
      let right ← translateExpr context right
      checked context (.prod left.ty right.ty) (← mkPair left.value right.value)
  | .bin op left right => do
      match op with
      | "∪" | "∩" | "∖" =>
          let left ← translateExpr context left
          let right ← translateExpr context right
          let (leftType, left) ← asSet left
          let (rightType, right) ← asSet right
          let _ ← sameType leftType rightType
          checked context (.pow leftType)
            (← mkSetBinary op (← typeExpr context leftType) left right)
      | "×" =>
          let left ← translateExpr context left
          let right ← translateExpr context right
          let (leftType, left) ← asSet left
          let (rightType, right) ← asSet right
          checked context (.pow (.prod leftType rightType))
            (← mkProductSet (← typeExpr context leftType) (← typeExpr context rightType)
              left right)
      | "↔" | "⇸" | "→" | "⤔" | "↣" | "⤀" | "↠" | "⤖" =>
          let left ← translateExpr context left
          let right ← translateExpr context right
          let (leftType, left) ← asSet left
          let (rightType, right) ← asSet right
          let relation ← mkRelationSpace (← typeExpr context leftType)
            (← typeExpr context rightType) left right
          checked context (.pow (.pow (.prod leftType rightType))) relation
      | "+" | "−" | "∗" | "÷" | "mod" | "^" =>
          let left ← translateExpr context left
          let right ← translateExpr context right
          let _ ← sameType left.ty .int
          let _ ← sameType right.ty .int
          let function := match op with
            | "+" => ``Int.add
            | "−" => ``Int.sub
            | "∗" => ``Int.mul
            | "÷" => ``Int.ediv
            | "mod" => ``Int.emod
            | "^" => ``Int.pow
            | _ => ``Int.add
          checked context .int (← mkAppM function #[left.value, right.value])
      | "‥" =>
          let left ← translateExpr context left
          let right ← translateExpr context right
          let _ ← sameType left.ty .int
          let _ ← sameType right.ty .int
          withLocalDeclD `x (mkConst ``Int) fun x => do
            let lower := mkApp2 (mkConst ``Int.le) left.value x
            let upper := mkApp2 (mkConst ``Int.le) x right.value
            checked context (.pow .int) (← mkLambdaFVars #[x] (← mkAnd lower upper))
      | _ => throwError s!"unsupported Event-B expression operator `{op}`"

private def translatePred (context : KernelContext) : Formula.Term → MetaM Expr
  | .id "⊤" => pure (mkConst ``True)
  | .id "⊥" => pure (mkConst ``False)
  | .pre "¬" value => do
      mkNot (← translatePred context value)
  | .bin "∧" left right => do
      mkAnd (← translatePred context left) (← translatePred context right)
  | .bin "∨" left right => do
      mkOr (← translatePred context left) (← translatePred context right)
  | .bin "⇒" left right => do
      mkImp (← translatePred context left) (← translatePred context right)
  | .bin "⇔" left right => do
      mkAppM ``Iff #[← translatePred context left, ← translatePred context right]
  | .bin "=" left right => do
      let left ← translateExpr context left
      let right ← translateExpr context right
      let _ ← sameType left.ty right.ty
      mkEq left.value right.value
  | .bin "≠" left right => do
      let left ← translateExpr context left
      let right ← translateExpr context right
      let _ ← sameType left.ty right.ty
      mkNot (← mkEq left.value right.value)
  | .bin op left right => do
      match op with
      | "<" | "≤" | ">" | "≥" =>
          let left ← translateExpr context left
          let right ← translateExpr context right
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
          let left ← translateExpr context left
          let right ← translateExpr context right
          let (rightType, set) ← asSet right
          let _ ← sameType left.ty rightType
          let membership := mkApp set left.value
          if op == "∈" then pure membership else mkNot membership
      | "⊆" | "⊈" | "⊂" | "⊄" =>
          let left ← translateExpr context left
          let right ← translateExpr context right
          let (leftType, left) ← asSet left
          let (rightType, right) ← asSet right
          let _ ← sameType leftType rightType
          let subset ← mkSubset (← typeExpr context leftType) left right
          if op == "⊆" then pure subset else mkNot subset
      | _ => throwError s!"unsupported Event-B predicate operator `{op}`"
  | .app (.id "finite") value => do
      let value ← translateExpr context value
      let _ ← asSet value
      throwError "finite needs a finite-set semantic binding"
  | .bind kind pattern body => do
      unless kind == "∀" || kind == "∃" do
        throwError s!"unsupported Event-B binder `{kind}`"
      match pattern with
      | .bin "⦂" (.id name) typeTerm => do
          let eventBType ← match typeTerm with
            | .id "ℤ" => pure .int
            | .id "BOOL" => pure .bool
            | .id carrier => pure (.given carrier)
            | _ => throwError "unsupported quantified binder type"
          let typeExpr ← typeExpr context eventBType
          withLocalDeclD (Name.mkSimple name) typeExpr fun localVar => do
            let body ← translatePred { context with bindings :=
              { name, ty := eventBType, value := localVar } :: context.bindings } body
            if kind == "∀" then mkForallFVars #[localVar] body
            else mkAppM ``Exists #[← mkLambdaFVars #[localVar] body]
      | _ => throwError "quantifiers need a typed simple binder"
  | .app _ _ => throwError "predicate application needs a semantic predicate binding"
  | term => throwError s!"unsupported Event-B predicate `{Formula.print term}`"

end

def translateExpression (context : KernelContext) (term : Formula.Term) : MetaM KernelTerm :=
  translateExpr context term

def translatePredicate (context : KernelContext) (term : Formula.Term) : MetaM Expr :=
  translatePred context term

end EventB.Embedding
