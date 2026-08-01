/-
Small, dependency-free adapter for the supported Event-B theory-file subset.

Rodin theory files use XML and the `.tuf` extension.  This adapter deliberately
accepts only the declarations represented by `Theory.Spec`; every other child is
reported instead of being discarded.  It is an interchange boundary, not a Rodin
runtime or a replacement for the native theory checker.
-/

import EventB.Xml
import EventB.Theory.Validate

namespace EventB.Theory.Rodin

open EventB EventB.Formula EventB.Prelude EventB.Typing

private def ns := "org.eventb.theory.core."
private def tag (name : String) : String := ns ++ name

private def attr (elem : XmlElem) (names : List String) : Option String :=
  names.findSome? elem.attr?

private def required (path : List String) (elem : XmlElem) (names : List String) :
    Except String String :=
  match attr elem names with
  | some value => pure value
  | none => .error s!"{String.intercalate "/" path}: missing `{names.head!}`"

private def checkChildren (path : List String) (elem : XmlElem) (allowed : List String) :
    Except String Unit :=
  match elem.children.find? (fun child => !allowed.contains child.tag) with
  | none => pure ()
  | some child => .error s!"{String.intercalate "/" path}: unsupported child `{child.tag}`"

private def parseType (path : List String) (elem : XmlElem) : Except String Ty := do
  let source ← required path elem ["type", "org.eventb.core.type"]
  match Ty.parse source with
  | some type => pure type
  | none => .error s!"{String.intercalate "/" path}: invalid type `{source}`"

private def parseFormula (path : List String) (source : String) : Except String Term :=
  match Formula.parse source with
  | .ok term => pure term
  | .error error => .error s!"{String.intercalate "/" path}: invalid formula: {error}"

private def parseFormulaAttr (path : List String) (elem : XmlElem) (name : String) :
    Except String Term := do
  let source ← required path elem [name]
  parseFormula path source

private def parseSymbol (path : List String) (elem : XmlElem) : Except String Symbol := do
  let _ ← checkChildren path elem []
  let name ← required path elem ["identifier", "name"]
  let kind ← required path elem ["kind"]
  let kind : SymbolKind ← match kind with
    | "carrierSet" => pure .carrierSet
    | "constant" => pure .constant
    | "predicate" => pure .predicate
    | "expression" => pure .expression
    | other => .error s!"{String.intercalate "/" path}: unsupported symbol kind `{other}`"
  let type ← match kind with
    | SymbolKind.predicate => pure none
    | _ => some <$> parseType path elem
  let application ← match attr elem ["application"] with
    | none => pure none
    | some "total" => pure (some ApplicationKind.total)
    | some "wellDefined" => pure (some ApplicationKind.wellDefined)
    | some other => .error s!"{String.intercalate "/" path}: unsupported application `{other}`"
  let description := (attr elem ["description"]).getD "Imported Rodin theory symbol."
  pure (Symbol.mk name kind type description application [] (SymbolId.unqualified name)
    (SourceRange.synthetic "Rodin theory"))

private def parseConstructor (path : List String) (elem : XmlElem) :
    Except String Constructor := do
  let _ ← checkChildren path elem [tag "constructorArgument"]
  let name ← required path elem ["identifier", "name"]
  let arguments ← elem.children.mapM fun child => do
    if child.tag != tag "constructorArgument" then
      .error s!"{String.intercalate "/" path}: unsupported constructor child `{child.tag}`"
    let childPath := path ++ ["constructorArgument"]
    parseType childPath child
  pure { name, arguments }

private def parseDatatype (path : List String) (elem : XmlElem) :
    Except String Declaration := do
  let _ ← checkChildren path elem [tag "typeParameter", tag "datatypeConstructor"]
  let name ← required path elem ["identifier", "name"]
  let parameters ← elem.children.filter (·.tag == tag "typeParameter") |>.mapM fun child =>
    required (path ++ [child.tag]) child ["identifier", "name"]
  let constructors ← elem.children.filter (·.tag == tag "datatypeConstructor") |>.mapM
    (parseConstructor (path ++ ["datatypeConstructor"]))
  pure (.dataType { name, parameters, constructors })

private def parseParameters (path : List String) (elem : XmlElem) :
    Except String (List (String × Ty)) :=
  elem.children.filter (·.tag == tag "parameter") |>.mapM fun child => do
    let name ← required (path ++ [child.tag]) child ["identifier", "name"]
    let type ← parseType (path ++ [child.tag]) child
    pure (name, type)

private def parseTypeParameters (path : List String) (elem : XmlElem) :
    Except String (List String) :=
  elem.children.filter (·.tag == tag "typeParameter") |>.mapM fun child =>
    required (path ++ [child.tag]) child ["identifier", "name"]

private def parseDefinition (path : List String) (elem : XmlElem) :
    Except String Declaration := do
  let _ ← checkChildren path elem [tag "typeParameter", tag "parameter"]
  let name ← required path elem ["identifier", "name"]
  let typeParameters ← parseTypeParameters path elem
  let parameters ← parseParameters path elem
  let result ← parseType path elem
  let body ← parseFormulaAttr path elem "formula"
  let kind := if attr elem ["kind"] == some "axiomatic" then .axiomatic else .definitional
  pure (.definitionDecl { name, typeParameters, parameters, result, body, kind })

private def parseRule (path : List String) (elem : XmlElem) (kind : DeclarationKind) :
    Except String Declaration := do
  let _ ← checkChildren path elem [tag "typeParameter", tag "parameter", tag "premise"]
  let name ← required path elem ["identifier", "name"]
  let typeParameters ← parseTypeParameters path elem
  let parameters ← parseParameters path elem
  let premises ← elem.children.filter (·.tag == tag "premise") |>.mapM fun child =>
    parseFormulaAttr (path ++ [child.tag]) child "formula"
  let lhs ← match kind with
    | .rewrite => some <$> parseFormulaAttr path elem "lhs"
    | _ => pure none
  let rhs ← match kind with
    | .rewrite => some <$> parseFormulaAttr path elem "rhs"
    | _ => pure none
  let conclusion ← match kind with
    | .rewrite => pure none
    | _ => some <$> parseFormulaAttr path elem "conclusion"
  pure (.ruleDecl { name, kind, typeParameters, parameters, premises, lhs, rhs, conclusion })

private def parseChild (path : List String) (elem : XmlElem) : Except String (Option String ×
    Option Symbol × Option Declaration) := do
  if elem.tag == tag "import" then
    let name ← required path elem ["identifier", "name"]
    pure (some name, none, none)
  else if elem.tag == tag "symbol" then
    pure (none, some (← parseSymbol path elem), none)
  else if elem.tag == tag "datatypeDefinition" then
    pure (none, none, some (← parseDatatype path elem))
  else if elem.tag == tag "definition" then
    pure (none, none, some (← parseDefinition path elem))
  else if elem.tag == tag "rewriteRule" then
    pure (none, none, some (← parseRule path elem .rewrite))
  else if elem.tag == tag "inferenceRule" then
    pure (none, none, some (← parseRule path elem .inference))
  else if elem.tag == tag "theorem" then
    pure (none, none, some (← parseRule path elem .theorem))
  else .error s!"{String.intercalate "/" path}: unsupported theory child `{elem.tag}`"

private def parseRoot (root : XmlElem) : Except String Spec := do
  unless root.tag == tag "theoryFile" || root.tag == tag "theoryRoot" do
    throw s!"root is not a Rodin theory file: `{root.tag}`"
  let name ← required [root.tag] root ["identifier", "name"]
  let values ← root.children.mapM fun child =>
    parseChild [root.tag, child.tag] child
  let imports := values.filterMap (·.1)
  let symbols := values.filterMap (fun value => value.2.1)
  let declarations := values.filterMap (fun value => value.2.2)
  pure (Theory.canonicalize { name, imports, symbols, declarations })

def importSpec (env : Env) (source : String) : Except String Spec := do
  let root ← match parseXmlString source with
    | .ok root => pure root
    | .error error => .error s!"invalid Rodin theory XML: {error.pretty source.toUTF8}"
  let spec ← parseRoot root
  let report := Validate.validateSpec env spec
  if report.isValid then pure spec
  else .error (report.errors.map (·.message) |>.intersperse "; " |>.foldl (· ++ ·) "")

private def escape (source : String) : String :=
  source.toList.foldl (fun output char => output ++ match char with
    | '&' => "&amp;"
    | '<' => "&lt;"
    | '>' => "&gt;"
    | '"' => "&quot;"
    | '\'' => "&apos;"
    | char => char.toString) ""

private def attrs (values : List (String × String)) : String :=
  values.foldl (fun output (name, value) =>
    output ++ " " ++ name ++ "=\"" ++ escape value ++ "\"") ""

mutual

private def render : Nat → XmlElem → Except String String
  | 0, _ => .error "Rodin theory XML is too deeply nested"
  | fuel + 1, elem => do
      let head := "<" ++ elem.tag ++ attrs elem.attrs
      if elem.children.isEmpty then pure (head ++ "/>")
      else
        let children ← renderChildren fuel elem.children
        pure (head ++ ">" ++ children ++ "</" ++ elem.tag ++ ">")

private def renderChildren : Nat → List XmlElem → Except String String
  | 0, _ => .error "Rodin theory XML is too deeply nested"
  | _, [] => pure ""
  | fuel + 1, child :: children => do
      let first ← render fuel child
      let rest ← renderChildren fuel children
      pure (first ++ rest)

end

private def symbolElem (symbol : Symbol) : XmlElem :=
  { tag := tag "symbol"
    attrs := [("identifier", symbol.name), ("kind", match symbol.kind with
      | .carrierSet => "carrierSet"
      | .constant => "constant"
      | .predicate => "predicate"
      | .expression => "expression")] ++
      (symbol.type.map (fun type => ("type", type.print)) |>.toList) ++
      (symbol.application.map (fun application => ("application", match application with
        | .total => "total"
        | .wellDefined => "wellDefined")) |>.toList)
    children := [] }

private def constructorElem (constructor : Constructor) : XmlElem :=
  { tag := tag "datatypeConstructor", attrs := [("identifier", constructor.name)]
    children := constructor.arguments.map fun type =>
      { tag := tag "constructorArgument", attrs := [("type", type.print)], children := [] } }

private def datatypeElem (datatype : Datatype) : XmlElem :=
  let parameters : List XmlElem := datatype.parameters.map fun parameter =>
    { tag := tag "typeParameter", attrs := [("identifier", parameter)], children := [] }
  { tag := tag "datatypeDefinition", attrs := [("identifier", datatype.name)],
        children := parameters ++ datatype.constructors.map constructorElem }

private def typeParameterElems (parameters : List String) : List XmlElem :=
  parameters.map fun parameter =>
    { tag := tag "typeParameter", attrs := [("identifier", parameter)], children := [] }

private def parameterElem (parameter : String × Ty) : XmlElem :=
  { tag := tag "parameter", attrs := [("identifier", parameter.1), ("type", parameter.2.print)],
    children := [] }

private def declarationElems : Declaration → List XmlElem
  | .dataType datatype =>
      [datatypeElem datatype]
  | .definitionDecl definition =>
      let kind := match definition.kind with
        | .definitional => "definitional"
        | .axiomatic => "axiomatic"
      [{ tag := tag "definition", attrs := [("identifier", definition.name),
          ("type", definition.result.print), ("formula", Formula.print definition.body),
          ("kind", kind)], children :=
          typeParameterElems definition.typeParameters ++ definition.parameters.map parameterElem }]
  | .ruleDecl rule =>
      let name : String := match rule.kind with
        | .rewrite => "rewriteRule"
        | .inference => "inferenceRule"
        | .theorem => "theorem"
        | _ => "unsupported"
      let ruleAttrs := [("identifier", rule.name)] ++
        (rule.lhs.map (fun term => ("lhs", Formula.print term))).toList ++
        (rule.rhs.map (fun term => ("rhs", Formula.print term))).toList ++
        (rule.conclusion.map (fun term => ("conclusion", Formula.print term))).toList
      [XmlElem.mk (tag name) ruleAttrs
        (typeParameterElems rule.typeParameters ++ rule.parameters.map parameterElem ++
          rule.premises.map fun premise =>
          XmlElem.mk (tag "premise") [("formula", Formula.print premise)] [])]

def exportSpec (env : Env) (spec : Spec) : Except String String := do
  let report := Validate.validateSpec env spec
  if report.isValid then
    let root : XmlElem :=
      { tag := tag "theoryFile", attrs := [("identifier", spec.name)],
        children := (spec.imports.map fun name =>
            { tag := tag "import", attrs := [("identifier", name)], children := [] }) ++
          spec.symbols.map symbolElem ++ spec.declarations.flatMap declarationElems }
    let xml ← render 1000 root
    pure ("<?xml version=\"1.0\"?>" ++ xml)
  else .error (report.errors.map (·.message) |>.intersperse "; " |>.foldl (· ++ ·) "")

end EventB.Theory.Rodin
