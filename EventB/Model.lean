/-
The P0 model is deliberately shallow. XML attributes remain strings;
formula syntax and typing are P1/P2 concerns.
-/

import EventB.Xml

namespace EventB

abbrev XmlAttrs := List (String × String)

inductive Elem where
  | machineFile : XmlAttrs → List Elem → Elem
  | contextFile : XmlAttrs → List Elem → Elem
  | seesContext : XmlAttrs → List Elem → Elem
  | refinesMachine : XmlAttrs → List Elem → Elem
  | extendsContext : XmlAttrs → List Elem → Elem
  | carrierSet : XmlAttrs → List Elem → Elem
  | constant : XmlAttrs → List Elem → Elem
  | axiom : XmlAttrs → List Elem → Elem
  | variable : XmlAttrs → List Elem → Elem
  | invariant : XmlAttrs → List Elem → Elem
  | event : XmlAttrs → List Elem → Elem
  | refinesEvent : XmlAttrs → List Elem → Elem
  | parameter : XmlAttrs → List Elem → Elem
  | witness : XmlAttrs → List Elem → Elem
  | guard : XmlAttrs → List Elem → Elem
  | action : XmlAttrs → List Elem → Elem
  /-- Anything outside the `org.eventb.core.*` namespace, kept verbatim by tag.
  ERTMS-HL3 embeds iUML-B state machines and class diagrams as
  `ac.soton.eventb.emf.core.extension.persistence.serialisedExtension` nodes; dropping
  them would make the reader lossy, and hard-erroring on them would reject 12 of the 38
  corpus files over payload that is not Event-B. Unknown `org.eventb.core.*` elements
  still fail loudly. -/
  | extension : String → XmlAttrs → List Elem → Elem
  deriving BEq, Repr

structure Model where
  root : Elem
  deriving BEq, Repr

def inventoryTags : List String :=
  ["guard", "action", "event", "refinesEvent", "variable", "invariant", "parameter",
   "axiom", "constant", "machineFile", "seesContext", "refinesMachine", "extendsContext",
   "contextFile", "witness", "carrierSet"]

def Elem.tag : Elem → String
  | .machineFile _ _ => "org.eventb.core.machineFile"
  | .contextFile _ _ => "org.eventb.core.contextFile"
  | .seesContext _ _ => "org.eventb.core.seesContext"
  | .refinesMachine _ _ => "org.eventb.core.refinesMachine"
  | .extendsContext _ _ => "org.eventb.core.extendsContext"
  | .carrierSet _ _ => "org.eventb.core.carrierSet"
  | .constant _ _ => "org.eventb.core.constant"
  | .axiom _ _ => "org.eventb.core.axiom"
  | .variable _ _ => "org.eventb.core.variable"
  | .invariant _ _ => "org.eventb.core.invariant"
  | .event _ _ => "org.eventb.core.event"
  | .refinesEvent _ _ => "org.eventb.core.refinesEvent"
  | .parameter _ _ => "org.eventb.core.parameter"
  | .witness _ _ => "org.eventb.core.witness"
  | .guard _ _ => "org.eventb.core.guard"
  | .action _ _ => "org.eventb.core.action"
  | .extension tag _ _ => tag

def Elem.attrs : Elem → XmlAttrs
  | .machineFile attrs _ => attrs
  | .contextFile attrs _ => attrs
  | .seesContext attrs _ => attrs
  | .refinesMachine attrs _ => attrs
  | .extendsContext attrs _ => attrs
  | .carrierSet attrs _ => attrs
  | .constant attrs _ => attrs
  | .axiom attrs _ => attrs
  | .variable attrs _ => attrs
  | .invariant attrs _ => attrs
  | .event attrs _ => attrs
  | .refinesEvent attrs _ => attrs
  | .parameter attrs _ => attrs
  | .witness attrs _ => attrs
  | .guard attrs _ => attrs
  | .action attrs _ => attrs
  | .extension _ attrs _ => attrs

def Elem.children : Elem → List Elem
  | .machineFile _ children => children
  | .contextFile _ children => children
  | .seesContext _ children => children
  | .refinesMachine _ children => children
  | .extendsContext _ children => children
  | .carrierSet _ children => children
  | .constant _ children => children
  | .axiom _ children => children
  | .variable _ children => children
  | .invariant _ children => children
  | .event _ children => children
  | .refinesEvent _ children => children
  | .parameter _ children => children
  | .witness _ children => children
  | .guard _ children => children
  | .action _ children => children
  | .extension _ _ children => children

def Elem.attr? (elem : Elem) (key : String) : Option String :=
  elem.attrs.find? (fun (name, _) => name == key) |>.map (·.2)

private partial def countTag (wanted : String) (elem : Elem) : Nat :=
  (if elem.tag == wanted then 1 else 0) +
    elem.children.foldl (fun count child => count + countTag wanted child) 0

def Model.inventory (model : Model) : List (String × Nat) :=
  inventoryTags.map (fun tag => (tag, countTag ("org.eventb.core." ++ tag) model.root))

/-- Attributes carrying an Event-B formula. `expression` is the variant used by
`org.eventb.core.variant`, which the corpus does not exercise but Rodin emits. -/
def formulaAttrs : List String :=
  ["org.eventb.core.predicate", "org.eventb.core.assignment", "org.eventb.core.expression"]

/-- Every formula in the model, in document order, tagged by the owning element's label
so a P1 failure names the invariant or guard it came from. -/
partial def Elem.formulas (elem : Elem) : List (String × String) :=
  let label := (elem.attr? "org.eventb.core.label").getD (elem.tag.splitOn "." |>.getLast!)
  let here := formulaAttrs.filterMap (fun a => (elem.attr? a).map (fun f => (label, f)))
  elem.children.foldl (fun acc c => acc ++ c.formulas) here

def Model.formulas (model : Model) : List (String × String) :=
  model.root.formulas

private partial def mapElem (elem : XmlElem) : Except String Elem := do
  let children ← elem.children.mapM mapElem
  match elem.tag with
  | "org.eventb.core.machineFile" => pure (.machineFile elem.attrs children)
  | "org.eventb.core.contextFile" => pure (.contextFile elem.attrs children)
  | "org.eventb.core.seesContext" => pure (.seesContext elem.attrs children)
  | "org.eventb.core.refinesMachine" => pure (.refinesMachine elem.attrs children)
  | "org.eventb.core.extendsContext" => pure (.extendsContext elem.attrs children)
  | "org.eventb.core.carrierSet" => pure (.carrierSet elem.attrs children)
  | "org.eventb.core.constant" => pure (.constant elem.attrs children)
  | "org.eventb.core.axiom" => pure (.axiom elem.attrs children)
  | "org.eventb.core.variable" => pure (.variable elem.attrs children)
  | "org.eventb.core.invariant" => pure (.invariant elem.attrs children)
  | "org.eventb.core.event" => pure (.event elem.attrs children)
  | "org.eventb.core.refinesEvent" => pure (.refinesEvent elem.attrs children)
  | "org.eventb.core.parameter" => pure (.parameter elem.attrs children)
  | "org.eventb.core.witness" => pure (.witness elem.attrs children)
  | "org.eventb.core.guard" => pure (.guard elem.attrs children)
  | "org.eventb.core.action" => pure (.action elem.attrs children)
  | tag =>
      if tag.startsWith "org.eventb.core." then
        .error ("unknown Event-B core element: " ++ tag)
      else
        pure (.extension tag elem.attrs children)

def fromXml (xml : XmlElem) : Except String Model := do
  let root ← mapElem xml
  match root with
  | .machineFile _ _ | .contextFile _ _ => pure { root := root }
  | _ => .error ("expected machineFile or contextFile root, got " ++ root.tag)

def parseModel (source : ByteArray) : Except String Model :=
  match parseXml source with
  | .error err => .error (err.pretty source)
  | .ok xml => fromXml xml

def parseMachine (source : ByteArray) : Except String Model := do
  let model ← parseModel source
  match model.root with
  | .machineFile _ _ => pure model
  | _ => .error "expected machineFile root"

def parseContext (source : ByteArray) : Except String Model := do
  let model ← parseModel source
  match model.root with
  | .contextFile _ _ => pure model
  | _ => .error "expected contextFile root"

def readModel (path : System.FilePath) : IO (Except String Model) := do
  pure (parseModel (← IO.FS.readBinFile path))

end EventB
