/-
The P0 Rodin model is deliberately shallow. XML attributes remain strings;
formula syntax and typing are P1/P2 concerns.
-/

import EventB.Rodin.Xml

namespace EventB.Rodin

abbrev XmlAttrs := List (String × String)

inductive RodinElem where
  | machineFile : XmlAttrs → List RodinElem → RodinElem
  | contextFile : XmlAttrs → List RodinElem → RodinElem
  | seesContext : XmlAttrs → List RodinElem → RodinElem
  | refinesMachine : XmlAttrs → List RodinElem → RodinElem
  | extendsContext : XmlAttrs → List RodinElem → RodinElem
  | carrierSet : XmlAttrs → List RodinElem → RodinElem
  | constant : XmlAttrs → List RodinElem → RodinElem
  | axiom : XmlAttrs → List RodinElem → RodinElem
  | variable : XmlAttrs → List RodinElem → RodinElem
  | invariant : XmlAttrs → List RodinElem → RodinElem
  | event : XmlAttrs → List RodinElem → RodinElem
  | refinesEvent : XmlAttrs → List RodinElem → RodinElem
  | parameter : XmlAttrs → List RodinElem → RodinElem
  | witness : XmlAttrs → List RodinElem → RodinElem
  | guard : XmlAttrs → List RodinElem → RodinElem
  | action : XmlAttrs → List RodinElem → RodinElem
  /-- Anything outside the `org.eventb.core.*` namespace, kept verbatim by tag.
  ERTMS-HL3 embeds iUML-B state machines and class diagrams as
  `ac.soton.eventb.emf.core.extension.persistence.serialisedExtension` nodes; dropping
  them would make the reader lossy, and hard-erroring on them would reject 12 of the 38
  corpus files over payload that is not Event-B. Unknown `org.eventb.core.*` elements
  still fail loudly. -/
  | extension : String → XmlAttrs → List RodinElem → RodinElem
  deriving BEq, Repr

structure RodinModel where
  root : RodinElem
  deriving BEq, Repr

def inventoryTags : List String :=
  ["guard", "action", "event", "refinesEvent", "variable", "invariant", "parameter",
   "axiom", "constant", "machineFile", "seesContext", "refinesMachine", "extendsContext",
   "contextFile", "witness", "carrierSet"]

def RodinElem.tag : RodinElem → String
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

def RodinElem.attrs : RodinElem → XmlAttrs
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

def RodinElem.children : RodinElem → List RodinElem
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

def RodinElem.attr? (elem : RodinElem) (key : String) : Option String :=
  elem.attrs.find? (fun (name, _) => name == key) |>.map (·.2)

private partial def countTag (wanted : String) (elem : RodinElem) : Nat :=
  (if elem.tag == wanted then 1 else 0) +
    elem.children.foldl (fun count child => count + countTag wanted child) 0

def RodinModel.inventory (model : RodinModel) : List (String × Nat) :=
  inventoryTags.map (fun tag => (tag, countTag ("org.eventb.core." ++ tag) model.root))

private partial def mapElem (elem : XmlElem) : Except String RodinElem := do
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
        .error ("unknown Rodin core element: " ++ tag)
      else
        pure (.extension tag elem.attrs children)

def fromXml (xml : XmlElem) : Except String RodinModel := do
  let root ← mapElem xml
  match root with
  | .machineFile _ _ | .contextFile _ _ => pure { root := root }
  | _ => .error ("expected machineFile or contextFile root, got " ++ root.tag)

def parseModel (source : ByteArray) : Except String RodinModel :=
  match parse source with
  | .error err => .error (err.pretty source)
  | .ok xml => fromXml xml

def parseMachine (source : ByteArray) : Except String RodinModel := do
  let model ← parseModel source
  match model.root with
  | .machineFile _ _ => pure model
  | _ => .error "expected machineFile root"

def parseContext (source : ByteArray) : Except String RodinModel := do
  let model ← parseModel source
  match model.root with
  | .contextFile _ _ => pure model
  | _ => .error "expected contextFile root"

def readModel (path : System.FilePath) : IO (Except String RodinModel) := do
  pure (parseModel (← IO.FS.readBinFile path))

end EventB.Rodin
