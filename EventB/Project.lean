/- Shared source-artifact to typing-project adapter. -/

import EventB.Typing.Check

namespace EventB

open EventB.Typing

inductive ModelKind where
  | machine
  | context
  deriving BEq, Repr, Inhabited

def ModelKind.label : ModelKind → String
  | .machine => "machine"
  | .context => "context"

structure ModelArtifact where
  component : String
  kind : ModelKind
  bytes : ByteArray
  path : Option String := none
  theories : List String := []
  deriving BEq, Inhabited

instance : Repr ModelArtifact where
  reprPrec artifact _ := Std.Format.text
    s!"ModelArtifact({artifact.component}, {artifact.bytes.size} bytes)"

def ModelArtifact.byteString (artifact : ModelArtifact) : String :=
  (String.fromUTF8? artifact.bytes).getD ""

private def artifactError (artifact : ModelArtifact) (message : String) : EventB.Error :=
  match artifact.path with
  | some path => (EventB.Error.model message).withPath path
  | none => EventB.Error.model message

def parseModelArtifact (artifact : ModelArtifact) : Except EventB.Error Component := do
  unless !artifact.component.isEmpty do
    throw (artifactError artifact "model artifact has no component identity")
  let model ← match parseModel artifact.bytes with
    | .ok model => pure model
    | .error error => .error error
  let rootKind := match model.root with
    | .machineFile _ _ => ModelKind.machine
    | .contextFile _ _ => ModelKind.context
    | _ => ModelKind.context
  unless rootKind == artifact.kind do
    throw (artifactError artifact "model artifact kind does not match its XML root")
  match model.root.attr? "org.eventb.core.name" with
  | some rootName =>
      unless rootName == artifact.component do
        throw (artifactError artifact
          s!"XML component name `{rootName}` does not match `{artifact.component}`")
  | none => pure ()
  pure { name := artifact.component, elem := model.root, theories := artifact.theories }

def projectFromArtifacts (artifacts : List ModelArtifact) : Except EventB.Error Project := do
  let components ← artifacts.mapM parseModelArtifact
  let names := components.map (·.name)
  unless names.eraseDups.length == names.length do
    throw (EventB.Error.model "model artifacts contain duplicate component identities")
  pure components

#guard match parseModelArtifact
    { component := "M", kind := .machine,
      bytes := "<?xml version=\"1.0\"?><org.eventb.core.machineFile/>".toUTF8 } with
  | .ok component => component.name == "M"
  | .error _ => false

#guard ModelArtifact.byteString
    { component := "M", kind := .machine,
      bytes := "<x>∈ ≔</x>".toUTF8 } == "<x>∈ ≔</x>"

#guard match parseModelArtifact
    { component := "M", kind := .machine,
      bytes := "<?xml version=\"1.0\"?><org.eventb.core.contextFile/>".toUTF8 } with
  | .error _ => true
  | .ok _ => false

#guard match parseModelArtifact
    { component := "M", kind := .machine,
      bytes := ("<?xml version=\"1.0\"?><org.eventb.core.machineFile " ++
        "org.eventb.core.name=\"Other\"/>").toUTF8 } with
  | .error _ => true
  | .ok _ => false

#guard match projectFromArtifacts
    [{ component := "M", kind := .machine,
       bytes := "<?xml version=\"1.0\"?><org.eventb.core.machineFile/>".toUTF8 }
     , { component := "M", kind := .machine,
         bytes := "<?xml version=\"1.0\"?><org.eventb.core.machineFile/>".toUTF8 }] with
  | .error _ => true
  | .ok _ => false

end EventB
