/- A supported `.tuf` subset round-trips without a Rodin installation. -/
import EventB.Theory.Rodin

namespace EventB.RodinTheoryDemo

open EventB EventB.Theory

private def source :=
  "<?xml version=\"1.0\"?><org.eventb.theory.core.theoryFile " ++
    "identifier=\"Basic\"><org.eventb.theory.core.symbol " ++
    "identifier=\"LIMIT\" kind=\"constant\" type=\"ℤ\"/>" ++
    "<org.eventb.theory.core.datatypeDefinition identifier=\"Colour\">" ++
    "<org.eventb.theory.core.datatypeConstructor identifier=\"red\"/>" ++
    "<org.eventb.theory.core.datatypeConstructor identifier=\"blue\"/>" ++
    "</org.eventb.theory.core.datatypeDefinition>" ++
    "<org.eventb.theory.core.definition identifier=\"zero\" type=\"ℤ\" " ++
    "formula=\"0\" kind=\"definitional\"/>" ++
    "<org.eventb.theory.core.rewriteRule identifier=\"add_zero\" " ++
    "lhs=\"x + 0\" rhs=\"x\"><org.eventb.theory.core.parameter " ++
    "identifier=\"x\" type=\"ℤ\"/></org.eventb.theory.core.rewriteRule>" ++
    "<org.eventb.theory.core.theorem identifier=\"zero_eq\" " ++
    "conclusion=\"0 = 0\"/>" ++
    "</org.eventb.theory.core.theoryFile>"

private def unsupported :=
  "<?xml version=\"1.0\"?><org.eventb.theory.core.theoryFile " ++
    "identifier=\"Bad\"><org.eventb.theory.core.future/></" ++
    "org.eventb.theory.core.theoryFile>"

#guard match Theory.Rodin.importSpec Theory.empty source with
  | .ok spec => spec.name == "Basic" &&
      spec.symbols.map (·.name) == ["LIMIT"] &&
      spec.declarations.map Declaration.name == ["Colour", "zero", "add_zero", "zero_eq"]
  | .error _ => false

#guard match Theory.Rodin.importSpec Theory.empty source with
  | .ok spec => match Theory.Rodin.exportSpec Theory.empty spec with
    | .ok output => match Theory.Rodin.importSpec Theory.empty output with
      | .ok roundTrip => roundTrip.name == spec.name &&
          roundTrip.declarations.map Declaration.name == spec.declarations.map Declaration.name
      | .error _ => false
    | .error _ => false
  | .error _ => false

#guard match Theory.Rodin.importSpec Theory.empty unsupported with
  | .error _ => true
  | .ok _ => false

private def base : Spec :=
  { name := "Base"
    symbols := [{ name := "LIMIT", kind := .constant, type := some .int, description := "A base constant." }] }

#guard match Theory.add Theory.empty base with
  | .ok env => match Theory.Rodin.importSpec env
      ("<?xml version=\"1.0\"?><org.eventb.theory.core.theoryFile " ++
        "identifier=\"Derived\"><org.eventb.theory.core.import " ++
        "identifier=\"Base\"/></org.eventb.theory.core.theoryFile>") with
    | .ok _ => true
    | .error _ => false
  | .error _ => false

end EventB.RodinTheoryDemo
