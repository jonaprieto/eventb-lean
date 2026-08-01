/-
  Boundary cases from Rossi's grammar: formulas may span lines, and actions may be
  adjacent without labels or semicolons.
-/
import EventB.Rossi

namespace EventB.RossiBoundaryDemo

open EventB

private def childrenWith (tag : String) (elem : Elem) : List Elem :=
  elem.children.filter (fun child => child.tag == "org.eventb.core." ++ tag)

private def formulaOf (elem : Elem) : Option String :=
  elem.attr? "org.eventb.core.predicate"

private def assignmentOf (elem : Elem) : Option String :=
  elem.attr? "org.eventb.core.assignment"

private def wrapped : String :=
  "CONTEXT C\nSETS S\nCONSTANTS x y\nAXIOMS\n@a\nx ∈ S\n∧ y ∈ S\n@b\ny = y\nEND\n" ++
  "MACHINE M\nSEES C\nVARIABLES v w\nEVENTS\nEVENT INITIALISATION\nTHEN\n" ++
  "v := 0 v := 1\nEND\nEVENT update\nTHEN\n@set_v\n" ++
  "v := v +\n1\n@set_w w := w + 1\nEND\nEND\n"

#guard match Rossi.parse wrapped with
  | .ok [context, machine] =>
      (childrenWith "axiom" context.model.root).map formulaOf ==
          [some "x ∈ S ∧ y ∈ S", some "y = y"] &&
        match childrenWith "event" machine.model.root with
        | first :: second :: _ =>
            (childrenWith "action" first).map assignmentOf ==
                [some "v := 0", some "v := 1"] &&
              (childrenWith "action" second).map assignmentOf ==
                [some "v := v + 1", some "w := w + 1"]
        | _ => false
  | _ => false

end EventB.RossiBoundaryDemo
