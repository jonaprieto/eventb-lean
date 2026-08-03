/-
  Plain-text input in the format used by eventb-rossi.org.

  The parser lowers both components below to the same `Elem` tree used by Rodin XML,
  so the existing typing and proof-obligation pipeline can consume the result.
-/
import EventB.Rossi

namespace EventB.RossiDemo

open EventB

private def source : String :=
  "CONTEXT counter_ctx SETS STATUS CONSTANTS max_value " ++
  "AXIOMS @max_value_eq max_value = 100 @max_value_pos max_value > 0 END " ++
  "MACHINE counter SEES counter_ctx VARIABLES count INVARIANTS " ++
  "@count_nat count ∈ ℕ @count_bound count ≤ max_value EVENTS " ++
  "EVENT INITIALISATION THEN count := 0 END " ++
  "EVENT increment STATUS convergent WHERE @below_max count < max_value " ++
  "THEN count := count + 1 END END"

private def childrenWith (tag : String) (elem : Elem) : List Elem :=
  elem.children.filter (fun child => child.tag == "org.eventb.core." ++ tag)

private def compactMachine : String :=
  "MACHINE M VARIABLES x INVARIANTS @i x ∈ ℕ EVENTS " ++
  "EVENT INITIALISATION THEN x := 0 END END"

#guard match Rossi.parse source with
  | .ok [context, machine] =>
      context.name == "counter_ctx" && machine.name == "counter" &&
      (childrenWith "carrierSet" context.model.root).map (·.attr? "org.eventb.core.identifier")
        == [some "STATUS"] &&
      (childrenWith "event" machine.model.root).length == 2
  | _ => false

#guard match Rossi.parse compactMachine with
  | .ok [component] =>
      component.name == "M" &&
        (childrenWith "variable" component.model.root).length == 1
  | _ => false

#guard match Rossi.parse "CONTEXT C AXIOMS @only END" with
  | .error message => (EventB.Error.render message).contains "formula"
  | _ => false

private def sourceWithRefinement : String :=
  "context C\nsets\n  S = {a, b}\nconstants\n  k\n" ++
  "axioms\n  @a1\n  k ∈ S\ntheorems\n  theorem @t1 k = k\nend\n" ++
  "machine M\nvariables x\nevents\nconvergent event M\nrefines Old\n" ++
  "any p q\nwhere @g p ∈ S\n" ++
  "with @w p' = p\nbegin\n  x := x + 1\nend\nend\n"

#guard match Rossi.parse sourceWithRefinement with
  | .ok [context, machine] =>
      (childrenWith "carrierSet" context.model.root).length == 1 &&
      (childrenWith "axiom" context.model.root).any
        (fun elem => elem.attr? "org.eventb.core.theorem" == some "true") &&
      (childrenWith "event" machine.model.root).length == 1
  | _ => false

end EventB.RossiDemo
