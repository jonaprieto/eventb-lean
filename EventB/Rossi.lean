/-
  Reader for the plain-text Event-B syntax used by eventb-rossi.org.

  The reader lowers Rossi components to the same `Elem` tree as Rodin XML.  It is
  intentionally a source reader, not a second typechecker: formulas remain strings
  until P1/P2, just as they do in `Model.parseModel`.
-/

import EventB.Model

namespace EventB.Rossi

open EventB

structure Component where
  name : String
  model : Model
  deriving BEq, Repr

private structure Line where
  number : Nat
  text : String

private inductive CommentMode where
  | normal
  | line
  | block

private def whitespace (c : Char) : Bool := c.isWhitespace

private def trim (s : String) : String :=
  let left := s.toList.dropWhile whitespace
  String.ofList (left.reverse.dropWhile whitespace |>.reverse)

private def lower (s : String) : String :=
  String.ofList (s.toList.map Char.toLower)

private def stripComments (source : String) : Except String String :=
  go source.toList .normal []
where
  go : List Char → CommentMode → List Char → Except String String
    | [], .block, _ => .error "unterminated block comment"
    | [], _, out => .ok (String.ofList out.reverse)
    | '/' :: '/' :: rest, .normal, out => go rest .line out
    | '/' :: '*' :: rest, .normal, out => go rest .block out
    | c :: rest, .normal, out => go rest .normal (c :: out)
    | '\n' :: rest, .line, out => go rest .normal ('\n' :: out)
    | _ :: rest, .line, out => go rest .line out
    | '*' :: '/' :: rest, .block, out => go rest .normal out
    | '\n' :: rest, .block, out => go rest .block ('\n' :: out)
    | _ :: rest, .block, out => go rest .block out

private def structuralWords : List String :=
  ["context", "extends", "sets", "constants", "axioms", "theorems", "end", "machine",
   "refines", "sees", "variables", "invariants", "variant", "events", "event", "any",
   "where", "when", "with", "then", "begin", "witness"]

private def wordPrefix? (word : String) (cs : List Char) : Bool :=
  let wanted := (lower word).toList
  let actual := cs.take wanted.length |>.map Char.toLower
  actual == wanted && match cs.drop wanted.length with
    | c :: _ => !c.isAlphanum && c != '_' && c != '-'
    | [] => true

private def splitStructural (source : String) : String :=
  go (source.length + 1) source.toList true []
where
  go : Nat → List Char → Bool → List Char → String
    | 0, _, _, out => String.ofList out.reverse
    | _, [], _, out => String.ofList out.reverse
    | fuel + 1, c :: rest, atWordStart, out =>
        if whitespace c then
          go fuel rest true (c :: out)
        else if atWordStart then
          if c == '@' then
            go fuel rest false ('@' :: '\n' :: out)
          else
            match structuralWords.find? (fun word => wordPrefix? word (c :: rest)) with
            | some word =>
                let n := word.length
                let actual := (c :: rest).take n
                go fuel ((c :: rest).drop n) false (actual.reverse ++ '\n' :: out)
            | none => go fuel rest false (c :: out)
        else
          go fuel rest false (c :: out)

private def lines (source : String) : List Line :=
  (splitStructural source).splitOn "\n" |>.mapIdx fun number text =>
    { number := number + 1, text := trim text }

private def firstWord? (s : String) : Option (String × String) :=
  let cs := (trim s).toList
  let word := cs.takeWhile (fun c => !whitespace c)
  if word.isEmpty then none
  else
    let rest := cs.drop word.length |>.dropWhile whitespace
    some (String.ofList word, String.ofList rest)

private def head? (s : String) : Option String :=
  firstWord? s |>.map (fun p => lower p.1)

private def tail (s : String) : String := (firstWord? s).map (·.2) |>.getD ""

private def words (s : String) : List String :=
  go s.toList [] []
where
  go : List Char → List Char → List String → List String
    | [], current, out =>
        if current.isEmpty then out.reverse
        else (String.ofList current.reverse :: out).reverse
    | c :: rest, current, out =>
        if whitespace c then
          if current.isEmpty then go rest [] out
          else go rest [] (String.ofList current.reverse :: out)
        else go rest (c :: current) out

private def lineError (line : Line) (message : String) : String :=
  s!"line {line.number}: {message}"

private def identAttrs (name : String) : XmlAttrs :=
  [("org.eventb.core.identifier", name)]

private def targetAttrs (name : String) : XmlAttrs :=
  [("org.eventb.core.target", name)]

private def labelAttrs (label formula : String) (isTheorem : Bool := false) : XmlAttrs :=
  [("org.eventb.core.label", label), ("org.eventb.core.predicate", formula)] ++
    (if isTheorem then [("org.eventb.core.theorem", "true")] else [])

private def assignmentAttrs (label formula : String) : XmlAttrs :=
  [("org.eventb.core.label", label), ("org.eventb.core.assignment", formula)]

private def removeTrailingColon (s : String) : String :=
  if s.endsWith ":" then String.ofList (s.toList.reverse.drop 1 |>.reverse) else s

private structure Labelled where
  label : Option String
  formula : String
  isTheorem : Bool := false

private def leadingLabel? (s : String) : Option (String × String) :=
  let s := trim s
  if !s.startsWith "@" then none
  else
    let cs := s.toList.drop 1
    let label := cs.takeWhile (fun c => !whitespace c)
    if label.isEmpty then none
    else
      let rest := cs.drop label.length |>.dropWhile whitespace
      some (removeTrailingColon (String.ofList label), String.ofList rest)

private def labelled (_generated : String) (source : String) : Except String Labelled := do
  let source := trim source
  let (theoremBefore, source) :=
    match firstWord? source with
    | some (word, rest) => (lower word == "theorem", if lower word == "theorem" then rest else source)
    | none => (false, source)
  let (label, source) :=
    match leadingLabel? source with
    | some (label, rest) => (some label, rest)
    | none => (none, source)
  let (theoremAfter, source) :=
    match firstWord? source with
    | some (word, rest) => (lower word == "theorem", if lower word == "theorem" then rest else source)
    | none => (false, source)
  if source.isEmpty then .error "expected a formula"
  else .ok { label, formula := source, isTheorem := theoremBefore || theoremAfter }

private def labelOnly? (source : String) : Option String :=
  leadingLabel? source |>.filter (·.2.isEmpty) |>.map (·.1)

private inductive PredicateKind where
  | axiom
  | theoremAxiom
  | invariant
  | theoremInvariant
  | guard
  | witness

private def predicateElem (kind : PredicateKind) (label formula : String) : Elem :=
  match kind with
  | .axiom => .axiom (labelAttrs label formula) []
  | .theoremAxiom => .axiom (labelAttrs label formula true) []
  | .invariant => .invariant (labelAttrs label formula) []
  | .theoremInvariant => .invariant (labelAttrs label formula true) []
  | .guard => .guard (labelAttrs label formula) []
  | .witness => .witness (labelAttrs label formula) []

private def skipBlank : List Line → List Line
  | [] => []
  | line :: rest => if line.text.isEmpty then skipBlank rest else line :: rest

private def isOneOf (value : String) (values : List String) : Bool := values.contains value

private def predicateBoundary (stops : List String) (line : Line) : Bool :=
  match head? line.text with
  | some head => isOneOf head stops
  | none => false

private def predicateLine (kind : PredicateKind) (index : Nat) (line : Line)
    (rest : List Line) : Except String (Elem × List Line) := do
  if lower line.text == "theorem" then
    match skipBlank rest with
    | next :: remaining =>
        let parsed ← labelled ("thm" ++ toString index) ("theorem " ++ next.text)
        let actualKind := match kind with
          | .axiom => .theoremAxiom
          | .invariant => .theoremInvariant
          | other => other
        return (predicateElem actualKind (parsed.label.getD ("thm" ++ toString index))
          parsed.formula, remaining)
    | [] => .error (lineError line "theorem is not followed by a formula")
  else
  match labelled (match kind with
    | .axiom | .theoremAxiom => "axm" ++ toString index
    | .invariant | .theoremInvariant => "inv" ++ toString index
    | .guard => "grd" ++ toString index
    | .witness => "wit" ++ toString index) line.text with
  | .ok parsed =>
      let actualKind := match kind, parsed.isTheorem with
        | .axiom, true => .theoremAxiom
        | .invariant, true => .theoremInvariant
        | _, _ => kind
      return (predicateElem actualKind (parsed.label.getD (match kind with
        | .axiom | .theoremAxiom => "axm" ++ toString index
        | .invariant | .theoremInvariant => "inv" ++ toString index
        | .guard => "grd" ++ toString index
        | .witness => "wit" ++ toString index)) parsed.formula, rest)
  | .error _ =>
      match labelOnly? line.text, skipBlank rest with
      | some label, next :: remaining =>
          if predicateBoundary ["end", "extends", "sets", "constants", "axioms", "theorems",
              "refines", "sees", "variables", "invariants", "variant", "events"] next then
            .error (lineError line "label is not followed by a formula")
          else
            let parsed ← labelled label ("@" ++ label ++ " " ++ next.text)
            return (predicateElem kind (parsed.label.getD label) parsed.formula, remaining)
      | _, _ => .error (lineError line s!"invalid labelled formula `{line.text}`")

private def parsePredicates (kind : PredicateKind) (stops : List String) : Nat → Nat →
    List Line → Except String (List Elem × List Line)
  | 0, _, _ => .error "Rossi parser ran out of fuel"
  | fuel + 1, index, source =>
      let source := skipBlank source
      match source with
      | [] => .error "unexpected end of input; expected END"
      | line :: rest =>
          if predicateBoundary stops line then
            .ok ([], source)
          else do
            let (elem, remaining) ← predicateLine kind index line rest
            let (more, remaining) ← parsePredicates kind stops fuel (index + 1) remaining
            return (elem :: more, remaining)

private def parseActions : Nat → Nat → List Line → Except String (List Elem × List Line)
  | 0, _, _ => .error "Rossi parser ran out of fuel"
  | fuel + 1, index, source =>
      let source := skipBlank source
      match source with
      | [] => .error "unexpected end of input; expected END"
      | line :: rest =>
          if head? line.text == some "end" then .ok ([], source)
          else do
            let parsed ← labelled ("act" ++ toString index) line.text
            let label := parsed.label.getD ("act" ++ toString index)
            let (more, remaining) ← parseActions fuel (index + 1) rest
            return (.action (assignmentAttrs label parsed.formula) [] :: more, remaining)

private def sectionData (line : Line) (rest : List Line) : String × List Line :=
  if !(tail line.text).isEmpty then (tail line.text, rest)
  else
    match skipBlank rest with
    | next :: remaining => (next.text, remaining)
    | [] => ("", [])

private def collectNames : Nat → List String → List Line → List String × List Line
  | 0, _, source => ([], source)
  | fuel + 1, stops, source =>
      let source := skipBlank source
      match source with
      | [] => ([], [])
      | line :: rest =>
          if predicateBoundary stops line then ([], source)
          else
            let (more, remaining) := collectNames fuel stops rest
            (words line.text ++ more, remaining)

private def collectText : Nat → List String → List Line → List String × List Line
  | 0, _, source => ([], source)
  | fuel + 1, stops, source =>
      let source := skipBlank source
      match source with
      | [] => ([], [])
      | line :: rest =>
          if predicateBoundary stops line then ([], source)
          else
            let (more, remaining) := collectText fuel stops rest
            (line.text :: more, remaining)

private def names (stops : List String) (line : Line) (rest : List Line) :
    Except String (List String × List Line) :=
  let first := if (tail line.text).isEmpty then [] else
    [{ number := line.number, text := tail line.text }]
  let (result, remaining) := collectNames (rest.length + 2) stops (first ++ rest)
  if result.isEmpty then .error (lineError line "expected one or more names")
  else .ok (result, remaining)

private def setTokens (s : String) : List String :=
  go s.toList [] []
where
  flush (current : List Char) (out : List String) : List String :=
    if current.isEmpty then out else String.ofList current.reverse :: out
  go : List Char → List Char → List String → List String
    | [], current, out => (flush current out).reverse
    | c :: rest, current, out =>
        if whitespace c then go rest [] (flush current out)
        else if c == '=' || c == '{' || c == '}' || c == ',' then
          let out := flush current out
          go rest [] (String.ofList [c] :: out)
        else go rest (c :: current) out

private def parseSetDecls : Nat → List String → Except String (List (String × Option String))
  | 0, _ => .error "too many set declarations"
  | _, [] => .ok []
  | fuel + 1, name :: "=" :: "{" :: rest => do
      let (members, remaining) ← takeSetMembers [] rest
      let more ← parseSetDecls fuel remaining
      return (name, some ("{" ++ String.intercalate " " members ++ "}")) :: more
  | fuel + 1, name :: rest => do
      let more ← parseSetDecls fuel rest
      return (name, none) :: more
where
  takeSetMembers : List String → List String → Except String (List String × List String)
    | _, [] => .error "enumerated set is missing `}`"
    | members, "}" :: rest => .ok (members, rest)
    | members, token :: rest => takeSetMembers (members ++ [token]) rest

private def setElements (line : Line) (rest : List Line) : Except String (List Elem × List Line) := do
  let (text, remaining) := sectionData line rest
  let (continuations, remaining) := collectText (remaining.length + 2)
    ["extends", "sets", "constants", "axioms", "theorems", "end"] remaining
  let declarations ← parseSetDecls (text.length + 1)
    (setTokens (String.intercalate " " (text :: continuations)))
  if declarations.isEmpty then .error (lineError line "expected one or more sets")
  else
    return (declarations.map fun (name, expression) =>
      let attrs := match expression with
        | some value => [("org.eventb.core.expression", value)]
        | none => []
      .carrierSet (identAttrs name ++ attrs) [], remaining)

private def parseContextBody : Nat → List Elem → List Line →
    Except String (Elem × List Line)
  | 0, _, _ => .error "Rossi parser ran out of fuel"
  | fuel + 1, children, source =>
      let source := skipBlank source
      match source with
      | [] => .error "unexpected end of input; context is missing END"
      | line :: rest =>
          match head? line.text with
          | some "end" => .ok (.contextFile [] children, rest)
          | some "extends" => do
              let (ns, remaining) ← names
                ["extends", "sets", "constants", "axioms", "theorems", "end"] line rest
              parseContextBody fuel (children ++ ns.map fun n =>
                .extendsContext (targetAttrs n) []) remaining
          | some "sets" => do
              let (sets, remaining) ← setElements line rest
              parseContextBody fuel (children ++ sets) remaining
          | some "constants" => do
              let (ns, remaining) ← names
                ["extends", "sets", "constants", "axioms", "theorems", "end"] line rest
              parseContextBody fuel (children ++ ns.map fun n =>
                .constant (identAttrs n) []) remaining
          | some "axioms" => do
              let source := if (tail line.text).isEmpty then rest else
                ({ number := line.number, text := tail line.text } :: rest)
              let (items, remaining) ← parsePredicates .axiom
                ["extends", "sets", "constants", "axioms", "theorems", "end"] fuel 1 source
              parseContextBody fuel (children ++ items) remaining
          | some "theorems" => do
              let source := if (tail line.text).isEmpty then rest else
                ({ number := line.number, text := tail line.text } :: rest)
              let (items, remaining) ← parsePredicates .theoremAxiom
                ["extends", "sets", "constants", "axioms", "theorems", "end"] fuel 1 source
              parseContextBody fuel (children ++ items) remaining
          | _ => .error (lineError line "unexpected context clause")

private def parseContext (line : Line) (rest : List Line) : Except String (Component × List Line) := do
  let (name, headerTail) ← match firstWord? (tail line.text) with
    | some pair => pure pair
    | none => .error (lineError line "CONTEXT needs a component name")
  let source := if headerTail.isEmpty then rest else
    ({ number := line.number, text := headerTail } :: rest)
  let (root, remaining) ← parseContextBody (source.length + 1) [] source
  return ({ name, model := { root } }, remaining)

private def convergence (status : String) : Option String :=
  if status == "ordinary" then some "0"
  else if status == "convergent" then some "1"
  else if status == "anticipated" then some "2"
  else none

private def parseEventHeader (line : Line) : Except String (String × Option String × String) := do
  let (first, rest) ← match firstWord? line.text with
    | some pair => pure pair
    | none => .error (lineError line "EVENT needs a name")
  let (status, eventText) := match convergence (lower first) with
    | some value => (some value, rest)
    | none => (none, line.text)
  let eventRest := if status.isSome then tail eventText else rest
  let (name, afterName) ← match firstWord? eventRest with
    | some pair => pure pair
    | none => .error (lineError line "EVENT needs a name")
  return (name, status, afterName)

private def eventStatus (line : Line) : Except String (Option String × String) := do
  let (word, rest) ← match firstWord? (tail line.text) with
    | some pair => pure pair
    | none => .error (lineError line "STATUS expects ordinary, convergent, or anticipated")
  match convergence (lower word) with
  | some value => pure (some value, rest)
  | none => .error (lineError line "STATUS expects ordinary, convergent, or anticipated")

private def parseEventBody : Nat → String → Option String → List Elem → List Line →
    Except String (Elem × List Line)
  | 0, _, _, _, _ => .error "Rossi parser ran out of fuel"
  | fuel + 1, name, status, children, source =>
      let source := skipBlank source
      match source with
      | [] => .error "unexpected end of input; event is missing END"
      | line :: rest =>
          match head? line.text with
          | some "end" =>
              let attrs := [("org.eventb.core.label", name)] ++ match status with
                | some value => [("org.eventb.core.convergence", value)]
                | none => []
              .ok (.event attrs children, rest)
          | some "status" => do
              let (value, afterStatus) ← eventStatus line
              let source := if afterStatus.isEmpty then rest else
                ({ number := line.number, text := afterStatus } :: rest)
              parseEventBody fuel name value children source
          | some "refines" => do
              let (target, remaining) ← names
                ["any", "where", "when", "with", "witness", "then", "begin", "end"] line rest
              match target with
              | [target] =>
                  let child : Elem := .refinesEvent (targetAttrs target) []
                  parseEventBody fuel name status (children ++ [child]) remaining
              | _ => .error (lineError line
                  s!"REFINES expects one event name, got {String.intercalate "," target}")
          | some "extends" => do
              let (target, remaining) ← names
                ["any", "where", "when", "with", "witness", "then", "begin", "end"] line rest
              match target with
              | [target] =>
                  let child : Elem := .refinesEvent (targetAttrs target ++
                    [("org.eventb.core.extended", "true")]) []
                  parseEventBody fuel name status (children ++ [child]) remaining
              | _ => .error (lineError line
                  s!"EXTENDS expects one event name, got {String.intercalate "," target}")
          | some "any" => do
              let (ns, remaining) ← names
                ["where", "when", "with", "witness", "then", "begin", "end"] line rest
              parseEventBody fuel name status
                (children ++ ns.map fun n => .parameter (identAttrs n) []) remaining
          | some "where" | some "when" => do
              let source := if (tail line.text).isEmpty then rest else
                ({ number := line.number, text := tail line.text } :: rest)
              let (items, remaining) ← parsePredicates .guard
                ["where", "when", "with", "witness", "then", "begin", "end"] fuel 1 source
              parseEventBody fuel name status (children ++ items) remaining
          | some "with" | some "witness" => do
              let source := if (tail line.text).isEmpty then rest else
                ({ number := line.number, text := tail line.text } :: rest)
              let (items, remaining) ← parsePredicates .witness
                ["where", "when", "with", "witness", "then", "begin", "end"] fuel 1 source
              parseEventBody fuel name status (children ++ items) remaining
          | some "then" | some "begin" => do
              let source := if (tail line.text).isEmpty then rest else
                ({ number := line.number, text := tail line.text } :: rest)
              let (items, remaining) ← parseActions fuel 1 source
              parseEventBody fuel name status (children ++ items) remaining
          | _ => .error (lineError line "unexpected event clause")

private def parseEvent (line : Line) (rest : List Line) : Except String (Elem × List Line) := do
  let (name, status, headerTail) ← parseEventHeader line
  let source := if headerTail.isEmpty then rest else
    ({ number := line.number, text := headerTail } :: rest)
  parseEventBody (source.length + 1) name status [] source

private def parseEvents : Nat → List Elem → List Line → Except String (List Elem × List Line)
  | 0, _, _ => .error "Rossi parser ran out of fuel"
  | fuel + 1, events, source =>
      let source := skipBlank source
      match source with
      | [] => .error "unexpected end of input; EVENTS is missing machine END"
      | line :: rest =>
          if head? line.text == some "end" then
            if events.isEmpty then .error (lineError line "EVENTS needs at least one event")
            else .ok (events, source)
          else if (convergence (lower line.text)).isSome && (tail line.text).isEmpty then
            match skipBlank rest with
            | next :: remaining =>
                if head? next.text == some "event" then do
                  let header := { number := line.number, text := line.text ++ " " ++ next.text }
                  let (event, after) ← parseEvent header remaining
                  parseEvents fuel (events ++ [event]) after
                else
                  .error (lineError line "event status must precede EVENT")
            | [] => .error (lineError line "event status must precede EVENT")
          else do
            let (event, remaining) ← parseEvent line rest
            parseEvents fuel (events ++ [event]) remaining

private def parseMachineBody : Nat → List Elem → List Line →
    Except String (Elem × List Line)
  | 0, _, _ => .error "Rossi parser ran out of fuel"
  | fuel + 1, children, source =>
      let source := skipBlank source
      match source with
      | [] => .error "unexpected end of input; machine is missing END"
      | line :: rest =>
          match head? line.text with
          | some "end" => .ok (.machineFile [] children, rest)
          | some "refines" => do
              let (target, remaining) ← names
                ["refines", "sees", "variables", "invariants", "theorems", "variant", "events", "end"]
                line rest
              match target with
              | [target] =>
                  let child : Elem := .refinesMachine (targetAttrs target) []
                  parseMachineBody fuel (children ++ [child]) remaining
              | _ => .error (lineError line "REFINES expects one machine name")
          | some "sees" => do
              let (ns, remaining) ← names
                ["refines", "sees", "variables", "invariants", "theorems", "variant", "events", "end"]
                line rest
              parseMachineBody fuel (children ++ ns.map fun n =>
                .seesContext (targetAttrs n) []) remaining
          | some "variables" => do
              let (ns, remaining) ← names
                ["refines", "sees", "variables", "invariants", "theorems", "variant", "events", "end"]
                line rest
              parseMachineBody fuel (children ++ ns.map fun n =>
                .variable (identAttrs n) []) remaining
          | some "invariants" => do
              let source := if (tail line.text).isEmpty then rest else
                ({ number := line.number, text := tail line.text } :: rest)
              let (items, remaining) ← parsePredicates .invariant
                ["refines", "sees", "variables", "invariants", "theorems", "variant", "events", "end"]
                fuel 1 source
              parseMachineBody fuel (children ++ items) remaining
          | some "theorems" => do
              let source := if (tail line.text).isEmpty then rest else
                ({ number := line.number, text := tail line.text } :: rest)
              let (items, remaining) ← parsePredicates .theoremInvariant
                ["refines", "sees", "variables", "invariants", "theorems", "variant", "events", "end"]
                fuel 1 source
              parseMachineBody fuel (children ++ items) remaining
          | some "variant" => do
              let (text, remaining) := sectionData line rest
              if text.isEmpty then .error (lineError line "VARIANT needs an expression")
              else
                let child : Elem := .variant [("org.eventb.core.expression", text)] []
                parseMachineBody fuel (children ++ [child]) remaining
          | some "events" => do
              let (events, remaining) ← parseEvents fuel [] rest
              parseMachineBody fuel (children ++ events) remaining
          | _ => .error (lineError line "unexpected machine clause")

private def parseMachine (line : Line) (rest : List Line) : Except String (Component × List Line) := do
  let (name, headerTail) ← match firstWord? (tail line.text) with
    | some pair => pure pair
    | none => .error (lineError line "MACHINE needs a component name")
  let source := if headerTail.isEmpty then rest else
    ({ number := line.number, text := headerTail } :: rest)
  let (root, remaining) ← parseMachineBody (source.length + 1) [] source
  return ({ name, model := { root } }, remaining)

private def parseComponents : Nat → List Line → Except String (List Component)
  | 0, _ => .error "Rossi parser ran out of fuel"
  | fuel + 1, source =>
      let source := skipBlank source
      match source with
      | [] => .ok []
      | line :: rest =>
          match head? line.text with
          | some "context" => do
              let (component, remaining) ← parseContext line rest
              let more ← parseComponents fuel remaining
              return component :: more
          | some "machine" => do
              let (component, remaining) ← parseMachine line rest
              let more ← parseComponents fuel remaining
              return component :: more
          | _ => .error (lineError line "expected CONTEXT or MACHINE")

def parse (source : String) : Except String (List Component) := do
  let source ← stripComments source
  let result ← parseComponents ((source.length * 2) + 1) (lines source)
  if result.isEmpty then .error "Rossi input contains no CONTEXT or MACHINE"
  else return result

def parseModel (source : String) : Except String (List Model) :=
  parse source |>.map (·.map (·.model))

def read (path : System.FilePath) : IO (Except String (List Component)) := do
  try
    let source ← IO.FS.readFile path
    return parse source
  catch error =>
    return .error s!"{path}: could not be read: {error}"

end EventB.Rossi
