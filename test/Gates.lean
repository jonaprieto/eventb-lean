import EventB.Model
import EventB.Formula.Parse

namespace EventB.Gates

open EventB
open EventB.Formula

structure FileResult where
  path : String
  status : String
  model : Option Model := none

def expectedInventory : List (String × Nat) :=
  [("guard", 467), ("action", 410), ("event", 308), ("refinesEvent", 222),
   ("variable", 180), ("invariant", 142), ("parameter", 137), ("axiom", 68),
   ("constant", 33), ("machineFile", 22), ("seesContext", 22),
   ("refinesMachine", 19), ("extendsContext", 17), ("contextFile", 16),
   ("witness", 15), ("carrierSet", 6)]

private def isSource (path : System.FilePath) : Bool :=
  path.toString.endsWith ".bum" || path.toString.endsWith ".buc"

private def sourceFiles : IO (List System.FilePath) := do
  let mut paths : List System.FilePath := []
  let corpus : System.FilePath := "corpus"
  for project in ← corpus.readDir do
    -- corpus/ holds MANIFEST.tsv alongside the project directories.
    if ← project.path.isDir then
      for entry in ← project.path.readDir do
        if isSource entry.path then
          paths := entry.path :: paths
  pure (paths.mergeSort (fun left right => left.toString < right.toString))

private def shortReason (reason : String) : String :=
  reason.splitOn "\n" |>.head?.getD "parse failed"

private def checkFile (path : System.FilePath) : IO FileResult := do
  try
    let source ← IO.FS.readBinFile path
    let parsed :=
      if path.toString.endsWith ".bum" then
        parseMachine source
      else
        parseContext source
    match parsed with
    | .ok model => pure { path := path.toString, status := "PASS", model := some model }
    | .error reason =>
        pure { path := path.toString, status := "FAIL:" ++ shortReason reason }
  catch err =>
    pure { path := path.toString, status := "FAIL:IO " ++ err.toString }

private def sumInventory : List (String × Nat) → List (String × Nat) →
    List (String × Nat)
  | [], _ => []
  | _, [] => []
  | (name, left) :: xs, (_, right) :: ys =>
      (name, left + right) :: sumInventory xs ys

private def totalInventory (results : List FileResult) : List (String × Nat) :=
  results.foldl
    (fun total result =>
      match result.model with
      | some model => sumInventory total model.inventory
      | none => total)
    (expectedInventory.map (fun (name, _) => (name, 0)))

private def histogramAdd (reason : String) : List (String × Nat) → List (String × Nat)
  | [] => [(reason, 1)]
  | (name, count) :: rest =>
      if name == reason then
        (name, count + 1) :: rest
      else
        (name, count) :: histogramAdd reason rest

private def histogram (results : List FileResult) : List (String × Nat) :=
  (results.foldl
    (fun counts result =>
      if result.status.startsWith "FAIL:" then
        histogramAdd result.status counts
      else
        counts)
    []).mergeSort (fun left right =>
      if left.2 == right.2 then left.1 < right.1 else right.2 < left.2)


/-- P1 gate. Every formula must parse, and reparsing the printed form must give back the
same tree: a printer that lost an operator, or a precedence bug that quietly rebracketed,
would pass a parse-only check. Denominator 1102, from `scripts/manifest.py`. -/
private def formulaCount : Nat := 1102

private structure FormulaResult where
  key    : String
  status : String

private def checkFormula (file label formula : String) : FormulaResult :=
  let key := file ++ "\t" ++ label
  match Formula.parse formula with
  | .error reason => { key := key, status := "FAIL:" ++ reason }
  | .ok term =>
      match Formula.parse (Formula.print term) with
      | .error reason => { key := key, status := "FAIL:reprint " ++ reason }
      | .ok again =>
          if again == term then { key := key, status := "PASS" }
          else { key := key, status := "FAIL:round-trip differs" }

private def formulaResults (results : List FileResult) : List FormulaResult :=
  results.flatMap fun result =>
    match result.model with
    | none => []
    | some model => model.formulas.map (fun (label, f) => checkFormula result.path label f)

private def formulaHistogram (results : List FormulaResult) : List (String × Nat) :=
  (results.foldl
    (fun counts result =>
      if result.status.startsWith "FAIL:" then histogramAdd result.status counts
      else counts)
    []).mergeSort (fun left right =>
      if left.2 == right.2 then left.1 < right.1 else right.2 < left.2)

private def nonemptyLines (source : String) : List String :=
  source.splitOn "\n" |>.filter (fun line => !line.isEmpty)

private def baselineDiff (baseline actual : List String) : IO Bool := do
  if baseline == actual then
    pure true
  else
    IO.eprintln "parse baseline mismatch:"
    for line in actual do
      if !baseline.contains line then
        IO.eprintln s!"+ {line}"
    for line in baseline do
      if !actual.contains line then
        IO.eprintln s!"- {line}"
    pure false

private def writeBaseline (path : String) (lines : List String) : IO Unit := do
  IO.FS.writeFile path (String.intercalate "\n" lines ++ "\n")

private def writeStatus (results : List FileResult) (formulas : List FormulaResult)
    (inventory : List (String × Nat)) : IO Unit := do
  let passed := results.countP (fun result => result.status == "PASS")
  let fpass := formulas.countP (fun result => result.status == "PASS")
  let counts := inventory.map (fun (name, count) => s!"| {name} | {count} |")
  IO.FS.writeFile "STATUS.md"
    ("# STATUS\n\nGenerated by `lake exe gates --status`. Do not edit; see AGENTS.md " ++
      "rule 1.\n\n| Phase | Gate | Actual | Target |\n| --- | --- | --- | --- |\n" ++
      s!"| P0 reader | files read losslessly | {passed}/{results.length} | " ++
        s!"{results.length} |\n" ++
      s!"| P1 formula parser | formulas parsed and round-tripped | {fpass}/{formulas.length}" ++
        s!" | {formulaCount} |\n" ++
      "| P2 typechecker | `.bpo` type assertions reproduced | 0/2019 | 2019 |\n" ++
      "| P3 POG | `.bpo` PO sequents reproduced | 0/1133 | 1133 |\n" ++
      "| P4 provers | discharge rate vs Rodin `.bps` | not started | within 20pt |\n" ++
      "\n## Element census\n\nSummed over every corpus source file. A reader that " ++
      "silently dropped an element would\nshow up here as a shortfall, which a per-file " ++
      "PASS/FAIL cannot detect.\n\n| element | count |\n| --- | --- |\n" ++
      String.intercalate "\n" counts ++ "\n")

private def run (args : List String) : IO UInt32 := do
  let files ← sourceFiles
  let mut acc : List FileResult := []
  for path in files do
    acc := (← checkFile path) :: acc
  let results := acc.reverse
  let actual := results.map (fun result => result.path ++ "\t" ++ result.status)
  let inventory := totalInventory results
  let filesPassed := results.countP (fun result => result.status == "PASS")
  let inventoryOK := inventory == expectedInventory
  let formulas := formulaResults results
  let formulaPassed := formulas.countP (fun result => result.status == "PASS")
  let formulaActual := formulas.map (fun result => result.key ++ "\t" ++ result.status)
  let formulaCountOK := formulas.length == formulaCount
  IO.println s!"P0 reader: {filesPassed}/{results.length}"
  IO.println s!"P1 formulas: {formulaPassed}/{formulas.length}"
  if !formulaCountOK then
    IO.eprintln s!"formula count {formulas.length}, expected {formulaCount}"
  if !inventoryOK then
    IO.eprintln s!"element inventory mismatch: {inventory}"
  if args.contains "--histogram" then
    for (reason, count) in histogram results do
      IO.println s!"{count}\t{reason}"
    for (reason, count) in formulaHistogram formulas do
      IO.println s!"{count}\t{reason}"
  if args.contains "--status" then
    writeStatus results formulas inventory
  let parseOK := results.all (fun result => result.status == "PASS")
  if args.contains "--bless" then
    -- P0 must be perfect to bless, since a dropped file would silently shrink the P1
    -- denominator. P1 blesses whatever it currently reaches: that is the ratchet.
    if parseOK && inventoryOK && formulaCountOK then
      writeBaseline "baseline/parse.tsv" actual
      writeBaseline "baseline/formula.tsv" formulaActual
    else
      IO.eprintln "refusing to bless a failed P0 gate"
      return 1
    return 0
  let baseline ← try IO.FS.readFile "baseline/parse.tsv" catch _ => pure ""
  let baselineOK ← baselineDiff (nonemptyLines baseline) actual
  let fbaseline ← try IO.FS.readFile "baseline/formula.tsv" catch _ => pure ""
  let fbaselineOK ← baselineDiff (nonemptyLines fbaseline) formulaActual
  if !baselineOK || !fbaselineOK then
    return 1
  if parseOK && inventoryOK && formulaCountOK then
    return 0
  return 1

end EventB.Gates

-- Must sit at the top level: `lean_exe gates` links against `main`, not
-- `EventB.Gates.main`.
def main (args : List String) : IO UInt32 := EventB.Gates.run args
