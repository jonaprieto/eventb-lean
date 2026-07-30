import EventB.Rodin.Model

namespace EventB.Gates

open EventB.Rodin

structure FileResult where
  path : String
  status : String
  model : Option RodinModel := none

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

private def writeBaseline (lines : List String) : IO Unit := do
  IO.FS.writeFile "baseline/parse.tsv" (String.intercalate "\n" lines ++ "\n")

private def writeStatus (results : List FileResult) (inventory : List (String × Nat)) :
    IO Unit := do
  let passed := results.countP (fun result => result.status == "PASS")
  let files := s!"P0 reader: {passed}/{results.length} files pass"
  let counts := inventory.map (fun (name, count) => s!"{name}: {count}")
  IO.FS.writeFile "STATUS.md"
    ("# Event-B Lean status\n\n" ++ files ++ "\n\n## Element inventory\n\n" ++
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
  IO.println s!"P0 reader: {filesPassed}/{results.length}"
  if !inventoryOK then
    IO.eprintln s!"element inventory mismatch: {inventory}"
  if args.contains "--histogram" then
    for (reason, count) in histogram results do
      IO.println s!"{count}\t{reason}"
  if args.contains "--status" then
    writeStatus results inventory
  let parseOK := results.all (fun result => result.status == "PASS")
  if args.contains "--bless" then
    if parseOK && inventoryOK then
      writeBaseline actual
    else
      IO.eprintln "refusing to bless a failed P0 gate"
      return 1
  else
    let baseline ← try IO.FS.readFile "baseline/parse.tsv" catch _ => pure ""
    let baselineOK ← baselineDiff (nonemptyLines baseline) actual
    if !baselineOK then
      return 1
  if parseOK && inventoryOK then
    return 0
  return 1

end EventB.Gates

-- Must sit at the top level: `lean_exe gates` links against `main`, not
-- `EventB.Gates.main`.
def main (args : List String) : IO UInt32 := EventB.Gates.run args
