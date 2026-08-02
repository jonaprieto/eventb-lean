import EventB.POG
import EventB.Prover.Local
import EventB.Rossi
import EventB.Theory.Rodin

namespace EventB.Cli

open EventB
open EventB.Formula
open EventB.POG
open EventB.Typing

private def isSource (path : System.FilePath) : Bool :=
  path.toString.endsWith ".bum" || path.toString.endsWith ".buc"

private def isRossi (path : System.FilePath) : Bool :=
  path.toString.endsWith ".eventb"

private def isBpo (path : System.FilePath) : Bool :=
  path.toString.endsWith ".bpo"

private def isTheory (path : System.FilePath) : Bool :=
  path.toString.endsWith ".tuf"

private def stem (path : System.FilePath) : String :=
  ((path.toString.splitOn "/").getLast!).splitOn "." |>.head!

private def sourceFiles (dir : System.FilePath) : IO (List System.FilePath) := do
  let mut paths : List System.FilePath := []
  for entry in ← dir.readDir do
    if !(← entry.path.isDir) && isSource entry.path then
      paths := entry.path :: paths
  return paths.mergeSort (fun left right => left.toString < right.toString)

private partial def rossiFiles (dir : System.FilePath) : IO (List System.FilePath) := do
  let mut paths : List System.FilePath := []
  for entry in ← dir.readDir do
    if ← entry.path.isDir then
      paths := (← rossiFiles entry.path) ++ paths
    else if isRossi entry.path then
      paths := entry.path :: paths
  return paths.mergeSort (fun left right => left.toString < right.toString)

private partial def theoryFiles (dir : System.FilePath) : IO (List System.FilePath) := do
  let mut paths : List System.FilePath := []
  for entry in ← dir.readDir do
    if ← entry.path.isDir then
      paths := (← theoryFiles entry.path) ++ paths
    else if isTheory entry.path then
      paths := entry.path :: paths
  return paths.mergeSort (fun left right => left.toString < right.toString)

private def bpoFiles (dir : System.FilePath) : IO (List System.FilePath) := do
  let mut paths : List System.FilePath := []
  for entry in ← dir.readDir do
    if !(← entry.path.isDir) && isBpo entry.path then
      paths := entry.path :: paths
  return paths.mergeSort (fun left right => left.toString < right.toString)

private structure Source where
  path : System.FilePath
  name : String
  model : Model

private def projectComponent (roots : List String) (source : Source) : Component :=
  { name := source.name, elem := source.model.root, theories := roots }

private structure ProjectData where
  project : Project
  sources : List Source
  theory : Theory.Env
  errors : List String

private def loadTheories (paths : List System.FilePath) : IO (Theory.Env × List String) := do
  let mut pending := paths
  let mut env := Theory.empty
  let mut errors : List String := []
  while !pending.isEmpty do
    let mut next : List (System.FilePath × String) := []
    let mut progressed := false
    for path in pending do
      try
        let source ← IO.FS.readFile path
        match Theory.Rodin.importSpec env source with
        | .ok spec =>
            match Theory.add env spec with
            | .ok extended =>
                env := extended
                progressed := true
            | .error error => errors := s!"{path}: {error}" :: errors
        | .error error =>
            if error.endsWith "is not registered" then
              next := (path, error) :: next
            else
              errors := s!"{path}: {error}" :: errors
      catch error => errors := s!"{path}: could not be read: {error}" :: errors
    if !progressed && next.length == pending.length then
      for (path, error) in next do
        errors := s!"{path}: {error}" :: errors
      pending := []
    else
      pending := next.reverse.map (·.1)
  return (env, errors.reverse)

private def readSource (path : System.FilePath) : IO (Except String Source) := do
  try
    match ← readModel path with
    | .ok model =>
        let correctRoot := if path.toString.endsWith ".bum" then
            match model.root with
            | .machineFile _ _ => true
            | _ => false
          else
            match model.root with
            | .contextFile _ _ => true
            | _ => false
        if correctRoot then
          return .ok { path := path, name := stem path, model := model }
        let expected := if path.toString.endsWith ".bum" then "machineFile" else
          "contextFile"
        return .error s!"{path}: expected {expected} root"
    | .error reason =>
        return .error s!"{path}: invalid Event-B file: {reason}"
  catch err =>
    return .error s!"{path}: could not be read: {err}"

private def readRossi (path : System.FilePath) : IO (Except String (List Source)) := do
  match ← Rossi.read path with
  | .error reason => return .error s!"{path}: invalid Rossi Event-B file: {reason}"
  | .ok components =>
      return .ok (components.map fun component =>
        { path := path, name := component.name, model := component.model })

private def loadProject (path : System.FilePath) : IO ProjectData := do
  let mut sources : List Source := []
  let mut errors : List String := []
  let (theory, theoryErrors) ← if ← path.isDir then
      loadTheories (← theoryFiles path)
    else
      pure (Theory.empty, [])
  errors := theoryErrors
  if ← path.isDir then
    for sourcePath in ← sourceFiles path do
      match ← readSource sourcePath with
      | .ok source => sources := source :: sources
      | .error reason => errors := reason :: errors
    for sourcePath in ← rossiFiles path do
      match ← readRossi sourcePath with
      | .ok parsed => sources := parsed.reverse ++ sources
      | .error reason => errors := reason :: errors
  else if isRossi path then
    match ← readRossi path with
    | .ok parsed => sources := parsed.reverse
    | .error reason => errors := reason :: errors
  else
    errors := s!"{path}: expected a project directory or .eventb file" :: errors
  let orderedSources := sources.reverse
  let mut uniqueSources : List Source := []
  let mut duplicateErrors : List String := []
  for source in orderedSources do
    if uniqueSources.any (fun existing => existing.name == source.name) then
      duplicateErrors := s!"{source.path}: duplicate component `{source.name}`" :: duplicateErrors
    else
      uniqueSources := uniqueSources ++ [source]
  let roots := theory.theories.filter (·.name != Theory.core.name) |>.map (·.name)
  let project : Project := uniqueSources.map (projectComponent roots)
  return ProjectData.mk project uniqueSources theory (errors.reverse ++ duplicateErrors.reverse)

private def formulaErrorLabel (model : Model) (error : String) : Option String :=
  model.formulas.find? (fun pair =>
    match pair with
    | (_label, formula) =>
        match Formula.parse formula with
        | .error reason => error == "parse: " ++ reason
        | .ok term =>
            let marker := "unbound identifier "
            error.startsWith marker &&
              (EventB.POG.identifiers term).contains
                (error.drop marker.length).toString)
  |>.map (·.1)

private def formatTypeError (source : Source) (error : String) : String :=
  let reason := if error.startsWith "parse: " then error.drop 7 else error
  match formulaErrorLabel source.model error with
  | some label => s!"{source.path}: element {label}: {reason}"
  | none => s!"{source.path}: typechecking failed: {reason}"

private def recoverableTypeError (error : String) : Bool :=
  error.startsWith "unbound identifier "

private def typeErrors (data : ProjectData) (source : Source) : List String :=
  match inferComponentIn data.theory data.project source.name with
  | .error error => [formatTypeError source error]
  | .ok (_, errors) => errors.filter (fun error => !recoverableTypeError error)
      |>.map (formatTypeError source)

private def typeWarnings (data : ProjectData) (source : Source) : List String :=
  match inferComponentIn data.theory data.project source.name with
  | .error _ => []
  | .ok (_, errors) =>
      let messages := errors.filter recoverableTypeError |>.map (formatTypeError source)
      messages.foldl (fun unique message =>
        if unique.contains message then unique else unique ++ [message]) []

private structure Report where
  source : Source
  obligations : List Obligation
  errors : List String
  warnings : List String

private def reports (data : ProjectData) : List Report :=
  data.sources.map fun source =>
    { source := source
      obligations := generateIn data.theory data.project source.name
      errors := typeErrors data source
      warnings := typeWarnings data source }

private def fatalErrors (data : ProjectData) (rs : List Report) : List String :=
  data.errors ++ rs.flatMap (·.errors)

private def kinds : List String := ["INV", "WD", "GRD", "SIM", "THM", "WFIS", "WWD"]

private def parseKinds (value : String) : Except String (List String) :=
  let values := value.splitOn ","
  if values.isEmpty || values.any (fun kind => !kinds.contains kind) then
    .error s!"unknown obligation class in --kind {value}; use {String.intercalate "," kinds}"
  else
    .ok values

private structure CheckArgs where
  dir : System.FilePath
  json : Bool := false
  kinds : Option (List String) := none
  machine : Option String := none

private def printCheckDiagnostics (args : CheckArgs) (data : ProjectData)
    (rs : List Report) : IO Unit := do
  for error in fatalErrors data rs do
    IO.eprintln s!"eventb: error: {error}"
  let selectedReports := rs.filter fun report =>
    match args.machine with
    | none => true
    | some name => report.source.name == name
  for warning in selectedReports.flatMap (·.warnings) do
    IO.eprintln s!"eventb: warning: {warning}"

private def parseCheckOptions : List String → CheckArgs → Except String (Option CheckArgs)
  | [], args => .ok (some args)
  | "--help" :: _, _ => .ok none
  | "-h" :: _, _ => .ok none
  | "--json" :: rest, args => parseCheckOptions rest { args with json := true }
  | "--kind" :: [], _ => .error "--kind needs a comma-separated class list"
  | "--kind" :: value :: rest, args => do
      let selected ← parseKinds value
      parseCheckOptions rest { args with kinds := some selected }
  | "--machine" :: [], _ => .error "--machine needs a component name"
  | "--machine" :: name :: rest, args =>
      if name.startsWith "--" then
        .error "--machine needs a component name"
      else
        parseCheckOptions rest { args with machine := some name }
  | option :: _, _ => .error s!"unexpected argument {option}"

private def parseCheck : List String → Except String (Option CheckArgs)
  | [] => .error "check needs <project-dir-or-.eventb>"
  | "--help" :: _ => .ok none
  | "-h" :: _ => .ok none
  | dir :: rest =>
      if dir.startsWith "--" then .error "check needs <project-dir-or-.eventb>"
      else parseCheckOptions rest { dir := dir }

private def parseSummary : List String → Except String (Option (System.FilePath × Bool))
  | [] => .error "summary needs <project-dir-or-.eventb>"
  | "--help" :: _ => .ok none
  | "-h" :: _ => .ok none
  | dir :: rest =>
      if dir.startsWith "--" then .error "summary needs <project-dir-or-.eventb>"
      else go dir rest false
where
  go : System.FilePath → List String → Bool →
      Except String (Option (System.FilePath × Bool))
    | dir, [], json => .ok (some (dir, json))
    | _, "--help" :: _, _ => .ok none
    | _, "-h" :: _, _ => .ok none
    | dir, "--json" :: rest, _ => go dir rest true
    | _, option :: _, _ => .error s!"unexpected argument {option}"

private def help : String :=
  "eventb: inspect Event-B projects (Rodin XML or Rossi text)\n\n" ++
  "Usage: eventb <command> [arguments]\n\n" ++
  "Commands:\n" ++
  "  check <project-dir-or-.eventb> [--json] [--kind INV,WD,...] [--machine NAME]\n" ++
  "  po <project-dir-or-.eventb> <PO-NAME>\n" ++
  "  summary <project-dir-or-.eventb> [--json]\n" ++
  "  report <project-dir-or-.eventb>\n" ++
  "  theory <project-dir-or-.tuf>\n" ++
  "  prove <project-dir-or-.eventb>\n" ++
  "  diff <project-dir>\n"

private def checkHelp : String :=
  "Usage: eventb check <project-dir-or-.eventb> [--json] " ++
  "[--kind INV,WD,...] [--machine NAME]\n\n" ++
  "Typecheck the project and list generated obligations."

private def poHelp : String :=
  "Usage: eventb po <project-dir-or-.eventb> <PO-NAME>\n\n" ++
  "Print hypotheses and the generated statement for one obligation."

private def summaryHelp : String :=
  "Usage: eventb summary <project-dir-or-.eventb> [--json]\n\n" ++
  "Count obligations by class and component."

private def reportHelp : String :=
  "Usage: eventb report <project-dir-or-.eventb>\n\n" ++
  "Emit one JSON report containing coverage, fingerprints, and trust-ledger entries."

private def diffHelp : String :=
  "Usage: eventb diff <project-dir>\n\n" ++
  "Compare generated obligation names with Rodin .bpo files."

private def theoryHelp : String :=
  "Usage: eventb theory <project-dir-or-.tuf>\n\n" ++
  "Load and validate Rodin theory files in dependency order."

private def proveHelp : String :=
  "Usage: eventb prove <project-dir-or-.eventb>\n\n" ++
  "Run the deterministic local discharge baseline and report its evidence count."

private def jsonEscape (value : String) : String :=
  String.ofList (value.toList.flatMap fun c =>
    match c with
    | '"' => ['\\', '"']
    | '\\' => ['\\', '\\']
    | '\n' => ['\\', 'n']
    | '\r' => ['\\', 'r']
    | '\t' => ['\\', 't']
    | _ => [c])

private def jsonString (value : String) : String :=
  "\"" ++ jsonEscape value ++ "\""

private def jsonBool (value : Bool) : String := if value then "true" else "false"

private def hypothesisOnly (obligation : Obligation) : Bool :=
  obligation.kind == "WWD" && obligation.goal.isNone

private def selected (args : CheckArgs) (report : Report) (obligation : Obligation) : Bool :=
  (match args.machine with
   | none => true
   | some name => name == report.source.name) &&
  (match args.kinds with
   | none => true
   | some selectedKinds => selectedKinds.contains obligation.kind)

private def filteredObligations (args : CheckArgs) (rs : List Report) :
    List (String × Obligation) :=
  rs.flatMap fun report =>
    (report.obligations.filter (selected args report)).map (fun o => (report.source.name, o))

private def runCheck (args : CheckArgs) : IO UInt32 := do
  let data ← loadProject args.dir
  if data.sources.isEmpty then
    for error in data.errors do
      IO.eprintln s!"eventb: error: {error}"
    IO.eprintln s!"eventb check: {args.dir} contains no .bum, .buc, or .eventb files"
    return 1
  let rs := reports data
  printCheckDiagnostics args data rs
  if args.machine.isSome && !rs.any (fun report =>
      report.source.name == args.machine.getD "") then
    IO.eprintln s!"eventb check: no component named {args.machine.getD ""}"
    return 1
  for (machine, obligation) in filteredObligations args rs do
    let derived := obligation.goal.isSome
    let hypothesisOnly := hypothesisOnly obligation
    if args.json then
      IO.println ("{\"machine\":" ++ jsonString machine ++
        ",\"name\":" ++ jsonString obligation.name ++
        ",\"kind\":" ++ jsonString obligation.kind ++
        ",\"derived\":" ++ jsonBool derived ++
        ",\"hypothesis_only\":" ++ jsonBool hypothesisOnly ++ "}")
    else
      IO.println (s!"{machine}: {obligation.name} [{obligation.kind}] " ++
        (if derived then "derived" else
          if hypothesisOnly then "hypothesis-only" else "no statement"))
  return if (fatalErrors data rs).isEmpty then 0 else 1

private def bump (key : String) : List (String × Nat) → List (String × Nat)
  | [] => [(key, 1)]
  | (name, count) :: rest =>
      if name == key then (name, count + 1) :: rest else
        (name, count) :: bump key rest

private def countKinds (obligations : List Obligation) : List (String × Nat) :=
  obligations.foldl (fun counts obligation => bump obligation.kind counts) []

private def derivedCount (obligations : List Obligation) : Nat :=
  obligations.countP (·.goal.isSome)

private def notDerivedCount (obligations : List Obligation) : Nat :=
  obligations.countP (·.goal.isNone)

private def notDerivedKinds (obligations : List Obligation) : List (String × Nat) :=
  countKinds (obligations.filter (·.goal.isNone))

private def hypothesisOnlyCount (obligations : List Obligation) : Nat :=
  obligations.countP hypothesisOnly

private def jsonCounts (counts : List (String × Nat)) : String :=
  "{" ++ String.intercalate "," (counts.map fun (name, count) =>
    jsonString name ++ ":" ++ toString count) ++ "}"

private def runSummary (dir : System.FilePath) (json : Bool) : IO UInt32 := do
  let data ← loadProject dir
  if data.sources.isEmpty then
    for error in data.errors do
      IO.eprintln s!"eventb: error: {error}"
    IO.eprintln s!"eventb summary: {dir} contains no .bum, .buc, or .eventb files"
    return 1
  let rs := reports data
  for error in fatalErrors data rs do
    IO.eprintln s!"eventb: error: {error}"
  let obligations := rs.flatMap (·.obligations)
  let counts := countKinds obligations
  if json then
    let machines := rs.map fun report =>
      jsonString report.source.name ++ ":{\"obligations\":" ++
        toString report.obligations.length ++ ",\"derived\":" ++
        toString (derivedCount report.obligations) ++ "}"
    IO.println ("{\"obligations\":" ++ toString obligations.length ++
      ",\"derived\":" ++ toString (derivedCount obligations) ++
      ",\"by_class\":" ++ jsonCounts counts ++
      ",\"not_derived\":" ++ toString (notDerivedCount obligations) ++
      ",\"not_derived_by_class\":" ++ jsonCounts (notDerivedKinds obligations) ++
      ",\"hypothesis_only\":" ++ toString (hypothesisOnlyCount obligations) ++
      ",\"by_machine\":{" ++ String.intercalate "," machines ++ "}}")
  else
    IO.println s!"obligations: {obligations.length}"
    IO.println s!"derived statements: {derivedCount obligations}"
    IO.println "by class:"
    for (kind, count) in counts do
      IO.println s!"  {kind}: {count}"
    IO.println "not derived by class:"
    for (kind, count) in notDerivedKinds obligations do
      IO.println s!"  {kind}: {count}"
    IO.println s!"hypothesis-only obligations: {hypothesisOnlyCount obligations}"
    IO.println "by machine:"
    for report in rs do
      IO.println (s!"  {report.source.name}: {report.obligations.length} " ++
        s!"({derivedCount report.obligations} derived)")
  return if (fatalErrors data rs).isEmpty then 0 else 1

private def runTheory (path : System.FilePath) : IO UInt32 := do
  let paths ← if ← path.isDir then theoryFiles path
    else if isTheory path then pure [path]
    else pure []
  if paths.isEmpty then
    IO.eprintln s!"eventb theory: {path} contains no .tuf file"
    return 1
  let (env, errors) ← loadTheories paths
  for error in errors do
    IO.eprintln s!"eventb theory: error: {error}"
  for spec in env.theories do
    if spec.name != Theory.core.name then
      IO.println (s!"{spec.name}: {spec.symbols.length} symbols, " ++
        s!"{spec.declarations.length} declarations, imports=" ++
        String.intercalate "," spec.imports)
  return if errors.isEmpty then 0 else 1

private def runProve (dir : System.FilePath) : IO UInt32 := do
  let data ← loadProject dir
  if data.sources.isEmpty then
    for error in data.errors do
      IO.eprintln s!"eventb: error: {error}"
    IO.eprintln s!"eventb prove: {dir} contains no Event-B source file"
    return 1
  let rs := reports data
  for error in fatalErrors data rs do
    IO.eprintln s!"eventb: error: {error}"
  let obligations := rs.flatMap (·.obligations)
  let results := obligations.map Prover.Local.prove
  let discharged := results.countP Prover.Local.Result.discharged
  IO.println s!"local baseline: {discharged}/{obligations.length} discharged"
  for (obligation, result) in obligations.zip results do
    if let some rule := result.rule then
      IO.println s!"  {obligation.name}: {rule.label} [external evidence]"
  return if (fatalErrors data rs).isEmpty then 0 else 1

private def findObligation : List Report → String → Option (String × Obligation)
  | [], _ => none
  | report :: rest, name =>
      match report.obligations.find? (fun obligation => obligation.name == name) with
      | some obligation => some (report.source.name, obligation)
      | none => findObligation rest name

private def runPo (dir : System.FilePath) (name : String) : IO UInt32 := do
  let data ← loadProject dir
  if data.sources.isEmpty then
    for error in data.errors do
      IO.eprintln s!"eventb: error: {error}"
    IO.eprintln s!"eventb po: {dir} contains no .bum, .buc, or .eventb files"
    return 1
  let rs := reports data
  for error in fatalErrors data rs do
    IO.eprintln s!"eventb: error: {error}"
  match findObligation rs name with
  | none =>
      IO.eprintln s!"eventb po: no obligation named {name}"
      return 1
  | some (machine, obligation) =>
      IO.println s!"{machine}: {obligation.name} [{obligation.kind}]"
      for hypothesis in obligation.hyps do
        IO.println s!"  {Formula.print hypothesis}"
      match obligation.goal with
      | some goal => IO.println s!"⊢ {Formula.print goal}"
      | none => IO.println "⊢ (no statement derived)"
      return if (fatalErrors data rs).isEmpty then 0 else 1

mutual

private def poNames (elem : XmlElem) : List String :=
  let here := if elem.tag == "org.eventb.core.poSequent" then
      elem.attr? "name" |>.toList
    else []
  here ++ poNamesList elem.children

termination_by sizeOf elem
decreasing_by cases elem; simp +arith

private def poNamesList : List XmlElem → List String
  | [] => []
  | elem :: rest => poNames elem ++ poNamesList rest

termination_by rest => sizeOf rest

end

private def readGoldPOs (path : System.FilePath) : IO (Except String (List String)) := do
  try
    let bytes ← IO.FS.readBinFile path
    match parseXml bytes with
    | .ok xml => return .ok (poNames xml)
    | .error error => return .error s!"invalid Rodin .bpo: {error.pretty bytes}"
  catch error =>
    return .error s!"could not be read: {error}"

private def localLedger (obligations : List Obligation) : Trust.Ledger :=
  obligations.foldl (fun ledger obligation =>
    match Prover.Local.attach ledger obligation (Prover.Local.prove obligation) with
    | .ok updated => updated
    | .error _ => ledger) (Trust.Ledger.ofObligations obligations)

private def reportCoverage (gold : List (String × List String))
    (machine name : String) : String :=
  match gold.find? (·.1 == machine) with
  | none => "not-compared"
  | some (_, names) => if names.contains name then "name-matched" else "name-missing"

private def reportEntry (gold : List (String × List String)) (ledger : Trust.Ledger)
    (machine : String) (obligation : Obligation) : String :=
  let entry := ledger.entry? machine obligation.name
  let mode := entry.map (·.mode.label) |>.getD "unproved"
  let rule := Prover.Local.prove obligation |>.rule.map Prover.Local.Rule.label |>.getD "none"
  let goal := obligation.goal.map Formula.print |>.getD ""
  let translation := if obligation.goal.isNone then "no-goal"
    else "requires-explicit-bindings"
  "{\"machine\":" ++ jsonString machine ++
    ",\"name\":" ++ jsonString obligation.name ++
    ",\"kind\":" ++ jsonString obligation.kind ++
    ",\"coverage\":" ++ jsonString (reportCoverage gold machine obligation.name) ++
    ",\"derived\":" ++ jsonBool obligation.goal.isSome ++
    ",\"hypothesis_only\":" ++ jsonBool (hypothesisOnly obligation) ++
    ",\"proof_mode\":" ++ jsonString mode ++
    ",\"rule\":" ++ jsonString rule ++
    ",\"translation\":" ++ jsonString translation ++
    ",\"fingerprint\":" ++ jsonString (Trust.fingerprint obligation.canonical) ++
    ",\"goal\":" ++ jsonString goal ++ "}"

private def runReport (dir : System.FilePath) : IO UInt32 := do
  let data ← loadProject dir
  if data.sources.isEmpty then
    for error in data.errors do
      IO.eprintln s!"eventb: error: {error}"
    IO.eprintln s!"eventb report: {dir} contains no Event-B source file"
    return 1
  let rs := reports data
  for error in fatalErrors data rs do
    IO.eprintln s!"eventb: error: {error}"
  let mut gold : List (String × List String) := []
  if ← dir.isDir then
    for path in ← bpoFiles dir do
      match ← readGoldPOs path with
      | .ok names => gold := (stem path, names) :: gold
      | .error error => IO.eprintln s!"eventb report: {error}"
  let obligations := rs.flatMap fun report =>
    report.obligations.map (fun obligation => (report.source.name, obligation))
  let ledger := localLedger (obligations.map (·.2))
  let records := obligations.map fun (machine, obligation) =>
    reportEntry gold ledger machine obligation
  let modes := [Trust.Mode.kernel, .smt, .rodinImported, .external, .unproved]
  let counts := modes.map fun mode =>
    jsonString mode.label ++ ":" ++ toString (ledger.count mode)
  IO.println ("{\"coverage_source\":" ++
    jsonString (if gold.isEmpty then "none" else "bpo-names") ++
    ",\"obligations\":[" ++ String.intercalate "," records ++
    "],\"trust_ledger\":{" ++ String.intercalate "," counts ++ "}}")
  return if (fatalErrors data rs).isEmpty then 0 else 1

private def findSource (sources : List Source) (name : String) : Option Source :=
  sources.find? (fun source => source.name == name)

private def runDiff (dir : System.FilePath) : IO UInt32 := do
  let data ← loadProject dir
  if data.sources.isEmpty then
    IO.eprintln s!"eventb diff: {dir} contains no .bum or .buc files"
    return 1
  let bpos ← bpoFiles dir
  if bpos.isEmpty then
    IO.eprintln s!"eventb diff: {dir} contains no .bpo files"
    return 1
  let rs := reports data
  for error in fatalErrors data rs do
    IO.eprintln s!"eventb: error: {error}"
  let mut failed := !(fatalErrors data rs).isEmpty
  for path in bpos do
    match findSource data.sources (stem path) with
    | none =>
        failed := true
        IO.eprintln s!"eventb diff: {path}: no matching .bum or .buc file"
    | some source =>
        match ← readGoldPOs path with
        | .error error =>
            failed := true
            IO.eprintln s!"eventb diff: {path}: {error}"
        | .ok gold =>
            let ours := (generateIn data.theory data.project source.name).map (·.name)
            let missing := gold.filter (fun name => !ours.contains name)
            let extra := ours.filter (fun name => !gold.contains name)
            let matching := gold.length - missing.length
            IO.println (s!"{source.name}: {matching} match, " ++
              s!"{missing.length} only Rodin, {extra.length} only ours")
            if !missing.isEmpty then
              IO.println s!"  only Rodin: {String.intercalate ", " missing}"
            if !extra.isEmpty then
              IO.println s!"  only ours: {String.intercalate ", " extra}"
  for source in data.sources do
    if !bpos.any (fun path => stem path == source.name) then
      failed := true
      IO.eprintln s!"eventb diff: {source.path}: no matching .bpo file"
  return if failed then 1 else 0

private def runCommand (args : List String) : IO UInt32 := do
  match args with
  | ["--help"] | ["-h"] =>
      IO.println help
      return 0
  | "check" :: rest =>
      match parseCheck rest with
      | .error error =>
          IO.eprintln s!"eventb check: {error}"
          IO.eprintln checkHelp
          return 1
      | .ok none =>
          IO.println checkHelp
          return 0
      | .ok (some parsed) => runCheck parsed
  | "po" :: rest =>
      if rest.any (fun arg => arg == "--help" || arg == "-h") then
        IO.println poHelp
        return 0
      match rest with
      | [dir, name] => runPo dir name
      | _ =>
          IO.eprintln "eventb po: expected <project-dir> <PO-NAME>"
          IO.eprintln poHelp
          return 1
  | "summary" :: rest =>
      match parseSummary rest with
      | .error error =>
          IO.eprintln s!"eventb summary: {error}"
          IO.eprintln summaryHelp
          return 1
      | .ok none =>
          IO.println summaryHelp
          return 0
      | .ok (some (dir, json)) => runSummary dir json
  | "report" :: rest =>
      if rest.any (fun arg => arg == "--help" || arg == "-h") then
        IO.println reportHelp
        return 0
      match rest with
      | [dir] => runReport dir
      | _ =>
          IO.eprintln "eventb report: expected <project-dir-or-.eventb>"
          IO.eprintln reportHelp
          return 1
  | "theory" :: rest =>
      if rest.any (fun arg => arg == "--help" || arg == "-h") then
        IO.println theoryHelp
        return 0
      match rest with
      | [path] => runTheory path
      | _ =>
          IO.eprintln "eventb theory: expected <project-dir-or-.tuf>"
          IO.eprintln theoryHelp
          return 1
  | "prove" :: rest =>
      if rest.any (fun arg => arg == "--help" || arg == "-h") then
        IO.println proveHelp
        return 0
      match rest with
      | [dir] => runProve dir
      | _ =>
          IO.eprintln "eventb prove: expected <project-dir-or-.eventb>"
          IO.eprintln proveHelp
          return 1
  | "diff" :: rest =>
      if rest.any (fun arg => arg == "--help" || arg == "-h") then
        IO.println diffHelp
        return 0
      match rest with
      | [dir] => runDiff dir
      | _ =>
          IO.eprintln "eventb diff: expected <project-dir>"
          IO.eprintln diffHelp
          return 1
  | command :: _ =>
      IO.eprintln s!"eventb: unknown command {command}"
      IO.eprintln help
      return 1
  | [] =>
      IO.eprintln "eventb: a command is required"
      IO.eprintln help
      return 1

def main (args : List String) : IO UInt32 := do
  try
    runCommand args
  catch error =>
    IO.eprintln s!"eventb: {error}"
    return (1 : UInt32)

end EventB.Cli

def main (args : List String) : IO UInt32 := EventB.Cli.main args
