import EventB.POG
import EventB.Prover.Local
import EventB.Rossi
import EventB.Theory.Rodin
import Argus
import Argus.Term
import TermColor.Diagnostics

namespace EventB.Cli

open EventB
open EventB.Formula
open EventB.POG
open EventB.Typing
open Argus
open TermColor

private def diagnosticText (paths : List System.FilePath) (error : EventB.Error) :
    IO TermColor.Text := do
  let candidates := error.path.toList.map System.FilePath.mk ++ paths
  match candidates.head? with
  | none => pure (TermColor.Text.plain error.render)
  | some path =>
      let absolute ← try IO.FS.realPath path catch _ => pure path
      let sourceText ← try IO.FS.readFile path catch _ => pure ""
      let source :=
        (TermColor.Diagnostics.Source.named path.toString sourceText).withUri
          (System.Uri.pathToUri absolute)
      let diagnostic :=
        (TermColor.Diagnostics.Diagnostic.error error.message).withLabel
          (TermColor.Diagnostics.Label.primary (TermColor.Diagnostics.Span.point 0 0))
      let diagnostic := error.context.foldl
        (fun diagnostic context => diagnostic.withNote context) diagnostic
      pure (TermColor.Diagnostics.render #[source] diagnostic)

private def printError (paths : List System.FilePath) (error : EventB.Error) : IO Unit := do
  let stderr ← IO.getStderr
  let target ← TermColor.targetWithTty .auto (← stderr.isTty)
  let text ← diagnosticText paths error
  stderr.putStr (TermColor.Text.render target (text ++ TermColor.Text.plain "\n"))

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
  errors : List EventB.Error
  paths : List System.FilePath

private def loadTheories (paths : List System.FilePath) :
    IO (Theory.Env × List EventB.Error) := do
  let mut pending := paths
  let mut env := Theory.empty
  let mut errors : List EventB.Error := []
  while !pending.isEmpty do
    let mut next : List (System.FilePath × EventB.Error) := []
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
            | .error error => errors := error.withPath path.toString :: errors
        | .error error =>
            if error.message.endsWith "is not registered" then
              next := (path, error) :: next
            else
              errors := error.withPath path.toString :: errors
      catch error =>
        errors := (EventB.Error.io s!"could not be read: {error}").withPath path.toString :: errors
    if !progressed && next.length == pending.length then
      for (path, error) in next do
        errors := error.withPath path.toString :: errors
      pending := []
    else
      pending := next.reverse.map (·.1)
  return (env, errors.reverse)

private def readSource (path : System.FilePath) : IO (Except EventB.Error Source) := do
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
        return .error ((EventB.Error.model s!"expected {expected} root").withPath path.toString)
    | .error reason =>
        return .error (reason.withPath path.toString)
  catch err =>
    return .error ((EventB.Error.io s!"could not be read: {err}").withPath path.toString)

private def readRossi (path : System.FilePath) : IO (Except EventB.Error (List Source)) := do
  match ← Rossi.read path with
  | .error reason => return .error (reason.withPath path.toString)
  | .ok components =>
      return .ok (components.map fun component =>
        { path := path, name := component.name, model := component.model })

private def loadProject (path : System.FilePath) : IO ProjectData := do
  let mut sources : List Source := []
  let mut errors : List EventB.Error := []
  let isDir ← path.isDir
  let theoryPaths ← if isDir then theoryFiles path else pure []
  let sourcePaths ← if isDir then sourceFiles path else pure []
  let rossiPaths ← if isDir then rossiFiles path else pure []
  let (theory, theoryErrors) ← if isDir then
      loadTheories theoryPaths
    else
      pure (Theory.empty, [])
  errors := theoryErrors
  if isDir then
    for sourcePath in sourcePaths do
      match ← readSource sourcePath with
      | .ok source => sources := source :: sources
      | .error reason => errors := reason :: errors
    for sourcePath in rossiPaths do
      match ← readRossi sourcePath with
      | .ok parsed => sources := parsed.reverse ++ sources
      | .error reason => errors := reason :: errors
  else if isRossi path then
    match ← readRossi path with
    | .ok parsed => sources := parsed.reverse
    | .error reason => errors := reason :: errors
  else
    errors := (EventB.Error.cli "expected a project directory or .eventb file").withPath
      path.toString :: errors
  let orderedSources := sources.reverse
  let mut uniqueSources : List Source := []
  let mut duplicateErrors : List EventB.Error := []
  for source in orderedSources do
    if uniqueSources.any (fun existing => existing.name == source.name) then
      duplicateErrors :=
        (EventB.Error.cli s!"duplicate component `{source.name}`").withPath
          source.path.toString :: duplicateErrors
    else
      uniqueSources := uniqueSources ++ [source]
  let roots := theory.theories.filter (·.name != Theory.core.name) |>.map (·.name)
  let project : Project := uniqueSources.map (projectComponent roots)
  return ProjectData.mk project uniqueSources theory (errors.reverse ++ duplicateErrors.reverse)
    (path :: theoryPaths ++ sourcePaths ++ rossiPaths)

private def formulaErrorLabel (model : Model) (error : String) : Option String :=
  model.formulas.find? (fun pair =>
    match pair with
    | (_label, formula) =>
        match Formula.parse formula with
        | .error reason => error == "parse: " ++ EventB.Error.render reason
        | .ok term =>
            let marker := "unbound identifier "
            error.startsWith marker &&
              (EventB.POG.identifiers term).contains
                (error.drop marker.length).toString)
  |>.map (·.1)

private def formatTypeError (source : Source) (error : String) : EventB.Error :=
  let reason := if error.startsWith "parse: " then error.drop 7 else error
  let message := match formulaErrorLabel source.model error with
    | some label => s!"element {label}: {reason}"
    | none => s!"typechecking failed: {reason}"
  (EventB.Error.typing message).withPath source.path.toString

private def typeErrors (data : ProjectData) (source : Source) : List EventB.Error :=
  match inferComponentIn data.theory data.project source.name with
  | .error error => [formatTypeError source error.message]
  | .ok (_, errors) => errors.map (formatTypeError source)

private structure Report where
  source : Source
  obligations : List Obligation
  errors : List EventB.Error

private def reports (data : ProjectData) : List Report :=
  data.sources.map fun source =>
    { source := source
      obligations := generateIn data.theory data.project source.name
      errors := typeErrors data source }

private def fatalErrors (data : ProjectData) (rs : List Report) : List EventB.Error :=
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
  kinds : Option String := none
  machine : Option String := none

private def printCheckDiagnostics (data : ProjectData) (rs : List Report) : IO Unit := do
  for error in fatalErrors data rs do
    printError data.paths error

private def makeCheck (dir : System.FilePath) (json : Bool) (kinds : Option String)
    (machine : Option String) : CheckArgs :=
  { dir, json, kinds, machine }

private inductive Action where
  | check (args : CheckArgs)
  | po (dir : System.FilePath) (name : String)
  | summary (dir : System.FilePath) (json : Bool)
  | report (dir : System.FilePath)
  | theory (path : System.FilePath)
  | prove (dir : System.FilePath)
  | diff (dir : System.FilePath)

private def pathParam : Param System.FilePath :=
  Param.map System.FilePath.mk Param.path

private def projectArg (help : String) :=
  Spec.arg "PROJECT" help pathParam

private def checkSpec :=
  Spec.seq
    (Spec.seq
      (Spec.seq
        (Spec.map makeCheck (projectArg "Project directory or .eventb file"))
        (Spec.switch "json" none "Emit one JSON record per obligation"))
      (Spec.opt (Spec.flag "kind" none "Comma-separated obligation classes" Param.str)))
    (Spec.opt (Spec.flag "machine" none "Limit output to one component" Param.str))

private def summarySpec :=
  Spec.map2 Action.summary (projectArg "Project directory or .eventb file")
    (Spec.switch "json" none "Emit one JSON summary")

private def command : Command Action :=
  group "eventb" [
    cmd "check" (Spec.map Action.check checkSpec)
      (description := "Typecheck a project and list generated obligations."),
    cmd "po" (Spec.map2 Action.po (projectArg "Project directory or .eventb file")
      (Spec.arg "PO-NAME" "Proof-obligation name" Param.str))
      (description := "Print one generated proof obligation."),
    cmd "summary" summarySpec
      (description := "Count obligations by class and component."),
    cmd "report" (Spec.map Action.report (projectArg
      "Project directory or .eventb file"))
      (description := "Emit coverage, fingerprints, and trust-ledger JSON."),
    cmd "theory" (Spec.map Action.theory (Spec.arg "PATH" "Theory file or directory"
      pathParam))
      (description := "Load and validate Rodin theory files."),
    cmd "prove" (Spec.map Action.prove (projectArg
      "Project directory or .eventb file"))
      (description := "Run the deterministic local discharge baseline."),
    cmd "diff" (Spec.map Action.diff (Spec.arg "PROJECT" "Rodin project directory"
      pathParam))
      (description := "Compare generated obligation names with Rodin .bpo files.")
  ] (description := "Inspect Event-B projects from Rodin XML or Rossi text.")

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

private def selected (machine : Option String) (kinds : Option (List String)) (report : Report)
    (obligation : Obligation) : Bool :=
  (match machine with
   | none => true
   | some name => name == report.source.name) &&
  (match kinds with
   | none => true
   | some selectedKinds => selectedKinds.contains obligation.kind)

private def filteredObligations (args : CheckArgs) (kinds : Option (List String))
    (rs : List Report) :
    List (String × Obligation) :=
  rs.flatMap fun report =>
    (report.obligations.filter (selected args.machine kinds report)).map
      (fun o => (report.source.name, o))

private def runCheckWithKinds (args : CheckArgs) (kinds : Option (List String)) : IO UInt32 := do
  let data ← loadProject args.dir
  if data.sources.isEmpty then
    for error in data.errors do
      printError data.paths error
    printError [args.dir]
      ((EventB.Error.cli s!"eventb check: {args.dir} contains no .bum, .buc, or .eventb files").withPath
        args.dir.toString)
    return 1
  let rs := reports data
  printCheckDiagnostics data rs
  if args.machine.isSome && !rs.any (fun report =>
      report.source.name == args.machine.getD "") then
    printError [] (EventB.Error.cli s!"eventb check: no component named {args.machine.getD ""}")
    return 1
  for (machine, obligation) in filteredObligations args kinds rs do
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

private def runCheck (args : CheckArgs) : IO UInt32 :=
  match args.kinds with
  | none => runCheckWithKinds args none
  | some value =>
      match parseKinds value with
      | .ok kinds => runCheckWithKinds args (some kinds)
      | .error error => do
          printError [] (EventB.Error.cli s!"eventb check: {error}")
          return 1

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
      printError data.paths error
    printError [dir]
      ((EventB.Error.cli s!"eventb summary: {dir} contains no .bum, .buc, or .eventb files").withPath
        dir.toString)
    return 1
  let rs := reports data
  for error in fatalErrors data rs do
    printError data.paths error
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
    printError [path]
      ((EventB.Error.cli s!"eventb theory: {path} contains no .tuf file").withPath path.toString)
    return 1
  let (env, errors) ← loadTheories paths
  for error in errors do
    printError paths error
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
      printError data.paths error
    printError [dir]
      ((EventB.Error.cli s!"eventb prove: {dir} contains no Event-B source file").withPath dir.toString)
    return 1
  let rs := reports data
  for error in fatalErrors data rs do
    printError data.paths error
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
      printError data.paths error
    printError [dir]
      ((EventB.Error.cli s!"eventb po: {dir} contains no .bum, .buc, or .eventb files").withPath
        dir.toString)
    return 1
  let rs := reports data
  for error in fatalErrors data rs do
    printError data.paths error
  match findObligation rs name with
  | none =>
      printError [] (EventB.Error.cli s!"eventb po: no obligation named {name}")
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

private def jsonArray (values : List String) : String :=
  "[" ++ String.intercalate "," (values.map jsonString) ++ "]"

private def evidenceJson : Trust.Evidence → String
  | .none =>
      "{\"mode\":\"unproved\",\"declaration\":\"\",\"verifier\":\"\",\"dependencies\":[]}"
  | .kernel declaration axioms =>
      "{\"mode\":" ++ jsonString Trust.Mode.kernel.label ++
      ",\"declaration\":" ++ jsonString declaration ++
      ",\"verifier\":\"Lean kernel\",\"dependencies\":" ++ jsonArray axioms ++ "}"
  | .smt solver version inputDigest verifier =>
      "{\"mode\":" ++ jsonString Trust.Mode.smt.label ++
      ",\"tool\":" ++ jsonString solver ++
      ",\"version\":" ++ jsonString version ++
      ",\"input_digest\":" ++ jsonString inputDigest ++
      ",\"verifier\":" ++ jsonString verifier ++ "}"
  | .external tool version artifactDigest verifier =>
      "{\"mode\":" ++ jsonString Trust.Mode.external.label ++
      ",\"tool\":" ++ jsonString tool ++
      ",\"version\":" ++ jsonString version ++
      ",\"input_digest\":" ++ jsonString artifactDigest ++
      ",\"verifier\":" ++ jsonString verifier ++ "}"
  | .rodinImported source digest manual =>
      "{\"mode\":" ++ jsonString Trust.Mode.rodinImported.label ++
      ",\"source\":" ++ jsonString source ++
      ",\"input_digest\":" ++ jsonString digest ++
      ",\"manual\":" ++ jsonBool manual ++
      ",\"verifier\":\"Rodin .bps importer\"}"

private def reportEntry (gold : List (String × List String)) (ledger : Trust.Ledger)
    (machine : String) (obligation : Obligation) : String :=
  let fallback := (Trust.Ledger.ofObligations [obligation]).entries.head!
  let entry := (ledger.entry? machine obligation.name).getD fallback
  let mode := entry.mode.label
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
    ",\"evidence\":" ++ evidenceJson entry.evidence ++
    ",\"translation\":" ++ jsonString translation ++
    ",\"fingerprint\":" ++ jsonString (Trust.fingerprint obligation.canonical) ++
    ",\"goal\":" ++ jsonString goal ++ "}"

private def runReport (dir : System.FilePath) : IO UInt32 := do
  let data ← loadProject dir
  if data.sources.isEmpty then
    for error in data.errors do
      printError data.paths error
    printError [dir]
      ((EventB.Error.cli s!"eventb report: {dir} contains no Event-B source file").withPath dir.toString)
    return 1
  let rs := reports data
  for error in fatalErrors data rs do
    printError data.paths error
  let mut gold : List (String × List String) := []
  if ← dir.isDir then
    for path in ← bpoFiles dir do
      match ← readGoldPOs path with
      | .ok names => gold := (stem path, names) :: gold
      | .error error =>
          printError [path] ((EventB.Error.cli s!"eventb report: {error}").withPath path.toString)
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
    printError [dir]
      ((EventB.Error.cli s!"eventb diff: {dir} contains no .bum or .buc files").withPath dir.toString)
    return 1
  let bpos ← bpoFiles dir
  if bpos.isEmpty then
    printError [dir]
      ((EventB.Error.cli s!"eventb diff: {dir} contains no .bpo files").withPath dir.toString)
    return 1
  let rs := reports data
  for error in fatalErrors data rs do
    printError data.paths error
  let mut failed := !(fatalErrors data rs).isEmpty
  for path in bpos do
    match findSource data.sources (stem path) with
    | none =>
        failed := true
        printError [path]
          ((EventB.Error.cli "eventb diff: no matching .bum or .buc file").withPath path.toString)
    | some source =>
        match ← readGoldPOs path with
        | .error error =>
            failed := true
            printError [path]
              ((EventB.Error.cli s!"eventb diff: {error}").withPath path.toString)
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
      printError [source.path]
        ((EventB.Error.cli "eventb diff: no matching .bpo file").withPath source.path.toString)
  return if failed then 1 else 0

private def runAction : Action → IO UInt32
  | .check args => runCheck args
  | .po dir name => runPo dir name
  | .summary dir json => runSummary dir json
  | .report dir => runReport dir
  | .theory path => runTheory path
  | .prove dir => runProve dir
  | .diff dir => runDiff dir

def main (args : List String) : IO UInt32 := do
  try
    Argus.Term.main command args runAction
  catch error =>
    printError [] (EventB.Error.cli s!"eventb: {error}")
    return (1 : UInt32)

end EventB.Cli

def main (args : List String) : IO UInt32 := EventB.Cli.main args
