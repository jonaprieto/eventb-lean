import EventB.POG

open EventB EventB.POG EventB.Typing

/-- Print the goal this generator derives for one obligation, for comparing against the
`.bpo` by eye when the gate says "differs". -/
def main (args : List String) : IO Unit := do
  let dir : System.FilePath := "corpus"
  let mut project : Project := []
  for proj in ← dir.readDir do
    if ← proj.path.isDir then
      for f in ← proj.path.readDir do
        let p := f.path.toString
        if p.endsWith ".bum" || p.endsWith ".buc" then
          match ← readModel f.path with
          | .ok m =>
            let name := ((p.splitOn "/").getLast!.splitOn ".").head!
            project := project ++ [{ name := name, elem := m.root }]
          | .error _ => pure ()
  let file := args[0]!
  let want := args[1]!
  for o in generate project file do
    if o.name == want then
      IO.println o.name
      for h in o.hyps do
        IO.println s!"  HYP: {Formula.print h}"
      match o.goal with
      | some g => IO.println s!"  ours: {Formula.print g}"
      | none => IO.println "  ours: (no goal derived)"
