import EventB.Model
import EventB.Formula.Parse

open EventB

def main : IO Unit := do
  let mut forms : Array (String × String) := #[]
  for proj in ← (System.FilePath.mk "corpus").readDir do
    if ← proj.path.isDir then
      for f in ← proj.path.readDir do
        if f.path.toString.endsWith ".bum" || f.path.toString.endsWith ".buc" then
          match ← readModel f.path with
          | .ok m =>
            for (l, s) in m.formulas do forms := forms.push (l, s)
          | .error _ => pure ()
  IO.println s!"formulas {forms.size}"
  let t0 ← IO.monoMsNow
  let mut lexed := 0
  for (_, s) in forms do
    match Formula.lex s with | .ok ts => lexed := lexed + ts.length | .error _ => pure ()
  let t1 ← IO.monoMsNow
  IO.println s!"lex {t1 - t0}ms  tokens {lexed}"
  let mut ok := 0
  for (_, s) in forms do
    match Formula.parse s with | .ok _ => ok := ok + 1 | .error _ => pure ()
  let t2 ← IO.monoMsNow
  IO.println s!"parse {t2 - t1}ms  ok {ok}/{forms.size}"
