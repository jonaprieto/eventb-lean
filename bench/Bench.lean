import EventB.Model
import EventB.Formula.Parse

open EventB

/-- Parse every predicate Rodin wrote into the `.bpo` files, extracted by
`spike/extract.py`. These are the proof obligations themselves, not the model, and they
use syntax a `.bum` never contains: type ascriptions on bound variables. -/
def main (args : List String) : IO Unit := do
  let path := args.getLast?.getD "/tmp/allpo.txt"
  let text ← try IO.FS.readFile path catch _ =>
    throw <| IO.userError s!"bench: input file not found: {path} (run spike/extract.py first)"
  let lines := text.splitOn "\n" |>.filter (fun l => !l.isEmpty)
  let mut ok := 0
  let mut fails : List String := []
  for l in lines do
    match Formula.parse l with
    | .ok _ => ok := ok + 1
    | .error e => fails := (EventB.Error.render e ++ "  ||  " ++ l.take 70) :: fails
  IO.println s!"PO predicates parsed {ok}/{lines.length}"
  for f in (fails.take 6) do IO.println s!"  {f}"
