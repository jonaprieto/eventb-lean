import EventB.Formula.Parse

open EventB.Formula

/-- Dump the parsed form of each input line as JSON, so the spike's translator works
from the real parser's output rather than a second implementation of it. -/
def toJson : Term → String
  | .id s => "[\"id\"," ++ esc s ++ "]"
  | .num n => "[\"num\"," ++ toString n ++ "]"
  | .bin o a b => "[\"bin\"," ++ esc o ++ "," ++ toJson a ++ "," ++ toJson b ++ "]"
  | .pre o a => "[\"pre\"," ++ esc o ++ "," ++ toJson a ++ "]"
  | .post o a => "[\"post\"," ++ esc o ++ "," ++ toJson a ++ "]"
  | .app f a => "[\"app\"," ++ toJson f ++ "," ++ toJson a ++ "]"
  | .img r a => "[\"img\"," ++ toJson r ++ "," ++ toJson a ++ "]"
  | .set ts => "[\"set\",[" ++ String.intercalate "," (toJsonList ts) ++ "]]"
  | .bind k p b => "[\"bind\"," ++ esc k ++ "," ++ toJson p ++ "," ++ toJson b ++ "]"
where
  toJsonList : List Term → List String
  | [] => []
  | term :: terms => toJson term :: toJsonList terms

  esc (s : String) : String :=
    "\"" ++ (s.replace "\\" "\\\\" |>.replace "\"" "\\\"") ++ "\""

def main (args : List String) : IO Unit := do
  let path := args.head!
  let text ← IO.FS.readFile path
  for l in text.splitOn "\n" do
    if !l.isEmpty then
      match parse l with
      | .ok t => IO.println (toJson t)
      | .error e => IO.println ("[\"ERROR\",\"" ++ e.message.replace "\"" "'" ++ "\"]")
