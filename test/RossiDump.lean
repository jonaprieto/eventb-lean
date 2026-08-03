import EventB.Rossi

namespace EventB.RossiDump

open EventB

private def jsonEscape (value : String) : String :=
  String.ofList (value.toList.flatMap fun c =>
    match c with
    | '"' => ['\\', '"']
    | '\\' => ['\\', '\\']
    | '\n' => ['\\', 'n']
    | '\r' => ['\\', 'r']
    | '\t' => ['\\', 't']
    | _ => [c])

private def jsonString (value : String) : String := "\"" ++ jsonEscape value ++ "\""

private def componentJson (component : Rossi.Component) : String :=
  let kind := if component.model.root.tag.endsWith "contextFile" then "Context" else "Machine"
  "{\"component_type\":" ++ jsonString kind ++
    ",\"component_name\":" ++ jsonString component.name ++ "}"

private def fileJson (path : String) (components : List Rossi.Component) : String :=
  "{\"file\":" ++ jsonString path ++ ",\"success\":true,\"components\":[" ++
    String.intercalate "," (components.map componentJson) ++ "]}"

def main (args : List String) : IO UInt32 := do
  let mut failed := false
  for path in args do
    match ← Rossi.read path with
    | .ok components => IO.println (fileJson path components)
    | .error error =>
        failed := true
        IO.println ("{\"file\":" ++ jsonString path ++ ",\"success\":false," ++
          "\"error\":" ++ jsonString (EventB.Error.render error) ++ "}")
  return if failed then 1 else 0

end EventB.RossiDump

def main (args : List String) : IO UInt32 := EventB.RossiDump.main args
