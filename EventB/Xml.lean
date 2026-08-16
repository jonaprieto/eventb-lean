/-
Rodin's .bum/.buc files are regular XML: one declaration, one root element, and
element-only content. Keep this reader byte-oriented; formulas are attribute
strings and belong to the next phase.
-/

import Grip

namespace EventB

open Grip
open Grip.Ascii

structure XmlElem where
  tag      : String
  attrs    : List (String × String)
  children : List XmlElem
  deriving BEq, Repr

namespace XmlElem

def attr? (elem : XmlElem) (key : String) : Option String :=
  elem.attrs.find? (fun (name, _) => name == key) |>.map (·.2)

end XmlElem

private def isNameByte (b : UInt8) : Bool :=
  Ascii.isAlphaNum b || b == Ascii.code '.' || b == Ascii.code '-'
    || b == Ascii.code ':' || b == 95

private def isNameStartByte (b : UInt8) : Bool :=
  Ascii.isAlpha b || b == Ascii.code ':' || b == 95

private def digitValue (base : Nat) (c : Char) : Option Nat :=
  let n := c.toNat
  if 48 ≤ n && n ≤ 57 && n - 48 < base then
    some (n - 48)
  else if 65 ≤ n && n ≤ 70 && n - 55 < base then
    some (n - 55)
  else if 97 ≤ n && n ≤ 102 && n - 87 < base then
    some (n - 87)
  else
    none

private def digitsValue (base : Nat) (digits : List Char) : Option Nat :=
  if digits.isEmpty then
    none
  else
    digits.foldl
      (fun acc c => do
        let n ← acc
        let d ← digitValue base c
        pure (n * base + d))
      (some 0)

private def entityChar : List Char → Option Char
  | ['l', 't'] => some '<'
  | ['g', 't'] => some '>'
  | ['a', 'm', 'p'] => some '&'
  | ['q', 'u', 'o', 't'] => some '"'
  | ['a', 'p', 'o', 's'] => some '\''
  | '#' :: 'x' :: digits => digitsValue 16 digits |>.map Char.ofNat
  | '#' :: 'X' :: digits => digitsValue 16 digits |>.map Char.ofNat
  | '#' :: digits => digitsValue 10 digits |>.map Char.ofNat
  | _ => none

private structure DecodeState where
  output : List Char := []
  entity : Option (List Char) := none
  failed : Bool := false

private def decodeStep (state : DecodeState) (c : Char) : DecodeState :=
  if state.failed then
    state
  else
    match state.entity with
    | none =>
        if c == '&' then
          { state with entity := some [] }
        else
          { state with output := c :: state.output }
    | some rev =>
        if c != ';' then
          { state with entity := some (c :: rev) }
        else
          match entityChar rev.reverse with
          | some decoded => { state with output := decoded :: state.output, entity := none }
          | none => { state with failed := true }

private def unescape (s : String) : Option String :=
  let state := s.toList.foldl decodeStep {}
  if state.failed then
    none
  else
    match state.entity with
    | some _ => none
    | none => some (String.ofList state.output.reverse)

private def anyByte : GParser conditional UInt8 := GParser.satisfy (fun _ => true)

private def xmlName : GParser conditional String :=
  GParser.capture (GParser.seqR (GParser.satisfy isNameStartByte)
    (GParser.takeWhile isNameByte))

private def decodedValue : GParser fallible String :=
  GParser.captureWith?
    (fun arr q q' => String.fromUTF8? (arr.extract q q') >>= unescape)
    (GParser.takeWhile (fun b => b != Ascii.quote && b != Ascii.code '<'))

private def attrValue : GParser conditional String :=
  GParser.seqR (GParser.ch '"')
    (GParser.seqL decodedValue (GParser.ch '"'))

private def xmlAttribute : GParser conditional (String × String) :=
  GParser.map2 (fun name value => (name, value)) xmlName
    (GParser.seqR GParser.ws
      (GParser.seqR (GParser.ch '=')
        (GParser.seqR GParser.ws attrValue)))

private def tagTail (endTag : GParser conditional Unit) :
    GParser conditional (List (String × String)) :=
  GParser.fix fun rest =>
    GParser.alt
      (GParser.map (fun _ => []) (GParser.seqR GParser.ws endTag))
      (GParser.map2 (fun attr attrs => attr :: attrs)
        (GParser.seqR GParser.ws1 xmlAttribute) rest)

private def selfClosingTag : GParser conditional (String × List (String × String)) :=
  GParser.seqR (GParser.ch '<')
    (GParser.map2 (fun tag attrs => (tag, attrs)) xmlName
      (tagTail (GParser.seqR (GParser.ch '/') (GParser.ch '>'))))

private def openTag : GParser conditional (String × List (String × String)) :=
  GParser.seqR (GParser.ch '<')
    (GParser.map2 (fun tag attrs => (tag, attrs)) xmlName
      (tagTail (GParser.ch '>')))

private def closeTag (expected : String) : GParser conditional Unit :=
  let checkedName : GParser conditional Unit :=
    GParser.captureWith?
      (fun arr q q' =>
        let actual := (String.fromUTF8? (arr.extract q q')).getD ""
        if actual == expected then some () else none)
      (GParser.takeWhile1 isNameByte)
  GParser.seqR (GParser.string "</")
    (GParser.seqL checkedName
      (GParser.seqR GParser.ws (GParser.ch '>')))

private def element : GParser conditional XmlElem :=
  GParser.fix fun self =>
    let leaf : GParser conditional XmlElem :=
      GParser.map (fun (tag, attrs) => ⟨tag, attrs, []⟩) selfClosingTag
    let branch : GParser conditional XmlElem :=
      GParser.bind openTag fun (tag, attrs) =>
        GParser.map (fun children => ⟨tag, attrs, children⟩)
          (GParser.manyTill
            (GParser.seqR GParser.ws self)
            (GParser.seqR GParser.ws (closeTag tag)))
    GParser.alt leaf branch

private def xmlVersionAttribute : GParser conditional Unit :=
  GParser.seqR (GParser.string "version")
    (GParser.seqR GParser.ws
      (GParser.seqR (GParser.ch '=')
        (GParser.seqR GParser.ws
          (GParser.seqR (GParser.ch '"')
            (GParser.seqL (GParser.string "1.0") (GParser.ch '"'))))))

private def declaration : GParser conditional Unit :=
  GParser.map (fun _ => ())
    (GParser.seqR (GParser.string "<?xml")
      (GParser.seqR GParser.ws1
        (GParser.seqR xmlVersionAttribute (tagTail (GParser.string "?>")))))

private def document : GParser conditional XmlElem :=
  GParser.seqR declaration
    (GParser.seqR GParser.ws
      (GParser.seqL element (GParser.seqR GParser.ws GParser.eof)))

private def duplicateAttributeName (seen : List String) :
    List (String × String) → Bool
  | [] => false
  | (name, _) :: rest => seen.contains name || duplicateAttributeName (name :: seen) rest

private partial def hasDuplicateXmlAttributes (elem : XmlElem) : Bool :=
  duplicateAttributeName [] elem.attrs || elem.children.any hasDuplicateXmlAttributes

private def duplicateAttributeError : Grip.ParseError :=
  { pos := 0, line := 1, col := 1, expected := ["unique XML attributes"] }

/-- Parse one Rodin XML document from its UTF-8 bytes. -/
def parseXml (source : ByteArray) : Except Grip.ParseError XmlElem :=
  match GParser.parse document source with
  | .error error => .error error
  | .ok root =>
      if hasDuplicateXmlAttributes root then .error duplicateAttributeError
      else .ok root

/-- Parse one Rodin XML document from a Lean string. -/
def parseXmlString (source : String) : Except Grip.ParseError XmlElem :=
  parseXml source.toUTF8

#guard match parseXmlString
    "<?xml version=\"1.0\"?><root a=\"&lt;&#10;&amp;\"><group><x/></group></root>" with
  | .ok elem => elem.tag == "root"
      && elem.attrs == [("a", "<\n&")]
      && elem.children.map (·.tag) == ["group"]
  | .error _ => false

#guard match parseXmlString
    "<?xml version=\"1.0\"?><root a=\"1\" a=\"2\"/>" with
  | .error _ => true
  | .ok _ => false

#guard match parseXmlString "<?xml?><root/>" with
  | .error _ => true
  | .ok _ => false

#guard match parseXmlString "<?xml nonsense?><root/>" with
  | .error _ => true
  | .ok _ => false

#guard match parseXmlString "<?xml version=\"1.0\"?><1/>" with
  | .error _ => true
  | .ok _ => false


end EventB
