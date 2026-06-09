import OmegaJCS.Types
import OmegaJCS.Encode

namespace OmegaJCS

private def startsWith (s : List Char) (pre : String) : Bool :=
  s.take pre.length = pre.toList

private def takePrefix (s : List Char) (pre : String) : Option (List Char) :=
  if startsWith s pre then some (s.drop pre.length) else none

private def isDigit (c : Char) : Bool :=
  '0'.toNat ≤ c.toNat ∧ c.toNat ≤ '9'.toNat

private partial def parseNatDigits (s : List Char) (acc : Nat) : Option (Nat × List Char) :=
  match s with
  | [] => some (acc, [])
  | c :: rest =>
      if isDigit c then
        parseNatDigits rest (acc * 10 + (c.toNat - '0'.toNat))
      else
        some (acc, s)

private partial def parseInt (s : List Char) : Option (Int × List Char) :=
  match s with
  | '-' :: rest =>
      match parseNatDigits rest 0 with
      | some (n, rest') => some (-Int.ofNat n, rest')
      | none => none
  | c :: _ =>
      if isDigit c then
        match parseNatDigits s 0 with
        | some (n, rest') => some (Int.ofNat n, rest')
        | none => none
      else none
  | [] => none

private def hexValue (c : Char) : Option Nat :=
  if '0'.toNat ≤ c.toNat ∧ c.toNat ≤ '9'.toNat then some (c.toNat - '0'.toNat)
  else if 'a'.toNat ≤ c.toNat ∧ c.toNat ≤ 'f'.toNat then some (c.toNat - 'a'.toNat + 10)
  else if 'A'.toNat ≤ c.toNat ∧ c.toNat ≤ 'F'.toNat then some (c.toNat - 'A'.toNat + 10)
  else none

private def parseHex4 (s : List Char) : Option (Nat × List Char) :=
  match s with
  | a :: b :: c :: d :: rest =>
      match hexValue a, hexValue b, hexValue c, hexValue d with
      | some ha, some hb, some hc, some hd =>
          some (ha * 4096 + hb * 256 + hc * 16 + hd, rest)
      | _, _, _, _ => none
  | _ => none

private partial def parseStringChars (s : List Char) (acc : List Char) : Option (String × List Char) :=
  match s with
  | [] => none
  | '"' :: rest => some (String.ofList acc, rest)
  | '\\' :: rest =>
      match rest with
      | '"' :: r => parseStringChars r (acc ++ ['"'])
      | '\\' :: r => parseStringChars r (acc ++ ['\\'])
      | 'b' :: r => parseStringChars r (acc ++ [Char.ofNat 0x08])
      | 'f' :: r => parseStringChars r (acc ++ [Char.ofNat 0x0C])
      | 'n' :: r => parseStringChars r (acc ++ [Char.ofNat 0x0A])
      | 'r' :: r => parseStringChars r (acc ++ [Char.ofNat 0x0D])
      | 't' :: r => parseStringChars r (acc ++ [Char.ofNat 0x09])
      | 'u' :: r =>
          match parseHex4 r with
          | some (cp, r') => parseStringChars r' (acc ++ [Char.ofNat cp])
          | none => none
      | _ => none
  | c :: rest => parseStringChars rest (acc ++ [c])

private def parseString (s : List Char) : Option (String × List Char) :=
  match s with
  | '"' :: rest => parseStringChars rest []
  | _ => none

mutual
  partial def parseValue (s : List Char) : Option (OmegaJson × List Char) :=
    if let some rest := takePrefix s "null" then
      some (OmegaJson.null, rest)
    else if let some rest := takePrefix s "true" then
      some (OmegaJson.bool true, rest)
    else if let some rest := takePrefix s "false" then
      some (OmegaJson.bool false, rest)
    else if let some (n, rest) := parseInt s then
      some (OmegaJson.int n, rest)
    else if let some (str, rest) := parseString s then
      some (OmegaJson.str str, rest)
    else if let some rest := takePrefix s "[" then
      parseArray rest []
    else if let some rest := takePrefix s "{" then
      parseObject rest []
    else none

  partial def parseArray (s : List Char) (acc : List OmegaJson) : Option (OmegaJson × List Char) :=
    match s with
    | ']' :: rest => some (OmegaJson.arr acc.reverse, rest)
    | rest =>
        match parseValue rest with
        | some (v, rest') =>
            match rest' with
            | ',' :: rest'' => parseArray rest'' (v :: acc)
            | ']' :: rest'' => some (OmegaJson.arr (v :: acc).reverse, rest'')
            | _ => none
        | none => none

  partial def parseObjectPair (s : List Char) : Option (String × OmegaJson × List Char) :=
    match parseString s with
    | some (k, rest) =>
        match rest with
        | ':' :: rest' =>
            match parseValue rest' with
            | some (v, rest'') => some (k, v, rest'')
            | none => none
        | _ => none
    | none => none

  partial def parseObject (s : List Char) (acc : List (String × OmegaJson)) :
      Option (OmegaJson × List Char) :=
    match s with
    | '}' :: rest => some (OmegaJson.obj acc.reverse, rest)
    | rest =>
        match parseObjectPair rest with
        | some (k, v, rest') =>
            match rest' with
            | ',' :: rest'' => parseObject rest'' ((k, v) :: acc)
            | '}' :: rest'' => some (OmegaJson.obj ((k, v) :: acc).reverse, rest'')
            | _ => none
        | none => none
end

/-- Decoder for encoder output only — not a general JSON parser. -/
def jcsDecode (s : String) : Option OmegaJson :=
  match parseValue s.toList with
  | some (v, []) => some v
  | _ => none

end OmegaJCS
