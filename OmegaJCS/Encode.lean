import OmegaJCS.Types

namespace OmegaJCS

private def hexDigit (n : Nat) : Char :=
  if n < 10 then Char.ofNat (n + '0'.toNat)
  else Char.ofNat (n - 10 + 'a'.toNat)

private def hex4Lower (n : Nat) : String :=
  String.ofList [
    hexDigit ((n >>> 12) &&& 0xF),
    hexDigit ((n >>> 8) &&& 0xF),
    hexDigit ((n >>> 4) &&& 0xF),
    hexDigit (n &&& 0xF)]

/-- RFC 8785 string escaping for one character (profile table). -/
def escapeChar (c : Char) : String :=
  if c == '"' then "\\" ++ "\""
  else if c == '\\' then "\\\\"
  else if c.toNat == 0x08 then "\\" ++ "b"
  else if c.toNat == 0x0C then "\\" ++ "f"
  else if c.toNat == 0x0A then "\\" ++ "n"
  else if c.toNat == 0x0D then "\\" ++ "r"
  else if c.toNat == 0x09 then "\\" ++ "t"
  else if c.toNat < 0x20 then
    "\\u" ++ hex4Lower c.toNat
  else
    String.singleton c

def jcsEscapeString (s : String) : String :=
  "\"" ++ String.join (s.toList.map escapeChar) ++ "\""

private partial def natToStringAux (n : Nat) (acc : String) : String :=
  if n = 0 then acc
  else natToStringAux (n / 10) (String.singleton (Char.ofNat (n % 10 + '0'.toNat)) ++ acc)

private def natToString (n : Nat) : String :=
  if n = 0 then "0" else natToStringAux n ""

/-- Profile integer printing: decimal, leading `-` only, no `+`, no leading zeros.
    `-0` cannot occur — `Int` has a single zero (unlike JS IEEE `-0`). -/
def intToString (n : Int) : String :=
  if n < 0 then
    "-" ++ natToString n.natAbs
  else
    natToString n.toNat

mutual
  partial def jcsEncode : OmegaJson → String
    | .null => "null"
    | .bool true => "true"
    | .bool false => "false"
    | .int n => intToString n
    | .str s => jcsEscapeString s
    | .arr xs =>
        "[" ++ String.intercalate "," (xs.map jcsEncode) ++ "]"
    | .obj kvs =>
        "{" ++ String.intercalate "," (kvs.map fun ⟨k, v⟩ =>
          jcsEscapeString k ++ ":" ++ jcsEncode v) ++ "}"

end

def canonicalBytesJCS (v : OmegaJson) : ByteArray :=
  (jcsEncode v).toUTF8

end OmegaJCS
