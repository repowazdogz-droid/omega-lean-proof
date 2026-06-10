import OmegaJCS.Types

namespace OmegaJCS

def hexDigit (n : Nat) : Char :=
  if n < 10 then Char.ofNat (n + '0'.toNat)
  else Char.ofNat (n - 10 + 'a'.toNat)

def hex4Lower (n : Nat) : String :=
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

def escapeCharList (c : Char) : List Char :=
  (escapeChar c).toList

def escapeStringChars (cs : List Char) : List Char :=
  cs.flatMap escapeCharList

def jcsEscapeString (s : String) : String :=
  "\"" ++ String.join (s.toList.map escapeChar) ++ "\""

def jcsEscapeStringChars (s : String) : List Char :=
  '"' :: escapeStringChars s.toList ++ ['"']

def natToDecimalAux (n : Nat) (acc : List Char) : List Char :=
  if h : n = 0 then acc
  else natToDecimalAux (n / 10) (Char.ofNat (n % 10 + '0'.toNat) :: acc)
termination_by n
decreasing_by
  apply Nat.div_lt_self (Nat.zero_lt_of_ne_zero h) (by decide)

def natToDecimal (n : Nat) : List Char :=
  if n = 0 then ['0'] else natToDecimalAux n []

def natToDecimalString (n : Nat) : String :=
  String.ofList (natToDecimal n)

def intToStringChars (n : Int) : List Char :=
  if n < 0 then
    '-' :: natToDecimal n.natAbs
  else
    natToDecimal n.toNat

def intToString (n : Int) : String :=
  String.ofList (intToStringChars n)

mutual
  def encObjPairChars (kv : String × OmegaJson) : List Char :=
    jcsEscapeStringChars kv.1 ++ ':' :: jcsEncodeChars kv.2

  def jcsEncodeChars : OmegaJson → List Char
    | .null => "null".toList
    | .bool true => "true".toList
    | .bool false => "false".toList
    | .int n => intToStringChars n
    | .str s => jcsEscapeStringChars s
    | .arr xs => '[' :: encArrBody xs
    | .obj kvs => '{' :: encObjBody kvs

  def encArrSuffix (xs : List OmegaJson) : List Char :=
    match xs with
    | [] => [']']
    | v :: vs => ',' :: jcsEncodeChars v ++ encArrSuffix vs

  def encArrBody (xs : List OmegaJson) : List Char :=
    match xs with
    | [] => [']']
    | v :: vs => jcsEncodeChars v ++ encArrSuffix vs

  def encObjSuffix (kvs : List (String × OmegaJson)) : List Char :=
    match kvs with
    | [] => ['}']
    | kv :: kvs' => ',' :: encObjPairChars kv ++ encObjSuffix kvs'

  def encObjBody (kvs : List (String × OmegaJson)) : List Char :=
    match kvs with
    | [] => ['}']
    | kv :: kvs' => encObjPairChars kv ++ encObjSuffix kvs'
end

partial def jcsEncode (v : OmegaJson) : String :=
  String.ofList (jcsEncodeChars v)

def canonicalBytesJCS (v : OmegaJson) : ByteArray :=
  (jcsEncode v).toUTF8

theorem jcsEncode_toList (v : OmegaJson) :
    (jcsEncode v).toList = jcsEncodeChars v := by
  simp [jcsEncode, jcsEncodeChars, String.toList_ofList]

end OmegaJCS
