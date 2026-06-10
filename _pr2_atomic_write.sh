#!/bin/bash
set -euo pipefail
ROOT="/Users/warre/Omega/lean-proof"
cd "$ROOT"

rm -f OmegaJCS/Roundtrip_test.lean

cat > OmegaJCS/Encode.lean << 'EOF'
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

def jcsEncodeChars (v : OmegaJson) : List Char :=
  (jcsEncode v).toList

def encArrSuffix (xs : List OmegaJson) : List Char :=
  match xs with
  | [] => [']']
  | v :: vs => ',' :: jcsEncodeChars v ++ encArrSuffix vs

def encArrBody (xs : List OmegaJson) : List Char :=
  match xs with
  | [] => [']']
  | v :: vs => jcsEncodeChars v ++ encArrSuffix vs

def encObjPairChars (kv : String × OmegaJson) : List Char :=
  jcsEscapeStringChars kv.1 ++ ':' :: jcsEncodeChars kv.2

def encObjSuffix (kvs : List (String × OmegaJson)) : List Char :=
  match kvs with
  | [] => ['}']
  | kv :: kvs' => ',' :: encObjPairChars kv ++ encObjSuffix kvs'

def encObjBody (kvs : List (String × OmegaJson)) : List Char :=
  match kvs with
  | [] => ['}']
  | kv :: kvs' => encObjPairChars kv ++ encObjSuffix kvs'

def canonicalBytesJCS (v : OmegaJson) : ByteArray :=
  (jcsEncode v).toUTF8

theorem jcsEncode_toList (v : OmegaJson) :
    (jcsEncode v).toList = jcsEncodeChars v := rfl

@[simp] theorem jcsEncodeChars_null : jcsEncodeChars OmegaJson.null = "null".toList := rfl

@[simp] theorem jcsEncodeChars_bool (b : Bool) :
    jcsEncodeChars (OmegaJson.bool b) = (if b then "true" else "false").toList := by
  cases b <;> rfl

@[simp] theorem jcsEncodeChars_int (n : Int) :
    jcsEncodeChars (OmegaJson.int n) = intToStringChars n := rfl

@[simp] theorem jcsEncodeChars_str (s : String) :
    jcsEncodeChars (OmegaJson.str s) = jcsEscapeStringChars s := rfl

end OmegaJCS
EOF

cat > OmegaJCS/Decode.lean << 'EOF'
import OmegaJCS.Types
import OmegaJCS.Encode

namespace OmegaJCS

def startsWith (s : List Char) (pre : String) : Bool :=
  s.take pre.length = pre.toList

def takePrefix (s : List Char) (pre : String) : Option (List Char) :=
  if startsWith s pre then some (s.drop pre.length) else none

def isDigit (c : Char) : Bool :=
  '0'.toNat ≤ c.toNat ∧ c.toNat ≤ '9'.toNat

def parseNatDigits (s : List Char) (acc : Nat) : Option (Nat × List Char) :=
  match s with
  | [] => some (acc, [])
  | c :: rest =>
      if isDigit c then
        parseNatDigits rest (acc * 10 + (c.toNat - '0'.toNat))
      else
        some (acc, s)
termination_by s.length
decreasing_by
  all_goals simp only [List.length_cons]; apply Nat.lt_succ_self

def parseInt (s : List Char) : Option (Int × List Char) :=
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

def hexValue (c : Char) : Option Nat :=
  if '0'.toNat ≤ c.toNat ∧ c.toNat ≤ '9'.toNat then some (c.toNat - '0'.toNat)
  else if 'a'.toNat ≤ c.toNat ∧ c.toNat ≤ 'f'.toNat then some (c.toNat - 'a'.toNat + 10)
  else if 'A'.toNat ≤ c.toNat ∧ c.toNat ≤ 'F'.toNat then some (c.toNat - 'A'.toNat + 10)
  else none

def parseHex4 (s : List Char) : Option (Nat × List Char) :=
  match s with
  | a :: b :: c :: d :: rest =>
      match hexValue a, hexValue b, hexValue c, hexValue d with
      | some ha, some hb, some hc, some hd =>
          some (ha * 4096 + hb * 256 + hc * 16 + hd, rest)
      | _, _, _, _ => none
  | _ => none

partial def parseStringChars (s : List Char) (acc : List Char) : Option (String × List Char) :=
  match s with
  | [] => none
  | '"' :: rest => some (String.ofList acc, rest)
  | '\\' :: rest =>
      match rest with
      | [] => none
      | '"' :: r => parseStringChars r (acc ++ ['"'])
      | '\\' :: r => parseStringChars r (acc ++ ['\\'])
      | 'b' :: r => parseStringChars r (acc ++ [Char.ofNat 0x08])
      | 'f' :: r => parseStringChars r (acc ++ [Char.ofNat 0x0C])
      | 'n' :: r => parseStringChars r (acc ++ [Char.ofNat 0x0A])
      | 'r' :: r => parseStringChars r (acc ++ [Char.ofNat 0x0D])
      | 't' :: r => parseStringChars r (acc ++ [Char.ofNat 0x09])
      | 'u' :: a :: b :: c :: d :: r =>
          match hexValue a, hexValue b, hexValue c, hexValue d with
          | some ha, some hb, some hc, some hd =>
              parseStringChars r (acc ++ [Char.ofNat (ha * 4096 + hb * 256 + hc * 16 + hd)])
          | _, _, _, _ => none
      | _ => none
  | c :: rest => parseStringChars rest (acc ++ [c])
termination_by s.length
decreasing_by
  all_goals simp only [List.length_cons]
  first | apply Nat.lt_succ_self | apply Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_refl _)

def parseString (s : List Char) : Option (String × List Char) :=
  match s with
  | '"' :: rest => parseStringChars rest []
  | _ => none

mutual
  def parseValueFuel : Nat → List Char → Option (OmegaJson × List Char)
    | 0, _ => none
    | fuel + 1, s =>
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
          parseArrayFuel fuel rest []
        else if let some rest := takePrefix s "{" then
          parseObjectFuel fuel rest []
        else none

  def parseArrayFuel : Nat → List Char → List OmegaJson → Option (OmegaJson × List Char)
    | 0, _, _ => none
    | fuel + 1, ']' :: rest, acc => some (OmegaJson.arr acc.reverse, rest)
    | fuel + 1, s, acc =>
        match parseValueFuel fuel s with
        | some (v, rest') =>
            match rest' with
            | ',' :: rest'' => parseArrayFuel fuel rest'' (v :: acc)
            | ']' :: rest'' => some (OmegaJson.arr (v :: acc).reverse, rest'')
            | _ => none
        | none => none

  def parseObjectPairFuel : Nat → List Char → Option (String × OmegaJson × List Char)
    | 0, _ => none
    | fuel + 1, s =>
        match parseString s with
        | some (k, rest) =>
            match rest with
            | ':' :: rest' =>
                match parseValueFuel fuel rest' with
                | some (v, rest'') => some (k, v, rest'')
                | none => none
            | _ => none
        | none => none

  def parseObjectFuel : Nat → List Char → List (String × OmegaJson) → Option (OmegaJson × List Char)
    | 0, _, _ => none
    | fuel + 1, '}' :: rest, acc => some (OmegaJson.obj acc.reverse, rest)
    | fuel + 1, s, acc =>
        match parseObjectPairFuel fuel s with
        | some (k, v, rest') =>
            match rest' with
            | ',' :: rest'' => parseObjectFuel fuel rest'' ((k, v) :: acc)
            | '}' :: rest'' => some (OmegaJson.obj ((k, v) :: acc).reverse, rest'')
            | _ => none
        | none => none
end

def parseFuel (s : List Char) : Nat := s.length + 1

def parseValue (s : List Char) : Option (OmegaJson × List Char) :=
  parseValueFuel (parseFuel s) s

def parseArray (s : List Char) (acc : List OmegaJson) : Option (OmegaJson × List Char) :=
  parseArrayFuel (parseFuel s) s acc

def parseObjectPair (s : List Char) : Option (String × OmegaJson × List Char) :=
  parseObjectPairFuel (parseFuel s) s

def parseObject (s : List Char) (acc : List (String × OmegaJson)) :
    Option (OmegaJson × List Char) :=
  parseObjectFuel (parseFuel s) s acc

def jcsDecode (s : String) : Option OmegaJson :=
  match parseValue s.toList with
  | some (v, []) => some v
  | _ => none

end OmegaJCS
EOF

echo "Wrote Encode.lean and Decode.lean"
