#!/bin/bash
set -euo pipefail
cd /Users/warre/Omega/lean-proof
rm -f OmegaJCS/Roundtrip_test.lean

python3 << 'PY'
from pathlib import Path
root = Path("OmegaJCS")

encode = (root / "Encode.lean.bak").read_text() if (root / "Encode.lean.bak").exists() else ""
# use inline encode from our good version
encode = '''import OmegaJCS.Types

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
  if c == '"' then "\\\\" ++ "\\""
  else if c == '\\\\' then "\\\\\\\\"
  else if c.toNat == 0x08 then "\\\\" ++ "b"
  else if c.toNat == 0x0C then "\\\\" ++ "f"
  else if c.toNat == 0x0A then "\\\\" ++ "n"
  else if c.toNat == 0x0D then "\\\\" ++ "r"
  else if c.toNat == 0x09 then "\\\\" ++ "t"
  else if c.toNat < 0x20 then
    "\\\\u" ++ hex4Lower c.toNat
  else
    String.singleton c

def escapeCharList (c : Char) : List Char :=
  (escapeChar c).toList

def escapeStringChars (cs : List Char) : List Char :=
  cs.flatMap escapeCharList

def jcsEscapeString (s : String) : String :=
  "\\"" ++ String.join (s.toList.map escapeChar) ++ "\\""

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

def intToStringChars (n : Int) : List Char :=
  if n < 0 then '-' :: natToDecimal n.natAbs else natToDecimal n.toNat

def intToString (n : Int) : String :=
  String.ofList (intToStringChars n)

partial def jcsEncode : OmegaJson → String
  | .null => "null"
  | .bool true => "true"
  | .bool false => "false"
  | .int n => intToString n
  | .str s => jcsEscapeString s
  | .arr xs => "[" ++ String.intercalate "," (xs.map jcsEncode) ++ "]"
  | .obj kvs => "{" ++ String.intercalate "," (kvs.map fun ⟨k, v⟩ =>
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

end OmegaJCS
'''.replace('\\\\', '\\')  # fix escaping in python string

decode = Path("OmegaJCS/Decode.lean").read_text()
if "parseStringCharsGoFuel" in decode:
    raise SystemExit("Decode has fuel parser - abort")

# Write Roundtrip from template file if we have a good snapshot
rt = Path("OmegaJCS/Roundtrip.lean")
# minimal fix: use backup2 prefix+number+composite from earlier generation stored in Roundtrip.lean.bak2
bak2 = Path("OmegaJCS/Roundtrip.lean.bak2")
if not bak2.exists():
    raise SystemExit("missing Roundtrip.lean.bak2")

bak = bak2.read_text()
prefix_hex = bak[:bak.index("section ParseString")]
number_parse = bak[bak.index("section NumberParse"):bak.index("section FuelGe")]

parse_string = open("/Users/warre/Omega/lean-proof/OmegaJCS/_parse_string.lean").read() if Path("OmegaJCS/_parse_string.lean").exists() else ""

(root / "Encode.lean").write_text(encode)
print("wrote Encode")
PY

# If python failed, exit
test ! -f OmegaJCS/_parse_string.lean && cat > OmegaJCS/_parse_string.lean << 'PSEOF'
section ParseString

private theorem escapeCharList_quote : escapeCharList '"' = ['\\', '"'] := by native_decide
private theorem escapeCharList_backslash : escapeCharList '\\' = ['\\', '\\'] := by native_decide

private theorem parseStringChars_escapeCharList_quote (acc rest : List Char) :
    parseStringChars (escapeCharList '"' ++ rest) acc =
      parseStringChars rest (acc ++ ['"']) := by
  simp only [escapeCharList_quote, parseStringChars, List.cons_append, List.nil_append]

private theorem parseStringChars_escapeCharList_backslash (acc rest : List Char) :
    parseStringChars (escapeCharList '\\' ++ rest) acc =
      parseStringChars rest (acc ++ ['\\']) := by
  simp only [escapeCharList_backslash, parseStringChars, List.cons_append, List.nil_append]

private theorem parseStringChars_escapeCharList_ctrl (acc rest : List Char) (tag : Char)
    (h : tag = 'b' ∨ tag = 'f' ∨ tag = 'n' ∨ tag = 'r' ∨ tag = 't') :
    parseStringChars (['\\', tag] ++ rest) acc =
      parseStringChars rest (acc ++ [match tag with
        | 'b' => Char.ofNat 0x08 | 'f' => Char.ofNat 0x0C | 'n' => Char.ofNat 0x0A
        | 'r' => Char.ofNat 0x0D | 't' => Char.ofNat 0x09 | _ => tag]) := by
  rcases h with rfl | rfl | rfl | rfl | rfl <;> simp [parseStringChars, List.cons_append, List.nil_append]

private theorem parseStringChars_escapeCharList_unicode (c : Char) (acc rest : List Char)
    (h1 : c ≠ '"') (h2 : c ≠ '\\') (h3 : c.toNat ≠ 0x08) (h4 : c.toNat ≠ 0x0C)
    (h5 : c.toNat ≠ 0x0A) (h6 : c.toNat ≠ 0x0D) (h7 : c.toNat ≠ 0x09) (hlt : c.toNat < 0x20) :
    parseStringChars (escapeCharList c ++ rest) acc =
      parseStringChars rest (acc ++ [c]) := by
  simp only [escapeCharList, escapeChar, beq_iff_eq, h1, h2, h3, h4, h5, h6, h7, if_false, hlt,
    if_pos, String.append, String.toList, List.cons_append, List.nil_append, hex4Lower,
    hex4Lower_toList]
  have h0 := hexDigit_spec ((c.toNat >>> 12) &&& 0xF) (land_f_lt16 _)
  have h1d := hexDigit_spec ((c.toNat >>> 8) &&& 0xF) (land_f_lt16 _)
  have h2d := hexDigit_spec ((c.toNat >>> 4) &&& 0xF) (land_f_lt16 _)
  have h3d := hexDigit_spec (c.toNat &&& 0xF) (land_f_lt16 _)
  simp only [parseStringChars, List.cons_append, List.nil_append, h0, h1d, h2d, h3d,
    hex4_recomb_small c.toNat (by omega)]

private theorem parseStringChars_escapeCharList_plain (c : Char) (acc rest : List Char)
    (h1 : c ≠ '"') (h2 : c ≠ '\\') (h3 : c.toNat ≠ 0x08) (h4 : c.toNat ≠ 0x0C)
    (h5 : c.toNat ≠ 0x0A) (h6 : c.toNat ≠ 0x0D) (h7 : c.toNat ≠ 0x09) (h8 : ¬ c.toNat < 0x20) :
    parseStringChars (escapeCharList c ++ rest) acc =
      parseStringChars rest (acc ++ [c]) := by
  simp [parseStringChars, escapeCharList, escapeChar, beq_iff_eq, h1, h2, h3, h4, h5, h6, h7,
    if_false, h8, if_neg, String.singleton, String.toList, List.cons_append, List.nil_append]

theorem parseStringChars_escapeCharList (c : Char) (acc rest : List Char) :
    parseStringChars (escapeCharList c ++ rest) acc =
      parseStringChars rest (acc ++ [c]) := by
  rcases c with (_ | _ | c) <;> first | rfl | exact parseStringChars_escapeCharList_quote acc rest
      | exact parseStringChars_escapeCharList_backslash acc rest
  · exact parseStringChars_escapeCharList_ctrl acc rest 'b' (Or.inl rfl)
  · exact parseStringChars_escapeCharList_ctrl acc rest 'f' (Or.inr (Or.inl rfl))
  · exact parseStringChars_escapeCharList_ctrl acc rest 'n' (Or.inr (Or.inr (Or.inl rfl)))
  · exact parseStringChars_escapeCharList_ctrl acc rest 'r' (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  · exact parseStringChars_escapeCharList_ctrl acc rest 't' (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
  by_cases hlt : c.toNat < 0x20
  · exact parseStringChars_escapeCharList_unicode c acc rest (by rintro h; exact absurd rfl h)
      (by rintro h; exact absurd rfl h) (by rintro h; exact absurd rfl h)
      (by rintro h; exact absurd rfl h) (by rintro h; exact absurd rfl h)
      (by rintro h; exact absurd rfl h) (by rintro h; exact absurd rfl h) hlt
  · exact parseStringChars_escapeCharList_plain c acc rest (by rintro h; exact absurd rfl h)
      (by rintro h; exact absurd rfl h) (by rintro h; exact absurd rfl h)
      (by rintro h; exact absurd rfl h) (by rintro h; exact absurd rfl h)
      (by rintro h; exact absurd rfl h) (by rintro h; exact absurd rfl h) hlt

theorem parseStringChars_escapeStringChars (cs : List Char) (rest : List Char) :
    parseStringChars (escapeStringChars cs ++ rest) [] =
      parseStringChars rest (String.ofList cs).toList := by
  induction cs with
  | nil => simp [escapeStringChars]
  | cons c cs ih =>
    simp only [escapeStringChars, List.flatMap_cons, List.append_assoc]
    rw [← List.append_assoc, parseStringChars_escapeCharList, ih]

theorem parseStringChars_escapeString (s : String) (rest : List Char) :
    parseStringChars (escapeStringChars s.toList ++ '"' :: rest) [] = some (s, rest) := by
  have h := parseStringChars_escapeStringChars s.toList ('"' :: rest)
  simp [parseStringChars, String.toList_ofList] at h ⊢
  simpa using h

theorem parseString_jcsEscapeString (s : String) (rest : List Char) :
    parseString (jcsEscapeStringChars s ++ rest) = some (s, rest) := by
  unfold parseString jcsEscapeStringChars
  simpa [List.cons_append] using parseStringChars_escapeString s rest

end ParseString
PSEOF

echo "script incomplete - use direct write"
exit 1
