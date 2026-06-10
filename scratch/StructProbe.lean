import OmegaJCS.Encode
import OmegaJCS.Decode

open OmegaJCS

example : jcsEncodeChars (OmegaJson.arr []) = ['[', ']'] := by
  dsimp [jcsEncodeChars, encArrBody, encArrSuffix, jsonFuel, jsonFuelList, jcsEncodeFuel, encArrBodyFuel, encArrSuffixFuel]
  rfl

example (v : OmegaJson) :
    jcsEncodeChars (OmegaJson.arr [v]) = '[' :: jcsEncodeChars v ++ [']'] := by
  dsimp [jcsEncodeChars, encArrBody, encArrSuffix, jsonFuel, jsonFuelList, jcsEncodeFuel, encArrBodyFuel, encArrSuffixFuel]
  rfl

example (v w : OmegaJson) :
    jcsEncodeChars (OmegaJson.arr [v, w]) = '[' :: jcsEncodeChars v ++ ',' :: jcsEncodeChars w ++ [']'] := by
  dsimp [jcsEncodeChars, encArrBody, encArrSuffix, jsonFuel, jsonFuelList, jcsEncodeFuel, encArrBodyFuel, encArrSuffixFuel]
  rfl

example (v : OmegaJson) (vs : List OmegaJson) :
    jcsEncodeChars (OmegaJson.arr (v :: vs)) = '[' :: jcsEncodeChars v ++ encArrSuffix (v :: vs) := by
  dsimp [jcsEncodeChars, encArrBody, encArrSuffix, jsonFuel, jsonFuelList, jcsEncodeFuel, encArrBodyFuel, encArrSuffixFuel]
  rfl

example (k v : String) (vs : List (String × OmegaJson)) :
    jcsEncodeChars (OmegaJson.obj [(k, v)]) = '{' :: jcsEscapeStringChars k ++ ':' :: jcsEncodeChars v ++ ['}'] := by
  dsimp [jcsEncodeChars, encObjBody, encObjSuffix, jsonFuel, jsonFuelObj, jcsEncodeFuel, encObjBodyFuel, encObjSuffixFuel]
  rfl

example (k1 k2 : String) (v1 v2 : OmegaJson) :
    jcsEncodeChars (OmegaJson.obj [(k1, v1), (k2, v2)]) =
      '{' :: jcsEscapeStringChars k1 ++ ':' :: jcsEncodeChars v1 ++
        ',' :: (jcsEscapeStringChars k2 ++ ':' :: jcsEncodeChars v2) ++ ['}'] := by
  dsimp [jcsEncodeChars, encObjBody, encObjSuffix, jsonFuel, jsonFuelObj, jcsEncodeFuel, encObjBodyFuel, encObjSuffixFuel]
  rfl

example (kv : String × OmegaJson) (kvs : List (String × OmegaJson)) :
    jcsEncodeChars (OmegaJson.obj (kv :: kvs)) =
      '{' :: jcsEscapeStringChars kv.1 ++ ':' :: jcsEncodeChars kv.2 ++ encObjSuffix (kv :: kvs) := by
  dsimp [jcsEncodeChars, encObjBody, encObjSuffix, jsonFuel, jsonFuelObj, jcsEncodeFuel, encObjBodyFuel, encObjSuffixFuel]
  rfl

example (m n : Nat) (s acc : List Char) (h : m ≤ n) :
    parseStringCharsGoFuel (m + 1) s acc = parseStringCharsGoFuel (n + 1) s acc := by
  induction n generalizing m s acc with
  | zero =>
    subst Nat.eq_zero_of_le_zero h
    rfl
  | succ k ih =>
    rcases Nat.eq_or_lt_of_le h with rfl | hlt
    · rfl
    · have hk : m ≤ k := Nat.lt_succ_iff.mp hlt
      cases s with
      | nil => simp [parseStringCharsGoFuel]
      | cons c s =>
        cases c with
        | ofNat n =>
          cases n with
          | zero => sorry
          | succ n => sorry

example (acc rest : List Char) :
    parseStringChars (['\\', '"'] ++ rest) acc = parseStringChars rest (acc ++ ['"']) := by
  dsimp [parseStringChars, parseStringCharsFuelBound, parseStringCharsGoFuel, escapeCharList, escapeChar]
  simp only [beq_self_eq_true, if_true, String.toList_append, String.toList_singleton, List.append_assoc]

example (n : Nat) (rest : List Char) :
    parseNatDigits (natToDecimal n ++ rest) 0 = some (n, rest) := by
  cases n with
  | zero =>
    induction rest with
    | nil => simp [natToDecimal, parseNatDigits]
    | cons c rest ih =>
      by_cases hd : isDigit c
      · simp [parseNatDigits, hd, List.append_assoc, ih]
      · simp [natToDecimal, parseNatDigits, hd, List.append_assoc]
  | succ n => sorry
