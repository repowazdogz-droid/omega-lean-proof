import OmegaJCS.Encode
import OmegaJCS.Decode

open OmegaJCS

example : jcsEncodeChars (OmegaJson.arr []) = '[' :: encArrBody [] := by
  dsimp [jcsEncodeChars, encArrBody, jsonFuel, jsonFuelList, jcsEncodeFuel, encArrBodyFuel]
  rfl

example (xs : List OmegaJson) :
    jcsEncodeChars (OmegaJson.arr xs) = '[' :: encArrBody xs := by
  dsimp [jcsEncodeChars, encArrBody, jsonFuel, jsonFuelList, jcsEncodeFuel, encArrBodyFuel]
  rfl

example (kvs : List (String × OmegaJson)) :
    jcsEncodeChars (OmegaJson.obj kvs) = '{' :: encObjBody kvs := by
  dsimp [jcsEncodeChars, encObjBody, jsonFuel, jsonFuelObj, jcsEncodeFuel, encObjBodyFuel]
  rfl

example (v : OmegaJson) (vs : List OmegaJson) :
    encArrBody (v :: vs) = jcsEncodeChars v ++ encArrSuffix (v :: vs) := by
  dsimp [encArrBody, encArrSuffix, jsonFuel, jsonFuelList, encArrBodyFuel, encArrSuffixFuel, jcsEncodeChars, jcsEncodeFuel]
  rfl

example (xs : List OmegaJson) (h : (OmegaJson.arr xs).WF) (x : OmegaJson) (hx : x ∈ xs) : x.WF := by
  dsimp [OmegaJson.WF] at h
  exact List.all_eq_true.mp h x hx

example (kvs : List (String × OmegaJson)) (h : (OmegaJson.obj kvs).WF) (kv : String × OmegaJson) (hkv : kv ∈ kvs) :
    kv.2.WF := by
  dsimp [OmegaJson.WF] at h
  simp only [OmegaJson.wfBool] at h
  have hall := (Bool.and_eq_true.mp h).1
  exact List.all_eq_true.mp hall kv hkv

example (n : Nat) (rest : List Char) :
    parseNatDigits (natToDecimal n ++ rest) 0 = some (n, rest) := by
  cases n <;> dsimp [natToDecimal, parseNatDigits]

example (acc rest : List Char) :
    parseStringCharsGoFuel 10 ("\\".toList ++ "\"".toList ++ rest) acc =
      parseStringCharsGoFuel 9 rest (acc ++ ['"']) := by
  dsimp [parseStringCharsGoFuel]
  rfl
