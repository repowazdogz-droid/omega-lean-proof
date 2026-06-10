import OmegaJCS.Encode
import OmegaJCS.Decode

open OmegaJCS

example (v : OmegaJson) :
    jcsEncodeChars (OmegaJson.arr [v]) = '[' :: jcsEncodeChars v ++ [']'] := by
  dsimp [jcsEncodeChars, encArrBody, encArrSuffix]
  rfl

example (v w : OmegaJson) :
    jcsEncodeChars (OmegaJson.arr [v, w]) = '[' :: jcsEncodeChars v ++ ',' :: jcsEncodeChars w ++ [']'] := by
  dsimp [jcsEncodeChars, encArrBody, encArrSuffix]
  rfl

example (v : OmegaJson) (vs : List OmegaJson) :
    jcsEncodeChars (OmegaJson.arr (v :: vs)) = '[' :: jcsEncodeChars v ++ encArrSuffix (v :: vs) := by
  dsimp [jcsEncodeChars, encArrBody, encArrSuffix]
  rfl

example (k : String) (v : OmegaJson) :
    jcsEncodeChars (OmegaJson.obj [(k, v)]) = '{' :: jcsEscapeStringChars k ++ ':' :: jcsEncodeChars v ++ ['}'] := by
  dsimp [jcsEncodeChars, encObjBody, encObjSuffix]
  rfl

example (kv : String × OmegaJson) (kvs : List (String × OmegaJson)) :
    jcsEncodeChars (OmegaJson.obj (kv :: kvs)) =
      '{' :: jcsEscapeStringChars kv.1 ++ ':' :: jcsEncodeChars kv.2 ++ encObjSuffix (kv :: kvs) := by
  dsimp [jcsEncodeChars, encObjBody, encObjSuffix]
  rfl

example (acc rest : List Char) :
    parseStringChars (['\\', '"'] ++ rest) acc = some (String.ofList (acc ++ ['"']), rest) := by
  sorry

example (n : Nat) (rest : List Char) :
    parseNatDigits (natToDecimal n ++ rest) 0 = some (n, rest) := by
  sorry
