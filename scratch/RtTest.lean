import Init.Data.Nat.Bitwise.Lemmas
import OmegaJCS.Types
import OmegaJCS.Encode
import OmegaJCS.Decode

open OmegaJCS

example (acc rest : List Char) :
    parseStringChars (escapeCharList '"' ++ rest) acc =
      parseStringChars rest (acc ++ ['"']) := by
  dsimp [escapeCharList, escapeChar, beq_self_eq_true]
  simp only [parseStringChars, List.cons_append, List.nil_append]

example (acc rest : List Char) :
    parseStringChars (escapeCharList '\\' ++ rest) acc =
      parseStringChars rest (acc ++ ['\\']) := by
  dsimp [escapeCharList, escapeChar]
  simp only [parseStringChars, beq_iff_eq, Bool.false_eq_true, List.cons_append, List.nil_append]

example (acc rest : List Char) :
    parseStringChars (['\\', 'b'] ++ rest) acc =
      parseStringChars rest (acc ++ [Char.ofNat 0x08]) := by
  simp only [parseStringChars, List.cons_append]

example (acc rest : List Char) :
    parseStringChars ('"' :: rest) acc = some (String.ofList acc, rest) := by
  simp only [parseStringChars]

example (xs : List OmegaJson) :
    jcsEncodeChars (OmegaJson.arr xs) = '[' :: encArrBody xs := by
  dsimp [jcsEncodeChars, encArrBody, encArrSuffix, jcsEncodeFuel, jsonFuel, jsonFuelList]
  rfl

example (s : String) :
    String.intercalate "," [s] = s := by
  unfold String.intercalate
  rfl

example (d : Nat) (hd : d < 10) :
    isDigit (Char.ofNat (d + '0'.toNat)) = true := by
  revert d hd; decide +revert
