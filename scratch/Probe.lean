import OmegaJCS.Encode
import OmegaJCS.Decode

open OmegaJCS

example : jcsEncodeChars .null = "null".toList := by
  dsimp only [jcsEncodeChars]
  rfl

example (v : OmegaJson) : jcsEncodeChars (.arr [v]) = '[' :: jcsEncodeChars v ++ [']'] := by
  dsimp only [jcsEncodeChars, encArrBody, encArrSuffix]
  rfl

example : parseNatDigits (['0'] ++ ([] : List Char)) 0 = some (0, []) := by
  dsimp only [parseNatDigits, isDigit]
  rfl
