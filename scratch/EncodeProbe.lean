import OmegaJCS.Encode

open OmegaJCS

#check @jcsEncodeChars
#check @encArrBody

example : jcsEncodeChars (.arr []) = ['[', ']'] := by
  dsimp [jcsEncodeChars, encArrBody]
  rfl

example (v : OmegaJson) : jcsEncodeChars (.arr [v]) = '[' :: jcsEncodeChars v ++ [']'] := by
  dsimp [jcsEncodeChars, encArrBody, encArrSuffix]
  rfl

example : parseNatDigits (['0'] ++ ([] : List Char)) 0 = some (0, []) := by
  dsimp [parseNatDigits, isDigit]
  rfl
