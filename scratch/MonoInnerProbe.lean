import OmegaJCS.Decode

open OmegaJCS

#eval parseStringCharsGoFuel 1 ('"' :: []) ['"']
#eval parseStringCharsGoFuel 0 ('"' :: []) ['"']

example : parseStringCharsGoFuel 1 ('"' :: []) ['"'] =
    parseStringCharsGoFuel 0 ('"' :: []) ['"'] := by
  native_decide
