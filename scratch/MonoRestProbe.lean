import OmegaJCS.Decode

open OmegaJCS

#eval parseStringCharsGoFuel 12 ('"' :: []) ['"']
#eval parseStringCharsGoFuel 1 ('"' :: []) ['"']

example (acc : List Char) :
    parseStringCharsGoFuel 12 ('"' :: []) acc =
    parseStringCharsGoFuel 1 ('"' :: []) acc := by
  native_decide
