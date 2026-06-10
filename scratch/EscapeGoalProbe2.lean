import OmegaJCS.Decode

open OmegaJCS

#eval parseStringCharsGoFuel 12 ('"' :: []) []
#eval parseStringCharsGoFuel 1 ('"' :: []) []

example : parseStringCharsGoFuel 12 ('"' :: []) [] =
    parseStringCharsGoFuel 1 ('"' :: []) [] := by
  native_decide
