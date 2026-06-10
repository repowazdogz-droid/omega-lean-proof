import OmegaJCS.Decode

open OmegaJCS

#eval parseStringCharsGoFuel 2 ('\\' :: '"' :: '"' :: []) []
#eval parseStringCharsGoFuel 1 ('\\' :: '"' :: '"' :: []) []

example : parseStringCharsGoFuel 2 ('\\' :: '"' :: '"' :: []) [] =
    parseStringCharsGoFuel 1 ('\\' :: '"' :: '"' :: []) [] := by
  native_decide
