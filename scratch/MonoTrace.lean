import OmegaJCS.Decode

open OmegaJCS

#eval parseStringCharsGoFuel 1 ('\\' :: '"' :: '"' :: []) []
#eval parseStringCharsGoFuel 0 ('"' :: '"' :: []) []
#eval parseStringCharsGoFuel 0 ('"' :: []) ['"']
