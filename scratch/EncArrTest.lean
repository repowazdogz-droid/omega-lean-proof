import OmegaJCS.Encode

open OmegaJCS

example (xs : List OmegaJson) :
    jcsEncodeChars (OmegaJson.arr xs) = '[' :: encArrBody xs := by
  cases xs <;> dsimp [jcsEncodeChars, jcsEncode, encArrBody, encArrSuffix] <;> rfl

example (s t : String) (ss : List String) :
    String.intercalate "," (s :: t :: ss) = s ++ "," ++ String.intercalate "," (t :: ss) := by
  unfold String.intercalate String.intercalate.go
  rfl
