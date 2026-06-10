import OmegaJCS.Encode

open OmegaJCS

example (xs : List OmegaJson) :
    jcsEncodeChars (OmegaJson.arr xs) = '[' :: encArrBody xs := by
  exact jcsEncodeChars_arr xs

example (v : OmegaJson) (vs : List OmegaJson) :
    encArrBody (v :: vs) = jcsEncodeChars v ++ encArrSuffix (v :: vs) := by
  exact encArrBody_cons v vs

example : jcsEncodeFuel 2 OmegaJson.null = "null".toList := by
  simp [jcsEncodeFuel_null]
