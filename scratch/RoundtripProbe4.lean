import OmegaJCS.Encode

open OmegaJCS

#eval jcsEncodeChars (OmegaJson.arr [OmegaJson.null])
#eval encArrBodyFuel 1 [OmegaJson.null]
#eval jcsEncodeFuel 0 OmegaJson.null
#eval jcsEncodeFuel 1 OmegaJson.null
#eval jsonFuel (OmegaJson.arr [OmegaJson.null])
#eval jsonFuelList [OmegaJson.null]

example (v : OmegaJson) : jcsEncodeChars (OmegaJson.arr [v]) = '[' :: jcsEncodeChars v ++ [']'] := by
  dsimp [jcsEncodeChars, encArrBody, encArrSuffix]
  rfl

example : encArrBodyFuel 1 [OmegaJson.null] = jcsEncodeFuel 1 OmegaJson.null ++ [']'] := by
  dsimp [encArrBodyFuel, encArrSuffixFuel, jcsEncodeFuel, jsonFuel]
  rfl
