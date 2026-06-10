import OmegaJCS.Roundtrip
open OmegaJCS

example (fuel rest : Nat) (hf : nodeCount OmegaJson.null < fuel) :
    parseValueFuel fuel (jcsEncodeChars OmegaJson.null ++ rest) = some (OmegaJson.null, rest) := by
  native_decide
