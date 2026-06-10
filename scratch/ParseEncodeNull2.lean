import OmegaJCS.Encode
import OmegaJCS.Decode
import OmegaJCS.Types
open OmegaJCS

example (fuel rest : Nat) (hf : nodeCount OmegaJson.null < fuel) :
    parseValueFuel fuel (jcsEncodeChars OmegaJson.null ++ rest) = some (OmegaJson.null, rest) := by
  dsimp [jcsEncodeChars, jcsEncode, takePrefix_append]
  rfl
