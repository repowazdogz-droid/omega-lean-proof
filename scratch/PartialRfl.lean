import OmegaJCS.Types
import OmegaJCS.Encode

open OmegaJCS

theorem jcsEncode_int (n : Int) : jcsEncode (OmegaJson.int n) = intToString n := by
  cases n <;> native_decide +revert

theorem jcsEncodeChars_int (n : Int) : jcsEncodeChars (OmegaJson.int n) = intToStringChars n := by
  unfold jcsEncodeChars
  rw [jcsEncode_int n, intToString]
  rfl
