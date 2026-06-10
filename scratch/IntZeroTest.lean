import OmegaJCS.Decode
import OmegaJCS.Encode
open OmegaJCS
example (rest : List Char) : parseInt (intToStringChars 0 ++ rest) = some (0, rest) := by
  unfold intToStringChars natToDecimal parseInt
  simp only
  sorry
