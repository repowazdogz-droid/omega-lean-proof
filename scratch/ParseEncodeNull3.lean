import OmegaJCS.Encode
import OmegaJCS.Decode
import OmegaJCS.Types
open OmegaJCS

theorem takePrefix_append (pre : String) (rest : List Char) :
    takePrefix (pre.toList ++ rest) pre = some rest := by
  unfold takePrefix startsWith
  have hlen : pre.toList.length = pre.length := by rw [String.length_toList]
  have htake : (pre.toList ++ rest).take pre.length = pre.toList := by
    rw [List.take_append, ← hlen, Nat.sub_self, List.take_zero, List.append_nil, List.take_length]
  have hdrop : (pre.toList ++ rest).drop pre.length = rest := by
    rw [List.drop_append, hlen, Nat.sub_self, List.drop_zero, ← hlen, List.drop_length, List.nil_append]
  simp [htake, hdrop]

example (fuel : Nat) (rest : List Char) (hf : nodeCount OmegaJson.null < fuel) :
    parseValueFuel fuel (jcsEncodeChars OmegaJson.null ++ rest) = some (OmegaJson.null, rest) := by
  native_decide
