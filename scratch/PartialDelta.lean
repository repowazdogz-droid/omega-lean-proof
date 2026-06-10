import OmegaJCS.Types
import OmegaJCS.Encode

open OmegaJCS

theorem jcsEncode_int_ofNat (m : Nat) : jcsEncode (OmegaJson.int (Int.ofNat m)) = intToString (Int.ofNat m) := by native_decide +revert

theorem jcsEncode_int_negSucc (m : Nat) : jcsEncode (OmegaJson.int (Int.negSucc m)) = intToString (Int.negSucc m) := by native_decide +revert

theorem jcsEncode_int (n : Int) : jcsEncode (OmegaJson.int n) = intToString n := by
  cases n <;> first | apply jcsEncode_int_ofNat | apply jcsEncode_int_negSucc
