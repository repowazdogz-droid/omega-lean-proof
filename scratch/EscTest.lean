import OmegaJCS.Encode
import OmegaJCS.Decode
open OmegaJCS
example : escapeCharList '"' = ['\\', '"'] := by native_decide
example (acc rest : List Char) :
    parseStringChars (escapeCharList '"' ++ rest) acc =
      parseStringChars rest (acc ++ ['"']) := by
  conv_lhs => arg 1; rw [show escapeCharList '"' = ['\\', '"'] from by native_decide]
  simp [parseStringChars, List.cons_append, List.nil_append]
