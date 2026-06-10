import OmegaJCS.Decode
import OmegaJCS.Encode

open OmegaJCS

example (acc rest : List Char) :
    parseStringChars (escapeCharList '"' ++ rest) acc =
      parseStringChars rest (acc ++ ['"']) := by
  rw [escapeCharList_quote]
  simp only [parseStringChars, List.cons_append, List.nil_append]

private theorem escapeCharList_quote : escapeCharList '"' = ['\\', '"'] := by native_decide
