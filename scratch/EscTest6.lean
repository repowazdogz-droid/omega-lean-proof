import OmegaJCS.Encode
import OmegaJCS.Decode
open OmegaJCS
theorem escapeCharList_quote : escapeCharList '"' = ['\\', '"'] := by native_decide
example (acc rest : List Char) :
    parseStringChars (escapeCharList '"' ++ rest) acc =
      parseStringChars rest (acc ++ ['"']) := by
  rw [escapeCharList_quote, List.cons_append]
  unfold parseStringChars
  rfl
example (acc rest : List Char) :
    parseStringChars ('\\' :: '"' :: rest) acc =
      parseStringChars rest (acc ++ ['"']) := by
  unfold parseStringChars
  rfl
