import OmegaJCS.Decode
import OmegaJCS.Encode

open OmegaJCS

example (acc rest : List Char) :
    parseStringChars (escapeCharList '"' ++ rest) acc =
      parseStringChars rest (acc ++ ['"']) := by
  dsimp [escapeCharList, escapeChar, parseStringChars, parseStringCharsFuelBound, parseStringCharsGoFuel]
  have ht : ("\\\"").toList = ['\\', '"'] := rfl
  simp only [beq_iff_eq, if_true, ht, List.cons_append, List.nil_append, parseStringCharsGoFuel]
