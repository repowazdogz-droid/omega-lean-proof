import OmegaJCS.Types
import OmegaJCS.Encode
import OmegaJCS.Decode

namespace OmegaJCS

theorem probe_quote (acc rest : List Char) :
    parseStringChars (escapeCharList '"' ++ rest) acc =
      parseStringChars rest (acc ++ ['"']) := by
  simp only [escapeCharList, escapeChar, beq_iff_eq, if_true,
    String.toList, List.cons_append, List.nil_append]
  unfold parseStringChars
  rfl

end OmegaJCS
