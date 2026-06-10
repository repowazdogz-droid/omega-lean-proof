import OmegaJCS.Decode
import OmegaJCS.Encode

namespace OmegaJCS

private theorem parseStringCharsGoFuel_pos (f : Nat) (s acc : List Char) (hf : 0 < f) :
    parseStringCharsGoFuel f s acc = parseStringCharsGo s acc := by
  match f with
  | 0 => omega
  | _ + 1 => rfl

private theorem parseStringChars_go (s acc : List Char) :
    parseStringChars s acc = parseStringCharsGo s acc := by
  unfold parseStringChars parseStringCharsFuelBound
  exact parseStringCharsGoFuel_pos (s.length * 6 + 1) s acc (by omega)

example (acc rest : List Char) :
    parseStringChars (escapeCharList '"' ++ rest) acc =
      parseStringChars rest (acc ++ ['"']) := by
  rw [parseStringChars_go, parseStringChars_go]
  dsimp [escapeCharList, escapeChar, parseStringCharsGo]
  have ht : ("\\\"").toList = ['\\', '"'] := rfl
  simp only [ht, List.cons_append, List.nil_append]
  rfl

end OmegaJCS
