import OmegaJCS.Decode
import OmegaJCS.Encode

open OmegaJCS

theorem parseStringCharsGoFuel_mono_ge (fuel extra : Nat) (s acc : List Char)
    (hle : extra ≤ fuel) (hpos : 0 < extra) :
    parseStringCharsGoFuel fuel s acc = parseStringCharsGoFuel extra s acc := by
  induction fuel generalizing extra s acc with
  | zero =>
    match extra with
    | 0 => exact (Nat.pos_iff_ne_zero.mp hpos rfl).elim
    | _ + 1 => omega
  | succ f ih =>
    match extra with
    | 0 => exact (Nat.pos_iff_ne_zero.mp hpos rfl).elim
    | e + 1 =>
      have he : e ≤ f := Nat.le_of_succ_le_succ hle
      rcases Nat.eq_or_lt_of_le he with rfl | hlt
      · rfl
      · exact ih (e + 1) s acc (Nat.succ_le_iff.mpr hlt) (by omega)

theorem parseStringCharsGoFuel_mono (m n : Nat) (s acc : List Char) (h : m ≤ n) :
    parseStringCharsGoFuel (m + 1) s acc = parseStringCharsGoFuel (n + 1) s acc := by
  have hpos : 0 < m + 1 := by omega
  have hle : m + 1 ≤ n + 1 := Nat.add_le_add_right h 1
  exact (parseStringCharsGoFuel_mono_ge (n + 1) (m + 1) s acc hle hpos).symm

example (acc rest : List Char) :
    parseStringChars (escapeCharList '"' ++ rest) acc =
      parseStringChars rest (acc ++ ['"']) := by
  dsimp [escapeCharList, escapeChar, parseStringChars, parseStringCharsFuelBound, parseStringCharsGoFuel]
  have ht : ("\\\"").toList = ['\\', '"'] := rfl
  simp only [ht, List.cons_append, List.nil_append, parseStringCharsGoFuel]
  have hlen : ('\\' :: '"' :: rest).length * 6 = (2 + rest.length) * 6 := by
    simp only [List.length_cons]; omega
  rw [hlen]
  exact parseStringCharsGoFuel_mono_ge ((2 + rest.length) * 6) (rest.length * 6 + 1) rest
    (acc ++ ['"']) (by omega) (by omega)
