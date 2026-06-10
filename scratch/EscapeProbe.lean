import OmegaJCS.Decode
import OmegaJCS.Encode

open OmegaJCS

example (acc rest : List Char) :
    parseStringChars (escapeCharList '"' ++ rest) acc =
      parseStringChars rest (acc ++ ['"']) := by
  dsimp [escapeCharList, escapeChar, parseStringChars, parseStringCharsFuelBound, parseStringCharsGoFuel]
  have ht : ("\\\"").toList = ['\\', '"'] := rfl
  simp only [beq_self_eq_true, if_true, ht, List.cons_append, List.nil_append, parseStringCharsGoFuel]
  simp only [parseStringCharsGoFuel, parseStringChars, parseStringCharsFuelBound]

example (m n : Nat) (s acc : List Char) (h : m ≤ n) :
    parseStringCharsGoFuel (m + 1) s acc = parseStringCharsGoFuel (n + 1) s acc := by
  induction n generalizing m s acc with
  | zero =>
    subst Nat.eq_zero_of_le_zero h
    rfl
  | succ k ih =>
    rcases Nat.eq_or_lt_of_le h with rfl | hlt
    · rfl
    · have hk : m ≤ k := Nat.le_of_lt_succ hlt
      rcases s with
      | [] => simp [parseStringCharsGoFuel]
      | head :: tail =>
        by_cases hquote : head = '"'
        · subst hquote
          simp [parseStringCharsGoFuel]
        · by_cases hbs : head = '\\'
          · subst hbs
            rcases tail with
            | [] => simp [parseStringCharsGoFuel]
            | t :: r =>
              by_cases h1 : t = '"'
              · subst h1
                conv =>
                  lhs; unfold parseStringCharsGoFuel
                  rhs; unfold parseStringCharsGoFuel
                exact ih m r (acc ++ ['"']) hk
              · sorry
          · simp [parseStringCharsGoFuel]
            exact ih m tail (acc ++ [head]) hk
