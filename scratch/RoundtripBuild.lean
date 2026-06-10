import Init.Data.Nat.Bitwise.Lemmas
import OmegaJCS.Types
import OmegaJCS.Encode
import OmegaJCS.Decode

open OmegaJCS

private theorem parseStringGoFuel_nil (f : Nat) (acc : List Char) :
    parseStringCharsGoFuel f [] acc = none := by
  cases f with
  | zero => rfl
  | succ _ => rfl

theorem parseStringCharsGoFuel_mono (m n : Nat) (s acc : List Char) (h : m ≤ n) :
    parseStringCharsGoFuel (m + 1) s acc = parseStringCharsGoFuel (n + 1) s acc := by
  induction n generalizing m s acc with
  | zero =>
    have hm : m = 0 := Nat.eq_zero_of_le_zero h
    subst hm
    rfl
  | succ n ih =>
    rcases Nat.eq_or_lt_of_le h with rfl | hlt
    · rfl
    · have hle : m ≤ n := Nat.lt_succ_iff.mp hlt
      have ih' := ih m s acc hle
      match s with
      | [] =>
        rw [ih']
        simp [parseStringCharsGoFuel, parseStringGoFuel_nil]
      | '"' :: rest => rfl
      | '\\' :: rest =>
        simp only [parseStringCharsGoFuel]
        match rest with
        | [] => rfl
        | '"' :: r => exact ih r (acc ++ ['"']) (Nat.le_of_lt hlt)
        | '\\' :: r => exact ih r (acc ++ ['\\']) (Nat.le_of_lt hlt)
        | 'b' :: r => exact ih r (acc ++ [Char.ofNat 0x08]) (Nat.le_of_lt hlt)
        | 'f' :: r => exact ih r (acc ++ [Char.ofNat 0x08]) (Nat.le_of_lt hlt)
        | 'n' :: r => exact ih r (acc ++ [Char.ofNat 0x0A]) (Nat.le_of_lt hlt)
        | 'r' :: r => exact ih r (acc ++ [Char.ofNat 0x0D]) (Nat.le_of_lt hlt)
        | 't' :: r => exact ih r (acc ++ [Char.ofNat 0x09]) (Nat.le_of_lt hlt)
        | 'u' :: r =>
          simp only [parseStringCharsGoFuel]
          cases parseHex4 r with
          | none => rfl
          | some p => exact ih p.2 (acc ++ [Char.ofNat p.1]) (Nat.le_of_lt hlt)
        | _ :: _ => rfl
      | c :: rest =>
        simp only [parseStringCharsGoFuel]
        exact ih rest (acc ++ [c]) (Nat.le_of_lt hlt)

example (acc rest : List Char) :
    parseStringChars (escapeCharList '"' ++ rest) acc =
      parseStringChars rest (acc ++ ['"']) := by
  dsimp [escapeCharList, escapeChar, parseStringChars, parseStringCharsFuelBound, parseStringCharsGoFuel]
  have ht : ("\\\"").toList = ['\\', '"'] := rfl
  simp only [ht, List.cons_append, List.nil_append, parseStringCharsGoFuel]
  have hstep :
      parseStringCharsGoFuel ((2 + rest.length) * 6) ('"' :: rest) (acc ++ ['"']) =
        parseStringCharsGoFuel (rest.length * 6 + 1) rest (acc ++ ['"']) := by
    have hle : rest.length * 6 + 1 ≤ (2 + rest.length) * 6 := by omega
    have hm : rest.length * 6 ≤ (2 + rest.length) * 6 - 1 := by omega
    exact parseStringCharsGoFuel_mono (rest.length * 6) ((2 + rest.length) * 6 - 1) rest
      (acc ++ ['"']) hm
  simp only [parseStringCharsGoFuel, hstep]
