import OmegaJCS.Decode
import OmegaJCS.Encode

open OmegaJCS

private theorem parseStringGoFuel_nil (f : Nat) (acc : List Char) :
    parseStringCharsGoFuel f [] acc = none := by cases f <;> rfl

theorem parseStringCharsGoFuel_mono (m n : Nat) (s acc : List Char) (h : m ≤ n) :
    parseStringCharsGoFuel (m + 1) s acc = parseStringCharsGoFuel (n + 1) s acc := by
  induction n generalizing m s acc with
  | zero =>
    have hm : m = 0 := Nat.eq_zero_of_le_zero h
    subst hm; rfl
  | succ n ih =>
    rcases Nat.eq_or_lt_of_le h with rfl | hlt
    · rfl
    · have hle : m ≤ n := Nat.lt_succ_iff.mp hlt
      match s with
      | [] => simp [parseStringCharsGoFuel, parseStringGoFuel_nil]
      | '"' :: rest => rfl
      | '\\' :: rest =>
        simp only [parseStringCharsGoFuel]
        match rest with
        | [] => rfl
        | '"' :: r => exact ih m r (acc ++ ['"']) hle
        | '\\' :: r => exact ih m r (acc ++ ['\\']) hle
        | 'b' :: r => exact ih m r (acc ++ [Char.ofNat 0x08]) hle
        | 'f' :: r => exact ih m r (acc ++ [Char.ofNat 0x0C]) hle
        | 'n' :: r => exact ih m r (acc ++ [Char.ofNat 0x0A]) hle
        | 'r' :: r => exact ih m r (acc ++ [Char.ofNat 0x0D]) hle
        | 't' :: r => exact ih m r (acc ++ [Char.ofNat 0x09]) hle
        | 'u' :: r =>
          cases parseHex4 r with
          | none => rfl
          | some p => exact ih m p.2 (acc ++ [Char.ofNat p.1]) hle
        | _ :: _ => rfl
      | c :: rest => exact ih m rest (acc ++ [c]) hle

example (acc rest : List Char) :
    parseStringChars (escapeCharList '"' ++ rest) acc =
      parseStringChars rest (acc ++ ['"']) := by
  dsimp [parseStringChars, parseStringCharsGo, parseStringCharsFuelBound, escapeCharList, escapeChar]
  have ht : ("\\\"").toList = ['\\', '"'] := rfl
  simp only [ht, List.cons_append, List.nil_append, parseStringCharsGoFuel]
  exact parseStringCharsGoFuel_mono (rest.length * 6) ((2 + rest.length) * 6 - 1) rest
    (acc ++ ['"']) (by omega)
