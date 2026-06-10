import OmegaJCS.Decode

open OmegaJCS

example (m n : Nat) (s acc : List Char) (h : m ≤ n) :
    parseStringCharsGoFuel (m + 1) s acc = parseStringCharsGoFuel (n + 1) s acc := by
  induction n generalizing m s acc with
  | zero =>
    have hm : m = 0 := Nat.eq_zero_of_le_zero h
    subst hm
    rfl
  | succ k ih =>
    rcases Nat.eq_or_lt_of_le h with rfl | hlt
    · rfl
    · have hk : m ≤ k := Nat.le_of_lt_succ hlt
      match s with
      | [] => simp [parseStringCharsGoFuel]
      | '"' :: rest => simp [parseStringCharsGoFuel]
      | '\\' :: rest =>
        conv =>
          lhs; unfold parseStringCharsGoFuel
          rhs; unfold parseStringCharsGoFuel
        match rest with
        | '"' :: r => exact ih m r (acc ++ ['"']) hk
        | '\\' :: r => exact ih m r (acc ++ ['\\']) hk
        | 'b' :: r => exact ih m r (acc ++ [Char.ofNat 0x08]) hk
        | 'f' :: r => exact ih m r (acc ++ [Char.ofNat 0x0C]) hk
        | 'n' :: r => exact ih m r (acc ++ [Char.ofNat 0x0A]) hk
        | 'r' :: r => exact ih m r (acc ++ [Char.ofNat 0x0D]) hk
        | 't' :: r => exact ih m r (acc ++ [Char.ofNat 0x09]) hk
        | 'u' :: r =>
          cases parseHex4 r with
          | none => simp [parseStringCharsGoFuel]
          | some p => simp [parseStringCharsGoFuel]; exact ih m p.2 (acc ++ [Char.ofNat p.1]) hk
        | _ :: _ => simp [parseStringCharsGoFuel]
      | c :: rest =>
        simp only [parseStringCharsGoFuel]
        exact ih m rest (acc ++ [c]) hk
