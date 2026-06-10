import OmegaJCS.Decode

open OmegaJCS

theorem parseStringCharsGoFuel_mono (m n : Nat) (s acc : List Char) (h : m ≤ n) :
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
      conv =>
        lhs; unfold parseStringCharsGoFuel
        rhs; unfold parseStringCharsGoFuel
      match s with
      | [] => rfl
      | '"' :: rest => rfl
      | '\\' :: rest =>
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
          | none => rfl
          | some p => exact ih m p.2 (acc ++ [Char.ofNat p.1]) hk
        | _ :: _ => rfl
      | c :: rest => exact ih m rest (acc ++ [c]) hk

theorem parseStringCharsGoFuel_mono_ge (fuel extra : Nat) (s acc : List Char)
    (hle : extra ≤ fuel) (hpos : 0 < extra) :
    parseStringCharsGoFuel fuel s acc = parseStringCharsGoFuel extra s acc := by
  have henz : extra ≠ 0 := Nat.pos_iff_ne_zero.mp hpos
  match extra with
  | 0 => exact (henz rfl).elim
  | e + 1 =>
    match fuel with
    | 0 => omega
    | f + 1 =>
      exact (parseStringCharsGoFuel_mono e f s acc (Nat.le_of_succ_le_succ hle)).symm

example (acc rest : List Char) :
    parseStringChars (escapeCharList '"' ++ rest) acc =
      parseStringChars rest (acc ++ ['"']) := by
  dsimp [escapeCharList, escapeChar, parseStringChars, parseStringCharsFuelBound, parseStringCharsGoFuel]
  have ht : ("\\\"").toList = ['\\', '"'] := rfl
  simp only [ht, List.cons_append, List.nil_append, parseStringCharsGoFuel]
  have hlen : ('\\' :: '"' :: rest).length * 6 = (2 + rest.length) * 6 := by
    simp only [List.length_cons]; omega
  rw [hlen]
  exact (parseStringCharsGoFuel_mono_ge ((2 + rest.length) * 6) (rest.length * 6 + 1) rest
    (acc ++ ['"']) (by omega) (by omega)).symm
