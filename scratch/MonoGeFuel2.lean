import OmegaJCS.Decode

namespace OmegaJCS

theorem parseStringCharsGoFuel_mono_ge (fuel extra : Nat) (s acc : List Char)
    (hle : extra ≤ fuel) (hpos : 0 < extra) :
    parseStringCharsGoFuel fuel s acc = parseStringCharsGoFuel extra s acc := by
  induction fuel generalizing extra s acc with
  | zero =>
    have he : extra = 0 := Nat.eq_zero_of_le_zero hle
    subst he
    exact absurd hpos (Nat.not_lt_zero _)
  | succ f ih =>
    cases extra with
    | zero => exact absurd hpos (Nat.not_lt_zero _)
    | succ e =>
      rcases Nat.eq_or_lt_of_le hle with heq | hlt
      · have hf : e = f := by injection heq
        subst hf; rfl
      · have hele : e ≤ f := Nat.le_of_lt (Nat.lt_of_succ_lt_succ hlt)
        unfold parseStringCharsGoFuel
        match s with
        | [] => rfl
        | '"' :: rest => rfl
        | '\\' :: rest =>
          match rest with
          | [] => rfl
          | '"' :: r => exact ih r (acc ++ ['"']) hele (Nat.lt_succ_self _)
          | '\\' :: r => exact ih r (acc ++ ['\\']) hele (Nat.lt_succ_self _)
          | 'b' :: r => exact ih r (acc ++ [Char.ofNat 0x08]) hele (Nat.lt_succ_self _)
          | 'f' :: r => exact ih r (acc ++ [Char.ofNat 0x0C]) hele (Nat.lt_succ_self _)
          | 'n' :: r => exact ih r (acc ++ [Char.ofNat 0x0A]) hele (Nat.lt_succ_self _)
          | 'r' :: r => exact ih r (acc ++ [Char.ofNat 0x0D]) hele (Nat.lt_succ_self _)
          | 't' :: r => exact ih r (acc ++ [Char.ofNat 0x09]) hele (Nat.lt_succ_self _)
          | 'u' :: r =>
            match parseHex4 r with
            | none => rfl
            | some (cp, r') => exact ih r' (acc ++ [Char.ofNat cp]) hele (Nat.lt_succ_self _)
          | _ :: _ => rfl
        | c :: rest => exact ih rest (acc ++ [c]) hele (Nat.lt_succ_self _)

end OmegaJCS
