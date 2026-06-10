import OmegaJCS.Decode

namespace OmegaJCS

theorem parseStringCharsGoFuel_mono_ge (fuel extra : Nat) (s acc : List Char)
    (hle : extra ≤ fuel) (hpos : 0 < extra) :
    parseStringCharsGoFuel fuel s acc = parseStringCharsGoFuel extra s acc := by
  induction fuel generalizing extra s acc with
  | zero => exact absurd hpos (Nat.not_lt_zero _)
  | succ f ih =>
    rcases extra with
    | zero => exact absurd hpos (Nat.not_lt_zero _)
    | succ e =>
      simp only [parseStringCharsGoFuel]
      rcases Nat.le_iff_eq_add_or_le.mp hle with rfl | hlt
      · rfl
      · have hele : e ≤ f := Nat.lt_succ_iff.mp hlt
        cases s with
        | nil => rfl
        | head :: tail =>
          cases head with
          | ofNat n =>
            by_cases hn : n = '"'.toNat
            · subst hn; rfl
            by_cases hn : n = '\\'.toNat
            · subst hn
              cases tail with
              | nil => rfl
              | t :: r =>
                cases t with
                | ofNat tn =>
                  by_cases htn : tn = '"'.toNat
                  · subst htn; exact ih r (acc ++ ['"']) hele (Nat.lt_succ_self _)
                  by_cases htn : tn = '\\'.toNat
                  · subst htn; exact ih r (acc ++ ['\\']) hele (Nat.lt_succ_self _)
                  by_cases htn : tn = 'b'.toNat
                  · subst htn; exact ih r (acc ++ [Char.ofNat 0x08]) hele (Nat.lt_succ_self _)
                  by_cases htn : tn = 'f'.toNat
                  · subst htn; exact ih r (acc ++ [Char.ofNat 0x0C]) hele (Nat.lt_succ_self _)
                  by_cases htn : tn = 'n'.toNat
                  · subst htn; exact ih r (acc ++ [Char.ofNat 0x0A]) hele (Nat.lt_succ_self _)
                  by_cases htn : tn = 'r'.toNat
                  · subst htn; exact ih r (acc ++ [Char.ofNat 0x0D]) hele (Nat.lt_succ_self _)
                  by_cases htn : tn = 't'.toNat
                  · subst htn; exact ih r (acc ++ [Char.ofNat 0x09]) hele (Nat.lt_succ_self _)
                  by_cases htn : tn = 'u'.toNat
                  · subst htn
                    cases parseHex4 r with
                    | none => rfl
                    | some (cp, r') => exact ih r' (acc ++ [Char.ofNat cp]) hele (Nat.lt_succ_self _)
                  · rfl
                | _ => rfl
            · exact ih tail (acc ++ [head]) hele (Nat.lt_succ_self _)
          | _ => exact ih tail (acc ++ [head]) hele (Nat.lt_succ_self _)

end OmegaJCS
