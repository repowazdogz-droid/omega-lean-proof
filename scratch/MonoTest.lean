import OmegaJCS.Decode

open OmegaJCS

theorem parseStringCharsGoFuel_mono_ge (fuel extra : Nat) (s acc : List Char)
    (hle : extra ≤ fuel) (hpos : 0 < extra) :
    parseStringCharsGoFuel fuel s acc = parseStringCharsGoFuel extra s acc := by
  induction fuel generalizing extra s acc with
  | zero =>
    have hz : extra = 0 := Nat.eq_zero_of_le_zero hle
    subst hz
    exact absurd hpos (Nat.not_lt_zero 0)
  | succ f ih =>
    match extra, hpos with
    | 0, hpos => exact absurd hpos (Nat.not_lt_zero 0)
    | e + 1, _ =>
      rcases Nat.eq_or_lt_of_le (Nat.le_of_succ_le_succ hle) with rfl | hlt
      · rfl
      · have hef : e + 1 ≤ f := Nat.succ_le_iff.mpr hlt
        match s with
        | [] => rfl
        | '"' :: rest => rfl
        | '\\' :: rest =>
          match rest with
          | [] => rfl
          | '"' :: r =>
            simp [parseStringCharsGoFuel]
            exact (ih (e + 1) r (acc ++ ['"']) hef (Nat.succ_pos e)).symm
          | '\\' :: r =>
            simp [parseStringCharsGoFuel]
            exact (ih (e + 1) r (acc ++ ['\\']) hef (Nat.succ_pos e)).symm
          | 'b' :: r =>
            simp [parseStringCharsGoFuel]
            exact (ih (e + 1) r (acc ++ [Char.ofNat 0x08]) hef (Nat.succ_pos e)).symm
          | 'f' :: r =>
            simp [parseStringCharsGoFuel]
            exact (ih (e + 1) r (acc ++ [Char.ofNat 0x0C]) hef (Nat.succ_pos e)).symm
          | 'n' :: r =>
            simp [parseStringCharsGoFuel]
            exact (ih (e + 1) r (acc ++ [Char.ofNat 0x0A]) hef (Nat.succ_pos e)).symm
          | 'r' :: r =>
            simp [parseStringCharsGoFuel]
            exact (ih (e + 1) r (acc ++ [Char.ofNat 0x0D]) hef (Nat.succ_pos e)).symm
          | 't' :: r =>
            simp [parseStringCharsGoFuel]
            exact (ih (e + 1) r (acc ++ [Char.ofNat 0x09]) hef (Nat.succ_pos e)).symm
          | 'u' :: r =>
            simp [parseStringCharsGoFuel]
            cases parseHex4 r with
            | none => rfl
            | some p =>
              exact (ih (e + 1) p.2 (acc ++ [Char.ofNat p.1]) hef (Nat.succ_pos e)).symm
          | _ :: _ => rfl
        | c :: rest =>
          simp [parseStringCharsGoFuel]
          exact (ih (e + 1) rest (acc ++ [c]) hef (Nat.succ_pos e)).symm

example (acc rest : List Char) :
    parseStringChars (escapeCharList '"' ++ rest) acc =
      parseStringChars rest (acc ++ ['"']) := by
  dsimp [escapeCharList, escapeChar, parseStringChars, parseStringCharsFuelBound, parseStringCharsGoFuel]
  have ht : ("\\\"").toList = ['\\', '"'] := rfl
  simp only [ht, List.cons_append, List.nil_append, parseStringCharsGoFuel]
  have hlen : ('\\' :: '"' :: rest).length * 6 = (2 + rest.length) * 6 := by simp; omega
  rw [hlen]
  exact parseStringCharsGoFuel_mono_ge ((2 + rest.length) * 6) (rest.length * 6 + 1) rest
    (acc ++ ['"']) (by omega) (by omega)
