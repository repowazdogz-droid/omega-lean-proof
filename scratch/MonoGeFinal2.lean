import OmegaJCS.Decode
open OmegaJCS

private theorem parseStringGoFuel_nil (f : Nat) (acc : List Char) :
    parseStringCharsGoFuel f [] acc = none := by
  cases f <;> rfl

private theorem rest_extra_ge7 (rest : List Char) (h : rest ≠ []) : 7 ≤ rest.length * 6 + 1 := by
  cases rest with
  | nil => exact absurd rfl h
  | cons _ _ => simp [List.length_cons]; omega

theorem parseStringCharsGoFuel_mono_ge (fuel extra : Nat) (s acc : List Char)
    (hle : extra ≤ fuel) (hpos : 0 < extra) (h7 : 7 ≤ extra) :
    parseStringCharsGoFuel fuel s acc = parseStringCharsGoFuel extra s acc := by
  induction fuel generalizing extra s acc with
  | zero =>
    have hz := Nat.eq_zero_of_le_zero hle
    subst hz
    exact absurd hpos (Nat.not_lt_zero _)
  | succ f ih =>
    cases extra with
    | zero => exact absurd hpos (Nat.not_lt_zero _)
    | succ e =>
      rcases Nat.eq_or_lt_of_le (Nat.le_of_succ_le_succ hle) with heq | hlt
      · subst heq; rfl
      · have hele : e ≤ f := Nat.le_of_lt hlt
        match s with
        | [] => simp [parseStringCharsGoFuel, parseStringGoFuel_nil]
        | '"' :: rest => simp [parseStringCharsGoFuel]
        | '\\' :: rest =>
          match rest with
          | [] => simp [parseStringCharsGoFuel]
          | '"' :: r =>
            simp [parseStringCharsGoFuel]
            by_cases he0 : e = 0
            · subst he0; simp [parseStringCharsGoFuel]
            · exact ih e r (acc ++ ['"']) hele (Nat.pos_of_ne_zero he0) (by omega)
          | '\\' :: r =>
            simp [parseStringCharsGoFuel]
            by_cases he0 : e = 0
            · subst he0; simp [parseStringCharsGoFuel]
            · exact ih e r (acc ++ ['\\']) hele (Nat.pos_of_ne_zero he0) (by omega)
          | 'b' :: r =>
            simp [parseStringCharsGoFuel]
            by_cases he0 : e = 0
            · subst he0; simp [parseStringCharsGoFuel]
            · exact ih e r (acc ++ [Char.ofNat 0x08]) hele (Nat.pos_of_ne_zero he0) (by omega)
          | 'f' :: r =>
            simp [parseStringCharsGoFuel]
            by_cases he0 : e = 0
            · subst he0; simp [parseStringCharsGoFuel]
            · exact ih e r (acc ++ [Char.ofNat 0x0C]) hele (Nat.pos_of_ne_zero he0) (by omega)
          | 'n' :: r =>
            simp [parseStringCharsGoFuel]
            by_cases he0 : e = 0
            · subst he0; simp [parseStringCharsGoFuel]
            · exact ih e r (acc ++ [Char.ofNat 0x0A]) hele (Nat.pos_of_ne_zero he0) (by omega)
          | 'r' :: r =>
            simp [parseStringCharsGoFuel]
            by_cases he0 : e = 0
            · subst he0; simp [parseStringCharsGoFuel]
            · exact ih e r (acc ++ [Char.ofNat 0x0D]) hele (Nat.pos_of_ne_zero he0) (by omega)
          | 't' :: r =>
            simp [parseStringCharsGoFuel]
            by_cases he0 : e = 0
            · subst he0; simp [parseStringCharsGoFuel]
            · exact ih e r (acc ++ [Char.ofNat 0x09]) hele (Nat.pos_of_ne_zero he0) (by omega)
          | 'u' :: r =>
            simp [parseStringCharsGoFuel]
            cases parseHex4 r with
            | none => rfl
            | some p =>
              by_cases he0 : e = 0
              · subst he0; simp [parseStringCharsGoFuel]
              · exact ih e p.2 (acc ++ [Char.ofNat p.1]) hele (Nat.pos_of_ne_zero he0) (by omega)
          | _ :: _ => simp [parseStringCharsGoFuel]
        | c :: rest =>
          simp [parseStringCharsGoFuel]
          by_cases he0 : e = 0
          · subst he0; simp [parseStringCharsGoFuel]
          · exact ih e rest (acc ++ [c]) hele (Nat.pos_of_ne_zero he0) (by omega)

private theorem parseStringChars_tail_mono (rest acc : List Char) (h : rest ≠ [])
    (hfuel : Nat) (hle : rest.length * 6 + 1 ≤ hfuel) :
    parseStringCharsGoFuel hfuel rest acc =
      parseStringCharsGoFuel (rest.length * 6 + 1) rest acc :=
  parseStringCharsGoFuel_mono_ge hfuel (rest.length * 6 + 1) rest acc (by omega) (by omega)
    (rest_extra_ge7 rest h)

private theorem parseStringChars_escapeCharList_quote (acc rest : List Char) :
    parseStringChars (escapeCharList '"' ++ rest) acc =
      parseStringChars rest (acc ++ ['"']) := by
  dsimp [parseStringChars, parseStringCharsGo, parseStringCharsFuelBound, escapeCharList, escapeChar]
  have ht : ("\\\"").toList = ['\\', '"'] := rfl
  rw [ht, List.cons_append, List.nil_append]
  cases rest with
  | nil =>
    simp [parseStringCharsGoFuel, parseStringGoFuel_nil, List.length_nil]
  | cons c rest' =>
    simp only [parseStringCharsGoFuel, List.length_cons]
    exact parseStringChars_tail_mono (c :: rest') (acc ++ ['"']) (by intro h; cases h)
      _ (by simp [List.length_cons]; omega)
