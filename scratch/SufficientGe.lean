import OmegaJCS.Decode
open OmegaJCS

theorem parseStringCharsGoFuel_ge (fuel : Nat) (s acc : List Char)
    (h : parseStringCharsFuelBound s ≤ fuel) :
    parseStringCharsGoFuel fuel s acc =
      parseStringCharsGoFuel (parseStringCharsFuelBound s) s acc := by
  induction fuel with
  | zero =>
    have hb : parseStringCharsFuelBound s = 0 := by simpa using h
    cases s <;> simp [parseStringCharsGoFuel, parseStringCharsFuelBound, hb]
  | succ fuel' ih =>
    by_cases hle : parseStringCharsFuelBound s ≤ fuel'
    · exact ih hle
    · have hb : parseStringCharsFuelBound s = fuel' + 1 := by
        simp [parseStringCharsFuelBound] at h hle ⊢
        omega
      subst hb
      match s with
      | [] => simp [parseStringCharsGoFuel]
      | '"' :: rest => simp [parseStringCharsGoFuel]
      | '\\' :: rest =>
        simp [parseStringCharsGoFuel]
        match rest with
        | [] => rfl
        | '"' :: r =>
          simpa using
            parseStringCharsGoFuel_ge fuel' r (acc ++ ['"']) (by simp [List.length_cons]; omega)
        | '\\' :: r =>
          simpa using
            parseStringCharsGoFuel_ge fuel' r (acc ++ ['\\']) (by simp [List.length_cons]; omega)
        | 'b' :: r =>
          simpa using
            parseStringCharsGoFuel_ge fuel' r (acc ++ [Char.ofNat 0x08]) (by simp [List.length_cons]; omega)
        | 'f' :: r =>
          simpa using
            parseStringCharsGoFuel_ge fuel' r (acc ++ [Char.ofNat 0x0C]) (by simp [List.length_cons]; omega)
        | 'n' :: r =>
          simpa using
            parseStringCharsGoFuel_ge fuel' r (acc ++ [Char.ofNat 0x0A]) (by simp [List.length_cons]; omega)
        | 'r' :: r =>
          simpa using
            parseStringCharsGoFuel_ge fuel' r (acc ++ [Char.ofNat 0x0D]) (by simp [List.length_cons]; omega)
        | 't' :: r =>
          simpa using
            parseStringCharsGoFuel_ge fuel' r (acc ++ [Char.ofNat 0x09]) (by simp [List.length_cons]; omega)
        | 'u' :: r =>
          cases parseHex4 r with
          | none => rfl
          | some p =>
            simpa using
              parseStringCharsGoFuel_ge fuel' p.2 (acc ++ [Char.ofNat p.1]) (by simp [List.length_cons]; omega)
        | _ :: _ => rfl
      | c :: rest =>
        simp [parseStringCharsGoFuel]
        simpa using
          parseStringCharsGoFuel_ge fuel' rest (acc ++ [c]) (by simp [List.length_cons]; omega)

theorem parseStringCharsGoFuel_sufficient_eq (f1 f2 : Nat) (s acc : List Char)
    (h1 : parseStringCharsFuelBound s ≤ f1) (h2 : parseStringCharsFuelBound s ≤ f2) :
    parseStringCharsGoFuel f1 s acc = parseStringCharsGoFuel f2 s acc := by
  rw [parseStringCharsGoFuel_ge f1 s acc h1, parseStringCharsGoFuel_ge f2 s acc h2]

private theorem parseStringChars_escapeCharList_quote (acc rest : List Char) :
    parseStringChars (escapeCharList '"' ++ rest) acc =
      parseStringChars rest (acc ++ ['"']) := by
  dsimp [parseStringChars, parseStringCharsGo, parseStringCharsFuelBound, escapeCharList, escapeChar]
  have ht : ("\\\"").toList = ['\\', '"'] := rfl
  rw [ht, List.cons_append, List.nil_append]
  simp only [parseStringCharsGoFuel, List.length_cons, List.length_nil]
  have hsuff1 : parseStringCharsFuelBound rest ≤ (2 + rest.length) * 6 := by simp; omega
  have hsuff2 : parseStringCharsFuelBound rest ≤ rest.length * 6 + 1 := Nat.le_refl _
  have hstep :=
    parseStringCharsGoFuel_sufficient_eq ((2 + rest.length) * 6) (rest.length * 6 + 1) rest
      (acc ++ ['"']) hsuff1 hsuff2
  rw [hstep]
  dsimp [parseStringChars, parseStringCharsGo, parseStringCharsFuelBound]
