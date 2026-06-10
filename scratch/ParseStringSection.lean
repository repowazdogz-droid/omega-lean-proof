section ParseString

private theorem parseStringCharsGoFuel_pos (f : Nat) (s acc : List Char) (hf : 0 < f) :
    parseStringCharsGoFuel f s acc = parseStringCharsGo s acc := by
  cases f with | zero => omega | succ _ => rfl

theorem parseStringCharsGoFuel_mono_ge (fuel extra : Nat) (s acc : List Char)
    (hle : extra ≤ fuel) (hpos : 0 < extra) :
    parseStringCharsGoFuel fuel s acc = parseStringCharsGoFuel extra s acc := by
  have hf : 0 < fuel := Nat.lt_of_le_of_lt hpos hle
  rw [parseStringCharsGoFuel_pos fuel s acc hf, parseStringCharsGoFuel_pos extra s acc hpos]

private theorem parseStringChars_escapeCharList_quote (acc rest : List Char) :
    parseStringChars (escapeCharList '"' ++ rest) acc =
      parseStringChars rest (acc ++ ['"']) := by
  simp only [escapeCharList, escapeChar, parseStringChars, beq_iff_eq, if_true,
    String.toList, List.cons_append, List.nil_append, parseStringCharsGo]

private theorem parseStringChars_escapeCharList_backslash (acc rest : List Char) :
    parseStringChars (escapeCharList '\\' ++ rest) acc =
      parseStringChars rest (acc ++ ['\\']) := by
  simp only [escapeCharList, escapeChar, parseStringChars, beq_iff_eq, if_false, if_true,
    String.toList, List.cons_append, List.nil_append, parseStringCharsGo]

private theorem parseStringChars_escapeCharList_ctrl (acc rest : List Char) (tag : Char)
    (h : tag = 'b' ∨ tag = 'f' ∨ tag = 'n' ∨ tag = 'r' ∨ tag = 't') :
    parseStringChars (['\\', tag] ++ rest) acc =
      parseStringChars rest (acc ++ [match tag with
        | 'b' => Char.ofNat 0x08 | 'f' => Char.ofNat 0x0C | 'n' => Char.ofNat 0x0A
        | 'r' => Char.ofNat 0x0D | 't' => Char.ofNat 0x09 | _ => tag]) := by
  rcases h with rfl | rfl | rfl | rfl | rfl <;>
    simp [parseStringChars, parseStringCharsGo, List.cons_append, List.nil_append]

private theorem parseStringChars_escapeCharList_unicode (c : Char) (acc rest : List Char)
    (h1 : c ≠ '"') (h2 : c ≠ '\\') (h3 : c.toNat ≠ 0x08) (h4 : c.toNat ≠ 0x0C)
    (h5 : c.toNat ≠ 0x0A) (h6 : c.toNat ≠ 0x0D) (h7 : c.toNat ≠ 0x09) (hlt : c.toNat < 0x20) :
    parseStringChars (escapeCharList c ++ rest) acc =
      parseStringChars rest (acc ++ [c]) := by
  simp only [escapeCharList, escapeChar, parseStringChars, beq_iff_eq, h1, h2, h3, h4, h5, h6, h7,
    if_false, hlt, if_pos, String.append, String.toList, List.cons_append, List.nil_append,
    hex4Lower, hex4Lower_toList, parseStringCharsGo]
  rw [hex4Lower_parseHex4 c.toNat (by omega) rest]

private theorem parseStringChars_escapeCharList_plain (c : Char) (acc rest : List Char)
    (h1 : c ≠ '"') (h2 : c ≠ '\\') (h3 : c.toNat ≠ 0x08) (h4 : c.toNat ≠ 0x0C)
    (h5 : c.toNat ≠ 0x0A) (h6 : c.toNat ≠ 0x0D) (h7 : c.toNat ≠ 0x09) (h8 : ¬ c.toNat < 0x20) :
    parseStringChars (escapeCharList c ++ rest) acc =
      parseStringChars rest (acc ++ [c]) := by
  simp only [escapeCharList, escapeChar, parseStringChars, beq_iff_eq, h1, h2, h3, h4, h5, h6, h7,
    if_false, h8, if_neg, String.singleton, String.toList, List.cons_append, List.nil_append,
    parseStringCharsGo]

private theorem parseStringChars_escapeCharList (c : Char) (acc rest : List Char) :
    parseStringChars (escapeCharList c ++ rest) acc =
      parseStringChars rest (acc ++ [c]) := by
  match c with
  | '"' => exact parseStringChars_escapeCharList_quote acc rest
  | '\\' => exact parseStringChars_escapeCharList_backslash acc rest
  | c =>
    by_cases h8 : c = Char.ofNat 0x08
    · subst h8; exact parseStringChars_escapeCharList_ctrl acc rest 'b' (Or.inl rfl)
    by_cases h12 : c = Char.ofNat 0x0C
    · subst h12; exact parseStringChars_escapeCharList_ctrl acc rest 'f' (Or.inr (Or.inl rfl))
    by_cases h10 : c = Char.ofNat 0x0A
    · subst h10; exact parseStringChars_escapeCharList_ctrl acc rest 'n' (Or.inr (Or.inr (Or.inl rfl)))
    by_cases h13 : c = Char.ofNat 0x0D
    · subst h13
      exact parseStringChars_escapeCharList_ctrl acc rest 'r' (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    by_cases h9 : c = Char.ofNat 0x09
    · subst h9
      exact parseStringChars_escapeCharList_ctrl acc rest 't' (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
    by_cases hlt : c.toNat < 0x20
    · exact parseStringChars_escapeCharList_unicode c acc rest
        (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h) hlt
    · exact parseStringChars_escapeCharList_plain c acc rest
        (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h) hlt

theorem parseStringChars_escapeStringChars (cs : List Char) (rest : List Char) :
    parseStringChars (escapeStringChars cs ++ rest) [] =
      parseStringChars rest (String.ofList cs).toList := by
  induction cs with
  | nil => simp [escapeStringChars]
  | cons c cs ih =>
    simp only [escapeStringChars, List.flatMap_cons, List.append_assoc]
    rw [← List.append_assoc, parseStringChars_escapeCharList, ih]

theorem parseStringChars_escapeString (s : String) (rest : List Char) :
    parseStringChars (escapeStringChars s.toList ++ '"' :: rest) [] = some (s, rest) := by
  have h := parseStringChars_escapeStringChars s.toList ('"' :: rest)
  simp only [parseStringChars, parseStringCharsGo, String.toList_ofList] at h ⊢
  simpa using h

theorem parseString_jcsEscapeString (s : String) (rest : List Char) :
    parseString (jcsEscapeStringChars s ++ rest) = some (s, rest) := by
  unfold parseString jcsEscapeStringChars
  simpa [List.cons_append] using parseStringChars_escapeString s rest

end ParseString
