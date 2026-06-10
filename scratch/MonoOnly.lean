import OmegaJCS.Decode
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
      | [] =>
        rw [ih m [] acc hle]
        simp [parseStringCharsGoFuel, parseStringGoFuel_nil]
      | '"' :: rest => rfl
      | '\\' :: rest =>
        match rest with
        | [] => rfl
        | '"' :: r =>
          have h1 : parseStringCharsGoFuel (m + 1) ('\\' :: '"' :: r) acc =
              parseStringCharsGoFuel (m + 1) r (acc ++ ['"']) := by
            simp only [parseStringCharsGoFuel]
          have h2 : parseStringCharsGoFuel (n + 1) ('\\' :: '"' :: r) acc =
              parseStringCharsGoFuel (n + 1) r (acc ++ ['"']) := by
            simp only [parseStringCharsGoFuel]
          rw [h1, h2]
          exact ih m r (acc ++ ['"']) hle
        | '\\' :: r =>
          have h1 : parseStringCharsGoFuel (m + 1) ('\\' :: '\\' :: r) acc =
              parseStringCharsGoFuel (m + 1) r (acc ++ ['\\']) := by
            simp only [parseStringCharsGoFuel]
          have h2 : parseStringCharsGoFuel (n + 1) ('\\' :: '\\' :: r) acc =
              parseStringCharsGoFuel (n + 1) r (acc ++ ['\\']) := by
            simp only [parseStringCharsGoFuel]
          rw [h1, h2]
          exact ih m r (acc ++ ['\\']) hle
        | 'b' :: r =>
          have h1 : parseStringCharsGoFuel (m + 1) ('\\' :: 'b' :: r) acc =
              parseStringCharsGoFuel (m + 1) r (acc ++ [Char.ofNat 0x08]) := by
            simp only [parseStringCharsGoFuel]
          have h2 : parseStringCharsGoFuel (n + 1) ('\\' :: 'b' :: r) acc =
              parseStringCharsGoFuel (n + 1) r (acc ++ [Char.ofNat 0x08]) := by
            simp only [parseStringCharsGoFuel]
          rw [h1, h2]
          exact ih m r (acc ++ [Char.ofNat 0x08]) hle
        | 'f' :: r =>
          have h1 : parseStringCharsGoFuel (m + 1) ('\\' :: 'f' :: r) acc =
              parseStringCharsGoFuel (m + 1) r (acc ++ [Char.ofNat 0x0C]) := by
            simp only [parseStringCharsGoFuel]
          have h2 : parseStringCharsGoFuel (n + 1) ('\\' :: 'f' :: r) acc =
              parseStringCharsGoFuel (n + 1) r (acc ++ [Char.ofNat 0x0C]) := by
            simp only [parseStringCharsGoFuel]
          rw [h1, h2]
          exact ih m r (acc ++ [Char.ofNat 0x0C]) hle
        | 'n' :: r =>
          have h1 : parseStringCharsGoFuel (m + 1) ('\\' :: 'n' :: r) acc =
              parseStringCharsGoFuel (m + 1) r (acc ++ [Char.ofNat 0x0A]) := by
            simp only [parseStringCharsGoFuel]
          have h2 : parseStringCharsGoFuel (n + 1) ('\\' :: 'n' :: r) acc =
              parseStringCharsGoFuel (n + 1) r (acc ++ [Char.ofNat 0x0A]) := by
            simp only [parseStringCharsGoFuel]
          rw [h1, h2]
          exact ih m r (acc ++ [Char.ofNat 0x0A]) hle
        | 'r' :: r =>
          have h1 : parseStringCharsGoFuel (m + 1) ('\\' :: 'r' :: r) acc =
              parseStringCharsGoFuel (m + 1) r (acc ++ [Char.ofNat 0x0D]) := by
            simp only [parseStringCharsGoFuel]
          have h2 : parseStringCharsGoFuel (n + 1) ('\\' :: 'r' :: r) acc =
              parseStringCharsGoFuel (n + 1) r (acc ++ [Char.ofNat 0x0D]) := by
            simp only [parseStringCharsGoFuel]
          rw [h1, h2]
          exact ih m r (acc ++ [Char.ofNat 0x0D]) hle
        | 't' :: r =>
          have h1 : parseStringCharsGoFuel (m + 1) ('\\' :: 't' :: r) acc =
              parseStringCharsGoFuel (m + 1) r (acc ++ [Char.ofNat 0x09]) := by
            simp only [parseStringCharsGoFuel]
          have h2 : parseStringCharsGoFuel (n + 1) ('\\' :: 't' :: r) acc =
              parseStringCharsGoFuel (n + 1) r (acc ++ [Char.ofNat 0x09]) := by
            simp only [parseStringCharsGoFuel]
          rw [h1, h2]
          exact ih m r (acc ++ [Char.ofNat 0x09]) hle
        | 'u' :: r =>
          cases parseHex4 r with
          | none => simp [parseStringCharsGoFuel]
          | some p =>
            have h1 : parseStringCharsGoFuel (m + 1) ('\\' :: 'u' :: r) acc =
                parseStringCharsGoFuel (m + 1) p.2 (acc ++ [Char.ofNat p.1]) := by
              simp only [parseStringCharsGoFuel]
            have h2 : parseStringCharsGoFuel (n + 1) ('\\' :: 'u' :: r) acc =
                parseStringCharsGoFuel (n + 1) p.2 (acc ++ [Char.ofNat p.1]) := by
              simp only [parseStringCharsGoFuel]
            rw [h1, h2]
            exact ih m p.2 (acc ++ [Char.ofNat p.1]) hle
        | _ :: _ => simp [parseStringCharsGoFuel]
      | c :: rest =>
        have h1 : parseStringCharsGoFuel (m + 1) (c :: rest) acc =
            parseStringCharsGoFuel (m + 1) rest (acc ++ [c]) := by
          simp only [parseStringCharsGoFuel]
        have h2 : parseStringCharsGoFuel (n + 1) (c :: rest) acc =
            parseStringCharsGoFuel (n + 1) rest (acc ++ [c]) := by
          simp only [parseStringCharsGoFuel]
        rw [h1, h2]
        exact ih m rest (acc ++ [c]) hle
