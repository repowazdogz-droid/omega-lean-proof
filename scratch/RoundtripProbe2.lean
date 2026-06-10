import OmegaJCS.Encode
import OmegaJCS.Decode
import OmegaJCS.Types

open OmegaJCS

example (xs : List OmegaJson) :
    jcsEncodeChars (OmegaJson.arr xs) = '[' :: encArrBody xs := by
  unfold jcsEncodeChars encArrBody jsonFuel jsonFuelList jcsEncodeFuel encArrBodyFuel
  simp only [jcsEncodeFuel]

example (v : OmegaJson) (vs : List OmegaJson) :
    encArrBody (v :: vs) = jcsEncodeChars v ++ encArrSuffix (v :: vs) := by
  unfold encArrBody encArrSuffix jsonFuel jsonFuelList encArrBodyFuel encArrSuffixFuel jcsEncodeChars jcsEncodeFuel
  simp only [encArrBodyFuel, encArrSuffixFuel, jcsEncodeFuel]

example (xs : List OmegaJson) (h : (OmegaJson.arr xs).WF) (x : OmegaJson) (hx : x ∈ xs) : x.WF := by
  unfold OmegaJson.WF at h
  unfold OmegaJson.wfBool at h
  exact List.all_eq_true.mp h x hx

example (kvs : List (String × OmegaJson)) (h : (OmegaJson.obj kvs).WF) (kv : String × OmegaJson) (hkv : kv ∈ kvs) :
    kv.2.WF := by
  unfold OmegaJson.WF at h
  unfold OmegaJson.wfBool at h
  rcases Bool.and_eq_true.mp h with ⟨hall, _⟩
  exact List.all_eq_true.mp hall kv hkv

example (n : Nat) (rest : List Char) :
    parseNatDigits (natToDecimal n ++ rest) 0 = some (n, rest) := by
  cases n with
  | zero => simp [natToDecimal, parseNatDigits, isDigit]
  | succ n => sorry

example (m n : Nat) (s acc : List Char) (h : m ≤ n) :
    parseStringCharsGoFuel (m + 1) s acc = parseStringCharsGoFuel (n + 1) s acc := by
  induction n generalizing m s acc with
  | zero =>
    have hm : m = 0 := Nat.eq_zero_of_le_zero h
    subst hm
    rfl
  | succ k ih =>
    rcases Nat.eq_or_lt_of_le h with heq | hlt
    · subst heq; rfl
    · have hk : m ≤ k := Nat.le_of_lt_succ hlt
      match s with
      | [] => simp [parseStringCharsGoFuel]
      | '"' :: rest => simp [parseStringCharsGoFuel]
      | '\\' :: rest =>
        simp only [parseStringCharsGoFuel]
        match rest with
        | '"' :: r => exact ih m r (acc ++ ['"']) hk
        | '\\' :: r => exact ih m r (acc ++ ['\\']) hk
        | 'b' :: r => exact ih m r (acc ++ [Char.ofNat 8]) hk
        | 'f' :: r => exact ih m r (acc ++ [Char.ofNat 12]) hk
        | 'n' :: r => exact ih m r (acc ++ [Char.ofNat 10]) hk
        | 'r' :: r => exact ih m r (acc ++ [Char.ofNat 13]) hk
        | 't' :: r => exact ih m r (acc ++ [Char.ofNat 9]) hk
        | 'u' :: r =>
          cases parseHex4 r with
          | none => simp [parseStringCharsGoFuel]
          | some p => simp [parseStringCharsGoFuel]; exact ih m p.2 (acc ++ [Char.ofNat p.1]) hk
        | _ :: _ => simp [parseStringCharsGoFuel]
      | c :: rest => simp [parseStringCharsGoFuel]; exact ih m rest (acc ++ [c]) hk

example (acc rest : List Char) :
    parseStringCharsGoFuel 2 ("\\".toList ++ "\"".toList ++ rest) acc =
      parseStringCharsGoFuel 1 rest (acc ++ ['"']) := by
  simp only [parseStringCharsGoFuel, List.singleton_append, String.toList_singleton]

#check Bool.and_eq_true
