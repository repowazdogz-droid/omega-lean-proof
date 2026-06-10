import OmegaJCS.Encode

open OmegaJCS

theorem jsonFuel_ge_one (v : OmegaJson) : 1 ≤ jsonFuel v := by
  cases v <;> simp [jsonFuel, jsonFuelList, jsonFuelObj]

theorem jsonFuelList_cons (v : OmegaJson) (vs : List OmegaJson) :
    jsonFuelList (v :: vs) = jsonFuel v + jsonFuelList vs := rfl

theorem jsonFuelList_ge_one (v : OmegaJson) (vs : List OmegaJson) :
    1 ≤ jsonFuelList (v :: vs) := by
  rw [jsonFuelList_cons]
  omega [jsonFuel_ge_one v]

example (n : Nat) (v : OmegaJson) (vs : List OmegaJson)
    (h : jsonFuel v + jsonFuelList vs ≤ n + 1) :
    jsonFuel v ≤ n + 1 := by omega

example (n : Nat) (v : OmegaJson) (vs : List OmegaJson)
    (h : jsonFuel v + jsonFuelList vs ≤ n) :
    jsonFuelList vs ≤ n := by omega

mutual
theorem jcsEncodeFuel_ge (fuel : Nat) (v : OmegaJson) (h : jsonFuel v ≤ fuel) :
    jcsEncodeFuel (jsonFuel v) v = jcsEncodeFuel fuel v := by
  rcases Nat.eq_or_lt_of_le h with heq | hlt
  · subst heq; rfl
  · match fuel with
    | 0 => cases v <;> simp [jsonFuel] at hlt
    | fuel' + 1 =>
      cases v with
      | null | bool _ | int _ | str _ => simp [jsonFuel, jcsEncodeFuel]
      | arr xs =>
        simp only [jsonFuel, jcsEncodeFuel]
        rw [← encArrBodyFuel_ge fuel' xs (by
          have : jsonFuelList xs ≤ jsonFuel (OmegaJson.arr xs) - 1 := by simp [jsonFuel, jsonFuelList]
          omega)]
      | obj kvs =>
        simp only [jsonFuel, jcsEncodeFuel]
        rw [← encObjBodyFuel_ge fuel' kvs (by simp [jsonFuel, jsonFuelObj]; omega)]

theorem encArrBodyFuel_ge (f : Nat) (xs : List OmegaJson) (h : jsonFuelList xs ≤ f) :
    encArrBodyFuel (jsonFuelList xs) xs = encArrBodyFuel f xs := by
  revert xs
  induction f with
  | zero =>
    intro xs h
    cases xs with
    | nil => rfl
    | cons v vs =>
      simp only [jsonFuelList] at h
      have : False := by omega [jsonFuel_ge_one v]
      exact this.elim
  | succ n ih =>
    intro xs h
    cases xs with
    | nil => rfl
    | cons v vs =>
      simp only [encArrBodyFuel, jsonFuelList]
      have hsum : jsonFuel v + jsonFuelList vs ≤ n + 1 := h
      have hsuff : jsonFuelList vs ≤ n + 1 := by omega
      have hbody := ih vs hsuff
      rcases Nat.le_or_gt n (jsonFuel v + jsonFuelList vs) with hle | hgt
      · have hcall := ih (v :: vs) hle
        sorry
      · have heq : jsonFuel v + jsonFuelList vs = n + 1 := by omega
        sorry

theorem encObjBodyFuel_ge (f : Nat) (kvs : List (String × OmegaJson)) (h : jsonFuelObj kvs ≤ f) :
    encObjBodyFuel (jsonFuelObj kvs) kvs = encObjBodyFuel f kvs := by
  sorry
end

example (xs : List OmegaJson) :
    jcsEncodeChars (OmegaJson.arr xs) = '[' :: encArrBody xs := by
  unfold jcsEncodeChars encArrBody jsonFuel jsonFuelList jcsEncodeFuel
  simp only [jcsEncodeFuel]
  rw [← encArrBodyFuel_ge (1 + jsonFuelList xs) xs (Nat.le_succ _)]
