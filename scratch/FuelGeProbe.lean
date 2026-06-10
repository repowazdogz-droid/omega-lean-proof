import OmegaJCS.Encode

open OmegaJCS

theorem jsonFuel_ge_one (v : OmegaJson) : 1 ≤ jsonFuel v := by
  cases v <;> simp [jsonFuel, jsonFuelList, jsonFuelObj]

mutual
theorem jcsEncodeFuel_ge (fuel : Nat) (v : OmegaJson) (h : jsonFuel v ≤ fuel) :
    jcsEncodeFuel (jsonFuel v) v = jcsEncodeFuel fuel v := by
  rcases Nat.eq_or_lt_of_le h with rfl | hlt
  · rfl
  · match fuel with
    | 0 => cases v <;> simp [jsonFuel] at hlt
    | fuel' + 1 =>
      cases v with
      | null | bool _ | int _ | str _ => simp [jsonFuel, jcsEncodeFuel]
      | arr xs =>
        simp only [jsonFuel, jcsEncodeFuel_succ_arr]
        congr 1
        exact encArrBodyFuel_ge fuel' xs (by omega)
      | obj kvs =>
        simp only [jsonFuel, jcsEncodeFuel_succ_obj]
        congr 1
        exact encObjBodyFuel_ge fuel' kvs (by omega)

theorem encArrBodyFuel_ge (f : Nat) (xs : List OmegaJson) (h : jsonFuelList xs ≤ f) :
    encArrBodyFuel (jsonFuelList xs) xs = encArrBodyFuel f xs := by
  revert xs
  induction f with
  | zero =>
    intro xs h
    cases xs with
    | nil => rfl
    | cons v vs =>
      simp [jsonFuelList] at h
      exact absurd h (by omega [jsonFuel_ge_one v])
  | succ n ih =>
    intro xs h
    cases xs with
    | nil => rfl
    | cons v vs =>
      simp only [encArrBodyFuel, jsonFuelList]
      rcases Nat.eq_or_lt_of_le h with heq | hlt
      · subst heq; rfl
      · have hle : jsonFuel v + jsonFuelList vs ≤ n := Nat.lt_succ_iff.mp hlt
        have hvs : jsonFuelList vs ≤ n := by omega
        rw [← ih vs hvs]
        congr 1
        · exact jcsEncodeFuel_ge n v (by omega)
        · exact encArrSuffixFuel_ge n vs hvs

theorem encArrSuffixFuel_ge (f : Nat) (xs : List OmegaJson) (h : jsonFuelList xs ≤ f) :
    encArrSuffixFuel (jsonFuelList xs) xs = encArrSuffixFuel f xs := by
  revert xs
  induction f with
  | zero =>
    intro xs h
    cases xs with
    | nil => rfl
    | cons v vs =>
      simp [jsonFuelList] at h
      exact absurd h (by omega [jsonFuel_ge_one v])
  | succ n ih =>
    intro xs h
    cases xs with
    | nil => rfl
    | cons v vs =>
      cases vs with
      | nil => rfl
      | cons w ws =>
        simp only [encArrSuffixFuel, jsonFuelList]
        rcases Nat.eq_or_lt_of_le h with heq | hlt
        · subst heq; rfl
        · have hle : jsonFuel v + jsonFuelList (w :: ws) ≤ n := Nat.lt_succ_iff.mp hlt
          have hws : jsonFuelList (w :: ws) ≤ n := by omega
          rw [← ih (w :: ws) hws]
          congr 1
          · exact jcsEncodeFuel_ge n w (by omega)
          · exact encArrSuffixFuel_ge n (w :: ws) hws

theorem encObjBodyFuel_ge (f : Nat) (kvs : List (String × OmegaJson)) (h : jsonFuelObj kvs ≤ f) :
    encObjBodyFuel (jsonFuelObj kvs) kvs = encObjBodyFuel f kvs := by
  revert kvs
  induction f with
  | zero =>
    intro kvs h
    cases kvs with
    | nil => rfl
    | cons kv kvs' =>
      simp [jsonFuelObj] at h
      exact absurd h (by omega [jsonFuel_ge_one kv.2])
  | succ n ih =>
    intro kvs h
    cases kvs with
    | nil => rfl
    | cons kv kvs' =>
      simp only [encObjBodyFuel, jsonFuelObj]
      rcases Nat.eq_or_lt_of_le h with heq | hlt
      · subst heq; rfl
      · have hle : jsonFuel kv.2 + jsonFuelObj kvs' ≤ n := Nat.lt_succ_iff.mp hlt
        have hvs : jsonFuelObj kvs' ≤ n := by omega
        rw [← ih kvs' hvs]
        congr 1
        · exact jcsEncodeFuel_ge n kv.2 (by omega)
        · exact encObjSuffixFuel_ge n (kv :: kvs') (by omega)

theorem encObjSuffixFuel_ge (f : Nat) (kvs : List (String × OmegaJson)) (h : jsonFuelObj kvs ≤ f) :
    encObjSuffixFuel (jsonFuelObj kvs) kvs = encObjSuffixFuel f kvs := by
  revert kvs
  induction f with
  | zero =>
    intro kvs h
    cases kvs with
    | nil => rfl
    | cons kv kvs' =>
      simp [jsonFuelObj] at h
      exact absurd h (by omega [jsonFuel_ge_one kv.2])
  | succ n ih =>
    intro kvs h
    cases kvs with
    | nil => rfl
    | cons kv kvs' =>
      cases kvs' with
      | nil => rfl
      | cons kv' kvs'' =>
        simp only [encObjSuffixFuel, jsonFuelObj]
        rcases Nat.eq_or_lt_of_le h with heq | hlt
        · subst heq; rfl
        · have hle : jsonFuel kv.2 + jsonFuelObj (kv' :: kvs'') ≤ n := Nat.lt_succ_iff.mp hlt
          have hvs : jsonFuelObj (kv' :: kvs'') ≤ n := by omega
          rw [← ih (kv' :: kvs'') hvs]
          congr 1
          · exact jcsEncodeFuel_ge n kv'.2 (by omega)
          · exact encObjSuffixFuel_ge n (kv' :: kvs'') hvs
end

theorem jcsEncodeChars_arr (xs : List OmegaJson) :
    jcsEncodeChars (OmegaJson.arr xs) = '[' :: encArrBody xs := by
  simp [jcsEncodeChars, encArrBody, jsonFuel, jsonFuelList, jcsEncodeFuel_succ_arr,
    encArrBodyFuel_ge (jsonFuelList xs) (jsonFuelList xs) (Nat.le_refl _)]

example (v : OmegaJson) :
    jcsEncodeChars (OmegaJson.arr [v]) = '[' :: jcsEncodeChars v ++ [']'] := by
  simp [jcsEncodeChars_arr, encArrBody, encArrBodyFuel, jsonFuel, jsonFuelList, jcsEncodeFuel]
