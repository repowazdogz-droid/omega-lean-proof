import OmegaJCS.Encode

open OmegaJCS

example (xs : List OmegaJson) :
    jcsEncodeChars (OmegaJson.arr xs) = '[' :: encArrBody xs := by
  unfold jcsEncodeChars encArrBody jsonFuel jsonFuelList jcsEncodeFuel encArrBodyFuel
  have h : jsonFuelList xs ≤ 1 + jsonFuelList xs := Nat.le_succ _
  sorry

example (f : Nat) (xs : List OmegaJson) (h : jsonFuelList xs ≤ f) :
    encArrBodyFuel (jsonFuelList xs) xs = encArrBodyFuel f xs := by
  revert xs
  induction f with
  | zero =>
    intro xs h
    cases xs with
    | nil => rfl
    | cons v vs =>
      simp only [jsonFuelList] at h
      omega
  | succ n ih =>
    intro xs h
    cases xs with
    | nil => rfl
    | cons v vs =>
      simp only [encArrBodyFuel, jsonFuelList]
      have hv : jsonFuel v ≤ n := by simp only [jsonFuelList] at h; omega
      have hvs : jsonFuelList vs ≤ n := by simp only [jsonFuelList] at h; omega
      sorry

#check jsonFuelList
#eval jsonFuelList [OmegaJson.null, OmegaJson.null]

example (xs : List OmegaJson) (h : (OmegaJson.arr xs).WF) (x : OmegaJson) (hx : x ∈ xs) : x.WF := by
  cases xs
  case nil => simp at hx
  case cons x' xs' =>
    cases h
    sorry

example (kvs : List (String × OmegaJson)) (h : (OmegaJson.obj kvs).WF) :
    True := by
  cases kvs
  case nil => trivial
  case cons kv kvs' =>
    cases h
    trivial
