import OmegaJCS.Types

open OmegaJCS

example (xs : List OmegaJson) (h : (OmegaJson.arr xs).WF) (x : OmegaJson) (hx : x ∈ xs) : x.WF := by
  dsimp [OmegaJson.WF] at h
  delta OmegaJson.wfBool at h
  exact List.all_eq_true.mp h x hx

example (kvs : List (String × OmegaJson)) (h : (OmegaJson.obj kvs).WF) (kv : String × OmegaJson) (hkv : kv ∈ kvs) :
    kv.2.WF := by
  dsimp [OmegaJson.WF] at h
  delta OmegaJson.wfBool at h
  rcases Bool.and_eq_true.mp h with ⟨hall, _⟩
  exact List.all_eq_true.mp hall kv hkv

example (n : Nat) : jsonFuelList (List.replicate n OmegaJson.null) = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [jsonFuelList, ih, jsonFuel]

example (n : Nat) (h : jsonFuelList (List.replicate n OmegaJson.null) ≤ n) : n = 0 ∨ n > 0 := by
  omega
