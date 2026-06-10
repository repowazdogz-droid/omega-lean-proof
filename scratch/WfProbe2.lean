import OmegaJCS.Types

open OmegaJCS

example (xs : List OmegaJson) : OmegaJson.wfBool (OmegaJson.arr xs) = xs.all OmegaJson.wfBool := by
  cases xs with
  | nil => native_decide
  | cons x xs => native_decide

example (xs : List OmegaJson) (h : (OmegaJson.arr xs).WF) (x : OmegaJson) (hx : x ∈ xs) : x.WF := by
  have hall : xs.all OmegaJson.wfBool = true := by
    dsimp [OmegaJson.WF] at h
    native_decide
  exact List.all_eq_true.mp hall x hx
