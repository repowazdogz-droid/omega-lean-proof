import OmegaJCS.Types

namespace OmegaJCS

example : OmegaJson.wfBool (.arr []) = true := by native_decide
example : OmegaJson.wfBool (.arr []) = [].all OmegaJson.wfBool := by native_decide

example (h : OmegaJson) (t : List OmegaJson) :
    OmegaJson.wfBool (.arr (h :: t)) = (h.wfBool && t.all OmegaJson.wfBool) := by native_decide

theorem wfBool_arr (xs : List OmegaJson) :
    OmegaJson.wfBool (.arr xs) = xs.all OmegaJson.wfBool := by
  induction xs with
  | nil => native_decide
  | cons h t ih =>
    have hcons : OmegaJson.wfBool (.arr (h :: t)) = (h.wfBool && t.all OmegaJson.wfBool) := by native_decide
    rw [hcons, ih, List.all_cons]
    rfl

theorem arr_wf_all (xs : List OmegaJson) (h : (OmegaJson.arr xs).WF) :
    ∀ x ∈ xs, x.WF := by
  intro x hx
  dsimp [OmegaJson.WF] at h ⊢
  rw [wfBool_arr] at h
  exact (List.all_eq_true.mp h x hx)

end OmegaJCS
