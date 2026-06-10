import OmegaJCS.Types

namespace OmegaJCS

theorem wfBool_arr (xs : List OmegaJson) :
    OmegaJson.wfBool (.arr xs) = xs.all OmegaJson.wfBool := by
  induction xs with
  | nil => simp [List.all_nil]
  | cons h t ih => simp [List.all_cons]

theorem wfBool_obj (kvs : List (String × OmegaJson)) :
    OmegaJson.wfBool (.obj kvs) =
      (kvs.all fun kv => kv.snd.wfBool) && keysStrictSortedBool (kvs.map Prod.fst) := by
  induction kvs with
  | nil => simp
  | cons kv kvs ih => simp [List.all_cons, List.map_cons, ih]

#check List.all_eq_true
#check Bool.and_eq_true

theorem arr_wf_all (xs : List OmegaJson) (h : (OmegaJson.arr xs).WF) :
    ∀ x ∈ xs, x.WF := by
  intro x hx
  dsimp [OmegaJson.WF] at h ⊢
  rw [wfBool_arr] at h
  exact ?goal

end OmegaJCS
