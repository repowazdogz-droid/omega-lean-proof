import OmegaJCS.Types

namespace OmegaJCS

#check OmegaJson.wfBool
#check OmegaJson.WF

example (xs : List OmegaJson) : OmegaJson.wfBool (.arr xs) = xs.all OmegaJson.wfBool := by
  simp [OmegaJson.wfBool]
  -- delta OmegaJson.wfBool
  -- dsimp [OmegaJson.wfBool]
  -- unfold OmegaJson.wfBool

example (kvs : List (String × OmegaJson)) :
    OmegaJson.wfBool (.obj kvs) =
      (kvs.all fun kv => kv.snd.wfBool) && keysStrictSortedBool (kvs.map Prod.fst) := by
  rfl

example (xs : List OmegaJson) (h : (OmegaJson.arr xs).WF) (x : OmegaJson) (hx : x ∈ xs) : x.WF := by
  dsimp [OmegaJson.WF] at h ⊢
  sorry

end OmegaJCS
