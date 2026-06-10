import OmegaJCS.Types

open OmegaJCS

example (xs : List OmegaJson) : OmegaJson.wfBool (OmegaJson.arr xs) = xs.all OmegaJson.wfBool := by
  rw [show OmegaJson.wfBool (OmegaJson.arr xs) = xs.all OmegaJson.wfBool from by cases xs <;> rfl]

example (xs : List OmegaJson) : OmegaJson.wfBool (OmegaJson.arr xs) = xs.all OmegaJson.wfBool := by
  conv_lhs => unfold OmegaJson.wfBool
  rfl

example (xs : List OmegaJson) : OmegaJson.wfBool (OmegaJson.arr xs) = xs.all OmegaJson.wfBool := by
  simp only [OmegaJson.wfBool]

example (kvs : List (String × OmegaJson)) :
    OmegaJson.wfBool (OmegaJson.obj kvs) =
      (kvs.all fun kv => kv.2.wfBool) && keysStrictSortedBool (kvs.map Prod.fst) := by
  conv_lhs => unfold OmegaJson.wfBool
  rfl
