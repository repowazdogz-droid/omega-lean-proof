import OmegaJCS.Encode

theorem foldl_append_start (pfx start : String) (ss : List String) :
    List.foldl (fun r s => r ++ s) (pfx ++ start) ss =
      pfx ++ List.foldl (fun r s => r ++ s) start ss := by
  induction ss generalizing start with
  | nil => simp [List.foldl_nil, String.append_assoc]
  | cons t ts ih =>
    simp only [List.foldl_cons]
    rw [String.append_assoc]
    exact ih (start ++ t)
