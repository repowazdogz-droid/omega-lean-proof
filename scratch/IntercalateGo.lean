theorem intercalate_go_nil (acc sep : String) :
    String.intercalate.go acc sep [] = acc := by
  unfold String.intercalate.go
  rfl

theorem intercalate_go_cons (acc sep u : String) (us : List String) :
    String.intercalate.go acc sep (u :: us) =
      String.intercalate.go (acc ++ sep ++ u) sep us := by
  unfold String.intercalate.go
  rfl

theorem String_intercalate_cons_cons (s t : String) (ss : List String) :
    String.intercalate "," (s :: t :: ss) = s ++ "," ++ String.intercalate "," (t :: ss) := by
  unfold String.intercalate
  rw [intercalate_go_cons]
  exact intercalate_go_shift s t "," ss

theorem intercalate_go_shift (s t sep : String) (ss : List String) :
    String.intercalate.go (s ++ sep ++ t) sep ss = s ++ sep ++ String.intercalate.go t sep ss := by
  induction ss with
  | nil => simp [intercalate_go_nil, String.append_assoc]
  | cons u us ih =>
    rw [intercalate_go_cons, intercalate_go_cons, ih, String.append_assoc]
