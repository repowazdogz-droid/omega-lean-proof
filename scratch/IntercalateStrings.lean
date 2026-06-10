private def intercalateStrings (sep : String) : List String → String
  | [] => ""
  | [s] => s
  | s :: t :: ss => s ++ sep ++ intercalateStrings sep (t :: ss)

theorem intercalateStrings_toList_pair (a b : String) :
    (intercalateStrings "," [a, b]).toList = a.toList ++ ',' :: b.toList := by
  simp [intercalateStrings]

theorem intercalateStrings_toList_step (a : String) (bs : List String) :
    (intercalateStrings "," (a :: bs)).toList =
      a.toList ++ (match bs with | [] => [] | b :: bs' => ',' :: (intercalateStrings "," (b :: bs')).toList) := by
  cases bs <;> simp [intercalateStrings, String.toList_append]
