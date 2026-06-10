import OmegaJCS.Encode
open OmegaJCS

example (v : OmegaJson) :
    (String.intercalate "," [jcsEncode v]).toList = (jcsEncode v).toList := by
  unfold String.intercalate
  rfl

example (v w : OmegaJson) :
    (String.intercalate "," [jcsEncode v, jcsEncode w]).toList =
      (jcsEncode v).toList ++ ',' :: (jcsEncode w).toList := by
  unfold String.intercalate
  rfl

example (v w : OmegaJson) (ws : List OmegaJson) :
    (String.intercalate "," (jcsEncode v :: jcsEncode w :: ws.map jcsEncode)).toList =
      (jcsEncode v).toList ++ ',' :: (String.intercalate "," (jcsEncode w :: ws.map jcsEncode)).toList := by
  unfold String.intercalate
  rfl
