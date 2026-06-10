import OmegaJCS.Types
import OmegaJCS.Encode

namespace OmegaJCS

def jcsEncodeWf (v : OmegaJson) : String :=
  match v with
  | .null => "null"
  | .bool true => "true"
  | .bool false => "false"
  | .int n => intToString n
  | .str s => jcsEscapeString s
  | .arr xs => "[" ++ String.intercalate "," (xs.map jcsEncodeWf) ++ "]"
  | .obj kvs => "{" ++ String.intercalate "," (kvs.map fun ⟨k, v⟩ =>
      jcsEscapeString k ++ ":" ++ jcsEncodeWf v) ++ "}"
termination_by nodeCount v
decreasing_by
  all_goals simp only [nodeCount, nodeCountList, nodeCountObj]
  first | apply nodeCount_lt_arr_cons | apply nodeCount_lt_obj_cons | omega

theorem test : jcsEncodeWf OmegaJson.null = "null" := rfl
