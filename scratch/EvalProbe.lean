import OmegaJCS.Encode
open OmegaJCS
#eval jcsEncodeChars (OmegaJson.arr [OmegaJson.null])
#eval encArrBody [OmegaJson.null]
#eval encArrSuffix [OmegaJson.null]
#eval jcsEncodeChars (OmegaJson.arr [OmegaJson.null, OmegaJson.bool true])
#eval encArrBody [OmegaJson.null, OmegaJson.bool true]
#eval encArrSuffix [OmegaJson.null, OmegaJson.bool true]
