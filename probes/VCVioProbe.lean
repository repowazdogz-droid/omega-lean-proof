-- VCVio compatibility probe (not in default Lake roots).
-- Run: `cd lean-proof && lake build VCVio && lake env lean probes/VCVioProbe.lean`
import VCVio
import VCVio.CryptoFoundations.Asymptotics.Negligible

#check negligible
