import Examples.Precompiles.Blake2f.Correct.Valid
import Examples.Precompiles.Blake2f.Correct.Invalid

/-!
# BLAKE2F bytecode spec

Final Solm-independent wrapper for the BLAKE2F bytecode experiment: valid inputs return the
trusted pure model output with exact bytecode gas, and invalid inputs fail at the caller-visible
`Θ` projection.
-/

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

theorem bytecodeSpec : bytecodeSpecTarget bytecodeGasCost :=
  bytecodeSpec_of_validTrace bytecodeGasCost validTrace

end Blake2f
