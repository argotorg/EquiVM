import Examples.Precompiles.Ripemd160.Common
import Examples.Ripemd160.Spec

/-!
# RIPEMD-160 Solm equivalence setup

Solm-only state used to relate the fallback parameter to the EVM execution environment.
The bytecode memory layout and pure return model live in
`Examples.Precompiles.Ripemd160.Common`.
-/

open Solm Ethereum Ethereum.EVM

namespace Ripemd160

abbrev fallbackLocals (I : ExecutionEnv) : Store :=
  (∅ : Store).insert "data" (.bytes I.calldata)

end Ripemd160
