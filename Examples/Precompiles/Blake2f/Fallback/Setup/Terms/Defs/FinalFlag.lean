import Examples.Precompiles.Blake2f.Fallback.Setup.Terms.Defs.Return

/-!
# BLAKE2F fallback bytecode memory terms: final-flag parser
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

abbrev finalFlagLoadWord (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian ((t1StoredMem I).readWithPadding 372 32))

abbrev parsedFinalFlagWord (I : ExecutionEnv) : UInt256 :=
  UInt256.shiftRight (finalFlagLoadWord I) ⟨248⟩

abbrev parsedFinalFlagBranchCond (I : ExecutionEnv) : UInt256 :=
  UInt256.gt (parsedFinalFlagWord I) ⟨1⟩

end Blake2f
