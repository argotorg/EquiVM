import Examples.Precompiles.Blake2f.Fallback.OutputBridge.ReturnSlice

/-!
# BLAKE2F zero-round output-word bridge: common facts

Shared facts for the word-specific zero-round output bridge modules.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

theorem readWord_of_toByteArray_extract0_32 (w : UInt256) :
    UInt256.ofNat (fromByteArrayBigEndian ((UInt256.toByteArray w).extract 0 32)) = w := by
  rw [fromByteArrayBigEndian_toByteArray_extract0_32, u256_ofNat_toNat]

end Blake2f
