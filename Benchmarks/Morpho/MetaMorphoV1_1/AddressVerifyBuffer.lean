import Benchmarks.Morpho.MetaMorphoV1_1.AddressVerifySource
import Benchmarks.Morpho.MetaMorphoV1_1.CallReturnMemory

/-! Relate the Address code-size guard to the allocated return-buffer header. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

theorem addressReturnValid_memory {evm : State} {target : AccountAddress}
    {mem out : ByteArray} {ptr : UInt256} (hout : out.size < UInt256.size)
    (hzero : memLoad ⟨96⟩ mem = ⟨0⟩) :
    addressReturnValid evm target out ↔
      memLoad (callReturnPointer ptr out) (callReturnMemory mem ptr out) ≠ ⟨0⟩ ∨
        extCodeSizeWord evm.accountMap (UInt256.ofNat target.toNat) ≠ ⟨0⟩ := by
  rw [callReturnMemory_length mem ptr out hzero]
  have hz : UInt256.ofNat out.size = ⟨0⟩ ↔ out.size = 0 := by
    constructor
    · intro he
      have hn := congrArg UInt256.toNat he
      simpa only [UInt256.toNat_ofNat_of_lt hout] using hn
    · intro he
      rw [he]
      rfl
  simp only [addressReturnValid, ne_eq, hz]

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
