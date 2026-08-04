import Examples.Ripemd160Old.Fallback

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 50000000
set_option maxHeartbeats 0

namespace Ripemd160Old

open Ripemd160

def oldHashBitLength (I : ExecutionEnv) : UInt256 :=
  calldataSizeWord I * ⟨8⟩

/-- The old hash entry allocates its padded buffer and reaches the source-copy loop. -/
theorem runtime_reachHashCopyLoop {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hsize : I.calldata.size < UInt256.size)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize) :
    ∃ k C, RD runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨8350⟩
      [⟨160⟩, ⟨0⟩, calldataSizeWord I, oldHashBitLength I,
        hashPadPtr I, hashPaddedLengthWord I, ⟨254⟩]
      (hashAllocatedMem I) (fallbackPaddedAw I)
      ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd8306⟩ := runtime_reachHash
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g)
    hcode hwv hsize hsmall
  have rd8316 := evm_run_rfl rd8306 with [
    jumpdest, push2 ⟨8314⟩, push2 ⟨264⟩, jump jump_264,
    jumpdest, push0, swap1, jump jump_8314, jumpdest, pop ]
  have rd8319 := evm_run_rfl rd8316 with [push1 ⟨32⟩, dup2]
  have rd8320 := RD.mload 0 (calldataSizeWord I) (fallbackPaddedAw I)
    rd8319 (by old_decode)
    (fallbackPaddedMload128Cost I hsmall)
    (fallbackPaddedMload128Value I hsmall)
    (fallbackPaddedAw_mload128 I hsmall) (by simp)
  have rd8340 := evm_run_rfl rd8320 with [
    swap2, add, push1 ⟨8⟩, dup3, mul,
    push1 ⟨63⟩, not, push1 ⟨63⟩, push1 ⟨9⟩,
    dup6, add, add, and, swap3, push1 ⟨64⟩ ]
  have hpadded :
      UInt256.land (calldataSizeWord I + ⟨9⟩ + ⟨63⟩) (UInt256.lnot ⟨63⟩) =
        hashPaddedLengthWord I := by
    rw [u256_add_assoc,
      show (⟨9⟩ : UInt256) + ⟨63⟩ = ⟨72⟩ from by native_decide]
    rfl
  have rd8341 := RD.mload 0 (hashPadPtr I) (fallbackPaddedAw I)
    rd8340 (by old_decode)
    (fallbackPaddedMload64Cost I hsmall)
    (fallbackPaddedMload64Value I hsmall)
    (fallbackPaddedAw_mload64 I hsmall) (by simp)
  have rd8347 := evm_run_rfl rd8341 with [
    swap3, dup5, dup5, add, push1 ⟨64⟩ ]
  rw [hpadded] at rd8347
  have rd8348 := RD.mstore 0 (hashAllocatedMem I) (fallbackPaddedAw I)
    rd8347 (by old_decode)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', hstk]
      rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide,
        haw, fallbackPaddedAw_mload64 I hsmall]
      omega)
    (by
      simp [hashAllocatedMem, hashNewFreePtr]
      rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide])
    (fallbackPaddedAw_mload64 I hsmall) (by simp)
  have rd8350 := evm_run_rfl rd8348 with [push0, swap1]
  exact ⟨_, _, by
    simpa [oldHashBitLength] using rd8350⟩

end Ripemd160Old
