import Examples.Precompiles.Blake2f.Fallback.Setup.Compression.Entry.CompressionEntry

/-!
# BLAKE2F fallback compression entry: VInitLoopEntry
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

theorem validVInitLoopEntryPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlen : I.calldata.size = 213)
    (hflag : Model.validFinalFlag I.calldata) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1182⟩
      [⟨0⟩, ⟨1152⟩, UInt256.eq (parsedFinalFlagWord I) ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (compressionVAllocMem I) (UInt256.ofNat 46) ByteArray.empty (cA, σ) k 6692 := by
  obtain ⟨k0, rd1154⟩ := validCompressionEntryPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hflag
  have hmload64_t1 :
      (if (⟨64⟩ : UInt256).toNat ≥ (t1StoredMem I).size
          ∨ (⟨64⟩ : UInt256) ≥ (UInt256.ofNat 38) * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian ((t1StoredMem I).readWithPadding 64 32))) =
        (UInt256.ofNat 1216) := by
    exact mloadWordValue_of_readWithPadding
      (off := (⟨64⟩ : UInt256)) (aw := UInt256.ofNat 38) (v := UInt256.ofNat 1216)
      (by
        rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide, t1StoredMem_size I hlen]
        decide)
      (by native_decide)
      (by simpa [show (⟨64⟩ : UInt256).toNat = 64 from by decide] using
        t1StoredMem_read64 I hlen)
  have hmload64_scratch :
      (if (⟨64⟩ : UInt256).toNat ≥ (compressionScratchZeroMem I).size
          ∨ (⟨64⟩ : UInt256) ≥ (UInt256.ofNat 46) * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian ((compressionScratchZeroMem I).readWithPadding 64 32))) =
        (UInt256.ofNat 1472) := by
    exact mloadWordValue_of_readWithPadding
      (off := (⟨64⟩ : UInt256)) (aw := UInt256.ofNat 46) (v := UInt256.ofNat 1472)
      (by
        rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide,
          compressionScratchZeroMem_size I hlen]
        decide)
      (by native_decide)
      (by simpa [show (⟨64⟩ : UInt256).toNat = 64 from by decide] using
        compressionScratchZeroMem_read64 I hlen)
  have rd1182 := evm_run rd1154 with [
    raw jumpdest (by decide) (by evm_ov),
    swap1,
    swap2,
    swap5,
    swap4,
    swap5,
    push2 ⟨1167⟩,
    push2 ⟨837⟩,
    jump (by jump_dest),
    raw jumpdest (by decide) (by evm_ov),
    push2 ⟨256⟩,
    swap1,
    push2 ⟨850⟩,
    dup3,
    push2 ⟨706⟩,
    jump (by jump_dest),
    raw jumpdest (by decide) (by evm_ov),
    swap1,
    push32 ⟨115792089237316195423570985008687907853269984665640564039457584007913129639904⟩,
    push1 ⟨31⟩,
    push1 ⟨64⟩,
    raw mload 0 (UInt256.ofNat 1216) (UInt256.ofNat 38)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmload64_t1
      (by native_decide) (by evm_ov),
    swap4,
    add,
    and,
    dup3,
    add,
    dup3,
    dup2,
    lt,
    push8 ⟨18446744073709551615⟩,
    dup3,
    gt,
    or,
    push2 ⟨774⟩,
    jumpiNT (by native_decide),
    push1 ⟨64⟩,
    raw mstore 0 (compressionScratchAllocMem I) (UInt256.ofNat 38)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      (by
        unfold compressionScratchAllocMem
        rfl)
      (by native_decide) (by evm_ov),
    jump (by jump_dest),
    raw jumpdest (by decide) (by evm_ov),
    swap2,
    calldatasize,
    dup4,
    raw calldatacopy 26 (compressionScratchZeroMem I) (UInt256.ofNat 46)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      (by
        rw [hlen]
        unfold compressionScratchZeroMem
        rfl)
      (by native_decide) (by evm_ov),
    jump (by jump_dest),
    raw jumpdest (by decide) (by evm_ov),
    swap6,
    push1 ⟨64⟩,
    raw mload 0 (UInt256.ofNat 1472) (UInt256.ofNat 46)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmload64_scratch
      (by native_decide) (by evm_ov),
    swap5,
    push2 ⟨512⟩,
    dup7,
    add,
    push1 ⟨64⟩,
    raw mstore 0 (compressionVAllocMem I) (UInt256.ofNat 46)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      (by
        unfold compressionVAllocMem
        rfl)
      (by native_decide) (by evm_ov),
    push0 ]
  exact ⟨_, by simpa [GasConstants.Gverylow, GasConstants.Gcopy] using rd1182⟩

end Blake2f
