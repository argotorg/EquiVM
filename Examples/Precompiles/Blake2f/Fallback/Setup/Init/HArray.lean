import Examples.Precompiles.Blake2f.Fallback.Setup.Init.Validation

/-!
# BLAKE2F fallback `h` parser-array allocation prefix
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

theorem validHArrayPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlen : I.calldata.size = 213)
    (hflag : Model.validFinalFlag I.calldata) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨83⟩ [⟨384⟩, ⟨128⟩, ⟨160⟩] (hArrayZeroMem I)
      (UInt256.ofNat 20) ByteArray.empty (cA, σ) k 554 := by
  obtain ⟨k0, rd76⟩ := validBytesInputPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hflag
  have hsrc : (⟨0⟩ : UInt256).toNat + (UInt256.ofNat 213).toNat ≤ I.calldata.size := by
    rw [hlen]
    decide
  have hread64 :
      (solcBytesSetPaddedMem I.calldata (UInt256.ofNat 213) ⟨0⟩).readWithPadding 64 32 =
        UInt256.toByteArray (solcBytesReturnFreePtr (UInt256.ofNat 213)) :=
    solcBytesSetPaddedMem_read64 I.calldata (UInt256.ofNat 213) ⟨0⟩
      (by decide) hsrc (by native_decide)
  have hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥
              (solcBytesSetPaddedMem I.calldata (UInt256.ofNat 213) ⟨0⟩).size
          ∨ (⟨64⟩ : UInt256) ≥ (UInt256.ofNat 13) * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian
            ((solcBytesSetPaddedMem I.calldata (UInt256.ofNat 213) ⟨0⟩).readWithPadding 64 32))) =
        UInt256.ofNat 384 := by
    have hfree : solcBytesReturnFreePtr (UInt256.ofNat 213) = UInt256.ofNat 384 := by
      native_decide
    exact mloadWordValue_of_readWithPadding
      (off := (⟨64⟩ : UInt256)) (aw := UInt256.ofNat 13) (v := UInt256.ofNat 384)
      (by
        rw [show (⟨64⟩ : UInt256).toNat = 64 by decide,
          solcBytesSetPaddedMem_size I.calldata (UInt256.ofNat 213) ⟨0⟩
            (by decide) hsrc (by native_decide)]
        decide)
      (by decide)
      (by simpa [hfree] using hread64)
  have rd83 := evm_run rd76 with [
    push2 ⟨83⟩,
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
    raw mload 0 (UInt256.ofNat 384) (UInt256.ofNat 13)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmload64
      (by decide) (by evm_ov),
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
    raw mstore 0 (hArrayAllocMem I) (UInt256.ofNat 13)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      (by
        unfold hArrayAllocMem
        rfl)
      (by decide) (by evm_ov),
    jump (by jump_dest),
    raw jumpdest (by decide) (by evm_ov),
    swap2,
    calldatasize,
    dup4,
    raw calldatacopy 21 (hArrayZeroMem I) (UInt256.ofNat 20)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      (by
        rw [hlen]
        unfold hArrayZeroMem
        rfl)
      (by native_decide) (by evm_ov),
    jump (by jump_dest) ]
  exact ⟨_, by simpa [hlen, GasConstants.Gverylow, GasConstants.Gcopy] using rd83⟩

end Blake2f
