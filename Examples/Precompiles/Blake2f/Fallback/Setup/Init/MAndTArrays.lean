import Examples.Precompiles.Blake2f.Fallback.Setup.Init.HArray

/-!
# BLAKE2F fallback `m` and `t` parser-array allocation prefixes
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

theorem validMArrayPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlen : I.calldata.size = 213)
    (hflag : Model.validFinalFlag I.calldata) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨92⟩ [⟨640⟩, ⟨160⟩, ⟨128⟩, ⟨384⟩] (mArrayZeroMem I)
      (UInt256.ofNat 36) ByteArray.empty (cA, σ) k 793 := by
  obtain ⟨k0, rd83⟩ := validHArrayPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hflag
  have hread64 :
      (hArrayZeroMem I).readWithPadding 64 32 = UInt256.toByteArray (UInt256.ofNat 640) :=
    hArrayZeroMem_read64 I hlen
  have hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ (hArrayZeroMem I).size
          ∨ (⟨64⟩ : UInt256) ≥ (UInt256.ofNat 20) * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian ((hArrayZeroMem I).readWithPadding 64 32))) =
        UInt256.ofNat 640 := by
    exact mloadWordValue_of_readWithPadding
      (off := (⟨64⟩ : UInt256)) (aw := UInt256.ofNat 20) (v := UInt256.ofNat 640)
      (by rw [hArrayZeroMem_size I hlen]; decide)
      (by decide)
      hread64
  have hallocWord :
      UInt256.ofNat 640 +
          ((⟨512⟩ : UInt256) + ⟨31⟩).land
            ⟨115792089237316195423570985008687907853269984665640564039457584007913129639904⟩ =
        UInt256.ofNat 1152 := by
    native_decide
  have rd92 := evm_run rd83 with [
    raw jumpdest (by decide) (by evm_ov),
    swap2,
    push2 ⟨92⟩,
    push2 ⟨856⟩,
    jump (by jump_dest),
    raw jumpdest (by decide) (by evm_ov),
    push2 ⟨512⟩,
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
    raw mload 0 (UInt256.ofNat 640) (UInt256.ofNat 20)
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
    raw mstore 0 (mArrayAllocMem I) (UInt256.ofNat 20)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      (by
        rw [hallocWord]
        unfold mArrayAllocMem
        rfl)
      (by decide) (by evm_ov),
    jump (by jump_dest),
    raw jumpdest (by decide) (by evm_ov),
    swap2,
    calldatasize,
    dup4,
    raw calldatacopy 50 (mArrayZeroMem I) (UInt256.ofNat 36)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      (by
        rw [hlen]
        unfold mArrayZeroMem
        rfl)
      (by native_decide) (by evm_ov),
    jump (by jump_dest) ]
  exact ⟨_, by simpa [hlen, GasConstants.Gverylow, GasConstants.Gcopy] using rd92⟩

/-- The valid path allocates and zero-initializes the `uint64[2]` memory array used for parsed
BLAKE2F offset counters.

Source note: this is the helper entered at PC `92` (`0x0365`). It returns to PC `100`, leaving the
new `t` array pointer `0x480` above the `m`, bytes, and `h` pointers.  The free pointer is advanced
to `0x4c0` (`1216`), while the concrete bytearray still does not extend because the zeroing copy
reads from `calldatasize()`. -/
theorem validTArrayPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlen : I.calldata.size = 213)
    (hflag : Model.validFinalFlag I.calldata) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨100⟩ [⟨1152⟩, ⟨640⟩, ⟨160⟩, ⟨128⟩, ⟨384⟩] (tArrayZeroMem I)
      (UInt256.ofNat 38) ByteArray.empty (cA, σ) k 940 := by
  obtain ⟨k0, rd92⟩ := validMArrayPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hflag
  have hread64 :
      (mArrayZeroMem I).readWithPadding 64 32 = UInt256.toByteArray (UInt256.ofNat 1152) :=
    mArrayZeroMem_read64 I hlen
  have hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ (mArrayZeroMem I).size
          ∨ (⟨64⟩ : UInt256) ≥ (UInt256.ofNat 36) * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian ((mArrayZeroMem I).readWithPadding 64 32))) =
        UInt256.ofNat 1152 := by
    exact mloadWordValue_of_readWithPadding
      (off := (⟨64⟩ : UInt256)) (aw := UInt256.ofNat 36) (v := UInt256.ofNat 1152)
      (by rw [mArrayZeroMem_size I hlen]; decide)
      (by decide)
      hread64
  have hallocWord :
      UInt256.ofNat 1152 +
          ((⟨64⟩ : UInt256) + ⟨31⟩).land
            ⟨115792089237316195423570985008687907853269984665640564039457584007913129639904⟩ =
        UInt256.ofNat 1216 := by
    native_decide
  have rd100 := evm_run rd92 with [
    raw jumpdest (by decide) (by evm_ov),
    push2 ⟨100⟩,
    push2 ⟨869⟩,
    jump (by jump_dest),
    raw jumpdest (by decide) (by evm_ov),
    push2 ⟨879⟩,
    push1 ⟨64⟩,
    push2 ⟨706⟩,
    jump (by jump_dest),
    raw jumpdest (by decide) (by evm_ov),
    swap1,
    push32 ⟨115792089237316195423570985008687907853269984665640564039457584007913129639904⟩,
    push1 ⟨31⟩,
    push1 ⟨64⟩,
    raw mload 0 (UInt256.ofNat 1152) (UInt256.ofNat 36)
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
    raw mstore 0 (tArrayAllocMem I) (UInt256.ofNat 36)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      (by
        rw [hallocWord]
        unfold tArrayAllocMem
        rfl)
      (by decide) (by evm_ov),
    jump (by jump_dest),
    raw jumpdest (by decide) (by evm_ov),
    swap1,
    push1 ⟨64⟩,
    calldatasize,
    dup4,
    raw calldatacopy 6 (tArrayZeroMem I) (UInt256.ofNat 38)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      (by
        rw [hlen]
        unfold tArrayZeroMem
        rfl)
      (by native_decide) (by evm_ov),
    jump (by jump_dest) ]
  exact ⟨_, by simpa [hlen, GasConstants.Gverylow, GasConstants.Gcopy] using rd100⟩

end Blake2f
