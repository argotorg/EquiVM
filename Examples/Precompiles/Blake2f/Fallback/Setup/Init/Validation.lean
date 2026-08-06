import Examples.Precompiles.Blake2f.Fallback.Setup.Terms

/-!
# BLAKE2F fallback validation and calldata materialization prefixes
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

theorem zeroValuePrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode) (hwv : I.weiValue = ⟨0⟩) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨10⟩ [] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k 33 := by
  have rd0 :
      RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨0⟩ [] ByteArray.empty (UInt256.ofNat 0) ByteArray.empty (cA, σ) 0 0 :=
    RDx.initState hcode
  have rd10 := evm_run rd0 with [
    push1 ⟨128⟩,
    push1 ⟨64⟩,
    raw mstore 9 solcFreePtrMem (UInt256.ofNat 3) (by decide)
      mem_cost
      (by rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide]; rfl)
      (by decide) (by evm_ov),
    callvalue,
    push2 ⟨657⟩,
    jumpiNT hwv ]
  exact ⟨_, rd10⟩

/-- Gas-erasing wrapper for older call sites that only need the reached cursor. -/
theorem zeroValuePrefix {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode) (hwv : I.weiValue = ⟨0⟩) :
    ∃ k C, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨10⟩ [] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨k, h⟩ := zeroValuePrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv
  exact ⟨k, 33, h⟩

/-- Exact valid-validation prefix through both explicit EIP-152 fallback guards.

Source note: after this cursor, execution has proved the bytecode-side length and final-flag
guards match the trusted model's valid-input shape.  The remaining valid-input proof starts at
PC `30`, where the Solidity wrapper begins materializing `msg.data` as `bytes memory`. -/
theorem validValidationPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlen : I.calldata.size = 213)
    (hflag : Model.validFinalFlag I.calldata) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨30⟩ [] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k 84 := by
  obtain ⟨k0, rd10⟩ := zeroValuePrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv
  have hlenOk : UInt256.sub (calldataSizeWord I) ⟨213⟩ = ⟨0⟩ :=
    lengthGuardSub_zero hlen
  have hflagOk : UInt256.gt (finalFlagWord I) ⟨1⟩ = ⟨0⟩ :=
    finalFlagGuard_of_valid I hlen hflag
  have rd30 := evm_run rd10 with [
    push1 ⟨213⟩,
    calldatasize,
    sub,
    push2 ⟨310⟩,
    jumpiNT hlenOk,
    push1 ⟨1⟩,
    push1 ⟨212⟩,
    calldataload,
    push0,
    byte,
    gt,
    push2 ⟨310⟩,
    jumpiNT hflagOk ]
  exact ⟨_, rd30⟩

/-- The valid path's dynamic-bytes allocation helper rounds length `213` to allocation size `256`,
updates the Solidity free pointer to `0x180`, and returns the old free pointer `0x80`.

Source note: this is the compiler-generated `bytes memory input = msg.data` allocation helper
entered from PC `30`.  It stops at PC `46`, immediately before the wrapper stores the byte length
and copies calldata into the allocated payload area. -/
theorem validAllocationHelperPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlen : I.calldata.size = 213)
    (hflag : Model.validFinalFlag I.calldata) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨46⟩ [⟨128⟩] (solcBytesReturnAllocMem (UInt256.ofNat 213))
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k 246 := by
  obtain ⟨k0, rd30⟩ := validValidationPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hflag
  have hcdsz : UInt256.ofNat I.calldata.size = UInt256.ofNat 213 := by
    rw [hlen]
  have hlenNotHuge :
      UInt256.gt (UInt256.ofNat I.calldata.size) ⟨18446744073709551615⟩ = ⟨0⟩ := by
    rw [hlen]
    native_decide
  have hfree : solcBytesReturnFreePtr (UInt256.ofNat 213) = ⟨384⟩ := by
    native_decide
  have rd46 := evm_run rd30 with [
    push2 ⟨46⟩,
    push2 ⟨41⟩,
    calldatasize,
    push2 ⟨779⟩,
    jump (by jump_dest),
    raw jumpdest (by decide) (by evm_ov),
    push8 ⟨18446744073709551615⟩,
    dup2,
    gt,
    push2 ⟨774⟩,
    jumpiNT hlenNotHuge,
    push1 ⟨31⟩,
    add,
    push32 ⟨115792089237316195423570985008687907853269984665640564039457584007913129639904⟩,
    and,
    push1 ⟨32⟩,
    add,
    swap1,
    jump (by jump_dest),
    raw jumpdest (by decide) (by evm_ov),
    push2 ⟨706⟩,
    jump (by jump_dest),
    raw jumpdest (by decide) (by evm_ov),
    swap1,
    push32 ⟨115792089237316195423570985008687907853269984665640564039457584007913129639904⟩,
    push1 ⟨31⟩,
    push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost solcFreePtrMem_mload64 (by decide) (by evm_ov),
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
    jumpiNT (by rw [hlen]; native_decide),
    push1 ⟨64⟩,
    raw mstore 0 (solcBytesReturnAllocMem (UInt256.ofNat 213)) (UInt256.ofNat 3)
      (by decide)
      mem_cost
      (by
        rw [hlen]
        unfold solcBytesReturnAllocMem
        native_decide)
      (by decide) (by evm_ov),
    jump (by jump_dest) ]
  exact ⟨_, rd46⟩

/-- The valid path stores the dynamic `bytes` length and copies the full 213-byte calldata payload
into the allocated Solidity bytes buffer.

Source note: this stops immediately after `CALLDATACOPY` at PC `59`.  The next bytecode sequence
writes the zero padding word at the non-word-aligned end of the 213-byte payload. -/
theorem validCalldataCopyPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlen : I.calldata.size = 213)
    (hflag : Model.validFinalFlag I.calldata) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨59⟩ [⟨128⟩, ⟨160⟩] (solcBytesSetCalldataMem I.calldata (UInt256.ofNat 213) ⟨0⟩)
      (UInt256.ofNat 12) ByteArray.empty (cA, σ) k 325 := by
  obtain ⟨k0, rd46⟩ := validAllocationHelperPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hflag
  have rd59 := evm_run rd46 with [
    raw jumpdest (by decide) (by evm_ov),
    calldatasize,
    dup2,
    raw mstore 6 (solcBytesReturnLengthMem (UInt256.ofNat 213)) (UInt256.ofNat 5)
      (by decide)
      mem_cost
      (by
        rw [hlen]
        rw [show (⟨128⟩ : UInt256).toNat = 128 by decide]
        unfold solcBytesReturnLengthMem
        rfl)
      (by decide) (by evm_ov),
    push1 ⟨32⟩,
    dup2,
    add,
    swap1,
    calldatasize,
    push0,
    dup4,
    raw calldatacopy 21 (solcBytesSetCalldataMem I.calldata (UInt256.ofNat 213) ⟨0⟩)
      (UInt256.ofNat 12)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        rw [hlen]
        native_decide)
      (by
        rw [hlen]
        rw [show ((⟨128⟩ : UInt256) + ⟨32⟩).toNat = 160 by decide,
          show (⟨0⟩ : UInt256).toNat = 0 by decide]
        unfold solcBytesSetCalldataMem
        rfl)
      (by rw [hlen]; native_decide) (by evm_ov) ]
  exact ⟨_, by simpa [hlen, GasConstants.Gverylow, GasConstants.Gcopy] using rd59⟩

/-- The valid path finishes materializing `msg.data` as Solidity `bytes memory` and passes the
library-level `input.length == 213` check.

Source note: the local fallback already validated calldata length before allocation; this second
length check is generated by the copied library function `Blake2f.compress(bytes)`. -/
theorem validBytesInputPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlen : I.calldata.size = 213)
    (hflag : Model.validFinalFlag I.calldata) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨76⟩ [⟨128⟩, ⟨160⟩]
      (solcBytesSetPaddedMem I.calldata (UInt256.ofNat 213) ⟨0⟩)
      (UInt256.ofNat 13) ByteArray.empty (cA, σ) k 372 := by
  obtain ⟨k0, rd59⟩ := validCalldataCopyPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hflag
  have hsrc : (⟨0⟩ : UInt256).toNat + (UInt256.ofNat 213).toNat ≤ I.calldata.size := by
    rw [hlen]
    decide
  have hread128 :
      (solcBytesSetPaddedMem I.calldata (UInt256.ofNat 213) ⟨0⟩).readWithPadding 128 32 =
        UInt256.toByteArray (UInt256.ofNat 213) :=
    solcBytesSetPaddedMem_read128 I.calldata (UInt256.ofNat 213) ⟨0⟩
      (by decide) hsrc (by native_decide)
  have hmload128 :
      (if (⟨128⟩ : UInt256).toNat ≥
              (solcBytesSetPaddedMem I.calldata (UInt256.ofNat 213) ⟨0⟩).size
          ∨ (⟨128⟩ : UInt256) ≥ (UInt256.ofNat 13) * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian
            ((solcBytesSetPaddedMem I.calldata (UInt256.ofNat 213) ⟨0⟩).readWithPadding 128 32))) =
        UInt256.ofNat 213 := by
    exact mloadWordValue_of_readWithPadding
      (off := (⟨128⟩ : UInt256)) (aw := UInt256.ofNat 13) (v := UInt256.ofNat 213)
      (by
        rw [show (⟨128⟩ : UInt256).toNat = 128 by decide,
          solcBytesSetPaddedMem_size I.calldata (UInt256.ofNat 213) ⟨0⟩
            (by decide) hsrc (by native_decide)]
        decide)
      (by decide)
      hread128
  have rd76 := evm_run rd59 with [
    push0,
    push1 ⟨32⟩,
    calldatasize,
    dup4,
    add,
    add,
    raw mstore 3 (solcBytesSetPaddedMem I.calldata (UInt256.ofNat 213) ⟨0⟩)
      (UInt256.ofNat 13)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        rw [hlen]
        native_decide)
      (by
        rw [hlen]
        unfold solcBytesSetPaddedMem
        rfl)
      (by rw [hlen]; native_decide) (by evm_ov),
    push1 ⟨213⟩,
    dup2,
    raw mload 0 (UInt256.ofNat 213) (UInt256.ofNat 13)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmload128
      (by decide) (by evm_ov),
    sub,
    push2 ⟨310⟩,
    jumpiNT (by native_decide) ]
  exact ⟨_, by simpa [hlen] using rd76⟩

end Blake2f
