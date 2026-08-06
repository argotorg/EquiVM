import Examples.Precompiles.Blake2f.Fallback.Setup.Compression.Entry

/-!
# BLAKE2F fallback compression vector initialization, words 0 through 3
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

theorem validV0InitPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlen : I.calldata.size = 213)
    (hflag : Model.validFinalFlag I.calldata) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1182⟩
      [⟨1⟩, ⟨1152⟩, UInt256.eq (parsedFinalFlagWord I) ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (v0InitMem I) (UInt256.ofNat 47) ByteArray.empty (cA, σ) k 6778 := by
  obtain ⟨k0, rd1182⟩ := validVInitLoopEntryPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hflag
  have hmload384 :
      (if (⟨384⟩ : UInt256).toNat ≥ (compressionVAllocMem I).size
          ∨ (⟨384⟩ : UInt256) ≥ (UInt256.ofNat 46) * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian ((compressionVAllocMem I).readWithPadding 384 32))) =
        v0LoadWord I := by
    unfold v0LoadWord
    exact mloadValue_eq_readWithPadding_of_lt_size
      (mem := compressionVAllocMem I) (aw := UInt256.ofNat 46) (off := (⟨384⟩ : UInt256))
      (memSize := 1216) (compressionVAllocMem_size I hlen) (by decide) (by decide)
  have rd1182' := evm_run rd1182 with [
    raw jumpdest (by decide) (by evm_ov),
    push1 ⟨8⟩,
    dup2,
    lt,
    push2 ⟨3318⟩,
    jumpiT (by native_decide) (by jump_dest),
    raw jumpdest (by decide) (by evm_ov),
    dup1,
    push1 ⟨1⟩,
    swap2,
    push1 ⟨5⟩,
    shl,
    push8 ⟨18446744073709551615⟩,
    dup2,
    dup10,
    add,
    raw mload 0 (v0LoadWord I) (UInt256.ofNat 46)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmload384
      (by native_decide) (by evm_ov),
    and,
    swap1,
    dup10,
    add,
    raw mstore 3 (v0InitMem I) (UInt256.ofNat 47)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      (by
        unfold v0InitMem v0StoredWord
        rfl)
      (by native_decide) (by evm_ov),
    add,
    push2 ⟨1182⟩,
    jump (by jump_dest) ]
  exact ⟨_, by simpa [v0StoredWord, GasConstants.Gverylow] using rd1182'⟩

/-- Second working-vector initialization iteration.

Source note: this is the same loop body as `validV0InitPrefixGas`, now for `i = 1`; it copies the
exact bytecode-loaded word from `h + 32` into `v + 32`. -/
theorem validV1InitPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlen : I.calldata.size = 213)
    (hflag : Model.validFinalFlag I.calldata) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1182⟩
      [⟨2⟩, ⟨1152⟩, UInt256.eq (parsedFinalFlagWord I) ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (v1InitMem I) (UInt256.ofNat 48) ByteArray.empty (cA, σ) k 6864 := by
  obtain ⟨k0, rd1182⟩ := validV0InitPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hflag
  have hmload416 :
      (if (⟨416⟩ : UInt256).toNat ≥ (v0InitMem I).size
          ∨ (⟨416⟩ : UInt256) ≥ (UInt256.ofNat 47) * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian ((v0InitMem I).readWithPadding 416 32))) =
        v1LoadWord I := by
    unfold v1LoadWord
    exact mloadValue_eq_readWithPadding_of_lt_size
      (mem := v0InitMem I) (aw := UInt256.ofNat 47) (off := (⟨416⟩ : UInt256))
      (memSize := 1504) (v0InitMem_size I hlen) (by decide) (by decide)
  have rd1182' := evm_run rd1182 with [
    raw jumpdest (by decide) (by evm_ov),
    push1 ⟨8⟩,
    dup2,
    lt,
    push2 ⟨3318⟩,
    jumpiT (by native_decide) (by jump_dest),
    raw jumpdest (by decide) (by evm_ov),
    dup1,
    push1 ⟨1⟩,
    swap2,
    push1 ⟨5⟩,
    shl,
    push8 ⟨18446744073709551615⟩,
    dup2,
    dup10,
    add,
    raw mload 0 (v1LoadWord I) (UInt256.ofNat 47)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmload416
      (by native_decide) (by evm_ov),
    and,
    swap1,
    dup10,
    add,
    raw mstore 3 (v1InitMem I) (UInt256.ofNat 48)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      (by
        unfold v1InitMem v1StoredWord
        rfl)
      (by native_decide) (by evm_ov),
    add,
    push2 ⟨1182⟩,
    jump (by jump_dest) ]
  exact ⟨_, by simpa [v1StoredWord, GasConstants.Gverylow] using rd1182'⟩

/-- Third working-vector initialization iteration.

Source note: same bytecode loop body, now for `i = 2`; it copies the exact bytecode-loaded word
from `h + 64` into `v + 64`. -/
theorem validV2InitPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlen : I.calldata.size = 213)
    (hflag : Model.validFinalFlag I.calldata) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1182⟩
      [⟨3⟩, ⟨1152⟩, UInt256.eq (parsedFinalFlagWord I) ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (v2InitMem I) (UInt256.ofNat 49) ByteArray.empty (cA, σ) k 6950 := by
  obtain ⟨k0, rd1182⟩ := validV1InitPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hflag
  have hmload448 :
      (if (⟨448⟩ : UInt256).toNat ≥ (v1InitMem I).size
          ∨ (⟨448⟩ : UInt256) ≥ (UInt256.ofNat 48) * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian ((v1InitMem I).readWithPadding 448 32))) =
        v2LoadWord I := by
    unfold v2LoadWord
    exact mloadValue_eq_readWithPadding_of_lt_size
      (mem := v1InitMem I) (aw := UInt256.ofNat 48) (off := (⟨448⟩ : UInt256))
      (memSize := 1536) (v1InitMem_size I hlen) (by decide) (by decide)
  have rd1182' := evm_run rd1182 with [
    raw jumpdest (by decide) (by evm_ov),
    push1 ⟨8⟩,
    dup2,
    lt,
    push2 ⟨3318⟩,
    jumpiT (by native_decide) (by jump_dest),
    raw jumpdest (by decide) (by evm_ov),
    dup1,
    push1 ⟨1⟩,
    swap2,
    push1 ⟨5⟩,
    shl,
    push8 ⟨18446744073709551615⟩,
    dup2,
    dup10,
    add,
    raw mload 0 (v2LoadWord I) (UInt256.ofNat 48)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmload448
      (by native_decide) (by evm_ov),
    and,
    swap1,
    dup10,
    add,
    raw mstore 3 (v2InitMem I) (UInt256.ofNat 49)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      (by
        unfold v2InitMem v2StoredWord
        rfl)
      (by native_decide) (by evm_ov),
    add,
    push2 ⟨1182⟩,
    jump (by jump_dest) ]
  exact ⟨_, by simpa [v2StoredWord, GasConstants.Gverylow] using rd1182'⟩

/-- Fourth working-vector initialization iteration.

Source note: same bytecode loop body, now for `i = 3`; it copies the exact bytecode-loaded word
from `h + 96` into `v + 96`. -/
theorem validV3InitPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlen : I.calldata.size = 213)
    (hflag : Model.validFinalFlag I.calldata) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1182⟩
      [⟨4⟩, ⟨1152⟩, UInt256.eq (parsedFinalFlagWord I) ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (v3InitMem I) (UInt256.ofNat 50) ByteArray.empty (cA, σ) k 7036 := by
  obtain ⟨k0, rd1182⟩ := validV2InitPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hflag
  have hmload480 :
      (if (⟨480⟩ : UInt256).toNat ≥ (v2InitMem I).size
          ∨ (⟨480⟩ : UInt256) ≥ (UInt256.ofNat 49) * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian ((v2InitMem I).readWithPadding 480 32))) =
        v3LoadWord I := by
    unfold v3LoadWord
    exact mloadValue_eq_readWithPadding_of_lt_size
      (mem := v2InitMem I) (aw := UInt256.ofNat 49) (off := (⟨480⟩ : UInt256))
      (memSize := 1568) (v2InitMem_size I hlen) (by decide) (by decide)
  have rd1182' := evm_run rd1182 with [
    raw jumpdest (by decide) (by evm_ov),
    push1 ⟨8⟩,
    dup2,
    lt,
    push2 ⟨3318⟩,
    jumpiT (by native_decide) (by jump_dest),
    raw jumpdest (by decide) (by evm_ov),
    dup1,
    push1 ⟨1⟩,
    swap2,
    push1 ⟨5⟩,
    shl,
    push8 ⟨18446744073709551615⟩,
    dup2,
    dup10,
    add,
    raw mload 0 (v3LoadWord I) (UInt256.ofNat 49)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmload480
      (by native_decide) (by evm_ov),
    and,
    swap1,
    dup10,
    add,
    raw mstore 3 (v3InitMem I) (UInt256.ofNat 50)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      (by
        unfold v3InitMem v3StoredWord
        rfl)
      (by native_decide) (by evm_ov),
    add,
    push2 ⟨1182⟩,
    jump (by jump_dest) ]
  exact ⟨_, by simpa [v3StoredWord, GasConstants.Gverylow] using rd1182'⟩
