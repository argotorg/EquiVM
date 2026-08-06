import Examples.Precompiles.Blake2f.Fallback.Setup.Compression.V8ToFinal.V15

/-!
# BLAKE2F fallback compression V8-to-final: TMix
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

theorem validTMixBranchPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlen : I.calldata.size = 213)
    (hflag : Model.validFinalFlag I.calldata) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1367⟩
      [⟨3298⟩, UInt256.eq (parsedFinalFlagWord I) ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (v13MixedMem I) (UInt256.ofNat 62) ByteArray.empty (cA, σ) k 7624 := by
  obtain ⟨k0, rd1312⟩ := validV15InitPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hflag
  have hmload1152 :
      (if (⟨1152⟩ : UInt256).toNat ≥ (v15InitMem I).size
          ∨ (⟨1152⟩ : UInt256) ≥ (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian ((v15InitMem I).readWithPadding 1152 32))) =
        t0MixLoadWord I := by
    unfold t0MixLoadWord
    exact mloadValue_eq_readWithPadding_of_lt_size
      (mem := v15InitMem I) (aw := UInt256.ofNat 62) (off := (⟨1152⟩ : UInt256))
      (memSize := 1984) (v15InitMem_size I hlen) (by decide) (by decide)
  have hmload1184 :
      (if (⟨1184⟩ : UInt256).toNat ≥ (v15InitMem I).size
          ∨ (⟨1184⟩ : UInt256) ≥ (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian ((v15InitMem I).readWithPadding 1184 32))) =
        t1MixLoadWord I := by
    unfold t1MixLoadWord
    exact mloadValue_eq_readWithPadding_of_lt_size
      (mem := v15InitMem I) (aw := UInt256.ofNat 62) (off := (⟨1184⟩ : UInt256))
      (memSize := 1984) (v15InitMem_size I hlen) (by decide) (by decide)
  have rd1367 := evm_run rd1312 with [
    push8 ⟨18446744073709551615⟩,
    push1 ⟨32⟩,
    dup2,
    dup4,
    raw mload 0 (t0MixLoadWord I) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmload1152
      (by native_decide) (by evm_ov),
    and,
    swap3,
    add,
    raw mload 0 (t1MixLoadWord I) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmload1184
      (by native_decide) (by evm_ov),
    and,
    swap1,
    push8 ⟨5840696475078001361⟩,
    xor,
    push2 ⟨384⟩,
    dup8,
    add,
    raw mstore 0 (v12MixedMem I) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      (by
        unfold v12MixedMem v12MixedWord t0MixMaskedWord
        rfl)
      (by native_decide) (by evm_ov),
    push8 ⟨11170449401992604703⟩,
    xor,
    push2 ⟨416⟩,
    dup7,
    add,
    raw mstore 0 (v13MixedMem I) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      (by
        unfold v13MixedMem v13MixedWord t1MixMaskedWord
        rfl)
      (by native_decide) (by evm_ov),
    push2 ⟨3298⟩ ]
  exact ⟨_, by simpa [GasConstants.Gverylow] using rd1367⟩

end Blake2f
