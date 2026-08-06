import Examples.Precompiles.Blake2f.Fallback.Setup.Compression.Entry.TLoopExit

/-!
# BLAKE2F fallback compression entry: FinalFlagCheck
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

theorem validFinalFlagCheckPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlen : I.calldata.size = 213)
    (hflag : Model.validFinalFlag I.calldata) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨155⟩ [⟨310⟩, parsedFinalFlagBranchCond I, ⟨384⟩, ⟨640⟩, ⟨1152⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, parsedFinalFlagWord I]
      (t1StoredMem I) (UInt256.ofNat 38) ByteArray.empty (cA, σ) k 6423 := by
  obtain ⟨k0, rd140⟩ := validTLoopExitPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hflag
  have hmload372 :
      (if (⟨372⟩ : UInt256).toNat ≥ (t1StoredMem I).size
          ∨ (⟨372⟩ : UInt256) ≥ (UInt256.ofNat 38) * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian ((t1StoredMem I).readWithPadding 372 32))) =
        finalFlagLoadWord I := by
    unfold finalFlagLoadWord
    exact mloadValue_eq_readWithPadding_of_lt_size
      (mem := t1StoredMem I) (aw := UInt256.ofNat 38) (off := (⟨372⟩ : UInt256))
      (memSize := 1216) (t1StoredMem_size I hlen) (by decide) (by decide)
  have rd155 := evm_run rd140 with [
    push1 ⟨244⟩,
    add,
    raw mload 0 (finalFlagLoadWord I) (UInt256.ofNat 38)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmload372
      (by native_decide) (by evm_ov),
    push1 ⟨248⟩,
    shr,
    swap4,
    push1 ⟨1⟩,
    dup6,
    gt,
    push2 ⟨310⟩ ]
  exact ⟨_, by simpa [parsedFinalFlagWord, parsedFinalFlagBranchCond] using rd155⟩

end Blake2f
