import Examples.Precompiles.Blake2f.Fallback.ZeroRounds.Words4To7.Words4To5

/-!
# BLAKE2F fallback zero-round output-loop words 6 through loop exit
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

theorem outputLoopSeventhBodyPrefixGasFrom {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {k C : Nat}
    (hmem : mem.size = 1984)
    (h : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1395⟩ [⟨6⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      mem (UInt256.ofNat 62) ByteArray.empty (cA, σ) k C) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1382⟩ [⟨7⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (outputWord6Mem mem) (UInt256.ofNat 62) ByteArray.empty (cA, σ) k (C + 111) := by
  have hmload576 :
      (if (⟨576⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨576⟩ : UInt256) ≥ (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian (mem.readWithPadding 576 32))) =
        outputH6LoadWord mem := by
    unfold outputH6LoadWord
    exact mloadValue_eq_readWithPadding_of_lt_size
      (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨576⟩ : UInt256))
      (memSize := 1984) hmem (by decide) (by decide)
  have hmload1664 :
      (if (⟨1664⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨1664⟩ : UInt256) ≥ (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian (mem.readWithPadding 1664 32))) =
        outputV6LoadWord mem := by
    unfold outputV6LoadWord
    exact mloadValue_eq_readWithPadding_of_lt_size
      (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨1664⟩ : UInt256))
      (memSize := 1984) hmem (by decide) (by decide)
  have hmload1920 :
      (if (⟨1920⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨1920⟩ : UInt256) ≥ (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian (mem.readWithPadding 1920 32))) =
        outputV14LoadWord mem := by
    unfold outputV14LoadWord
    exact mloadValue_eq_readWithPadding_of_lt_size
      (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨1920⟩ : UInt256))
      (memSize := 1984) hmem (by decide) (by decide)
  have rd1382 := evm_run h with [
    raw jumpdest (by decide) (by evm_ov),
    dup1,
    push1 ⟨1⟩,
    swap2,
    push1 ⟨5⟩,
    shl,
    push8 ⟨18446744073709551615⟩,
    dup1,
    dup3,
    dup7,
    add,
    raw mload 0 (outputH6LoadWord mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmload576
      (by native_decide) (by evm_ov),
    and,
    dup3,
    dup8,
    add,
    raw mload 0 (outputV6LoadWord mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmload1664
      (by native_decide) (by evm_ov),
    push1 ⟨8⟩,
    dup6,
    add,
    push1 ⟨5⟩,
    shl,
    dup9,
    add,
    raw mload 0 (outputV14LoadWord mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmload1920
      (by native_decide) (by evm_ov),
    swap2,
    xor,
    xor,
    and,
    swap1,
    dup8,
    add,
    raw mstore 0 (outputWord6Mem mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      (by
        unfold outputWord6Mem outputWord6
        rfl)
      (by native_decide) (by evm_ov),
    add,
    push2 ⟨1382⟩,
    jump (by jump_dest) ]
  exact ⟨_, by simpa [GasConstants.Gverylow] using rd1382⟩

/-- Valid final-flag-`0` zero-round inputs have completed the seventh output-loop write. -/
theorem validOutputWord6ZeroRoundsZeroFlagPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlen : I.calldata.size = 213)
    (hbyte : I.calldata[212]! = 0)
    (hcond : UInt256.lt ⟨0⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) = ⟨0⟩) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1382⟩
      [⟨7⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (outputWord6Mem
        (outputWord5Mem
          (outputWord4Mem
            (outputWord3Mem
              (outputWord2Mem (outputWord1Mem (outputWord0Mem (v13MixedMem I))))))))
      (UInt256.ofNat 62) ByteArray.empty (cA, σ) k 8606 := by
  obtain ⟨k0, rd1382⟩ := validOutputWord5ZeroRoundsZeroFlagPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hbyte hcond
  have rd1395 := evm_run rd1382 with [
    raw jumpdest (by decide) (by evm_ov),
    push1 ⟨8⟩,
    dup2,
    lt,
    push2 ⟨1395⟩,
    jumpiT (by native_decide) (by jump_dest) ]
  obtain ⟨k1, rd1382'⟩ := outputLoopSeventhBodyPrefixGasFrom
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (mem :=
      outputWord5Mem
        (outputWord4Mem
          (outputWord3Mem
            (outputWord2Mem (outputWord1Mem (outputWord0Mem (v13MixedMem I)))))))
    (k := _) (C := 8495)
    (outputWord5Mem_size
      (outputWord4Mem_size
        (outputWord3Mem_size
          (outputWord2Mem_size
            (outputWord1Mem_size (outputWord0Mem_size (v13MixedMem_size I hlen)))))))
    rd1395
  exact ⟨k1, by simpa using rd1382'⟩

/-- Valid final-flag-`1` zero-round inputs have completed the seventh output-loop write. -/
theorem validOutputWord6ZeroRoundsOneFlagPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlen : I.calldata.size = 213)
    (hbyte : I.calldata[212]! = 1)
    (hcond : UInt256.lt ⟨0⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) = ⟨0⟩) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1382⟩
      [⟨7⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (outputWord6Mem
        (outputWord5Mem
          (outputWord4Mem
            (outputWord3Mem
              (outputWord2Mem (outputWord1Mem (outputWord0Mem (v14FinalFlagMem I))))))))
      (UInt256.ofNat 62) ByteArray.empty (cA, σ) k 8633 := by
  obtain ⟨k0, rd1382⟩ := validOutputWord5ZeroRoundsOneFlagPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hbyte hcond
  have rd1395 := evm_run rd1382 with [
    raw jumpdest (by decide) (by evm_ov),
    push1 ⟨8⟩,
    dup2,
    lt,
    push2 ⟨1395⟩,
    jumpiT (by native_decide) (by jump_dest) ]
  obtain ⟨k1, rd1382'⟩ := outputLoopSeventhBodyPrefixGasFrom
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (mem :=
      outputWord5Mem
        (outputWord4Mem
          (outputWord3Mem
            (outputWord2Mem (outputWord1Mem (outputWord0Mem (v14FinalFlagMem I)))))))
    (k := _) (C := 8522)
    (outputWord5Mem_size
      (outputWord4Mem_size
        (outputWord3Mem_size
          (outputWord2Mem_size
            (outputWord1Mem_size (outputWord0Mem_size (v14FinalFlagMem_size I hlen)))))))
    rd1395
  exact ⟨k1, by simpa using rd1382'⟩

end Blake2f
