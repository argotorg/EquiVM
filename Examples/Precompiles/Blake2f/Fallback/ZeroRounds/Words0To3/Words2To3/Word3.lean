import Examples.Precompiles.Blake2f.Fallback.ZeroRounds.Words0To3.Words2To3.Word2

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

theorem outputLoopFourthBodyPrefixGasFrom {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {k C : Nat}
    (hmem : mem.size = 1984)
    (h : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1395⟩ [⟨3⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      mem (UInt256.ofNat 62) ByteArray.empty (cA, σ) k C) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1382⟩ [⟨4⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (outputWord3Mem mem) (UInt256.ofNat 62) ByteArray.empty (cA, σ) k (C + 111) := by
  have hmload480 :
      (if (⟨480⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨480⟩ : UInt256) ≥ (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian (mem.readWithPadding 480 32))) =
        outputH3LoadWord mem := by
    unfold outputH3LoadWord
    exact mloadValue_eq_readWithPadding_of_lt_size
      (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨480⟩ : UInt256))
      (memSize := 1984) hmem (by decide) (by decide)
  have hmload1568 :
      (if (⟨1568⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨1568⟩ : UInt256) ≥ (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian (mem.readWithPadding 1568 32))) =
        outputV3LoadWord mem := by
    unfold outputV3LoadWord
    exact mloadValue_eq_readWithPadding_of_lt_size
      (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨1568⟩ : UInt256))
      (memSize := 1984) hmem (by decide) (by decide)
  have hmload1824 :
      (if (⟨1824⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨1824⟩ : UInt256) ≥ (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian (mem.readWithPadding 1824 32))) =
        outputV11LoadWord mem := by
    unfold outputV11LoadWord
    exact mloadValue_eq_readWithPadding_of_lt_size
      (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨1824⟩ : UInt256))
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
    raw mload 0 (outputH3LoadWord mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmload480
      (by native_decide) (by evm_ov),
    and,
    dup3,
    dup8,
    add,
    raw mload 0 (outputV3LoadWord mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmload1568
      (by native_decide) (by evm_ov),
    push1 ⟨8⟩,
    dup6,
    add,
    push1 ⟨5⟩,
    shl,
    dup9,
    add,
    raw mload 0 (outputV11LoadWord mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmload1824
      (by native_decide) (by evm_ov),
    swap2,
    xor,
    xor,
    and,
    swap1,
    dup8,
    add,
    raw mstore 0 (outputWord3Mem mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      (by
        unfold outputWord3Mem outputWord3
        rfl)
      (by native_decide) (by evm_ov),
    add,
    push2 ⟨1382⟩,
    jump (by jump_dest) ]
  exact ⟨_, by simpa [GasConstants.Gverylow] using rd1382⟩

/-- Valid final-flag-`0` zero-round inputs have completed the fourth output-loop write. -/
theorem validOutputWord3ZeroRoundsZeroFlagPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlen : I.calldata.size = 213)
    (hbyte : I.calldata[212]! = 0)
    (hcond : UInt256.lt ⟨0⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) = ⟨0⟩) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1382⟩
      [⟨4⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (outputWord3Mem (outputWord2Mem (outputWord1Mem (outputWord0Mem (v13MixedMem I)))))
      (UInt256.ofNat 62) ByteArray.empty (cA, σ) k 8204 := by
  obtain ⟨k0, rd1382⟩ := validOutputWord2ZeroRoundsZeroFlagPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hbyte hcond
  have rd1395 := evm_run rd1382 with [
    raw jumpdest (by decide) (by evm_ov),
    push1 ⟨8⟩,
    dup2,
    lt,
    push2 ⟨1395⟩,
    jumpiT (by native_decide) (by jump_dest) ]
  obtain ⟨k1, rd1382'⟩ := outputLoopFourthBodyPrefixGasFrom
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (mem := outputWord2Mem (outputWord1Mem (outputWord0Mem (v13MixedMem I)))) (k := _)
    (C := 8093)
    (outputWord2Mem_size (outputWord1Mem_size (outputWord0Mem_size (v13MixedMem_size I hlen))))
    rd1395
  exact ⟨k1, by simpa using rd1382'⟩

/-- Valid final-flag-`1` zero-round inputs have completed the fourth output-loop write. -/
theorem validOutputWord3ZeroRoundsOneFlagPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlen : I.calldata.size = 213)
    (hbyte : I.calldata[212]! = 1)
    (hcond : UInt256.lt ⟨0⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) = ⟨0⟩) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1382⟩
      [⟨4⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (outputWord3Mem (outputWord2Mem (outputWord1Mem (outputWord0Mem (v14FinalFlagMem I)))))
      (UInt256.ofNat 62) ByteArray.empty (cA, σ) k 8231 := by
  obtain ⟨k0, rd1382⟩ := validOutputWord2ZeroRoundsOneFlagPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hbyte hcond
  have rd1395 := evm_run rd1382 with [
    raw jumpdest (by decide) (by evm_ov),
    push1 ⟨8⟩,
    dup2,
    lt,
    push2 ⟨1395⟩,
    jumpiT (by native_decide) (by jump_dest) ]
  obtain ⟨k1, rd1382'⟩ := outputLoopFourthBodyPrefixGasFrom
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (mem := outputWord2Mem (outputWord1Mem (outputWord0Mem (v14FinalFlagMem I)))) (k := _)
    (C := 8120)
    (outputWord2Mem_size (outputWord1Mem_size (outputWord0Mem_size (v14FinalFlagMem_size I hlen))))
    rd1395
  exact ⟨k1, by simpa using rd1382'⟩

end Blake2f
