import Examples.Precompiles.Blake2f.Fallback.ZeroRounds.Words4To7.Words6To7.Word6

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

theorem outputLoopEighthBodyPrefixGasFrom {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {k C : Nat}
    (hmem : mem.size = 1984)
    (h : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1395⟩ [⟨7⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      mem (UInt256.ofNat 62) ByteArray.empty (cA, σ) k C) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1382⟩ [⟨8⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (outputWord7Mem mem) (UInt256.ofNat 62) ByteArray.empty (cA, σ) k (C + 111) := by
  have hmload608 :
      (if (⟨608⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨608⟩ : UInt256) ≥ (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian (mem.readWithPadding 608 32))) =
        outputH7LoadWord mem := by
    unfold outputH7LoadWord
    exact mloadValue_eq_readWithPadding_of_lt_size
      (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨608⟩ : UInt256))
      (memSize := 1984) hmem (by decide) (by decide)
  have hmload1696 :
      (if (⟨1696⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨1696⟩ : UInt256) ≥ (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian (mem.readWithPadding 1696 32))) =
        outputV7LoadWord mem := by
    unfold outputV7LoadWord
    exact mloadValue_eq_readWithPadding_of_lt_size
      (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨1696⟩ : UInt256))
      (memSize := 1984) hmem (by decide) (by decide)
  have hmload1952 :
      (if (⟨1952⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨1952⟩ : UInt256) ≥ (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian (mem.readWithPadding 1952 32))) =
        outputV15LoadWord mem := by
    unfold outputV15LoadWord
    exact mloadValue_eq_readWithPadding_of_lt_size
      (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨1952⟩ : UInt256))
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
    raw mload 0 (outputH7LoadWord mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmload608
      (by native_decide) (by evm_ov),
    and,
    dup3,
    dup8,
    add,
    raw mload 0 (outputV7LoadWord mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmload1696
      (by native_decide) (by evm_ov),
    push1 ⟨8⟩,
    dup6,
    add,
    push1 ⟨5⟩,
    shl,
    dup9,
    add,
    raw mload 0 (outputV15LoadWord mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmload1952
      (by native_decide) (by evm_ov),
    swap2,
    xor,
    xor,
    and,
    swap1,
    dup8,
    add,
    raw mstore 0 (outputWord7Mem mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      (by
        unfold outputWord7Mem outputWord7
        rfl)
      (by native_decide) (by evm_ov),
    add,
    push2 ⟨1382⟩,
    jump (by jump_dest) ]
  exact ⟨_, by simpa [GasConstants.Gverylow] using rd1382⟩

/-- Valid final-flag-`0` zero-round inputs have completed the eighth output-loop write. -/
theorem validOutputWord7ZeroRoundsZeroFlagPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlen : I.calldata.size = 213)
    (hbyte : I.calldata[212]! = 0)
    (hcond : UInt256.lt ⟨0⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) = ⟨0⟩) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1382⟩
      [⟨8⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (outputWord7Mem
        (outputWord6Mem
          (outputWord5Mem
            (outputWord4Mem
              (outputWord3Mem
                (outputWord2Mem (outputWord1Mem (outputWord0Mem (v13MixedMem I)))))))))
      (UInt256.ofNat 62) ByteArray.empty (cA, σ) k 8740 := by
  obtain ⟨k0, rd1382⟩ := validOutputWord6ZeroRoundsZeroFlagPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hbyte hcond
  have rd1395 := evm_run rd1382 with [
    raw jumpdest (by decide) (by evm_ov),
    push1 ⟨8⟩,
    dup2,
    lt,
    push2 ⟨1395⟩,
    jumpiT (by native_decide) (by jump_dest) ]
  obtain ⟨k1, rd1382'⟩ := outputLoopEighthBodyPrefixGasFrom
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (mem :=
      outputWord6Mem
        (outputWord5Mem
          (outputWord4Mem
            (outputWord3Mem
              (outputWord2Mem (outputWord1Mem (outputWord0Mem (v13MixedMem I))))))))
    (k := _) (C := 8629)
    (outputWord6Mem_size
      (outputWord5Mem_size
        (outputWord4Mem_size
          (outputWord3Mem_size
            (outputWord2Mem_size
              (outputWord1Mem_size (outputWord0Mem_size (v13MixedMem_size I hlen))))))))
    rd1395
  exact ⟨k1, by simpa using rd1382'⟩

/-- Valid final-flag-`1` zero-round inputs have completed the eighth output-loop write. -/
theorem validOutputWord7ZeroRoundsOneFlagPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlen : I.calldata.size = 213)
    (hbyte : I.calldata[212]! = 1)
    (hcond : UInt256.lt ⟨0⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) = ⟨0⟩) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1382⟩
      [⟨8⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (outputWord7Mem
        (outputWord6Mem
          (outputWord5Mem
            (outputWord4Mem
              (outputWord3Mem
                (outputWord2Mem (outputWord1Mem (outputWord0Mem (v14FinalFlagMem I)))))))))
      (UInt256.ofNat 62) ByteArray.empty (cA, σ) k 8767 := by
  obtain ⟨k0, rd1382⟩ := validOutputWord6ZeroRoundsOneFlagPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hbyte hcond
  have rd1395 := evm_run rd1382 with [
    raw jumpdest (by decide) (by evm_ov),
    push1 ⟨8⟩,
    dup2,
    lt,
    push2 ⟨1395⟩,
    jumpiT (by native_decide) (by jump_dest) ]
  obtain ⟨k1, rd1382'⟩ := outputLoopEighthBodyPrefixGasFrom
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (mem :=
      outputWord6Mem
        (outputWord5Mem
          (outputWord4Mem
            (outputWord3Mem
              (outputWord2Mem (outputWord1Mem (outputWord0Mem (v14FinalFlagMem I))))))))
    (k := _) (C := 8656)
    (outputWord6Mem_size
      (outputWord5Mem_size
        (outputWord4Mem_size
          (outputWord3Mem_size
            (outputWord2Mem_size
              (outputWord1Mem_size (outputWord0Mem_size (v14FinalFlagMem_size I hlen))))))))
    rd1395
  exact ⟨k1, by simpa using rd1382'⟩

/-- Valid final-flag-`0` zero-round inputs have exited the output loop.

Source note: at PC `1382`, output index `8` makes the guard `i < 8` false.  The fallthrough
`POP; POP; POP; JUMP` discards the output-loop state and jumps to PC `168`, leaving the scratch
output pointer on the stack. -/
theorem validOutputLoopExitZeroRoundsZeroFlagPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlen : I.calldata.size = 213)
    (hbyte : I.calldata[212]! = 0)
    (hcond : UInt256.lt ⟨0⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) = ⟨0⟩) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨168⟩
      [⟨1216⟩]
      (outputWordsMem (v13MixedMem I)) (UInt256.ofNat 62) ByteArray.empty (cA, σ) k 8777 := by
  obtain ⟨k0, rd1382⟩ := validOutputWord7ZeroRoundsZeroFlagPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hbyte hcond
  have rd168 := evm_run rd1382 with [
    raw jumpdest (by decide) (by evm_ov),
    push1 ⟨8⟩,
    dup2,
    lt,
    push2 ⟨1395⟩,
    jumpiNT (by native_decide),
    pop,
    pop,
    pop,
    jump (by jump_dest) ]
  exact ⟨_, by simpa [outputWordsMem] using rd168⟩

/-- Valid final-flag-`1` zero-round inputs have exited the output loop.

This is the same output-loop exit as the flag-`0` case, from the final-flag-adjusted memory. -/
theorem validOutputLoopExitZeroRoundsOneFlagPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlen : I.calldata.size = 213)
    (hbyte : I.calldata[212]! = 1)
    (hcond : UInt256.lt ⟨0⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) = ⟨0⟩) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨168⟩
      [⟨1216⟩]
      (outputWordsMem (v14FinalFlagMem I)) (UInt256.ofNat 62) ByteArray.empty (cA, σ) k 8804 := by
  obtain ⟨k0, rd1382⟩ := validOutputWord7ZeroRoundsOneFlagPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hbyte hcond
  have rd168 := evm_run rd1382 with [
    raw jumpdest (by decide) (by evm_ov),
    push1 ⟨8⟩,
    dup2,
    lt,
    push2 ⟨1395⟩,
    jumpiNT (by native_decide),
    pop,
    pop,
    pop,
    jump (by jump_dest) ]
  exact ⟨_, by simpa [outputWordsMem] using rd168⟩

end Blake2f
