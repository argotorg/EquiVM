import Examples.Precompiles.Blake2f.Fallback.ReturnLoop.Words0To3

/-!
# BLAKE2F fallback return-loop words 4 through 5
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

private theorem returnLoopFifthWordPrefixGasFrom {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {k C : Nat}
    (hlen : I.calldata.size = 213)
    (hmem : mem.size = 1984)
    (h : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨179⟩ [⟨4⟩, ⟨1216⟩, ⟨1984⟩]
      (returnLoopWord3Mem I mem) (UInt256.ofNat 65) ByteArray.empty (cA, σ) k C) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨179⟩ [⟨5⟩, ⟨1216⟩, ⟨1984⟩]
      (returnLoopWord4Mem I mem) (UInt256.ofNat 65) ByteArray.empty (cA, σ) k (C + 206) := by
  have hmload1344 :
      (if (⟨1344⟩ : UInt256).toNat ≥ (returnLoopWord3Mem I mem).size
          ∨ (⟨1344⟩ : UInt256) ≥ (UInt256.ofNat 65) * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian ((returnLoopWord3Mem I mem).readWithPadding 1344 32))) =
        returnLoopLoadWord4 I mem := by
    unfold returnLoopLoadWord4
    exact mloadValue_eq_readWithPadding_of_lt_size
      (mem := returnLoopWord3Mem I mem) (aw := UInt256.ofNat 65)
      (off := (⟨1344⟩ : UInt256)) (memSize := 2072)
      (returnLoopWord3Mem_size I hlen hmem) (by decide) (by native_decide)
  have rd179 := evm_run h with [
    raw jumpdest (by decide) (by evm_ov),
    push1 ⟨8⟩,
    dup2,
    lt,
    push2 ⟨195⟩,
    jumpiT (by native_decide) (by jump_dest),
    raw jumpdest (by decide) (by evm_ov),
    dup1,
    push2 ⟨291⟩,
    push1 ⟨1⟩,
    swap3,
    push1 ⟨5⟩,
    shl,
    dup5,
    add,
    raw mload 0 (returnLoopLoadWord4 I mem) (UInt256.ofNat 65)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmload1344
      (by native_decide) (by evm_ov),
    push8 ⟨18374966859414961920⟩,
    push7 ⟨71777214294589695⟩,
    dup3,
    push1 ⟨8⟩,
    shr,
    and,
    swap2,
    push1 ⟨8⟩,
    shl,
    and,
    or,
    push8 ⟨18446462603027742720⟩,
    push6 ⟨281470681808895⟩,
    dup3,
    push1 ⟨16⟩,
    shr,
    and,
    swap2,
    push1 ⟨16⟩,
    shl,
    and,
    or,
    push8 ⟨18446744069414584320⟩,
    push4 ⟨4294967295⟩,
    dup3,
    push1 ⟨32⟩,
    shr,
    and,
    swap2,
    push1 ⟨32⟩,
    shl,
    and,
    or,
    swap1,
    jump (by jump_dest),
    raw jumpdest (by decide) (by evm_ov),
    push1 ⟨192⟩,
    shl,
    push1 ⟨32⟩,
    dup3,
    push1 ⟨3⟩,
    shl,
    dup7,
    add,
    add,
    raw mstore 0 (returnLoopWord4Mem I mem) (UInt256.ofNat 65)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      (by
        unfold returnLoopWord4Mem returnLoopWord4 evmSwap64
        rfl)
      (by native_decide) (by evm_ov),
    add,
    push2 ⟨179⟩,
    jump (by jump_dest) ]
  have hidx : (⟨4⟩ : UInt256) + ⟨1⟩ = ⟨5⟩ := by native_decide
  have rd179' := by simpa [hidx] using rd179
  exact ⟨k + 65, RDx.withIndices (k' := k + 65) (C' := C + 206)
    rd179' (by rfl) (by omega)⟩

/-- Valid final-flag-`0` zero-round inputs have written the fifth 64-bit return word.

The cursor has returned to PC `179` with loop index `5`; exact cumulative gas is `9988`. -/
theorem validReturnWord4ZeroRoundsZeroFlagPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlen : I.calldata.size = 213)
    (hbyte : I.calldata[212]! = 0)
    (hcond : UInt256.lt ⟨0⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) = ⟨0⟩) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨179⟩ [⟨5⟩, ⟨1216⟩, ⟨1984⟩]
      (returnLoopWord4Mem I (outputWordsMem (v13MixedMem I)))
      (UInt256.ofNat 65) ByteArray.empty (cA, σ) k 9988 := by
  obtain ⟨k0, rd179⟩ := validReturnWord3ZeroRoundsZeroFlagPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hbyte hcond
  exact returnLoopFifthWordPrefixGasFrom
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (mem := outputWordsMem (v13MixedMem I)) (k := k0) (C := 9782)
    hlen
    (by
      rw [outputWordsMem]
      exact outputWord7Mem_size
        (outputWord6Mem_size
          (outputWord5Mem_size
            (outputWord4Mem_size
              (outputWord3Mem_size
                (outputWord2Mem_size (outputWord1Mem_size
                  (outputWord0Mem_size (v13MixedMem_size I hlen)))))))))
    rd179

/-- Valid final-flag-`1` zero-round inputs have written the fifth 64-bit return word. -/
theorem validReturnWord4ZeroRoundsOneFlagPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlen : I.calldata.size = 213)
    (hbyte : I.calldata[212]! = 1)
    (hcond : UInt256.lt ⟨0⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) = ⟨0⟩) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨179⟩ [⟨5⟩, ⟨1216⟩, ⟨1984⟩]
      (returnLoopWord4Mem I (outputWordsMem (v14FinalFlagMem I)))
      (UInt256.ofNat 65) ByteArray.empty (cA, σ) k 10015 := by
  obtain ⟨k0, rd179⟩ := validReturnWord3ZeroRoundsOneFlagPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hbyte hcond
  exact returnLoopFifthWordPrefixGasFrom
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (mem := outputWordsMem (v14FinalFlagMem I)) (k := k0) (C := 9809)
    hlen
    (by
      rw [outputWordsMem]
      exact outputWord7Mem_size
        (outputWord6Mem_size
          (outputWord5Mem_size
            (outputWord4Mem_size
              (outputWord3Mem_size
                (outputWord2Mem_size (outputWord1Mem_size
                  (outputWord0Mem_size (v14FinalFlagMem_size I hlen)))))))))
    rd179

end Blake2f
