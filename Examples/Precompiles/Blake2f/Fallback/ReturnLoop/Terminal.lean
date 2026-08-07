import Examples.Precompiles.Blake2f.Fallback.ReturnLoop.Words4To7

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

private theorem returnLengthMem_read1984 {mem : ByteArray} (hmem : mem.size = 1984) :
    (returnLengthMem mem).readWithPadding 1984 32 =
      UInt256.toByteArray (UInt256.ofNat 64) := by
  unfold returnLengthMem
  rw [toByteArray_write32_read_back]
  rw [returnAllocMem_size hmem]

private theorem returnZeroPadMem_read1984
    (I : ExecutionEnv) {mem : ByteArray}
    (hlen : I.calldata.size = 213) (hmem : mem.size = 1984) :
    (returnZeroPadMem I mem).readWithPadding 1984 32 =
      UInt256.toByteArray (UInt256.ofNat 64) := by
  have hsize : (returnLengthMem mem).size = 2016 := returnLengthMem_size hmem
  unfold returnZeroPadMem ByteArray.write
  rw [if_neg (by decide : ¬ 64 = 0)]
  rw [if_pos (by rw [hlen])]
  simp [hsize]
  change ((ffi.ByteArray.zeroes 0).copySlice 0 (returnLengthMem mem) 2016 0).readWithPadding
    1984 32 = UInt256.toByteArray (UInt256.ofNat 64)
  rw [copySlice_read_below_gen]
  exact returnLengthMem_read1984 hmem
  · decide
  · rw [hsize]
  · decide
  · decide

private theorem toByteArray_write_preserves_read1984
    (w : UInt256) (mem : ByteArray) (off size : Nat)
    (hsize : mem.size = size) (hread : 2016 ≤ size) (hbelow : 2016 ≤ off)
    (hgap : off - size < USize.size) :
    ((UInt256.toByteArray w).write 0 mem off 32).readWithPadding 1984 32 =
      mem.readWithPadding 1984 32 := by
  exact toByteArray_write_read_below_of_gap w mem off 1984
    (by rw [hsize]; omega) (by omega) (by rwa [hsize])

private theorem returnLoopWord0Mem_read1984
    (I : ExecutionEnv) {mem : ByteArray}
    (hlen : I.calldata.size = 213) (hmem : mem.size = 1984) :
    (returnLoopWord0Mem I mem).readWithPadding 1984 32 =
      UInt256.toByteArray (UInt256.ofNat 64) := by
  unfold returnLoopWord0Mem
  rw [toByteArray_write_preserves_read1984 (returnLoopWord0 I mem) (returnZeroPadMem I mem)
    2016 2016 (returnZeroPadMem_size I hlen hmem) (by decide) (by decide) (by native_decide)]
  exact returnZeroPadMem_read1984 I hlen hmem

private theorem returnLoopWord1Mem_read1984
    (I : ExecutionEnv) {mem : ByteArray}
    (hlen : I.calldata.size = 213) (hmem : mem.size = 1984) :
    (returnLoopWord1Mem I mem).readWithPadding 1984 32 =
      UInt256.toByteArray (UInt256.ofNat 64) := by
  unfold returnLoopWord1Mem
  rw [toByteArray_write_preserves_read1984 (returnLoopWord1 I mem) (returnLoopWord0Mem I mem)
    2024 2048 (returnLoopWord0Mem_size I hlen hmem) (by decide) (by decide) (by native_decide)]
  exact returnLoopWord0Mem_read1984 I hlen hmem

private theorem returnLoopWord2Mem_read1984
    (I : ExecutionEnv) {mem : ByteArray}
    (hlen : I.calldata.size = 213) (hmem : mem.size = 1984) :
    (returnLoopWord2Mem I mem).readWithPadding 1984 32 =
      UInt256.toByteArray (UInt256.ofNat 64) := by
  unfold returnLoopWord2Mem
  rw [toByteArray_write_preserves_read1984 (returnLoopWord2 I mem) (returnLoopWord1Mem I mem)
    2032 2056 (returnLoopWord1Mem_size I hlen hmem) (by decide) (by decide) (by native_decide)]
  exact returnLoopWord1Mem_read1984 I hlen hmem

private theorem returnLoopWord3Mem_read1984
    (I : ExecutionEnv) {mem : ByteArray}
    (hlen : I.calldata.size = 213) (hmem : mem.size = 1984) :
    (returnLoopWord3Mem I mem).readWithPadding 1984 32 =
      UInt256.toByteArray (UInt256.ofNat 64) := by
  unfold returnLoopWord3Mem
  rw [toByteArray_write_preserves_read1984 (returnLoopWord3 I mem) (returnLoopWord2Mem I mem)
    2040 2064 (returnLoopWord2Mem_size I hlen hmem) (by decide) (by decide) (by native_decide)]
  exact returnLoopWord2Mem_read1984 I hlen hmem

private theorem returnLoopWord4Mem_read1984
    (I : ExecutionEnv) {mem : ByteArray}
    (hlen : I.calldata.size = 213) (hmem : mem.size = 1984) :
    (returnLoopWord4Mem I mem).readWithPadding 1984 32 =
      UInt256.toByteArray (UInt256.ofNat 64) := by
  unfold returnLoopWord4Mem
  rw [toByteArray_write_preserves_read1984 (returnLoopWord4 I mem) (returnLoopWord3Mem I mem)
    2048 2072 (returnLoopWord3Mem_size I hlen hmem) (by decide) (by decide) (by native_decide)]
  exact returnLoopWord3Mem_read1984 I hlen hmem

private theorem returnLoopWord5Mem_read1984
    (I : ExecutionEnv) {mem : ByteArray}
    (hlen : I.calldata.size = 213) (hmem : mem.size = 1984) :
    (returnLoopWord5Mem I mem).readWithPadding 1984 32 =
      UInt256.toByteArray (UInt256.ofNat 64) := by
  unfold returnLoopWord5Mem
  rw [toByteArray_write_preserves_read1984 (returnLoopWord5 I mem) (returnLoopWord4Mem I mem)
    2056 2080 (returnLoopWord4Mem_size I hlen hmem) (by decide) (by decide) (by native_decide)]
  exact returnLoopWord4Mem_read1984 I hlen hmem

private theorem returnLoopWord6Mem_read1984
    (I : ExecutionEnv) {mem : ByteArray}
    (hlen : I.calldata.size = 213) (hmem : mem.size = 1984) :
    (returnLoopWord6Mem I mem).readWithPadding 1984 32 =
      UInt256.toByteArray (UInt256.ofNat 64) := by
  unfold returnLoopWord6Mem
  rw [toByteArray_write_preserves_read1984 (returnLoopWord6 I mem) (returnLoopWord5Mem I mem)
    2064 2088 (returnLoopWord5Mem_size I hlen hmem) (by decide) (by decide) (by native_decide)]
  exact returnLoopWord5Mem_read1984 I hlen hmem

private theorem returnLoopWord7Mem_read1984
    (I : ExecutionEnv) {mem : ByteArray}
    (hlen : I.calldata.size = 213) (hmem : mem.size = 1984) :
    (returnLoopWord7Mem I mem).readWithPadding 1984 32 =
      UInt256.toByteArray (UInt256.ofNat 64) := by
  unfold returnLoopWord7Mem
  rw [toByteArray_write_preserves_read1984 (returnLoopWord7 I mem) (returnLoopWord6Mem I mem)
    2072 2096 (returnLoopWord6Mem_size I hlen hmem) (by decide) (by decide) (by native_decide)]
  exact returnLoopWord6Mem_read1984 I hlen hmem

theorem returnLoopExitRetGasFrom {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {k C : Nat}
    (hlen : I.calldata.size = 213)
    (hmem : mem.size = 1984)
    (h : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨179⟩ [⟨8⟩, ⟨1216⟩, ⟨1984⟩]
      (returnLoopWord7Mem I mem) (UInt256.ofNat 66) ByteArray.empty (cA, σ) k C) :
    RDxRet runtimeBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, σ) ((returnLoopWord7Mem I mem).readWithPadding 2016 64) (C + 38) := by
  have hmload1984 :
      (if (⟨1984⟩ : UInt256).toNat ≥ (returnLoopWord7Mem I mem).size
          ∨ (⟨1984⟩ : UInt256) ≥ (UInt256.ofNat 66) * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian ((returnLoopWord7Mem I mem).readWithPadding 1984 32))) =
        UInt256.ofNat 64 := by
    exact mloadWordValue_of_readWithPadding
      (mem := returnLoopWord7Mem I mem) (aw := UInt256.ofNat 66)
      (off := (⟨1984⟩ : UInt256)) (v := UInt256.ofNat 64)
      (by rw [returnLoopWord7Mem_size I hlen hmem]; decide)
      (by native_decide)
      (returnLoopWord7Mem_read1984 I hlen hmem)
  have rd194 := evm_run h with [
    raw jumpdest (by decide) (by evm_ov),
    push1 ⟨8⟩,
    dup2,
    lt,
    push2 ⟨195⟩,
    jumpiNT (by native_decide),
    dup3,
    raw mload 0 (UInt256.ofNat 64) (UInt256.ofNat 66)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmload1984
      (by native_decide) (by evm_ov),
    push1 ⟨32⟩,
    dup5,
    add ]
  exact RDx.ret 0 ((returnLoopWord7Mem I mem).readWithPadding 2016 64)
    rd194
    (by native_decide)
    (by
      intro s haw hstk
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
      native_decide)
    rfl
    (by decide)

/-- Valid final-flag-`0` zero-round inputs terminate successfully with the concrete return slice.

The output is stated as the bytecode memory slice; the bridge to the trusted pure BLAKE2F model is
the next functional-correctness obligation. -/
theorem validReturnZeroRoundsZeroFlagRetGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlen : I.calldata.size = 213)
    (hbyte : I.calldata[212]! = 0)
    (hcond : UInt256.lt ⟨0⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) = ⟨0⟩) :
    RDxRet runtimeBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, σ)
      ((returnLoopWord7Mem I (outputWordsMem (v13MixedMem I))).readWithPadding 2016 64)
      10647 := by
  obtain ⟨k0, rd179⟩ := validReturnWord7ZeroRoundsZeroFlagPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hbyte hcond
  exact returnLoopExitRetGasFrom
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (mem := outputWordsMem (v13MixedMem I)) (k := k0) (C := 10609)
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

/-- Valid final-flag-`1` zero-round inputs terminate successfully with the concrete return slice. -/
theorem validReturnZeroRoundsOneFlagRetGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlen : I.calldata.size = 213)
    (hbyte : I.calldata[212]! = 1)
    (hcond : UInt256.lt ⟨0⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) = ⟨0⟩) :
    RDxRet runtimeBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, σ)
      ((returnLoopWord7Mem I (outputWordsMem (v14FinalFlagMem I))).readWithPadding 2016 64)
      10674 := by
  obtain ⟨k0, rd179⟩ := validReturnWord7ZeroRoundsOneFlagPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hbyte hcond
  exact returnLoopExitRetGasFrom
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (mem := outputWordsMem (v14FinalFlagMem I)) (k := k0) (C := 10636)
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
