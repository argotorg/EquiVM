import Examples.Precompiles.Blake2f.Fallback.Base

/-!
# BLAKE2F fallback return-loop traces

This module contains the zero-round output return-buffer allocation and final return-formatting
loop proofs.  It is split out of the main fallback trace file so that active work on exact return
gas does not recheck the parser/compression/output-prefix proof body.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

private theorem returnAllocatorPrefixGasFrom {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {k C : Nat}
    (hmem : mem.size = 1984)
    (hread : mem.readWithPadding 64 32 = UInt256.toByteArray (UInt256.ofNat 1984))
    (h : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨168⟩ [⟨1216⟩] mem (UInt256.ofNat 62) ByteArray.empty (cA, σ) k C) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨899⟩ [⟨1984⟩, ⟨176⟩, ⟨96⟩, ⟨1216⟩]
      (returnAllocMem mem) (UInt256.ofNat 62) ByteArray.empty (cA, σ) k (C + 118) := by
  have hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨64⟩ : UInt256) ≥ (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian (mem.readWithPadding 64 32))) =
        UInt256.ofNat 1984 := by
    exact mloadWordValue_of_readWithPadding
      (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨64⟩ : UInt256))
      (v := UInt256.ofNat 1984)
      (by rw [hmem]; decide)
      (by native_decide)
      hread
  have rd899 := evm_run h with [
    raw jumpdest (by decide) (by evm_ov),
    push2 ⟨176⟩,
    push2 ⟨887⟩,
    jump (by jump_dest),
    raw jumpdest (by decide) (by evm_ov),
    push1 ⟨96⟩,
    swap1,
    push2 ⟨899⟩,
    dup3,
    push2 ⟨706⟩,
    jump (by jump_dest),
    raw jumpdest (by decide) (by evm_ov),
    swap1,
    push32 ⟨115792089237316195423570985008687907853269984665640564039457584007913129639904⟩,
    push1 ⟨31⟩,
    push1 ⟨64⟩,
    raw mload 0 ⟨1984⟩ (UInt256.ofNat 62) (by decide)
      mem_cost hmload64 (by decide) (by evm_ov),
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
    raw mstore 0 (returnAllocMem mem) (UInt256.ofNat 62)
      (by decide)
      mem_cost
      (by
        have hnew :
            (⟨1984⟩ +
                UInt256.land (⟨96⟩ + ⟨31⟩)
                  ⟨115792089237316195423570985008687907853269984665640564039457584007913129639904⟩) =
              UInt256.ofNat 2080 := by
          native_decide
        rw [hnew]
        unfold returnAllocMem
        rfl)
      (by decide) (by evm_ov),
    jump (by jump_dest) ]
  exact ⟨_, by simpa [GasConstants.Gverylow] using rd899⟩

/-- Valid final-flag-`0` zero-round inputs have allocated the Solidity return buffer.

Source note: this steps from PC `168` through the shared allocator at PC `887`/`706`, stopping at
PC `899` with the allocated payload pointer (`0x7c0`) on the stack.  The allocator rounds the
fixed return length `0x60` and updates Solidity's free-memory pointer to `0x820`. -/
theorem validReturnAllocZeroRoundsZeroFlagPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlen : I.calldata.size = 213)
    (hbyte : I.calldata[212]! = 0)
    (hcond : UInt256.lt ⟨0⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) = ⟨0⟩) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨899⟩ [⟨1984⟩, ⟨176⟩, ⟨96⟩, ⟨1216⟩]
      (returnAllocMem (outputWordsMem (v13MixedMem I)))
      (UInt256.ofNat 62) ByteArray.empty (cA, σ) k 8895 := by
  obtain ⟨k0, rd168⟩ := validOutputLoopExitZeroRoundsZeroFlagPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hbyte hcond
  exact returnAllocatorPrefixGasFrom
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (mem := outputWordsMem (v13MixedMem I)) (k := k0) (C := 8777)
    (by
      rw [outputWordsMem]
      exact outputWord7Mem_size
        (outputWord6Mem_size
          (outputWord5Mem_size
            (outputWord4Mem_size
              (outputWord3Mem_size
                (outputWord2Mem_size (outputWord1Mem_size
                  (outputWord0Mem_size (v13MixedMem_size I hlen)))))))))
    (outputWordsMem_read64 (v13MixedMem_size I hlen) (v13MixedMem_read64 I hlen))
    rd168

/-- Valid final-flag-`1` zero-round inputs have allocated the Solidity return buffer. -/
theorem validReturnAllocZeroRoundsOneFlagPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlen : I.calldata.size = 213)
    (hbyte : I.calldata[212]! = 1)
    (hcond : UInt256.lt ⟨0⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) = ⟨0⟩) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨899⟩ [⟨1984⟩, ⟨176⟩, ⟨96⟩, ⟨1216⟩]
      (returnAllocMem (outputWordsMem (v14FinalFlagMem I)))
      (UInt256.ofNat 62) ByteArray.empty (cA, σ) k 8922 := by
  obtain ⟨k0, rd168⟩ := validOutputLoopExitZeroRoundsOneFlagPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hbyte hcond
  exact returnAllocatorPrefixGasFrom
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (mem := outputWordsMem (v14FinalFlagMem I)) (k := k0) (C := 8804)
    (by
      rw [outputWordsMem]
      exact outputWord7Mem_size
        (outputWord6Mem_size
          (outputWord5Mem_size
            (outputWord4Mem_size
              (outputWord3Mem_size
                (outputWord2Mem_size (outputWord1Mem_size
                  (outputWord0Mem_size (v14FinalFlagMem_size I hlen)))))))))
    (outputWordsMem_read64 (v14FinalFlagMem_size I hlen) (v14FinalFlagMem_read64 I hlen))
    rd168

private theorem returnBufferCopyPrefixGasFrom {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {k C : Nat}
    (hlen : I.calldata.size = 213)
    (h : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨899⟩ [⟨1984⟩, ⟨176⟩, ⟨96⟩, ⟨1216⟩]
      (returnAllocMem mem) (UInt256.ofNat 62) ByteArray.empty (cA, σ) k C) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨176⟩ [⟨1984⟩, ⟨1216⟩]
      (returnZeroPadMem I mem) (UInt256.ofNat 65) ByteArray.empty (cA, σ) k (C + 57) := by
  have rd176 := evm_run h with [
    raw jumpdest (by decide) (by evm_ov),
    push1 ⟨64⟩,
    dup2,
    raw mstore 3 (returnLengthMem mem) (UInt256.ofNat 63)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      (by
        unfold returnLengthMem
        rfl)
      (by native_decide) (by evm_ov),
    swap2,
    push32 ⟨115792089237316195423570985008687907853269984665640564039457584007913129639904⟩,
    add,
    calldatasize,
    push1 ⟨32⟩,
    dup5,
    add,
    raw calldatacopy 7 (returnZeroPadMem I mem) (UInt256.ofNat 65)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      (by
        rw [hlen]
        unfold returnZeroPadMem
        rfl)
      (by native_decide) (by evm_ov),
    jump (by jump_dest) ]
  exact ⟨_, by simpa [GasConstants.Gverylow, GasConstants.Gcopy] using rd176⟩

/-- Valid final-flag-`0` zero-round inputs have returned from the return-buffer copy helper.

The cursor is PC `176`, immediately before the final return formatting loop, with stack
`[0x7c0, 0x4c0]`, active words `65`, and exact cumulative gas `8952`. -/
theorem validReturnCopyZeroRoundsZeroFlagPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlen : I.calldata.size = 213)
    (hbyte : I.calldata[212]! = 0)
    (hcond : UInt256.lt ⟨0⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) = ⟨0⟩) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨176⟩ [⟨1984⟩, ⟨1216⟩]
      (returnZeroPadMem I (outputWordsMem (v13MixedMem I)))
      (UInt256.ofNat 65) ByteArray.empty (cA, σ) k 8952 := by
  obtain ⟨k0, rd899⟩ := validReturnAllocZeroRoundsZeroFlagPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hbyte hcond
  exact returnBufferCopyPrefixGasFrom
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (mem := outputWordsMem (v13MixedMem I)) (k := k0) (C := 8895) hlen rd899

/-- Valid final-flag-`1` zero-round inputs have returned from the return-buffer copy helper. -/
theorem validReturnCopyZeroRoundsOneFlagPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlen : I.calldata.size = 213)
    (hbyte : I.calldata[212]! = 1)
    (hcond : UInt256.lt ⟨0⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) = ⟨0⟩) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨176⟩ [⟨1984⟩, ⟨1216⟩]
      (returnZeroPadMem I (outputWordsMem (v14FinalFlagMem I)))
      (UInt256.ofNat 65) ByteArray.empty (cA, σ) k 8979 := by
  obtain ⟨k0, rd899⟩ := validReturnAllocZeroRoundsOneFlagPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hbyte hcond
  exact returnBufferCopyPrefixGasFrom
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (mem := outputWordsMem (v14FinalFlagMem I)) (k := k0) (C := 8922) hlen rd899

private theorem returnLoopSetupPrefixGasFrom {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {aw : UInt256} {k C : Nat}
    (h : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨176⟩ [⟨1984⟩, ⟨1216⟩]
      mem aw ByteArray.empty (cA, σ) k C) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨179⟩ [⟨0⟩, ⟨1216⟩, ⟨1984⟩]
      mem aw ByteArray.empty (cA, σ) k (C + 6) := by
  have rd179 := evm_run h with [
    raw jumpdest (by decide) (by evm_ov),
    swap1,
    push0 ]
  exact ⟨_, by simpa [GasConstants.Gverylow] using rd179⟩

/-- Valid final-flag-`0` zero-round inputs are at the final return-loop head.

The cursor is PC `179`, with loop index `0`, scratch output pointer `0x4c0`, return buffer pointer
`0x7c0`, active words `65`, and exact cumulative gas `8958`. -/
theorem validReturnLoopSetupZeroRoundsZeroFlagPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlen : I.calldata.size = 213)
    (hbyte : I.calldata[212]! = 0)
    (hcond : UInt256.lt ⟨0⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) = ⟨0⟩) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨179⟩ [⟨0⟩, ⟨1216⟩, ⟨1984⟩]
      (returnZeroPadMem I (outputWordsMem (v13MixedMem I)))
      (UInt256.ofNat 65) ByteArray.empty (cA, σ) k 8958 := by
  obtain ⟨k0, rd176⟩ := validReturnCopyZeroRoundsZeroFlagPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hbyte hcond
  exact returnLoopSetupPrefixGasFrom
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (mem := returnZeroPadMem I (outputWordsMem (v13MixedMem I)))
    (aw := UInt256.ofNat 65) (k := k0) (C := 8952) rd176

/-- Valid final-flag-`1` zero-round inputs are at the final return-loop head. -/
theorem validReturnLoopSetupZeroRoundsOneFlagPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlen : I.calldata.size = 213)
    (hbyte : I.calldata[212]! = 1)
    (hcond : UInt256.lt ⟨0⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) = ⟨0⟩) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨179⟩ [⟨0⟩, ⟨1216⟩, ⟨1984⟩]
      (returnZeroPadMem I (outputWordsMem (v14FinalFlagMem I)))
      (UInt256.ofNat 65) ByteArray.empty (cA, σ) k 8985 := by
  obtain ⟨k0, rd176⟩ := validReturnCopyZeroRoundsOneFlagPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hbyte hcond
  exact returnLoopSetupPrefixGasFrom
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (mem := returnZeroPadMem I (outputWordsMem (v14FinalFlagMem I)))
    (aw := UInt256.ofNat 65) (k := k0) (C := 8979) rd176

end Blake2f
