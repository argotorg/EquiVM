import Examples.Precompiles.Blake2f.Fallback.PositiveRounds.Round1Mix4Selector

/-!
# BLAKE2F fallback positive-round traces: round-1 first diagonal `mixG`

This module continues the multi-round path from PC `2429`, the first diagonal `mixG` routine for
round-1 vector slots `v[0]`, `v[5]`, `v[10]`, and `v[15]`, using message words `m[1]` and
`m[12]`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

abbrev round1Mix4V0Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1472 32))

abbrev round1Mix4V5Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1632 32))

abbrev round1Mix4V10Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1792 32))

abbrev round1Mix4V15Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1952 32))

abbrev round1Mix4A0 (mem : ByteArray) : UInt256 :=
  mask64Bytecode (round1Mix4V0Load mem + round1Mix4V5Load mem + round1M1Arg mem)

abbrev round1Mix4D0 (mem : ByteArray) : UInt256 :=
  rotr64Bytecode (UInt256.xor (round1Mix4V15Load mem) (round1Mix4A0 mem)) ⟨32⟩ ⟨32⟩

abbrev round1Mix4C0 (mem : ByteArray) : UInt256 :=
  mask64Bytecode (round1Mix4V10Load mem + round1Mix4D0 mem)

abbrev round1Mix4B0 (mem : ByteArray) : UInt256 :=
  rotr64Bytecode (UInt256.xor (round1Mix4V5Load mem) (round1Mix4C0 mem)) ⟨24⟩ ⟨40⟩

abbrev round1Mix4A1 (mem : ByteArray) : UInt256 :=
  mask64Bytecode (round1Mix4A0 mem + round1Mix4B0 mem + round1M12Arg mem)

abbrev round1Mix4D1 (mem : ByteArray) : UInt256 :=
  rotr64Bytecode (UInt256.xor (round1Mix4D0 mem) (round1Mix4A1 mem)) ⟨16⟩ ⟨48⟩

abbrev round1Mix4C1 (mem : ByteArray) : UInt256 :=
  mask64Bytecode (round1Mix4C0 mem + round1Mix4D1 mem)

abbrev round1Mix4B1 (mem : ByteArray) : UInt256 :=
  rotr64Bytecode (UInt256.xor (round1Mix4B0 mem) (round1Mix4C1 mem)) ⟨63⟩ ⟨1⟩

def round1Mix4Mem0 (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray (round1Mix4A1 mem)).write 0 mem
    (⟨1472⟩ : UInt256).toNat 32

def round1Mix4Mem1 (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray (round1Mix4B1 mem)).write 0 (round1Mix4Mem0 mem)
    ((⟨1472⟩ : UInt256) + ⟨160⟩).toNat 32

def round1Mix4Mem2 (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray (round1Mix4C1 mem)).write 0 (round1Mix4Mem1 mem)
    ((⟨1472⟩ : UInt256) + ⟨320⟩).toNat 32

def round1Mix4Mem3 (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray (round1Mix4D1 mem)).write 0 (round1Mix4Mem2 mem)
    ((⟨1472⟩ : UInt256) + ⟨480⟩).toNat 32

theorem round1Mix4Mem0_size {mem : ByteArray} (hmem : mem.size = 1984) :
    (round1Mix4Mem0 mem).size = 1984 := by
  unfold round1Mix4Mem0
  apply toByteArray_write32_size_of_le
  · exact hmem
  · rw [hmem]
    decide
  · native_decide

theorem round1Mix4Mem1_size {mem : ByteArray} (hmem : mem.size = 1984) :
    (round1Mix4Mem1 mem).size = 1984 := by
  unfold round1Mix4Mem1
  apply toByteArray_write32_size_of_le
  · exact round1Mix4Mem0_size hmem
  · rw [round1Mix4Mem0_size hmem]
    decide
  · native_decide

theorem round1Mix4Mem2_size {mem : ByteArray} (hmem : mem.size = 1984) :
    (round1Mix4Mem2 mem).size = 1984 := by
  unfold round1Mix4Mem2
  apply toByteArray_write32_size_of_le
  · exact round1Mix4Mem1_size hmem
  · rw [round1Mix4Mem1_size hmem]
    decide
  · native_decide

theorem round1Mix4Mem3_size {mem : ByteArray} (hmem : mem.size = 1984) :
    (round1Mix4Mem3 mem).size = 1984 := by
  unfold round1Mix4Mem3
  apply toByteArray_write32_size_of_le
  · exact round1Mix4Mem2_size hmem
  · rw [round1Mix4Mem2_size hmem]
    decide
  · native_decide

private theorem round1Mix4Mload1472 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (⟨1472⟩ : UInt256).toNat ≥ mem.size
        ∨ (⟨1472⟩ : UInt256) ≥ (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1472 32))) =
      round1Mix4V0Load mem := by
  unfold round1Mix4V0Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨1472⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem round1Mix4Mload1632 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (⟨1632⟩ : UInt256).toNat ≥ mem.size
        ∨ (⟨1632⟩ : UInt256) ≥ (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1632 32))) =
      round1Mix4V5Load mem := by
  unfold round1Mix4V5Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨1632⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem round1Mix4Mload1792 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (⟨1792⟩ : UInt256).toNat ≥ mem.size
        ∨ (⟨1792⟩ : UInt256) ≥ (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1792 32))) =
      round1Mix4V10Load mem := by
  unfold round1Mix4V10Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨1792⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem round1Mix4Mload1952 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (⟨1952⟩ : UInt256).toNat ≥ mem.size
        ∨ (⟨1952⟩ : UInt256) ≥ (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1952 32))) =
      round1Mix4V15Load mem := by
  unfold round1Mix4V15Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨1952⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem round1Mix4BodyFromArgsGas {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {startGas : Nat}
    (hmem : mem.size = 1984)
    (hprefix :
      ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨2429⟩
        [round1M12Arg mem, round1M1Arg mem, ⟨2610⟩, sigmaRound1Word,
          ⟨3109⟩, ⟨3292⟩, ⟨1⟩, ⟨1⟩, ⟨640⟩,
          UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
        mem (UInt256.ofNat 62) ByteArray.empty (cA, σ) k startGas) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨2610⟩
      [sigmaRound1Word, ⟨3109⟩, ⟨3292⟩, ⟨1⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (round1Mix4Mem3 mem) (UInt256.ofNat 62) ByteArray.empty (cA, σ) k (startGas + 315) := by
  obtain ⟨k0, rd2429⟩ := hprefix
  have hmload1472 := round1Mix4Mload1472 hmem
  have hmload1632 := round1Mix4Mload1632 hmem
  have hmload1792 := round1Mix4Mload1792 hmem
  have hmload1952 := round1Mix4Mload1952 hmem
  have rd2610 := evm_run rd2429 with [
    raw jumpdest (by decide) (by evm_ov),
    swap1,
    push2 ⟨480⟩,
    dup13,
    add,
    push2 ⟨320⟩,
    dup14,
    add,
    dup14,
    push1 ⟨160⟩,
    dup2,
    add,
    swap1,
    swap4,
    swap3,
    swap4,
    dup1,
    raw mload 0 (round1Mix4V0Load mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmload1472
      (by native_decide) (by evm_ov),
    swap4,
    dup3,
    raw mload 0 (round1Mix4V5Load mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmload1632
      (by native_decide) (by evm_ov),
    swap7,
    dup5,
    raw mload 0 (round1Mix4V10Load mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmload1792
      (by native_decide) (by evm_ov),
    swap2,
    dup9,
    dup9,
    raw mload 0 (round1Mix4V15Load mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmload1952
      (by native_decide) (by evm_ov),
    swap8,
    add,
    add,
    push8 u64MaskWord,
    and,
    dup1,
    swap7,
    xor,
    dup1,
    push1 ⟨32⟩,
    shl,
    swap1,
    push1 ⟨32⟩,
    shr,
    or,
    push8 u64MaskWord,
    and,
    dup1,
    swap3,
    add,
    push8 u64MaskWord,
    and,
    dup1,
    swap9,
    xor,
    dup1,
    push1 ⟨40⟩,
    shl,
    swap1,
    push1 ⟨24⟩,
    shr,
    or,
    push8 u64MaskWord,
    and,
    dup1,
    swap7,
    add,
    add,
    push8 u64MaskWord,
    and,
    dup1,
    swap2,
    xor,
    dup1,
    push1 ⟨48⟩,
    shl,
    swap1,
    push1 ⟨16⟩,
    shr,
    or,
    push8 u64MaskWord,
    and,
    dup1,
    swap8,
    add,
    push8 u64MaskWord,
    and,
    dup1,
    swap6,
    xor,
    swap2,
    raw mstore 0 (round1Mix4Mem0 mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      (by
        unfold round1Mix4Mem0
        simp [round1Mix4A1, round1Mix4B0, round1Mix4C0, round1Mix4D0, round1Mix4A0,
          rotr64Bytecode, mask64Bytecode, u64MaskWord])
      (by native_decide) (by evm_ov),
    dup1,
    push1 ⟨1⟩,
    shl,
    swap1,
    push1 ⟨63⟩,
    shr,
    or,
    push8 u64MaskWord,
    and,
    swap1,
    raw mstore 0 (round1Mix4Mem1 mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      (by
        unfold round1Mix4Mem1
        simp [round1Mix4B1, round1Mix4C1, round1Mix4D1, round1Mix4A1, round1Mix4B0,
          round1Mix4C0, round1Mix4D0, round1Mix4A0, rotr64Bytecode, mask64Bytecode,
          u64MaskWord])
      (by native_decide) (by evm_ov),
    raw mstore 0 (round1Mix4Mem2 mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      (by
        unfold round1Mix4Mem2
        simp [round1Mix4C1, round1Mix4D1, round1Mix4A1, round1Mix4B0, round1Mix4C0,
          round1Mix4D0, round1Mix4A0, rotr64Bytecode, mask64Bytecode, u64MaskWord])
      (by native_decide) (by evm_ov),
    raw mstore 0 (round1Mix4Mem3 mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      (by
        unfold round1Mix4Mem3
        simp [round1Mix4D1, round1Mix4A1, round1Mix4B0, round1Mix4C0, round1Mix4D0,
          round1Mix4A0, rotr64Bytecode, mask64Bytecode, u64MaskWord])
      (by native_decide) (by evm_ov),
    jump (by jump_dest) ]
  exact ⟨_, by
    simpa [round1Mix4A0, round1Mix4D0, round1Mix4C0, round1Mix4B0, round1Mix4A1,
      round1Mix4D1, round1Mix4C1, round1Mix4B1, rotr64Bytecode, mask64Bytecode,
      u64MaskWord, Nat.add_assoc] using rd2610⟩

/-- Final-flag-`0`, at least two rounds: the first diagonal round-1 `mixG` call is complete. -/
theorem validPositiveRound1Mix4DoneZeroFlagPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlen : I.calldata.size = 213)
    (hbyte : I.calldata[212]! = 0)
    (hpos : UInt256.lt ⟨0⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont : UInt256.lt ⟨1⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨2610⟩
      [sigmaRound1Word, ⟨3109⟩, ⟨3292⟩, ⟨1⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (round1Mix4Mem3
        (round1Mix3Mem3
          (round1Mix2Mem3
            (round1Mix1Mem3
              (round1Mix0Mem3
                (eighthMixMem3
                  (seventhMixMem3
                    (sixthMixMem3
                      (fifthMixMem3 (fourthMixMem3 (thirdMixMem3 (secondMixMem3 (firstMixMem3 (v13MixedMem I))))))))))))))
      (UInt256.ofNat 62) ByteArray.empty (cA, σ) k 13216 := by
  have hprefix := validPositiveRound1Mix4ArgsZeroFlagPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hbyte hpos hcont
  simpa using round1Mix4BodyFromArgsGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (mem := round1Mix3Mem3
      (round1Mix2Mem3
        (round1Mix1Mem3
          (round1Mix0Mem3
            (eighthMixMem3
              (seventhMixMem3
                (sixthMixMem3
                  (fifthMixMem3 (fourthMixMem3 (thirdMixMem3 (secondMixMem3 (firstMixMem3 (v13MixedMem I)))))))))))))
    (startGas := 12901)
    (round1Mix3Mem3_size
      (round1Mix2Mem3_size
        (round1Mix1Mem3_size
          (round1Mix0Mem3_size
            (eighthMixMem3_size
              (seventhMixMem3_size
                (sixthMixMem3_size
                  (fifthMixMem3_size
                    (fourthMixMem3_size (thirdMixMem3_size (secondMixMem3_size (firstMixMem3_size (v13MixedMem_size I hlen)))))))))))))
    hprefix

/-- Final-flag-`1`, at least two rounds: the first diagonal round-1 `mixG` call is complete. -/
theorem validPositiveRound1Mix4DoneOneFlagPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlen : I.calldata.size = 213)
    (hbyte : I.calldata[212]! = 1)
    (hpos : UInt256.lt ⟨0⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont : UInt256.lt ⟨1⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨2610⟩
      [sigmaRound1Word, ⟨3109⟩, ⟨3292⟩, ⟨1⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (round1Mix4Mem3
        (round1Mix3Mem3
          (round1Mix2Mem3
            (round1Mix1Mem3
              (round1Mix0Mem3
                (eighthMixMem3
                  (seventhMixMem3
                    (sixthMixMem3
                      (fifthMixMem3 (fourthMixMem3 (thirdMixMem3 (secondMixMem3 (firstMixMem3 (v14FinalFlagMem I))))))))))))))
      (UInt256.ofNat 62) ByteArray.empty (cA, σ) k 13243 := by
  have hprefix := validPositiveRound1Mix4ArgsOneFlagPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hbyte hpos hcont
  simpa using round1Mix4BodyFromArgsGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (mem := round1Mix3Mem3
      (round1Mix2Mem3
        (round1Mix1Mem3
          (round1Mix0Mem3
            (eighthMixMem3
              (seventhMixMem3
                (sixthMixMem3
                  (fifthMixMem3 (fourthMixMem3 (thirdMixMem3 (secondMixMem3 (firstMixMem3 (v14FinalFlagMem I)))))))))))))
    (startGas := 12928)
    (round1Mix3Mem3_size
      (round1Mix2Mem3_size
        (round1Mix1Mem3_size
          (round1Mix0Mem3_size
            (eighthMixMem3_size
              (seventhMixMem3_size
                (sixthMixMem3_size
                  (fifthMixMem3_size
                    (fourthMixMem3_size (thirdMixMem3_size (secondMixMem3_size (firstMixMem3_size (v14FinalFlagMem_size I hlen)))))))))))))
    hprefix

end Blake2f
