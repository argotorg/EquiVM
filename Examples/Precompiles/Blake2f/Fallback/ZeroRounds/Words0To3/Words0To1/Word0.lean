import Examples.Precompiles.Blake2f.Fallback.ZeroRounds.Setup

/-!
# BLAKE2F fallback zero-round output-loop words 0 through 1
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

theorem outputLoopFirstBodyPrefixGasFrom {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {k C : Nat}
    (hmem : mem.size = 1984)
    (h : RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1395⟩ [⟨0⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      mem (UInt256.ofNat 62) ByteArray.empty (cA, σ) k C) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1382⟩ [⟨1⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (outputWord0Mem mem) (UInt256.ofNat 62) ByteArray.empty (cA, σ) k (C + 111) := by
  have hmload384 :
      (if (⟨384⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨384⟩ : UInt256) ≥ (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian (mem.readWithPadding 384 32))) =
        outputH0LoadWord mem := by
    unfold outputH0LoadWord
    exact mloadValue_eq_readWithPadding_of_lt_size
      (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨384⟩ : UInt256))
      (memSize := 1984) hmem (by decide) (by decide)
  have hmload1472 :
      (if (⟨1472⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨1472⟩ : UInt256) ≥ (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian (mem.readWithPadding 1472 32))) =
        outputV0LoadWord mem := by
    unfold outputV0LoadWord
    exact mloadValue_eq_readWithPadding_of_lt_size
      (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨1472⟩ : UInt256))
      (memSize := 1984) hmem (by decide) (by decide)
  have hmload1728 :
      (if (⟨1728⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨1728⟩ : UInt256) ≥ (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian (mem.readWithPadding 1728 32))) =
        outputV8LoadWord mem := by
    unfold outputV8LoadWord
    exact mloadValue_eq_readWithPadding_of_lt_size
      (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨1728⟩ : UInt256))
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
    raw mload 0 (outputH0LoadWord mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmload384
      (by native_decide) (by evm_ov),
    and,
    dup3,
    dup8,
    add,
    raw mload 0 (outputV0LoadWord mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmload1472
      (by native_decide) (by evm_ov),
    push1 ⟨8⟩,
    dup6,
    add,
    push1 ⟨5⟩,
    shl,
    dup9,
    add,
    raw mload 0 (outputV8LoadWord mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmload1728
      (by native_decide) (by evm_ov),
    swap2,
    xor,
    xor,
    and,
    swap1,
    dup8,
    add,
    raw mstore 0 (outputWord0Mem mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      (by
        unfold outputWord0Mem outputWord0
        rfl)
      (by native_decide) (by evm_ov),
    add,
    push2 ⟨1382⟩,
    jump (by jump_dest) ]
  exact ⟨_, by simpa [GasConstants.Gverylow] using rd1382⟩

/-- Valid final-flag-`0` zero-round inputs have completed the first output-loop iteration.

Source note: PC `1395..1444` stores
`(h[0] ^ v[0] ^ v[8]) & uint64.max` into the scratch output buffer at `0x4c0`, then returns to the
output-loop head with index `1`. -/
theorem validOutputWord0ZeroRoundsZeroFlagPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlen : I.calldata.size = 213)
    (hbyte : I.calldata[212]! = 0)
    (hcond : UInt256.lt ⟨0⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) = ⟨0⟩) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1382⟩
      [⟨1⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (outputWord0Mem (v13MixedMem I)) (UInt256.ofNat 62) ByteArray.empty (cA, σ) k 7802 := by
  obtain ⟨k0, rd1395⟩ := validOutputLoopBodyZeroRoundsZeroFlagPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hbyte hcond
  obtain ⟨k1, rd1382⟩ := outputLoopFirstBodyPrefixGasFrom
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (mem := v13MixedMem I) (k := k0) (C := 7691) (v13MixedMem_size I hlen) rd1395
  exact ⟨k1, by simpa using rd1382⟩

/-- Valid final-flag-`1` zero-round inputs have completed the first output-loop iteration.

This is the same output write as the flag-`0` case, but from the memory where the final-block tweak
has overwritten `v[14]`. -/
theorem validOutputWord0ZeroRoundsOneFlagPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlen : I.calldata.size = 213)
    (hbyte : I.calldata[212]! = 1)
    (hcond : UInt256.lt ⟨0⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) = ⟨0⟩) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1382⟩
      [⟨1⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (outputWord0Mem (v14FinalFlagMem I)) (UInt256.ofNat 62) ByteArray.empty (cA, σ) k 7829 := by
  obtain ⟨k0, rd1395⟩ := validOutputLoopBodyZeroRoundsOneFlagPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hbyte hcond
  obtain ⟨k1, rd1382⟩ := outputLoopFirstBodyPrefixGasFrom
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (mem := v14FinalFlagMem I) (k := k0) (C := 7718) (v14FinalFlagMem_size I hlen) rd1395
  exact ⟨k1, by simpa using rd1382⟩

end Blake2f
