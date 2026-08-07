import Examples.Precompiles.Blake2f.Fallback.PositiveRounds.Guard3

/-!
# BLAKE2F fallback positive-round traces: round-3 SIGMA selector

This module starts the fourth compression round on the path with at least four rounds. From
PC `1445` with loop index `3`, the bytecode computes `3 % 10`, selects packed SIGMA word
`0x7931dcbe265a40f8`, loads message words `m[7]` and `m[9]`, and jumps to the first shared
`mixG` body at PC `1512`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

/-- The compiled selector's packed SIGMA word for round `3`. -/
abbrev sigmaRound3Word : UInt256 :=
  ⟨8733003861693448440⟩

/-- Round-3 SIGMA index `0` selects bytecode memory offset `864`, i.e. `m[7]`. -/
theorem sigmaRound3Offset0 : ⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound3Word ⟨55⟩)
    ⟨480⟩ = (⟨864⟩ : UInt256) := by
  native_decide

/-- Round-3 SIGMA index `1` selects bytecode memory offset `928`, i.e. `m[9]`. -/
theorem sigmaRound3Offset1 : UInt256.land (UInt256.shiftRight sigmaRound3Word ⟨51⟩)
    ⟨480⟩ + ⟨640⟩ = (⟨928⟩ : UInt256) := by
  native_decide

abbrev round3M7Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 864 32))

abbrev round3M9Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 928 32))

abbrev round3M7Arg (mem : ByteArray) : UInt256 :=
  UInt256.land (round3M7Load mem) u64MaskWord

abbrev round3M9Arg (mem : ByteArray) : UInt256 :=
  UInt256.land (round3M9Load mem) u64MaskWord

private theorem round3SelectorMloadM7 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound3Word ⟨55⟩) ⟨480⟩).toNat ≥
          mem.size
        ∨ (⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound3Word ⟨55⟩) ⟨480⟩) ≥
          (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding
        (⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound3Word ⟨55⟩) ⟨480⟩).toNat 32))) =
      round3M7Load mem := by
  rw [sigmaRound3Offset0]
  unfold round3M7Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨864⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem round3SelectorMloadM9 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (UInt256.land (UInt256.shiftRight sigmaRound3Word ⟨51⟩) ⟨480⟩ + ⟨640⟩).toNat ≥
          mem.size
        ∨ (UInt256.land (UInt256.shiftRight sigmaRound3Word ⟨51⟩) ⟨480⟩ + ⟨640⟩) ≥
          (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding
        (UInt256.land (UInt256.shiftRight sigmaRound3Word ⟨51⟩) ⟨480⟩ + ⟨640⟩).toNat 32))) =
      round3M9Load mem := by
  rw [sigmaRound3Offset1]
  unfold round3M9Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨928⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem round3Mix0ArgsFromGuardGas {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {startGas : Nat}
    (hmem : mem.size = 1984)
    (hprefix :
      ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨1445⟩
        [⟨3⟩, ⟨640⟩, UInt256.shiftRight (inputFirstWord I) ⟨224⟩,
          ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
        mem (UInt256.ofNat 62) ByteArray.empty (cA, σ) k startGas) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1512⟩
      [round3M9Arg mem, round3M7Arg mem, ⟨1693⟩,
        sigmaRound3Word, ⟨3109⟩, ⟨3292⟩, ⟨3⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      mem (UInt256.ofNat 62) ByteArray.empty (cA, σ) k (startGas + 234) := by
  obtain ⟨k0, rd1445⟩ := hprefix
  have hmloadM7 := round3SelectorMloadM7 hmem
  have hmloadM9 := round3SelectorMloadM9 hmem
  have rd1512 := evm_run rd1445 with [
    raw jumpdest (by decide) (by evm_ov),
    dup1,
    push2 ⟨3292⟩,
    push2 ⟨3109⟩,
    push2 ⟨1466⟩,
    push1 ⟨10⟩,
    push1 ⟨1⟩,
    swap6,
    mod,
    push2 ⟨946⟩,
    jump (by jump_dest),
    raw jumpdest (by decide) (by evm_ov),
    dup1,
    iszero,
    push2 ⟨1141⟩,
    jumpiNT (by native_decide),
    dup1,
    push1 ⟨1⟩,
    eq,
    push2 ⟨1128⟩,
    jumpiNT (by native_decide),
    dup1,
    push1 ⟨2⟩,
    eq,
    push2 ⟨1115⟩,
    jumpiNT (by native_decide),
    dup1,
    push1 ⟨3⟩,
    eq,
    push2 ⟨1102⟩,
    jumpiT (by native_decide) (by jump_dest),
    raw jumpdest (by decide) (by evm_ov),
    pop,
    push8 sigmaRound3Word,
    swap1,
    jump (by jump_dest),
    raw jumpdest (by decide) (by evm_ov),
    push2 ⟨1693⟩,
    push2 ⟨1512⟩,
    dup3,
    dup9,
    push8 ⟨18446744073709551615⟩,
    swap1,
    swap3,
    swap2,
    swap3,
    push2 ⟨480⟩,
    dup3,
    dup2,
    dup7,
    push1 ⟨55⟩,
    shr,
    and,
    dup4,
    add,
    raw mload 0 (round3M7Load mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmloadM7
      (by native_decide) (by evm_ov),
    and,
    swap5,
    push1 ⟨51⟩,
    shr,
    and,
    add,
    raw mload 0 (round3M9Load mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmloadM9
      (by native_decide) (by evm_ov),
    and,
    swap1,
    jump (by jump_dest) ]
  exact ⟨_, by simpa [sigmaRound3Word, u64MaskWord, round3M7Arg, round3M9Arg,
    Nat.add_assoc] using rd1512⟩

def round2DoneZeroMem (I : ExecutionEnv) : ByteArray :=
  round2Mix7Mem3 (round2Mix6ZeroMem I)

def round2DoneOneMem (I : ExecutionEnv) : ByteArray :=
  round2Mix7Mem3 (round2Mix6OneMem I)

theorem round2DoneZeroMem_size {I : ExecutionEnv} (hlen : I.calldata.size = 213) :
    (round2DoneZeroMem I).size = 1984 := by
  unfold round2DoneZeroMem
  exact round2Mix7Mem3_size (round2Mix6ZeroMem_size hlen)

theorem round2DoneOneMem_size {I : ExecutionEnv} (hlen : I.calldata.size = 213) :
    (round2DoneOneMem I).size = 1984 := by
  unfold round2DoneOneMem
  exact round2Mix7Mem3_size (round2Mix6OneMem_size hlen)

/-- Final-flag-`0`, at least four rounds: the first round-3 `mixG` call is prepared. -/
theorem validPositiveRound3Mix0ArgsZeroFlagPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlen : I.calldata.size = 213)
    (hbyte : I.calldata[212]! = 0)
    (hpos : UInt256.lt ⟨0⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont1 : UInt256.lt ⟨1⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont2 : UInt256.lt ⟨2⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont3 : UInt256.lt ⟨3⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1512⟩
      [round3M9Arg (round2DoneZeroMem I),
        round3M7Arg (round2DoneZeroMem I),
        ⟨1693⟩, sigmaRound3Word, ⟨3109⟩, ⟨3292⟩, ⟨3⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (round2DoneZeroMem I)
      (UInt256.ofNat 62) ByteArray.empty (cA, σ) k 18163 := by
  have hprefix := validPositiveRound3GuardContinueZeroFlagPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hbyte hpos hcont1 hcont2 hcont3
  simpa using round3Mix0ArgsFromGuardGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (mem := round2DoneZeroMem I)
    (startGas := 17929)
    (round2DoneZeroMem_size hlen)
    hprefix

/-- Final-flag-`1`, at least four rounds: the first round-3 `mixG` call is prepared. -/
theorem validPositiveRound3Mix0ArgsOneFlagPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlen : I.calldata.size = 213)
    (hbyte : I.calldata[212]! = 1)
    (hpos : UInt256.lt ⟨0⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont1 : UInt256.lt ⟨1⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont2 : UInt256.lt ⟨2⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont3 : UInt256.lt ⟨3⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1512⟩
      [round3M9Arg (round2DoneOneMem I),
        round3M7Arg (round2DoneOneMem I),
        ⟨1693⟩, sigmaRound3Word, ⟨3109⟩, ⟨3292⟩, ⟨3⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (round2DoneOneMem I)
      (UInt256.ofNat 62) ByteArray.empty (cA, σ) k 18190 := by
  have hprefix := validPositiveRound3GuardContinueOneFlagPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hbyte hpos hcont1 hcont2 hcont3
  simpa using round3Mix0ArgsFromGuardGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (mem := round2DoneOneMem I)
    (startGas := 17956)
    (round2DoneOneMem_size hlen)
    hprefix

end Blake2f
