import Examples.Precompiles.Blake2f.Fallback.PositiveRounds.Guard2

/-!
# BLAKE2F fallback positive-round traces: round-2 SIGMA selector

This module starts the third compression round on the path with at least three rounds.  From
PC `1445` with loop index `2`, the bytecode computes `2 % 10`, selects packed SIGMA word
`0xb8c052fdae367194`, loads message words `m[11]` and `m[8]`, and jumps to the first shared
`mixG` body at PC `1512`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

/-- The compiled selector's packed SIGMA word for round `2`. -/
abbrev sigmaRound2Word : UInt256 :=
  ⟨13312731748010193300⟩

/-- Round-2 SIGMA index `0` selects bytecode memory offset `992`, i.e. `m[11]`. -/
theorem sigmaRound2Offset0 : ⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound2Word ⟨55⟩)
    ⟨480⟩ = (⟨992⟩ : UInt256) := by
  native_decide

/-- Round-2 SIGMA index `1` selects bytecode memory offset `896`, i.e. `m[8]`. -/
theorem sigmaRound2Offset1 : UInt256.land (UInt256.shiftRight sigmaRound2Word ⟨51⟩)
    ⟨480⟩ + ⟨640⟩ = (⟨896⟩ : UInt256) := by
  native_decide

abbrev round2M11Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 992 32))

abbrev round2M8Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 896 32))

abbrev round2M11Arg (mem : ByteArray) : UInt256 :=
  UInt256.land (round2M11Load mem) u64MaskWord

abbrev round2M8Arg (mem : ByteArray) : UInt256 :=
  UInt256.land (round2M8Load mem) u64MaskWord

private theorem round2SelectorMloadM11 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound2Word ⟨55⟩) ⟨480⟩).toNat ≥
          mem.size
        ∨ (⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound2Word ⟨55⟩) ⟨480⟩) ≥
          (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding
        (⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound2Word ⟨55⟩) ⟨480⟩).toNat 32))) =
      round2M11Load mem := by
  rw [sigmaRound2Offset0]
  unfold round2M11Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨992⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem round2SelectorMloadM8 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (UInt256.land (UInt256.shiftRight sigmaRound2Word ⟨51⟩) ⟨480⟩ + ⟨640⟩).toNat ≥
          mem.size
        ∨ (UInt256.land (UInt256.shiftRight sigmaRound2Word ⟨51⟩) ⟨480⟩ + ⟨640⟩) ≥
          (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding
        (UInt256.land (UInt256.shiftRight sigmaRound2Word ⟨51⟩) ⟨480⟩ + ⟨640⟩).toNat 32))) =
      round2M8Load mem := by
  rw [sigmaRound2Offset1]
  unfold round2M8Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨896⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem round2Mix0ArgsFromGuardGas {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {startGas : Nat}
    (hmem : mem.size = 1984)
    (hprefix :
      ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨1445⟩
        [⟨2⟩, ⟨640⟩, UInt256.shiftRight (inputFirstWord I) ⟨224⟩,
          ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
        mem (UInt256.ofNat 62) ByteArray.empty (cA, σ) k startGas) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1512⟩
      [round2M8Arg mem, round2M11Arg mem, ⟨1693⟩,
        sigmaRound2Word, ⟨3109⟩, ⟨3292⟩, ⟨2⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      mem (UInt256.ofNat 62) ByteArray.empty (cA, σ) k (startGas + 212) := by
  obtain ⟨k0, rd1445⟩ := hprefix
  have hmloadM11 := round2SelectorMloadM11 hmem
  have hmloadM8 := round2SelectorMloadM8 hmem
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
    jumpiT (by native_decide) (by jump_dest),
    raw jumpdest (by decide) (by evm_ov),
    pop,
    push8 sigmaRound2Word,
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
    raw mload 0 (round2M11Load mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmloadM11
      (by native_decide) (by evm_ov),
    and,
    swap5,
    push1 ⟨51⟩,
    shr,
    and,
    add,
    raw mload 0 (round2M8Load mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmloadM8
      (by native_decide) (by evm_ov),
    and,
    swap1,
    jump (by jump_dest) ]
  exact ⟨_, by simpa [sigmaRound2Word, u64MaskWord, round2M11Arg, round2M8Arg,
    Nat.add_assoc] using rd1512⟩

def round1DoneZeroMem (I : ExecutionEnv) : ByteArray :=
  round1Mix7Mem3 (round1Mix6ZeroMem I)

def round1DoneOneMem (I : ExecutionEnv) : ByteArray :=
  round1Mix7Mem3 (round1Mix6OneMem I)

theorem round1DoneZeroMem_size {I : ExecutionEnv} (hlen : I.calldata.size = 213) :
    (round1DoneZeroMem I).size = 1984 := by
  unfold round1DoneZeroMem
  exact round1Mix7Mem3_size (round1Mix6ZeroMem_size hlen)

theorem round1DoneOneMem_size {I : ExecutionEnv} (hlen : I.calldata.size = 213) :
    (round1DoneOneMem I).size = 1984 := by
  unfold round1DoneOneMem
  exact round1Mix7Mem3_size (round1Mix6OneMem_size hlen)

/-- Final-flag-`0`, at least three rounds: the first round-2 `mixG` call is prepared. -/
theorem validPositiveRound2Mix0ArgsZeroFlagPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlen : I.calldata.size = 213)
    (hbyte : I.calldata[212]! = 0)
    (hpos : UInt256.lt ⟨0⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont1 : UInt256.lt ⟨1⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont2 : UInt256.lt ⟨2⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1512⟩
      [round2M8Arg (round1DoneZeroMem I),
        round2M11Arg (round1DoneZeroMem I),
        ⟨1693⟩, sigmaRound2Word, ⟨3109⟩, ⟨3292⟩, ⟨2⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (round1DoneZeroMem I)
      (UInt256.ofNat 62) ByteArray.empty (cA, σ) k
      (((((((((13216 + 93) + 321) + 93) + 321) + 84) + 318) + 15) + 23) + 212) := by
  have hprefix := validPositiveRound2GuardContinueZeroFlagPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hbyte hpos hcont1 hcont2
  exact round2Mix0ArgsFromGuardGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (mem := round1DoneZeroMem I)
    (startGas := ((((((((13216 + 93) + 321) + 93) + 321) + 84) + 318) + 15) + 23))
    (round1DoneZeroMem_size hlen)
    hprefix

/-- Final-flag-`1`, at least three rounds: the first round-2 `mixG` call is prepared. -/
theorem validPositiveRound2Mix0ArgsOneFlagPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlen : I.calldata.size = 213)
    (hbyte : I.calldata[212]! = 1)
    (hpos : UInt256.lt ⟨0⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont1 : UInt256.lt ⟨1⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont2 : UInt256.lt ⟨2⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1512⟩
      [round2M8Arg (round1DoneOneMem I),
        round2M11Arg (round1DoneOneMem I),
        ⟨1693⟩, sigmaRound2Word, ⟨3109⟩, ⟨3292⟩, ⟨2⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (round1DoneOneMem I)
      (UInt256.ofNat 62) ByteArray.empty (cA, σ) k
      (((((((((13243 + 93) + 321) + 93) + 321) + 84) + 318) + 15) + 23) + 212) := by
  have hprefix := validPositiveRound2GuardContinueOneFlagPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hbyte hpos hcont1 hcont2
  exact round2Mix0ArgsFromGuardGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (mem := round1DoneOneMem I)
    (startGas := ((((((((13243 + 93) + 321) + 93) + 321) + 84) + 318) + 15) + 23))
    (round1DoneOneMem_size hlen)
    hprefix

end Blake2f
