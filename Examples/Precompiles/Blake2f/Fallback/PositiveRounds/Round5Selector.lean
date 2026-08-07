import Examples.Precompiles.Blake2f.Fallback.PositiveRounds.Guard5

/-!
# BLAKE2F fallback positive-round traces: round-5 SIGMA selector

This module starts the sixth compression round on the path with at least six rounds. From
PC `1445` with loop index `5`, the bytecode computes `5 % 10`, selects packed SIGMA word
`0x2c6a0b834d75fe19`, loads message words `m[2]` and `m[12]`, and jumps to the first shared
`mixG` body at PC `1512`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

/-- The compiled selector's packed SIGMA word for round `5`. -/
abbrev sigmaRound5Word : UInt256 :=
  ⟨3200383143768358425⟩

/-- Round-5 SIGMA index `0` selects bytecode memory offset `704`, i.e. `m[2]`. -/
theorem sigmaRound5Offset0 : ⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound5Word ⟨55⟩)
    ⟨480⟩ = (⟨704⟩ : UInt256) := by
  native_decide

/-- Round-5 SIGMA index `1` selects bytecode memory offset `1024`, i.e. `m[12]`. -/
theorem sigmaRound5Offset1 : UInt256.land (UInt256.shiftRight sigmaRound5Word ⟨51⟩)
    ⟨480⟩ + ⟨640⟩ = (⟨1024⟩ : UInt256) := by
  native_decide

abbrev round5M2Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 704 32))

abbrev round5M12Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1024 32))

abbrev round5M2Arg (mem : ByteArray) : UInt256 :=
  UInt256.land (round5M2Load mem) u64MaskWord

abbrev round5M12Arg (mem : ByteArray) : UInt256 :=
  UInt256.land (round5M12Load mem) u64MaskWord

private theorem round5SelectorMloadM2 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound5Word ⟨55⟩) ⟨480⟩).toNat ≥
          mem.size
        ∨ (⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound5Word ⟨55⟩) ⟨480⟩) ≥
          (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding
        (⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound5Word ⟨55⟩) ⟨480⟩).toNat 32))) =
      round5M2Load mem := by
  rw [sigmaRound5Offset0]
  unfold round5M2Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨704⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem round5SelectorMloadM12 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (UInt256.land (UInt256.shiftRight sigmaRound5Word ⟨51⟩) ⟨480⟩ + ⟨640⟩).toNat ≥
          mem.size
        ∨ (UInt256.land (UInt256.shiftRight sigmaRound5Word ⟨51⟩) ⟨480⟩ + ⟨640⟩) ≥
          (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding
        (UInt256.land (UInt256.shiftRight sigmaRound5Word ⟨51⟩) ⟨480⟩ + ⟨640⟩).toNat 32))) =
      round5M12Load mem := by
  rw [sigmaRound5Offset1]
  unfold round5M12Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨1024⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem round5Mix0ArgsFromGuardGas {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {startGas : Nat}
    (hmem : mem.size = 1984)
    (hprefix :
      ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨1445⟩
        [⟨5⟩, ⟨640⟩, UInt256.shiftRight (inputFirstWord I) ⟨224⟩,
          ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
        mem (UInt256.ofNat 62) ByteArray.empty (cA, σ) k startGas) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1512⟩
      [round5M12Arg mem, round5M2Arg mem, ⟨1693⟩,
        sigmaRound5Word, ⟨3109⟩, ⟨3292⟩, ⟨5⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      mem (UInt256.ofNat 62) ByteArray.empty (cA, σ) k (startGas + 278) := by
  obtain ⟨k0, rd1445⟩ := hprefix
  have hmloadM2 := round5SelectorMloadM2 hmem
  have hmloadM12 := round5SelectorMloadM12 hmem
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
    jumpiNT (by native_decide),
    dup1,
    push1 ⟨4⟩,
    eq,
    push2 ⟨1089⟩,
    jumpiNT (by native_decide),
    dup1,
    push1 ⟨5⟩,
    eq,
    push2 ⟨1076⟩,
    jumpiT (by native_decide) (by jump_dest),
    raw jumpdest (by decide) (by evm_ov),
    pop,
    push8 sigmaRound5Word,
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
    raw mload 0 (round5M2Load mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmloadM2
      (by native_decide) (by evm_ov),
    and,
    swap5,
    push1 ⟨51⟩,
    shr,
    and,
    add,
    raw mload 0 (round5M12Load mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmloadM12
      (by native_decide) (by evm_ov),
    and,
    swap1,
    jump (by jump_dest) ]
  exact ⟨_, by simpa [sigmaRound5Word, u64MaskWord, round5M2Arg, round5M12Arg,
    Nat.add_assoc] using rd1512⟩

def round4DoneZeroMem (I : ExecutionEnv) : ByteArray :=
  round4Mix7Mem3 (round4Mix6ZeroMem I)

def round4DoneOneMem (I : ExecutionEnv) : ByteArray :=
  round4Mix7Mem3 (round4Mix6OneMem I)

theorem round4DoneZeroMem_size {I : ExecutionEnv} (hlen : I.calldata.size = 213) :
    (round4DoneZeroMem I).size = 1984 := by
  unfold round4DoneZeroMem
  exact round4Mix7Mem3_size (round4Mix6ZeroMem_size hlen)

theorem round4DoneOneMem_size {I : ExecutionEnv} (hlen : I.calldata.size = 213) :
    (round4DoneOneMem I).size = 1984 := by
  unfold round4DoneOneMem
  exact round4Mix7Mem3_size (round4Mix6OneMem_size hlen)

/-- Final-flag-`0`, at least six rounds: the first round-5 `mixG` call is prepared. -/
theorem validPositiveRound5Mix0ArgsZeroFlagPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlen : I.calldata.size = 213)
    (hbyte : I.calldata[212]! = 0)
    (hpos : UInt256.lt ⟨0⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont1 : UInt256.lt ⟨1⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont2 : UInt256.lt ⟨2⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont3 : UInt256.lt ⟨3⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont4 : UInt256.lt ⟨4⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont5 : UInt256.lt ⟨5⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1512⟩
      [round5M12Arg (round4DoneZeroMem I),
        round5M2Arg (round4DoneZeroMem I),
        ⟨1693⟩, sigmaRound5Word, ⟨3109⟩, ⟨3292⟩, ⟨5⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (round4DoneZeroMem I)
      (UInt256.ofNat 62) ByteArray.empty (cA, σ) k 25163 := by
  have hprefix := validPositiveRound5GuardContinueZeroFlagPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hbyte hpos hcont1 hcont2 hcont3 hcont4 hcont5
  simpa using round5Mix0ArgsFromGuardGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (mem := round4DoneZeroMem I)
    (startGas := 24885)
    (round4DoneZeroMem_size hlen)
    hprefix

/-- Final-flag-`1`, at least six rounds: the first round-5 `mixG` call is prepared. -/
theorem validPositiveRound5Mix0ArgsOneFlagPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlen : I.calldata.size = 213)
    (hbyte : I.calldata[212]! = 1)
    (hpos : UInt256.lt ⟨0⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont1 : UInt256.lt ⟨1⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont2 : UInt256.lt ⟨2⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont3 : UInt256.lt ⟨3⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont4 : UInt256.lt ⟨4⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont5 : UInt256.lt ⟨5⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1512⟩
      [round5M12Arg (round4DoneOneMem I),
        round5M2Arg (round4DoneOneMem I),
        ⟨1693⟩, sigmaRound5Word, ⟨3109⟩, ⟨3292⟩, ⟨5⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (round4DoneOneMem I)
      (UInt256.ofNat 62) ByteArray.empty (cA, σ) k 25190 := by
  have hprefix := validPositiveRound5GuardContinueOneFlagPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hbyte hpos hcont1 hcont2 hcont3 hcont4 hcont5
  simpa using round5Mix0ArgsFromGuardGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (mem := round4DoneOneMem I)
    (startGas := 24912)
    (round4DoneOneMem_size hlen)
    hprefix

end Blake2f
