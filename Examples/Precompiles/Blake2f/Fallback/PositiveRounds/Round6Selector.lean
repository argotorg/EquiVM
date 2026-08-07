import Examples.Precompiles.Blake2f.Fallback.PositiveRounds.Guard6

/-!
# BLAKE2F fallback positive-round traces: round-6 SIGMA selector

This module starts the seventh compression round on the path with at least seven rounds. From
PC `1445` with loop index `6`, the bytecode computes `6 % 10`, selects packed SIGMA word
`0xc51fed4a0763928b`, loads message words `m[12]` and `m[5]`, and jumps to the first shared
`mixG` body at PC `1512`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

/-- The compiled selector's packed SIGMA word for round `6`. -/
abbrev sigmaRound6Word : UInt256 :=
  ⟨14204332651957162635⟩

/-- Round-6 SIGMA index `0` selects bytecode memory offset `1024`, i.e. `m[12]`. -/
theorem sigmaRound6Offset0 : ⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound6Word ⟨55⟩)
    ⟨480⟩ = (⟨1024⟩ : UInt256) := by
  native_decide

/-- Round-6 SIGMA index `1` selects bytecode memory offset `800`, i.e. `m[5]`. -/
theorem sigmaRound6Offset1 : UInt256.land (UInt256.shiftRight sigmaRound6Word ⟨51⟩)
    ⟨480⟩ + ⟨640⟩ = (⟨800⟩ : UInt256) := by
  native_decide

abbrev round6M12Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 1024 32))

abbrev round6M5Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 800 32))

abbrev round6M12Arg (mem : ByteArray) : UInt256 :=
  UInt256.land (round6M12Load mem) u64MaskWord

abbrev round6M5Arg (mem : ByteArray) : UInt256 :=
  UInt256.land (round6M5Load mem) u64MaskWord

private theorem round6SelectorMloadM12 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound6Word ⟨55⟩) ⟨480⟩).toNat ≥
          mem.size
        ∨ (⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound6Word ⟨55⟩) ⟨480⟩) ≥
          (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding
        (⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound6Word ⟨55⟩) ⟨480⟩).toNat 32))) =
      round6M12Load mem := by
  rw [sigmaRound6Offset0]
  unfold round6M12Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨1024⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem round6SelectorMloadM5 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (UInt256.land (UInt256.shiftRight sigmaRound6Word ⟨51⟩) ⟨480⟩ + ⟨640⟩).toNat ≥
          mem.size
        ∨ (UInt256.land (UInt256.shiftRight sigmaRound6Word ⟨51⟩) ⟨480⟩ + ⟨640⟩) ≥
          (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding
        (UInt256.land (UInt256.shiftRight sigmaRound6Word ⟨51⟩) ⟨480⟩ + ⟨640⟩).toNat 32))) =
      round6M5Load mem := by
  rw [sigmaRound6Offset1]
  unfold round6M5Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨800⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem round6Mix0ArgsFromGuardGas {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {startGas : Nat}
    (hmem : mem.size = 1984)
    (hprefix :
      ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨1445⟩
        [⟨6⟩, ⟨640⟩, UInt256.shiftRight (inputFirstWord I) ⟨224⟩,
          ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
        mem (UInt256.ofNat 62) ByteArray.empty (cA, σ) k startGas) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1512⟩
      [round6M5Arg mem, round6M12Arg mem, ⟨1693⟩,
        sigmaRound6Word, ⟨3109⟩, ⟨3292⟩, ⟨6⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      mem (UInt256.ofNat 62) ByteArray.empty (cA, σ) k (startGas + 300) := by
  obtain ⟨k0, rd1445⟩ := hprefix
  have hmloadM12 := round6SelectorMloadM12 hmem
  have hmloadM5 := round6SelectorMloadM5 hmem
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
    jumpiNT (by native_decide),
    dup1,
    push1 ⟨6⟩,
    eq,
    push2 ⟨1063⟩,
    jumpiT (by native_decide) (by jump_dest),
    raw jumpdest (by decide) (by evm_ov),
    pop,
    push8 sigmaRound6Word,
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
    raw mload 0 (round6M12Load mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmloadM12
      (by native_decide) (by evm_ov),
    and,
    swap5,
    push1 ⟨51⟩,
    shr,
    and,
    add,
    raw mload 0 (round6M5Load mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmloadM5
      (by native_decide) (by evm_ov),
    and,
    swap1,
    jump (by jump_dest) ]
  exact ⟨_, by simpa [sigmaRound6Word, u64MaskWord, round6M12Arg, round6M5Arg,
    Nat.add_assoc] using rd1512⟩

def round5DoneZeroMem (I : ExecutionEnv) : ByteArray :=
  round5Mix7Mem3 (round5Mix6ZeroMem I)

def round5DoneOneMem (I : ExecutionEnv) : ByteArray :=
  round5Mix7Mem3 (round5Mix6OneMem I)

theorem round5DoneZeroMem_size {I : ExecutionEnv} (hlen : I.calldata.size = 213) :
    (round5DoneZeroMem I).size = 1984 := by
  unfold round5DoneZeroMem
  exact round5Mix7Mem3_size (round5Mix6ZeroMem_size hlen)

theorem round5DoneOneMem_size {I : ExecutionEnv} (hlen : I.calldata.size = 213) :
    (round5DoneOneMem I).size = 1984 := by
  unfold round5DoneOneMem
  exact round5Mix7Mem3_size (round5Mix6OneMem_size hlen)

/-- Final-flag-`0`, at least seven rounds: the first round-6 `mixG` call is prepared. -/
theorem validPositiveRound6Mix0ArgsZeroFlagPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlen : I.calldata.size = 213)
    (hbyte : I.calldata[212]! = 0)
    (hpos : UInt256.lt ⟨0⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont1 : UInt256.lt ⟨1⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont2 : UInt256.lt ⟨2⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont3 : UInt256.lt ⟨3⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont4 : UInt256.lt ⟨4⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont5 : UInt256.lt ⟨5⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont6 : UInt256.lt ⟨6⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1512⟩
      [round6M5Arg (round5DoneZeroMem I),
        round6M12Arg (round5DoneZeroMem I),
        ⟨1693⟩, sigmaRound6Word, ⟨3109⟩, ⟨3292⟩, ⟨6⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (round5DoneZeroMem I)
      (UInt256.ofNat 62) ByteArray.empty (cA, σ) k 28696 := by
  have hprefix := validPositiveRound6GuardContinueZeroFlagPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hbyte hpos hcont1 hcont2 hcont3 hcont4 hcont5 hcont6
  simpa using round6Mix0ArgsFromGuardGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (mem := round5DoneZeroMem I)
    (startGas := 28396)
    (round5DoneZeroMem_size hlen)
    hprefix

/-- Final-flag-`1`, at least seven rounds: the first round-6 `mixG` call is prepared. -/
theorem validPositiveRound6Mix0ArgsOneFlagPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlen : I.calldata.size = 213)
    (hbyte : I.calldata[212]! = 1)
    (hpos : UInt256.lt ⟨0⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont1 : UInt256.lt ⟨1⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont2 : UInt256.lt ⟨2⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont3 : UInt256.lt ⟨3⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont4 : UInt256.lt ⟨4⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont5 : UInt256.lt ⟨5⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont6 : UInt256.lt ⟨6⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1512⟩
      [round6M5Arg (round5DoneOneMem I),
        round6M12Arg (round5DoneOneMem I),
        ⟨1693⟩, sigmaRound6Word, ⟨3109⟩, ⟨3292⟩, ⟨6⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (round5DoneOneMem I)
      (UInt256.ofNat 62) ByteArray.empty (cA, σ) k 28723 := by
  have hprefix := validPositiveRound6GuardContinueOneFlagPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hbyte hpos hcont1 hcont2 hcont3 hcont4 hcont5 hcont6
  simpa using round6Mix0ArgsFromGuardGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (mem := round5DoneOneMem I)
    (startGas := 28423)
    (round5DoneOneMem_size hlen)
    hprefix

end Blake2f
