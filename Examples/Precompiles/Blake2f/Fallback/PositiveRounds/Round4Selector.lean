import Examples.Precompiles.Blake2f.Fallback.PositiveRounds.Guard4

/-!
# BLAKE2F fallback positive-round traces: round-4 SIGMA selector

This module starts the fifth compression round on the path with at least five rounds. From
PC `1445` with loop index `4`, the bytecode computes `4 % 10`, selects packed SIGMA word
`0x905724afe1bc683d`, loads message words `m[9]` and `m[0]`, and jumps to the first shared
`mixG` body at PC `1512`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

/-- The compiled selector's packed SIGMA word for round `4`. -/
abbrev sigmaRound4Word : UInt256 :=
  ⟨10400822202260547645⟩

/-- Round-4 SIGMA index `0` selects bytecode memory offset `928`, i.e. `m[9]`. -/
theorem sigmaRound4Offset0 : ⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound4Word ⟨55⟩)
    ⟨480⟩ = (⟨928⟩ : UInt256) := by
  native_decide

/-- Round-4 SIGMA index `1` selects bytecode memory offset `640`, i.e. `m[0]`. -/
theorem sigmaRound4Offset1 : UInt256.land (UInt256.shiftRight sigmaRound4Word ⟨51⟩)
    ⟨480⟩ + ⟨640⟩ = (⟨640⟩ : UInt256) := by
  native_decide

abbrev round4M9Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 928 32))

abbrev round4M0Load (mem : ByteArray) : UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding 640 32))

abbrev round4M9Arg (mem : ByteArray) : UInt256 :=
  UInt256.land (round4M9Load mem) u64MaskWord

abbrev round4M0Arg (mem : ByteArray) : UInt256 :=
  UInt256.land (round4M0Load mem) u64MaskWord

private theorem round4SelectorMloadM9 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound4Word ⟨55⟩) ⟨480⟩).toNat ≥
          mem.size
        ∨ (⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound4Word ⟨55⟩) ⟨480⟩) ≥
          (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding
        (⟨640⟩ + UInt256.land (UInt256.shiftRight sigmaRound4Word ⟨55⟩) ⟨480⟩).toNat 32))) =
      round4M9Load mem := by
  rw [sigmaRound4Offset0]
  unfold round4M9Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨928⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem round4SelectorMloadM0 {mem : ByteArray} (hmem : mem.size = 1984) :
    (if (UInt256.land (UInt256.shiftRight sigmaRound4Word ⟨51⟩) ⟨480⟩ + ⟨640⟩).toNat ≥
          mem.size
        ∨ (UInt256.land (UInt256.shiftRight sigmaRound4Word ⟨51⟩) ⟨480⟩ + ⟨640⟩) ≥
          (UInt256.ofNat 62) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding
        (UInt256.land (UInt256.shiftRight sigmaRound4Word ⟨51⟩) ⟨480⟩ + ⟨640⟩).toNat 32))) =
      round4M0Load mem := by
  rw [sigmaRound4Offset1]
  unfold round4M0Load
  exact mloadValue_eq_readWithPadding_of_lt_size
    (mem := mem) (aw := UInt256.ofNat 62) (off := (⟨640⟩ : UInt256))
    (memSize := 1984) hmem (by decide) (by decide)

private theorem round4Mix0ArgsFromGuardGas {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {startGas : Nat}
    (hmem : mem.size = 1984)
    (hprefix :
      ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨1445⟩
        [⟨4⟩, ⟨640⟩, UInt256.shiftRight (inputFirstWord I) ⟨224⟩,
          ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
        mem (UInt256.ofNat 62) ByteArray.empty (cA, σ) k startGas) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1512⟩
      [round4M0Arg mem, round4M9Arg mem, ⟨1693⟩,
        sigmaRound4Word, ⟨3109⟩, ⟨3292⟩, ⟨4⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      mem (UInt256.ofNat 62) ByteArray.empty (cA, σ) k (startGas + 256) := by
  obtain ⟨k0, rd1445⟩ := hprefix
  have hmloadM9 := round4SelectorMloadM9 hmem
  have hmloadM0 := round4SelectorMloadM0 hmem
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
    jumpiT (by native_decide) (by jump_dest),
    raw jumpdest (by decide) (by evm_ov),
    pop,
    push8 sigmaRound4Word,
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
    raw mload 0 (round4M9Load mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmloadM9
      (by native_decide) (by evm_ov),
    and,
    swap5,
    push1 ⟨51⟩,
    shr,
    and,
    add,
    raw mload 0 (round4M0Load mem) (UInt256.ofNat 62)
      (by decide)
      (by
        intro s haw hstk
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk]
        native_decide)
      hmloadM0
      (by native_decide) (by evm_ov),
    and,
    swap1,
    jump (by jump_dest) ]
  exact ⟨_, by simpa [sigmaRound4Word, u64MaskWord, round4M9Arg, round4M0Arg,
    Nat.add_assoc] using rd1512⟩

def round3DoneZeroMem (I : ExecutionEnv) : ByteArray :=
  round3Mix7Mem3 (round3Mix6ZeroMem I)

def round3DoneOneMem (I : ExecutionEnv) : ByteArray :=
  round3Mix7Mem3 (round3Mix6OneMem I)

theorem round3DoneZeroMem_size {I : ExecutionEnv} (hlen : I.calldata.size = 213) :
    (round3DoneZeroMem I).size = 1984 := by
  unfold round3DoneZeroMem
  exact round3Mix7Mem3_size (round3Mix6ZeroMem_size hlen)

theorem round3DoneOneMem_size {I : ExecutionEnv} (hlen : I.calldata.size = 213) :
    (round3DoneOneMem I).size = 1984 := by
  unfold round3DoneOneMem
  exact round3Mix7Mem3_size (round3Mix6OneMem_size hlen)

/-- Final-flag-`0`, at least five rounds: the first round-4 `mixG` call is prepared. -/
theorem validPositiveRound4Mix0ArgsZeroFlagPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlen : I.calldata.size = 213)
    (hbyte : I.calldata[212]! = 0)
    (hpos : UInt256.lt ⟨0⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont1 : UInt256.lt ⟨1⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont2 : UInt256.lt ⟨2⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont3 : UInt256.lt ⟨3⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont4 : UInt256.lt ⟨4⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1512⟩
      [round4M0Arg (round3DoneZeroMem I),
        round4M9Arg (round3DoneZeroMem I),
        ⟨1693⟩, sigmaRound4Word, ⟨3109⟩, ⟨3292⟩, ⟨4⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (round3DoneZeroMem I)
      (UInt256.ofNat 62) ByteArray.empty (cA, σ) k 21652 := by
  have hprefix := validPositiveRound4GuardContinueZeroFlagPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hbyte hpos hcont1 hcont2 hcont3 hcont4
  simpa using round4Mix0ArgsFromGuardGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (mem := round3DoneZeroMem I)
    (startGas := 21396)
    (round3DoneZeroMem_size hlen)
    hprefix

/-- Final-flag-`1`, at least five rounds: the first round-4 `mixG` call is prepared. -/
theorem validPositiveRound4Mix0ArgsOneFlagPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlen : I.calldata.size = 213)
    (hbyte : I.calldata[212]! = 1)
    (hpos : UInt256.lt ⟨0⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont1 : UInt256.lt ⟨1⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont2 : UInt256.lt ⟨2⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont3 : UInt256.lt ⟨3⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont4 : UInt256.lt ⟨4⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1512⟩
      [round4M0Arg (round3DoneOneMem I),
        round4M9Arg (round3DoneOneMem I),
        ⟨1693⟩, sigmaRound4Word, ⟨3109⟩, ⟨3292⟩, ⟨4⟩, ⟨1⟩, ⟨640⟩,
        UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (round3DoneOneMem I)
      (UInt256.ofNat 62) ByteArray.empty (cA, σ) k 21679 := by
  have hprefix := validPositiveRound4GuardContinueOneFlagPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hbyte hpos hcont1 hcont2 hcont3 hcont4
  simpa using round4Mix0ArgsFromGuardGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (mem := round3DoneOneMem I)
    (startGas := 21423)
    (round3DoneOneMem_size hlen)
    hprefix

end Blake2f
