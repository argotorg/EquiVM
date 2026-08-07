import Examples.Precompiles.Blake2f.Fallback.PositiveRounds.Round2

/-!
# BLAKE2F fallback positive-round traces: loop-index-3 guard

This module splits the rounds-loop guard after round 2. At PC `1370` the loop index is `3`, so
the guard tests `3 < rounds`: false exits the compression loop at PC `1378`, true enters the next
round body at PC `1445`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

private theorem round3GuardExitFromRound2Gas {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {startGas : Nat}
    (hcond : UInt256.lt ⟨3⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) = ⟨0⟩)
    (hprefix :
      ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨1370⟩
        [⟨3⟩, ⟨640⟩, UInt256.shiftRight (inputFirstWord I) ⟨224⟩,
          ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
        mem (UInt256.ofNat 62) ByteArray.empty (cA, σ) k startGas) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1378⟩
      [⟨3⟩, ⟨640⟩, UInt256.shiftRight (inputFirstWord I) ⟨224⟩,
        ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      mem (UInt256.ofNat 62) ByteArray.empty (cA, σ) k (startGas + 23) := by
  obtain ⟨k0, rd1370⟩ := hprefix
  have rd1378 := evm_run rd1370 with [
    raw jumpdest (by decide) (by evm_ov),
    dup3,
    dup2,
    lt,
    push2 ⟨1445⟩,
    jumpiNT hcond ]
  exact ⟨_, by simpa [Nat.add_assoc] using rd1378⟩

private theorem round3GuardContinueFromRound2Gas {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {startGas : Nat}
    (hcond : UInt256.lt ⟨3⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hprefix :
      ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨1370⟩
        [⟨3⟩, ⟨640⟩, UInt256.shiftRight (inputFirstWord I) ⟨224⟩,
          ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
        mem (UInt256.ofNat 62) ByteArray.empty (cA, σ) k startGas) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1445⟩
      [⟨3⟩, ⟨640⟩, UInt256.shiftRight (inputFirstWord I) ⟨224⟩,
        ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      mem (UInt256.ofNat 62) ByteArray.empty (cA, σ) k (startGas + 23) := by
  obtain ⟨k0, rd1370⟩ := hprefix
  have rd1445 := evm_run rd1370 with [
    raw jumpdest (by decide) (by evm_ov),
    dup3,
    dup2,
    lt,
    push2 ⟨1445⟩,
    jumpiT hcond (by jump_dest) ]
  exact ⟨_, by simpa [Nat.add_assoc] using rd1445⟩

/-- Final-flag-`0`, exactly three rounds: after round 2, the rounds guard exits at PC `1378`. -/
theorem validPositiveRound3GuardExitZeroFlagPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlen : I.calldata.size = 213)
    (hbyte : I.calldata[212]! = 0)
    (hpos : UInt256.lt ⟨0⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont1 : UInt256.lt ⟨1⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont2 : UInt256.lt ⟨2⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hexit : UInt256.lt ⟨3⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) = ⟨0⟩) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1378⟩
      [⟨3⟩, ⟨640⟩, UInt256.shiftRight (inputFirstWord I) ⟨224⟩,
        ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (round2Mix7Mem3 (round2Mix6ZeroMem I))
      (UInt256.ofNat 62) ByteArray.empty (cA, σ) k 17929 := by
  have hprefix := validPositiveRound2DoneZeroFlagPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hbyte hpos hcont1 hcont2
  exact round3GuardExitFromRound2Gas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (mem := round2Mix7Mem3 (round2Mix6ZeroMem I))
    (startGas := 17906)
    hexit hprefix

/-- Final-flag-`1`, exactly three rounds: after round 2, the rounds guard exits at PC `1378`. -/
theorem validPositiveRound3GuardExitOneFlagPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlen : I.calldata.size = 213)
    (hbyte : I.calldata[212]! = 1)
    (hpos : UInt256.lt ⟨0⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont1 : UInt256.lt ⟨1⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont2 : UInt256.lt ⟨2⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hexit : UInt256.lt ⟨3⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) = ⟨0⟩) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1378⟩
      [⟨3⟩, ⟨640⟩, UInt256.shiftRight (inputFirstWord I) ⟨224⟩,
        ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (round2Mix7Mem3 (round2Mix6OneMem I))
      (UInt256.ofNat 62) ByteArray.empty (cA, σ) k 17956 := by
  have hprefix := validPositiveRound2DoneOneFlagPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hbyte hpos hcont1 hcont2
  exact round3GuardExitFromRound2Gas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (mem := round2Mix7Mem3 (round2Mix6OneMem I))
    (startGas := 17933)
    hexit hprefix

/-- Final-flag-`0`, at least four rounds: after round 2, the next body starts at PC `1445`. -/
theorem validPositiveRound3GuardContinueZeroFlagPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlen : I.calldata.size = 213)
    (hbyte : I.calldata[212]! = 0)
    (hpos : UInt256.lt ⟨0⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont1 : UInt256.lt ⟨1⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont2 : UInt256.lt ⟨2⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont3 : UInt256.lt ⟨3⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1445⟩
      [⟨3⟩, ⟨640⟩, UInt256.shiftRight (inputFirstWord I) ⟨224⟩,
        ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (round2Mix7Mem3 (round2Mix6ZeroMem I))
      (UInt256.ofNat 62) ByteArray.empty (cA, σ) k 17929 := by
  have hprefix := validPositiveRound2DoneZeroFlagPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hbyte hpos hcont1 hcont2
  exact round3GuardContinueFromRound2Gas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (mem := round2Mix7Mem3 (round2Mix6ZeroMem I))
    (startGas := 17906)
    hcont3 hprefix

/-- Final-flag-`1`, at least four rounds: after round 2, the next body starts at PC `1445`. -/
theorem validPositiveRound3GuardContinueOneFlagPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlen : I.calldata.size = 213)
    (hbyte : I.calldata[212]! = 1)
    (hpos : UInt256.lt ⟨0⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont1 : UInt256.lt ⟨1⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont2 : UInt256.lt ⟨2⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont3 : UInt256.lt ⟨3⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1445⟩
      [⟨3⟩, ⟨640⟩, UInt256.shiftRight (inputFirstWord I) ⟨224⟩,
        ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (round2Mix7Mem3 (round2Mix6OneMem I))
      (UInt256.ofNat 62) ByteArray.empty (cA, σ) k 17956 := by
  have hprefix := validPositiveRound2DoneOneFlagPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hbyte hpos hcont1 hcont2
  exact round3GuardContinueFromRound2Gas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (mem := round2Mix7Mem3 (round2Mix6OneMem I))
    (startGas := 17933)
    hcont3 hprefix

end Blake2f
