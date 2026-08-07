import Examples.Precompiles.Blake2f.Fallback.PositiveRounds.Round5

/-!
# BLAKE2F fallback positive-round traces: loop-index-6 guard

This module splits the rounds-loop guard after round 5. At PC `1370` the loop index is `6`, so
the guard tests `6 < rounds`: false exits the compression loop at PC `1378`, true enters the next
round body at PC `1445`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

private theorem round6GuardExitFromRound5Gas {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {startGas : Nat}
    (hcond : UInt256.lt ⟨6⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) = ⟨0⟩)
    (hprefix :
      ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨1370⟩
        [⟨6⟩, ⟨640⟩, UInt256.shiftRight (inputFirstWord I) ⟨224⟩,
          ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
        mem (UInt256.ofNat 62) ByteArray.empty (cA, σ) k startGas) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1378⟩
      [⟨6⟩, ⟨640⟩, UInt256.shiftRight (inputFirstWord I) ⟨224⟩,
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

private theorem round6GuardContinueFromRound5Gas {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {startGas : Nat}
    (hcond : UInt256.lt ⟨6⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hprefix :
      ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨1370⟩
        [⟨6⟩, ⟨640⟩, UInt256.shiftRight (inputFirstWord I) ⟨224⟩,
          ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
        mem (UInt256.ofNat 62) ByteArray.empty (cA, σ) k startGas) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1445⟩
      [⟨6⟩, ⟨640⟩, UInt256.shiftRight (inputFirstWord I) ⟨224⟩,
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

/-- Final-flag-`0`, exactly six rounds: after round 5, the rounds guard exits at PC `1378`. -/
theorem validPositiveRound6GuardExitZeroFlagPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
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
    (hexit : UInt256.lt ⟨6⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) = ⟨0⟩) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1378⟩
      [⟨6⟩, ⟨640⟩, UInt256.shiftRight (inputFirstWord I) ⟨224⟩,
        ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (round5Mix7Mem3 (round5Mix6ZeroMem I))
      (UInt256.ofNat 62) ByteArray.empty (cA, σ) k 28396 := by
  have hprefix := validPositiveRound5DoneZeroFlagPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hbyte hpos hcont1 hcont2 hcont3 hcont4 hcont5
  exact round6GuardExitFromRound5Gas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (mem := round5Mix7Mem3 (round5Mix6ZeroMem I))
    (startGas := 28373)
    hexit hprefix

/-- Final-flag-`1`, exactly six rounds: after round 5, the rounds guard exits at PC `1378`. -/
theorem validPositiveRound6GuardExitOneFlagPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
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
    (hexit : UInt256.lt ⟨6⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) = ⟨0⟩) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1378⟩
      [⟨6⟩, ⟨640⟩, UInt256.shiftRight (inputFirstWord I) ⟨224⟩,
        ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (round5Mix7Mem3 (round5Mix6OneMem I))
      (UInt256.ofNat 62) ByteArray.empty (cA, σ) k 28423 := by
  have hprefix := validPositiveRound5DoneOneFlagPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hbyte hpos hcont1 hcont2 hcont3 hcont4 hcont5
  exact round6GuardExitFromRound5Gas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (mem := round5Mix7Mem3 (round5Mix6OneMem I))
    (startGas := 28400)
    hexit hprefix

/-- Final-flag-`0`, at least seven rounds: after round 5, the next body starts at PC `1445`. -/
theorem validPositiveRound6GuardContinueZeroFlagPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
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
      ⟨1445⟩
      [⟨6⟩, ⟨640⟩, UInt256.shiftRight (inputFirstWord I) ⟨224⟩,
        ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (round5Mix7Mem3 (round5Mix6ZeroMem I))
      (UInt256.ofNat 62) ByteArray.empty (cA, σ) k 28396 := by
  have hprefix := validPositiveRound5DoneZeroFlagPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hbyte hpos hcont1 hcont2 hcont3 hcont4 hcont5
  exact round6GuardContinueFromRound5Gas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (mem := round5Mix7Mem3 (round5Mix6ZeroMem I))
    (startGas := 28373)
    hcont6 hprefix

/-- Final-flag-`1`, at least seven rounds: after round 5, the next body starts at PC `1445`. -/
theorem validPositiveRound6GuardContinueOneFlagPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
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
      ⟨1445⟩
      [⟨6⟩, ⟨640⟩, UInt256.shiftRight (inputFirstWord I) ⟨224⟩,
        ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (round5Mix7Mem3 (round5Mix6OneMem I))
      (UInt256.ofNat 62) ByteArray.empty (cA, σ) k 28423 := by
  have hprefix := validPositiveRound5DoneOneFlagPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hbyte hpos hcont1 hcont2 hcont3 hcont4 hcont5
  exact round6GuardContinueFromRound5Gas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (mem := round5Mix7Mem3 (round5Mix6OneMem I))
    (startGas := 28400)
    hcont6 hprefix

end Blake2f
