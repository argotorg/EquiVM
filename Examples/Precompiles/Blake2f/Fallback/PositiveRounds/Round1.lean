import Examples.Precompiles.Blake2f.Fallback.PositiveRounds.Round1Mix7

/-!
# BLAKE2F fallback positive-round traces: round-1 completion

This module advances from PC `3292`, after all eight round-1 `mixG` calls, through the loop-index
increment and jump back to the rounds-loop guard at PC `1370`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

private theorem round1DoneFromRound1Mix7Gas {cA gh bl σ σ₀ A I} {g : Sat256}
    {mem : ByteArray} {startGas : Nat}
    (hprefix :
      ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨3292⟩
        [⟨1⟩, ⟨1⟩, ⟨640⟩, UInt256.shiftRight (inputFirstWord I) ⟨224⟩,
          ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
        mem (UInt256.ofNat 62) ByteArray.empty (cA, σ) k startGas) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1370⟩
      [⟨2⟩, ⟨640⟩, UInt256.shiftRight (inputFirstWord I) ⟨224⟩,
        ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      mem (UInt256.ofNat 62) ByteArray.empty (cA, σ) k (startGas + 15) := by
  obtain ⟨k0, rd3292⟩ := hprefix
  have rd1370 := evm_run rd3292 with [
    raw jumpdest (by decide) (by evm_ov),
    add,
    push2 ⟨1370⟩,
    jump (by jump_dest) ]
  exact ⟨_, by simpa [Nat.add_assoc] using rd1370⟩

/-- Final-flag-`0`, at least two rounds: round 1 is complete and control returned to the guard. -/
theorem validPositiveRound1DoneZeroFlagPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlen : I.calldata.size = 213)
    (hbyte : I.calldata[212]! = 0)
    (hpos : UInt256.lt ⟨0⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont : UInt256.lt ⟨1⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1370⟩
      [⟨2⟩, ⟨640⟩, UInt256.shiftRight (inputFirstWord I) ⟨224⟩,
        ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (round1Mix7Mem3 (round1Mix6ZeroMem I))
      (UInt256.ofNat 62) ByteArray.empty (cA, σ) k
      (((((((13216 + 93) + 321) + 93) + 321) + 84) + 318) + 15) := by
  have hprefix := validPositiveRound1Mix7DoneZeroFlagPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hbyte hpos hcont
  exact round1DoneFromRound1Mix7Gas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (mem := round1Mix7Mem3 (round1Mix6ZeroMem I))
    (startGas := ((((((13216 + 93) + 321) + 93) + 321) + 84) + 318))
    hprefix

/-- Final-flag-`1`, at least two rounds: round 1 is complete and control returned to the guard. -/
theorem validPositiveRound1DoneOneFlagPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlen : I.calldata.size = 213)
    (hbyte : I.calldata[212]! = 1)
    (hpos : UInt256.lt ⟨0⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hcont : UInt256.lt ⟨1⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1370⟩
      [⟨2⟩, ⟨640⟩, UInt256.shiftRight (inputFirstWord I) ⟨224⟩,
        ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (round1Mix7Mem3 (round1Mix6OneMem I))
      (UInt256.ofNat 62) ByteArray.empty (cA, σ) k
      (((((((13243 + 93) + 321) + 93) + 321) + 84) + 318) + 15) := by
  have hprefix := validPositiveRound1Mix7DoneOneFlagPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hbyte hpos hcont
  exact round1DoneFromRound1Mix7Gas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (mem := round1Mix7Mem3 (round1Mix6OneMem I))
    (startGas := ((((((13243 + 93) + 321) + 93) + 321) + 84) + 318))
    hprefix

end Blake2f
