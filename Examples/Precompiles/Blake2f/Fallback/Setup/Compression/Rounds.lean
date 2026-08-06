import Examples.Precompiles.Blake2f.Fallback.Setup.Compression.V8ToFinal

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

/-- Valid inputs with final flag `0` enter the common rounds-loop setup.

Source note: this executes the fallthrough `JUMPDEST` at PC `1368` and `PUSH0`, stopping before
the loop-head `JUMPDEST` at PC `1370`. -/
theorem validRoundsLoopSetupZeroPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlen : I.calldata.size = 213)
    (hbyte : I.calldata[212]! = 0) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1370⟩
      [⟨0⟩, ⟨640⟩, UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩,
        ⟨1216⟩]
      (v13MixedMem I) (UInt256.ofNat 62) ByteArray.empty (cA, σ) k 7637 := by
  obtain ⟨k0, rd1368⟩ := validFinalFlagZeroBranchPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hbyte
  have rd1370 := evm_run rd1368 with [
    raw jumpdest (by decide) (by evm_ov),
    push0 ]
  exact ⟨_, by simpa using rd1370⟩

/-- Valid inputs with final flag `1` enter the common rounds-loop setup after applying the
final-block `v[14]` overwrite.

Source note: this executes the rejoined `JUMPDEST` at PC `1368` and `PUSH0`, stopping before the
loop-head `JUMPDEST` at PC `1370`. -/
theorem validRoundsLoopSetupOnePrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlen : I.calldata.size = 213)
    (hbyte : I.calldata[212]! = 1) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1370⟩
      [⟨0⟩, ⟨640⟩, UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩,
        ⟨1216⟩]
      (v14FinalFlagMem I) (UInt256.ofNat 62) ByteArray.empty (cA, σ) k 7664 := by
  obtain ⟨k0, rd1368⟩ := validFinalFlagOneRejoinPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hbyte
  have rd1370 := evm_run rd1368 with [
    raw jumpdest (by decide) (by evm_ov),
    push0 ]
  exact ⟨_, by simpa using rd1370⟩

/-- Valid inputs with final flag `0` and zero rounds leave the compression loop immediately.

Source note: the loop head at PC `1370` tests `i < rounds`.  At loop entry `i = 0`, so when this
condition is zero the `JUMPI` at PC `1377` falls through to PC `1378`. -/
theorem validRoundsGuardZeroRoundsZeroFlagPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlen : I.calldata.size = 213)
    (hbyte : I.calldata[212]! = 0)
    (hcond : UInt256.lt ⟨0⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) = ⟨0⟩) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1378⟩
      [⟨0⟩, ⟨640⟩, UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩,
        ⟨1216⟩]
      (v13MixedMem I) (UInt256.ofNat 62) ByteArray.empty (cA, σ) k 7660 := by
  obtain ⟨k0, rd1370⟩ := validRoundsLoopSetupZeroPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hbyte
  have rd1378 := evm_run rd1370 with [
    raw jumpdest (by decide) (by evm_ov),
    dup3,
    dup2,
    lt,
    push2 ⟨1445⟩,
    jumpiNT hcond ]
  exact ⟨_, by simpa using rd1378⟩

/-- Valid inputs with final flag `0` and positive rounds enter the compression loop body.

Source note: this is the taken side of the PC `1377` loop-head `JUMPI`, reaching the body
`JUMPDEST` at PC `1445`. -/
theorem validRoundsGuardPositiveRoundsZeroFlagPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlen : I.calldata.size = 213)
    (hbyte : I.calldata[212]! = 0)
    (hcond : UInt256.lt ⟨0⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1445⟩
      [⟨0⟩, ⟨640⟩, UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩,
        ⟨1216⟩]
      (v13MixedMem I) (UInt256.ofNat 62) ByteArray.empty (cA, σ) k 7660 := by
  obtain ⟨k0, rd1370⟩ := validRoundsLoopSetupZeroPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hbyte
  have rd1445 := evm_run rd1370 with [
    raw jumpdest (by decide) (by evm_ov),
    dup3,
    dup2,
    lt,
    push2 ⟨1445⟩,
    jumpiT hcond (by jump_dest) ]
  exact ⟨_, by simpa using rd1445⟩

/-- Valid inputs with final flag `1` and zero rounds leave the compression loop immediately.

This is the same PC `1370` guard as the flag-`0` case, but with the post-final-flag memory
`v14FinalFlagMem`. -/
theorem validRoundsGuardZeroRoundsOneFlagPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlen : I.calldata.size = 213)
    (hbyte : I.calldata[212]! = 1)
    (hcond : UInt256.lt ⟨0⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) = ⟨0⟩) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1378⟩
      [⟨0⟩, ⟨640⟩, UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩,
        ⟨1216⟩]
      (v14FinalFlagMem I) (UInt256.ofNat 62) ByteArray.empty (cA, σ) k 7687 := by
  obtain ⟨k0, rd1370⟩ := validRoundsLoopSetupOnePrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hbyte
  have rd1378 := evm_run rd1370 with [
    raw jumpdest (by decide) (by evm_ov),
    dup3,
    dup2,
    lt,
    push2 ⟨1445⟩,
    jumpiNT hcond ]
  exact ⟨_, by simpa using rd1378⟩

/-- Valid inputs with final flag `1` and positive rounds enter the compression loop body.

This is the taken side of the same PC `1377` loop-head branch, preserving the final-flag memory
update. -/
theorem validRoundsGuardPositiveRoundsOneFlagPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlen : I.calldata.size = 213)
    (hbyte : I.calldata[212]! = 1)
    (hcond : UInt256.lt ⟨0⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1445⟩
      [⟨0⟩, ⟨640⟩, UInt256.shiftRight (inputFirstWord I) ⟨224⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩,
        ⟨1216⟩]
      (v14FinalFlagMem I) (UInt256.ofNat 62) ByteArray.empty (cA, σ) k 7687 := by
  obtain ⟨k0, rd1370⟩ := validRoundsLoopSetupOnePrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hbyte
  have rd1445 := evm_run rd1370 with [
    raw jumpdest (by decide) (by evm_ov),
    dup3,
    dup2,
    lt,
    push2 ⟨1445⟩,
    jumpiT hcond (by jump_dest) ]
  exact ⟨_, by simpa using rd1445⟩

end Blake2f
