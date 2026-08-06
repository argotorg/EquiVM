import Examples.Precompiles.Blake2f.Fallback.Setup

/-!
# BLAKE2F fallback zero-round output-loop traces

This module contains the zero-round branch from compression-loop exit through materializing the
eight scratch output words.  It is separated from parser/compression setup so return-data proof work
does not recheck parser prefixes.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

/-- Valid final-flag-`0` inputs with zero rounds enter the output-loop setup.

Source note: after the rounds-loop guard falls through, PC `1378..1381` pops the compression loop
state (`i`, `m`, and `rounds`) and pushes output index `0`, reaching the output-loop head at PC
`1382`. -/
theorem validOutputLoopSetupZeroRoundsZeroFlagPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlen : I.calldata.size = 213)
    (hbyte : I.calldata[212]! = 0)
    (hcond : UInt256.lt ⟨0⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) = ⟨0⟩) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1382⟩
      [⟨0⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (v13MixedMem I) (UInt256.ofNat 62) ByteArray.empty (cA, σ) k 7668 := by
  obtain ⟨k0, rd1378⟩ := validRoundsGuardZeroRoundsZeroFlagPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hbyte hcond
  have rd1382 := evm_run rd1378 with [
    pop,
    pop,
    pop,
    push0 ]
  exact ⟨_, by simpa using rd1382⟩

/-- Valid final-flag-`1` inputs with zero rounds enter the output-loop setup.

This is the same PC `1378..1381` cleanup as the flag-`0` case, preserving the final-flag memory
update. -/
theorem validOutputLoopSetupZeroRoundsOneFlagPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlen : I.calldata.size = 213)
    (hbyte : I.calldata[212]! = 1)
    (hcond : UInt256.lt ⟨0⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) = ⟨0⟩) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1382⟩
      [⟨0⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (v14FinalFlagMem I) (UInt256.ofNat 62) ByteArray.empty (cA, σ) k 7695 := by
  obtain ⟨k0, rd1378⟩ := validRoundsGuardZeroRoundsOneFlagPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hbyte hcond
  have rd1382 := evm_run rd1378 with [
    pop,
    pop,
    pop,
    push0 ]
  exact ⟨_, by simpa using rd1382⟩

/-- Valid final-flag-`0` zero-round inputs enter the first output-loop iteration.

Source note: the output-loop guard at PC `1382` checks `i < 8`.  At loop entry `i = 0`, so the
branch is always taken to PC `1395`. -/
theorem validOutputLoopBodyZeroRoundsZeroFlagPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlen : I.calldata.size = 213)
    (hbyte : I.calldata[212]! = 0)
    (hcond : UInt256.lt ⟨0⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) = ⟨0⟩) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1395⟩
      [⟨0⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (v13MixedMem I) (UInt256.ofNat 62) ByteArray.empty (cA, σ) k 7691 := by
  obtain ⟨k0, rd1382⟩ := validOutputLoopSetupZeroRoundsZeroFlagPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hbyte hcond
  have rd1395 := evm_run rd1382 with [
    raw jumpdest (by decide) (by evm_ov),
    push1 ⟨8⟩,
    dup2,
    lt,
    push2 ⟨1395⟩,
    jumpiT (by native_decide) (by jump_dest) ]
  exact ⟨_, by simpa using rd1395⟩

/-- Valid final-flag-`1` zero-round inputs enter the first output-loop iteration.

This is the same output-loop guard as the flag-`0` case, preserving the final-flag memory update. -/
theorem validOutputLoopBodyZeroRoundsOneFlagPrefixGas {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = runtimeBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hlen : I.calldata.size = 213)
    (hbyte : I.calldata[212]! = 1)
    (hcond : UInt256.lt ⟨0⟩ (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) = ⟨0⟩) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨1395⟩
      [⟨0⟩, ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
      (v14FinalFlagMem I) (UInt256.ofNat 62) ByteArray.empty (cA, σ) k 7718 := by
  obtain ⟨k0, rd1382⟩ := validOutputLoopSetupZeroRoundsOneFlagPrefixGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hcode hwv hlen hbyte hcond
  have rd1395 := evm_run rd1382 with [
    raw jumpdest (by decide) (by evm_ov),
    push1 ⟨8⟩,
    dup2,
    lt,
    push2 ⟨1395⟩,
    jumpiT (by native_decide) (by jump_dest) ]
  exact ⟨_, by simpa using rd1395⟩

end Blake2f
