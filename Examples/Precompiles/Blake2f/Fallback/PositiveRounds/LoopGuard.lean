import Examples.Precompiles.Blake2f.Fallback.ModelBridge
import Examples.Precompiles.Blake2f.Fallback.PositiveRounds.ProofSupportExact

/-!
# BLAKE2F positive-round traces: generic loop guard

This file is intentionally parametric in the loop index.  The older `GuardN.lean` files prove the
same bytecode branch for concrete indices; this module is the reusable guard step needed by an
arbitrary-round `RDx.whileLoopCarryGas` proof.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Blake2f

set_option maxRecDepth 500000
set_option maxHeartbeats 0

abbrev positiveRoundHeaderPc : UInt256 := ⟨1370⟩

abbrev positiveRoundBodyPc : UInt256 := ⟨1445⟩

abbrev positiveRoundExitPc : UInt256 := ⟨1378⟩

def positiveRoundHeaderStack (I : ExecutionEnv) (i : Nat) : List UInt256 :=
  [UInt256.ofNat i, ⟨640⟩, UInt256.shiftRight (inputFirstWord I) ⟨224⟩,
    ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]

def positiveRoundHeaderRDx
    (cA : Batteries.RBSet AccountAddress compare) (gh : BlockHeader) (bl : ProcessedBlocks)
    (σ σ₀ : AccountMap) (A : Substate) (I : ExecutionEnv) (g : Sat256)
    (i : Nat) (mem : ByteArray) (gas : Nat) : Prop :=
  ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
    positiveRoundHeaderPc
    (positiveRoundHeaderStack I i)
    mem (UInt256.ofNat 62) ByteArray.empty (cA, σ) k gas

private theorem positiveRoundGuardExitFromHeaderGas {cA gh bl σ σ₀ A I} {g : Sat256}
    {idx : UInt256} {mem : ByteArray} {startGas : Nat}
    (hcond : UInt256.lt idx (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) = ⟨0⟩)
    (hprefix :
      ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
        positiveRoundHeaderPc
        [idx, ⟨640⟩, UInt256.shiftRight (inputFirstWord I) ⟨224⟩,
          ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
        mem (UInt256.ofNat 62) ByteArray.empty (cA, σ) k startGas) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      positiveRoundExitPc
      [idx, ⟨640⟩, UInt256.shiftRight (inputFirstWord I) ⟨224⟩,
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
  exact ⟨_, by simpa [positiveRoundHeaderPc, positiveRoundExitPc, Nat.add_assoc] using rd1378⟩

private theorem positiveRoundGuardContinueFromHeaderGas {cA gh bl σ σ₀ A I} {g : Sat256}
    {idx : UInt256} {mem : ByteArray} {startGas : Nat}
    (hcond : UInt256.lt idx (UInt256.shiftRight (inputFirstWord I) ⟨224⟩) ≠ ⟨0⟩)
    (hprefix :
      ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
        positiveRoundHeaderPc
        [idx, ⟨640⟩, UInt256.shiftRight (inputFirstWord I) ⟨224⟩,
          ⟨384⟩, ⟨1472⟩, ⟨168⟩, ⟨1216⟩]
        mem (UInt256.ofNat 62) ByteArray.empty (cA, σ) k startGas) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      positiveRoundBodyPc
      [idx, ⟨640⟩, UInt256.shiftRight (inputFirstWord I) ⟨224⟩,
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
  exact ⟨_, by simpa [positiveRoundHeaderPc, positiveRoundBodyPc, Nat.add_assoc] using rd1445⟩

/-- Generic exact-gas guard exit at loop index `i`, tied to the trusted model round count. -/
theorem positiveRoundGuardExitOfModelRoundsEqGas {cA gh bl σ σ₀ A I} {g : Sat256}
    {i : Nat} {mem : ByteArray} {startGas : Nat}
    (hlen : I.calldata.size = 213)
    (hrounds : Model.rounds I.calldata = i)
    (hprefix :
      positiveRoundHeaderRDx cA gh bl σ σ₀ A I g i mem startGas) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      positiveRoundExitPc
      (positiveRoundHeaderStack I i)
      mem (UInt256.ofNat 62) ByteArray.empty (cA, σ) k (startGas + 23) := by
  exact positiveRoundGuardExitFromHeaderGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (idx := UInt256.ofNat i) (mem := mem) (startGas := startGas)
    (bytecodeRoundIndexGuard_zero_of_modelRounds_eq I hlen hrounds)
    (by simpa [positiveRoundHeaderRDx, positiveRoundHeaderStack] using hprefix)

/-- Generic exact-gas guard continuation at loop index `i`, tied to the trusted model round count. -/
theorem positiveRoundGuardContinueOfModelRoundsGtGas {cA gh bl σ σ₀ A I} {g : Sat256}
    {i : Nat} {mem : ByteArray} {startGas : Nat}
    (hlen : I.calldata.size = 213)
    (hrounds : i < Model.rounds I.calldata)
    (hprefix :
      positiveRoundHeaderRDx cA gh bl σ σ₀ A I g i mem startGas) :
    ∃ k, RDx runtimeBytecode I g (initState cA gh bl σ σ₀ g A I)
      positiveRoundBodyPc
      (positiveRoundHeaderStack I i)
      mem (UInt256.ofNat 62) ByteArray.empty (cA, σ) k (startGas + 23) := by
  exact positiveRoundGuardContinueFromHeaderGas
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (idx := UInt256.ofNat i) (mem := mem) (startGas := startGas)
    (bytecodeRoundIndexGuard_ne_zero_of_modelRounds_gt I hlen hrounds)
    (by simpa [positiveRoundHeaderRDx, positiveRoundHeaderStack] using hprefix)

end Blake2f
