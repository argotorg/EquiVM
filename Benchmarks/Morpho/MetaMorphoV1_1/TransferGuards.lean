import Benchmarks.Morpho.MetaMorphoV1_1.ApprovalRoutines

/-! The sender and recipient guards in the compiled transfer routine. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false
set_option maxRecDepth 2000

theorem transferSenderGuard {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {sender recipient : AccountAddress} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 5 ≤ 1024)
    (ho : sender ≠ ⟨0, by decide⟩)
    (rd : RD (deployedRuntime v) I g s0 ⟨12728⟩
      (UInt256.ofNat sender.toNat :: UInt256.ofNat recipient.toNat :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨12745⟩
      (UInt256.ofNat recipient.toNat :: UInt256.ofNat sender.toNat :: R)
      mem aw' rdata σ k' C' := by
  have hm : UInt256.land
      (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
        (UInt256.ofNat 1)) (UInt256.ofNat sender.toNat) = UInt256.ofNat sender.toNat :=
    solcAddrMask_clean_left (addressWord_val_canonical sender)
  obtain ⟨aw1, k1, C1, h1⟩ := metaMorphoV1_1_block_12728_fallthrough_packed
    (immWords := wordsOf (immStore v)) hstack (by
      rw [hm]
      exact isZero_eq_zero_of_ne (approvalAddressWord_ne_zero ho)) rd
  simp only [metaMorphoV1_1_block_12728_fallthrough_stack, hm] at h1
  exact ⟨aw1, k1, C1, h1⟩

theorem transferReachBalance {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {sender recipient : AccountAddress} {value ret : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 7 ≤ 1024)
    (ho : sender ≠ ⟨0, by decide⟩) (hs : recipient ≠ ⟨0, by decide⟩)
    (rd : RD (deployedRuntime v) I g s0 ⟨12728⟩
      (UInt256.ofNat sender.toNat :: UInt256.ofNat recipient.toNat :: value :: ret :: R)
      mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨12761⟩
      (value :: UInt256.ofNat sender.toNat :: UInt256.ofNat recipient.toNat :: ret :: R)
      mem aw' rdata σ k' C' := by
  obtain ⟨aw1, k1, C1, h1⟩ := transferSenderGuard v (by simp only [List.length_cons]; omega) ho rd
  have hm : UInt256.land
      (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
        (UInt256.ofNat 1)) (UInt256.ofNat recipient.toNat) = UInt256.ofNat recipient.toNat :=
    solcAddrMask_clean_left (addressWord_val_canonical recipient)
  obtain ⟨aw2, k2, C2, h2⟩ := metaMorphoV1_1_block_12745_fallthrough_packed
    (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega) (by
      rw [hm]
      exact isZero_eq_zero_of_ne (approvalAddressWord_ne_zero hs)) h1
  simp only [metaMorphoV1_1_block_12745_fallthrough_stack, hm] at h2
  exact ⟨aw2, k2, C2, h2⟩

theorem transferRevertAddress {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {sender recipient : AccountAddress} {value ret : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 7 ≤ 1024)
    (hbad : ¬ (sender ≠ ⟨0, by decide⟩ ∧ recipient ≠ ⟨0, by decide⟩))
    (rd : RD (deployedRuntime v) I g s0 ⟨12728⟩
      (UInt256.ofNat sender.toNat :: UInt256.ofNat recipient.toNat :: value :: ret :: R)
      mem aw rdata σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  by_cases ho : sender ≠ ⟨0, by decide⟩
  · obtain ⟨aw1, k1, C1, h1⟩ := transferSenderGuard v
      (by simp only [List.length_cons]; omega) ho rd
    have hs : recipient = ⟨0, by decide⟩ := by
      by_contra hs
      exact hbad ⟨ho, hs⟩
    subst recipient
    obtain ⟨aw2, k2, C2, h2⟩ := metaMorphoV1_1_block_12745_taken_packed
      (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega) (by decide)
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h1
    exact metaMorphoV1_1_block_12879 (immWords := wordsOf (immStore v))
      (by simp only [metaMorphoV1_1_block_12745_taken_stack, List.length_cons]; omega) h2
  · have hz : sender = ⟨0, by decide⟩ := not_ne_iff.mp ho
    subst sender
    obtain ⟨aw1, k1, C1, h1⟩ := metaMorphoV1_1_block_12728_taken_packed
      (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega) (by decide)
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
    exact metaMorphoV1_1_block_12898 (immWords := wordsOf (immStore v))
      (by simp only [metaMorphoV1_1_block_12728_taken_stack, List.length_cons]; omega) h1

end Benchmarks.Morpho.MetaMorphoV1_1
