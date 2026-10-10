import Benchmarks.Morpho.MetaMorphoV1_1.SpendAllowanceLookup

/-! Finite allowance sufficiency and approval-address guards. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false
set_option maxRecDepth 2000

theorem spendAllowanceEnoughGuard {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {owner spender value allowed : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 6 ≤ 1024)
    (hle : value.toNat ≤ allowed.toNat)
    (rd : RD (deployedRuntime v) I g s0 ⟨12585⟩
      (owner :: spender :: value :: allowed :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨12593⟩
      (owner :: spender :: value :: allowed :: R) mem aw' rdata σ k' C' :=
  metaMorphoV1_1_block_12585_fallthrough_packed (immWords := wordsOf (immStore v))
    hstack (ult_zero hle) rd

theorem spendAllowanceOwnerGuard {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {owner : AccountAddress} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 3 ≤ 1024)
    (ho : owner ≠ ⟨0, by decide⟩)
    (rd : RD (deployedRuntime v) I g s0 ⟨12593⟩
      (UInt256.ofNat owner.toNat :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨12599⟩
      (UInt256.ofNat owner.toNat :: R) mem aw' rdata σ k' C' :=
  metaMorphoV1_1_block_12593_fallthrough_packed (immWords := wordsOf (immStore v))
    hstack (isZero_eq_zero_of_ne (approvalAddressWord_ne_zero ho)) rd

theorem spendAllowanceReachStore {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {owner spender : AccountAddress} {value allowed : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 7 ≤ 1024)
    (hg : value.toNat ≤ allowed.toNat ∧ owner ≠ ⟨0, by decide⟩ ∧ spender ≠ ⟨0, by decide⟩)
    (rd : RD (deployedRuntime v) I g s0 ⟨12585⟩
      (UInt256.ofNat owner.toNat :: UInt256.ofNat spender.toNat :: value :: allowed :: R)
      mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨12614⟩
      (UInt256.ofNat owner.toNat :: UInt256.ofNat spender.toNat :: value :: allowed :: R)
      mem aw' rdata σ k' C' := by
  obtain ⟨aw1, k1, C1, h1⟩ := spendAllowanceEnoughGuard v (by omega) hg.1 rd
  obtain ⟨aw2, k2, C2, h2⟩ := spendAllowanceOwnerGuard v
    (by simp only [List.length_cons]; omega) hg.2.1 h1
  have hm : UInt256.land (UInt256.ofNat spender.toNat)
      (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
        (UInt256.ofNat 1)) = UInt256.ofNat spender.toNat :=
    solcAddrMask_clean (addressWord_val_canonical spender)
  exact metaMorphoV1_1_block_12599_fallthrough_packed (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega)
    (by rw [hm]; exact isZero_eq_zero_of_ne (approvalAddressWord_ne_zero hg.2.2)) h2

theorem spendAllowanceRevertGuard {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {owner spender : AccountAddress} {value allowed : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 7 ≤ 1024)
    (hb : ¬ (value.toNat ≤ allowed.toNat ∧ owner ≠ ⟨0, by decide⟩ ∧ spender ≠ ⟨0, by decide⟩))
    (rd : RD (deployedRuntime v) I g s0 ⟨12585⟩
      (UInt256.ofNat owner.toNat :: UInt256.ofNat spender.toNat :: value :: allowed :: R)
      mem aw rdata σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  by_cases hle : value.toNat ≤ allowed.toNat
  · obtain ⟨aw1, k1, C1, h1⟩ := spendAllowanceEnoughGuard v (by omega) hle rd
    by_cases ho : owner ≠ ⟨0, by decide⟩
    · obtain ⟨aw2, k2, C2, h2⟩ := spendAllowanceOwnerGuard v
        (by simp only [List.length_cons]; omega) ho h1
      have hz : spender = ⟨0, by decide⟩ := by
        by_contra hs
        exact hb ⟨hle, ho, hs⟩
      subst spender
      obtain ⟨aw3, k3, C3, h3⟩ := metaMorphoV1_1_block_12599_taken_packed
        (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega)
        (by decide) (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h2
      exact metaMorphoV1_1_block_12655 (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons]; omega) h3
    · have hz := not_ne_iff.mp ho
      subst owner
      obtain ⟨aw2, k2, C2, h2⟩ := metaMorphoV1_1_block_12593_taken_packed
        (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega)
        (by decide) (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h1
      exact metaMorphoV1_1_block_12674 (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons]; omega) h2
  · obtain ⟨aw1, k1, C1, h1⟩ := metaMorphoV1_1_block_12585_taken_packed
      (immWords := wordsOf (immStore v)) (by omega)
      (by rw [ult_one (Nat.lt_of_not_ge hle)]; decide)
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
    exact metaMorphoV1_1_block_12693 (immWords := wordsOf (immStore v)) hstack h1

end Benchmarks.Morpho.MetaMorphoV1_1
