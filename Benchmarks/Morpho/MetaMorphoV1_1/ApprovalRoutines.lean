import Benchmarks.Morpho.MetaMorphoV1_1.ApprovalSource
import Benchmarks.Morpho.MetaMorphoV1_1.ApprovalStatic
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_063

/-! Approval address guards and the nested allowance-mapping write. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false
set_option maxRecDepth 2000

theorem approvalAddressWord_ne_zero {a : AccountAddress} (h : a ≠ ⟨0, by decide⟩) :
    UInt256.ofNat a.toNat ≠ ⟨0⟩ := by
  intro heq
  have hv := congrArg UInt256.toNat heq
  rw [UInt256.toNat_ofNat_of_lt (n := a.toNat) (lt_trans a.isLt (by decide))] at hv
  exact h (Fin.ext hv)

theorem approvalOwnerGuard {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {owner spender : AccountAddress} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 5 ≤ 1024)
    (ho : owner ≠ ⟨0, by decide⟩)
    (rd : RD (deployedRuntime v) I g s0 ⟨16692⟩
      (UInt256.ofNat owner.toNat :: UInt256.ofNat spender.toNat :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨16709⟩
      (UInt256.ofNat spender.toNat :: UInt256.ofNat owner.toNat :: R)
      mem aw' rdata σ k' C' := by
  have hm : UInt256.land
      (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
        (UInt256.ofNat 1)) (UInt256.ofNat owner.toNat) = UInt256.ofNat owner.toNat :=
    solcAddrMask_clean_left (addressWord_val_canonical owner)
  obtain ⟨aw1, k1, C1, h1⟩ := metaMorphoV1_1_block_16692_fallthrough_packed
    (immWords := wordsOf (immStore v)) hstack (by
      rw [hm]
      exact isZero_eq_zero_of_ne (approvalAddressWord_ne_zero ho)) rd
  simp only [metaMorphoV1_1_block_16692_fallthrough_stack, hm] at h1
  exact ⟨aw1, k1, C1, h1⟩

theorem approvalReachStore {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {owner spender : AccountAddress} {value ret : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 7 ≤ 1024)
    (ho : owner ≠ ⟨0, by decide⟩) (hs : spender ≠ ⟨0, by decide⟩)
    (rd : RD (deployedRuntime v) I g s0 ⟨16692⟩
      (UInt256.ofNat owner.toNat :: UInt256.ofNat spender.toNat :: value :: ret :: R)
      mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨16725⟩
      (value :: UInt256.ofNat owner.toNat :: UInt256.ofNat spender.toNat :: ret :: R)
      mem aw' rdata σ k' C' := by
  obtain ⟨aw1, k1, C1, h1⟩ := approvalOwnerGuard v (by simp only [List.length_cons]; omega) ho rd
  have hm : UInt256.land
      (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
        (UInt256.ofNat 1)) (UInt256.ofNat spender.toNat) = UInt256.ofNat spender.toNat :=
    solcAddrMask_clean_left (addressWord_val_canonical spender)
  obtain ⟨aw2, k2, C2, h2⟩ := metaMorphoV1_1_block_16709_fallthrough_packed
    (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega) (by
      rw [hm]
      exact isZero_eq_zero_of_ne (approvalAddressWord_ne_zero hs)) h1
  simp only [metaMorphoV1_1_block_16709_fallthrough_stack, hm] at h2
  exact ⟨aw2, k2, C2, h2⟩

theorem approvalRevertAddress {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {owner spender : AccountAddress} {value ret : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 7 ≤ 1024)
    (hbad : ¬ (owner ≠ ⟨0, by decide⟩ ∧ spender ≠ ⟨0, by decide⟩))
    (rd : RD (deployedRuntime v) I g s0 ⟨16692⟩
      (UInt256.ofNat owner.toNat :: UInt256.ofNat spender.toNat :: value :: ret :: R)
      mem aw rdata σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  by_cases ho : owner ≠ ⟨0, by decide⟩
  · obtain ⟨aw1, k1, C1, h1⟩ := approvalOwnerGuard v
      (by simp only [List.length_cons]; omega) ho rd
    have hs : spender = ⟨0, by decide⟩ := by
      by_contra hs
      exact hbad ⟨ho, hs⟩
    subst spender
    obtain ⟨aw2, k2, C2, h2⟩ := metaMorphoV1_1_block_16709_taken_packed
      (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega) (by decide)
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h1
    exact metaMorphoV1_1_block_12655 (immWords := wordsOf (immStore v))
      (by simp only [metaMorphoV1_1_block_16709_taken_stack, List.length_cons]; omega) h2
  · have hz : owner = ⟨0, by decide⟩ := not_ne_iff.mp ho
    subst owner
    obtain ⟨aw1, k1, C1, h1⟩ := metaMorphoV1_1_block_16692_taken_packed
      (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega) (by decide)
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
    exact metaMorphoV1_1_block_12674 (immWords := wordsOf (immStore v))
      (by simp only [metaMorphoV1_1_block_16692_taken_stack, List.length_cons]; omega) h1

def approvalScratchMem (mem : ByteArray) (owner spender : AccountAddress) : ByteArray :=
  twoWordHashMem (UInt256.ofNat spender.toNat)
    (solcMappingSlot ⟨1⟩ (UInt256.ofNat owner.toNat))
    (twoWordHashMem (UInt256.ofNat owner.toNat) ⟨1⟩ mem)

def approvalReturnMem (mem : ByteArray) (owner spender : AccountAddress) (value : UInt256) :
    ByteArray :=
  writeWord (approvalScratchMem mem owner spender)
    (memLoad ⟨64⟩ (approvalScratchMem mem owner spender)).toNat value

theorem approvalStoreReturn {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {owner spender : AccountAddress} {value ret : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 9 ≤ 1024) (hperm : I.perm = true)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD (deployedRuntime v) I g s0 ⟨16725⟩
      (value :: UInt256.ofNat owner.toNat :: UInt256.ofNat spender.toNat :: ret :: R)
      mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 ret R
      (approvalReturnMem mem owner spender value) aw' rdata
      (sstoreAccountMap I.codeOwner σ (approvalSlot owner spender) value) k' C' := by
  let inner := twoWordHashMem (UInt256.ofNat owner.toNat) ⟨1⟩ mem
  let outer := twoWordHashMem (UInt256.ofNat spender.toNat) (keccakWord ⟨0⟩ ⟨64⟩ inner) inner
  have hi : keccakWord ⟨0⟩ ⟨64⟩ inner =
      solcMappingSlot ⟨1⟩ (UInt256.ofNat owner.toNat) :=
    twoWordHashMem_solcMappingSlot_any _ _ _
  have hout : outer = approvalScratchMem mem owner spender := by
    dsimp only [outer, approvalScratchMem]
    rw [hi]
  obtain ⟨aw1, k1, C1, h1⟩ := metaMorphoV1_1_block_16725_packed
    (immWords := wordsOf (immStore v)) hstack hperm hret rd
  change RD (deployedRuntime v) I g s0 ret R
    (writeWord outer (memLoad ⟨64⟩ outer).toNat value) aw1 rdata
    (sstoreAccountMap I.codeOwner σ (keccakWord ⟨0⟩ ⟨64⟩ outer) value) k1 C1 at h1
  rw [hout] at h1
  have hh : keccakWord ⟨0⟩ ⟨64⟩ (approvalScratchMem mem owner spender) =
      approvalSlot owner spender := twoWordHashMem_solcMappingSlot_any _ _ _
  rw [hh] at h1
  exact ⟨aw1, k1, C1, h1⟩

end Benchmarks.Morpho.MetaMorphoV1_1
