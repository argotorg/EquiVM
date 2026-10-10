import Benchmarks.Morpho.MetaMorphoV1_1.ApprovalRoutines
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_013
import Reasoning.ExternalCall

/-! Check the recovered permit signer and execute its approval. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option maxRecDepth 2000

theorem permitSignerMatch {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {owner spender : AccountAddress} {value : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 8 ≤ 1024)
    (rd : RD (deployedRuntime v) I g s0 ⟨1840⟩
      (UInt256.ofNat owner.toNat :: UInt256.ofNat owner.toNat :: UInt256.ofNat spender.toNat ::
        value :: UInt256.ofNat owner.toNat :: R) mem aw rdata σ k C) :
    ∃ k' C', RD (deployedRuntime v) I g s0 ⟨16692⟩
      (UInt256.ofNat owner.toNat :: UInt256.ofNat spender.toNat :: value :: ⟨1867⟩ :: R)
      mem aw rdata σ k' C' := by
  have hc : UInt256.land
      (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))
      (UInt256.ofNat owner.toNat) = UInt256.ofNat owner.toNat :=
    solcAddrMask_clean_left (addressWord_val_canonical owner)
  have r1 := metaMorphoV1_1_block_1840_fallthrough (immWords := wordsOf (immStore v)) hstack
    (by rw [hc]; exact u256_sub_self _) rd
  have r2 := metaMorphoV1_1_block_1857 (immWords := wordsOf (immStore v)) (by omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) r1
  exact ⟨_, _, r2⟩

theorem permitSignerMismatch {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {signer owner spender : AccountAddress} {value : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 8 ≤ 1024) (hne : signer ≠ owner)
    (rd : RD (deployedRuntime v) I g s0 ⟨1840⟩
      (UInt256.ofNat signer.toNat :: UInt256.ofNat owner.toNat :: UInt256.ofNat spender.toNat ::
        value :: UInt256.ofNat owner.toNat :: R) mem aw rdata σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  have hc : UInt256.land
      (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))
      (UInt256.ofNat signer.toNat) = UInt256.ofNat signer.toNat :=
    solcAddrMask_clean_left (addressWord_val_canonical signer)
  have r1 := metaMorphoV1_1_block_1840_taken (immWords := wordsOf (immStore v)) hstack
    (by
      rw [hc]
      apply u256_sub_ne_zero_of_ne
      intro he
      have he' := congrArg UInt256.toNat he
      rw [UInt256.toNat_ofNat_of_lt (n := signer.toNat) (lt_trans signer.isLt (by decide)),
        UInt256.toNat_ofNat_of_lt (n := owner.toNat) (lt_trans owner.isLt (by decide))] at he'
      exact hne (Fin.ext he'))
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  exact metaMorphoV1_1_block_1869 (immWords := wordsOf (immStore v)) hstack r1

theorem permitApprovalReturn {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {owner spender : AccountAddress} {value : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 9 ≤ 1024) (hperm : I.perm = true)
    (ho : owner ≠ AccountAddress.ofNat 0) (hsp : spender ≠ AccountAddress.ofNat 0)
    (hs : SourceState s0 I σ evm)
    (rd : RD (deployedRuntime v) I g s0 ⟨16692⟩
      (UInt256.ofNat owner.toNat :: UInt256.ofNat spender.toNat :: value :: ⟨1867⟩ :: R)
      mem aw rdata σ k C) :
    RDret (deployedRuntime v) g s0 (approvalState evm owner spender value).accountMap
      ByteArray.empty := by
  obtain ⟨aw1, k1, C1, r1⟩ := approvalReachStore v (by omega) ho hsp rd
  obtain ⟨aw2, k2, C2, r2⟩ := approvalStoreReturn v hstack hperm
    (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) r1
  have hstore := hs.storageWrite (approvalSlot owner spender) value
  rw [← hs.env] at hstore
  have ha : sstoreAccountMap I.codeOwner σ (approvalSlot owner spender) value =
      (approvalState evm owner spender value).accountMap := by
    simpa only [hs.env, approvalState] using hstore.accounts
  rw [ha] at r2
  exact metaMorphoV1_1_block_1867 (immWords := wordsOf (immStore v)) (by omega) r2

end Benchmarks.Morpho.MetaMorphoV1_1
