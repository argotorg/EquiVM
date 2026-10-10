import Benchmarks.Morpho.MetaMorphoV1_1.SetCapQueueSource
import Benchmarks.Morpho.MetaMorphoV1_1.ArrayRoutines
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_013
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_051
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_065
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_066

/-! Queue growth and both queue-length guards in the cap setter. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option maxRecDepth 2000

theorem setCapQueueLengthRuntime {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 5 ≤ 1024)
    (rd : RD (deployedRuntime v) I g s0 ⟨13596⟩ R mem aw rdata σ k C) :
    (¬ (codeOwnerStorageWord I σ ⟨21⟩).toNat < 2 ^ 64 ∧ RDrev (deployedRuntime v) g s0) ∨
    ((codeOwnerStorageWord I σ ⟨21⟩).toNat < 2 ^ 64 ∧ ∃ k' C',
      RD (deployedRuntime v) I g s0 ⟨13612⟩
        (codeOwnerStorageWord I σ ⟨21⟩ :: R) mem aw rdata σ k' C') := by
  by_cases hl : (codeOwnerStorageWord I σ ⟨21⟩).toNat < 2 ^ 64
  · refine .inr ⟨hl, ?_⟩
    exact metaMorphoV1_1_block_13596_fallthrough (immWords := wordsOf (immStore v))
      (by omega)
      (by rw [ult_one (by exact hl)]; decide) rd
  · refine .inl ⟨hl, ?_⟩
    obtain ⟨_, _, h⟩ := metaMorphoV1_1_block_13596_taken
      (immWords := wordsOf (immStore v)) (by omega)
      (by rw [ult_zero (by exact Nat.le_of_not_gt hl)]; decide)
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
    exact metaMorphoV1_1_block_2690 (immWords := wordsOf (immStore v))
      (by change (codeOwnerStorageWord I σ ⟨21⟩ :: R).length + 2 ≤ 1024
          simp only [List.length_cons]; omega) h

def setCapQueueAccounts (I : ExecutionEnv) (σ : AccountMap) (len id : UInt256) : AccountMap :=
  sstoreAccountMap I.codeOwner (sstoreAccountMap I.codeOwner σ ⟨21⟩ (len + ⟨1⟩))
    (solidityBytesDataBaseSlot ⟨21⟩ + len) id

theorem setCapQueuePushState_accounts (evm : State) (id : UInt256) :
    (setCapQueuePushState evm id).accountMap =
      setCapQueueAccounts evm.executionEnv evm.accountMap (setCapQueueLength evm) id := by
  simp only [setCapQueuePushState, storageStore_accountMap]
  rfl

theorem setCapQueuePushState_source {s0 evm : State} {I : ExecutionEnv} {σ : AccountMap}
    (hs : SourceState s0 I σ evm) (id : UInt256) :
    SourceState s0 I
      (setCapQueueAccounts I σ (codeOwnerStorageWord I σ ⟨21⟩) id)
      (setCapQueuePushState evm id) := by
  unfold setCapQueuePushState
  rw [show setCapQueueLength evm = codeOwnerStorageWord I σ ⟨21⟩ from hs.storageRead ⟨21⟩,
    hs.env]
  exact (hs.storageWrite ⟨21⟩ (codeOwnerStorageWord I σ ⟨21⟩ + ⟨1⟩)).storageWrite
    (solidityBytesDataBaseSlot ⟨21⟩ + codeOwnerStorageWord I σ ⟨21⟩) id

theorem setCapQueuePushRuntime {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} {len params cap id ret slot : UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 10 ≤ 1024)
    (hsmall : len.toNat < 2 ^ 64) (hacc : ∃ acc, σ.get? I.codeOwner = some acc)
    (hperm : I.perm = true)
    (rd : RD (deployedRuntime v) I g s0 ⟨13612⟩
      ([len, params, cap, id, ret, slot] ++ R) mem aw rdata σ k C) :
    (¬ (codeOwnerStorageWord I (setCapQueueAccounts I σ len id) ⟨21⟩).toNat ≤ 30 ∧
      RDrev (deployedRuntime v) g s0) ∨
    ((codeOwnerStorageWord I (setCapQueueAccounts I σ len id) ⟨21⟩).toNat ≤ 30 ∧
      ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨13658⟩
        ([params, cap, id, ret, slot] ++ R) (wordAt0Mem ⟨21⟩ mem) aw' rdata
        (setCapQueueAccounts I σ len id) k' C') := by
  obtain ⟨acc, hacc⟩ := hacc
  obtain ⟨_, _, h1⟩ := metaMorphoV1_1_block_13612 (immWords := wordsOf (immStore v))
    (R := [params, cap, id, ret, slot] ++ R)
    (by simp only [List.length_append, List.length_cons, List.length_nil]; omega) hperm
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  have hn : codeOwnerStorageWord I
      (sstoreAccountMap I.codeOwner σ (UInt256.ofNat 21) (len + UInt256.ofNat 1))
      ⟨21⟩ = len + ⟨1⟩ := sstoreAccountMap_storage_getD_self_present σ I.codeOwner hacc _ _
  obtain ⟨_, _, h2⟩ := withdrawQueueIndex v
    (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
    (by rw [hn, uadd_toNat]
        change len.toNat < (len.toNat + 1) % UInt256.size
        rw [Nat.mod_eq_of_lt (by change len.toNat + 1 < 2 ^ 256; omega)]
        omega)
    (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) h1
  have hw (word : UInt256) : UInt256.lor
      (UInt256.land (UInt256.lnot
        (UInt256.shiftLeft (UInt256.lnot ⟨0⟩) (UInt256.shiftLeft ⟨0⟩ (UInt256.ofNat 3)))) word)
      (UInt256.shiftLeft id (UInt256.shiftLeft ⟨0⟩ (UInt256.ofNat 3))) = id := by
    rw [show UInt256.lnot
        (UInt256.shiftLeft (UInt256.lnot ⟨0⟩) (UInt256.shiftLeft ⟨0⟩ (UInt256.ofNat 3))) =
        ⟨0⟩ by decide, u256_land_zero_left, uint256_lor_zero_left]
    rw [show UInt256.shiftLeft ⟨0⟩ (UInt256.ofNat 3) = ⟨0⟩ by decide]
    apply u256_inj
    simp [UInt256.shiftLeft, UInt256.toNat, Fin.shiftLeft_val]
    exact Nat.mod_eq_of_lt id.val.isLt
  by_cases hl : (codeOwnerStorageWord I (setCapQueueAccounts I σ len id) ⟨21⟩).toNat ≤ 30
  · refine .inr ⟨hl, ?_⟩
    obtain ⟨k3, C3, h3⟩ := metaMorphoV1_1_block_13627_fallthrough
      (immWords := wordsOf (immStore v))
      (R := [ret, slot] ++ R)
      (by simp only [List.length_append, List.length_cons, List.length_nil]; omega) hperm
      (by rw [hw]
          apply ugt_zero
          exact hl) h2
    rw [hw] at h3
    exact ⟨_, k3, C3, h3⟩
  · refine .inl ⟨hl, ?_⟩
    obtain ⟨_, _, h3⟩ := metaMorphoV1_1_block_13627_taken
      (immWords := wordsOf (immStore v))
      (R := [ret, slot] ++ R)
      (by simp only [List.length_append, List.length_cons, List.length_nil]; omega) hperm
      (by rw [hw, ugt_one (by exact Nat.lt_of_not_ge hl)]; decide)
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h2
    exact metaMorphoV1_1_block_10384 (immWords := wordsOf (immStore v))
      (by change (params :: cap :: id :: [ret, slot] ++ R).length + 2 ≤ 1024
          simp only [List.length_append, List.length_cons, List.length_nil]; omega) h3

end Benchmarks.Morpho.MetaMorphoV1_1
