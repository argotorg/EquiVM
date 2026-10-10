import Benchmarks.Morpho.MetaMorphoV1_1.AccrueInterestTailSource
import Benchmarks.Morpho.MetaMorphoV1_1.UpdateLastAssetsRoutines
import Benchmarks.Morpho.MetaMorphoV1_1.MintRoutines
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_067
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_068

/-! The bytecode continuations around accrued assets, asset stores, and optional minting. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option maxRecDepth 2000

def lostAssetsTopic : UInt256 :=
  UInt256.ofNat 38231767796075997893968272344063384893917211852704487755612492856989667015537

def accrueInterestTopic : UInt256 :=
  UInt256.ofNat 111465361699314498625366748111526505401489847034838589105786939632250855302124

def accrueInterestCalcTail (ret : UInt256) (R : List UInt256) : List UInt256 :=
  ⟨32⟩ :: lostAssetsTopic :: ⟨64⟩ :: accrueInterestTopic :: ret :: R

def accrueInterestStoreTail (lost total shares ret : UInt256) (R : List UInt256) : List UInt256 :=
  lost :: ⟨32⟩ :: lostAssetsTopic :: shares :: total :: ⟨64⟩ :: accrueInterestTopic :: ret :: R

def accrueInterestEventStack (total shares ret : UInt256) (R : List UInt256) : List UInt256 :=
  shares :: total :: ⟨64⟩ :: accrueInterestTopic :: ret :: R

def accrueInterestStoreMemory (mem : ByteArray) (lost total : UInt256) : ByteArray :=
  let changed := writeWord mem (memLoad ⟨64⟩ mem).toNat total
  writeWord changed (memLoad ⟨64⟩ changed).toNat lost

def accrueInterestBranchPC (shares : UInt256) : UInt256 :=
  if shares = ⟨0⟩ then ⟨14369⟩ else ⟨14382⟩

theorem accrueInterestReachCalculation {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {ret : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 7 ≤ 1024)
    (rd : RD (deployedRuntime v) I g s0 ⟨14262⟩ (ret :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨12247⟩
      (⟨14340⟩ :: accrueInterestCalcTail ret R) mem aw' rdata σ k' C' := by
  exact metaMorphoV1_1_block_14262_packed (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd

theorem accrueInterestReachLastStore {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {lost total shares ret : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 11 ≤ 1024)
    (rd : RD (deployedRuntime v) I g s0 ⟨14340⟩
      ([lost, total, shares] ++ accrueInterestCalcTail ret R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨16830⟩
      (total :: ⟨14353⟩ :: accrueInterestStoreTail lost total shares ret R)
      mem aw' rdata σ k' C' := by
  exact metaMorphoV1_1_block_14340_packed (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd

theorem accrueInterestStoreReturn {evm : State} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {k C : Nat}
    {lost total shares ret : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 14 ≤ 1024)
    (hperm : evm.executionEnv.perm = true)
    (rd : RD (deployedRuntime v) evm.executionEnv g s0 ⟨16830⟩
      (total :: ⟨14353⟩ :: accrueInterestStoreTail lost total shares ret R)
      mem aw rdata evm.accountMap k C) :
    ∃ aw' k' C', RD (deployedRuntime v) evm.executionEnv g s0 (accrueInterestBranchPC shares)
      (accrueInterestEventStack total shares ret R) (accrueInterestStoreMemory mem lost total)
      aw' rdata (accrueInterestStoredState evm lost total).accountMap k' C' := by
  obtain ⟨aw1, k1, C1, h1⟩ := updateLastAssetsReturn v
    (by simp only [accrueInterestStoreTail, List.length_cons]; omega) hperm
    (by rw [metaMorphoV1_1PatchedValidJumps]; jump_dest) rd
  by_cases hzero : shares = ⟨0⟩
  · obtain ⟨aw2, k2, C2, h2⟩ := metaMorphoV1_1_block_14353_fallthrough_packed
      (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega) hperm hzero h1
    refine ⟨aw2, k2, C2, ?_⟩
    simpa only [accrueInterestBranchPC, hzero, ↓reduceIte, accrueInterestStoredState,
      updateLastAssetsState, storageStore_executionEnv, storageStore_accountMap] using h2
  · obtain ⟨aw2, k2, C2, h2⟩ := metaMorphoV1_1_block_14353_taken_packed
      (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega) hperm hzero
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h1
    refine ⟨aw2, k2, C2, ?_⟩
    simpa only [accrueInterestBranchPC, hzero, ↓reduceIte, accrueInterestStoredState,
      updateLastAssetsState, storageStore_executionEnv, storageStore_accountMap] using h2

theorem accrueInterestReachMint {evm : State} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {k C : Nat}
    {total shares ret : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 9 ≤ 1024)
    (rd : RD (deployedRuntime v) evm.executionEnv g s0 ⟨14382⟩
      (accrueInterestEventStack total shares ret R) mem aw rdata evm.accountMap k C) :
    ∃ aw' k' C', RD (deployedRuntime v) evm.executionEnv g s0 ⟨17718⟩
      (UInt256.ofNat (accrueFeeRecipient evm).toNat :: shares :: ⟨14397⟩ ::
        accrueInterestEventStack total shares ret R) mem aw' rdata evm.accountMap k' C' := by
  have ha : UInt256.ofNat (accrueFeeRecipient evm).toNat =
      UInt256.shiftRight (codeOwnerStorageWord evm.executionEnv evm.accountMap ⟨18⟩) ⟨96⟩ :=
    addressWord_eq_ofNat_address (shiftRight96_canonical _)
  rw [ha]
  exact metaMorphoV1_1_block_14382_packed (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd

theorem accrueInterestFinish {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {total shares ret : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 7 ≤ 1024) (hperm : I.perm = true)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD (deployedRuntime v) I g s0 ⟨14369⟩
      (accrueInterestEventStack total shares ret R) mem aw rdata σ k C) :
    ∃ mem' aw' k' C', RD (deployedRuntime v) I g s0 ret R mem' aw' rdata σ k' C' := by
  obtain ⟨aw1, k1, C1, h1⟩ := metaMorphoV1_1_block_14369_packed
    (immWords := wordsOf (immStore v)) hstack hperm hret rd
  exact ⟨_, aw1, k1, C1, h1⟩

theorem accrueInterestMintFinish {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {total shares ret : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 7 ≤ 1024) (hperm : I.perm = true)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD (deployedRuntime v) I g s0 ⟨14397⟩
      (accrueInterestEventStack total shares ret R) mem aw rdata σ k C) :
    ∃ mem' aw' k' C', RD (deployedRuntime v) I g s0 ret R mem' aw' rdata σ k' C' := by
  obtain ⟨aw1, k1, C1, h1⟩ := metaMorphoV1_1_block_14397_packed
    (immWords := wordsOf (immStore v))
    (by simp only [accrueInterestEventStack, List.length_cons]; omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  exact accrueInterestFinish v hstack hperm hret h1

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
