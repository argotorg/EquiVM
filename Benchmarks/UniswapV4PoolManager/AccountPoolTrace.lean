import Benchmarks.UniswapV4PoolManager.AccountPoolSource
import Benchmarks.UniswapV4PoolManager.AccountDeltaCallTrace
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_038

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def accountPoolMemory (mem : ByteArray) (key : PoolKeyWords) (delta : UInt256) (target : AccountAddress) : ByteArray :=
  accountDeltaMemory
    (accountDeltaMemory mem target (accountPoolCurrency key false) (balanceDeltaComponent false delta))
    target (accountPoolCurrency key true) (balanceDeltaComponent true delta)
def accountPoolPost (evm : State) (key : PoolKeyWords) (delta : UInt256) (target : AccountAddress) : State :=
  accountDeltaPost
    (accountDeltaPost evm target (accountPoolCurrency key false) (balanceDeltaComponent false delta))
    target (accountPoolCurrency key true) (balanceDeltaComponent true delta)

theorem accountPoolCostTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {aw ptr delta ret : UInt256} {key : PoolKeyWords} {target : AccountAddress}
    {k C : Nat} {R : List UInt256} (f : Frame) (v : PoolManagerImmutables)
    (hstack : R.length+16 ≤ 1024) (hI : evm.executionEnv = I)
    (hkey0 : memLoad ptr mem = key.currency0)
    (hkey1 : memLoad (ptr+UInt256.ofNat 32) mem = key.currency1)
    (hptr : 64 ≤ (ptr+UInt256.ofNat 32).toNat)
    (hmem : (ptr+UInt256.ofNat 32).toNat+32 ≤ mem.size)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) I g s0 ⟨13906⟩
      (ptr :: delta :: accountWord target :: ret :: R) mem aw rdata evm.accountMap k C) :
    functionResultTrace (deployedRuntime v) g s0 (fun post values =>
      post = accountPoolPost evm key delta target ∧ values = none ∧ ∃ aw' k' C',
        C+Cₘ aw' ≤ C'+Cₘ aw ∧ RD (deployedRuntime v) I g s0 ret R (accountPoolMemory mem key delta target)
          aw' rdata post.accountMap k' C') (accountPoolResult f evm key delta target) := by
  have rd0 := poolManagerBlocks.poolManager_block_13906 (by simp only [List.length_cons]; omega)
    (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
  change RD (deployedRuntime v) I g s0 ⟨12528⟩
    (UInt256.land (memLoad ptr mem) solcAddrMask :: UInt256.sar (UInt256.ofNat 128) delta ::
      accountWord target :: ⟨13953⟩ :: ptr :: ⟨32⟩ :: solcAddrMask :: delta ::
      accountWord target :: ⟨12705⟩ :: ret :: R) mem _ rdata evm.accountMap _ _ at rd0
  rw [hkey0, ← accountWord_fromId] at rd0
  have hr0 := accountDeltaCallCostTrace (ret := ⟨13953⟩)
    (R := ptr :: ⟨32⟩ :: solcAddrMask :: delta :: accountWord target :: ⟨12705⟩ :: ret :: R)
    (delta := balanceDeltaComponent false delta) (currency := accountPoolCurrency key false)
    (accountPoolStepFrame f delta false) (accountPoolAccountRet false) v
    (by simp only [List.length_cons]; omega) hI (solcAddrMask_clean (accountWord_canonical _))
    (balanceDeltaComponent_fits false delta) (by rw [deployedRuntime_jumps]; jump_dest)
    (by simpa only [balanceDeltaComponent, Bool.false_eq_true, if_false, balanceDeltaAmount0,
      wordOfInt_signed] using rd0)
  have hsteps : blockResultTrace (deployedRuntime v) g s0 (fun _ post =>
      post = accountPoolPost evm key delta target ∧ ∃ aw' k' C',
        C+Cₘ aw' ≤ C'+Cₘ aw ∧ RD (deployedRuntime v) I g s0 ret R (accountPoolMemory mem key delta target)
          aw' rdata post.accountMap k' C') (fun _ _ => False)
      (accountPoolBlockResult f evm key delta target) := by
    apply blockResultTrace_continueBlock hr0
    intro f1 post _ hh
    obtain ⟨rfl, aw1, k1, C1, hc0, rd1⟩ := hh
    have rd2 := poolManagerBlocks.poolManager_block_13953 (by simp only [List.length_cons]; omega)
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd1
    change RD (deployedRuntime v) I g s0 ⟨12528⟩
      (UInt256.land (memLoad (ptr+UInt256.ofNat 32)
          (accountDeltaMemory mem target (accountPoolCurrency key false) (balanceDeltaComponent false delta))) solcAddrMask ::
        UInt256.signextend (UInt256.ofNat 15) delta :: accountWord target :: ⟨12705⟩ :: ret :: R)
      _ _ rdata _ _ _ at rd2
    rw [accountDeltaMemory_load _ _ _ _ _ hptr hmem, hkey1, ← accountWord_fromId] at rd2
    have hr1 := accountDeltaCallCostTrace (ret := ⟨12705⟩) (R := ret :: R)
      (delta := balanceDeltaComponent true delta) (currency := accountPoolCurrency key true)
      (accountPoolStepFrame f1 delta true) (accountPoolAccountRet true) v
      (by simp only [List.length_cons]; omega) ((accountDeltaPost_env _ _ _ _).trans hI)
      (solcAddrMask_clean (accountWord_canonical _)) (balanceDeltaComponent_fits true delta)
      (by rw [deployedRuntime_jumps]; jump_dest)
      (by simpa only [balanceDeltaComponent, if_true, balanceDeltaAmount1, wordOfInt_signed] using rd2)
    apply blockResultTrace_mono hr1
    intro f2 post _ hh
    obtain ⟨rfl, aw2, k2, C2, hc1, rd3⟩ := hh
    have rd4 := poolManagerBlocks.poolManager_block_12705 (by omega) hret rd3
    refine ⟨rfl, _, _, _, ?_, rd4⟩
    dsimp only [memExpansionCost] at hc0 hc1 ⊢
    omega
  apply functionResultTrace_finishNormal hsteps
  intro f2 post _ hh
  exact ⟨hh.1, rfl, hh.2⟩

theorem accountPoolTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {aw ptr delta ret : UInt256} {key : PoolKeyWords} {target : AccountAddress}
    {k C : Nat} {R : List UInt256} (f : Frame) (v : PoolManagerImmutables)
    (hstack : R.length+16 ≤ 1024) (hI : evm.executionEnv = I)
    (hkey0 : memLoad ptr mem = key.currency0)
    (hkey1 : memLoad (ptr+UInt256.ofNat 32) mem = key.currency1)
    (hptr : 64 ≤ (ptr+UInt256.ofNat 32).toNat)
    (hmem : (ptr+UInt256.ofNat 32).toNat+32 ≤ mem.size)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) I g s0 ⟨13906⟩
      (ptr :: delta :: accountWord target :: ret :: R) mem aw rdata evm.accountMap k C) :
    functionResultTrace (deployedRuntime v) g s0 (fun post values =>
      post = accountPoolPost evm key delta target ∧ values = none ∧ ∃ aw' k' C',
        RD (deployedRuntime v) I g s0 ret R (accountPoolMemory mem key delta target)
          aw' rdata post.accountMap k' C') (accountPoolResult f evm key delta target) := by
  have hr := accountPoolCostTrace f v hstack hI hkey0 hkey1 hptr hmem hret h
  apply functionResultTrace_mono hr
  intro post values ht
  obtain ⟨hp, hv, aw1, k1, C1, _, rd⟩ := ht
  exact ⟨hp, hv, aw1, k1, C1, rd⟩

end Benchmarks.UniswapV4PoolManager
