import Benchmarks.UniswapV4PoolManager.AccountPoolMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager

def accountPoolCalleeFrame (f : Frame) (key : PoolKeyWords) (delta : UInt256) (target : AccountAddress) : Frame :=
  {f with locals := (((∅ : Store).insert "target" (.address target)).insert "delta"
    (.int (EVM.signed delta))).insert "key" (poolKeyValue key)}


theorem accountPoolCallCostTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {aw ptr delta ret : UInt256} {key : PoolKeyWords} {target : AccountAddress}
    {k C : Nat} {R : List UInt256} (f : Frame) (retVar : Ident) (v : PoolManagerImmutables)
    (hstack : R.length+16 ≤ 1024) (hI : evm.executionEnv = I)
    (hk : PoolKeyView mem ptr key) (hptr : 64 ≤ ptr.toNat)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) I g s0 ⟨13906⟩
      (ptr :: delta :: accountWord target :: ret :: R) mem aw rdata evm.accountMap k C) :
    blockResultTrace (deployedRuntime v) g s0 (fun f' post =>
      f' = {f with locals := f.locals.insert retVar .unit} ∧
      post = accountPoolPost evm key delta target ∧ ∃ aw' k' C', C+Cₘ aw' ≤ C'+Cₘ aw ∧
        RD (deployedRuntime v) I g s0 ret R (accountPoolMemory mem key delta target)
          aw' rdata post.accountMap k' C') (fun _ _ => False)
      (resumeCallResult f retVar (accountPoolResult (accountPoolCalleeFrame f key delta target) evm key delta target)) := by
  have h32 := uadd_word_ofNat_toNat ptr 32 (by have := hk.fits; omega)
  have h0 : memLoad ptr mem = key.currency0 := by
    simpa only [show ptr+UInt256.ofNat (32*0) = ptr from uint256_add_zero_right ptr] using hk.load (i := 0) rfl
  have hr := accountPoolCostTrace (accountPoolCalleeFrame f key delta target) v hstack hI h0 (hk.load (i := 1) rfl)
    (by omega) (by have := hk.inBounds; omega) hret h
  apply blockResultTrace_resumeCall hr
  intro cf post values _ ht
  obtain ⟨rfl, rfl, ht⟩ := ht
  exact ⟨rfl, rfl, ht⟩

theorem accountPoolCallTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {aw ptr delta ret : UInt256} {key : PoolKeyWords} {target : AccountAddress}
    {k C : Nat} {R : List UInt256} (f : Frame) (retVar : Ident) (v : PoolManagerImmutables)
    (hstack : R.length+16 ≤ 1024) (hI : evm.executionEnv = I)
    (hk : PoolKeyView mem ptr key) (hptr : 64 ≤ ptr.toNat)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) I g s0 ⟨13906⟩
      (ptr :: delta :: accountWord target :: ret :: R) mem aw rdata evm.accountMap k C) :
    blockResultTrace (deployedRuntime v) g s0 (fun f' post =>
      f' = {f with locals := f.locals.insert retVar .unit} ∧
      post = accountPoolPost evm key delta target ∧ ∃ aw' k' C',
        RD (deployedRuntime v) I g s0 ret R (accountPoolMemory mem key delta target)
          aw' rdata post.accountMap k' C') (fun _ _ => False)
      (resumeCallResult f retVar (accountPoolResult (accountPoolCalleeFrame f key delta target) evm key delta target)) := by
  have hr := accountPoolCallCostTrace f retVar v hstack hI hk hptr hret h
  apply blockResultTrace_mono hr
  intro ff post _ ht
  obtain ⟨hf, hp, aw', k', C', _, rd⟩ := ht
  exact ⟨hf, hp, aw', k', C', rd⟩

end Benchmarks.UniswapV4PoolManager
