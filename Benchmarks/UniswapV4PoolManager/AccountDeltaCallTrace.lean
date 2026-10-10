import Benchmarks.UniswapV4PoolManager.AccountDeltaTrace
import Benchmarks.UniswapV4PoolManager.ConditionalMappingMemory
import Benchmarks.UniswapV4PoolManager.BlockResultTrace
import Benchmarks.UniswapV4PoolManager.Signed128Range

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def accountDeltaMemory (mem : ByteArray) (target currency : AccountAddress) (delta : Int) : ByteArray :=
  conditionalHashMemory mem (accountWord target) (accountWord currency) (decide (delta ≠ 0))

theorem accountDeltaMemory_size (mem : ByteArray) (target currency : AccountAddress) (delta : Int)
    (hm : 64 ≤ mem.size) : (accountDeltaMemory mem target currency delta).size = mem.size :=
  conditionalHashMemory_size _ _ _ _ hm

theorem accountDeltaMemory_load (mem : ByteArray) (target currency : AccountAddress) (delta : Int)
    (read : UInt256) (hoff : 64 ≤ read.toNat) (hin : read.toNat+32 ≤ mem.size) :
    memLoad read (accountDeltaMemory mem target currency delta) = memLoad read mem :=
  conditionalHashMemory_loadWord _ _ _ _ _ hoff hin

theorem accountDeltaCallCostTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {aw ret currencyWord : UInt256} {target currency : AccountAddress} {delta : Int}
    {k C : Nat} {R : List UInt256} (f : Frame) (retVar : Ident) (v : PoolManagerImmutables)
    (hstack : R.length+9 ≤ 1024) (hI : evm.executionEnv = I)
    (hcurrency : UInt256.land currencyWord solcAddrMask = accountWord currency)
    (hd : signedFits ⟨128, by decide⟩ delta)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) I g s0 ⟨12528⟩
      (currencyWord :: EVM.wordOfInt delta :: accountWord target :: ret :: R)
      mem aw rdata evm.accountMap k C) :
    blockResultTrace (deployedRuntime v) g s0 (fun _ post =>
      post = accountDeltaPost evm target currency delta ∧ ∃ aw' k' C',
        C+Cₘ aw' ≤ C'+Cₘ aw ∧ RD (deployedRuntime v) I g s0 ret R (accountDeltaMemory mem target currency delta)
          aw' rdata post.accountMap k' C') (fun _ _ => False)
      (accountDeltaCallResult f evm target currency delta retVar) := by
  classical
  have hr := accountDeltaWordCostTrace v hstack hI hcurrency hd.1 hd.2 hret h
  unfold accountDeltaCostTraceResult at hr
  unfold accountDeltaCallResult
  by_cases hz : delta = 0
  · rw [if_pos hz] at hr ⊢
    exact ⟨by simp only [accountDeltaPost, if_pos hz], by
      simpa only [accountDeltaMemory, hz, ne_eq, not_true_eq_false, decide_false,
        conditionalHashMemory, Bool.false_eq_true, if_false] using hr⟩
  · rw [if_neg hz] at hr ⊢
    generalize hnext : currencyDeltaValue evm target currency + delta = next at hr ⊢
    by_cases hf : int256Fits next
    · rw [if_pos hf] at hr ⊢
      rw [hI]
      by_cases hp : I.perm = false
      · rw [if_pos hp] at hr ⊢
        exact hr
      · rw [if_neg hp] at hr ⊢
        exact ⟨rfl, by simpa only [accountDeltaMemory, decide_eq_true hz,
          conditionalHashMemory, if_true, currencyDeltaMemory] using hr⟩
    · rw [if_neg hf] at hr ⊢
      exact hr

theorem accountDeltaCallTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {aw ret currencyWord : UInt256} {target currency : AccountAddress} {delta : Int}
    {k C : Nat} {R : List UInt256} (f : Frame) (retVar : Ident) (v : PoolManagerImmutables)
    (hstack : R.length+9 ≤ 1024) (hI : evm.executionEnv = I)
    (hcurrency : UInt256.land currencyWord solcAddrMask = accountWord currency)
    (hd : signedFits ⟨128, by decide⟩ delta)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) I g s0 ⟨12528⟩
      (currencyWord :: EVM.wordOfInt delta :: accountWord target :: ret :: R)
      mem aw rdata evm.accountMap k C) :
    blockResultTrace (deployedRuntime v) g s0 (fun _ post =>
      post = accountDeltaPost evm target currency delta ∧ ∃ aw' k' C',
        RD (deployedRuntime v) I g s0 ret R (accountDeltaMemory mem target currency delta)
          aw' rdata post.accountMap k' C') (fun _ _ => False)
      (accountDeltaCallResult f evm target currency delta retVar) := by
  have hr := accountDeltaCallCostTrace f retVar v hstack hI hcurrency hd hret h
  apply blockResultTrace_mono hr
  intro ff post _ ht
  obtain ⟨hp, aw1, k1, C1, _, rd⟩ := ht
  exact ⟨hp, aw1, k1, C1, rd⟩

end Benchmarks.UniswapV4PoolManager
