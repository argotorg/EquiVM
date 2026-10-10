import Benchmarks.UniswapV4PoolManager.CheckedSignedAmountTrace
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_019

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

/-- All four signed amount calls in Pool.modifyLiquidity share the cast bridge at 6381. -/
theorem poolModifyCheckedAmountTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {aw a b castPC : UInt256} {delta : Int}
    {k C : Nat} {R : List UInt256} (f : Frame) (amountRet castRet : Ident)
    (one : Bool) (v : PoolManagerImmutables) (hstack : R.length+18 ≤ 1024)
    (ha : a.toNat < 2^160) (hb : b.toNat < 2^160) (hd : signedFits ⟨128, by decide⟩ delta)
    (hcast : (D_J (deployedRuntime v) 0).contains castPC = true)
    (h : RD (deployedRuntime v) I g s0 (if one then ⟨17610⟩ else ⟨17703⟩)
      (a :: b :: EVM.wordOfInt delta :: ⟨6381⟩ :: castPC :: R) mem aw rdata evm.accountMap k C) :
    blockResultTrace (deployedRuntime v) g s0 (fun _ post => post = evm ∧ ∃ k' C',
      RD (deployedRuntime v) I g s0 castPC (signedAmountWord one a b delta :: R)
        mem aw rdata post.accountMap k' C') (fun _ _ => False)
      (checkedSignedAmountResult f evm one a b delta amountRet castRet) :=
  checkedSignedAmountTrace f amountRet castRet one v hstack ha hb hd.1 hd.2
    (by rw [deployedRuntime_jumps]; jump_dest) hcast
    (fun hr => ⟨_, _, poolManagerBlocks.poolManager_block_6381
      (by simp only [List.length_cons]; omega)
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) hr⟩) h

end Benchmarks.UniswapV4PoolManager
