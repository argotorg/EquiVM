import Benchmarks.UniswapV4PoolManager.PoolFeeInsideTrace
import Benchmarks.UniswapV4PoolManager.ReachCost

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager

theorem poolFeeInsidePaidTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {aw id lower upper x0 x1 x2 x3 x4 x5 delta x9 x10 : UInt256}
    {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+18 ≤ 1024) (hI : evm.executionEnv = I)
    (hm : memLoad (UInt256.ofNat 128) mem = poolSlot id) (hmem : 160 ≤ mem.size)
    (hl : int24Canonical lower) (hu : int24Canonical upper)
    (h5 : 5 ≤ aw.toNat) (hpaid : Cₘ aw ≤ C)
    (h : RD (deployedRuntime v) I g s0 ⟨5722⟩
      (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: upper :: delta :: lower :: x9 :: x10 :: R)
      mem aw rdata evm.accountMap k C) :
    ∃ k' C', Cₘ aw ≤ C' ∧ RD (deployedRuntime v) I g s0 ⟨5802⟩
      (poolFeeInsideOutputStack lower upper x0 x1 x2 x3 x4 x5 delta x9 x10
        (poolFeeInsideWord evm id (EVM.signed lower) (EVM.signed upper) false)
        (poolFeeInsideWord evm id (EVM.signed lower) (EVM.signed upper) true) R)
      (poolFeeInsideMemory mem id lower upper) aw rdata evm.accountMap k' C' := by
  have he : M aw (UInt256.ofNat 128) ⟨32⟩ = aw := memoryWords_eq_self (by change 128+32 ≤ _*32; omega)
  obtain ⟨kr, Cr, hle, rd⟩ := RD_retainCost (fun budget start hin => by
    have hr := poolFeeInsideExactTrace v hstack hI hm hmem hl hu hin
    rw [he] at hr
    exact hr) h
  exact ⟨kr, Cr, hpaid.trans hle, rd⟩

end Benchmarks.UniswapV4PoolManager
