import Benchmarks.UniswapV4PoolManager.PoolModifyAllocatedTrace
import Benchmarks.UniswapV4PoolManager.PoolModifyParamsMemory
import Benchmarks.UniswapV4PoolManager.PoolTicksTrace
import Benchmarks.UniswapV4PoolManager.FunctionFinishTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def poolModifyMemory (mem : ByteArray) (params ptr id : UInt256) (p : PoolModifyParams) (evm : State) : ByteArray :=
  poolModifyAllocatedMemory (poolModifyParamsMemory mem params ptr p) ptr id p evm

/-- The complete inlined Pool.modifyLiquidity trace, including construction of its parameter record. -/
theorem poolModifyTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State} {σ₀ : AccountMap}
    {mem rdata : ByteArray} {aw id params ptr x1 x2 x4 x5 x9 extra : UInt256} {p : PoolModifyParams}
    {k C : Nat} {R : List UInt256} (f : Frame)
    (v : PoolManagerImmutables) (hstack : R.length+34 ≤ 1024) (hI : evm.executionEnv = I) (hσ : evm.σ₀ = σ₀)
    (ho : p.owner = I.source)
    (hc : int24Canonical p.spacing) (hl : int24Canonical p.lower) (hu : int24Canonical p.upper)
    (hd : signedFits ⟨128, by decide⟩ p.delta)
    (hm : memLoad (UInt256.ofNat 128) mem = poolSlot id) (hmem : 160 ≤ mem.size)
    (hp : 160 ≤ params.toNat) (hpb : params.toNat+192 ≤ ptr.toNat) (hfit : ptr.toNat+128 ≤ solcMaxU64)
    (h : RD (deployedRuntime v) I g s0 ⟨5584⟩
      (ptr :: p.spacing :: p.salt :: x2 :: x1 :: x4 :: x5 :: p.upper :: EVM.wordOfInt p.delta ::
        p.lower :: x9 :: params :: extra :: R) mem aw rdata evm.accountMap k C) :
    functionResultTrace (deployedRuntime v) g s0
      (poolModifyReturnTrace v I g s0 σ₀ (poolModifyMemory mem params ptr id p evm)
        rdata x1 x2 x4 x5 x9 extra R)
      (poolModifyResult f evm id p) := by
  have hparams : params.toNat+192 < UInt256.size := by
    change params.toNat+192 < 2^256
    change ptr.toNat+128 ≤ 2^64-1 at hfit
    omega
  have hr := poolTicksTrace v (by simp only [List.length_cons]; omega) h
  by_cases ht : poolTicksValid p.lower p.upper
  · rw [if_pos ht] at hr
    obtain ⟨aw1, k1, C1, rd1⟩ := hr
    rw [poolModifyParamsMemory_eq I mem params ptr p ho hparams hd] at rd1
    have hm1 := (poolModifyParamsMemory_pool mem params ptr p hp hmem).trans hm
    have hsize := poolModifyParamsMemory_size mem params ptr p
    have howner := poolModifyParamsMemory_load mem params ptr p (i := 0) rfl hparams
    have hz : params+UInt256.ofNat (32*0) = params := uint256_add_zero_right params
    rw [hz] at howner
    have ha : UInt256.land (memLoad params (poolModifyParamsMemory mem params ptr p)) solcAddrMask = accountWord p.owner := by
      rw [howner]
      exact solcAddrMask_clean (accountWord_canonical p.owner)
    unfold poolModifyResult
    apply functionResultTrace_finishBlock
    rw [poolModifyBlockResult, if_pos ht]
    exact poolModifyAllocatedTrace f v hstack hI hσ hc hl hu ht hd hm1 (by omega)
      (poolModifyParamsMemory_free mem params ptr p (by omega)) ha
      (poolModifyParamsMemory_load mem params ptr p (i := 5) rfl hparams)
      (poolModifyParamsMemory_load mem params ptr p (i := 4) rfl hparams)
      hp (by omega) hpb (by omega) hfit rd1
  · rw [if_neg ht] at hr
    rw [poolModifyResult, poolModifyBlockResult, if_neg ht]
    exact hr

end Benchmarks.UniswapV4PoolManager
