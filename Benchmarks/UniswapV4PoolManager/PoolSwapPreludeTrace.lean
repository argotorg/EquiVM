import Benchmarks.UniswapV4PoolManager.PoolSwapAllocateTrace
import Benchmarks.UniswapV4PoolManager.PoolSwapFeesTrace
import Benchmarks.UniswapV4PoolManager.PoolSwapGuardsTrace
import Benchmarks.UniswapV4PoolManager.PoolSwapStepInitTrace
import Benchmarks.UniswapV4PoolManager.PoolSwapAllocatedMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def poolSwapPreludeLoadedAW (aw state params : UInt256) : UInt256 :=
  poolSwapLoadedAW (poolSwapAllocateAW aw) state params
def poolSwapPreludeZeroAW (aw state params fee : UInt256) : UInt256 :=
  poolSwapZeroAW (poolSwapPreludeLoadedAW aw state params) fee params
def poolSwapPreludeAW (aw state params fee : UInt256) : UInt256 :=
  poolSwapStepInitAW (poolSwapGuardsAW (poolSwapPreludeLoadedAW aw state params) fee params) (state+UInt256.ofNat 96)

theorem poolSwapPreludeTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {aw id state params ret : UInt256} {p : PoolSwapParamsWords}
    {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+17 ≤ 1024) (hI : evm.executionEnv = I)
    (hm : WordStructView mem params (poolSwapParamsWordList p))
    (hp : 128 ≤ params.toNat) (hb : params.toNat+160 ≤ state.toNat)
    (hfit : state.toNat+352 ≤ solcMaxU64) (hfree : memLoad (UInt256.ofNat 64) mem = state)
    (hl : p.priceLimit.toNat < 2^160) (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) I g s0 ⟨18777⟩
      ([poolSlot id, params, ret]++R) mem aw rdata evm.accountMap k C) :
    if poolSwapLPFeeValid p.lpFeeOverride then
      if poolSwapModeValid (poolSwapInitialFee evm id p) p.amountSpecified then
        if p.amountSpecified = ⟨0⟩ then
          ∃ k' C', C ≤ C' ∧
            C+Cₘ (poolSwapPreludeZeroAW aw state params (poolSwapInitialFee evm id p)) ≤ C'+Cₘ aw ∧
            RD (deployedRuntime v) I g s0 ret
            ([state, poolSwapInitialFee evm id p, ⟨0⟩, ⟨0⟩]++R) (poolSwapAllocatedMem mem evm id state)
            (poolSwapPreludeZeroAW aw state params (poolSwapInitialFee evm id p)) rdata evm.accountMap k' C'
        else if poolSwapLimitValid (poolSlot0Word evm id) p.priceLimit p.zeroForOne then
          ∃ k' C', C ≤ C' ∧
            C+Cₘ (poolSwapPreludeAW aw state params (poolSwapInitialFee evm id p)) ≤ C'+Cₘ aw ∧
            RD (deployedRuntime v) I g s0 ⟨19155⟩
            ([p.amountSpecified, ret, params, ⟨0⟩, poolSlot0Word evm id, poolSwapInitialFee evm id p,
              poolSwapProtocolWord (poolSlot0Word evm id) p.zeroForOne, ⟨0⟩, UInt256.fromBool (!p.zeroForOne),
              state+UInt256.ofNat 96, poolSlot id, state]++R)
            (poolSwapPreludeMem mem evm id state p.zeroForOne)
            (poolSwapPreludeAW aw state params (poolSwapInitialFee evm id p)) rdata evm.accountMap k' C'
        else RDrev (deployedRuntime v) g s0
      else RDrev (deployedRuntime v) g s0
    else RDrev (deployedRuntime v) g s0 := by
  have hf : state.toNat+352 < UInt256.size := by
    change state.toNat+352 < 2^256
    change state.toNat+352 ≤ 2^64-1 at hfit
    omega
  have h96 := uadd_word_ofNat_toNat state 96 (by omega)
  have hparams0 := hm.write_disjoint 64 (state+UInt256.ofNat 96) (.inr (by omega))
  have hparams1 := poolSwapResultZeroMem_preserves hparams0 (by omega) hb
  have hparams2 := poolSwapAllocatedMemory_params hm evm id hp hb (by omega)
  obtain ⟨k1, C1, hc1, hp1, rd1⟩ := poolSwapAllocateTrace v (by change R.length+10 ≤ 1024; omega) hfree (by omega) h
  have ht1 := poolSwapFeesTrace v hstack hI (by omega) hb (hparams1.load 2 (by decide : 2 < 5))
    (hparams1.load_zero (by decide : 0 < 5)) (hparams2.load 4 (by decide : 4 < 5)) rd1
  by_cases ho : poolSwapLPFeeValid p.lpFeeOverride
  · rw [if_pos ho] at ht1 ⊢
    obtain ⟨k2, C2, hc2, hp2, rd2⟩ := ht1
    have hpa : params.toNat+160 ≤ (poolSwapPreludeLoadedAW aw state params).toNat*32 := by
      have hs := poolSwapResultZeroAW_covers (poolSwapAllocateAW aw) (params := params) (by omega : state.toNat+96 < UInt256.size)
      unfold poolSwapPreludeLoadedAW
      rw [poolSwapLoadedAW_eq (by omega) hb]
      omega
    change C1+Cₘ (poolSwapPreludeLoadedAW aw state params) ≤ C2+Cₘ (poolSwapAllocateAW aw) at hp2
    have ht2 := poolSwapGuardsTrace v hstack (poolSwapInitialFee_bound evm id p) hl
      (hparams2.load_zero (by decide : 0 < 5)) (hparams2.load 3 (by decide : 3 < 5)) hret rd2
    by_cases hmode : poolSwapModeValid (poolSwapInitialFee evm id p) p.amountSpecified
    · rw [if_pos hmode] at ht2 ⊢
      by_cases hz : p.amountSpecified = ⟨0⟩
      · rw [if_pos hz] at ht2 ⊢
        obtain ⟨k3, C3, hc3, rd3⟩ := ht2
        refine ⟨k3, C3, by omega, ?_, rd3⟩
        rw [poolSwapPreludeZeroAW, poolSwapZeroAW_eq _ hpa]
        omega
      · rw [if_neg hz] at ht2 ⊢
        by_cases hlimit : poolSwapLimitValid (poolSlot0Word evm id) p.priceLimit p.zeroForOne
        · rw [if_pos hlimit] at ht2 ⊢
          obtain ⟨k3, C3, hc3, rd3⟩ := ht2
          obtain ⟨k4, C4, hc4, hp4, rd4⟩ := poolSwapStepInitTrace v (by omega) hI
            (poolSwapAllocatedMemory_free mem evm id state (by omega) (by omega))
            (by rw [h96]; omega) rd3
          refine ⟨k4, C4, by omega, ?_, rd4⟩
          change C3+Cₘ (poolSwapPreludeAW aw state params (poolSwapInitialFee evm id p)) ≤
            C4+Cₘ (poolSwapGuardsAW (poolSwapPreludeLoadedAW aw state params) (poolSwapInitialFee evm id p) params) at hp4
          rw [poolSwapGuardsAW_eq _ hpa] at hp4
          omega
        · rw [if_neg hlimit] at ht2 ⊢
          exact ht2
    · rw [if_neg hmode] at ht2 ⊢
      exact ht2
  · rw [if_neg ho] at ht1 ⊢
    exact ht1

end Benchmarks.UniswapV4PoolManager
