import Benchmarks.UniswapV4PoolManager.PoolSwapBodyReturn
import Benchmarks.UniswapV4PoolManager.PoolSwapPreludeSource
import Benchmarks.UniswapV4PoolManager.PoolSwapPreludeActiveWords

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem poolSwapBodyCorrect {I : ExecutionEnv} {g : Sat256} {s0 evm : State} {f : Frame}
    {mem rdata : ByteArray} {aw id state params ret : UInt256} {p : PoolSwapParamsWords}
    {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+36 ≤ 1024) (hI : evm.executionEnv = I)
    (hσ0 : evm.σ₀ = s0.σ₀)
    (hf : f.contract = contract) (hs : f.locals.get? "self" = some (poolRefValue id))
    (hp : f.locals.get? "params" = some (poolSwapParamsValue p))
    (hm : WordStructView mem params (poolSwapParamsWordList p))
    (hparams : 128 ≤ params.toNat) (hb : params.toNat+160 ≤ state.toNat)
    (hfit : state.toNat+352 ≤ solcMaxU64) (hfree : memLoad (UInt256.ofNat 64) mem = state)
    (hspacing : int24Canonical p.tickSpacing) (hlimit : p.priceLimit.toNat < 2^160)
    (hoverride : p.lpFeeOverride.toNat < 2^24) (hpaid : Cₘ aw ≤ C)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) I g s0 ⟨18777⟩
      ([poolSlot id, params, ret]++R) mem aw rdata evm.accountMap k C) :
    X (g.toNat+1) (D_J (deployedRuntime v) 0) s0 = .error .OutOfGass ∨
    ∃ result, ExecFuncBody config f evm poolSwapFunction.body result ∧
      functionResultTrace (deployedRuntime v) g s0
        (poolSwapBodyReturn v I g s0 evm mem rdata id state params ret p R C) result := by
  have hsource := poolSwapPreludeSource (evm := evm) hf hs hp hoverride
  have htrace := poolSwapPreludeTrace v (by omega) hI hm hparams hb hfit hfree hlimit hret h
  have hbody : poolSwapFunction.body = poolSwapFunction.body.take 28 ++ poolSwapFunction.body.drop 28 :=
    (List.take_append_drop 28 poolSwapFunction.body).symm
  unfold poolSwapPreludeResult at hsource
  by_cases ho : poolSwapLPFeeValid p.lpFeeOverride
  · rw [if_pos ho] at hsource htrace
    unfold poolSwapGuardsResult at hsource
    by_cases hmode : poolSwapModeValid (poolSwapInitialFee evm id p) p.amountSpecified
    · rw [if_pos hmode] at hsource htrace
      by_cases hz : p.amountSpecified = ⟨0⟩
      · rw [if_pos hz] at hsource htrace
        obtain ⟨k1, C1, hc1, hp1, rd1⟩ := htrace
        refine .inr ⟨.returned (poolSwapFeesFrame f evm id p) evm
          (some (poolSwapReturnValues ⟨0⟩ (poolSwapInitialFee evm id p) ⟨0⟩
            (poolSwapInitialResult (poolSlot0Word evm id) (poolLiquidityWord evm id)))), ?_, ?_⟩
        · apply ExecFuncBody.execBlockRet
          rw [hbody]
          exact execBlock_append_term hsource (by intros; intro he; cases he)
        · exact .inl ⟨rfl, rfl, _, k1, C1, hc1, by omega, rd1⟩
      · rw [if_neg hz] at hsource htrace
        by_cases hl : poolSwapLimitValid (poolSlot0Word evm id) p.priceLimit p.zeroForOne
        · rw [if_pos hl] at hsource htrace
          obtain ⟨k1, C1, hc1, hp1, rd1⟩ := htrace
          have hfitWord : state.toNat+352 < UInt256.size := by
            change state.toNat+352 < 2^256
            change state.toNat+352 ≤ 2^64-1 at hfit
            omega
          let q : PoolSwapLoopWords := ⟨poolSwapInitialStep evm id p.zeroForOne,
            poolSwapInitialResult (poolSlot0Word evm id) (poolLiquidityWord evm id), p.amountSpecified, ⟨0⟩, ⟨0⟩⟩
          have hinv : PoolSwapLoopInvariant (poolSwapPreludeFrame f evm id p)
              (poolSwapPreludeMem mem evm id state p.zeroForOne) id (state+UInt256.ofNat 96) state params
              (poolSwapInitialFee evm id p) (poolSwapProtocolWord (poolSlot0Word evm id) p.zeroForOne) p q :=
            ⟨poolSwapPreludeLoopLocals hf hs hp, poolSwapPreludeMemory_view hm evm id hparams hb hfitWord,
              solcAddrMask_result_canonical _, slot0TickWord_canonical _, poolLiquidity_bound evm id⟩
          have hlocals := poolSwapPreludeLocals (evm := evm) hf hs hp
          have ha1 : PoolSwapActiveWords
              (poolSwapPreludeAW aw state params (poolSwapInitialFee evm id p))
              (state+UInt256.ofNat 96) state params :=
            poolSwapStepFillAW_active _ (by omega) hb hfitWord
          rcases poolSwapLoopFinishCorrect v hstack hI hσ0 hinv hlocals.slot hlocals.delta hspacing hlimit
              (poolSwapInitialFee_bound evm id p) (poolSwapProtocolWord_bound _ _) ha1 (by omega)
              hret rd1 with hog | ⟨result, ht, hrt⟩
          · exact .inl hog
          · have hfull : ExecBlock config f evm poolSwapFunction.body result := by
              rw [hbody]
              exact execBlock_append hsource ht
            have hr : functionResultTrace (deployedRuntime v) g s0
                (poolSwapBodyReturn v I g s0 evm mem rdata id state params ret p R C) result :=
              functionResultTrace_mono hrt (fun _ _ hh => poolSwapBodyReturn_of_loop hc1 hh)
            exact .inr ⟨result, execFuncBody_of_trace hfull hr, hr⟩
        · rw [if_neg hl] at hsource htrace
          refine .inr ⟨.reverted, .execBlockRevert ?_, htrace⟩
          rw [hbody]
          exact execBlock_reverted_append hsource
    · rw [if_neg hmode] at hsource htrace
      refine .inr ⟨.reverted, .execBlockRevert ?_, htrace⟩
      rw [hbody]
      exact execBlock_reverted_append hsource
  · rw [if_neg ho] at hsource htrace
    refine .inr ⟨.reverted, .execBlockRevert ?_, htrace⟩
    rw [hbody]
    exact execBlock_reverted_append hsource

end Benchmarks.UniswapV4PoolManager
