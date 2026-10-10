import Benchmarks.UniswapV3.Pool.FlashFeesTrace
import Benchmarks.UniswapV3.Pool.FlashTransfers
import Benchmarks.UniswapV3.Pool.FlashCallbackTail

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem flashBodyTailX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 evm : EVM.State} {k C : Nat} {aw p liquidity len start : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables} (a : FlashArgs)
    (rd : RD (deployedRuntime v) ee g s0 ⟨6595⟩
      (liquidity :: len :: start :: a.amount1 :: a.amount0 :: EVM.word a.recipient.val :: ⟨857⟩ :: R)
      mem aw rdata σ k C) (hs : SourceState s0 ee σ evm) (hperm : ee.perm = true)
    (hm : HeapMemory mem aw p)
    (hzero : memLoad (UInt256.ofNat 96) (balanceInputMem mem p ee.codeOwner) = ⟨0⟩)
    (hdata : a.data = ee.calldata.extract start.toNat (start.toNat + len.toNat))
    (hc : start.toNat + len.toNat ≤ ee.calldata.size) (hl : len.toNat ≤ 2 ^ 32)
    (hliquidity : liquidity.toNat < 2 ^ 128)
    (hb : p.toNat + 2 ^ 143 ≤ 2 ^ 200) (hov : R.length + 34 ≤ 1024) :
    (RDrev (deployedRuntime v) g s0 ∧
      ExecBlock config (flashReadyFrame v a liquidity) evm (flashTransition.body.drop 6) .reverted) ∨
    ∃ evm' locals',
      ExecBlock config (flashReadyFrame v a liquidity) evm (flashTransition.body.drop 6)
        (.ok {contract := contract, locals := locals', immutables := immStore v} evm') ∧
      RDret (deployedRuntime v) g s0 evm'.accountMap ByteArray.empty := by
  rcases flashFeesX (v := v) rd (by evm_ov) with
    ⟨rdBad, hbad⟩ | ⟨hv0, hv1, kFees, CFees, rdFees⟩
  · refine Or.inl ⟨rdBad, ?_⟩
    rw [← List.take_append_drop 2 (flashTransition.body.drop 6)]
    exact execBlockAppendReverted (flashFeesSourceReverts v evm a liquidity hbad)
  · let fee0 := fullMathRoundResult a.amount0 (poolFeeWord v) ⟨1000000⟩
    let fee1 := fullMathRoundResult a.amount1 (poolFeeWord v) ⟨1000000⟩
    have hsourceFees := flashFeesSource v evm a liquidity hv0 hv1
    rcases flashBalancesX (v := v) (flashFeesFrame v a liquidity fee0 fee1).locals false
        rdFees hs hm hzero (by omega) (by evm_ov) with
      ⟨rdBad, hbad⟩ | ⟨evm1, σ1, out1, mem1, aw1, p1, before0, before1,
        k1, C1, hs1, hsourceBalances, rd1, hm1, hmem1, hz1, hp1⟩
    · refine Or.inl ⟨rdBad, ?_⟩
      rw [← List.take_append_drop 2 (flashTransition.body.drop 6)]
      apply execBlock_append_ok hsourceFees
      change ExecBlock _ _ _ (flashTransition.body.drop 8) _
      rw [← List.take_append_drop 2 (flashTransition.body.drop 8)]
      rw [flashBalanceStmts_eq] at hbad
      exact execBlockAppendReverted hbad
    · have hvalues := flashCallValues_initial v a liquidity fee0 fee1 before0 before1
      rw [flashBalanceStmts_eq] at hsourceBalances
      rcases flashTransfersX (v := v) a _ rd1 hs1 hperm hvalues hm1 hmem1 hz1
          (by omega) (by evm_ov) with
        ⟨rdBad, hbad⟩ | ⟨evm2, σ2, locals2, out2, mem2, aw2, p2, k2, C2,
          hs2, hsourceTransfers, hvalues2, rd2, hm2, hmem2, hz2, hp2⟩
      · refine Or.inl ⟨rdBad, ?_⟩
        rw [← List.take_append_drop 2 (flashTransition.body.drop 6)]
        apply execBlock_append_ok hsourceFees
        change ExecBlock _ _ _ (flashTransition.body.drop 8) _
        rw [← List.take_append_drop 2 (flashTransition.body.drop 8)]
        apply execBlock_append_ok hsourceBalances
        change ExecBlock _ _ _ (flashTransition.body.drop 10) _
        rw [← List.take_append_drop 2 (flashTransition.body.drop 10)]
        exact execBlockAppendReverted hbad
      · rcases flashCallbackTailX (v := v) a locals2 rd2 hs2 hperm hvalues2 hm2 hmem2 hz2
            hdata hc hl hliquidity (by omega) (by evm_ov) with
          ⟨rdBad, hbad⟩ | ⟨evm3, locals3, hsourceTail, rdDone⟩
        · refine Or.inl ⟨rdBad, ?_⟩
          rw [← List.take_append_drop 2 (flashTransition.body.drop 6)]
          apply execBlock_append_ok hsourceFees
          change ExecBlock _ _ _ (flashTransition.body.drop 8) _
          rw [← List.take_append_drop 2 (flashTransition.body.drop 8)]
          apply execBlock_append_ok hsourceBalances
          change ExecBlock _ _ _ (flashTransition.body.drop 10) _
          rw [← List.take_append_drop 2 (flashTransition.body.drop 10)]
          exact execBlock_append_ok hsourceTransfers hbad
        · refine Or.inr ⟨evm3, locals3, ?_, rdDone⟩
          rw [← List.take_append_drop 2 (flashTransition.body.drop 6)]
          apply execBlock_append_ok hsourceFees
          change ExecBlock _ _ _ (flashTransition.body.drop 8) _
          rw [← List.take_append_drop 2 (flashTransition.body.drop 8)]
          apply execBlock_append_ok hsourceBalances
          change ExecBlock _ _ _ (flashTransition.body.drop 10) _
          rw [← List.take_append_drop 2 (flashTransition.body.drop 10)]
          exact execBlock_append_ok hsourceTransfers hsourceTail

end Benchmarks.UniswapV3.Pool
