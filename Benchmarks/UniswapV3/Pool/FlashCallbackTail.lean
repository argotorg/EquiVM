import Benchmarks.UniswapV3.Pool.FlashCallValues
import Benchmarks.UniswapV3.Pool.FlashSettlement

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem flashCallbackTailX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 evm : EVM.State} {k C : Nat} {aw p before1 before0 fee1 fee0 liquidity len start : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (a : FlashArgs) (locals : Store)
    (rd : RD (deployedRuntime v) ee g s0 ⟨6827⟩
      (before1 :: before0 :: fee1 :: fee0 :: liquidity :: len :: start :: a.amount1 :: a.amount0 ::
        EVM.word a.recipient.val :: ⟨857⟩ :: R) mem aw rdata σ k C)
    (hs : SourceState s0 ee σ evm) (hperm : ee.perm = true)
    (hvalues : FlashCallValues locals a liquidity fee0 fee1 before0 before1)
    (hm : HeapMemory mem aw p) (hmem : 128 ≤ mem.size)
    (hzero : memLoad (UInt256.ofNat 96) mem = ⟨0⟩)
    (hdata : a.data = ee.calldata.extract start.toNat (start.toNat + len.toNat))
    (hc : start.toNat + len.toNat ≤ ee.calldata.size) (hl : len.toNat ≤ 2 ^ 32)
    (hliquidity : liquidity.toNat < 2 ^ 128)
    (hb : p.toNat + 2 ^ 141 ≤ 2 ^ 200) (hov : R.length + 33 ≤ 1024) :
    (RDrev (deployedRuntime v) g s0 ∧
      ExecBlock config {contract := contract, locals := locals, immutables := immStore v} evm
        (flashTransition.body.drop 12) .reverted) ∨
    ∃ evm' locals',
      ExecBlock config {contract := contract, locals := locals, immutables := immStore v} evm
        (flashTransition.body.drop 12)
        (.ok {contract := contract, locals := locals', immutables := immStore v} evm') ∧
      RDret (deployedRuntime v) g s0 evm'.accountMap ByteArray.empty := by
  rcases flashCallbackX (v := v)
      (frame := {contract := contract, locals := locals, immutables := immStore v})
      rd hs hperm hm hvalues.fee0 hvalues.fee1 (by rw [← hdata]; exact hvalues.data)
      hc hl (by omega) (by evm_ov) with
    ⟨rdBad, hbad⟩ | ⟨evm1, σ1, out1, aw1, k1, C1, hs1, hsourceCallback, rd1, hm1, hpref1⟩
  · refine Or.inl ⟨rdBad, ?_⟩
    rw [← List.take_append_drop 3 (flashTransition.body.drop 12)]
    exact execBlockAppendReverted hbad
  · let frame1 := flashCallbackDoneFrame
      {contract := contract, locals := locals, immutables := immStore v} ee.source
    have hvalues1 : FlashCallValues frame1.locals a liquidity fee0 fee1 before0 before1 :=
      hvalues.callback (frame := {contract := contract, locals := locals, immutables := immStore v})
        ee.source
    have hmem1 : 128 ≤ (flashCallbackMem mem p fee0 fee1 ee.calldata start len).size :=
      le_trans hmem hpref1.size
    have hz1 : memLoad (UInt256.ofNat 96)
        (flashCallbackMem mem p fee0 fee1 ee.calldata start len) = ⟨0⟩ := by
      rw [MemoryPrefix.memLoad hpref1 (UInt256.ofNat 96) (by decide)
        (by exact hm.lower) hmem, hzero]
    rcases flashBalancesX (v := v) frame1.locals true rd1 hs1 hm1
        (balanceInputMem_zero hm1 ee.codeOwner hmem1 hz1) (by omega) (by evm_ov) with
      ⟨rdBad, hbad⟩ | ⟨evm2, σ2, out2, mem2, aw2, p2, after0, after1,
        k2, C2, hs2, hsourceBalances, rd2, hm2, hmem2, hz2, hp2⟩
    · refine Or.inl ⟨rdBad, ?_⟩
      rw [← List.take_append_drop 3 (flashTransition.body.drop 12)]
      apply execBlock_append_ok hsourceCallback
      change ExecBlock _ _ _ (flashTransition.body.drop 15) _
      rw [← List.take_append_drop 2 (flashTransition.body.drop 15)]
      rw [flashBalanceStmts_eq] at hbad
      exact execBlockAppendReverted hbad
    · have hvalues2 := hvalues1.balances v after0 after1
      rcases flashSettlementX (v := v) a.recipient _ rd2 hs2 hperm hvalues2.2 hvalues2.1
          hliquidity hov with ⟨rdBad, hbad⟩ | ⟨evm3, locals3, hsourceTail, rdDone⟩
      · refine Or.inl ⟨rdBad, ?_⟩
        rw [← List.take_append_drop 3 (flashTransition.body.drop 12)]
        apply execBlock_append_ok hsourceCallback
        change ExecBlock _ _ _ (flashTransition.body.drop 15) _
        rw [← List.take_append_drop 2 (flashTransition.body.drop 15)]
        rw [flashBalanceStmts_eq] at hsourceBalances
        exact execBlock_append_ok hsourceBalances hbad
      · refine Or.inr ⟨evm3, locals3, ?_, rdDone⟩
        rw [← List.take_append_drop 3 (flashTransition.body.drop 12)]
        apply execBlock_append_ok hsourceCallback
        change ExecBlock _ _ _ (flashTransition.body.drop 15) _
        rw [← List.take_append_drop 2 (flashTransition.body.drop 15)]
        rw [flashBalanceStmts_eq] at hsourceBalances
        exact execBlock_append_ok hsourceBalances hsourceTail

end Benchmarks.UniswapV3.Pool
