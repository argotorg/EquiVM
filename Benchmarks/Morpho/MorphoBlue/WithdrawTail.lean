import Benchmarks.Morpho.MorphoBlue.WithdrawMarketRefine
import Benchmarks.Morpho.MorphoBlue.MarketLiquidity
import Benchmarks.Morpho.MorphoBlue.MarketTransferPair
import Benchmarks.Morpho.MorphoBlue.MarketTransferEvents

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

theorem withdrawEmit (p : MarketParamsWords) (assets shares account receiver : UInt256)
    (locals imms : Store) (evm : EVM.State) (hl : MarketTransferLocals p assets shares account receiver locals) :
    ExecStmt config { contract := contract, locals := locals, immutables := imms } evm
      withdrawTransition.body[20]! (.ok { contract := contract, locals := locals, immutables := imms } evm) := hl.emit imms evm "Withdraw"

theorem morphoWithdrawTail {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 evm : State} {mem out : ByteArray} {aw fp assets shares account receiver : UInt256} {σ : AccountMap}
    {k C : Nat} (p : MarketParamsWords) (locals imms : Store) (hc : p.Canonical)
    (hr : receiver.toNat < EVM.addressModulus)
    (hl : MarketTransferLocals p assets shares account receiver locals) (hs : SourceState s0 ee σ evm) (hp : ee.perm = true)
    (hm : MorphoHeap mem fp 160) (hsize : 160 ≤ mem.size) (hptr : 160 ≤ fp.toNat)
    (hget : locals.get? "__memory" = some (.int (Int.ofNat (fp.toNat + 64))))
    (hzero : memLoad (UInt256.ofNat 96) mem = UInt256.ofNat 0)
    (htoken : memLoad (UInt256.ofNat 128) mem = p.loanToken)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 12880)
      ([UInt256.ofNat 585, UInt256.isZero (UInt256.lt (marketFieldWord σ ee p.id 0)
        (marketFieldWord σ ee p.id 2)), UInt256.ofNat 7950] ++
        withdrawEventTail p.id assets shares account receiver []) mem aw out σ k C) :
    ReturnBlockRefines config (deployedRuntime v) ee g s0
      { contract := contract, locals := locals, immutables := imms } evm
      (withdrawTransition.body.drop 19) withdrawTransition.returnType := by
  have hg := marketLiquidityGuard_eval p locals imms evm hl.toMarketLocals
  rw [hs.env, ← hs.accounts] at hg
  rcases morphoMarketLiquidity (v := v) (by change 35 ≤ 1024; decide)
      (by rw [morphoPatchedValidJumps v]; jump_dest) (hm.weaken (by decide))
      (by have hb := hm.space; omega) h with ⟨hbad, hrev⟩ | ⟨hgood, a1, k1, C1, rd1, hm1, had⟩
  · exact .reverted (ExecBlock.consRevert (ExecStmt.requireFalse (by
      simpa only [decide_eq_false (Nat.not_le_of_gt hbad)] using hg))) hrev
  · have hguard : ExecStmt config { contract := contract, locals := locals, immutables := imms }
        evm withdrawTransition.body[19]! (.ok { contract := contract, locals := locals, immutables := imms } evm) :=
      ExecStmt.requireTrue (by simpa only [decide_eq_true hgood] using hg)
    have hab : StateBlock config { contract := contract, locals := locals, immutables := imms } evm
        (withdrawTransition.body.drop 19) { contract := contract, locals := locals, immutables := imms } evm
        (withdrawTransition.body.drop 21) :=
      (StateBlock.start.step hguard).step (withdrawEmit p assets shares account receiver locals imms evm hl)
    have hm2 := hm1.event (UInt256.ofNat ee.source.val) assets shares
    have hpe := hm1.eventPrefix (UInt256.ofNat ee.source.val) assets shares
    have hpref := had.preserves.trans (hpe.mono (by rw [had.cursor]; omega))
    have hz1 : memLoad (UInt256.ofNat 96)
        (accrueEventMem (morphoLiquidityMem mem) (UInt256.ofNat ee.source.val) assets shares) = UInt256.ofNat 0 := by
      rw [memoryPrefix_memLoad hpref _ (by decide) (by change 128 ≤ fp.toNat; omega) (by change 128 ≤ mem.size; omega)]
      exact hzero
    have ht1 : memLoad (UInt256.ofNat 128)
        (accrueEventMem (morphoLiquidityMem mem) (UInt256.ofNat ee.source.val) assets shares) = p.loanToken := by
      rw [memoryPrefix_memLoad hpref (UInt256.ofNat 128) (by decide) hptr hsize]
      exact htoken
    obtain ⟨a2, k2, C2, rd2⟩ := morphoBlocks.morpho_block_7950_packed (immWords := wordsOf (immStore v))
      (by decide) hp (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rd1
    change RD _ _ _ _ _
      [UInt256.land (memLoad (UInt256.ofNat 128)
        (accrueEventMem (morphoLiquidityMem mem) (UInt256.ofNat ee.source.val) assets shares)) solcAddrMask,
        receiver, assets, UInt256.ofNat 2752, shares, assets, UInt256.ofNat 64]
      (accrueEventMem (morphoLiquidityMem mem) (UInt256.ofNat ee.source.val) assets shares) _ _ _ _ _ at rd2
    rw [ht1, solcAddrMask_clean hc.1] at rd2
    exact (morphoMarketTransferPair (v := v) p locals imms "__c8" (by decide) (by decide) hc.1 hr hl hs hm2
      (by have hh := hpref.size; omega) (by rw [had.cursor]; omega)
      (by rw [had.cursor]; exact hget) hz1 rd2).prepend hab

end Benchmarks.Morpho.MorphoBlue
