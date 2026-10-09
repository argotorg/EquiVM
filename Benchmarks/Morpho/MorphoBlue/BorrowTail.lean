import Benchmarks.Morpho.MorphoBlue.BorrowTailGuards
import Benchmarks.Morpho.MorphoBlue.MarketTransferPair
import Benchmarks.Morpho.MorphoBlue.MarketTransferEvents

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

theorem morphoBorrowTail {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 evm : State} {mem out : ByteArray} {aw fp assets shares account receiver : UInt256} {σ : AccountMap}
    {k C : Nat} (p : MarketParamsWords) (locals imms : Store) (z : Bool) (hc : p.Canonical)
    (hr : receiver.toNat < EVM.addressModulus)
    (hl : MarketTransferLocals p assets shares account receiver locals) (hs : SourceState s0 ee σ evm) (hp : ee.perm = true)
    (hm : MorphoHeap mem fp 192) (hsize : 160 ≤ mem.size) (hptr : 160 ≤ fp.toNat)
    (hget : locals.get? "__memory" = some (.int (Int.ofNat (fp.toNat + 128))))
    (hz : locals.get? "__c9" = some (.bool z))
    (hzero : memLoad (UInt256.ofNat 96) mem = UInt256.ofNat 0)
    (htoken : memLoad (UInt256.ofNat 128) mem = p.loanToken)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 8794)
      ((if z then UInt256.ofNat 1 else UInt256.ofNat 0) :: borrowHealthTail p.id assets shares account receiver [])
      mem aw out σ k C) :
    ReturnBlockRefines config (deployedRuntime v) ee g s0
      { contract := contract, locals := locals, immutables := imms } evm
      (borrowTransition.body.drop 22) borrowTransition.returnType := by
  have hez : evalExpr? config { contract := contract, locals := locals, immutables := imms } evm
      (.var "__c9") = .ok (.bool z) := by simp only [evalExpr?, hz, EvalResult.ofOption]
  have hcheck := morphoBorrowHealthCheck (v := v) z (by change 37 ≤ 1024; decide) (hm.weaken (by decide))
    (by have hh := hm.space; omega) h
  cases z
  · exact .reverted (ExecBlock.consRevert (ExecStmt.requireFalse hez)) hcheck
  obtain ⟨a1, k1, C1, rd1, hm1, had1⟩ := hcheck
  have ab1 : StateBlock config { contract := contract, locals := locals, immutables := imms } evm
      (borrowTransition.body.drop 22) { contract := contract, locals := locals, immutables := imms } evm
      (borrowTransition.body.drop 23) := StateBlock.start.step (ExecStmt.requireTrue hez)
  have hg := marketLiquidityGuard_eval p locals imms evm hl.toMarketLocals
  rw [hs.env, ← hs.accounts] at hg
  rcases morphoBorrowLiquidity (v := v) (by change 36 ≤ 1024; decide) hm1
      (by have hh := hm.space; rw [had1.cursor]; omega) rd1 with
    ⟨hbad, hrev⟩ | ⟨hgood, a2, k2, C2, rd2, hm2, had2⟩
  · exact .reverted (ab1.reverts (ExecStmt.requireFalse (by
      simpa only [decide_eq_false (Nat.not_le_of_gt hbad)] using hg))) hrev
  · have hguard : ExecStmt config { contract := contract, locals := locals, immutables := imms }
        evm borrowTransition.body[23]! (.ok { contract := contract, locals := locals, immutables := imms } evm) :=
      ExecStmt.requireTrue (by simpa only [decide_eq_true hgood] using hg)
    have hab : StateBlock config { contract := contract, locals := locals, immutables := imms } evm
        (borrowTransition.body.drop 22) { contract := contract, locals := locals, immutables := imms } evm
        (borrowTransition.body.drop 25) := (ab1.step hguard).step (hl.emit imms evm "Borrow")
    have had := had1.trans had2
    have hm3 := hm2.event (UInt256.ofNat ee.source.val) assets shares
    have hpe := hm2.eventPrefix (UInt256.ofNat ee.source.val) assets shares
    have hpref := had.preserves.trans (hpe.mono (by rw [had.cursor]; omega))
    let m2 := morphoLiquidityMem (twoWordHashMem p.id (UInt256.ofNat 3) (morphoHealthMem mem))
    have hz1 : memLoad (UInt256.ofNat 96)
        (accrueEventMem m2 (UInt256.ofNat ee.source.val) assets shares) = UInt256.ofNat 0 := by
      rw [memoryPrefix_memLoad hpref _ (by decide) (by change 128 ≤ fp.toNat; omega) (by change 128 ≤ mem.size; omega)]
      exact hzero
    have ht1 : memLoad (UInt256.ofNat 128)
        (accrueEventMem m2 (UInt256.ofNat ee.source.val) assets shares) = p.loanToken := by
      rw [memoryPrefix_memLoad hpref (UInt256.ofNat 128) (by decide) hptr hsize]
      exact htoken
    obtain ⟨a3, k3, C3, rd3⟩ := morphoBlocks.morpho_block_8850_packed (immWords := wordsOf (immStore v))
      (by change 14 ≤ 1024; decide) hp (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rd2
    change RD _ _ _ _ _
      [UInt256.land (memLoad (UInt256.ofNat 128)
        (accrueEventMem m2 (UInt256.ofNat ee.source.val) assets shares)) solcAddrMask,
        receiver, assets, UInt256.ofNat 8920, UInt256.ofNat 32, shares, assets]
      (accrueEventMem m2 (UInt256.ofNat ee.source.val) assets shares) _ _ _ _ _ at rd3
    rw [ht1, solcAddrMask_clean hc.1] at rd3
    exact (morphoMarketTransferPairAt (v := v) ⟨2, by decide⟩ p locals imms "__c10" (by decide) (by decide)
      hc.1 hr hl hs hm3 (by have hh := hpref.size; omega) (by rw [had.cursor]; omega)
      (by rw [had.cursor]; exact hget) hz1 rd3).prepend hab

end Benchmarks.Morpho.MorphoBlue
