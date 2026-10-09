import Benchmarks.Morpho.MorphoBlue.RepayCallbackTail

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

theorem morphoRepayTail {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 evm : State} {mem out data : ByteArray} {aw fp srcOff len assets shares account debt : UInt256} {σ : AccountMap}
    {k C : Nat} (p : MarketParamsWords) (locals imms : Store) (hc : p.Canonical)
    (hl : SupplyLocals p assets shares account data locals) (hs : SourceState s0 ee σ evm) (hp : ee.perm = true)
    (hm : MorphoHeap mem fp 96) (hsize : 160 ≤ mem.size) (hptr : 160 ≤ fp.toNat)
    (hget : locals.get? "__memory" = some (.int (Int.ofNat fp.toNat)))
    (hget7 : locals.get? "__c7" = some (.int (Int.ofNat debt.toNat)))
    (hzero : memLoad (UInt256.ofNat 96) mem = UInt256.ofNat 0)
    (htoken : memLoad (UInt256.ofNat 128) mem = p.loanToken)
    (hfit : debt.toNat < 2 ^ 128)
    (hlen : len.toNat ≤ solcMaxU64) (hsrc : srcOff.toNat + len.toNat ≤ ee.calldata.size)
    (hdata : ee.calldata.readWithPadding srcOff.toNat len.toNat = data) (hdataSize : data.size = len.toNat)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 10767)
      (debt :: repayMarketTail p.id assets shares account srcOff len [])
      mem aw out σ k C) :
    ReturnBlockRefines config (deployedRuntime v) ee g s0
      { contract := contract, locals := locals, immutables := imms } evm
      (repayTransition.body.drop 18) repayTransition.returnType := by
  have hass : ExecStmt config { contract := contract, locals := locals, immutables := imms }
      evm repayTransition.body[18]!
      (.ok { contract := contract, locals := locals, immutables := imms }
        (storeMarketField evm p.id ⟨2, by decide⟩ debt)) := by
    have he : evalExpr? config { contract := contract, locals := locals, immutables := imms }
        evm (.var "__c7") = .ok (.int (Int.ofNat debt.toNat)) := by
      simp only [evalExpr?, hget7, EvalResult.ofOption]
    apply ExecStmt.assign he
    exact assignMarketField evm locals imms (.var "id") p.id ⟨2, by decide⟩ debt hfit hl.market (hl.evalId imms evm)
  let e1 := storeMarketField evm p.id ⟨2, by decide⟩ debt
  let σ1 := storeMarketFieldAccounts σ ee p.id ⟨2, by decide⟩ debt
  have hs1 : SourceState s0 ee σ1 e1 := storeMarketField_bridge hs p.id ⟨2, by decide⟩ debt
  have hevent : StateBlock config { contract := contract, locals := locals, immutables := imms } evm
      (repayTransition.body.drop 18) { contract := contract, locals := locals, immutables := imms } e1
      (repayTransition.body.drop 20) :=
    (StateBlock.start.step hass).step (repayEmit p assets shares account data locals imms e1 hl)
  obtain ⟨a1, k1, C1, rd1⟩ := morphoRepayStoreEvent (v := v) (by decide) hp (hm.hash p.id (UInt256.ofNat 3)).free hfit h
  obtain ⟨hm1, hpe⟩ := (hm.hash p.id (UInt256.ofNat 3)).twoWordEvent (by decide) assets shares
  have hpref := (heapAdvance_hash mem fp p.id (UInt256.ofNat 3)).preserves.trans hpe
  have hm2 := hm1.weaken (by decide : 0 ≤ 96)
  have hz1 : memLoad (UInt256.ofNat 96) (twoWordEventMem (twoWordHashMem p.id (UInt256.ofNat 3) mem) fp assets shares) = UInt256.ofNat 0 := by
    rw [memoryPrefix_memLoad hpref _ (by decide) (by change 128 ≤ fp.toNat; omega) (by change 128 ≤ mem.size; omega)]
    exact hzero
  have ht1 : memLoad (UInt256.ofNat 128) (twoWordEventMem (twoWordHashMem p.id (UInt256.ofNat 3) mem) fp assets shares) = p.loanToken := by
    rw [memoryPrefix_memLoad hpref (UInt256.ofNat 128) (by decide) hptr hsize]; exact htoken
  by_cases hz : len = UInt256.ofNat 0
  · rw [if_pos hz] at rd1
    have hd : data.size = 0 := by rw [hdataSize, hz]; rfl
    have hg : evalExpr? config { contract := contract, locals := locals, immutables := imms } e1
        (.binary .gt (.arrayLength .localVar ⟨"data", []⟩) (.intLit 0)) = .ok (.bool false) := by
      rw [supplyDataGuard hl imms e1, hd]; rfl
    have hab : StateBlock config { contract := contract, locals := locals, immutables := imms } evm
        (repayTransition.body.drop 18) { contract := contract, locals := locals, immutables := imms } e1
        (repayTransition.body.drop 21) := hevent.step (ExecStmt.iteFalse hg ExecBlock.nil)
    exact (morphoLoanTransferPairAt p locals imms "__c9" (by decide) (by decide) hc hl hs1 hm2
      (le_trans hsize hpref.size) hptr hget hz1 ht1 (Or.inr rfl) rd1).prepend hab
  · rw [if_neg hz] at rd1
    have hn : 0 < data.size := by
      rw [hdataSize]
      exact Nat.pos_of_ne_zero (fun h0 => hz (uint256_toNat_eq_zero h0))
    exact (morphoRepayCallbackTail p locals imms hc hl hs1 hm2 (le_trans hsize hpref.size) hptr hget hz1 ht1
      hn hlen hsrc hdata hdataSize rd1).prepend hevent

end Benchmarks.Morpho.MorphoBlue
