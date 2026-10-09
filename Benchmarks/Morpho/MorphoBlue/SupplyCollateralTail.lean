import Benchmarks.Morpho.MorphoBlue.SupplyCollateralCallbackTail

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

theorem morphoSupplyCollateralTail {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 evm : State} {out data : ByteArray} {aw srcOff len assets account : UInt256} {σ : AccountMap}
    {k C : Nat} (p : MarketParamsWords) (locals imms : Store) (hc : p.Canonical)
    (hl : SupplyCollateralLocals p assets account data locals) (hs : SourceState s0 ee σ evm) (hp : ee.perm = true)
    (hlen : len.toNat ≤ solcMaxU64) (hsrc : srcOff.toNat + len.toNat ≤ ee.calldata.size)
    (hdata : ee.calldata.readWithPadding srcOff.toNat len.toNat = data) (hdataSize : data.size = len.toNat)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 10235)
      (supplyCollateralUpdateTail p.id assets account srcOff len []) (supplyCollateralPositionMem p account) aw out σ k C) :
    VoidBlockRefines config (deployedRuntime v) ee g s0
      { contract := contract, locals := locals, immutables := imms } evm (supplyCollateralTransition.body.drop 9) := by
  obtain ⟨a1, k1, C1, rd1⟩ := morphoSupplyCollateralEvent p (by decide) hp h
  obtain ⟨hm, hsize, hzero, hparams⟩ := supplyCollateralEventMem_facts p account assets
  have htoken : memLoad (UInt256.ofNat 160) (supplyCollateralEventMem p account assets) = p.collateralToken :=
    by simpa only [MarketParamsWords.word, Nat.reduceMul,
      show UInt256.ofNat 128 + UInt256.ofNat 32 = UInt256.ofNat 160 from rfl] using hparams ⟨1, by decide⟩
  have hevent : StateBlock config { contract := contract, locals := locals, immutables := imms } evm
      (supplyCollateralTransition.body.drop 9) { contract := contract, locals := locals, immutables := imms } evm
      (supplyCollateralTransition.body.drop 10) := StateBlock.start.step (supplyCollateralEmit p assets account data locals imms evm hl)
  by_cases hz : len = UInt256.ofNat 0
  · rw [if_pos hz] at rd1
    have hd : data.size = 0 := by rw [hdataSize, hz]; rfl
    have hg : evalExpr? config { contract := contract, locals := locals, immutables := imms } evm
        (.binary .gt (.arrayLength .localVar ⟨"data", []⟩) (.intLit 0)) = .ok (.bool false) := by
      rw [supplyCollateralDataGuard hl imms evm, hd]; rfl
    have hab : StateBlock config { contract := contract, locals := locals, immutables := imms } evm
        (supplyCollateralTransition.body.drop 9) { contract := contract, locals := locals, immutables := imms } evm
        (supplyCollateralTransition.body.drop 11) := hevent.step (ExecStmt.iteFalse hg ExecBlock.nil)
    exact (morphoSupplyCollateralTransfer p locals imms hc hl hs hm (by rw [hsize]; decide) hzero htoken rd1).prepend hab
  · rw [if_neg hz] at rd1
    have hn : 0 < data.size := by
      rw [hdataSize]
      exact Nat.pos_of_ne_zero (fun h0 => hz (uint256_toNat_eq_zero h0))
    exact (morphoSupplyCollateralCallbackTail p locals imms hc hl hs hm (by rw [hsize]; decide) hzero htoken
      hn hlen hsrc hdata hdataSize rd1).prepend hevent

end Benchmarks.Morpho.MorphoBlue
