import Benchmarks.Morpho.MorphoBlue.WithdrawCollateralTail

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

theorem morphoWithdrawCollateralUpdates {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 evm : State} {mem out : ByteArray} {aw fp assets account receiver : UInt256} {σ : AccountMap}
    {k C : Nat} (p : MarketParamsWords) (locals imms : Store) (hc : p.Canonical)
    (ha : account.toNat < EVM.addressModulus) (hr : receiver.toNat < EVM.addressModulus)
    (hl : CollateralTransferLocals p assets account receiver locals) (hs : SourceState s0 ee σ evm)
    (hm : MorphoHeap mem fp 416) (hsize : 288 ≤ mem.size) (hptr : 288 ≤ fp.toNat)
    (hget : locals.get? "__memory" = some (.int (Int.ofNat (fp.toNat + 128))))
    (hzero : memLoad (UInt256.ofNat 96) mem = UInt256.ofNat 0)
    (hparams : p.InMemory (UInt256.ofNat 128) mem)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 5630)
      (withdrawCollateralGuardTail p.id assets account receiver []) mem aw out σ k C) :
    VoidBlockRefines config (deployedRuntime v) ee g s0
      { contract := contract, locals := locals, immutables := imms } evm
      (withdrawCollateralTransition.body.drop 12) := by
  have hp := morphoWithdrawCollateralUpdateRefine p locals imms (by decide) ha hl hs hm h
  cases hp with
  | reverted he hr => exact .reverted he hr
  | static he hr => exact .static he hr
  | @ok evm1 σ1 mem1 fp1 a1 out1 k1 C1 ab1 hs1 hperm hm1 had1 rd1 =>
    let l1 := locals.insert "__c3" (.int (Int.ofNat assets.toNat))
    have hl1 : CollateralTransferLocals p assets account receiver l1 := hl.insert _ _ (by decide) (by decide)
    have hget1 : l1.get? "__memory" = some (.int (Int.ofNat (fp1.toNat + 64))) := by
      rw [show l1.get? "__memory" = locals.get? "__memory" from store_get_ne _ _ (by decide), hget, had1.cursor]
    have hparams1 := hparams.ofPrefix had1.preserves (by decide) (by decide) hsize hptr
    have hh := morphoWithdrawCollateralHealthRefine p l1 imms (by decide) ha hc hl1 hs1 hm1 hget1 hparams1
      (le_trans hsize had1.preserves.size) (by rw [had1.cursor]; omega) rd1
    cases hh with
    | reverted he hr => exact .reverted (ab1.run he) hr
    | @ok locals2 evm2 σ2 mem2 fp2 a2 out2 k2 C2 z ab2 hl2 hg2 hz2 hs2 hm2 had2 rd2 =>
      have had := had1.trans had2
      have hp2 := had.preserves
      have hz : memLoad (UInt256.ofNat 96) mem2 = UInt256.ofNat 0 := by
        rw [memoryPrefix_memLoad hp2 (UInt256.ofNat 96) (by decide)
          (by change 128 ≤ fp.toNat; omega) (by change 128 ≤ mem.size; omega)]
        exact hzero
      have ht : memLoad (UInt256.ofNat 160) mem2 = p.collateralToken := by
        rw [memoryPrefix_memLoad hp2 (UInt256.ofNat 160) (by decide)
          (by change 192 ≤ fp.toNat; omega) (by change 192 ≤ mem.size; omega)]
        simpa only [MarketParamsWords.word, Nat.reduceMul,
          show UInt256.ofNat 128 + UInt256.ofNat 32 = UInt256.ofNat 160 from rfl] using hparams ⟨1, by decide⟩
      exact ((morphoWithdrawCollateralTail p locals2 imms z hc hr hl2 hs2 hperm hm2
        (by have hb := hp2.size; omega) (by rw [had.cursor]; omega) hg2 hz2 hz ht rd2).prepend ab2).prepend ab1

end Benchmarks.Morpho.MorphoBlue
