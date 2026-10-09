import Benchmarks.Morpho.MorphoBlue.BorrowTail

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

theorem morphoBorrowUpdates {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 evm : State} {mem out : ByteArray} {aw fp assets shares account receiver : UInt256} {σ : AccountMap}
    {k C : Nat} (p : MarketParamsWords) (locals imms : Store) (hc : p.Canonical)
    (ha : account.toNat < EVM.addressModulus) (hr : receiver.toNat < EVM.addressModulus)
    (hl : MarketTransferLocals p assets shares account receiver locals) (hs : SourceState s0 ee σ evm)
    (hm : MorphoHeap mem fp 416) (hsize : 288 ≤ mem.size) (hptr : 288 ≤ fp.toNat)
    (hget : locals.get? "__memory" = some (.int (Int.ofNat (fp.toNat + 320))))
    (hzero : memLoad (UInt256.ofNat 96) mem = UInt256.ofNat 0)
    (hparams : p.InMemory (UInt256.ofNat 128) mem)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 8538)
      (borrowUpdateTail p.id assets shares account receiver []) mem aw out σ k C) :
    ReturnBlockRefines config (deployedRuntime v) ee g s0
      { contract := contract, locals := locals, immutables := imms } evm
      (borrowTransition.body.drop 14) borrowTransition.returnType := by
  have hp := morphoBorrowPositionRefine p locals imms (by decide) ha hl hs hm h
  cases hp with
  | reverted he hr => exact .reverted he hr
  | static he hr => exact .static he hr
  | @ok evm1 σ1 mem1 fp1 a1 out1 k1 C1 ab1 hs1 hperm hm1 had1 rd1 =>
    let l1 := locals.insert "__c6" (.int (Int.ofNat shares.toNat))
    have hl1 : MarketTransferLocals p assets shares account receiver l1 := hl.insert _ _ (by decide) (by decide)
    have hmkt := morphoBorrowMarketRefine p l1 imms (by decide) hperm hl1 hs1 hm1 rd1
    cases hmkt with
    | reverted he hr => exact .reverted (ab1.run he) hr
    | @ok locals2 evm2 σ2 mem2 fp2 a2 out2 k2 C2 ab2 hl2 hg2 hs2 hm2 had2 rd2 =>
      have had12 := had1.trans had2
      have hp2 := had12.preserves
      have hget2 : locals2.get? "__memory" = some (.int (Int.ofNat (fp2.toNat + 128))) := by
        rw [hg2, show l1.get? "__memory" = locals.get? "__memory" from store_get_ne _ _ (by decide), hget, had12.cursor]
      have hparams2 := hparams.ofPrefix hp2 (by decide) (by decide) hsize hptr
      have hh := morphoBorrowHealthRefine p locals2 imms (by decide) ha hc hl2 hs2 hm2 hget2 hparams2
        (le_trans hsize hp2.size) (by rw [had12.cursor]; omega) rd2
      cases hh with
      | reverted he hr => exact .reverted (ab1.run (ab2.run he)) hr
      | @ok locals3 evm3 σ3 mem3 fp3 a3 out3 k3 C3 z ab3 hl3 hg3 hz3 hs3 hm3 had3 rd3 =>
        have had123 := had12.trans had3
        have hp3 := had123.preserves
        have hz : memLoad (UInt256.ofNat 96) mem3 = UInt256.ofNat 0 := by
          rw [memoryPrefix_memLoad hp3 (UInt256.ofNat 96) (by decide)
            (by change 128 ≤ fp.toNat; omega) (by change 128 ≤ mem.size; omega)]
          exact hzero
        have ht : memLoad (UInt256.ofNat 128) mem3 = p.loanToken := by
          rw [memoryPrefix_memLoad hp3 (UInt256.ofNat 128) (by decide)
            (by change 160 ≤ fp.toNat; omega) (by change 160 ≤ mem.size; omega)]
          simpa only [MarketParamsWords.word, Nat.reduceMul, u256_add_zero] using hparams ⟨0, by decide⟩
        exact (((morphoBorrowTail p locals3 imms z hc hr hl3 hs3 hperm hm3
          (by have hb := hp3.size; omega) (by rw [had123.cursor]; omega) hg3 hz3 hz ht rd3).prepend ab3).prepend ab2).prepend ab1

end Benchmarks.Morpho.MorphoBlue
