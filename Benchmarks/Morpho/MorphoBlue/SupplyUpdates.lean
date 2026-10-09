import Benchmarks.Morpho.MorphoBlue.SupplyTail

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

theorem morphoSupplyUpdates {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 evm : State} {mem out data : ByteArray} {aw fp srcOff len assets shares account : UInt256} {σ : AccountMap}
    {k C : Nat} (p : MarketParamsWords) (locals imms : Store) (hc : p.Canonical)
    (ha : account.toNat < EVM.addressModulus)
    (hl : SupplyLocals p assets shares account data locals) (hs : SourceState s0 ee σ evm)
    (hm : MorphoHeap mem fp 288) (hsize : 160 ≤ mem.size) (hptr : 160 ≤ fp.toNat)
    (hget : locals.get? "__memory" = some (.int (Int.ofNat (fp.toNat + 128))))
    (hzero : memLoad (UInt256.ofNat 96) mem = UInt256.ofNat 0)
    (htoken : memLoad (UInt256.ofNat 128) mem = p.loanToken)
    (hlen : len.toNat ≤ solcMaxU64) (hsrc : srcOff.toNat + len.toNat ≤ ee.calldata.size)
    (hdata : ee.calldata.readWithPadding srcOff.toNat len.toNat = data) (hdataSize : data.size = len.toNat)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 3984)
      (supplyUpdateTail p.id assets shares account srcOff len []) mem aw out σ k C) :
    ReturnBlockRefines config (deployedRuntime v) ee g s0
      { contract := contract, locals := locals, immutables := imms } evm
      (supplyTransition.body.drop 12) supplyTransition.returnType := by
  have hp := morphoSupplyPositionRefine p data locals imms (by decide) ha hl hs h
  cases hp with
  | reverted he hr => exact .reverted he hr
  | static he hr => exact .static he hr
  | @ok evm1 σ1 a1 out1 k1 C1 ab1 hs1 hperm rd1 =>
    have hm1 := (hm.hash p.id (UInt256.ofNat 2)).hash account (solcMappingSlot ⟨2⟩ p.id)
    have hp1 : MemoryPrefix mem (supplyPositionMem p.id account mem) fp.toNat :=
      (heapAdvance_hash mem fp p.id (UInt256.ofNat 2)).preserves.trans
        (heapAdvance_hash _ fp account (solcMappingSlot ⟨2⟩ p.id)).preserves
    have hmkt := morphoSupplyMarketRefine p data locals imms (by decide) hperm hl hs1 hm1 rd1
    cases hmkt with
    | reverted he hr => exact .reverted (ab1.run he) hr
    | @ok locals2 evm2 σ2 mem2 fp2 a2 out2 k2 C2 ab2 hl2 hg2 hc6 hs2 hm2 had2 hfit rd2 =>
      have hp2 := hp1.trans had2.preserves
      have hget2 : locals2.get? "__memory" = some (.int (Int.ofNat fp2.toNat)) := by
        rw [hg2, hget, had2.cursor]
      have hz2 : memLoad (UInt256.ofNat 96) mem2 = UInt256.ofNat 0 := by
        rw [memoryPrefix_memLoad hp2 (UInt256.ofNat 96) (by decide)
          (by change 128 ≤ fp.toNat; omega) (by change 128 ≤ mem.size; omega)]
        exact hzero
      have ht2 : memLoad (UInt256.ofNat 128) mem2 = p.loanToken := by
        rw [memoryPrefix_memLoad hp2 (UInt256.ofNat 128) (by decide) hptr hsize]; exact htoken
      exact ((morphoSupplyTail p locals2 imms hc hl2 hs2 hperm hm2 (le_trans hsize hp2.size)
        (by rw [had2.cursor]; omega) hget2 hc6 hz2 ht2 hfit hlen hsrc hdata hdataSize rd2).prepend ab2).prepend ab1

end Benchmarks.Morpho.MorphoBlue
