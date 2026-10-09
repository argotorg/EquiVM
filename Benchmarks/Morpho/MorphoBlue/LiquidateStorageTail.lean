import Benchmarks.Morpho.MorphoBlue.LiquidateTransferTail

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

theorem morphoLiquidateStorageTail {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 evm : State} {aw fp assets seized shares account srcOff len : UInt256} {out mem data : ByteArray}
    {σ : AccountMap} {k C : Nat} (p : MarketParamsWords) (locals imms : Store) (hc : p.Canonical)
    (ha : account.toNat < EVM.addressModulus) (haccount : calldataWord ee.calldata 164 = account)
    (hl : LiquidateLocals p account seized shares data locals) (hs : SourceState s0 ee σ evm)
    (hm : MorphoHeap mem fp 832) (hsize : 192 ≤ mem.size) (hptr : 192 ≤ fp.toNat)
    (hget : locals.get? "__memory" = some (.int (Int.ofNat (fp.toNat + 256))))
    (hassets : locals.get? "repaidAssets" = some (.int (Int.ofNat assets.toNat)))
    (hzero : memLoad (UInt256.ofNat 96) mem = UInt256.ofNat 0)
    (hloan : memLoad (UInt256.ofNat 128) mem = p.loanToken)
    (htoken : memLoad (UInt256.ofNat 160) mem = p.collateralToken)
    (hlen : len.toNat ≤ solcMaxU64) (hsrc : srcOff.toNat + len.toNat ≤ ee.calldata.size)
    (hdata : ee.calldata.readWithPadding srcOff.toNat len.toNat = data) (hdataSize : data.size = len.toNat)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 2105)
      (assets :: liquidateFinishMathTail p.id seized shares srcOff len []) mem aw out σ k C) :
    ReturnBlockRefines config (deployedRuntime v) ee g s0
      { contract := contract, locals := locals, immutables := imms } evm
      (liquidateTransition.body.drop 19) liquidateTransition.returnType := by
  obtain he | he | ⟨ab1, hs1, hperm, hm1, ad1, rd1⟩ :=
    morphoLiquidatePositionRefine (v := v) p data locals imms (by decide) ha haccount hl hs hm h
  · exact .reverted he ‹RDrev _ _ _›
  · exact .static he ‹RDstatic _ _ _›
  rename_i evm1 σ1 mem1 fp1 aw1 out1 k1 C1
  have hl1 := hl.insert "__c12" (.int (Int.ofNat shares.toNat)) (by decide) (by decide)
  have hg1 : (locals.insert "__c12" (.int (Int.ofNat shares.toNat))).get? "repaidAssets" =
      some (.int (Int.ofNat assets.toNat)) := by rw [store_get_ne _ _ (by decide)]; exact hassets
  obtain he | ⟨ab2, hl2, hg2, hc2, has2, hs2, hm2, ad2, rd2⟩ :=
    morphoLiquidateMarketRefine (v := v) p data _ imms (by decide) hperm hl1 hs1 hg1 hm1 rd1
  · exact .reverted (ab1.run he) ‹RDrev _ _ _›
  rename_i locals2 evm2 σ2 mem2 fp2 aw2 out2 k2 C2
  have hd : (zeroFloorSubWord (marketFieldWord σ2 ee p.id 2) assets).toNat < 2 ^ 128 := by
    rw [zeroFloorSubWord_toNat]
    have hb : (marketFieldWord σ2 ee p.id 2).toNat < 2 ^ 128 := halfWord_bound _ _
    omega
  obtain he | ⟨ab3, hs3, hm3, ad3, rd3⟩ :=
    morphoLiquidateCollateralRefine (v := v) p _ imms (by decide) ha haccount hperm hl2 hs2 hm2 hc2 hd rd2
  · exact .reverted (ab1.run (ab2.run he)) ‹RDrev _ _ _›
  rename_i evm3 σ3 mem3 fp3 aw3 out3 k3 C3
  have hl3 := hl2.insert "__c15" (.int (Int.ofNat seized.toNat)) (by decide) (by decide)
  have hg3 : ((locals2.insert "__c15" (.int (Int.ofNat seized.toNat))) : Store).get? "__memory" =
      some (.int (Int.ofNat fp3.toNat)) := by
    rw [store_get_ne _ _ (by decide), hg2, store_get_ne _ _ (by decide), hget,
      ad3.cursor, ad2.cursor, ad1.cursor]
  have has3 : ((locals2.insert "__c15" (.int (Int.ofNat seized.toNat))) : Store).get? "repaidAssets" =
      some (.int (Int.ofNat assets.toNat)) := by rw [store_get_ne _ _ (by decide)]; exact has2
  obtain he | ⟨ab4, hl4, hg4, hs4, hm4, hp4, hlo4, rd4⟩ :=
    morphoLiquidateBadDebtRefine (v := v) p _ imms (by decide) hperm ha haccount hl3 has3 hs3 hm3
      hg3 rd3
  · exact .reverted (ab1.run (ab2.run (ab3.run he))) ‹RDrev _ _ _›
  rename_i trash4 badAssets4 badShares4 locals4 evm4 σ4 mem4 fp4 aw4 out4 k4 C4
  have ad03 := (ad1.trans ad2).trans ad3
  have hp04 := ad03.preserves.trans (hp4.mono (by have hh := ad03.cursor; omega))
  have hlo : 192 ≤ fp4.toNat := by
    have hh := ad03.cursor
    omega
  have hz4 := (memoryPrefix_memLoad hp04 (UInt256.ofNat 96) (by decide)
    (by change 128 ≤ fp.toNat; omega) (by change 128 ≤ mem.size; omega)).trans hzero
  have ht4 := (memoryPrefix_memLoad hp04 (UInt256.ofNat 128) (by decide)
    (by change 160 ≤ fp.toNat; omega) (by change 160 ≤ mem.size; omega)).trans hloan
  have hc4 := (memoryPrefix_memLoad hp04 (UInt256.ofNat 160) (by decide) hptr hsize).trans htoken
  obtain he | ⟨ab5, hs5, hm5, hsize5, hlo5, hz5, ht5, rd5⟩ :=
    morphoLiquidateCollateralTransfer (v := v) p _ imms hc (by decide) hperm hl4 hs4 hm4
      (le_trans hsize hp04.size) hlo hg4 hz4 ht4 hc4 rd4
  · exact .reverted (ab1.run (ab2.run (ab3.run (ab4.run he)))) ‹RDrev _ _ _›
  rename_i evm5 σ5 mem5 fp5 aw5 out5 k5 C5
  have hl5 := hl4.insert "__c21" (.int (Int.ofNat fp5.toNat)) (by decide) (by decide) (by decide)
  have ht := morphoLiquidateTransferTail (v := v) p _ imms hc hl5 hs5 hm5 hsize5 hlo5
    (store_get_self _ _ _) hz5 ht5 hlen hsrc hdata hdataSize rd5
  exact ht.prepend ⟨fun tail ↦ ab1.run (ab2.run (ab3.run (ab4.run (ab5.run tail))))⟩

end Benchmarks.Morpho.MorphoBlue
