import Benchmarks.Morpho.MorphoBlue.LiquidateStorageTail
import Benchmarks.Morpho.MorphoBlue.LiquidateOracleRefine

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

theorem morphoLiquidateRefine {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 evm : State} {aw account seized shares srcOff len : UInt256} {out data : ByteArray}
    {σ : AccountMap} {k C : Nat} (p : MarketParamsWords) (locals imms : Store) (hc : p.Canonical)
    (ha : account.toNat < EVM.addressModulus) (haccount : calldataWord ee.calldata 164 = account)
    (hl : LiquidateLocals p account seized shares data locals) (hs : SourceState s0 ee σ evm)
    (hac : locals.get? "__accrued" = some (.bool (accrueActive p evm)))
    (hlen : len.toNat ≤ solcMaxU64) (hsrc : srcOff.toNat + len.toNat ≤ ee.calldata.size)
    (hdata : ee.calldata.readWithPadding srcOff.toNat len.toNat = data) (hdataSize : data.size = len.toNat)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 1460)
      (liquidateGuardTail p.id seized shares srcOff len []) (supplyInputMem p) aw out σ k C) :
    ReturnBlockRefines config (deployedRuntime v) ee g s0
      { contract := contract, locals := locals, immutables := imms } evm
      (liquidateTransition.body.drop 8) liquidateTransition.returnType := by
  obtain he | he | ⟨ab1, hl1, hg1, hs1, hm1, hlo1, hsize1, hparams1, hz1, rd1⟩ :=
    morphoLiquidateAccrueRefine (v := v) p locals imms (by decide) hc hl hac hs h
  · exact .reverted he ‹RDrev _ _ _›
  · exact .static he ‹RDstatic _ _ _›
  rename_i locals1 evm1 σ1 mem1 fp1 aw1 out1 k1 C1
  obtain he | ⟨price, z, ab2, hl2, hg2, hp2, hz2, hs2, hm2, ad2, rd2⟩ :=
    morphoLiquidateOracleRefine (v := v) p _ imms (by decide) hc ha haccount hl1 hs1 hm1 hg1 hparams1
      (by omega) (by omega) rd1
  · exact .reverted (ab1.run he) ‹RDrev _ _ _›
  rename_i locals2 evm2 σ2 mem2 fp2 aw2 out2 k2 C2
  have hparams2 := hparams1.ofPrefix ad2.preserves (by decide) (by decide) (by change 288 ≤ mem1.size; omega) (by change 288 ≤ fp1.toNat; omega)
  have hsize2 : 288 ≤ mem2.size := le_trans (by omega) ad2.preserves.size
  have hlo2 : 288 ≤ fp2.toNat := by rw [ad2.cursor]; omega
  obtain he | ⟨ab3, hl3, hg3, hp3, hf3, hlltv, hs3, hm3, ad3, rd3⟩ :=
    morphoLiquidateIncentiveRefine (v := v) p _ imms z (by decide) hl2 hs2 hm2 hg2 hp2 hz2 hparams2 hsize2 hlo2 rd2
  · exact .reverted (ab1.run (ab2.run he)) ‹RDrev _ _ _›
  rename_i locals3 mem3 fp3 aw3 out3 σ3 k3 C3
  obtain he | ⟨assets, ab4, hl4, hg4, has4, hm4, ad4, rd4⟩ :=
    morphoLiquidateMathRefine (v := v) p _ imms (by decide) hl3 hs3 hlltv hm3 hp3 hf3 rd3
  · exact .reverted (ab1.run (ab2.run (ab3.run he))) ‹RDrev _ _ _›
  rename_i seized4 shares4 locals4 aw4 out4 mem4 k4 C4
  have ad24 := (ad2.trans ad3).trans ad4
  have hp := ad24.preserves
  have hsize4 : 192 ≤ mem4.size := le_trans (by omega) hp.size
  have hlo4 : 192 ≤ fp3.toNat := by have hh := ad24.cursor; omega
  have hparams4 := hparams1.ofPrefix hp (by decide) (by decide) (by change 288 ≤ mem1.size; omega) (by change 288 ≤ fp1.toNat; omega)
  have hloan : memLoad (UInt256.ofNat 128) mem4 = p.loanToken := by
    simpa only [show UInt256.ofNat 128 + UInt256.ofNat (32 * 0) = UInt256.ofNat 128 from rfl] using hparams4 ⟨0, by decide⟩
  have htoken : memLoad (UInt256.ofNat 160) mem4 = p.collateralToken := by
    simpa only [show UInt256.ofNat 128 + UInt256.ofNat (32 * 1) = UInt256.ofNat 160 from rfl] using hparams4 ⟨1, by decide⟩
  have hz4 : memLoad (UInt256.ofNat 96) mem4 = UInt256.ofNat 0 := by
    rw [memoryPrefix_memLoad hp (UInt256.ofNat 96) (by decide)
      (by change 128 ≤ fp1.toNat; omega) (by change 128 ≤ mem1.size; omega)]
    exact hz1
  have ht := morphoLiquidateStorageTail (v := v) p _ imms hc ha haccount hl4 hs3 hm4 hsize4 hlo4
    (hg4.trans hg3) has4 hz4 hloan htoken hlen hsrc hdata hdataSize rd4
  exact ht.prepend ⟨fun tail ↦ ab1.run (ab2.run (ab3.run (ab4.run tail)))⟩

end Benchmarks.Morpho.MorphoBlue
