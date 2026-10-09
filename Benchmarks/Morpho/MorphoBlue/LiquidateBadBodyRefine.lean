import Benchmarks.Morpho.MorphoBlue.LiquidateBadHighRefine

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

inductive LiquidateBadBodyRefines (v : MorphoImmutables) (ee : ExecutionEnv) (g : Sat256) (s0 : State)
    (p : MarketParamsWords) (assets seized shares account srcOff len : UInt256) (data : ByteArray)
    (locals imms : Store) (evm : EVM.State) (mem : ByteArray) (fp : UInt256) (R : List UInt256) : Prop where
  | reverted : ExecBlock config { contract := contract, locals := locals, immutables := imms }
      evm liquidateBadBody .reverted → RDrev (deployedRuntime v) g s0 →
      LiquidateBadBodyRefines v ee g s0 p assets seized shares account srcOff len data locals imms evm mem fp R
  | ok {badAssets badShares locals' evm' σ' mem' fp' aw' out' k' C'} :
      ExecBlock config { contract := contract, locals := locals, immutables := imms }
        evm liquidateBadBody (.ok { contract := contract, locals := locals', immutables := imms } evm') →
      LiquidateEventLocals p account seized shares data assets badAssets badShares locals' →
      locals'.get? "__memory" = some (.int (Int.ofNat fp'.toNat)) →
      SourceState s0 ee σ' evm' → MorphoHeap mem' fp' 384 → HeapAdvance mem fp mem' fp' 192 →
      RD (deployedRuntime v) ee g s0 (UInt256.ofNat 2574)
        (liquidateEventTail (UInt256.ofNat (deployedRuntime v).size) p.id assets seized shares badAssets badShares srcOff len R)
        mem' aw' out' σ' k' C' →
      LiquidateBadBodyRefines v ee g s0 p assets seized shares account srcOff len data locals imms evm mem fp R

theorem morphoLiquidateBadBodyRefine {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 evm : State} {aw fp assets seized shares account srcOff len : UInt256} {out mem data : ByteArray}
    {σ : AccountMap} {k C : Nat} {R : List UInt256} (p : MarketParamsWords) (locals imms : Store)
    (hstack : R.length + 48 ≤ 1024) (hperm : ee.perm = true)
    (ha : account.toNat < EVM.addressModulus) (haccount : calldataWord ee.calldata 164 = account)
    (hl : LiquidateEventLocals p account seized shares data assets (UInt256.ofNat 0) (UInt256.ofNat 0) locals)
    (hs : SourceState s0 ee σ evm) (hm : MorphoHeap mem fp 576)
    (hget : locals.get? "__memory" = some (.int (Int.ofNat fp.toNat)))
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 2873)
      (liquidateBadTail p.id assets seized shares (UInt256.ofNat 0) (UInt256.ofNat 0) srcOff len R) mem aw out σ k C) :
    LiquidateBadBodyRefines v ee g s0 p assets seized shares account srcOff len data locals imms evm mem fp R := by
  obtain hre | ⟨ab0, hl0, hg0, hc0, hba, hbs, hm0, ad0, rd0⟩ :=
    morphoLiquidateBadMathRefine (v := v) p locals imms hstack ha haccount hl hs hm hget h
  · exact .reverted hre ‹RDrev _ _ _›
  obtain hre | ⟨ab1, hl1, hg1, hc1, hs1, hm1, ad1, rd1⟩ :=
    morphoLiquidateBadLowRefine (v := v) true p _ imms hstack hperm hl0 hs hm0 (by decide) hc0 hba hbs rd0
  · exact .reverted (ab0.run hre) ‹RDrev _ _ _›
  obtain hre | ⟨ab2, hl2, hg2, hc2, hs2, hm2, ad2, rd2⟩ :=
    morphoLiquidateBadLowRefine (v := v) false p _ imms hstack hperm hl1 hs1 hm1 (by decide) hc1 hba hbs rd1
  · exact .reverted (ab0.run (ab1.run hre)) ‹RDrev _ _ _›
  obtain hre | ⟨he3, hs3, hm3, ad3, rd3⟩ :=
    morphoLiquidateBadHighRefine (v := v) p _ imms hstack hperm ha haccount hl2 hs2 hm2 hc2 hbs rd2
  · exact .reverted (ab0.run (ab1.run (ab2.run hre))) ‹RDrev _ _ _›
  refine .ok (ab0.run (ab1.run (ab2.run he3))) hl2 ?_ hs3 hm3 ?_ rd3
  · rw [hg2, hg1, hg0, ad2.cursor, ad1.cursor]
  · exact ((ad0.trans ad1).trans ad2).trans ad3

end Benchmarks.Morpho.MorphoBlue
