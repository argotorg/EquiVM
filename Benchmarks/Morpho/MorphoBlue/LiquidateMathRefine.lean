import Benchmarks.Morpho.MorphoBlue.LiquidateSeizedRefine
import Benchmarks.Morpho.MorphoBlue.LiquidateSharesRefine
import Benchmarks.Morpho.MorphoBlue.LiquidateIncentiveRefine

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

inductive LiquidateMathRefines (v : MorphoImmutables) (ee : ExecutionEnv) (g : Sat256) (s0 : State)
    (p : MarketParamsWords) (account srcOff len : UInt256) (data : ByteArray)
    (locals imms : Store) (evm : EVM.State) (σ : AccountMap) (mem : ByteArray) (fp : UInt256) (R : List UInt256) : Prop where
  | reverted : ExecBlock config { contract := contract, locals := locals, immutables := imms }
      evm (liquidateTransition.body.drop 17) .reverted → RDrev (deployedRuntime v) g s0 →
      LiquidateMathRefines v ee g s0 p account srcOff len data locals imms evm σ mem fp R
  | ok {seized' shares' locals' aw' out' mem' k' C'} (assets : UInt256) :
      ABlock config evm { contract := contract, locals := locals, immutables := imms }
        (liquidateTransition.body.drop 17) { contract := contract, locals := locals', immutables := imms }
        (liquidateTransition.body.drop 19) → LiquidateLocals p account seized' shares' data locals' →
      locals'.get? "__memory" = locals.get? "__memory" →
      locals'.get? "repaidAssets" = some (.int (Int.ofNat assets.toNat)) →
      MorphoHeap mem' fp 832 → HeapAdvance mem fp mem' fp 0 →
      RD (deployedRuntime v) ee g s0 (UInt256.ofNat 2105)
        (assets :: liquidateFinishMathTail p.id seized' shares' srcOff len R) mem' aw' out' σ k' C' →
      LiquidateMathRefines v ee g s0 p account srcOff len data locals imms evm σ mem fp R

theorem morphoLiquidateMathRefine {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 evm : State} {aw fp account seized shares price srcOff len : UInt256} {out mem data : ByteArray}
    {σ : AccountMap} {k C : Nat} {R : List UInt256} (p : MarketParamsWords) (locals imms : Store)
    (hstack : R.length + 40 ≤ 1024) (hl : LiquidateLocals p account seized shares data locals)
    (hs : SourceState s0 ee σ evm) (hlltv : p.lltv.toNat ≤ wad.toNat) (hm : MorphoHeap mem fp 832)
    (hprice : locals.get? "collateralPrice" = some (.int (Int.ofNat price.toNat)))
    (hfactor : locals.get? "liquidationIncentiveFactor" = some (.int (Int.ofNat (liquidationFactor p.lltv).toNat)))
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 1743)
      (liquidateMathStack p.id seized shares price (liquidationDenom p.lltv) srcOff len R) mem aw out σ k C) :
    LiquidateMathRefines v ee g s0 p account srcOff len data locals imms evm σ mem fp R := by
  have ha : LiquidateAmountRefines v ee g s0 p account srcOff len data locals imms evm σ mem R := by
    by_cases hz : seized = ⟨0⟩
    · exact morphoLiquidateSharesRefine p locals imms hstack hl hs hz hprice hfactor h
    · exact morphoLiquidateSeizedRefine p locals imms hstack hl hs hlltv hz hprice hfactor h
  cases ha with
  | reverted he hr => exact .reverted he hr
  | @ok seized' shares' locals' aw' out' k' C' hab hl' hmem rd =>
    obtain ⟨a1, k1, C1, rd1⟩ := morphoLiquidateReachAssets (v := v) (by omega) rd
    have heassets := hl'.evalField imms evm ⟨2, by decide⟩
    have heshares := hl'.evalField imms evm ⟨3, by decide⟩
    rw [hs.env, ← hs.accounts] at heassets heshares
    by_cases hf : AssetsUpFits shares' (marketFieldWord σ ee p.id 2) (marketFieldWord σ ee p.id 3)
    swap
    · exact .reverted (hab.run (ExecBlock.consRevert (morphoAssetsUpCallReverts _ _ _ evm locals' imms _ _ _ "repaidAssets"
        (hl'.evalShares imms evm) heassets heshares hf)))
        (morphoAssetsUpReverts (v := v) (by change R.length + 7 + 14 ≤ 1024; omega) hf rd1)
    obtain ⟨k2, C2, rd2⟩ := morphoAssetsUpOk (v := v) (by change R.length + 7 + 14 ≤ 1024; omega)
      (by rw [morphoPatchedValidJumps v]; jump_dest) hf rd1
    refine .ok _ (advancePureBlock hab (morphoAssetsUpCallOk _ _ _ evm locals' imms _ _ _ "repaidAssets"
      (hl'.evalShares imms evm) heassets heshares hf)) (hl'.insert _ _ (by decide) (by decide))
      ?_ (store_get_self _ _ _) ((hm.hash p.id (UInt256.ofNat 3)).hash p.id (UInt256.ofNat 3)) ?_ rd2
    · rw [store_get_ne _ _ (by decide)]; exact hmem
    · exact (heapAdvance_hash mem fp p.id (UInt256.ofNat 3)).trans (heapAdvance_hash _ fp p.id (UInt256.ofNat 3))

end Benchmarks.Morpho.MorphoBlue
