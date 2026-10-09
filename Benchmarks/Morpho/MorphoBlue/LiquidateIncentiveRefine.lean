import Benchmarks.Morpho.MorphoBlue.LiquidateIncentiveSource
import Benchmarks.Morpho.MorphoBlue.LiquidateIncentiveReach
import Benchmarks.Morpho.MorphoBlue.LiquidateHealthGuard

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

inductive LiquidateIncentiveRefines (v : MorphoImmutables) (ee : ExecutionEnv) (g : Sat256) (s0 : State)
    (p : MarketParamsWords) (account seized shares price srcOff len : UInt256) (data : ByteArray)
    (locals imms : Store) (evm : EVM.State) (mem : ByteArray) (fp : UInt256) (R : List UInt256) : Prop where
  | reverted : ExecBlock config { contract := contract, locals := locals, immutables := imms }
      evm (liquidateTransition.body.drop 13) .reverted → RDrev (deployedRuntime v) g s0 →
      LiquidateIncentiveRefines v ee g s0 p account seized shares price srcOff len data locals imms evm mem fp R
  | ok {locals' mem' fp' aw' out' σ' k' C'} :
      ABlock config evm { contract := contract, locals := locals, immutables := imms }
        (liquidateTransition.body.drop 13) { contract := contract, locals := locals', immutables := imms }
        (liquidateTransition.body.drop 17) → LiquidateLocals p account seized shares data locals' →
      locals'.get? "__memory" = some (.int (Int.ofNat (fp'.toNat + 256))) →
      locals'.get? "collateralPrice" = some (.int (Int.ofNat price.toNat)) →
      locals'.get? "liquidationIncentiveFactor" = some (.int (Int.ofNat (liquidationFactor p.lltv).toNat)) →
      p.lltv.toNat ≤ wad.toNat → SourceState s0 ee σ' evm → MorphoHeap mem' fp' 832 →
      HeapAdvance mem fp mem' fp' 64 →
      RD (deployedRuntime v) ee g s0 (UInt256.ofNat 1743)
        (liquidateMathStack p.id seized shares price (liquidationDenom p.lltv) srcOff len R)
        mem' aw' out' σ' k' C' →
      LiquidateIncentiveRefines v ee g s0 p account seized shares price srcOff len data locals imms evm mem fp R

theorem morphoLiquidateIncentiveRefine {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 evm : State} {mem out data : ByteArray} {aw fp account seized shares price srcOff len : UInt256} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} (p : MarketParamsWords) (locals imms : Store) (z : Bool)
    (hstack : R.length + 40 ≤ 1024) (hl : LiquidateLocals p account seized shares data locals)
    (hs : SourceState s0 ee σ evm) (hm : MorphoHeap mem fp 896)
    (hget : locals.get? "__memory" = some (.int (Int.ofNat (fp.toNat + 320))))
    (hprice : locals.get? "collateralPrice" = some (.int (Int.ofNat price.toNat)))
    (hz : locals.get? "__c4" = some (.bool z))
    (hparams : p.InMemory (UInt256.ofNat 128) mem) (hsize : 288 ≤ mem.size) (hbefore : 288 ≤ fp.toNat)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 1577)
      ([if z then UInt256.ofNat 1 else UInt256.ofNat 0, UInt256.ofNat 1638, price] ++
        liquidateGuardTail p.id seized shares srcOff len R) mem aw out σ k C) :
    LiquidateIncentiveRefines v ee g s0 p account seized shares price srcOff len data locals imms evm mem fp R := by
  have hez : evalExpr? config { contract := contract, locals := locals, immutables := imms } evm
      (.unary .not (.var "__c4")) = .ok (.bool (!z)) := by
    simp only [evalExpr?, hz, EvalResult.ofOption, evalUnaryOp?, bind, EvalResult.bind]
  have hg := morphoLiquidateHealthGuard (v := v) z (by change R.length + 8 + 20 ≤ 1024; omega) hm h
  cases z
  · obtain ⟨a1, k1, C1, rd1, hm1, had1⟩ := hg
    have ab : ABlock config evm { contract := contract, locals := locals, immutables := imms }
        (liquidateTransition.body.drop 13) { contract := contract, locals := locals, immutables := imms }
        (liquidateTransition.body.drop 14) := ABlock.start.requireStep hez
    have hlltv : memLoad (UInt256.ofNat 256) mem = p.lltv := by
      simpa only [show UInt256.ofNat 128 + UInt256.ofNat (32 * 4) = UInt256.ofNat 256 from by decide]
        using hparams ⟨4, by decide⟩
    have hlltv1 : memLoad (UInt256.ofNat 256) (liquidateHealthyMem mem) = p.lltv := by
      rw [memoryPrefix_memLoad had1.preserves _ (by decide) (by exact hbefore) (by exact hsize), hlltv]
    have hreach := morphoLiquidateIncentiveReach (v := v) p (by omega) hlltv1 rd1
    by_cases hf : p.lltv.toNat ≤ wad.toNat
    swap
    · rw [if_neg hf] at hreach
      exact .reverted (ab.run (morphoLiquidateIncentiveSourceReverts p account seized shares data locals imms evm hl
        (Nat.lt_of_not_ge hf))) hreach
    rw [if_pos hf] at hreach
    obtain ⟨a2, k2, C2, rd2⟩ := hreach
    refine .ok ⟨fun tail ↦ ab.run ((morphoLiquidateIncentiveSource p account seized shares data locals imms evm hl hf).run tail)⟩
      hl.incentive ?_ ?_ (store_get_self _ _ _) hf hs hm1 had1 rd2
    · rw [liquidateIncentiveLocals_get _ (by decide), hget, had1.cursor]
    · rw [liquidateIncentiveLocals_get _ (by decide)]; exact hprice
  · exact .reverted (ExecBlock.consRevert (ExecStmt.requireFalse hez)) hg

end Benchmarks.Morpho.MorphoBlue
