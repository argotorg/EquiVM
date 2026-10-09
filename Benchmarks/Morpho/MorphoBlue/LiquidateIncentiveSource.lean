import Benchmarks.Morpho.MorphoBlue.LiquidateIncentiveMath
import Benchmarks.Morpho.MorphoBlue.LiquidateSourceStart

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

def liquidateIncentiveLocals (locals : Store) (lltv : UInt256) : Store :=
  ((locals.insert "__c5" (.int (Int.ofNat (liquidationDiscount lltv).toNat))).insert "__c6"
    (.int (Int.ofNat (wDivDownResult wad (liquidationDenom lltv)).toNat))).insert
      "liquidationIncentiveFactor" (.int (Int.ofNat (liquidationFactor lltv).toNat))

theorem LiquidateLocals.incentive {p account seized shares data locals}
    (hl : LiquidateLocals p account seized shares data locals) :
    LiquidateLocals p account seized shares data (liquidateIncentiveLocals locals p.lltv) :=
  ((hl.insert _ _ (by decide) (by decide)).insert _ _ (by decide) (by decide)).insert _ _ (by decide) (by decide)

theorem liquidateIncentiveLocals_get {locals : Store} {lltv : UInt256} (name : Ident)
    (hn : name ≠ "__c5" ∧ name ≠ "__c6" ∧ name ≠ "liquidationIncentiveFactor") :
    (liquidateIncentiveLocals locals lltv).get? name = locals.get? name := by
  unfold liquidateIncentiveLocals
  rw [store_get_ne _ _ (by simp [Ne.symm hn.2.2]),
    store_get_ne _ _ (by simp [Ne.symm hn.2.1]), store_get_ne _ _ (by simp [Ne.symm hn.1])]

theorem morphoLiquidateIncentiveSource (p : MarketParamsWords) (account seized shares : UInt256)
    (data : ByteArray) (locals imms : Store) (evm : EVM.State)
    (hl : LiquidateLocals p account seized shares data locals) (hf : p.lltv.toNat ≤ wad.toNat) :
    ABlock config evm { contract := contract, locals := locals, immutables := imms }
      (liquidateTransition.body.drop 14)
      { contract := contract, locals := liquidateIncentiveLocals locals p.lltv, immutables := imms }
      (liquidateTransition.body.drop 17) := by
  have hecursor : evalExpr? config { contract := contract, locals := locals, immutables := imms } evm
      (.intLit 300000000000000000) = .ok (.int (Int.ofNat liquidationCursor.toNat)) := by simp only [evalExpr?, pure]; rfl
  have he1 := morphoWMulDownCallOk _ _ evm locals imms _ _ "__c5" hecursor
    (evalExpr_uint256_sub (evalWad _ evm) (hl.evalLltv imms evm) hf) (liquidationDiscount_mul_fits hf)
  let l1 := locals.insert "__c5" (.int (Int.ofNat (liquidationDiscount p.lltv).toNat))
  have hget1 : evalExpr? config { contract := contract, locals := l1, immutables := imms } evm
      (.var "__c5") = .ok (.int (Int.ofNat (liquidationDiscount p.lltv).toNat)) := by
    simp only [evalExpr?, l1, store_get_self, EvalResult.ofOption]
  have hb := liquidationDiscount_bound hf
  have hle : (liquidationDiscount p.lltv).toNat ≤ wad.toNat := by change _ ≤ 1000000000000000000; omega
  have he2 := morphoWDivDownCallOk _ _ evm l1 imms _ _ "__c6" (evalWad _ evm)
    (evalExpr_uint256_sub (evalWad _ evm) hget1 hle) (by decide) (liquidationDenom_ne_zero hf)
  let l2 := l1.insert "__c6" (.int (Int.ofNat (wDivDownResult wad (liquidationDenom p.lltv)).toNat))
  have hget2 : evalExpr? config { contract := contract, locals := l2, immutables := imms } evm
      (.var "__c6") = .ok (.int (Int.ofNat (wDivDownResult wad (liquidationDenom p.lltv)).toNat)) := by
    simp only [evalExpr?, l2, store_get_self, EvalResult.ofOption]
  have he3 := morphoMinCall liquidationCap _ evm l2 imms (.intLit 1150000000000000000) _
    "liquidationIncentiveFactor" (by simp only [evalExpr?, pure]; rfl) hget2
  exact advancePureBlock (advancePureBlock (advancePureBlock ABlock.start he1) he2) he3

theorem morphoLiquidateIncentiveSourceReverts (p : MarketParamsWords) (account seized shares : UInt256)
    (data : ByteArray) (locals imms : Store) (evm : EVM.State)
    (hl : LiquidateLocals p account seized shares data locals) (hf : wad.toNat < p.lltv.toNat) :
    ExecBlock config { contract := contract, locals := locals, immutables := imms }
      evm (liquidateTransition.body.drop 14) .reverted := by
  apply ExecBlock.consRevert
  apply ExecStmt.internalCallArgsRevert
  have he := evalCheckedSubUnderflow (evalWad _ evm) (hl.evalLltv imms evm) hf
  simp only [evalExprs?, he, evalExpr?, pure, bind, EvalResult.bind]

end Benchmarks.Morpho.MorphoBlue
