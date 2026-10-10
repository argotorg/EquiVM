import Benchmarks.CompoundIII.Comet.ArithmeticSource
import Benchmarks.CompoundIII.Comet.PresentValue

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

def baseRewardWord (v : CometWithExtendedAssetListImmutables)
    (principal delta : UInt256) : UInt256 :=
  UInt256.div (UInt256.div (UInt256.mul principal delta) v.trackingIndexScale)
    v.accrualDescaleFactor

abbrev BaseRewardValid (v : CometWithExtendedAssetListImmutables)
    (principal delta : UInt256) : Prop :=
  v.trackingIndexScale ≠ ⟨0⟩ ∧ v.accrualDescaleFactor ≠ ⟨0⟩ ∧
    (baseRewardWord v principal delta).toNat < 2^64

def baseRewardExpr (principal delta : Expr) : Expr :=
  .binary .div
    (.binary .div (.inRange (.uint ⟨256, by decide⟩) (.binary .mul principal delta))
      (.immutable "trackingIndexScale")) (.immutable "accrualDescaleFactor")

theorem baseRewardProduct_lt {principal delta : UInt256}
    (hp : principal.toNat < 2^104) (hd : delta.toNat < 2^64) :
    principal.toNat * delta.toNat < UInt256.size := by
  exact lt_trans (presentValue_mul_lt hd hp) (by decide)

theorem baseReward_call (v : CometWithExtendedAssetListImmutables)
    (frame : Frame) (evm : EVM.State) (principal delta : UInt256)
    (principalExpr deltaExpr : Expr) (ret : Ident)
    (hc : frame.contract = contract) (hi : frame.immutables = immStore v)
    (hp : evalExpr? config frame evm principalExpr = .ok (.int principal.toNat))
    (hd : evalExpr? config frame evm deltaExpr = .ok (.int delta.toNat))
    (hpb : principal.toNat < 2^104) (hdb : delta.toNat < 2^64) :
    ExecStmt config frame evm (.internalCall "safe64" [baseRewardExpr principalExpr deltaExpr] ret)
      (if BaseRewardValid v principal delta then
        .ok { frame with
          locals := frame.locals.insert ret (.int (baseRewardWord v principal delta).toNat) }
          evm else .reverted) := by
  have hm := checkedMulSourceOk hp hd (baseRewardProduct_lt hpb hdb)
  have hs : evalExpr? config frame evm (.immutable "trackingIndexScale") =
      .ok (.int v.trackingIndexScale.toNat) := by
    simp only [evalExpr?, hi, immStore_get_trackingIndexScale, EvalResult.ofOption]
    rfl
  have hf : evalExpr? config frame evm (.immutable "accrualDescaleFactor") =
      .ok (.int v.accrualDescaleFactor.toNat) := by
    simp only [evalExpr?, hi, immStore_get_accrualDescaleFactor, EvalResult.ofOption]
    rfl
  by_cases hscale : v.trackingIndexScale ≠ ⟨0⟩
  · have hd1 := divSourceOk hm hs hscale
    by_cases hfactor : v.accrualDescaleFactor ≠ ⟨0⟩
    · have hd2 := divSourceOk hd1 hf hfactor
      by_cases hfit : (baseRewardWord v principal delta).toNat < 2^64
      · rw [if_pos (show BaseRewardValid v principal delta from ⟨hscale, hfactor, hfit⟩)]
        exact safe64_call_ok frame evm (baseRewardWord v principal delta) _ ret hc hd2 hfit
      · rw [if_neg (show ¬ BaseRewardValid v principal delta from fun h ↦ hfit h.2.2)]
        exact safe64_call_revert frame evm (baseRewardWord v principal delta) _ ret hc hd2 hfit
    · rw [if_neg (show ¬ BaseRewardValid v principal delta from fun h ↦ hfactor h.2.1)]
      have heq := not_ne_iff.mp hfactor
      rw [heq] at hf
      have hr := divSourceZero hd1 hf
      apply ExecStmt.internalCallArgsRevert
      change evalExprs? config frame evm _ = _
      simp only [baseRewardExpr, evalExprs?, hr, bind, EvalResult.bind]
  · rw [if_neg (show ¬ BaseRewardValid v principal delta from fun h ↦ hscale h.1)]
    have heq := not_ne_iff.mp hscale
    rw [heq] at hs
    have hr := divSourceZero hm hs
    apply ExecStmt.internalCallArgsRevert
    change evalExprs? config frame evm _ = _
    simp only [baseRewardExpr, evalExprs?, evalExpr?, hr, bind, EvalResult.bind]

end Benchmarks.CompoundIII.Comet
