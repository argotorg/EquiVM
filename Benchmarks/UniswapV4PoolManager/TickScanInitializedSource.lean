import Benchmarks.UniswapV4PoolManager.TickScanWords
import Benchmarks.UniswapV4PoolManager.TickScanSyntax
import Benchmarks.UniswapV4PoolManager.LeastSignificantBitSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem tickScanDefault_eval {f : Frame} {evm : EVM.State} {bit : UInt256} (lte : Bool)
    (hb : f.locals.get? "bitPos" = some (.int (Int.ofNat bit.toNat))) :
    evalExpr? config f evm (tickScanDefaultExpr lte) =
      .ok (.int (Int.ofNat (tickScanDefaultDistance bit lte).toNat)) := by
  cases lte with
  | true => exact evalLocalValue hb
  | false =>
    exact evalUintWordSubWidth ⟨8, by decide⟩ (UInt256.ofNat 255) rfl
      (show evalExpr? config f evm (.intLit 255) = .ok (.int (Int.ofNat (UInt256.ofNat 255).toNat)) by
        simp only [evalExpr?, pure]; rfl) (evalLocalValue hb)

theorem tickScanDistance_eval {f : Frame} {evm : EVM.State} {bit index : UInt256} (lte : Bool)
    (hb : f.locals.get? "bitPos" = some (.int (Int.ofNat bit.toNat)))
    (hi : f.locals.get? (tickScanIndexName lte) = some (.int (Int.ofNat index.toNat))) :
    evalExpr? config f evm (tickScanDistanceExpr lte) =
      .ok (.int (Int.ofNat (tickScanDistance bit index lte).toNat)) := by
  cases lte with
  | true =>
    exact evalUintWordSubWidth ⟨8, by decide⟩ (UInt256.ofNat 255) rfl
      (evalLocalValue hb) (evalLocalValue hi)
  | false =>
    exact evalUintWordSubWidth ⟨8, by decide⟩ (UInt256.ofNat 255) rfl
      (evalLocalValue hi) (evalLocalValue hb)

theorem tickScanIndexCall {f : Frame} {evm : EVM.State} {e : Expr} {masked : UInt256} (lte : Bool)
    (hf : f.contract = contract) (he : evalExpr? config f evm e = .ok (.int (Int.ofNat masked.toNat)))
    (hn : masked ≠ ⟨0⟩) :
    ExecStmt config f evm (.internalCall (tickScanIndexFunctionName lte) [e] (tickScanIndexName lte))
      (.ok (wordLocal f (tickScanIndexName lte) (tickScanIndex masked lte)) evm) := by
  cases lte with
  | true => simpa only [if_neg hn] using mostSignificantBitCall hf he "msb"
  | false => simpa only [if_neg hn] using leastSignificantBitCall hf he "lsb"

theorem tickScanIndexFrame_get (f : Frame) (masked : UInt256) (lte : Bool) (name : Ident)
    (hm : ("msb" == name) = false) (hl : ("lsb" == name) = false) :
    (wordLocal f (tickScanIndexName lte) (tickScanIndex masked lte)).locals.get? name = f.locals.get? name := by
  cases lte <;> simp only [tickScanIndexName, ↓reduceIte, wordLocal_get, hm, hl, Bool.false_eq_true]

def tickScanInitializedFrame (f : Frame) (compressed spacing masked : UInt256) (lte : Bool) : Frame :=
  valueLocal (wordLocal f (tickScanIndexName lte) (tickScanIndex masked lte)) "next"
    (.int (EVM.signed (tickScanNextWord compressed spacing
      (tickScanDistance (tickPositionBit compressed) (tickScanIndex masked lte) lte) lte)))

theorem tickScanInitializedSource {f : Frame} {evm : EVM.State} {compressed spacing masked : UInt256}
    {old : Value} (lte : Bool) (hf : f.contract = contract)
    (hc : f.locals.get? "compressed" = some (.int (EVM.signed (UInt256.signextend (UInt256.ofNat 2) compressed))))
    (hs : f.locals.get? "tickSpacing" = some (.int (EVM.signed spacing)))
    (hb : f.locals.get? "bitPos" = some (.int (Int.ofNat (tickPositionBit compressed).toNat)))
    (hm : f.locals.get? "masked" = some (.int (Int.ofNat masked.toNat)))
    (ho : f.locals.get? "next" = some old) (hn : masked ≠ ⟨0⟩) :
    ExecBlock config f evm (tickScanInitializedStmts lte)
      (.ok (tickScanInitializedFrame f compressed spacing masked lte) evm) := by
  let f1 := wordLocal f (tickScanIndexName lte) (tickScanIndex masked lte)
  have hc1 : f1.locals.get? "compressed" = some (.int (EVM.signed (UInt256.signextend (UInt256.ofNat 2) compressed))) :=
    (tickScanIndexFrame_get f masked lte "compressed" (by decide) (by decide)).trans hc
  have hs1 : f1.locals.get? "tickSpacing" = some (.int (EVM.signed spacing)) :=
    (tickScanIndexFrame_get f masked lte "tickSpacing" (by decide) (by decide)).trans hs
  have hb1 : f1.locals.get? "bitPos" = some (.int (Int.ofNat (tickPositionBit compressed).toNat)) :=
    (tickScanIndexFrame_get f masked lte "bitPos" (by decide) (by decide)).trans hb
  have ho1 : f1.locals.get? "next" = some old :=
    (tickScanIndexFrame_get f masked lte "next" (by decide) (by decide)).trans ho
  have hi1 : f1.locals.get? (tickScanIndexName lte) = some (.int (Int.ofNat (tickScanIndex masked lte).toNat)) :=
    store_get_self _ _ _
  have he := tickScanNext_eval lte hc1 hs1 (tickScanDistance_fits _ _ _)
    (tickScanDistance_eval (evm := evm) lte hb1 hi1)
  exact ExecBlock.consNormal (tickScanIndexCall lte hf (evalLocalValue hm) hn)
    (execBlock_singleton (ExecStmt.assign he (assignLocalValue ho1)))

end Benchmarks.UniswapV4PoolManager
