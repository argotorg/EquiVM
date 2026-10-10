import Benchmarks.UniswapV4PoolManager.TickScanWords
import Benchmarks.UniswapV4PoolManager.TickScanSyntax
import Benchmarks.UniswapV4PoolManager.TickPositionSource
import Benchmarks.UniswapV4PoolManager.TransientSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def tickScanPositionFrame (f : Frame) (compressed : UInt256) : Frame :=
  wordLocal (valueLocal (valueLocal f "position" (.tuple (tickPositionValues compressed)))
    "wordPos" (.int (EVM.signed (tickPositionWord compressed)))) "bitPos" (tickPositionBit compressed)

def tickScanPreludeFrame (f : Frame) (evm : EVM.State) (id compressed : UInt256) (lte : Bool) : Frame :=
  valueLocal (wordLocal (wordLocal (tickScanPositionFrame f compressed) "mask"
    (tickScanMask (tickPositionBit compressed) lte)) "masked" (tickScanMasked evm id compressed lte))
    "initialized" (.bool (decide (tickScanMasked evm id compressed lte ≠ ⟨0⟩)))

theorem tickScanPreludeFrame_contract (f : Frame) (evm : EVM.State) (id compressed : UInt256) (lte : Bool) :
    (tickScanPreludeFrame f evm id compressed lte).contract = f.contract := by
  simp only [tickScanPreludeFrame, tickScanPositionFrame, wordLocal_contract, valueLocal_contract]

theorem tickScanPreludeFrame_get (f : Frame) (evm : EVM.State) (id compressed : UInt256)
    (lte : Bool) (name : Ident) :
    (tickScanPreludeFrame f evm id compressed lte).locals.get? name =
      if "initialized" == name then some (.bool (decide (tickScanMasked evm id compressed lte ≠ ⟨0⟩)))
      else if "masked" == name then some (.int (Int.ofNat (tickScanMasked evm id compressed lte).toNat))
      else if "mask" == name then some (.int (Int.ofNat (tickScanMask (tickPositionBit compressed) lte).toNat))
      else if "bitPos" == name then some (.int (Int.ofNat (tickPositionBit compressed).toNat))
      else if "wordPos" == name then some (.int (EVM.signed (tickPositionWord compressed)))
      else if "position" == name then some (.tuple (tickPositionValues compressed))
      else f.locals.get? name := by
  simp only [tickScanPreludeFrame, tickScanPositionFrame, wordLocal_get, valueLocal_get]

theorem tickScanPreludeSource {f : Frame} {evm : EVM.State} {id compressed : UInt256} (lte : Bool)
    (hf : f.contract = contract)
    (hc : f.locals.get? "compressed" = some (.int (EVM.signed (UInt256.signextend (UInt256.ofNat 2) compressed))))
    (hs : f.locals.get? "self" = some (tickBitmapRefValue id)) :
    ExecBlock config f evm (tickScanPreludeStmts lte)
      (.ok (tickScanPreludeFrame f evm id compressed lte) evm) := by
  let f1 := valueLocal f "position" (.tuple (tickPositionValues compressed))
  let f2 := valueLocal f1 "wordPos" (.int (EVM.signed (tickPositionWord compressed)))
  let f3 := tickScanPositionFrame f compressed
  let f4 := wordLocal f3 "mask" (tickScanMask (tickPositionBit compressed) lte)
  let f5 := wordLocal f4 "masked" (tickScanMasked evm id compressed lte)
  have h0 : ExecStmt config f evm (tickScanPreludeStmts lte)[0]! (.ok f1 evm) := by
    have h := tickPositionCall hf (evalLocalValue (cfg := config) (evm := evm) hc) "position"
    simpa only [tickPositionValues_signextend] using h
  have h1 : ExecStmt config f1 evm (tickScanPreludeStmts lte)[1]! (.ok f2 evm) :=
    ExecStmt.letDecl (evalTupleProjection
      (evalLocalValue (store_get_self _ _ _)) (i := 0) (by rfl))
  have hp2 : f2.locals.get? "position" = some (.tuple (tickPositionValues compressed)) :=
    (store_get_ne _ _ (by decide : ("wordPos" == "position") = false)).trans (store_get_self _ _ _)
  have h2 : ExecStmt config f2 evm (tickScanPreludeStmts lte)[2]! (.ok f3 evm) :=
    ExecStmt.letDecl (evalTupleProjection (evalLocalValue hp2) (i := 1) rfl)
  have hb3 : f3.locals.get? "bitPos" = some (.int (Int.ofNat (tickPositionBit compressed).toNat)) :=
    store_get_self _ _ _
  have h3 : ExecStmt config f3 evm (tickScanPreludeStmts lte)[3]! (.ok f4 evm) :=
    ExecStmt.letDecl (tickScanMask_eval lte (tickPositionBit_fits compressed) hb3)
  have hs4 : f4.locals.get? "self" = some (tickBitmapRefValue id) := by
    simp only [f4, f3, tickScanPositionFrame, wordLocal_get, valueLocal_get,
      beq_iff_eq, String.reduceEq, ↓reduceIte, hs]
  have hp4 : f4.locals.get? "wordPos" = some (.int (EVM.signed (tickPositionWord compressed))) := by
    simp only [f4, f3, tickScanPositionFrame, wordLocal_get, valueLocal_get,
      beq_iff_eq, String.reduceEq, ↓reduceIte]
  have h4 : ExecStmt config f4 evm (tickScanPreludeStmts lte)[4]! (.ok f5 evm) :=
    ExecStmt.letDecl (evalWordAnd (tickBitmapWord_read hs4 (evalLocalValue hp4)) wordLocal_eval)
  have hm5 : f5.locals.get? "masked" = some (.int (Int.ofNat (tickScanMasked evm id compressed lte).toNat)) :=
    store_get_self _ _ _
  have h5 : ExecStmt config f5 evm (tickScanPreludeStmts lte)[5]!
      (.ok (tickScanPreludeFrame f evm id compressed lte) evm) :=
    ExecStmt.letDecl (evalNeWords (b := ⟨0⟩) (evalLocalValue hm5)
      (show evalExpr? config f5 evm (.intLit 0) = .ok (.int (Int.ofNat (⟨0⟩ : UInt256).toNat)) by
        simp only [evalExpr?, pure]; rfl))
  exact ExecBlock.consNormal h0 (ExecBlock.consNormal h1 (ExecBlock.consNormal h2
    (ExecBlock.consNormal h3 (ExecBlock.consNormal h4 (execBlock_singleton h5)))))

end Benchmarks.UniswapV4PoolManager
