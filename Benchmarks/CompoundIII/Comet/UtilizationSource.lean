import Benchmarks.CompoundIII.Comet.PresentValue

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

def totalPresentValue (w0 w1 : UInt256) (borrow : Bool) : UInt256 :=
  presentValueWord (totalsIndexWord w0 borrow) (totalsPrincipalWord w1 borrow)

theorem totalPresentValue_lt (w0 w1 : UInt256) (borrow : Bool) :
    (totalPresentValue w0 w1 borrow).toNat < 2^168 :=
  presentValueWord_lt (totalsIndexWord_lt w0 borrow) (totalsPrincipalWord_lt w1 borrow)

theorem utilizationProduct_lt (w0 w1 : UInt256) :
    (totalPresentValue w0 w1 true).toNat * (⟨1000000000000000000⟩ : UInt256).toNat <
      UInt256.size := by
  calc
    _ < 2^168 * 2^60 :=
      Nat.mul_lt_mul_of_lt_of_lt (totalPresentValue_lt w0 w1 true) (by decide)
    _ < UInt256.size := by decide

def utilizationWord (w0 w1 : UInt256) : UInt256 :=
  if totalPresentValue w0 w1 false = ⟨0⟩ then ⟨0⟩
  else UInt256.div (UInt256.mul (totalPresentValue w0 w1 true) ⟨1000000000000000000⟩)
    (totalPresentValue w0 w1 false)

def utilizationAt (evm : EVM.State) : UInt256 :=
  utilizationWord (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩)
    (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩)

def utilizationCallable : CallableDecl :=
  { params := [], returnType := [.elem (.int (.uint ⟨256, by decide⟩))]
    body := [
      .internalCall "presentValueSupply"
        [.storage ⟨"baseSupplyIndex", []⟩, .storage ⟨"totalSupplyBase", []⟩] "totalSupply_",
      .internalCall "presentValueBorrow"
        [.storage ⟨"baseBorrowIndex", []⟩, .storage ⟨"totalBorrowBase", []⟩] "totalBorrow_",
      .ite (.binary .eq (.var "totalSupply_") (.intLit 0))
        [.return [.intLit 0]]
        [.return [.binary .div
          (.inRange (.uint ⟨256, by decide⟩)
            (.binary .mul (.var "totalBorrow_") (.intLit 1000000000000000000)))
          (.var "totalSupply_")]]] }

theorem utilizationCallable_lookup :
    lookupCallable? contract "getUtilization_body" = some utilizationCallable := rfl

theorem utilizationCallable_returns (evm : EVM.State) (imms : Store) :
    ∃ frame, ExecFuncBody config { contract := contract, locals := ∅, immutables := imms }
      evm utilizationCallable.body (.returned frame evm (some [.int (utilizationAt evm).toNat])) := by
  let w0 := Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩
  let w1 := Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩
  let supply := totalPresentValue w0 w1 false
  let borrow := totalPresentValue w0 w1 true
  let f0 : Frame := { contract := contract, locals := ∅, immutables := imms }
  let f1 : Frame := { f0 with locals := f0.locals.insert "totalSupply_" (.int supply.toNat) }
  let f2 : Frame := { f1 with locals := f1.locals.insert "totalBorrow_" (.int borrow.toNat) }
  refine ⟨f2, .execBlockRet ?_⟩
  apply ExecBlock.consNormal (presentValue_call f0 evm false
    (totalsIndexWord w0 false) (totalsPrincipalWord w1 false) _ _ "totalSupply_" rfl
    (totalsIndexWord_lt _ _) (totalsPrincipalWord_lt _ _)
    (evalTotalsIndex evm ∅ imms false (by simp))
    (evalTotalsPrincipal evm ∅ imms false (by simp)))
  apply ExecBlock.consNormal (presentValue_call f1 evm true
    (totalsIndexWord w0 true) (totalsPrincipalWord w1 true) _ _ "totalBorrow_" rfl
    (totalsIndexWord_lt _ _) (totalsPrincipalWord_lt _ _)
    (evalTotalsIndex evm f1.locals imms true (by simp [f1, f0, totalsIndexName]))
    (evalTotalsPrincipal evm f1.locals imms true (by simp [f1, f0, totalsPrincipalName])))
  have hsup : evalExpr? config f2 evm (.var "totalSupply_") = .ok (.int (Int.ofNat supply.toNat)) := by
    simp only [evalExpr?, f2, f1, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert, EvalResult.ofOption]
    rfl
  have hbor : evalExpr? config f2 evm (.var "totalBorrow_") = .ok (.int (Int.ofNat borrow.toNat)) := by
    simp only [evalExpr?, f2, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert, EvalResult.ofOption]
    rfl
  by_cases hz : supply = ⟨0⟩
  · have hzero : (Int.ofNat supply.toNat) = 0 := by rw [hz]; rfl
    apply ExecBlock.consReturn (ExecStmt.iteTrue ?_ ?_)
    · change evalExpr? config f2 evm _ = _
      simp only [evalExpr?, hsup, hzero, pure, bind, EvalResult.bind, evalBinaryOp?]
      rfl
    · apply ABlock.start.returns
      change evalExpr? config f2 evm (.intLit 0) = .ok (.int (Int.ofNat
        (if supply = ⟨0⟩ then (⟨0⟩ : UInt256) else UInt256.div
          (UInt256.mul borrow ⟨1000000000000000000⟩) supply).toNat))
      rw [if_pos hz]
      simp only [evalExpr?, pure]
      rfl
  · have hnonzero : (Int.ofNat supply.toNat) ≠ 0 := by
      intro hn
      apply hz
      apply u256_inj
      change supply.toNat = 0
      exact Int.ofNat.inj hn
    apply ExecBlock.consReturn (ExecStmt.iteFalse ?_ ?_)
    · change evalExpr? config f2 evm _ = _
      simp only [evalExpr?, hsup, pure, bind, EvalResult.bind, evalBinaryOp?]
      have hn : supply.toNat ≠ 0 := fun h ↦ hnonzero (congrArg Int.ofNat h)
      simp [hn]
    · apply ABlock.start.returns
      change evalExpr? config f2 evm _ = _
      change evalExpr? config f2 evm _ = .ok (.int (Int.ofNat
        (if supply = ⟨0⟩ then ⟨0⟩ else UInt256.div
          (UInt256.mul borrow ⟨1000000000000000000⟩) supply).toNat))
      rw [if_neg hz]
      apply divSourceOk ?_ hsup hz
      exact checkedMulSourceOk hbor
        (by norm_num [evalExpr?, pure, UInt256.toNat, UInt256.size])
        (utilizationProduct_lt w0 w1)

theorem utilization_call (frame : Frame) (evm : EVM.State) (ret : Ident)
    (hc : frame.contract = contract) :
    ExecStmt config frame evm (.internalCall "getUtilization_body" [] ret)
      (.ok { frame with locals := frame.locals.insert ret (.int (utilizationAt evm).toNat) } evm) := by
  obtain ⟨calleeFrame, hb⟩ := utilizationCallable_returns evm frame.immutables
  exact ExecStmt.internalCallReturn (callee := utilizationCallable) (locals := ∅)
    (cfg := config) (solm := frame) (evm := evm) (args := []) (argVals := [])
    rfl (by rw [hc]; exact utilizationCallable_lookup) rfl (by simpa only [hc] using hb)

end Benchmarks.CompoundIII.Comet
