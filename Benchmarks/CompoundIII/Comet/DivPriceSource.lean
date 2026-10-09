import Benchmarks.CompoundIII.Comet.MulPrice

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

abbrev DivPriceValid (n price scale : UInt256) : Prop := MulPriceValid n scale price

def divPriceWord (n price scale : UInt256) : UInt256 := mulPriceWord n scale price

def divPriceCallable : CallableDecl :=
  { params := [⟨"n", abiUInt256⟩, ⟨"price", abiUInt256⟩,
      ⟨"toScale", .elem (.int (.uint ⟨64, by decide⟩))⟩]
    returnType := [abiUInt256]
    body := [.return [.binary .div
      (.inRange (.uint ⟨256, by decide⟩) (.binary .mul (.var "n") (.var "toScale")))
      (.var "price")]] }

theorem divPriceCallable_lookup : lookupCallable? contract "divPrice" = some divPriceCallable := rfl

def divPriceEntry (imms : Store) (n price scale : UInt256) : Frame :=
  { contract := contract, immutables := imms
    locals := (((∅ : Store).insert "toScale" (.int scale.toNat)).insert "price" (.int price.toNat)).insert
      "n" (.int n.toNat) }

theorem divPrice_source (evm : EVM.State) (imms : Store) (n price scale : UInt256) :
    ExecFuncBody config (divPriceEntry imms n price scale) evm divPriceCallable.body
      (if DivPriceValid n price scale then .returned (divPriceEntry imms n price scale) evm
        (some [.int (divPriceWord n price scale).toNat]) else .reverted) := by
  let frame := divPriceEntry imms n price scale
  have hn : evalExpr? config frame evm (.var "n") = .ok (.int n.toNat) := by
    simp only [evalExpr?, frame, divPriceEntry, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert, EvalResult.ofOption]; rfl
  have hp : evalExpr? config frame evm (.var "price") = .ok (.int price.toNat) := by
    simp only [evalExpr?, frame, divPriceEntry, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert, EvalResult.ofOption]; rfl
  have hs : evalExpr? config frame evm (.var "toScale") = .ok (.int scale.toNat) := by
    simp only [evalExpr?, frame, divPriceEntry, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert, EvalResult.ofOption]; rfl
  have he := checkedMulDiv_source hn hs hp
  by_cases hv : DivPriceValid n price scale
  · rw [if_pos hv] at he ⊢
    exact ExecFuncBody.execBlockRet (ABlock.start.returns he)
  · rw [if_neg hv] at he ⊢
    apply ExecFuncBody.execBlockRevert
    apply ExecBlock.consRevert (ExecStmt.returnRevert ?_)
    change evalExprs? config frame evm _ = .revert
    simp only [evalExprs?, he, bind, EvalResult.bind]

theorem divPrice_call (frame : Frame) (evm : EVM.State) (n price scale : UInt256)
    (nExpr priceExpr scaleExpr : Expr) (ret : Ident) (hc : frame.contract = contract)
    (hn : evalExpr? config frame evm nExpr = .ok (.int n.toNat))
    (hp : evalExpr? config frame evm priceExpr = .ok (.int price.toNat))
    (hs : evalExpr? config frame evm scaleExpr = .ok (.int scale.toNat)) :
    ExecStmt config frame evm (.internalCall "divPrice" [nExpr, priceExpr, scaleExpr] ret)
      (if DivPriceValid n price scale then .ok { frame with
        locals := frame.locals.insert ret (.int (divPriceWord n price scale).toNat) } evm
      else .reverted) := by
  have hb := divPrice_source evm frame.immutables n price scale
  have he : evalExprs? config frame evm [nExpr, priceExpr, scaleExpr] =
      .ok [.int n.toNat, .int price.toNat, .int scale.toNat] := by
    simp only [evalExprs?, hn, hp, hs, pure, bind, EvalResult.bind]
  by_cases hv : DivPriceValid n price scale
  · rw [if_pos hv] at hb ⊢
    exact ExecStmt.internalCallReturn (callee := divPriceCallable) he
      (by rw [hc]; exact divPriceCallable_lookup) rfl (by simpa only [hc] using hb)
  · rw [if_neg hv] at hb ⊢
    exact ExecStmt.internalCallRevert (callee := divPriceCallable) he
      (by rw [hc]; exact divPriceCallable_lookup) rfl (by simpa only [hc] using hb)

end Benchmarks.CompoundIII.Comet
