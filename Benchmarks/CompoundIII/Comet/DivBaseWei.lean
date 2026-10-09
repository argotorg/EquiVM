import Benchmarks.CompoundIII.Comet.ArithmeticSource
import Benchmarks.CompoundIII.Comet.CheckedDivEvm
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_052

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

abbrev DivBaseWeiValid (v : CometWithExtendedAssetListImmutables) (n baseWei : UInt256) : Prop :=
  n.toNat * v.baseScale.toNat < UInt256.size ∧ baseWei ≠ ⟨0⟩

def divBaseWeiWord (v : CometWithExtendedAssetListImmutables) (n baseWei : UInt256) : UInt256 :=
  UInt256.div (UInt256.mul n v.baseScale) baseWei

def divBaseWeiCallable : CallableDecl :=
  { params := [⟨"n", .elem (.int (.uint ⟨256, by decide⟩))⟩,
      ⟨"baseWei", .elem (.int (.uint ⟨256, by decide⟩))⟩]
    returnType := [.elem (.int (.uint ⟨256, by decide⟩))]
    body := [.return [.binary .div
      (.inRange (.uint ⟨256, by decide⟩) (.binary .mul (.var "n") (.immutable "baseScale")))
      (.var "baseWei")]] }

def divBaseWeiLocals (n baseWei : UInt256) : Store :=
  ((∅ : Store).insert "baseWei" (.int baseWei.toNat)).insert "n" (.int n.toNat)

theorem divBaseWeiCallable_lookup :
    lookupCallable? contract "divBaseWei" = some divBaseWeiCallable := rfl

theorem divBaseWei_body (v : CometWithExtendedAssetListImmutables)
    (evm : EVM.State) (n baseWei : UInt256) :
    let frame : Frame :=
      { contract := contract, locals := divBaseWeiLocals n baseWei, immutables := immStore v }
    if DivBaseWeiValid v n baseWei then
      ExecFuncBody config frame evm divBaseWeiCallable.body
        (.returned frame evm (some [.int (divBaseWeiWord v n baseWei).toNat]))
    else ExecFuncBody config frame evm divBaseWeiCallable.body .reverted := by
  dsimp only
  let frame : Frame :=
    { contract := contract, locals := divBaseWeiLocals n baseWei, immutables := immStore v }
  have hn : evalExpr? config frame evm (.var "n") = .ok (.int n.toNat) := by
    simp only [evalExpr?, frame, divBaseWeiLocals, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert, EvalResult.ofOption]
    rfl
  have hb : evalExpr? config frame evm (.var "baseWei") = .ok (.int baseWei.toNat) := by
    simp only [evalExpr?, frame, divBaseWeiLocals, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert, EvalResult.ofOption]
    rfl
  have hs := evalImmutable_baseScale config contract (divBaseWeiLocals n baseWei) evm v
  by_cases hm : n.toNat * v.baseScale.toNat < UInt256.size
  · have hp := checkedMulSourceOk hn hs hm
    by_cases hz : baseWei ≠ ⟨0⟩
    · rw [if_pos (show DivBaseWeiValid v n baseWei from ⟨hm, hz⟩)]
      exact ExecFuncBody.execBlockRet (ABlock.start.returns (divSourceOk hp hb hz))
    · rw [if_neg (show ¬ DivBaseWeiValid v n baseWei from fun h ↦ hz h.2)]
      have heq := not_ne_iff.mp hz
      rw [heq] at hb
      have hr := divSourceZero hp hb
      apply ExecFuncBody.execBlockRevert
      apply ExecBlock.consRevert
      apply ExecStmt.returnRevert
      change evalExprs? config frame evm _ = _
      simp only [evalExprs?, hr, bind, EvalResult.bind]
  · rw [if_neg (show ¬ DivBaseWeiValid v n baseWei from fun h ↦ hm h.1)]
    have hr := checkedMulSourceOverflow hn hs (le_of_not_gt hm)
    apply ExecFuncBody.execBlockRevert
    apply ExecBlock.consRevert
    apply ExecStmt.returnRevert
    change evalExprs? config frame evm _ = _
    simp only [evalExprs?, evalExpr?, hr, bind, EvalResult.bind]

theorem divBaseWei_call (v : CometWithExtendedAssetListImmutables)
    (frame : Frame) (evm : EVM.State) (n baseWei : UInt256)
    (nExpr baseWeiExpr : Expr) (ret : Ident) (hc : frame.contract = contract)
    (hi : frame.immutables = immStore v)
    (hn : evalExpr? config frame evm nExpr = .ok (.int n.toNat))
    (hb : evalExpr? config frame evm baseWeiExpr = .ok (.int baseWei.toNat)) :
    ExecStmt config frame evm (.internalCall "divBaseWei" [nExpr, baseWeiExpr] ret)
      (if DivBaseWeiValid v n baseWei then
        .ok { frame with locals :=
          frame.locals.insert ret (.int (divBaseWeiWord v n baseWei).toNat) } evm
      else .reverted) := by
  have hbody := divBaseWei_body v evm n baseWei
  split_ifs with hv
  · rw [if_pos hv] at hbody
    exact ExecStmt.internalCallReturn (callee := divBaseWeiCallable)
      (cfg := config) (solm := frame) (evm := evm) (args := [nExpr, baseWeiExpr])
      (locals := divBaseWeiLocals n baseWei) (argVals := [.int n.toNat, .int baseWei.toNat])
      (by simp only [evalExprs?, hn, hb, pure, bind, EvalResult.bind])
      (by rw [hc]; exact divBaseWeiCallable_lookup) rfl (by simpa only [hc, hi] using hbody)
  · rw [if_neg hv] at hbody
    exact ExecStmt.internalCallRevert (callee := divBaseWeiCallable)
      (cfg := config) (solm := frame) (evm := evm) (args := [nExpr, baseWeiExpr])
      (locals := divBaseWeiLocals n baseWei) (argVals := [.int n.toNat, .int baseWei.toNat])
      (by simp only [evalExprs?, hn, hb, pure, bind, EvalResult.bind])
      (by rw [hc]; exact divBaseWeiCallable_lookup) rfl (by simpa only [hc, hi] using hbody)

theorem cometDivBaseWei {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray}
    {aw : UInt256} {σ : AccountMap} {k C : Nat} {n baseWei ret : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hvalid : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) ee g s0 ⟨11151⟩ (n :: baseWei :: ret :: R)
      mem aw rdata σ k C) :
    if DivBaseWeiValid v n baseWei then
      ∃ k' C', RD (deployedRuntime v) ee g s0 ret (divBaseWeiWord v n baseWei :: R)
        mem aw rdata σ k' C'
    else RDrev (deployedRuntime v) g s0 := by
  have r1 := cometWithExtendedAssetList_block_11151 (immWords := wordsOf (immStore v))
    (by change R.length + 2 + 4 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
  simp only [cometWithExtendedAssetList_block_11151_stack, wordsOf_immStore_baseScale,
    wordOfInt_ofNat_toNat] at r1
  by_cases hm : n.toNat * v.baseScale.toNat < UInt256.size
  · obtain ⟨k2, C2, r2⟩ := cometCheckedMul (v := v) (by simpa using hstack) hm
      (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r1
    have r3 := cometCheckedDiv (v := v) (by omega) hvalid r2
    simpa only [DivBaseWeiValid, hm, true_and, divBaseWeiWord] using r3
  · rw [if_neg (show ¬ DivBaseWeiValid v n baseWei from fun h ↦ hm h.1)]
    exact cometCheckedMul_revert (v := v) (by simpa using hstack) (le_of_not_gt hm) r1

end Benchmarks.CompoundIII.Comet
