import Benchmarks.CompoundIII.Comet.ArithmeticSource
import Benchmarks.CompoundIII.Comet.CheckedDivEvm
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_052

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

abbrev MulPriceValid (n p scale : UInt256) : Prop :=
  n.toNat * p.toNat < UInt256.size ∧ scale ≠ ⟨0⟩

def mulPriceWord (n p scale : UInt256) : UInt256 := UInt256.div (UInt256.mul n p) scale

-- LIBRARY CANDIDATE: checked unsigned multiplication followed by checked division.
theorem checkedMulDiv_source {cfg frame evm nExpr pExpr scaleExpr n p scale}
    (hn : evalExpr? cfg frame evm nExpr = .ok (.int (Int.ofNat n.toNat)))
    (hp : evalExpr? cfg frame evm pExpr = .ok (.int (Int.ofNat p.toNat)))
    (hs : evalExpr? cfg frame evm scaleExpr = .ok (.int (Int.ofNat scale.toNat))) :
    evalExpr? cfg frame evm
      (.binary .div (.inRange (.uint ⟨256, by decide⟩) (.binary .mul nExpr pExpr)) scaleExpr) =
      if MulPriceValid n p scale then .ok (.int (mulPriceWord n p scale).toNat) else .revert := by
  by_cases hm : n.toNat * p.toNat < UInt256.size
  · have he := checkedMulSourceOk hn hp hm
    by_cases hz : scale ≠ ⟨0⟩
    · rw [if_pos ⟨hm, hz⟩]
      exact divSourceOk he hs hz
    · rw [if_neg (fun h : MulPriceValid n p scale ↦ hz h.2)]
      have hz' := not_ne_iff.mp hz
      rw [hz'] at hs
      exact divSourceZero he hs
  · rw [if_neg (fun h : MulPriceValid n p scale ↦ hm h.1)]
    have he := checkedMulSourceOverflow hn hp (le_of_not_gt hm)
    simp only [evalExpr?, he, bind, EvalResult.bind]

def mulPriceCallable : CallableDecl :=
  { params := [⟨"n", abiUInt256⟩, ⟨"price", abiUInt256⟩,
      ⟨"fromScale", .elem (.int (.uint ⟨64, by decide⟩))⟩]
    returnType := [abiUInt256]
    body := [.return [.binary .div
      (.inRange (.uint ⟨256, by decide⟩) (.binary .mul (.var "n") (.var "price")))
      (.var "fromScale")]] }

theorem mulPriceCallable_lookup : lookupCallable? contract "mulPrice" = some mulPriceCallable :=
  rfl

def mulPriceEntry (imms : Store) (n p scale : UInt256) : Frame :=
  { contract := contract, immutables := imms,
    locals := ((∅ : Store).insert "fromScale" (.int scale.toNat)).insert "price" (.int p.toNat)
      |>.insert "n" (.int n.toNat) }

theorem mulPrice_source (evm : EVM.State) (imms : Store) (n p scale : UInt256) :
    ExecFuncBody config (mulPriceEntry imms n p scale) evm mulPriceCallable.body
      (if MulPriceValid n p scale then .returned (mulPriceEntry imms n p scale) evm
        (some [.int (mulPriceWord n p scale).toNat]) else .reverted) := by
  let frame := mulPriceEntry imms n p scale
  have hn : evalExpr? config frame evm (.var "n") = .ok (.int n.toNat) := by
    simp only [evalExpr?, frame, mulPriceEntry, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert, EvalResult.ofOption]
    rfl
  have hp : evalExpr? config frame evm (.var "price") = .ok (.int p.toNat) := by
    simp only [evalExpr?, frame, mulPriceEntry, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert, EvalResult.ofOption]
    rfl
  have hs : evalExpr? config frame evm (.var "fromScale") = .ok (.int scale.toNat) := by
    simp only [evalExpr?, frame, mulPriceEntry, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert, EvalResult.ofOption]
    rfl
  have he := checkedMulDiv_source hn hp hs
  by_cases hv : MulPriceValid n p scale
  · rw [if_pos hv] at he ⊢
    exact ExecFuncBody.execBlockRet (ABlock.start.returns he)
  · rw [if_neg hv] at he ⊢
    apply ExecFuncBody.execBlockRevert
    apply ExecBlock.consRevert (ExecStmt.returnRevert ?_)
    change evalExprs? config frame evm _ = .revert
    simp only [evalExprs?, he, bind, EvalResult.bind]

theorem mulPrice_call (frame : Frame) (evm : EVM.State) (n p scale : UInt256)
    (nExpr pExpr scaleExpr : Expr) (ret : Ident) (hc : frame.contract = contract)
    (hn : evalExpr? config frame evm nExpr = .ok (.int n.toNat))
    (hp : evalExpr? config frame evm pExpr = .ok (.int p.toNat))
    (hs : evalExpr? config frame evm scaleExpr = .ok (.int scale.toNat)) :
    ExecStmt config frame evm (.internalCall "mulPrice" [nExpr, pExpr, scaleExpr] ret)
      (if MulPriceValid n p scale then .ok { frame with
        locals := frame.locals.insert ret (.int (mulPriceWord n p scale).toNat) } evm
      else .reverted) := by
  have hb := mulPrice_source evm frame.immutables n p scale
  by_cases hv : MulPriceValid n p scale
  · rw [if_pos hv] at hb ⊢
    exact ExecStmt.internalCallReturn (cfg := config) (solm := frame) (evm := evm)
      (args := [nExpr, pExpr, scaleExpr]) (callee := mulPriceCallable)
      (argVals := [.int n.toNat, .int p.toNat, .int scale.toNat])
      (by simp only [evalExprs?, hn, hp, hs, pure, bind, EvalResult.bind])
      (by rw [hc]; exact mulPriceCallable_lookup) rfl (by simpa only [hc] using hb)
  · rw [if_neg hv] at hb ⊢
    exact ExecStmt.internalCallRevert (cfg := config) (solm := frame) (evm := evm)
      (args := [nExpr, pExpr, scaleExpr]) (callee := mulPriceCallable)
      (argVals := [.int n.toNat, .int p.toNat, .int scale.toNat])
      (by simp only [evalExprs?, hn, hp, hs, pure, bind, EvalResult.bind])
      (by rw [hc]; exact mulPriceCallable_lookup) rfl (by simpa only [hc] using hb)

theorem cometMulPrice {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray}
    {aw n p scale ret : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024) (hs : scale.toNat < 2^64)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) ee g s0 ⟨11194⟩
      (n :: p :: scale :: ret :: R) mem aw rdata σ k C) :
    if MulPriceValid n p scale then
      ∃ k' C', RD (deployedRuntime v) ee g s0 ret (mulPriceWord n p scale :: R)
        mem aw rdata σ k' C'
    else RDrev (deployedRuntime v) g s0 := by
  have r1 := cometWithExtendedAssetList_block_11194 (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
  by_cases hm : n.toNat * p.toNat < UInt256.size
  · obtain ⟨k2, C2, r2⟩ := cometCheckedMul (v := v) (by simpa using hstack) hm
      (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r1
    have hc : UInt256.land scale (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1)
        (UInt256.ofNat 64)) (UInt256.ofNat 1)) = scale :=
      u256LandMaskCleanOfToNat _ _ (bits := 64) rfl hs
    by_cases hz : scale ≠ ⟨0⟩
    · rw [if_pos ⟨hm, hz⟩]
      have r3 := cometWithExtendedAssetList_block_11204_fallthrough
        (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega)
        (by rw [hc]; exact isZero_eq_zero_of_ne hz) r2
      dsimp only [cometWithExtendedAssetList_block_11204_fallthrough_stack] at r3
      rw [hc] at r3
      exact ⟨_, _, cometWithExtendedAssetList_block_11223
        (immWords := wordsOf (immStore v)) (by omega) hret r3⟩
    · rw [if_neg (fun hv : MulPriceValid n p scale ↦ hz hv.2)]
      have hz' := not_ne_iff.mp hz
      have r3 := cometWithExtendedAssetList_block_11204_taken
        (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega)
        (by rw [hc, hz']; decide)
        (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r2
      have r4 := cometWithExtendedAssetList_block_9184
        (immWords := wordsOf (immStore v)) (by change R.length + 3 + 2 ≤ 1024; omega)
        (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r3
      exact cometWithExtendedAssetList_block_9151 (immWords := wordsOf (immStore v))
        (by change R.length + 3 + 2 ≤ 1024; omega) r4
  · rw [if_neg (fun hv : MulPriceValid n p scale ↦ hm hv.1)]
    exact cometCheckedMul_revert (v := v) (by simpa using hstack) (le_of_not_gt hm) r1

end Benchmarks.CompoundIII.Comet
