import Benchmarks.UniswapV4PoolManager.Slot0Source
import Benchmarks.UniswapV4PoolManager.WordLocals
import Benchmarks.UniswapV4PoolManager.PoolCheckSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

abbrev uintToUint160Function : FunctionDecl := contract.functions[118]!
theorem uintToUint160_lookup : lookupCallable? contract "SafeCast_toUint160" =
    some uintToUint160Function.toCallable := rfl

theorem uintToUint160Body {f : Frame} {evm : EVM.State} {w : UInt256}
    (hx : f.locals.get? "x" = some (.int (Int.ofNat w.toNat))) :
    ∃ f', ExecFuncBody config f evm uintToUint160Function.body
      (if w.toNat < 2^160 then .returned f' evm (some [.int (Int.ofNat w.toNat)]) else .reverted) := by
  let f0 := wordLocal f "y" ⟨0⟩
  let f1 := wordLocal f0 "y" (UInt256.land w solcAddrMask)
  have h0 : ExecStmt config f evm uintToUint160Function.body[0]! (.ok f0 evm) :=
    ExecStmt.letDecl (by simp only [evalExpr?, pure]; rfl)
  have hx0 : f0.locals.get? "x" = some (.int (Int.ofNat w.toNat)) := by
    simp only [f0, wordLocal_get, beq_iff_eq, String.reduceEq, ↓reduceIte, hx]
  have hc := evalExpr_cast_int (intType := .uint ⟨160, by decide⟩)
    (evalLocalValue (cfg := config) (f := f0) (evm := evm) hx0)
  rw [normalizeUintWord ⟨160, by decide⟩ w solcAddrMask rfl] at hc
  have h1 : ExecStmt config f0 evm uintToUint160Function.body[1]! (.ok f1 evm) :=
    ExecStmt.assign hc (assignLocalValue (store_get_self _ _ _))
  have hx1 : f1.locals.get? "x" = some (.int (Int.ofNat w.toNat)) :=
    (store_get_ne _ _ (by decide : ("y" == "x") = false)).trans hx0
  have hy : f1.locals.get? "y" = some (.int (Int.ofNat (UInt256.land w solcAddrMask).toNat)) :=
    store_get_self _ _ _
  have hg := evalNeWords (evalLocalValue (cfg := config) (f := f1) (evm := evm) hy)
    (evalLocalValue hx1)
  by_cases hfit : w.toNat < 2^160
  · simp only [if_pos hfit]
    have hm : UInt256.land w solcAddrMask = w := solcAddrMask_clean hfit
    have hy' : f1.locals.get? "y" = some (.int (Int.ofNat w.toNat)) := by simpa only [hm] using hy
    exact ⟨f1, ExecFuncBody.execBlockRet (ExecBlock.consNormal h0 (ExecBlock.consNormal h1
      (ExecBlock.consNormal (ExecStmt.iteFalse
        (by simpa only [hm, ne_self_iff_false, decide_false] using hg) ExecBlock.nil)
        (ABlock.start.returns (evalLocalValue hy')))))⟩
  · simp only [if_neg hfit]
    have hm : UInt256.land w solcAddrMask ≠ w :=
      fun he => hfit ((landMask_eq_iff w solcAddrMask (bits := 160) rfl).mp he)
    exact ⟨f1, ExecFuncBody.execBlockRevert (ExecBlock.consNormal h0 (ExecBlock.consNormal h1
      (ExecBlock.consRevert (ExecStmt.iteTrue (by simpa only [decide_eq_true hm] using hg)
        (ExecBlock.consRevert (ExecStmt.requireFalse (by simp only [evalExpr?, pure])))))))⟩

theorem uintToUint160Call {f : Frame} {evm : EVM.State} {w : UInt256} {e : Expr}
    (hf : f.contract = contract) (he : evalExpr? config f evm e = .ok (.int (Int.ofNat w.toNat)))
    (ret : Ident) :
    ExecStmt config f evm (.internalCall "SafeCast_toUint160" [e] ret)
      (if w.toNat < 2^160 then .ok (wordLocal f ret w) evm else .reverted) := by
  let fc : Frame := {f with locals := (∅ : Store).insert "x" (.int (Int.ofNat w.toNat))}
  obtain ⟨f', hbody⟩ := uintToUint160Body (f := fc) (evm := evm) (store_get_self _ _ _)
  have hlookup : lookupCallable? f.contract "SafeCast_toUint160" = some uintToUint160Function.toCallable := by
    rw [hf]; exact uintToUint160_lookup
  by_cases hfit : w.toNat < 2^160
  · rw [if_pos hfit] at hbody ⊢
    exact internalCallFunctionReturn (evalExprs?_singleton he) hlookup rfl hbody
  · rw [if_neg hfit] at hbody ⊢
    exact internalCallFunctionRevert (evalExprs?_singleton he) hlookup rfl hbody

end Benchmarks.UniswapV4PoolManager
