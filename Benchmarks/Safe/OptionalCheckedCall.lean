import Benchmarks.Safe.Membership
import Reasoning.ExternalCall

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe

-- LIBRARY CANDIDATE: an optional, code-checked external call with no transferred value.
def optionalCheckedCall (receiver : Expr) (name : Ident) (args : List Expr)
    (retVar : Ident) : Stmt :=
  .ite (.binary .ne receiver (.cast (.intLit 0) (.elem .address)))
    [.require (.binary .gt (.extCodeSize receiver) (.intLit 0)),
      .externalCall receiver name (.intLit 0) args retVar] []

theorem evalAddressValueNonzero {cfg : Config} {frame : Frame} {evm : EVM.State}
    {receiver : Expr} {target : EVM.Address}
    (he : evalExpr? cfg frame evm receiver = .ok (.address target)) :
    evalExpr? cfg frame evm (.binary .ne receiver (.cast (.intLit 0) (.elem .address))) =
      .ok (.bool (decide (target ≠ 0))) := by
  let word := UInt256.ofNat target.val
  have hw : word.toNat < EVM.addressModulus := by
    rw [ulit_toNat' _ (lt_trans target.isLt (by decide))]
    exact target.isLt
  have ht : AccountAddress.ofNat word.toNat = target := by
    rw [← accountAddress_ofUInt256_eq_ofNat_toNat, accountAddress_roundtrip]
  have hz : target = 0 ↔ word = ⟨0⟩ := by
    simpa only [ht] using canonicalAddress_eq_zero_iff word hw
  have hh := evalAddressNonzero hw (ht ▸ he)
  change evalExpr? cfg frame evm _ = .ok (.bool (decide (word ≠ ⟨0⟩))) at hh
  have hd : decide (word ≠ ⟨0⟩) = decide (target ≠ 0) := by
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    exact not_congr hz.symm
  rw [hd] at hh
  exact hh

theorem optionalCheckedCallZero {cfg : Config} {frame : Frame} {evm : EVM.State}
    {receiver : Expr} {name retVar : Ident} {args : List Expr}
    (he : evalExpr? cfg frame evm receiver = .ok (.address 0)) :
    ExecStmt cfg frame evm (optionalCheckedCall receiver name args retVar) (.ok frame evm) :=
  .iteFalse (by simpa using evalAddressValueNonzero he) .nil

theorem optionalCheckedCallNoCode {cfg : Config} {frame : Frame} {evm : EVM.State}
    {receiver : Expr} {name retVar : Ident} {args : List Expr} {target : EVM.Address}
    {word : UInt256} (he : evalExpr? cfg frame evm receiver = .ok (.address target))
    (hz : target ≠ 0) (ht : target = AccountAddress.ofUInt256 word)
    (hc : extCodeSizeWord evm.accountMap word = ⟨0⟩) :
    ExecStmt cfg frame evm (optionalCheckedCall receiver name args retVar) .reverted := by
  apply ExecStmt.iteTrue (by simpa [hz] using evalAddressValueNonzero he)
  apply checkedExternalCallNoCode
  simpa only [hc, show (⟨0⟩ : UInt256).toNat = 0 from rfl, Nat.lt_irrefl, decide_false] using
    evalExpr_codeGuard_of_accounts_eq rfl ht he

theorem optionalCheckedCallFailure {cfg : Config} {frame : Frame} {evm evm' : EVM.State}
    {receiver : Expr} {name retVar : Ident} {args : List Expr} {argVals : List Value}
    {target : EVM.Address} {word : UInt256} {out : ByteArray}
    (he : evalExpr? cfg frame evm receiver = .ok (.address target))
    (hz : target ≠ 0) (ht : target = AccountAddress.ofUInt256 word)
    (hc : extCodeSizeWord evm.accountMap word ≠ ⟨0⟩)
    (ha : evalExprs? cfg frame evm args = .ok argVals)
    (hcall : typedCallViaEVM cfg evm (EVM.address target) name 0 argVals (false, evm', out)) :
    ExecStmt cfg frame evm (optionalCheckedCall receiver name args retVar) .reverted := by
  apply ExecStmt.iteTrue (by simpa [hz] using evalAddressValueNonzero he)
  apply checkedExternalCallFailure _ he ha hcall
  have hp : 0 < (extCodeSizeWord evm.accountMap word).toNat :=
    Nat.pos_of_ne_zero (fun hz ↦ hc (u256_inj hz))
  simpa only [hp, decide_true] using evalExpr_codeGuard_of_accounts_eq rfl ht he

theorem optionalCheckedCallSuccess {cfg : Config} {frame : Frame} {evm evm' : EVM.State}
    {receiver : Expr} {name retVar : Ident} {args : List Expr} {argVals values : List Value}
    {target : EVM.Address} {word : UInt256} {out : ByteArray}
    (he : evalExpr? cfg frame evm receiver = .ok (.address target))
    (hz : target ≠ 0) (ht : target = AccountAddress.ofUInt256 word)
    (hc : extCodeSizeWord evm.accountMap word ≠ ⟨0⟩)
    (ha : evalExprs? cfg frame evm args = .ok argVals)
    (hcall : typedCallViaEVM cfg evm (EVM.address target) name 0 argVals (true, evm', out))
    (hd : cfg.externalABI.decode? name out = some values) :
    ExecStmt cfg frame evm (optionalCheckedCall receiver name args retVar)
      (.ok { frame with locals := frame.locals.insert retVar (collapseReturns values) } evm') :=
    by
  apply ExecStmt.iteTrue (by simpa [hz] using evalAddressValueNonzero he)
  apply checkedExternalCallSuccess _ he ha hcall hd
  have hp : 0 < (extCodeSizeWord evm.accountMap word).toNat :=
    Nat.pos_of_ne_zero (fun hz ↦ hc (u256_inj hz))
  simpa only [hp, decide_true] using evalExpr_codeGuard_of_accounts_eq rfl ht he

end Benchmarks.Safe
