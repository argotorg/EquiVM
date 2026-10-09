import Benchmarks.CompoundIII.Comet.AbsorbAccountsModel
import Benchmarks.CompoundIII.Comet.AbsorbInternalSource
import Benchmarks.CompoundIII.Comet.AssetSearch

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

def absorbAccountsCond : Expr :=
  .binary .lt (.var "i") (.arrayLength .localVar ⟨"accounts", []⟩)

def absorbAccountsIncrement : Stmt := .assign .localVar ⟨"i", []⟩
  (.cast (.binary .add (.var "i") (.intLit 1)) (.elem (.int (.uint ⟨256, by decide⟩))))

def absorbAccountsBody : List Stmt :=
  [.internalCall "absorbInternal" [.var "absorber", .index (.var "accounts") (.var "i")] "__c2",
    absorbAccountsIncrement]

def absorbAccountsBlock : List Stmt := [.while absorbAccountsCond absorbAccountsBody]

structure AbsorbAccountsFrame (v : CometWithExtendedAssetListImmutables)
    (absorber : AccountAddress) (accounts : List Value) (startGas : UInt256) (i : Nat)
    (frame : Frame) : Prop where
  contract : frame.contract = Comet.contract
  immutables : frame.immutables = immStore v
  absorber : frame.locals.get? "absorber" = some (.address absorber)
  accounts : frame.locals.get? "accounts" = some (.array accounts)
  gas : frame.locals.get? "startGas" = some (.int startGas.toNat)
  index : frame.locals.get? "i" = some (.int i)
  points : frame.locals.get? "liquidatorPoints" = none

def absorbAccountsCallFrame (frame : Frame) : Frame :=
  { frame with locals := frame.locals.insert "__c2" .unit }

def absorbAccountsNextFrame (frame : Frame) (i : Nat) : Frame :=
  { frame with locals := frame.locals.insert "i" (.int (i + 1)) }

theorem AbsorbAccountsFrame.called {v absorber accounts startGas i frame}
    (hf : AbsorbAccountsFrame v absorber accounts startGas i frame) :
    AbsorbAccountsFrame v absorber accounts startGas i (absorbAccountsCallFrame frame) := by
  cases hf
  constructor <;> simp_all only [absorbAccountsCallFrame, Std.HashMap.get?_eq_getElem?,
    Std.HashMap.getElem?_insert] <;> rfl

theorem AbsorbAccountsFrame.next {v absorber accounts startGas i frame}
    (hf : AbsorbAccountsFrame v absorber accounts startGas i frame) :
    AbsorbAccountsFrame v absorber accounts startGas (i + 1) (absorbAccountsNextFrame frame i) := by
  cases hf
  constructor <;> simp_all only [absorbAccountsNextFrame, Std.HashMap.get?_eq_getElem?,
    Std.HashMap.getElem?_insert] <;> rfl

theorem absorbAccountsCond_eval {v absorber accounts startGas i frame}
    (hf : AbsorbAccountsFrame v absorber accounts startGas i frame) (evm : State) :
    evalExpr? config frame evm absorbAccountsCond = .ok (.bool (decide (i < accounts.length))) := by
  simp only [absorbAccountsCond, evalExpr?, hf.index, hf.accounts, readLocalPath?,
    EvalResult.ofOption, pure, bind, EvalResult.bind, evalBinaryOp_lt_int_ok, Int.ofNat_eq_natCast]
  simp only [Int.ofNat_lt]

theorem absorbAccountsIncrement_exec {frame : Frame} {evm : State} {i : Nat}
    (hi : frame.locals.get? "i" = some (.int i)) (hb : i + 1 < UInt256.size) :
    ExecStmt config frame evm absorbAccountsIncrement (.ok (absorbAccountsNextFrame frame i) evm) := by
  apply ExecStmt.assign (value := .int (i + 1))
  · simp only [evalExpr?, hi, EvalResult.ofOption, bind, EvalResult.bind, pure,
      evalBinaryOp_add_int_ok, castValue?]
    have hbound : (i : Int) + 1 < Int.ofNat (EVM.twoPow 256) :=
      Int.ofNat_lt.mpr (show i + 1 < EVM.twoPow 256 from hb)
    rw [normalizeInt_uint_eq_self ⟨256, by decide⟩ ((i : Int) + 1) (by omega) hbound]
  · simp only [assignStorageRef?, hi, updateLocalPath?, pure, bind, EvalResult.bind]
    rfl

theorem absorbAccountsIndex_eval {v absorber accounts startGas i frame cd endOffset}
    (hf : AbsorbAccountsFrame v absorber accounts startGas i frame) (evm : State)
    (hread : Solc0815.decodeAddressArrayElems? (absorbArrayLength cd) (cd.toList.drop 4)
      (absorbArrayOffset cd + 32) = some (accounts, endOffset))
    (hlen : accounts.length = absorbArrayLength cd) (hi : i < absorbArrayLength cd) :
    evalExpr? config frame evm (.index (.var "accounts") (.var "i")) =
      if (absorbArrayAccountWord cd i).toNat < EVM.addressModulus
      then .ok (.address (absorbArrayAccount cd i)) else .revert := by
  simp only [evalExpr?, hf.accounts, hf.index, EvalResult.ofOption, bind, EvalResult.bind]
  exact absorbCalldata_account_index hread hlen hi

theorem absorbAccounts_source {v : CometWithExtendedAssetListImmutables} {cd : ByteArray}
    {i : Nat} {evm : State} {result : InternalOutcome}
    (ht : AbsorbAccountsTrace v cd i evm result)
    {accounts : List Value} {endOffset : Nat} {absorber : AccountAddress} {startGas : UInt256}
    (hread : Solc0815.decodeAddressArrayElems? (absorbArrayLength cd) (cd.toList.drop 4)
      (absorbArrayOffset cd + 32) = some (accounts, endOffset))
    (hlen : accounts.length = absorbArrayLength cd) (hn : absorbArrayLength cd < 2^64)
    (frame : Frame) (hf : AbsorbAccountsFrame v absorber accounts startGas i frame)
    (hib : i ≤ absorbArrayLength cd) :
    match result with
    | .ok evm' => ∃ final, ExecBlock config frame evm absorbAccountsBlock (.ok final evm') ∧
        AbsorbAccountsFrame v absorber accounts startGas (absorbArrayLength cd) final
    | .reverted => ExecBlock config frame evm absorbAccountsBlock .reverted
    | .staticViolation => ExecBlock config frame evm absorbAccountsBlock .staticViolation := by
  induction ht generalizing frame with
  | @exhausted i evm hi =>
      have heq : i = absorbArrayLength cd := by omega
      refine ⟨frame, ExecBlock.consNormal (ExecStmt.whileFalse ?_) .nil, ?_⟩
      · rw [absorbAccountsCond_eval hf evm, hlen, decide_eq_false (by omega)]
      · simpa only [heq] using hf
  | @dirty i evm hi hc =>
      apply ExecBlock.consRevert (ExecStmt.whileRevert ?_ ?_)
      · rw [absorbAccountsCond_eval hf evm, hlen, decide_eq_true hi]
      · apply ExecBlock.consRevert (ExecStmt.internalCallArgsRevert ?_)
        have ha : evalExpr? config frame evm (.var "absorber") = .ok (.address absorber) := by
          simp only [evalExpr?, hf.absorber, EvalResult.ofOption]
        simp only [evalExprs?, ha, absorbAccountsIndex_eval hf evm hread hlen hi, hc,
          if_false, pure, bind, EvalResult.bind]
  | @reverted i evm hi hc ht =>
      apply ExecBlock.consRevert (ExecStmt.whileRevert ?_ ?_)
      · rw [absorbAccountsCond_eval hf evm, hlen, decide_eq_true hi]
      · exact ExecBlock.consRevert (absorbInternal_call ht frame absorber _ _ "__c2"
          hf.contract hf.immutables
          (by simp only [evalExpr?, hf.absorber, EvalResult.ofOption])
          (by rw [absorbAccountsIndex_eval hf evm hread hlen hi, if_pos hc]))
  | @staticViolation i evm hi hc ht =>
      apply ExecBlock.consStatic (ExecStmt.whileStatic ?_ ?_)
      · rw [absorbAccountsCond_eval hf evm, hlen, decide_eq_true hi]
      · exact ExecBlock.consStatic (absorbInternal_call ht frame absorber _ _ "__c2"
          hf.contract hf.immutables
          (by simp only [evalExpr?, hf.absorber, EvalResult.ofOption])
          (by rw [absorbAccountsIndex_eval hf evm hread hlen hi, if_pos hc]))
  | @next i evm evm' result hi hc ht htail ih =>
      have hcall := absorbInternal_call ht frame absorber (.var "absorber")
        (.index (.var "accounts") (.var "i")) "__c2" hf.contract hf.immutables
        (by simp only [evalExpr?, hf.absorber, EvalResult.ofOption])
        (by rw [absorbAccountsIndex_eval hf evm hread hlen hi, if_pos hc])
      have hinc := absorbAccountsIncrement_exec (evm := evm') hf.called.index
        (by change i + 1 < 2^256; omega)
      have hbody : ExecBlock config frame evm absorbAccountsBody
          (.ok (absorbAccountsNextFrame (absorbAccountsCallFrame frame) i) evm') :=
        ExecBlock.consNormal hcall (ExecBlock.consNormal hinc .nil)
      have hcond : evalExpr? config frame evm absorbAccountsCond = .ok (.bool true) := by
        rw [absorbAccountsCond_eval hf evm, hlen, decide_eq_true hi]
      have htailSource := ih _ hf.called.next (by omega)
      cases result with
      | ok evm'' =>
          obtain ⟨final, htailSource, hfinal⟩ := htailSource
          exact ⟨final, execBlock_while_step hcond hbody htailSource, hfinal⟩
      | reverted => exact execBlock_while_step hcond hbody htailSource
      | staticViolation => exact execBlock_while_step hcond hbody htailSource

end Benchmarks.CompoundIII.Comet
