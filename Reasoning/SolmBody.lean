import Solm.Equiv
import Reasoning.EVMWord

/-!
# SolmBody — compositional lemmas for the Solm contract body

The Solm-side analogue of the EVM trace: facts about `ExecTransitionBody` / `ExecStmt`, all
contract-agnostic:

- the **non-payable guard** `require(callvalue == 0)` that opens each transition body — its
  evaluation (both directions) and the body-revert it produces under non-zero call value;
- internal-call unfolding, and wrappers for external / checked / low-level / delegate calls;
- Hoare-style while/for loop rules;
- the `ABlock` forward block builder;
- `Solm.Store` (locals) lookup and storage-access collapse lemmas.
-/

open Solm ABI Ethereum

namespace Reasoning.Theory

/-- The non-payable guard `callvalue == 0` evaluates to `true` when the call value is zero. -/
theorem evalCallvalueEq_true {cfg : Config} {solm : Frame} {evm : EVM.State}
    (h : evm.executionEnv.weiValue = ⟨0⟩) :
    evalExpr? cfg solm evm (.binary .eq (.env .callvalue) (.intLit 0)) = .ok (.bool true) := by
  have hval : (Value.int (Int.ofNat evm.executionEnv.weiValue.val) == Value.int 0) = true := by
    rw [h]; rfl
  simp only [evalExpr?, EvalResult.bind, bind, pure, envValue, evalBinaryOp?, hval]

/-- The non-payable guard `callvalue == 0` evaluates to `false` when the call value is non-zero. -/
theorem evalCallvalueEq_false {cfg : Config} {solm : Frame} {evm : EVM.State}
    (h : evm.executionEnv.weiValue ≠ ⟨0⟩) :
    evalExpr? cfg solm evm (.binary .eq (.env .callvalue) (.intLit 0)) = .ok (.bool false) := by
  have hval : (Value.int (Int.ofNat evm.executionEnv.weiValue.val) == Value.int 0) = false := by
    rw [beq_eq_false_iff_ne]; intro hh; rw [Value.int.injEq] at hh
    exact h (uint256_toNat_eq_zero (Int.ofNat.inj hh))
  simp only [evalExpr?, EvalResult.bind, bind, pure, envValue, evalBinaryOp?, hval]

/-- **The non-payable guard reverts the body.**  Any transition whose body opens with
    `require(callvalue == 0)` reverts when the call value is non-zero — independent of the rest of
    the body.  Shared by every contract's `callvalue ≠ 0` case. -/
theorem bodyReverts_nonPayable {cfg : Config} {contract : ContractDecl} {evm : EVM.State}
    {locals : Store} {rest : List Stmt}
    (h : evm.executionEnv.weiValue ≠ ⟨0⟩) :
    ExecTransitionBody cfg contract evm locals
      (.require (.binary .eq (.env .callvalue) (.intLit 0)) :: rest) .reverted :=
  ExecFuncBody.execBlockRevert (ExecBlock.consRevert (ExecStmt.requireFalse (evalCallvalueEq_false h)))

/-- Block-level form of the non-payable revert: the guard fails under non-zero call value. -/
theorem blockReverts_nonPayable {cfg : Config} {solm : Frame} {evm : EVM.State}
    {rest : List Stmt} (h : evm.executionEnv.weiValue ≠ ⟨0⟩) :
    ExecBlock cfg solm evm
      (.require (.binary .eq (.env .callvalue) (.intLit 0)) :: rest) .reverted :=
  ExecBlock.consRevert (ExecStmt.requireFalse (evalCallvalueEq_false h))

/-- The common `require(callvalue == 0); require(guard); storage := rhs` block, all three
    statements succeeding. -/
theorem nonpayableRequireAssignStorageBlock {cfg : Config} {solm : Frame}
    {evm evm' : EVM.State} {guard rhs : Expr} {ref : StorageRef} {value : Value}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hguard : evalExpr? cfg solm evm guard = .ok (.bool true))
    (hrhs : evalExpr? cfg solm evm rhs = .ok value)
    (hassign : assignStorageRef? cfg solm evm .storage ref value = .ok (solm, evm')) :
    ExecBlock cfg solm evm
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .require guard,
        .assign .storage ref rhs ]
      (.ok solm evm') := by
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
  exact ExecBlock.consNormal (ExecStmt.assign hrhs hassign) ExecBlock.nil

/-- Static-call twin of `nonpayableRequireAssignStorageBlock`: both guards pass and the storage
    assignment halts; later statements never run. -/
theorem nonpayableRequireAssignStorageBlockStatic {cfg : Config} {solm solm' : Frame}
    {evm evm' : EVM.State} {guard rhs : Expr} {ref : StorageRef} {value : Value}
    {rest : List Stmt}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hguard : evalExpr? cfg solm evm guard = .ok (.bool true))
    (hrhs : evalExpr? cfg solm evm rhs = .ok value)
    (hassign : assignStorageRef? cfg solm evm .storage ref value = .ok (solm', evm'))
    (hperm : evm.executionEnv.perm = false) :
    ExecBlock cfg solm evm
      (.require (.binary .eq (.env .callvalue) (.intLit 0)) ::
        .require guard :: .assign .storage ref rhs :: rest)
      .staticViolation := by
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
  exact ExecBlock.consStatic (ExecStmt.assignStatic hrhs hassign hperm)

/-- A storage assignment that succeeds halts instead when run in a static call. -/
theorem execStmt_assign_static {cfg : Config} {solm solm' : Frame} {evm evm' : EVM.State}
    {slot : StorageRef} {rhs : Expr}
    (h : ExecStmt cfg solm evm (.assign .storage slot rhs) (.ok solm' evm'))
    (hperm : evm.executionEnv.perm = false) :
    ExecStmt cfg solm evm (.assign .storage slot rhs) .staticViolation := by
  cases h with
  | assign heval hassign => exact ExecStmt.assignStatic heval hassign hperm

/-- The non-payable guard passes but the second `require(guard)` fails: the block reverts. -/
theorem nonpayableSecondRequireReverts {cfg : Config} {solm : Frame}
    {evm : EVM.State} {guard : Expr} {rest : List Stmt}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hguard : evalExpr? cfg solm evm guard = .ok (.bool false)) :
    ExecBlock cfg solm evm
      (.require (.binary .eq (.env .callvalue) (.intLit 0)) :: .require guard :: rest)
      .reverted := by
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  exact ExecBlock.consRevert (ExecStmt.requireFalse hguard)

/-- A singleton `storage := rhs` block, evaluating and assigning in one step. -/
theorem assignStorageBlock {cfg : Config} {solm : Frame} {evm evm' : EVM.State}
    {rhs : Expr} {ref : StorageRef} {value : Value}
    (hrhs : evalExpr? cfg solm evm rhs = .ok value)
    (hassign : assignStorageRef? cfg solm evm .storage ref value = .ok (solm, evm')) :
    ExecBlock cfg solm evm [ .assign .storage ref rhs ] (.ok solm evm') := by
  exact ExecBlock.consNormal (ExecStmt.assign hrhs hassign) ExecBlock.nil

/-- A single-expression `return` evaluates its one operand into a singleton value list. -/
theorem evalExprs?_singleton {cfg : Config} {solm : Frame} {evm : EVM.State}
    {e : Expr} {v : Value} (h : evalExpr? cfg solm evm e = .ok v) :
    evalExprs? cfg solm evm [e] = .ok [v] := by
  simp only [evalExprs?, h, bind, EvalResult.bind, pure]

theorem nonpayableBytesLiteralBodyReturns {cfg : Config} {contract : ContractDecl}
    (evm : EVM.State) (locals : Store) (bytes : ByteArray)
    (h : evm.executionEnv.weiValue = ⟨0⟩) :
    ExecTransitionBody cfg contract evm locals
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .return [.bytesLit bytes] ]
      (.returned { contract := contract, locals := locals } evm (some [.bytes bytes])) := by
  exact ExecFuncBody.execBlockRet <|
    ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true h)) <|
      ExecBlock.consReturn (ExecStmt.return (evalExprs?_singleton (by simp [evalExpr?, pure])))

theorem nonpayableReturnExprBodyReturns {cfg : Config} {contract : ContractDecl}
    {evm : EVM.State} {locals : Store} {expr : Expr} {value : Value}
    (h : evm.executionEnv.weiValue = ⟨0⟩)
    (heval : evalExpr? cfg { contract := contract, locals := locals } evm expr = .ok value) :
    ExecTransitionBody cfg contract evm locals
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .return [expr] ]
      (.returned { contract := contract, locals := locals } evm (some [value])) := by
  exact ExecFuncBody.execBlockRet <|
    ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true h)) <|
      ExecBlock.consReturn (ExecStmt.return (evalExprs?_singleton heval))

theorem nonpayableIntLiteralBodyReturns {cfg : Config} {contract : ContractDecl}
    (evm : EVM.State) (locals : Store) (n : Int)
    (h : evm.executionEnv.weiValue = ⟨0⟩) :
    ExecTransitionBody cfg contract evm locals
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .return [.intLit n] ]
      (.returned { contract := contract, locals := locals } evm (some [.int n])) := by
  exact nonpayableReturnExprBodyReturns h (by simp [evalExpr?, pure])

theorem nonpayableFixedBytesLiteralBodyReturns {cfg : Config} {contract : ContractDecl}
    (evm : EVM.State) (locals : Store) (n : Fin 32) (bytes : List UInt8)
    (h : evm.executionEnv.weiValue = ⟨0⟩) :
    ExecTransitionBody cfg contract evm locals
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .return [.fixedBytesLit n bytes] ]
      (.returned { contract := contract, locals := locals } evm (some [.fixedBytes n bytes])) := by
  exact nonpayableReturnExprBodyReturns h (by simp [evalExpr?, pure])

/-! ## Source values -/

abbrev uint256Value (w : UInt256) : Value :=
  .int (Int.ofNat w.toNat)

theorem evalExpr_timestampModUint32 {cfg : Config} {solm : Frame} (evm : EVM.State) :
    evalExpr? cfg solm evm
      (.inRange (.uint ⟨32, by decide⟩)
        (.binary .mod (.env .timestamp) (.intLit ((2 : Int) ^ 32)))) =
      .ok (.int (Int.ofNat (UInt256.ofNat evm.executionEnv.header.timestamp).toNat %
        ((2 : Int) ^ 32))) := by
  simp only [evalExpr?, envValue, EvalResult.bind, bind, pure, evalBinaryOp?]
  norm_num
  intro _hbad
  have hnonneg :
      0 ≤ Int.ofNat (UInt256.ofNat evm.executionEnv.header.timestamp).toNat %
        (4294967296 : Int) := by
    exact Int.emod_nonneg _ (by norm_num)
  have hlt :
      Int.ofNat (UInt256.ofNat evm.executionEnv.header.timestamp).toNat %
          (4294967296 : Int) <
        4294967296 := by
    exact Int.emod_lt_of_pos _ (by norm_num)
  omega

/-! ## Internal calls -/

/-- Run an internal call to a transition and bind its returned value in the caller's frame.

This packages `ExecStmt.internalCallReturn` for the common case where an externally callable
`TransitionDecl` is also the target of an internal call.  The callee body proof can be reused as an
`ExecTransitionBody`, while the conclusion exposes the caller-local `retVar` update directly. -/
theorem internalCallTransitionReturn {cfg : Config} {caller : Frame} {evm calleeEvm : EVM.State}
    {name retVar : Ident} {args : List Expr} {argVals : List Value}
    {callee : TransitionDecl} {locals : Store} {calleeSolm : Frame} {value : Value}
    (hargs : evalExprs? cfg caller evm args = .ok argVals)
    (hlookup : lookupCallable? caller.contract name = some callee.toCallable)
    (hbind : bindParams? callee.params argVals = some locals)
    (hbody : ExecTransitionBody cfg caller.contract evm locals callee.body
      (.returned calleeSolm calleeEvm (some [value]))) :
    ExecStmt cfg caller evm (.internalCall name args retVar)
      (.ok { caller with locals := caller.locals.insert retVar value } calleeEvm) := by
  simpa [TransitionDecl.toCallable, ExecTransitionBody, resumeAfterInternalCall] using
    ExecStmt.internalCallReturn (cfg := cfg) (solm := caller) (evm := evm) (name := name)
      (args := args) (retVar := retVar) (argVals := argVals) (callee := callee.toCallable)
      (locals := locals) (calleeSolm := calleeSolm) (calleeEvm := calleeEvm)
      (value := some [value]) hargs hlookup (by simpa [TransitionDecl.toCallable] using hbind)
      (by simpa [ExecTransitionBody, TransitionDecl.toCallable] using hbody)

/-- If an internal call's transition body reverts, the internal-call statement reverts. -/
theorem internalCallTransitionRevert {cfg : Config} {caller : Frame} {evm : EVM.State}
    {name retVar : Ident} {args : List Expr} {argVals : List Value}
    {callee : TransitionDecl} {locals : Store}
    (hargs : evalExprs? cfg caller evm args = .ok argVals)
    (hlookup : lookupCallable? caller.contract name = some callee.toCallable)
    (hbind : bindParams? callee.params argVals = some locals)
    (hbody : ExecTransitionBody cfg caller.contract evm locals callee.body .reverted) :
    ExecStmt cfg caller evm (.internalCall name args retVar) .reverted := by
  exact ExecStmt.internalCallRevert (cfg := cfg) (solm := caller) (evm := evm) (name := name)
    (args := args) (retVar := retVar) (argVals := argVals) (callee := callee.toCallable)
    (locals := locals) hargs hlookup (by simpa [TransitionDecl.toCallable] using hbind)
    (by simpa [ExecTransitionBody, TransitionDecl.toCallable] using hbody)

/-- `FunctionDecl` analogue of `internalCallTransitionReturn`, for internal/private Solidity
helper calls. -/
theorem internalCallFunctionReturn {cfg : Config} {caller : Frame} {evm calleeEvm : EVM.State}
    {name retVar : Ident} {args : List Expr} {argVals : List Value}
    {callee : FunctionDecl} {locals : Store} {calleeSolm : Frame} {value : Option (List Value)}
    (hargs : evalExprs? cfg caller evm args = .ok argVals)
    (hlookup : lookupCallable? caller.contract name = some callee.toCallable)
    (hbind : bindParams? callee.params argVals = some locals)
    (hbody : ExecFuncBody cfg { caller with locals := locals } evm callee.body
      (.returned calleeSolm calleeEvm value)) :
    ExecStmt cfg caller evm (.internalCall name args retVar)
      (.ok (resumeAfterInternalCall caller retVar value) calleeEvm) := by
  exact ExecStmt.internalCallReturn (cfg := cfg) (solm := caller) (evm := evm)
    (name := name) (args := args) (retVar := retVar) (argVals := argVals)
    (callee := callee.toCallable) (locals := locals) (calleeSolm := calleeSolm)
    (calleeEvm := calleeEvm) (value := value)
    hargs hlookup (by simpa [FunctionDecl.toCallable] using hbind)
    (by simpa [FunctionDecl.toCallable] using hbody)

/-- If an internal/private Solidity helper's body reverts, the internal-call statement reverts. -/
theorem internalCallFunctionRevert {cfg : Config} {caller : Frame} {evm : EVM.State}
    {name retVar : Ident} {args : List Expr} {argVals : List Value}
    {callee : FunctionDecl} {locals : Store}
    (hargs : evalExprs? cfg caller evm args = .ok argVals)
    (hlookup : lookupCallable? caller.contract name = some callee.toCallable)
    (hbind : bindParams? callee.params argVals = some locals)
    (hbody : ExecFuncBody cfg { caller with locals := locals } evm callee.body .reverted) :
    ExecStmt cfg caller evm (.internalCall name args retVar) .reverted := by
  exact ExecStmt.internalCallRevert (cfg := cfg) (solm := caller) (evm := evm)
    (name := name) (args := args) (retVar := retVar) (argVals := argVals)
    (callee := callee.toCallable) (locals := locals)
    hargs hlookup (by simpa [FunctionDecl.toCallable] using hbind)
    (by simpa [FunctionDecl.toCallable] using hbody)

/-! ## External calls -/

/-- A one-statement typed external call reverts when the raw call returns `success = false`. -/
theorem externalCallFailure {cfg : Config} {C : ContractDecl}
    {evm evm' : EVM.State} {locals : Store}
    {receiver : Expr} {retVar name : Ident} {target : AccountAddress} {sendVal : Int}
    {args : List Expr} {argVals : List Value} {out : ByteArray} {perm : Bool}
    (hreceiver :
      evalExpr? cfg { contract := C, locals := locals } evm receiver = .ok (.address target))
    (hargs : evalExprs? cfg { contract := C, locals := locals } evm args = .ok argVals)
    (hcall :
      typedCallViaEVM cfg evm (EVM.address target) name sendVal argVals
        (false, evm', out) perm) :
    ExecBlock cfg { contract := C, locals := locals } evm
      [ .externalCall receiver name (.intLit sendVal) args retVar (perm := perm) ]
      .reverted := by
  exact ExecBlock.consRevert
    (ExecStmt.externalCallFailure hreceiver (by simp [evalExpr?, pure]) hargs hcall)

/-- A one-statement typed external call succeeds and stores the decoded return value. -/
theorem externalCallSuccess {cfg : Config} {C : ContractDecl}
    {evm evm' : EVM.State} {locals : Store}
    {receiver : Expr} {retVar name : Ident} {target : AccountAddress} {sendVal : Int}
    {args : List Expr} {argVals : List Value} {out : ByteArray} {perm : Bool} {value : List Value}
    (hreceiver :
      evalExpr? cfg { contract := C, locals := locals } evm receiver = .ok (.address target))
    (hargs : evalExprs? cfg { contract := C, locals := locals } evm args = .ok argVals)
    (hcall :
      typedCallViaEVM cfg evm (EVM.address target) name sendVal argVals
        (true, evm', out) perm)
    (hdec : cfg.externalABI.decode? name out = some value) :
    ExecBlock cfg { contract := C, locals := locals } evm
      [ .externalCall receiver name (.intLit sendVal) args retVar (perm := perm) ]
      (.ok { contract := C, locals := locals.insert retVar (collapseReturns value) } evm') := by
  exact ExecBlock.consNormal
    (ExecStmt.externalCallSuccess hreceiver (by simp [evalExpr?, pure]) hargs hcall hdec)
    ExecBlock.nil

/-- If a typed external call succeeds but its return bytes fail ABI decoding, the source statement
reverts. -/
theorem externalCallDecodeRevert {cfg : Config} {C : ContractDecl}
    {evm evm' : EVM.State} {locals : Store}
    {receiver : Expr} {retVar name : Ident} {target : AccountAddress} {sendVal : Int}
    {args : List Expr} {argVals : List Value} {out : ByteArray} {perm : Bool}
    (hreceiver :
      evalExpr? cfg { contract := C, locals := locals } evm receiver = .ok (.address target))
    (hargs : evalExprs? cfg { contract := C, locals := locals } evm args = .ok argVals)
    (hcall :
      typedCallViaEVM cfg evm (EVM.address target) name sendVal argVals
        (true, evm', out) perm)
    (hdec : cfg.externalABI.decode? name out = none) :
    ExecBlock cfg { contract := C, locals := locals } evm
      [ .externalCall receiver name (.intLit sendVal) args retVar (perm := perm) ]
      .reverted := by
  exact ExecBlock.consRevert
    (ExecStmt.externalCallReturnDecodeRevert hreceiver (by simp [evalExpr?, pure]) hargs hcall hdec)

/-- A guarded typed external call reverts when the raw call returns `success = false`. -/
theorem checkedExternalCallFailure {cfg : Config} {C : ContractDecl}
    {evm evm' : EVM.State} {locals : Store}
    {receiver : Expr} {retVar name : Ident} {target : AccountAddress} {sendVal : Int}
    {args : List Expr} {argVals : List Value} {out : ByteArray} {perm : Bool}
    (hguard :
      evalExpr? cfg { contract := C, locals := locals } evm
        (.binary .gt (.extCodeSize receiver) (.intLit 0)) = .ok (.bool true))
    (hreceiver :
      evalExpr? cfg { contract := C, locals := locals } evm receiver = .ok (.address target))
    (hargs : evalExprs? cfg { contract := C, locals := locals } evm args = .ok argVals)
    (hcall :
      typedCallViaEVM cfg evm (EVM.address target) name sendVal argVals
        (false, evm', out) perm) :
    ExecBlock cfg { contract := C, locals := locals } evm
      [ .require (.binary .gt (.extCodeSize receiver) (.intLit 0)),
        .externalCall receiver name (.intLit sendVal) args retVar (perm := perm) ]
      .reverted := by
  refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
  exact externalCallFailure hreceiver hargs hcall

/-- A guarded typed external call succeeds and stores the decoded return value. -/
theorem checkedExternalCallSuccess {cfg : Config} {C : ContractDecl}
    {evm evm' : EVM.State} {locals : Store}
    {receiver : Expr} {retVar name : Ident} {target : AccountAddress} {sendVal : Int}
    {args : List Expr} {argVals : List Value} {out : ByteArray} {perm : Bool} {value : List Value}
    (hguard :
      evalExpr? cfg { contract := C, locals := locals } evm
        (.binary .gt (.extCodeSize receiver) (.intLit 0)) = .ok (.bool true))
    (hreceiver :
      evalExpr? cfg { contract := C, locals := locals } evm receiver = .ok (.address target))
    (hargs : evalExprs? cfg { contract := C, locals := locals } evm args = .ok argVals)
    (hcall :
      typedCallViaEVM cfg evm (EVM.address target) name sendVal argVals
        (true, evm', out) perm)
    (hdec : cfg.externalABI.decode? name out = some value) :
    ExecBlock cfg { contract := C, locals := locals } evm
      [ .require (.binary .gt (.extCodeSize receiver) (.intLit 0)),
        .externalCall receiver name (.intLit sendVal) args retVar (perm := perm) ]
      (.ok { contract := C, locals := locals.insert retVar (collapseReturns value) } evm') := by
  refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
  exact externalCallSuccess hreceiver hargs hcall hdec

/-- A guarded typed external call reverts when the successful subcall's return bytes do not
decode. -/
theorem checkedExternalCallDecodeRevert {cfg : Config} {C : ContractDecl}
    {evm evm' : EVM.State} {locals : Store}
    {receiver : Expr} {retVar name : Ident} {target : AccountAddress} {sendVal : Int}
    {args : List Expr} {argVals : List Value} {out : ByteArray} {perm : Bool}
    (hguard :
      evalExpr? cfg { contract := C, locals := locals } evm
        (.binary .gt (.extCodeSize receiver) (.intLit 0)) = .ok (.bool true))
    (hreceiver :
      evalExpr? cfg { contract := C, locals := locals } evm receiver = .ok (.address target))
    (hargs : evalExprs? cfg { contract := C, locals := locals } evm args = .ok argVals)
    (hcall :
      typedCallViaEVM cfg evm (EVM.address target) name sendVal argVals
        (true, evm', out) perm)
    (hdec : cfg.externalABI.decode? name out = none) :
    ExecBlock cfg { contract := C, locals := locals } evm
      [ .require (.binary .gt (.extCodeSize receiver) (.intLit 0)),
        .externalCall receiver name (.intLit sendVal) args retVar (perm := perm) ]
      .reverted := by
  refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
  exact externalCallDecodeRevert hreceiver hargs hcall hdec

/-- A guarded typed external call reverts before the call when the extcodesize guard is false. -/
theorem checkedExternalCallNoCode {cfg : Config} {C : ContractDecl} {evm : EVM.State}
    {locals : Store} {receiver : Expr} {retVar name : Ident} {sendVal : Int}
    {args : List Expr} {perm : Bool}
    (hguard :
      evalExpr? cfg { contract := C, locals := locals } evm
        (.binary .gt (.extCodeSize receiver) (.intLit 0)) = .ok (.bool false)) :
    ExecBlock cfg { contract := C, locals := locals } evm
      [ .require (.binary .gt (.extCodeSize receiver) (.intLit 0)),
        .externalCall receiver name (.intLit sendVal) args retVar (perm := perm) ]
      .reverted := by
  exact ExecBlock.consRevert (ExecStmt.requireFalse hguard)

/-- A one-statement typed external call through an address-valued local succeeds and stores the
decoded return value. -/
theorem externalCallVarSuccess {cfg : Config} {C : ContractDecl}
    {evm evm' : EVM.State} {locals : Store}
    {receiver retVar name : Ident} {target : AccountAddress} {sendVal : Int}
    {args : List Expr} {argVals : List Value} {out : ByteArray} {perm : Bool} {value : List Value}
    (hreceiver : locals.get? receiver = some (.address target))
    (hargs : evalExprs? cfg { contract := C, locals := locals } evm args = .ok argVals)
    (hcall :
      typedCallViaEVM cfg evm (EVM.address target) name sendVal argVals
        (true, evm', out) perm)
    (hdec : cfg.externalABI.decode? name out = some value) :
    ExecBlock cfg { contract := C, locals := locals } evm
      [ .externalCall (.var receiver) name (.intLit sendVal) args retVar (perm := perm) ]
      (.ok { contract := C, locals := locals.insert retVar (collapseReturns value) } evm') := by
  exact externalCallSuccess
    (receiver := .var receiver)
    (by rw [evalExpr?, hreceiver]; rfl)
    hargs hcall hdec

/-- A guarded typed external call through an address-valued local reverts when the raw call
returns `success = false`. -/
theorem checkedExternalCallVarFailure {cfg : Config} {C : ContractDecl}
    {evm evm' : EVM.State} {locals : Store}
    {receiver retVar name : Ident} {target : AccountAddress} {sendVal : Int}
    {args : List Expr} {argVals : List Value} {out : ByteArray} {perm : Bool}
    (hguard :
      evalExpr? cfg { contract := C, locals := locals } evm
        (.binary .gt (.extCodeSize (.var receiver)) (.intLit 0)) = .ok (.bool true))
    (hreceiver : locals.get? receiver = some (.address target))
    (hargs : evalExprs? cfg { contract := C, locals := locals } evm args = .ok argVals)
    (hcall :
      typedCallViaEVM cfg evm (EVM.address target) name sendVal argVals
        (false, evm', out) perm) :
    ExecBlock cfg { contract := C, locals := locals } evm
      [ .require (.binary .gt (.extCodeSize (.var receiver)) (.intLit 0)),
        .externalCall (.var receiver) name (.intLit sendVal) args retVar (perm := perm) ]
      .reverted := by
  exact checkedExternalCallFailure
    (receiver := .var receiver)
    hguard
    (by rw [evalExpr?, hreceiver]; rfl)
    hargs hcall

/-- A guarded typed external call through an address-valued local succeeds and stores the decoded
return value. -/
theorem checkedExternalCallVarSuccess {cfg : Config} {C : ContractDecl}
    {evm evm' : EVM.State} {locals : Store}
    {receiver retVar name : Ident} {target : AccountAddress} {sendVal : Int}
    {args : List Expr} {argVals : List Value} {out : ByteArray} {perm : Bool} {value : List Value}
    (hguard :
      evalExpr? cfg { contract := C, locals := locals } evm
        (.binary .gt (.extCodeSize (.var receiver)) (.intLit 0)) = .ok (.bool true))
    (hreceiver : locals.get? receiver = some (.address target))
    (hargs : evalExprs? cfg { contract := C, locals := locals } evm args = .ok argVals)
    (hcall :
      typedCallViaEVM cfg evm (EVM.address target) name sendVal argVals
        (true, evm', out) perm)
    (hdec : cfg.externalABI.decode? name out = some value) :
    ExecBlock cfg { contract := C, locals := locals } evm
      [ .require (.binary .gt (.extCodeSize (.var receiver)) (.intLit 0)),
        .externalCall (.var receiver) name (.intLit sendVal) args retVar (perm := perm) ]
      (.ok { contract := C, locals := locals.insert retVar (collapseReturns value) } evm') := by
  exact checkedExternalCallSuccess
    (receiver := .var receiver)
    hguard
    (by rw [evalExpr?, hreceiver]; rfl)
    hargs hcall hdec

/-- A guarded typed external call through an address-valued local reverts when the successful
subcall's return bytes do not decode. -/
theorem checkedExternalCallVarDecodeRevert {cfg : Config} {C : ContractDecl}
    {evm evm' : EVM.State} {locals : Store}
    {receiver retVar name : Ident} {target : AccountAddress} {sendVal : Int}
    {args : List Expr} {argVals : List Value} {out : ByteArray} {perm : Bool}
    (hguard :
      evalExpr? cfg { contract := C, locals := locals } evm
        (.binary .gt (.extCodeSize (.var receiver)) (.intLit 0)) = .ok (.bool true))
    (hreceiver : locals.get? receiver = some (.address target))
    (hargs : evalExprs? cfg { contract := C, locals := locals } evm args = .ok argVals)
    (hcall :
      typedCallViaEVM cfg evm (EVM.address target) name sendVal argVals
        (true, evm', out) perm)
    (hdec : cfg.externalABI.decode? name out = none) :
    ExecBlock cfg { contract := C, locals := locals } evm
      [ .require (.binary .gt (.extCodeSize (.var receiver)) (.intLit 0)),
        .externalCall (.var receiver) name (.intLit sendVal) args retVar (perm := perm) ]
      .reverted := by
  exact checkedExternalCallDecodeRevert
    (receiver := .var receiver)
    hguard
    (by rw [evalExpr?, hreceiver]; rfl)
    hargs hcall hdec

/-- A guarded typed external call reverts before the call when the extcodesize guard is false. -/
theorem checkedExternalCallVarNoCode {cfg : Config} {C : ContractDecl} {evm : EVM.State}
    {locals : Store} {receiver retVar name : Ident} {sendVal : Int}
    {args : List Expr} {perm : Bool}
    (hguard :
      evalExpr? cfg { contract := C, locals := locals } evm
        (.binary .gt (.extCodeSize (.var receiver)) (.intLit 0)) = .ok (.bool false)) :
    ExecBlock cfg { contract := C, locals := locals } evm
      [ .require (.binary .gt (.extCodeSize (.var receiver)) (.intLit 0)),
        .externalCall (.var receiver) name (.intLit sendVal) args retVar (perm := perm) ]
      .reverted := by
  exact checkedExternalCallNoCode (receiver := .var receiver) hguard

/-! ## Low-level calls -/

/-- A low-level call followed by `require cond` succeeds when the call returns `success = true` and
the post-call condition evaluates to `true` in the frame containing `(okVar, dataVar)`. -/
theorem lowLevelCallSuccessThenRequireTrue {cfg : Config} {C : ContractDecl}
    {evm evm' : EVM.State} {locals : Store}
    {receiver eth cdata requireCond : Expr} {okVar dataVar : Ident}
    {target : AccountAddress} {sendVal : Int} {calldata out : ByteArray}
    (hreceiver : evalExpr? cfg { contract := C, locals := locals } evm receiver =
      .ok (.address target))
    (heth : evalExpr? cfg { contract := C, locals := locals } evm eth = .ok (.int sendVal))
    (hdata : evalExpr? cfg { contract := C, locals := locals } evm cdata =
      .ok (.bytes calldata))
    (hcall : callViaEVM evm (EVM.address target) sendVal calldata (true, evm', out))
    (hrequire :
      evalExpr? cfg
        { contract := C, locals := (locals.insert okVar (.bool true)).insert dataVar (.bytes out) }
        evm' requireCond = .ok (.bool true)) :
    ExecBlock cfg { contract := C, locals := locals } evm
      [ .lowLevelCall receiver eth cdata okVar dataVar,
        .require requireCond ]
      (.ok
        { contract := C,
          locals := (locals.insert okVar (.bool true)).insert dataVar (.bytes out) } evm') := by
  refine ExecBlock.consNormal
    (solm' := { contract := C, locals := (locals.insert okVar (.bool true)).insert dataVar (.bytes out) })
    (evm' := evm') ?_ ?_
  · exact ExecStmt.lowLevelCallSuccess hreceiver heth hdata hcall
  · exact ExecBlock.consNormal (ExecStmt.requireTrue hrequire) ExecBlock.nil

/-- A low-level call followed by `require cond` reverts when the call returns `success = false` and
the post-call condition evaluates to `false` in the frame containing `(okVar, dataVar)`. -/
theorem lowLevelCallFailureThenRequireFalse {cfg : Config} {C : ContractDecl}
    {evm evm' : EVM.State} {locals : Store}
    {receiver eth cdata requireCond : Expr} {okVar dataVar : Ident}
    {target : AccountAddress} {sendVal : Int} {calldata out : ByteArray}
    (hreceiver : evalExpr? cfg { contract := C, locals := locals } evm receiver =
      .ok (.address target))
    (heth : evalExpr? cfg { contract := C, locals := locals } evm eth = .ok (.int sendVal))
    (hdata : evalExpr? cfg { contract := C, locals := locals } evm cdata =
      .ok (.bytes calldata))
    (hcall : callViaEVM evm (EVM.address target) sendVal calldata (false, evm', out))
    (hrequire :
      evalExpr? cfg
        { contract := C, locals := (locals.insert okVar (.bool false)).insert dataVar (.bytes out) }
        evm' requireCond = .ok (.bool false)) :
    ExecBlock cfg { contract := C, locals := locals } evm
      [ .lowLevelCall receiver eth cdata okVar dataVar,
        .require requireCond ]
      .reverted := by
  refine ExecBlock.consNormal
    (solm' :=
      { contract := C, locals := (locals.insert okVar (.bool false)).insert dataVar (.bytes out) })
    (evm' := evm') ?_ ?_
  · exact ExecStmt.lowLevelCallFailure hreceiver heth hdata hcall
  · exact ExecBlock.consRevert (ExecStmt.requireFalse hrequire)

/-- **Hoare while-rule for the Solm semantics** — the loop analog of the EVM `RD.loop`.

    A variant-indexed invariant `P : ℕ → Store → Prop` (`P v L` = "invariant holds with `v`
    iterations to go") that
    * makes the loop condition **false** at variant `0` (`hfalse`),
    * makes it **true** at `v+1` (`htrue`), and
    * carries one body iteration from `P (v+1)` to `P v`, leaving the EVM state and contract fixed
      (`hstep`),
    drives the `while` to a final store satisfying `P 0`, from any starting variant.  The EVM state
    and contract are loop-invariant; only the locals change (an Solm loop touches no EVM state). -/
theorem execWhile_var {cfg : Config} {C : ContractDecl} {evm : EVM.State}
    {cond : Expr} {body : List Stmt} (P : ℕ → Solm.Store → Prop)
    (hfalse : ∀ L, P 0 L →
        evalExpr? cfg { contract := C, locals := L } evm cond = .ok (.bool false))
    (htrue : ∀ v L, P (v + 1) L →
        evalExpr? cfg { contract := C, locals := L } evm cond = .ok (.bool true))
    (hstep : ∀ v L, P (v + 1) L →
        ∃ L', ExecBlock cfg { contract := C, locals := L } evm body
                (.ok { contract := C, locals := L' } evm) ∧ P v L') :
    ∀ v L, P v L → ∃ L',
      ExecStmt cfg { contract := C, locals := L } evm (.while cond body)
        (.ok { contract := C, locals := L' } evm) ∧ P 0 L' := by
  intro v
  induction v with
  | zero => intro L hP; exact ⟨L, ExecStmt.whileFalse (hfalse L hP), hP⟩
  | succ v ih =>
    intro L hP
    obtain ⟨L1, hbody, hP1⟩ := hstep v L hP
    obtain ⟨L', hwhile, hP'⟩ := ih L1 hP1
    exact ⟨L', ExecStmt.whileTrue (htrue v L hP) hbody hwhile, hP'⟩

/-- **Hoare for-loop rule** — the `for` analog of `execWhile_var`, for the loop body `ExecForLoop`
    (after `init` has already run).  A variant-indexed invariant `P` that makes the condition false
    at variant `0`, true at `v+1`, and is preserved by **one iteration of `body` followed by `post`**
    (`hstep`), drives the loop to a final store satisfying `P 0`.  Wrap with `ExecStmt.for hinit …`
    (running `init`) to get a full `ExecStmt (.for …)`.  As in `execWhile_var`, the EVM state and
    contract are loop-invariant; only the locals change. -/
theorem execFor_var {cfg : Config} {C : ContractDecl} {evm : EVM.State}
    {condExpr : Expr} {post body : List Stmt} (P : ℕ → Solm.Store → Prop)
    (hfalse : ∀ L, P 0 L →
        evalExpr? cfg { contract := C, locals := L } evm condExpr = .ok (.bool false))
    (htrue : ∀ v L, P (v + 1) L →
        evalExpr? cfg { contract := C, locals := L } evm condExpr = .ok (.bool true))
    (hstep : ∀ v L, P (v + 1) L →
        ∃ L1, ExecBlock cfg { contract := C, locals := L } evm body
                (.ok { contract := C, locals := L1 } evm) ∧
              ∃ L', ExecBlock cfg { contract := C, locals := L1 } evm post
                (.ok { contract := C, locals := L' } evm) ∧ P v L') :
    ∀ v L, P v L → ∃ L',
      ExecForLoop cfg { contract := C, locals := L } evm condExpr post body
        (.ok { contract := C, locals := L' } evm) ∧ P 0 L' := by
  intro v
  induction v with
  | zero => intro L hP; exact ⟨L, ExecForLoop.falseDone (hfalse L hP), hP⟩
  | succ v ih =>
    intro L hP
    obtain ⟨L1, hbody, L2, hpost, hP1⟩ := hstep v L hP
    obtain ⟨L', hloop, hP'⟩ := ih L2 hP1
    exact ⟨L', ExecForLoop.iterate (htrue v L hP) hbody hpost hloop, hP'⟩

/-- **State-threading, continue-aware Hoare for-loop rule.**

This is the `execFor_var` variant needed by loops whose body may either fall through or execute
`continue`, and whose body/post can update the EVM state.  A body `continue` still runs `post`, as
Solidity `for` loops do. -/
theorem execFor_var_state_continue {cfg : Config} {C : ContractDecl}
    {condExpr : Expr} {post body : List Stmt} (P : ℕ → Solm.Store → EVM.State → Prop)
    (hfalse : ∀ L evm, P 0 L evm →
        evalExpr? cfg { contract := C, locals := L } evm condExpr = .ok (.bool false))
    (htrue : ∀ v L evm, P (v + 1) L evm →
        evalExpr? cfg { contract := C, locals := L } evm condExpr = .ok (.bool true))
    (hstep : ∀ v L evm, P (v + 1) L evm →
        ∃ L1 evm1,
          (ExecBlock cfg { contract := C, locals := L } evm body
              (.ok { contract := C, locals := L1 } evm1) ∨
            ExecBlock cfg { contract := C, locals := L } evm body
              (.continue { contract := C, locals := L1 } evm1)) ∧
          ∃ L2 evm2,
            ExecBlock cfg { contract := C, locals := L1 } evm1 post
              (.ok { contract := C, locals := L2 } evm2) ∧
            P v L2 evm2) :
    ∀ v L evm, P v L evm → ∃ L' evm',
      ExecForLoop cfg { contract := C, locals := L } evm condExpr post body
        (.ok { contract := C, locals := L' } evm') ∧ P 0 L' evm' := by
  intro v
  induction v with
  | zero =>
      intro L evm hP
      exact ⟨L, evm, ExecForLoop.falseDone (hfalse L evm hP), hP⟩
  | succ v ih =>
      intro L evm hP
      obtain ⟨L1, evm1, hbody, L2, evm2, hpost, hP1⟩ := hstep v L evm hP
      obtain ⟨L', evm', hloop, hP'⟩ := ih L2 evm2 hP1
      rcases hbody with hbody | hbody
      · exact ⟨L', evm', ExecForLoop.iterate (htrue v L evm hP) hbody hpost hloop, hP'⟩
      · exact ⟨L', evm', ExecForLoop.continueIter (htrue v L evm hP) hbody hpost hloop, hP'⟩

/-! ## Block sequencing -/

/-- Append helper: if `s1` falls through to `(f1, e1)`, running `s2` from there is running `s1 ++ s2`. -/
theorem execBlock_append {cfg : Config} {s2 : List Stmt} :
    ∀ {s1 : List Stmt} {f e f1 e1 r}, ExecBlock cfg f e s1 (.ok f1 e1) → ExecBlock cfg f1 e1 s2 r →
      ExecBlock cfg f e (s1 ++ s2) r := by
  intro s1
  induction s1 with
  | nil => intro f e f1 e1 r h1 h2; cases h1; exact h2
  | cons stmt rest ih =>
      intro f e f1 e1 r h1 h2
      cases h1 with
      | consNormal hstmt hrest => exact ExecBlock.consNormal hstmt (ih hrest h2)

/-- Append helper: if `s1` *terminates* (any non-`.ok` result), `s1 ++ s2` terminates the same way —
    `s2` never runs. -/
theorem execBlock_append_term {cfg : Config} {s2 : List Stmt} :
    ∀ {s1 : List Stmt} {f e r}, ExecBlock cfg f e s1 r → (∀ f' e', r ≠ .ok f' e') →
      ExecBlock cfg f e (s1 ++ s2) r := by
  intro s1
  induction s1 with
  | nil => intro f e r h1 hterm; cases h1; exact absurd rfl (hterm _ _)
  | cons stmt rest ih =>
      intro f e r h1 hterm
      cases h1 with
      | consNormal hstmt hrest => exact ExecBlock.consNormal hstmt (ih hrest hterm)
      | consReturn hstmt => exact ExecBlock.consReturn hstmt
      | consRevert hstmt => exact ExecBlock.consRevert hstmt
      | consBreak hstmt => exact ExecBlock.consBreak hstmt
      | consContinue hstmt => exact ExecBlock.consContinue hstmt
      | consStatic hstmt => exact ExecBlock.consStatic hstmt

/-- A one-statement block ends as its statement does. -/
theorem execBlock_singleton {cfg : Config} {solm : Frame} {evm : EVM.State} {stmt : Stmt}
    {r : ExecResult} (h : ExecStmt cfg solm evm stmt r) : ExecBlock cfg solm evm [stmt] r := by
  cases r with
  | ok => exact ExecBlock.consNormal h ExecBlock.nil
  | returned => exact ExecBlock.consReturn h
  | «break» => exact ExecBlock.consBreak h
  | «continue» => exact ExecBlock.consContinue h
  | reverted => exact ExecBlock.consRevert h
  | staticViolation => exact ExecBlock.consStatic h

/-! ## Forward block builder

`ExecBlock` is built tail-first (`consNormal` needs the rest), so a straight-line body reads
inside-out.  `ABlock` is the difference-list/CPS view that lets it read **left-to-right** like
`evm_run`: `ABlock cfg evm solm₀ stmts₀ solm stmts` transforms a continuation from the cursor
`(solm, stmts)` into the whole block from `(solm₀, stmts₀)`.  Chain with `start |>.requireStep …
|>.letStep … |>.whileStep …` and close with a terminal (`returns` / `requireRevert`); wrap the
result with `ExecFuncBody.execBlockRet` / `.execBlockRevert` to get an `ExecTransitionBody`. -/

/-- A straight-line `ExecBlock` builder, cursor `(solm, stmts)` over fixed entry `(solm₀, stmts₀)`.
    (A one-field structure so the combinators chain by dot-notation.) -/
structure ABlock (cfg : Config) (evm : EVM.State) (solm₀ : Frame) (stmts₀ : List Stmt)
    (solm : Frame) (stmts : List Stmt) : Prop where
  run : ∀ {result}, ExecBlock cfg solm evm stmts result → ExecBlock cfg solm₀ evm stmts₀ result

/-- Open a builder at the entry frame. -/
theorem ABlock.start {cfg evm solm stmts} : ABlock cfg evm solm stmts solm stmts := ⟨fun h => h⟩

/-- A passing `require` (frame unchanged). -/
theorem ABlock.requireStep {cfg evm solm₀ stmts₀ solm rest} {cond : Expr}
    (prev : ABlock cfg evm solm₀ stmts₀ solm (.require cond :: rest))
    (heval : evalExpr? cfg solm evm cond = .ok (.bool true)) :
    ABlock cfg evm solm₀ stmts₀ solm rest :=
  ⟨fun h => prev.run (ExecBlock.consNormal (ExecStmt.requireTrue heval) h)⟩

/-- A `let` binding (advances the cursor's locals). -/
theorem ABlock.letStep {cfg evm solm₀ stmts₀ solm rest} {name ty expr value}
    (prev : ABlock cfg evm solm₀ stmts₀ solm (.letDecl name ty expr :: rest))
    (heval : evalExpr? cfg solm evm expr = .ok value) :
    ABlock cfg evm solm₀ stmts₀ { solm with locals := solm.locals.insert name value } rest :=
  ⟨fun h => prev.run (ExecBlock.consNormal (ExecStmt.letDecl heval) h)⟩

/-- An `emit` (frame unchanged; the arguments evaluate). -/
theorem ABlock.emitStep {cfg evm solm₀ stmts₀ solm rest} {name : Ident} {args : List Expr}
    {vals : List Value}
    (prev : ABlock cfg evm solm₀ stmts₀ solm (.emit name args :: rest))
    (heval : evalExprs? cfg solm evm args = .ok vals) :
    ABlock cfg evm solm₀ stmts₀ solm rest :=
  ⟨fun h => prev.run (ExecBlock.consNormal (ExecStmt.emit heval) h)⟩

/-- A `while` loop that runs to `.ok` at frame `solm'` (supply the loop fact, e.g. `execWhile_var`). -/
theorem ABlock.whileStep {cfg evm solm₀ stmts₀ solm solm' rest} {cond body}
    (prev : ABlock cfg evm solm₀ stmts₀ solm (.while cond body :: rest))
    (hwhile : ExecStmt cfg solm evm (.while cond body) (.ok solm' evm)) :
    ABlock cfg evm solm₀ stmts₀ solm' rest :=
  ⟨fun h => prev.run (ExecBlock.consNormal hwhile h)⟩

/-- A `for` loop that runs to `.ok` at frame `solm'` (supply the loop fact, e.g. `ExecStmt.for`
    composing `init` with `execFor_var`).  The `for` analog of `ABlock.whileStep`. -/
theorem ABlock.forStep {cfg evm solm₀ stmts₀ solm solm' rest} {init cond post body}
    (prev : ABlock cfg evm solm₀ stmts₀ solm (.for init cond post body :: rest))
    (hfor : ExecStmt cfg solm evm (.for init cond post body) (.ok solm' evm)) :
    ABlock cfg evm solm₀ stmts₀ solm' rest :=
  ⟨fun h => prev.run (ExecBlock.consNormal hfor h)⟩

/-- Close with a `return` ⇒ the block returns `value`. -/
theorem ABlock.returns {cfg evm solm₀ stmts₀ solm rest} {expr value}
    (prev : ABlock cfg evm solm₀ stmts₀ solm (.return [expr] :: rest))
    (heval : evalExpr? cfg solm evm expr = .ok value) :
    ExecBlock cfg solm₀ evm stmts₀ (.returned solm evm (some [value])) :=
  prev.run (ExecBlock.consReturn (ExecStmt.return (evalExprs?_singleton heval)))

/-- Close with a failing `require` ⇒ the block reverts. -/
theorem ABlock.requireRevert {cfg evm solm₀ stmts₀ solm rest} {cond : Expr}
    (prev : ABlock cfg evm solm₀ stmts₀ solm (.require cond :: rest))
    (heval : evalExpr? cfg solm evm cond = .ok (.bool false)) :
    ExecBlock cfg solm₀ evm stmts₀ .reverted :=
  prev.run (ExecBlock.consRevert (ExecStmt.requireFalse heval))

/-! ## `Solm.Store` (locals) lookup -/

/-- Reading the key just inserted. -/
theorem store_get_self (L : Solm.Store) (k : Ident) (v : Value) :
    (L.insert k v).get? k = some v := by simp

/-- Reading a key untouched by an insert of a different key. -/
theorem store_get_ne (L : Solm.Store) {k a : Ident} (v : Value) (h : (k == a) = false) :
    (L.insert k v).get? a = L.get? a := by
  simp [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, h]

/-- Reading a key untouched by two different-key inserts. -/
theorem store_get_ne2 (L : Solm.Store) {k1 k2 a : Ident} (v1 v2 : Value)
    (h1 : (k1 == a) = false) (h2 : (k2 == a) = false) :
    ((L.insert k1 v1).insert k2 v2).get? a = L.get? a := by
  rw [store_get_ne (L.insert k1 v1) (k := k2) (a := a) v2 h2]
  exact store_get_ne L (k := k1) (a := a) v1 h1

/-- Reading a key untouched by three different-key inserts. -/
theorem store_get_ne3 (L : Solm.Store) {k1 k2 k3 a : Ident} (v1 v2 v3 : Value)
    (h1 : (k1 == a) = false) (h2 : (k2 == a) = false) (h3 : (k3 == a) = false) :
    (((L.insert k1 v1).insert k2 v2).insert k3 v3).get? a = L.get? a := by
  rw [store_get_ne ((L.insert k1 v1).insert k2 v2) (k := k3) (a := a) v3 h3]
  exact store_get_ne2 L v1 v2 h1 h2

/-- Reading a key untouched by four different-key inserts. -/
theorem store_get_ne4 (L : Solm.Store) {k1 k2 k3 k4 a : Ident} (v1 v2 v3 v4 : Value)
    (h1 : (k1 == a) = false) (h2 : (k2 == a) = false) (h3 : (k3 == a) = false)
    (h4 : (k4 == a) = false) :
    ((((L.insert k1 v1).insert k2 v2).insert k3 v3).insert k4 v4).get? a =
      L.get? a := by
  rw [store_get_ne (((L.insert k1 v1).insert k2 v2).insert k3 v3) (k := k4) (a := a)
    v4 h4]
  exact store_get_ne3 L v1 v2 v3 h1 h2 h3

/-- Reading a key untouched by five different-key inserts. -/
theorem store_get_ne5 (L : Solm.Store) {k1 k2 k3 k4 k5 a : Ident}
    (v1 v2 v3 v4 v5 : Value) (h1 : (k1 == a) = false) (h2 : (k2 == a) = false)
    (h3 : (k3 == a) = false) (h4 : (k4 == a) = false) (h5 : (k5 == a) = false) :
    (((((L.insert k1 v1).insert k2 v2).insert k3 v3).insert k4 v4).insert k5 v5).get? a =
      L.get? a := by
  rw [store_get_ne ((((L.insert k1 v1).insert k2 v2).insert k3 v3).insert k4 v4)
    (k := k5) (a := a) v5 h5]
  exact store_get_ne4 L v1 v2 v3 v4 h1 h2 h3 h4

/-! ## Storage-access collapse (post storage-pointer refactor)

After native storage pointers, `evalExpr? (.storage …)` and `assignStorageRef? .storage` route
through `resolveStorageRef?` (a `locals` pointer-check + `storageTypeAt?`) and then
`readStorage?`/`writeStorage?`.  For the common case — a base that is **not** a storage pointer and a
**scalar** (`.elem`) type — these collapse the new wrappers back to the plain
`storageLocLoad`/`storageLocStore`, so storage proofs are a single `rw` longer than before. -/

/-- `resolveStorageRef?` for a base that is not a local storage pointer: just `evalStorageRef`
    paired with the declared type from `storageTypeAt?`. -/
theorem resolveStorageRef?_ok {cfg : Config} {solm : Frame} {evm : EVM.State} {slot : StorageRef}
    {er : EvaledStorageRef} {ty : StorageType}
    (hbase : solm.locals.get? slot.base = none)
    (her : evalStorageRef cfg solm evm slot = .ok er)
    (hty : storageTypeAt? solm.contract.storage er = some ty) :
    resolveStorageRef? cfg solm evm slot = .ok (er, ty) := by
  unfold resolveStorageRef?
  simp only [hbase, her, hty, EvalResult.ofOption, bind, EvalResult.bind, pure]

/-- `readStorage?` at a scalar type is exactly the single-slot `storageLocLoad`. -/
theorem readStorage?_elem {cfg : Config} {evm : EVM.State} {er : EvaledStorageRef}
    {t : ABI.ElemType} {loc : StorageLoc} (hloc : cfg.storage.layout er = fun _ => some loc) :
    readStorage? cfg evm er (.elem t) = .ok (storageLocLoad evm loc) := by
  rw [readStorage?]
  simp only [hloc]

/-- A scalar storage read collapses to a single `storageLocLoad`. -/
theorem evalExpr_storage_scalar {cfg : Config} {solm : Frame} {evm : EVM.State} {slot : StorageRef}
    {er : EvaledStorageRef} {t : ABI.ElemType} {loc : StorageLoc}
    (hbase : solm.locals.get? slot.base = none)
    (her : evalStorageRef cfg solm evm slot = .ok er)
    (hty : storageTypeAt? solm.contract.storage er = some (.elem t))
    (hloc : cfg.storage.layout er = fun _ => some loc) :
    evalExpr? cfg solm evm (.storage slot) = .ok (storageLocLoad evm loc) := by
  rw [evalExpr?]
  simp only [resolveStorageRef?_ok hbase her hty, bind, EvalResult.bind,
    readStorage?_elem hloc]

/-- A scalar storage read with an already-normalized `storageLocLoad` value. -/
theorem evalExpr_storage_scalar_value {cfg : Config} {solm : Frame} {evm : EVM.State}
    {slot : StorageRef} {er : EvaledStorageRef} {t : ABI.ElemType} {loc : StorageLoc}
    {value : Value}
    (hbase : solm.locals.get? slot.base = none)
    (her : evalStorageRef cfg solm evm slot = .ok er)
    (hty : storageTypeAt? solm.contract.storage er = some (.elem t))
    (hloc : cfg.storage.layout er = fun _ => some loc)
    (hload : storageLocLoad evm loc = value) :
    evalExpr? cfg solm evm (.storage slot) = .ok value := by
  rw [evalExpr_storage_scalar hbase her hty hloc]
  exact congrArg EvalResult.ok hload

/-- A scalar storage write collapses to a single `storageLocStore`. -/
theorem assignStorageRef_storage_scalar_value {cfg : Config} {solm : Frame} {evm evm' : EVM.State}
    {slot : StorageRef} {er : EvaledStorageRef} {ty : StorageType} {loc : StorageLoc} {value : Value}
    (hbase : solm.locals.get? slot.base = none)
    (her : evalStorageRef cfg solm evm slot = .ok er)
    (hty : storageTypeAt? solm.contract.storage er = some ty)
    (hloc : cfg.storage.layout er = fun _ => some loc)
    (hscalar : match value with | .struct _ _ | .array _ | .bytes _ => False | _ => True)
    (hstore : storageLocStore evm loc value = some evm') :
    assignStorageRef? cfg solm evm .storage slot value = .ok (solm, evm') := by
  rw [assignStorageRef?]
  simp only [resolveStorageRef?_ok hbase her hty, bind, EvalResult.bind, EvalResult.ofOption,
    hloc, hstore, pure]
  cases value <;> simp at hscalar ⊢

/-- A scalar integer storage write collapses to a single `storageLocStore`. -/
theorem assignStorageRef_storage_scalar {cfg : Config} {solm : Frame} {evm evm' : EVM.State}
    {slot : StorageRef} {er : EvaledStorageRef} {ty : StorageType} {loc : StorageLoc} {n : Int}
    (hbase : solm.locals.get? slot.base = none)
    (her : evalStorageRef cfg solm evm slot = .ok er)
    (hty : storageTypeAt? solm.contract.storage er = some ty)
    (hloc : cfg.storage.layout er = fun _ => some loc)
    (hstore : storageLocStore evm loc (.int n) = some evm') :
    assignStorageRef? cfg solm evm .storage slot (.int n) = .ok (solm, evm') := by
  exact assignStorageRef_storage_scalar_value hbase her hty hloc (by trivial) hstore

theorem evalExpr_uint256_vars_positiveOr {cfg : Config} {caller : Frame} (evm : EVM.State)
    (var0 var1 : Ident) (word0 word1 : UInt256)
    (h0 : caller.locals.get? var0 = some (uint256Value word0))
    (h1 : caller.locals.get? var1 = some (uint256Value word1)) :
    evalExpr? cfg caller evm
      (.binary .or (.binary .gt (.var var0) (.intLit 0)) (.binary .gt (.var var1) (.intLit 0))) =
      .ok (.bool (decide (0 < word0.toNat ∨ 0 < word1.toNat))) := by
  simp only [evalExpr?, EvalResult.ofOption, h0, h1, EvalResult.bind, bind, pure]
  by_cases hp0 : 0 < word0.toNat <;> simp [evalBinaryOp?, hp0]

theorem evalExpr_uint256_inRange {cfg : Config} {caller : Frame} {evm : EVM.State}
    {e : Expr} {word : UInt256} (he : evalExpr? cfg caller evm e = .ok (uint256Value word)) :
    evalExpr? cfg caller evm (.inRange (.uint ⟨256, by decide⟩) e) = .ok (uint256Value word) := by
  simp only [evalExpr?, he, EvalResult.bind, bind, uint256Value]
  have hbound := word.val.isLt
  change word.toNat < 2 ^ 256 at hbound
  have hn : ¬ Int.ofNat word.toNat < 0 := by simp only [Int.ofNat_eq_natCast]; omega
  have hh : ¬ Int.ofNat word.toNat ≥ 2 ^ 256 := by simp only [Int.ofNat_eq_natCast]; omega
  simp only [hn, hh, decide_false, Bool.false_or, Bool.false_eq_true, if_false, pure]

theorem evalExpr_uint256_mul {cfg : Config} {caller : Frame} {evm : EVM.State}
    {lhs rhs : Expr} {a b : UInt256}
    (ha : evalExpr? cfg caller evm lhs = .ok (uint256Value a))
    (hb : evalExpr? cfg caller evm rhs = .ok (uint256Value b))
    (hfit : a.toNat * b.toNat < UInt256.size) :
    evalExpr? cfg caller evm (.inRange (.uint ⟨256, by decide⟩) (.binary .mul lhs rhs)) =
      .ok (uint256Value (UInt256.mul a b)) := by
  apply evalExpr_uint256_inRange
  simp only [evalExpr?, ha, hb, EvalResult.bind, bind, uint256Value, evalBinaryOp?]
  rw [u256_mul_toNat, Nat.mod_eq_of_lt hfit]
  simp only [Int.ofNat_eq_natCast, Nat.cast_mul]

theorem evalExpr_uint256_mul_overflow {cfg : Config} {caller : Frame} {evm : EVM.State}
    {lhs rhs : Expr} {a b : UInt256}
    (ha : evalExpr? cfg caller evm lhs = .ok (uint256Value a))
    (hb : evalExpr? cfg caller evm rhs = .ok (uint256Value b))
    (hover : UInt256.size ≤ a.toNat * b.toNat) :
    evalExpr? cfg caller evm (.inRange (.uint ⟨256, by
      decide⟩) (.binary .mul lhs rhs)) = .revert := by
  have hge : Int.ofNat (a.toNat * b.toNat) ≥ (2 : Int) ^ 256 := by
    rw [UInt256.size] at hover
    exact Int.ofNat_le.mpr hover
  simp only [evalExpr?, ha, hb, EvalResult.bind, bind, uint256Value, evalBinaryOp?]
  rw [if_pos]
  simp only [Bool.or_eq_true, decide_eq_true_eq]
  exact Or.inr (by simpa [Nat.cast_mul] using hge)

theorem evalExpr_uint256_sub {cfg : Config} {caller : Frame} {evm : EVM.State}
    {lhs rhs : Expr} {a b : UInt256}
    (ha : evalExpr? cfg caller evm lhs = .ok (uint256Value a))
    (hb : evalExpr? cfg caller evm rhs = .ok (uint256Value b))
    (hle : b.toNat ≤ a.toNat) :
    evalExpr? cfg caller evm (.inRange (.uint ⟨256, by decide⟩) (.binary .sub lhs rhs)) =
      .ok (uint256Value (UInt256.sub a b)) := by
  apply evalExpr_uint256_inRange
  simp only [evalExpr?, ha, hb, EvalResult.bind, bind, uint256Value, evalBinaryOp?]
  rw [usub_toNat hle]
  simp only [Int.ofNat_eq_natCast, Int.ofNat_sub hle]

theorem evalExpr_uint256_var_positive {cfg : Config} {frame : Frame} (evm : EVM.State)
    (name : Ident) (word : UInt256)
    (hget : frame.locals.get? name = some (.int (Int.ofNat word.toNat))) :
    evalExpr? cfg frame evm (.binary .gt (.var name) (.intLit 0)) =
      .ok (.bool (decide (0 < word.toNat))) := by
  simp only [evalExpr?, EvalResult.ofOption, hget, EvalResult.bind, bind, pure]
  simp [evalBinaryOp?]

theorem frame_eq_of_contract {caller : Frame} {decl : ContractDecl} (h : caller.contract = decl) :
    caller = { contract := decl, locals := caller.locals } := by
  cases caller
  dsimp only at h ⊢
  cases h
  rfl

theorem evalPackedArgs_cons {cfg : Config} {solm : Frame} {evm : EVM.State}
    {ty : ABIType} {e : Expr} {v : Value} {head tailBytes : List UInt8}
    {rest : List (ABIType × Expr)}
    (he : evalExpr? cfg solm evm e = .ok v)
    (henc : encodePackedValue? ty v = some head)
    (htail : evalPackedArgs? cfg solm evm rest = .ok tailBytes) :
    evalPackedArgs? cfg solm evm ((ty, e) :: rest) = .ok (head ++ tailBytes) := by
  rw [evalPackedArgs?]
  simp only [he, henc, htail, EvalResult.bind, EvalResult.ofOption, bind, pure]

theorem evalPackedArgs_single {cfg : Config} {solm : Frame} {evm : EVM.State}
    {ty : ABIType} {e : Expr} {v : Value} {head : List UInt8}
    (he : evalExpr? cfg solm evm e = .ok v)
    (henc : encodePackedValue? ty v = some head) :
    evalPackedArgs? cfg solm evm [(ty, e)] = .ok head := by
  simp [evalPackedArgs?, he, henc, EvalResult.bind, EvalResult.ofOption, bind, pure]

theorem execBlockAppendRevert {cfg : Config} {solm solm' : Frame} {evm evm' : EVM.State}
    {pref suff : List Stmt}
    (hp : ExecBlock cfg solm evm pref (.ok solm' evm'))
    (hs : ExecBlock cfg solm' evm' suff .reverted) :
    ExecBlock cfg solm evm (pref ++ suff) .reverted := by
  exact execBlock_append hp hs

theorem execBlockAppendOk {cfg : Config} {solm solm' : Frame} {evm evm' : EVM.State}
    {pref suff : List Stmt} {res : ExecResult}
    (hp : ExecBlock cfg solm evm pref (.ok solm' evm'))
    (hs : ExecBlock cfg solm' evm' suff res) :
    ExecBlock cfg solm evm (pref ++ suff) res := by
  exact execBlock_append hp hs

theorem execBlockAppendReverted {cfg : Config} {solm : Frame} {evm : EVM.State}
    {pref suff : List Stmt}
    (hp : ExecBlock cfg solm evm pref .reverted) :
    ExecBlock cfg solm evm (pref ++ suff) .reverted := by
  exact execBlock_append_term hp (by intro _ _ h; cases h)

theorem execBlock_append_ok {cfg : Config} {solm evm solm' evm' result}
    {xs ys : List Stmt}
    (hxs : ExecBlock cfg solm evm xs (.ok solm' evm'))
    (hys : ExecBlock cfg solm' evm' ys result) :
    ExecBlock cfg solm evm (xs ++ ys) result := by
  exact execBlock_append hxs hys

theorem sliceBytes_nat {out : ByteArray} {start finish : Nat}
    (hs : start ≤ finish) (he : finish ≤ out.size) :
    sliceBytes? out (Int.ofNat start) (Int.ofNat finish) =
      .ok (.bytes (out.extract start finish)) := by
  simp [sliceBytes?, Int.ofNat_eq_natCast, Nat.not_lt.mpr hs, Nat.not_lt.mpr he]

theorem naturalAddSource {cfg frame evm lhs rhs} {a b : Nat}
    (ha : evalExpr? cfg frame evm lhs = .ok (.int (Int.ofNat a)))
    (hb : evalExpr? cfg frame evm rhs = .ok (.int (Int.ofNat b))) :
    evalExpr? cfg frame evm (.binary .add lhs rhs) = .ok (.int (Int.ofNat (a + b))) := by
  simp only [evalExpr?, ha, hb, bind, EvalResult.bind, evalBinaryOp?]
  rfl

theorem naturalLeSource {cfg frame evm lhs rhs} {a b : Nat}
    (ha : evalExpr? cfg frame evm lhs = .ok (.int (Int.ofNat a)))
    (hb : evalExpr? cfg frame evm rhs = .ok (.int (Int.ofNat b))) :
    evalExpr? cfg frame evm (.binary .le lhs rhs) = .ok (.bool (decide (a ≤ b))) := by
  simp only [evalExpr?, ha, hb, bind, EvalResult.bind, evalBinaryOp?, Int.ofNat_eq_natCast,
    Nat.cast_le]

theorem naturalGeSource {cfg frame evm lhs rhs} {a b : Nat}
    (ha : evalExpr? cfg frame evm lhs = .ok (.int (Int.ofNat a)))
    (hb : evalExpr? cfg frame evm rhs = .ok (.int (Int.ofNat b))) :
    evalExpr? cfg frame evm (.binary .ge lhs rhs) = .ok (.bool (decide (b ≤ a))) := by
  simp only [evalExpr?, ha, hb, bind, EvalResult.bind, evalBinaryOp?, Int.ofNat_eq_natCast,
    Nat.cast_le]

theorem localNatSource {cfg : Config} {contract : ContractDecl} {evm : EVM.State}
    {locals : Store} {name : Ident} {n : Nat}
    (hn : locals.get? name = some (.int (Int.ofNat n))) :
    evalExpr? cfg { contract := contract, locals := locals } evm (.var name) =
      .ok (.int (Int.ofNat n)) := by
  simp only [evalExpr?, hn, EvalResult.ofOption]

theorem uint256RangeSourceOk {cfg solm evm expr} {n : Nat}
    (he : evalExpr? cfg solm evm expr = .ok (.int (Int.ofNat n)))
    (hn : n < UInt256.size) :
    evalExpr? cfg solm evm (.inRange (.uint ⟨256, by decide⟩) expr) =
      .ok (.int (Int.ofNat n)) := by
  have hi0 : ¬ Int.ofNat n < 0 := by simp only [Int.ofNat_eq_natCast]; omega
  have hi : ¬ Int.ofNat n ≥ 2 ^ 256 := by
    change n < 2 ^ 256 at hn
    simp only [Int.ofNat_eq_natCast]
    omega
  simp only [evalExpr?, he, bind, EvalResult.bind, hi0, hi, decide_false, Bool.or_self,
    Bool.false_eq_true, if_false, pure]

theorem uint256RangeSourceOverflow {cfg solm evm expr} {n : Nat}
    (he : evalExpr? cfg solm evm expr = .ok (.int (Int.ofNat n)))
    (hn : UInt256.size ≤ n) :
    evalExpr? cfg solm evm (.inRange (.uint ⟨256, by decide⟩) expr) = .revert := by
  have hi : Int.ofNat n ≥ 2 ^ 256 := by
    change 2 ^ 256 ≤ n at hn
    simp only [Int.ofNat_eq_natCast]
    omega
  simp only [evalExpr?, he, bind, EvalResult.bind, hi, decide_true, Bool.or_true, if_true]

theorem checkedAddSourceOk {cfg solm evm lhs rhs a b}
    (ha : evalExpr? cfg solm evm lhs = .ok (.int (Int.ofNat (UInt256.toNat a))))
    (hb : evalExpr? cfg solm evm rhs = .ok (.int (Int.ofNat (UInt256.toNat b))))
    (hno : a.toNat + b.toNat < UInt256.size) :
    evalExpr? cfg solm evm (.inRange (.uint ⟨256, by decide⟩) (.binary .add lhs rhs)) =
      .ok (.int (Int.ofNat (a + b).toNat)) := by
  have hw : (a + b).toNat = a.toNat + b.toNat := addWord_toNat a b hno
  rw [hw]
  apply uint256RangeSourceOk ?_ hno
  simp only [evalExpr?, ha, hb, bind, EvalResult.bind, evalBinaryOp?]
  rfl

theorem checkedAddSourceOverflow {cfg solm evm lhs rhs a b}
    (ha : evalExpr? cfg solm evm lhs = .ok (.int (Int.ofNat (UInt256.toNat a))))
    (hb : evalExpr? cfg solm evm rhs = .ok (.int (Int.ofNat (UInt256.toNat b))))
    (hover : UInt256.size ≤ a.toNat + b.toNat) :
    evalExpr? cfg solm evm (.inRange (.uint ⟨256, by decide⟩) (.binary .add lhs rhs)) =
      .revert := by
  apply uint256RangeSourceOverflow ?_ hover
  simp only [evalExpr?, ha, hb, bind, EvalResult.bind, evalBinaryOp?]
  rfl

theorem checkedMulSourceOk {cfg solm evm lhs rhs a b}
    (ha : evalExpr? cfg solm evm lhs = .ok (.int (Int.ofNat (UInt256.toNat a))))
    (hb : evalExpr? cfg solm evm rhs = .ok (.int (Int.ofNat (UInt256.toNat b))))
    (hno : a.toNat * b.toNat < UInt256.size) :
    evalExpr? cfg solm evm (.inRange (.uint ⟨256, by decide⟩) (.binary .mul lhs rhs)) =
      .ok (.int (Int.ofNat (UInt256.mul a b).toNat)) := by
  rw [u256_mul_toNat, Nat.mod_eq_of_lt hno]
  apply uint256RangeSourceOk ?_ hno
  simp only [evalExpr?, ha, hb, bind, EvalResult.bind, evalBinaryOp?]
  rfl

theorem checkedMulSourceOverflow {cfg solm evm lhs rhs a b}
    (ha : evalExpr? cfg solm evm lhs = .ok (.int (Int.ofNat (UInt256.toNat a))))
    (hb : evalExpr? cfg solm evm rhs = .ok (.int (Int.ofNat (UInt256.toNat b))))
    (hover : UInt256.size ≤ a.toNat * b.toNat) :
    evalExpr? cfg solm evm (.inRange (.uint ⟨256, by decide⟩) (.binary .mul lhs rhs)) =
      .revert := by
  apply uint256RangeSourceOverflow ?_ hover
  simp only [evalExpr?, ha, hb, bind, EvalResult.bind, evalBinaryOp?]
  rfl

theorem divSourceOk {cfg solm evm lhs rhs a b}
    (ha : evalExpr? cfg solm evm lhs = .ok (.int (Int.ofNat (UInt256.toNat a))))
    (hb : evalExpr? cfg solm evm rhs = .ok (.int (Int.ofNat (UInt256.toNat b))))
    (hn : b ≠ ⟨0⟩) :
    evalExpr? cfg solm evm (.binary .div lhs rhs) =
      .ok (.int (Int.ofNat (UInt256.div a b).toNat)) := by
  have hz : (b.toNat : Int) ≠ 0 := by
    intro he
    exact hn (uint256_toNat_eq_zero (by omega))
  simp only [evalExpr?, ha, hb, bind, EvalResult.bind, evalBinaryOp?,
    udiv_toNat, Int.ofNat_eq_natCast, hz, if_false, Int.natCast_ediv]

theorem subSourceOk {cfg solm evm lhs rhs a b}
    (ha : evalExpr? cfg solm evm lhs = .ok (.int (Int.ofNat (UInt256.toNat a))))
    (hb : evalExpr? cfg solm evm rhs = .ok (.int (Int.ofNat (UInt256.toNat b))))
    (hn : b.toNat ≤ a.toNat) :
    evalExpr? cfg solm evm (.binary .sub lhs rhs) =
      .ok (.int (Int.ofNat (UInt256.sub a b).toNat)) := by
  simp only [evalExpr?, ha, hb, bind, EvalResult.bind, evalBinaryOp?,
    usub_toNat hn, Int.ofNat_eq_natCast, Int.natCast_sub hn]

theorem execFor_var_state {cfg : Config} {C : ContractDecl}
    {condExpr : Expr} {post body : List Stmt}
    (P : ℕ → Solm.Store → EVM.State → Prop)
    (hfalse : ∀ L evm, P 0 L evm →
        evalExpr? cfg { contract := C, locals := L } evm condExpr = .ok (.bool false))
    (htrue : ∀ v L evm, P (v + 1) L evm →
        evalExpr? cfg { contract := C, locals := L } evm condExpr = .ok (.bool true))
    (hstep : ∀ v L evm, P (v + 1) L evm →
        ∃ L1 evm1, ExecBlock cfg { contract := C, locals := L } evm body
              (.ok { contract := C, locals := L1 } evm1) ∧
            ∃ L2 evm2, ExecBlock cfg { contract := C, locals := L1 } evm1 post
              (.ok { contract := C, locals := L2 } evm2) ∧ P v L2 evm2) :
    ∀ v L evm, P v L evm → ∃ L' evm',
      ExecForLoop cfg { contract := C, locals := L } evm condExpr post body
        (.ok { contract := C, locals := L' } evm') ∧ P 0 L' evm' := by
  exact Reasoning.Theory.execFor_var_state_continue P hfalse htrue
    (fun v L evm hP => by
      obtain ⟨L1, evm1, hbody, L2, evm2, hpost, hP1⟩ := hstep v L evm hP
      exact ⟨L1, evm1, Or.inl hbody, L2, evm2, hpost, hP1⟩)

/-- An address value as an `Expr` literal. -/
def addressLiteral (a : EVM.Address) : Expr :=
  .cast (.intLit (Int.ofNat a.toNat)) (.elem .address)

theorem evalAddressLiteral (cfg : Config) (frame : Frame) (evm : EVM.State) (a : AccountAddress) :
    evalExpr? cfg frame evm (addressLiteral a) = .ok (.address a) := by
  simp only [addressLiteral, evalExpr?, EvalResult.bind, bind, pure, castValue?]
  erw [if_neg]
  · simp [EvalResult.ofOption, AccountAddress.ofNat]
  · exact not_lt.mpr (Int.natCast_nonneg (↑a : Nat))

theorem execBlock_reverted_append {cfg : Config} {s2 : List Stmt} :
    ∀ {f e s1}, ExecBlock cfg f e s1 .reverted →
      ExecBlock cfg f e (s1 ++ s2) .reverted := by
  intro f e s1
  induction s1 generalizing f e with
  | nil =>
      intro h
      cases h
  | cons stmt rest ih =>
      intro h
      cases h with
      | consNormal hstmt htail =>
          exact ExecBlock.consNormal hstmt (ih htail)
      | consRevert hstmt =>
          exact ExecBlock.consRevert hstmt

end Reasoning.Theory

/-! ## Elementary expression and local-store facts -/

namespace Reasoning.Theory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 2000000

theorem evalBinaryOpGtInt (x y : Int) :
    evalBinaryOp? .gt (.int x) (.int y) = .ok (.bool (x > y)) := by
  rfl

theorem evalBinaryOpNeAddress (a b : AccountAddress) :
    evalBinaryOp? .ne (.address a) (.address b) =
      .ok (.bool (!(Value.address a == Value.address b))) := by
  rfl

theorem evalExpr_binary_nonshort {cfg solm evm op lhs rhs}
    (hand : op ≠ BinaryOp.and) (hor : op ≠ BinaryOp.or) :
    evalExpr? cfg solm evm (.binary op lhs rhs) =
      (do
        let lhsValue <- evalExpr? cfg solm evm lhs
        let rhsValue <- evalExpr? cfg solm evm rhs
        evalBinaryOp? op lhsValue rhsValue) := by
  cases op <;> simp [evalExpr?] at hand hor ⊢

theorem evalBinaryOp_lt_int_ok (x y : Int) :
    evalBinaryOp? .lt (.int x) (.int y) = .ok (.bool (x < y)) := by
  rfl

theorem evalBinaryOp_add_int_ok (x y : Int) :
    evalBinaryOp? .add (.int x) (.int y) = .ok (.int (x + y)) := by
  rfl

theorem getElem?_insert_ne (locals : Store) {k a : Ident} (value : Value)
    (h : (k == a) = false) :
    (locals.insert k value)[a]? = locals[a]? := by
  simp [Std.HashMap.getElem?_insert, h]

theorem getElem?_insert_self (locals : Store) (k : Ident) (value : Value) :
    (locals.insert k value)[k]? = some value := by
  simp

theorem normalizeRawBoolWord_false_of_u256 {word : Nat}
    (hword : (UInt256.ofNat word).toNat = word) (hzero : UInt256.ofNat word = ⟨0⟩) :
    normalizeRawBoolWord? (rawBoolWordValue word) = .ok (.bool false) := by
  have hword0 : word = 0 := by
    have h := congrArg UInt256.toNat hzero
    simpa [hword] using h
  subst word
  rfl

theorem normalizeRawBoolWord_true_of_u256 {word : Nat}
    (hword : (UInt256.ofNat word).toNat = word) (hone : UInt256.ofNat word = ⟨1⟩) :
    normalizeRawBoolWord? (rawBoolWordValue word) = .ok (.bool true) := by
  have hword1 : word = 1 := by
    have h := congrArg UInt256.toNat hone
    simpa [hword] using h
  subst word
  rfl

theorem normalizeRawBoolWord_revert_of_u256 {word : Nat}
    (hword : (UInt256.ofNat word).toNat = word)
    (hzero : UInt256.ofNat word ≠ ⟨0⟩) (hone : UInt256.ofNat word ≠ ⟨1⟩) :
    normalizeRawBoolWord? (rawBoolWordValue word) = .revert := by
  have hword0 : word ≠ 0 := by
    intro h0
    apply hzero
    subst word
    rfl
  have hword1 : word ≠ 1 := by
    intro h1
    apply hone
    subst word
    rfl
  simp [normalizeRawBoolWord?, rawBoolWordValue, hword0, hword1]

theorem evalBinaryOp_eq_int_ok (x y : Int) :
    evalBinaryOp? .eq (.int x) (.int y) =
      .ok (.bool (Value.int x == Value.int y)) := by
  rfl

theorem store_get_empty (k : Ident) : (∅ : Solm.Store).get? k = none := by simp

theorem wordToElem_bool_scalar (word : UInt256) :
    match wordToElem .bool word with
    | .struct _ _ => False
    | .array _ => False
    | .bytes _ => False
    | _ => True := by
  change
    match
        (if (word.val == 0) = true then
          Value.bool false
        else
          Value.bool true) with
    | .struct _ _ => False
    | .array _ => False
    | .bytes _ => False
    | _ => True
  by_cases h : (word.val == 0) = true <;> simp [h]

theorem evalBinaryOp_ne_int_ok (x y : Int) :
    evalBinaryOp? .ne (.int x) (.int y) =
      .ok (.bool (!(Value.int x == Value.int y))) := by
  rfl

theorem valueInt_beq_false_of_ne {x y : Int} (h : x ≠ y) :
    (Value.int x == Value.int y) = false := by
  rw [beq_eq_false_iff_ne]
  intro hv
  cases hv
  exact h rfl

theorem assignStorageRef_storage_bool_word {cfg : Config} {solm : Frame}
    {evm evm' : EVM.State} {slot : StorageRef} {er : EvaledStorageRef}
    {ty : StorageType} {loc : StorageLoc} {word : UInt256}
    (hbase : solm.locals.get? slot.base = none)
    (her : evalStorageRef cfg solm evm slot = .ok er)
    (hty : storageTypeAt? solm.contract.storage er = some ty)
    (hloc : cfg.storage.layout er = fun _ => some loc)
    (hstore : storageLocStore evm loc (wordToElem .bool word) = some evm') :
    assignStorageRef? cfg solm evm .storage slot (wordToElem .bool word) =
      .ok (solm, evm') := by
  exact assignStorageRef_storage_scalar_value hbase her hty hloc
    (wordToElem_bool_scalar word) hstore

end Reasoning.Theory
