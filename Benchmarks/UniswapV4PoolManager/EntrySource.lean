import Benchmarks.UniswapV4PoolManager.Common

/-! Shared calldata guards for the PoolManager entry points. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.UniswapV4PoolManager

-- LIBRARY CANDIDATE: compiler signed length check with ADD(-4) instead of SUB(4).
theorem viaIRStaticLenCheckOk {size words : Nat}
    (hlen : 4 + 32 * words ≤ size) (hhi : size < 2^255 + 4)
    (hsize : size < UInt256.size) :
    UInt256.slt (UInt256.ofNat size + UInt256.ofNat (UInt256.size - 4))
      (UInt256.ofNat (32 * words)) = ⟨0⟩ := by
  change UInt256.slt (UInt256.ofNat size + UInt256.lnot ⟨3⟩) _ = _
  rw [u256_add_comm, lnot3_add_returnSize (by omega) hsize]
  exact slt_ofNat_lit_zero (by omega) (by omega) (by omega)

-- LIBRARY CANDIDATE: compiler signed length check with ADD(-4) instead of SUB(4).
theorem viaIRStaticLenCheckHuge {size words : Nat}
    (hhi : 2^255 + 4 ≤ size) (hsize : size < UInt256.size)
    (hwords : 32 * words < 2^255) :
    UInt256.slt (UInt256.ofNat size + UInt256.ofNat (UInt256.size - 4))
      (UInt256.ofNat (32 * words)) = ⟨1⟩ := by
  change UInt256.slt (UInt256.ofNat size + UInt256.lnot ⟨3⟩) _ = _
  rw [u256_add_comm, lnot3_add_returnSize (by omega) hsize]
  exact slt_lit_one_high hwords (by rw [ulit_toNat' _ (by omega)]; omega)

-- LIBRARY CANDIDATE: length guard for a bytes value held in a local variable.
theorem evalBytesLengthLt {cfg : Config} {frame : Frame} {evm : EVM.State}
    {name : Ident} {bytes : ByteArray} (bound : Nat)
    (hget : frame.locals.get? name = some (.bytes bytes)) :
    evalExpr? cfg frame evm
      (.binary .lt (.arrayLength .localVar { base := name }) (.intLit (Int.ofNat bound))) =
      .ok (.bool (decide (bytes.size < bound))) := by
  simp only [evalExpr?, hget, readLocalPath?, bind, EvalResult.bind, pure,
    evalBinaryOp?]
  simp only [Int.ofNat_eq_natCast, Nat.cast_lt]

/-- The source frame after binding `msg.data` at an ABI entry. -/
def calldataFrame (C : ContractDecl) (locals imms : Store) (evm : EVM.State) : Frame :=
  { contract := C, locals := locals.insert "__calldata" (.bytes evm.executionEnv.calldata),
    immutables := imms }

/-- The compiled signed size test's upper limit, also present in each source body. -/
abbrev calldataLimit : Nat := 2^255 + 4

def calldataSizeGuard : Expr :=
  .binary .lt (.arrayLength .localVar { base := "__calldata" })
    (.intLit (Int.ofNat calldataLimit))

def nonpayableCalldataPrefix : List Stmt :=
  [.require (.binary .eq (.env .callvalue) (.intLit 0)),
   .letDecl "__calldata" (some .bytes) (.env .msgData),
   .require calldataSizeGuard]

theorem calldataSizeGuard_eval (cfg : Config) (C : ContractDecl) (locals imms : Store)
    (evm : EVM.State) :
    evalExpr? cfg (calldataFrame C locals imms evm) evm calldataSizeGuard =
      .ok (.bool (decide (evm.executionEnv.calldata.size < calldataLimit))) :=
  evalBytesLengthLt calldataLimit (store_get_self _ _ _)

theorem guardedReturnBody {cfg : Config} {C : ContractDecl} {locals imms : Store}
    {evm : EVM.State} {expr : Expr} {value : Value}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < calldataLimit)
    (heval : evalExpr? cfg (calldataFrame C locals imms evm) evm expr = .ok value) :
    ExecTransitionBody cfg C evm locals (nonpayableCalldataPrefix ++ [.return [expr]])
      (.returned (calldataFrame C locals imms evm) evm (some [value])) imms := by
  apply ExecFuncBody.execBlockRet
  refine (ABlock.start.requireStep (evalCallvalueEq_true hwv)
    |>.letStep (by simp only [evalExpr?, envValue, pure])
    |>.requireStep ?_).returns heval
  exact (calldataSizeGuard_eval cfg C locals imms evm).trans
    (congrArg (fun b => EvalResult.ok (Value.bool b)) (decide_eq_true hhi))

theorem calldataSizeBodyReverts {cfg : Config} {C : ContractDecl} {locals imms : Store}
    {evm : EVM.State} {rest : List Stmt}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : ¬ evm.executionEnv.calldata.size < calldataLimit) :
    ExecTransitionBody cfg C evm locals (nonpayableCalldataPrefix ++ rest) .reverted imms := by
  apply ExecFuncBody.execBlockRevert
  refine (ABlock.start.requireStep (evalCallvalueEq_true hwv)
    |>.letStep (value := .bytes evm.executionEnv.calldata)
      (by simp only [evalExpr?, envValue, pure])).requireRevert ?_
  exact (calldataSizeGuard_eval cfg C locals imms evm).trans
    (congrArg (fun b => EvalResult.ok (Value.bool b)) (decide_eq_false hhi))

-- LIBRARY CANDIDATE: distinct selector bytes cannot both match one calldata prefix.
theorem selectorNe_of_selIs {I : ExecutionEnv} {selector other : ByteArray}
    (hsel : (selector == I.calldata.extract 0 4) = true) (hne : other ≠ selector) :
    ¬ (other == I.calldata.extract 0 4) = true := by
  intro h
  exact hne ((byteArray_eq_of_beq h).trans (byteArray_eq_of_beq hsel).symm)

-- LIBRARY CANDIDATE: lower failure branch of the signed ADD(-4) ABI size guard.
theorem viaIRStaticLenCheckShort {size words : Nat}
    (h4 : 4 ≤ size) (hlen : size < 4 + 32 * words)
    (hwords : 32 * words < 2^255) (hsize : size < UInt256.size) :
    UInt256.slt (UInt256.ofNat size + UInt256.ofNat (UInt256.size - 4))
      (UInt256.ofNat (32 * words)) = ⟨1⟩ := by
  change UInt256.slt (UInt256.ofNat size + UInt256.lnot ⟨3⟩) _ = _
  rw [u256_add_comm, lnot3_add_returnSize h4 hsize]
  exact slt_ofNat_lit_one_low hwords (by omega)

theorem nonpayableCalldataBlock {cfg : Config} {C : ContractDecl} {locals imms : Store}
    {evm : EVM.State} {rest : List Stmt} {result : ExecResult}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < calldataLimit)
    (hrest : ExecBlock cfg (calldataFrame C locals imms evm) evm rest result) :
    ExecBlock cfg {contract := C, locals := locals, immutables := imms} evm
      (nonpayableCalldataPrefix ++ rest) result := by
  apply (ABlock.start.requireStep (evalCallvalueEq_true hwv)
    |>.letStep (value := .bytes evm.executionEnv.calldata)
      (by simp only [evalExpr?, envValue, pure])
    |>.requireStep ?_).run hrest
  exact (calldataSizeGuard_eval cfg C locals imms evm).trans
    (congrArg (fun b => EvalResult.ok (Value.bool b)) (decide_eq_true hhi))

end Benchmarks.UniswapV4PoolManager
