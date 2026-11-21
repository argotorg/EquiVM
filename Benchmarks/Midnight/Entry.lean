import Benchmarks.Midnight.Common

/-! Shared source entry guards and their signed EVM size tests. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

abbrev calldataLimit : Nat := 2^255 + 4

-- LIBRARY CANDIDATE: the ADD(-4) form of solc's signed static-head size check.
theorem entrySizeCheck_ok {size bytes : Nat}
    (hlen : 4 + bytes ≤ size) (hhi : size < 2^255 + 4)
    (hsize : size < UInt256.size) :
    UInt256.slt (UInt256.lnot ⟨3⟩ + UInt256.ofNat size) (UInt256.ofNat bytes) = ⟨0⟩ := by
  rw [lnot3_add_returnSize (by omega) hsize]
  exact slt_ofNat_lit_zero (by omega) (by omega) (by omega)

-- LIBRARY CANDIDATE: upper failure branch of the ADD(-4) static-head check.
theorem entrySizeCheck_huge {size bytes : Nat}
    (hhi : 2^255 + 4 ≤ size) (hsize : size < UInt256.size) (hbytes : bytes < 2^255) :
    UInt256.slt (UInt256.lnot ⟨3⟩ + UInt256.ofNat size) (UInt256.ofNat bytes) = ⟨1⟩ := by
  rw [lnot3_add_returnSize (by omega) hsize]
  exact slt_lit_one_high hbytes (by rw [ulit_toNat' _ (by omega)]; omega)

-- LIBRARY CANDIDATE: lower failure branch of the ADD(-4) static-head check.
theorem entrySizeCheck_short {size bytes : Nat}
    (h4 : 4 ≤ size) (hlen : size < 4 + bytes)
    (hbytes : bytes < 2^255) (hsize : size < UInt256.size) :
    UInt256.slt (UInt256.lnot ⟨3⟩ + UInt256.ofNat size) (UInt256.ofNat bytes) = ⟨1⟩ := by
  rw [lnot3_add_returnSize h4 hsize]
  exact slt_ofNat_lit_one_low hbytes (by omega)

-- LIBRARY CANDIDATE: evaluating the length guard of a bytes-valued local.
theorem evalBytesLengthLt {cfg : Config} {frame : Frame} {evm : EVM.State}
    {name : Ident} {bytes : ByteArray} (bound : Nat)
    (hget : frame.locals.get? name = some (.bytes bytes)) :
    evalExpr? cfg frame evm
      (.binary .lt (.arrayLength .localVar { base := name }) (.intLit (Int.ofNat bound))) =
      .ok (.bool (decide (bytes.size < bound))) := by
  simp only [evalExpr?, hget, readLocalPath?, bind, EvalResult.bind, pure, evalBinaryOp?]
  simp only [Int.ofNat_eq_natCast, Nat.cast_lt]

def calldataFrame (C : ContractDecl) (locals imms : Store) (evm : EVM.State) : Frame :=
  { contract := C, locals := locals.insert "__calldata" (.bytes evm.executionEnv.calldata),
    immutables := imms }

def calldataSizeGuard : Expr :=
  .binary .lt (.arrayLength .localVar { base := "__calldata" }) (.intLit calldataLimit)

def entryPrefix : List Stmt :=
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
    ExecTransitionBody cfg C evm locals (entryPrefix ++ [.return [expr]])
      (.returned (calldataFrame C locals imms evm) evm (some [value])) imms := by
  apply ExecFuncBody.execBlockRet
  refine (ABlock.start.requireStep (evalCallvalueEq_true hwv)
    |>.letStep (by simp only [evalExpr?, envValue, pure])
    |>.requireStep ?_).returns heval
  exact (calldataSizeGuard_eval cfg C locals imms evm).trans
    (congrArg (fun b ↦ EvalResult.ok (Value.bool b)) (decide_eq_true hhi))

theorem guardedReturnReverts {cfg : Config} {C : ContractDecl} {locals imms : Store}
    {evm : EVM.State} {expr : Expr}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < calldataLimit)
    (heval : evalExpr? cfg (calldataFrame C locals imms evm) evm expr = .revert) :
    ExecTransitionBody cfg C evm locals (entryPrefix ++ [.return [expr]]) .reverted imms := by
  apply ExecFuncBody.execBlockRevert
  refine (ABlock.start.requireStep (evalCallvalueEq_true hwv)
    |>.letStep (value := .bytes evm.executionEnv.calldata)
      (by simp only [evalExpr?, envValue, pure])
    |>.requireStep ?_).run (ExecBlock.consRevert (ExecStmt.returnRevert ?_))
  · exact (calldataSizeGuard_eval cfg C locals imms evm).trans
      (congrArg (fun b ↦ EvalResult.ok (Value.bool b)) (decide_eq_true hhi))
  · change evalExprs? cfg (calldataFrame C locals imms evm) evm [expr] = .revert
    simp only [evalExprs?, heval, bind, EvalResult.bind]

theorem guardedReturnsBody {cfg : Config} {C : ContractDecl} {locals imms : Store}
    {evm : EVM.State} {exprs : List Expr} {values : List Value}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < calldataLimit)
    (heval : evalExprs? cfg (calldataFrame C locals imms evm) evm exprs = .ok values) :
    ExecTransitionBody cfg C evm locals (entryPrefix ++ [.return exprs])
      (.returned (calldataFrame C locals imms evm) evm (some values)) imms := by
  apply ExecFuncBody.execBlockRet
  refine (ABlock.start.requireStep (evalCallvalueEq_true hwv)
    |>.letStep (value := .bytes evm.executionEnv.calldata)
      (by simp only [evalExpr?, envValue, pure])
    |>.requireStep ?_).run (ExecBlock.consReturn (ExecStmt.return heval))
  exact (calldataSizeGuard_eval cfg C locals imms evm).trans
    (congrArg (fun b ↦ EvalResult.ok (Value.bool b)) (decide_eq_true hhi))

theorem calldataSizeBodyReverts {cfg : Config} {C : ContractDecl} {locals imms : Store}
    {evm : EVM.State} {rest : List Stmt}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : ¬ evm.executionEnv.calldata.size < calldataLimit) :
    ExecTransitionBody cfg C evm locals (entryPrefix ++ rest) .reverted imms := by
  apply ExecFuncBody.execBlockRevert
  refine (ABlock.start.requireStep (evalCallvalueEq_true hwv)
    |>.letStep (value := .bytes evm.executionEnv.calldata)
      (by simp only [evalExpr?, envValue, pure])).requireRevert ?_
  exact (calldataSizeGuard_eval cfg C locals imms evm).trans
    (congrArg (fun b ↦ EvalResult.ok (Value.bool b)) (decide_eq_false hhi))

theorem midnightDecodeEmpty {cd : ByteArray} (hsz : 4 ≤ cd.size) :
    config.externalABI.decodeCalldata? [] [] cd = some ∅ := by
  change Model.decodeCalldata [] [] cd = some ∅
  unfold Model.decodeCalldata
  rw [decodeCalldataWithMode_empty_ok hsz]
  simp [Model.inputSizesFit]

-- LIBRARY CANDIDATE: distinct selectors cannot match the same calldata prefix.
theorem selectorNe_of_selIs {I : ExecutionEnv} {selector other : ByteArray}
    (hsel : selIs I selector) (hne : other ≠ selector) : ¬ selIs I other := by
  intro h
  exact hne ((byteArray_eq_of_beq h).trans (byteArray_eq_of_beq hsel).symm)

def midnightEntryMemory : ByteArray := writeWord (writeWord .empty 64 ⟨832⟩) 800 ⟨0⟩

theorem midnightEntryMemory_freePtr : memLoad ⟨64⟩ midnightEntryMemory = ⟨832⟩ := by
  decide +kernel

theorem midnightEntryMemory_size : midnightEntryMemory.size = 832 := by decide +kernel

theorem midnightReturnWord (word : UInt256) :
    (writeWord midnightEntryMemory 832 word).readWithPadding 832 32 = word.toByteArray := by
  apply writeWord_read_back
  rw [midnightEntryMemory_size]
  exact USize.size_pos

end Benchmarks.Midnight
