import Benchmarks.Safe.RawStorage
import Benchmarks.Safe.LocalArrays
import Benchmarks.Safe.WordArrayMemory
import Reasoning.ABIViews

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe

def storageAtArgs (offset len : UInt256) : Store :=
  ((∅ : Store).insert "offset" (.int (Int.ofNat offset.toNat))).insert
    "length" (.int (Int.ofNat len.toNat))

def storageAtLoopBody : List Stmt :=
  [ .assign .localVar (varRef "result")
      (.abiEncodePacked [(bytesTy, .var "result"), (uint256, .storage
        (rawStorageRef (.cast (addE (.var "offset") (.var "index")) uint256St)))]),
    .assign .localVar (varRef "index") (inc256 (.var "index")) ]

def storageAtLoop : Stmt := .while (ltE (.var "index") (.var "length")) storageAtLoopBody

structure StorageAtLocals (locals : Store) (offset len : UInt256)
    (words : List UInt256) : Prop where
  offset : locals["offset"]? = some (.int (Int.ofNat offset.toNat))
  length : locals["length"]? = some (.int (Int.ofNat len.toNat))
  index : locals["index"]? = some (.int (Int.ofNat words.length))
  result : locals["result"]? = some (.bytes (wordBytes words))
  storage : locals["_rawStorage"]? = none

-- LIBRARY CANDIDATE: a cast after mathematical addition implements wrapping word addition.
theorem evalWrappingWordAdd {cfg : Config} {frame : Frame} {evm : EVM.State}
    {x y : Expr} {a b : UInt256}
    (hx : evalExpr? cfg frame evm x = .ok (.int (Int.ofNat a.toNat)))
    (hy : evalExpr? cfg frame evm y = .ok (.int (Int.ofNat b.toNat))) :
    evalExpr? cfg frame evm
      (.cast (.binary .add x y) (.elem (.int (.uint ⟨256, by decide⟩)))) =
      .ok (.int (Int.ofNat (a + b).toNat)) := by
  have hadd := naturalAddSource hx hy
  rw [evalExpr?, hadd]
  simp [EvalResult.bind, EvalResult.ofOption, bind, pure, castValue?, normalizeInt,
    EVM.twoPow, uadd_toNat, UInt256.size, Int.natCast_emod, Int.natCast_add]

theorem safeStorageAtCondition (evm : EVM.State) {locals offset len words}
    (hl : StorageAtLocals locals offset len words) :
    evalExpr? config { contract := contract, locals := locals } evm
      (ltE (.var "index") (.var "length")) =
      .ok (.bool (decide (words.length < len.toNat))) := by
  rw [ltE, evalExpr_binary_nonshort (by decide) (by decide), evalLocalValue hl.index,
    evalLocalValue hl.length]
  simp [EvalResult.bind, bind, pure, evalBinaryOp_lt_int_ok]

def storageAtWord (evm : EVM.State) (offset : UInt256) (i : Nat) : UInt256 :=
  Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (offset + UInt256.ofNat i)

def storageAtNextLocals (locals : Store) (words : List UInt256) (value : UInt256) : Store :=
  (locals.insert "result" (.bytes (wordBytes (words ++ [value])))).insert
    "index" (.int (Int.ofNat (words.length + 1)))

theorem safeStorageAtNextLocals {locals offset len words value}
    (hl : StorageAtLocals locals offset len words) :
    StorageAtLocals (storageAtNextLocals locals words value) offset len (words ++ [value]) := by
  constructor
  · simpa [storageAtNextLocals, Std.HashMap.getElem?_insert] using hl.offset
  · simpa [storageAtNextLocals, Std.HashMap.getElem?_insert] using hl.length
  · simp [storageAtNextLocals, Std.HashMap.getElem_insert]
  · simp [storageAtNextLocals, Std.HashMap.getElem_insert]
  · simpa [storageAtNextLocals, Std.HashMap.getElem?_insert] using hl.storage

theorem safeStorageAtStep (evm : EVM.State) {locals offset len words}
    (hl : StorageAtLocals locals offset len words) (hi : words.length + 1 < UInt256.size) :
    ExecBlock config { contract := contract, locals := locals } evm storageAtLoopBody
      (.ok { contract := contract, locals :=
        storageAtNextLocals locals words (storageAtWord evm offset words.length) } evm) := by
  let value := storageAtWord evm offset words.length
  have he : evalExpr? config { contract := contract, locals := locals } evm (.var "index") =
      .ok (.int (Int.ofNat (UInt256.ofNat words.length).toNat)) := by
    rw [ulit_toNat' words.length (by omega)]
    exact evalLocalValue hl.index
  have hraw := safeEvalRawStorage evm locals _ _ hl.storage
    (evalWrappingWordAdd (evalLocalValue hl.offset) he)
  have hp := evalPackedArgs_cons (evalLocalValue hl.result)
    (encodePacked_dynamic_bytes (wordBytes words))
    (evalPackedArgs_single hraw (encodePacked_uint256 value))
  have henc : evalExpr? config { contract := contract, locals := locals } evm
      (.abiEncodePacked [(bytesTy, .var "result"), (uint256, .storage
        (rawStorageRef (.cast (addE (.var "offset") (.var "index")) uint256St)))]) =
      .ok (.bytes (wordBytes (words ++ [value]))) := by
    rw [evalExpr?]
    dsimp only [bytesTy, uint256, uint256Int, uint256St, addE]
    rw [hp]
    simp only [EvalResult.bind, bind, pure, wordBytes_append, wordBytes,
      ByteArray.append_empty, byteArray_mk_toArray_eq_toByteArray, list_toByteArray_append,
      word_toBytesBE_toByteArray_eq_toByteArray, byteArray_toList_toByteArray]
  have hi' : (locals.insert "result" (.bytes (wordBytes (words ++ [value]))))["index"]? =
      some (.int (Int.ofNat words.length)) := by
    simpa [Std.HashMap.getElem?_insert] using hl.index
  exact .consNormal (.assign henc (assignLocalVarBase_ok hl.result))
    (.consNormal (.assign (evalNatIncrement (evalLocalValue hi') hi)
      (assignLocalVarBase_ok hi')) .nil)

theorem safeStorageAtLengthGuard (evm : EVM.State) (offset len : UInt256) :
    evalExpr? config { contract := contract, locals := storageAtArgs offset len } evm
      (leE (shlE (.var "length") (.intLit 5)) maxMemoryLength) =
      .ok (.bool (decide ((UInt256.shiftLeft len (UInt256.ofNat 5)).toNat ≤ 2 ^ 64 - 1))) := by
  have hs : (UInt256.shiftLeft len (UInt256.ofNat 5)).toNat =
      (len.toNat * 32) % UInt256.size := by
    change (len.toNat <<< 5) % UInt256.size = _
    rw [Nat.shiftLeft_eq]
  have hl : evalExpr? config { contract := contract, locals := storageAtArgs offset len } evm
      (.var "length") = .ok (.int (Int.ofNat len.toNat)) :=
    evalLocalValue (by simp [storageAtArgs, Std.HashMap.getElem?_insert])
  rw [hs]
  simp [leE, shlE, maxMemoryLength, evalExpr?, hl, evalBinaryOp?, uint256Int,
    IntType.bitWidth, normalizeInt, EVM.twoPow, UInt256.size, EvalResult.bind, bind, pure,
    Int.natCast_emod, Int.natCast_mul]
  norm_cast

def storageAtInitialLocals (offset len : UInt256) : Store :=
  ((storageAtArgs offset len).insert "result" (.bytes ByteArray.empty)).insert "index" (.int 0)

theorem safeStorageAtInitialLocals (offset len : UInt256) :
    StorageAtLocals (storageAtInitialLocals offset len) offset len [] := by
  constructor <;> simp [storageAtInitialLocals, storageAtArgs, wordBytes,
    Std.HashMap.getElem_insert]

theorem safeStorageAtPrefix (evm : EVM.State) (offset len : UInt256) {result : ExecResult}
    (hv : evm.executionEnv.weiValue = ⟨0⟩)
    (hl : (UInt256.shiftLeft len (UInt256.ofNat 5)).toNat ≤ 2 ^ 64 - 1)
    (htail : ExecBlock config { contract := contract, locals := storageAtInitialLocals offset len }
      evm [storageAtLoop, .return [.var "result"]] result) :
    ExecBlock config { contract := contract, locals := storageAtArgs offset len }
      evm getstorageatTransition.body result := by
  refine .consNormal (.requireTrue (evalCallvalueEq_true hv))
    (.consNormal (.requireTrue (by
      simpa only [hl, decide_true] using safeStorageAtLengthGuard evm offset len))
      (.consNormal (.letDecl ?_) (.consNormal (.letDecl ?_) htail)))
  · simp [emptyBytes, evalExpr?, pure]
  · simp [evalExpr?, pure]

theorem safeStorageAtLengthRevert (evm : EVM.State) (offset len : UInt256)
    (hv : evm.executionEnv.weiValue = ⟨0⟩)
    (hl : ¬(UInt256.shiftLeft len (UInt256.ofNat 5)).toNat ≤ 2 ^ 64 - 1) :
    ExecTransitionBody config contract evm (storageAtArgs offset len)
      getstorageatTransition.body .reverted :=
  .execBlockRevert (.consNormal (.requireTrue (evalCallvalueEq_true hv))
    (.consRevert (.requireFalse (by
      simpa only [hl, decide_false] using safeStorageAtLengthGuard evm offset len))))

end Benchmarks.Safe
