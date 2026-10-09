import Benchmarks.Morpho.MorphoBlue.WordArrayABI
import Benchmarks.Morpho.MorphoBlue.Storage
import Benchmarks.EAS.Attester.LocalArray

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

-- LIBRARY CANDIDATE: a full-width fixed-byte value casts to its unsigned word value.
theorem evalBytes32ToUint {cfg : Config} {frame : Frame} {evm : EVM.State}
    {expr : Expr} {word : UInt256}
    (h : evalExpr? cfg frame evm expr = .ok (wordBytes32Value word)) :
    evalExpr? cfg frame evm (.cast expr (.elem (.int (.uint ⟨256, by decide⟩)))) =
      .ok (.int (Int.ofNat word.toNat)) := by
  simp only [evalExpr?, h, bind, EvalResult.bind, castValue?, wordBytes32Value,
    abiBytes32Width, fixedBytesToNat?, fixedBytesValid, fixedBytesSize,
    word_toBytesBE_length_32, Nat.reduceAdd, Nat.reduceMul, Nat.reduceBEq, if_true,
    fromBytesBE_word, EvalResult.ofOption, decide_true]

theorem morphoLayout_rawSlot (word : UInt256) :
    Syntax.modelLayout ⟨"rawSlots", [.mindex (.int (Int.ofNat word.toNat))]⟩ =
      some (.leaf (bytes32Loc word)) := by
  change some (StorageAddr.leaf (bytes32Loc (keyValueToWord (.int (Int.ofNat word.toNat))))) = _
  rw [keyValueToWord_uint256]

theorem evalMorphoRawSlot {locals imms : Store} {evm : EVM.State} {expr : Expr} {word : UInt256}
    (hbase : locals.get? "rawSlots" = none)
    (hword : evalExpr? config { contract := contract, locals := locals, immutables := imms }
      evm expr = .ok (wordBytes32Value word)) :
    evalExpr? config { contract := contract, locals := locals, immutables := imms }
      evm (.storage ⟨"rawSlots", [.mindex
        (.cast expr (.elem (.int (.uint ⟨256, by decide⟩))))]⟩) =
      .ok (wordBytes32Value (solcSlotWordAt word evm.accountMap evm.executionEnv)) := by
  apply evalExpr_storage_scalar_value hbase
    (er := ⟨"rawSlots", [.mindex (.int (Int.ofNat word.toNat))]⟩)
  · exact evalStorageRef_mindex (evalBytes32ToUint hword) rfl
  · rfl
  · rfl
  · exact morphoLayout_rawSlot word
  · exact storageLocLoad_bytes32 evm word

def extSloadsCond : Expr := .binary .lt (.var "i") (.var "nSlots")
def extSloadsLoopBody : List Stmt := [
  .letDecl "slot" (some abiBytes32) (.index (.var "slots") (.var "i")),
  .letDecl "index" (some abiUInt256) (.var "i"),
  .assign .localVar ⟨"i", []⟩ (.inRange (.uint ⟨256, by decide⟩)
    (.binary .add (.var "i") (.intLit 1))),
  .assign .localVar ⟨"res", [.aindex (.var "index")]⟩
    (.storage ⟨"rawSlots", [.mindex
      (.cast (.var "slot") (.elem (.int (.uint ⟨256, by decide⟩))))]⟩)]

def extSloadsSlot (I : ExecutionEnv) (i : Nat) : UInt256 :=
  calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat + 32 + 32 * i)
def extSloadsValue (evm : EVM.State) (i : Nat) : UInt256 :=
  solcSlotWordAt (extSloadsSlot evm.executionEnv i) evm.accountMap evm.executionEnv

structure ExtSloadsLocals (slots : List Value) (res : List Value) (i : Nat) (locals : Store) : Prop where
  slots_eq : locals.get? "slots" = some (.array slots)
  count_eq : locals.get? "nSlots" = some (.int (Int.ofNat slots.length))
  index_eq : locals.get? "i" = some (.int (Int.ofNat i))
  result_eq : locals.get? "res" = some (.array res)
  raw_eq : locals.get? "rawSlots" = none

theorem extSloadsLoopStep (evm : EVM.State) (locals imms : Store) (slots res : List Value) (i : Nat)
    (hl : ExtSloadsLocals slots res i locals) (hi : i < slots.length)
    (hres : res.length = slots.length) (hfit : i + 1 < UInt256.size)
    (hd : WordArrayDecoded evm.executionEnv.calldata slots) :
    ∃ locals', ExecBlock config { contract := contract, locals := locals, immutables := imms }
      evm extSloadsLoopBody (.ok { contract := contract, locals := locals', immutables := imms } evm) ∧
      ExtSloadsLocals slots (res.set i (wordBytes32Value (extSloadsValue evm i))) (i + 1) locals' := by
  let l1 := locals.insert "slot" (wordBytes32Value (extSloadsSlot evm.executionEnv i))
  let l2 := l1.insert "index" (.int (Int.ofNat i))
  let l3 := l2.insert "i" (.int (Int.ofNat (i + 1)))
  let l4 := l3.insert "res" (.array (res.set i (wordBytes32Value (extSloadsValue evm i))))
  have hsi : l2.get? "i" = some (.int (Int.ofNat i)) := by
    simpa [l2, l1, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] using hl.index_eq
  have hrr : l3.get? "res" = some (.array res) := by
    simpa [l3, l2, l1, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] using hl.result_eq
  have hraw : l3.get? "rawSlots" = none := by
    simpa [l3, l2, l1, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] using hl.raw_eq
  have hlookup : slots[i]? = some (wordBytes32Value (extSloadsSlot evm.executionEnv i)) := by
    simpa only [← lookupNth_eq_getElem?, extSloadsSlot] using hd.lookup hi
  have hi1 : l1.get? "i" = some (.int (Int.ofNat i)) := by
    simpa [l1, Std.HashMap.getElem?_insert] using hl.index_eq
  have hi3 : l3.get? "index" = some (.int (Int.ofNat i)) := by
    simp only [l3, l2, store_get_ne (k := "i") (a := "index") _ _ (by decide), store_get_self]
  have hs3 : l3.get? "slot" = some (wordBytes32Value (extSloadsSlot evm.executionEnv i)) := by
    simp only [l3, l2, l1, store_get_ne (k := "i") (a := "slot") _ _ (by decide),
      store_get_ne (k := "index") (a := "slot") _ _ (by decide), store_get_self]
  refine ⟨l4, ?_, ?_⟩
  · refine ExecBlock.consNormal (ExecStmt.letDecl
      (evalLocalArrayIndex hl.slots_eq hl.index_eq hlookup rfl)) ?_
    refine ExecBlock.consNormal (ExecStmt.letDecl (evalLocalValue hi1)) ?_
    refine ExecBlock.consNormal (ExecStmt.assign
      (uint256RangeSourceOk (naturalAddSource (evalLocalValue hsi)
        (by simp only [evalExpr?, pure, Int.ofNat_eq_natCast, Nat.cast_one])) hfit)
      (assignLocalValue hsi)) ?_
    exact ExecBlock.consNormal (ExecStmt.assign (evalMorphoRawSlot hraw (evalLocalValue hs3))
      (assignLocalArrayIndex hrr hi3 (by omega))) ExecBlock.nil
  · constructor
    · simpa [l4, l3, l2, l1, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] using hl.slots_eq
    · simpa [l4, l3, l2, l1, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] using hl.count_eq
    · simp only [l4, l3, store_get_ne (k := "res") (a := "i") _ _ (by decide), store_get_self]
    · exact store_get_self _ _ _
    · simpa [l4, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] using hraw

end Benchmarks.Morpho.MorphoBlue
