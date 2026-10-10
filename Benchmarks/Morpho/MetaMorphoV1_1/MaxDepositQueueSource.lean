import Benchmarks.Morpho.MetaMorphoV1_1.MaxDepositLoopSyntax
import Benchmarks.Morpho.MetaMorphoV1_1.ArrayStorage
import Benchmarks.Morpho.MetaMorphoV1_1.MappingStructs

/-! Source queue reads, capacity selection, and loop control for maxDeposit. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

set_option autoImplicit false

def maxDepositQueueSlot (i : UInt256) : UInt256 :=
  uInt256OfByteArray (KEC (UInt256.toByteArray ⟨20⟩)) + i

def maxDepositIdWord (I : ExecutionEnv) (σ : AccountMap) (i : UInt256) : UInt256 :=
  codeOwnerStorageWord I σ (maxDepositQueueSlot i)

def maxDepositCapWord (I : ExecutionEnv) (σ : AccountMap) (id : UInt256) : UInt256 :=
  UInt256.land (codeOwnerStorageWord I σ (solcMappingSlot ⟨13⟩ id))
    (UInt256.ofNat (2 ^ 184 - 1))

def maxDepositCapFrame (frame : Frame) (id cap : UInt256) : Frame :=
  { frame with
    locals := (frame.locals.insert "id" (wordBytes32Value id)).insert "supplyCap"
      (uint256Value cap) }

theorem maxDepositQueueRead {frame : Frame} {evm : State} {i : UInt256}
    (hcontract : frame.contract = contract) (hbase : frame.locals.get? "supplyQueue" = none)
    (hi : frame.locals.get? "i" = some (uint256Value i))
    (hbound : i.toNat < (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨20⟩).toNat) :
    evalExpr? config frame evm (.storage ⟨"supplyQueue", [.aindex (.var "i")]⟩) =
      .ok (wordBytes32Value
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (maxDepositQueueSlot i))) := by
  have hb : arrayIndexInBounds? config evm frame.contract.storage "supplyQueue" []
      (.int (Int.ofNat i.toNat)) = .ok () := by
    rw [hcontract, supplyQueueBounds, if_pos hbound]
  apply evalExpr_storage_scalar_value
    (er := ⟨"supplyQueue", [.aindex (.int (Int.ofNat i.toNat))]⟩)
    (t := .bytes ⟨31, by decide⟩) hbase
    (evalStorageRef_arrayIndex "supplyQueue" "i" _ hi hb)
    (by rw [hcontract]; rfl) rfl (loc := bytes32Loc (maxDepositQueueSlot i))
  · change some (StorageAddr.leaf
      { slot := uInt256OfByteArray (KEC (UInt256.toByteArray ⟨20⟩)) +
          UInt256.ofNat ((keyValueToWord (.int (Int.ofNat i.toNat))).toNat / 1)
        offset := Fin.ofNat 32 ((keyValueToWord (.int (Int.ofNat i.toNat))).toNat % 1 * 32)
        size := 32, hbound := by simp, type := .bytes ⟨31, by decide⟩ }) = _
    simp only [keyValueToWord_uint256, Nat.div_one, Nat.mod_one, Nat.zero_mul,
      u256_ofNat_toNat]
    rfl
  · exact storageLocLoad_bytes32 evm _

theorem configCapRead {frame : Frame} {evm : State} {id : UInt256} {key : Expr}
    (hcontract : frame.contract = contract) (hbase : frame.locals.get? "config" = none)
    (hid : evalExpr? config frame evm key = .ok (wordBytes32Value id)) :
    evalExpr? config frame evm (.storage ⟨"config", [.mindex key, .field "cap"]⟩) =
      .ok (uint256Value (UInt256.land
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (solcMappingSlot ⟨13⟩ id))
        (UInt256.ofNat (2 ^ 184 - 1)))) := by
  apply evalExpr_storage_scalar_value
    (er := ⟨"config", [.mindex (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE id)),
      .field "cap"]⟩)
    (t := .int (.uint ⟨184, by decide⟩)) hbase
    (evalStorageRef_bytes32FieldExpr "config" "cap" key (EVM.Word.toBytesBE id)
      (word_toBytesBE_length_32 id) hid) (by rw [hcontract]; rfl) rfl
    (loc :=
      { slot := solcMappingSlot ⟨13⟩ id, offset := 0, size := 23,
        hbound := by decide, type := .int (.uint ⟨184, by decide⟩) })
  · change some (StorageAddr.leaf
      { slot := solcMappingSlot ⟨13⟩
          (keyValueToWord (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE id))),
        offset := 0, size := 23, hbound := by decide,
        type := .int (.uint ⟨184, by decide⟩) }) = _
    simp only [abiBytes32Width, keyValueToWord_fixedBytes32]
  · exact storageLocLoad_uint_offset0 evm _ 23 ⟨184, by decide⟩ rfl (by decide)

theorem maxDepositCapRead {frame : Frame} {evm : State} {id : UInt256}
    (hcontract : frame.contract = contract) (hbase : frame.locals.get? "config" = none)
    (hid : frame.locals.get? "id" = some (wordBytes32Value id)) :
    evalExpr? config frame evm (.storage ⟨"config", [.mindex (.var "id"), .field "cap"]⟩) =
      .ok (uint256Value (UInt256.land
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (solcMappingSlot ⟨13⟩ id))
        (UInt256.ofNat (2 ^ 184 - 1)))) :=
  configCapRead hcontract hbase (by simp only [evalExpr?, hid, EvalResult.ofOption])

theorem maxDepositQueuePrefix {frame : Frame} {evm s0 : State} {I : ExecutionEnv}
    {σ : AccountMap} {i : UInt256}
    (hcontract : frame.contract = contract) (hqueue : frame.locals.get? "supplyQueue" = none)
    (hconfig : frame.locals.get? "config" = none)
    (hi : frame.locals.get? "i" = some (uint256Value i))
    (hs : SourceState s0 I σ evm) (hbound : i.toNat < (codeOwnerStorageWord I σ ⟨20⟩).toNat) :
    ABlock config evm frame maxDepositIteration
      (maxDepositCapFrame frame (maxDepositIdWord I σ i)
        (maxDepositCapWord I σ (maxDepositIdWord I σ i))) (maxDepositIteration.drop 2) := by
  constructor
  intro result htail
  have hread := maxDepositQueueRead hcontract hqueue hi
    (by rw [hs.storageRead]; exact hbound)
  rw [hs.storageRead] at hread
  apply ExecBlock.consNormal (ExecStmt.letDecl hread)
  apply ExecBlock.consNormal (ExecStmt.letDecl ?_) htail
  have hcap := maxDepositCapRead (evm := evm) (frame := { frame with
    locals := frame.locals.insert "id" (wordBytes32Value (maxDepositIdWord I σ i)) })
    hcontract (by rw [store_get_ne _ _ (by decide)]; exact hconfig) (store_get_self _ _ _)
  rw [hs.storageRead] at hcap
  exact hcap

theorem maxDepositCapConditionSource {frame : Frame} {evm : State} {cap : UInt256}
    (hc : frame.locals.get? "supplyCap" = some (uint256Value cap)) :
    evalExpr? config frame evm maxDepositCapCondition = .ok (.bool (decide (cap = ⟨0⟩))) := by
  simp only [maxDepositCapCondition, evalExpr?, hc, EvalResult.ofOption, uint256Value,
    bind, EvalResult.bind, evalBinaryOp?, pure]
  simp only [BEq.beq, Value.int.injEq]
  congr 3
  exact propext (by
    constructor
    · intro h; apply u256_inj; simpa using h
    · rintro rfl; rfl)

theorem maxDepositConditionSource {frame : Frame} {evm : State} {i len : UInt256}
    (hcontract : frame.contract = contract) (hbase : frame.locals.get? "supplyQueue" = none)
    (hi : frame.locals.get? "i" = some (uint256Value i))
    (hlen : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨20⟩ = len) :
    evalExpr? config frame evm maxDepositCondition =
      .ok (.bool (decide (i.toNat < len.toNat))) := by
  rcases frame with ⟨c, locals, imms⟩
  dsimp only at hcontract hbase hi
  subst c
  have hl := evalStorage_supplyQueueLength evm locals imms hbase
  rw [hlen] at hl
  simp only [maxDepositCondition, evalExpr?, hl, hi, EvalResult.ofOption,
    bind, EvalResult.bind, uint256Value, evalBinaryOp?, Int.ofNat_eq_natCast, Int.ofNat_lt]

def maxDepositPostFrame (frame : Frame) (i : UInt256) : Frame :=
  { frame with locals := frame.locals.insert "i" (uint256Value (i + ⟨1⟩)) }

theorem maxDepositPostSource {frame : Frame} {evm : State} {i : UInt256}
    (hi : frame.locals.get? "i" = some (uint256Value i))
    (hfit : i.toNat + 1 < UInt256.size) :
    ExecBlock config frame evm maxDepositPost (.ok (maxDepositPostFrame frame i) evm) := by
  apply ExecBlock.consNormal
    (ExecStmt.assign (checkedAddSourceOk (a := i) (b := ⟨1⟩) ?_ ?_ hfit) ?_) ExecBlock.nil
  · simp only [evalExpr?, hi, EvalResult.ofOption]
  · simp only [evalExpr?, pure]; rfl
  · simp only [assignStorageRef?, hi, updateLocalPath?, bind, EvalResult.bind, pure]
    rfl

theorem maxDepositCapFrame_preserves (frame : Frame) (id cap : UInt256) (name : Ident)
    (hid : ("id" == name) = false) (hcap : ("supplyCap" == name) = false) :
    (maxDepositCapFrame frame id cap).locals.get? name = frame.locals.get? name := by
  rw [maxDepositCapFrame, store_get_ne _ _ hcap, store_get_ne _ _ hid]

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
