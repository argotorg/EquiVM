import Benchmarks.Morpho.MetaMorphoV1_1.StringStorageWrite
import Benchmarks.Morpho.MetaMorphoV1_1.AllocationSource
import Benchmarks.Morpho.MetaMorphoV1_1.AccessControl

/-! Shared source paths for the two metadata setters. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory
open Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

namespace Benchmarks.Morpho.MetaMorphoV1_1

set_option autoImplicit false
set_option maxRecDepth 2000

def stringSetParam (symbol : Bool) : Ident := if symbol then "newSymbol" else "newName"

def stringSetEvent (symbol : Bool) : Ident := if symbol then "SetSymbol" else "SetName"

def stringSetTransition (symbol : Bool) : TransitionDecl :=
  if symbol then setSymbolTransition else setNameTransition

def stringSetLocals (symbol : Bool) (bytes : ByteArray) : Store :=
  (∅ : Store).insert (stringSetParam symbol) (.bytes bytes)

def stringSetFrame (symbol : Bool) (evm : State) (imms : Store) (bytes : ByteArray) : Frame :=
  ⟨contract, (stringSetLocals symbol bytes).insert "__calldata" (.bytes evm.executionEnv.calldata),
    imms⟩

def stringSetAllocatedFrame (symbol : Bool) (evm : State) (imms : Store)
    (bytes : ByteArray) : Frame :=
  { stringSetFrame symbol evm imms bytes with
    locals := (stringSetFrame symbol evm imms bytes).locals.insert "__solcStringCursor"
      (uint256Value (nextCursor ⟨128⟩ (UInt256.ofNat (32 + bytes.size)))) }

def stringSetOwnerFrame (symbol : Bool) (evm : State) (imms : Store) (bytes : ByteArray) : Frame :=
  { stringSetAllocatedFrame symbol evm imms bytes with
    locals := (stringSetAllocatedFrame symbol evm imms bytes).locals.insert "__c0" .unit }

def stringSetAssignStatement (symbol : Bool) : Stmt :=
  .assign .storage ⟨stringViewField symbol, []⟩ (.var (stringSetParam symbol))

def stringSetTail (symbol : Bool) : List Stmt :=
  [stringSetAssignStatement symbol, .emit (stringSetEvent symbol) [.var (stringSetParam symbol)]]

def stringSetAllocationStatement (symbol : Bool) : Stmt :=
  .internalCall allocateFunction.name
    [.intLit 128, stringSetAllocationSizeExpr (stringSetParam symbol)] "__solcStringCursor"

theorem stringSetBodyShape (symbol : Bool) :
    (stringSetTransition symbol).body = (Syntax.contractSyntax.transitions[1]!).body.take 3 ++
      stringSetAllocationStatement symbol :: .internalCall "_checkOwner" [] "__c0" ::
        stringSetTail symbol := by
  cases symbol <;> rfl

theorem stringSetSizeSource (symbol : Bool) (evm : State) (imms : Store) (bytes : ByteArray)
    (hsize : 32 + bytes.size < UInt256.size) :
    evalExpr? config (stringSetFrame symbol evm imms bytes) evm
      (stringSetAllocationSizeExpr (stringSetParam symbol)) =
      .ok (uint256Value (UInt256.ofNat (32 + bytes.size))) := by
  have hl : evalExpr? config (stringSetFrame symbol evm imms bytes) evm
      (.arrayLength .localVar ⟨stringSetParam symbol, []⟩) = .ok (.int (Int.ofNat bytes.size)) := by
    cases symbol <;> simp [evalExpr?, stringSetFrame, stringSetLocals, stringSetParam,
      readLocalPath?, Std.HashMap.getElem_insert, EvalResult.ofOption, bind, EvalResult.bind, pure]
  have hr : evalExpr? config (stringSetFrame symbol evm imms bytes) evm (.intLit 32) =
      .ok (.int (Int.ofNat 32)) := by simp only [evalExpr?, pure]; rfl
  change _ = EvalResult.ok (Value.int (Int.ofNat (UInt256.ofNat (32 + bytes.size)).toNat))
  rw [UInt256.toNat_ofNat_of_lt hsize, Nat.add_comm 32 bytes.size]
  exact naturalAddSource hl hr

theorem stringSetPrefix (symbol : Bool) (evm : State) (imms : Store) (bytes : ByteArray)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < 2 ^ 255 + 4) :
    ABlock config evm ⟨contract, stringSetLocals symbol bytes, imms⟩
      (stringSetTransition symbol).body (stringSetFrame symbol evm imms bytes)
      (stringSetAllocationStatement symbol :: .internalCall "_checkOwner" [] "__c0" ::
        stringSetTail symbol) := by
  rw [stringSetBodyShape]
  exact nonpayableCalldataPrefix "__calldata" (2 ^ 255 + 4) hwv hhi

theorem stringSetAllocatedPrefix (symbol : Bool) (evm : State) (imms : Store) (bytes : ByteArray)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (hsize : bytes.size < 2 ^ 64)
    (hfit : allocationFits ⟨128⟩ (UInt256.ofNat (32 + bytes.size))) :
    ABlock config evm ⟨contract, stringSetLocals symbol bytes, imms⟩
      (stringSetTransition symbol).body (stringSetAllocatedFrame symbol evm imms bytes)
      (.internalCall "_checkOwner" [] "__c0" :: stringSetTail symbol) := by
  constructor
  intro result htail
  apply (stringSetPrefix symbol evm imms bytes hwv hhi).run
  exact ExecBlock.consNormal (allocateCallReturns "__solcStringCursor" rfl
    (by simp only [evalExpr?, pure]; rfl)
    (stringSetSizeSource symbol evm imms bytes (by change _ < 2 ^ 256; omega)) hfit) htail

theorem stringSetRevertsAllocation (symbol : Bool) (evm : State) (imms : Store) (bytes : ByteArray)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (hsize : bytes.size < 2 ^ 64)
    (hbad : ¬ allocationFits ⟨128⟩ (UInt256.ofNat (32 + bytes.size))) :
    ExecTransitionBody config contract evm (stringSetLocals symbol bytes)
      (stringSetTransition symbol).body .reverted imms := by
  apply ExecFuncBody.execBlockRevert
  apply (stringSetPrefix symbol evm imms bytes hwv hhi).run
  exact ExecBlock.consRevert (allocateCallReverts "__solcStringCursor" rfl
    (by simp only [evalExpr?, pure]; rfl)
    (stringSetSizeSource symbol evm imms bytes (by change _ < 2 ^ 256; omega)) hbad)

theorem stringSetRevertsOwner (symbol : Bool) (evm : State) (imms : Store) (bytes : ByteArray)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (hsize : bytes.size < 2 ^ 64)
    (hfit : allocationFits ⟨128⟩ (UInt256.ofNat (32 + bytes.size)))
    (howner : ownerAddress evm ≠ evm.executionEnv.source) :
    ExecTransitionBody config contract evm (stringSetLocals symbol bytes)
      (stringSetTransition symbol).body .reverted imms := by
  apply ExecFuncBody.execBlockRevert
  apply (stringSetAllocatedPrefix symbol evm imms bytes hwv hhi hsize hfit).run
  exact ExecBlock.consRevert (checkOwnerCallReverts evm _ imms "__c0" howner)

theorem stringSetOwnerPrefix (symbol : Bool) (evm : State) (imms : Store) (bytes : ByteArray)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (hsize : bytes.size < 2 ^ 64)
    (hfit : allocationFits ⟨128⟩ (UInt256.ofNat (32 + bytes.size)))
    (howner : ownerAddress evm = evm.executionEnv.source) :
    ABlock config evm ⟨contract, stringSetLocals symbol bytes, imms⟩
      (stringSetTransition symbol).body (stringSetOwnerFrame symbol evm imms bytes)
      (stringSetTail symbol) := by
  constructor
  intro result htail
  apply (stringSetAllocatedPrefix symbol evm imms bytes hwv hhi hsize hfit).run
  exact ExecBlock.consNormal (checkOwnerCallReturns evm _ imms "__c0" howner) htail

theorem stringSetValueSource (symbol : Bool) (evm evm' : State) (imms : Store) (bytes : ByteArray) :
    evalExpr? config (stringSetOwnerFrame symbol evm imms bytes) evm'
      (.var (stringSetParam symbol)) = .ok (.bytes bytes) := by
  cases symbol <;> simp [evalExpr?, stringSetOwnerFrame, stringSetAllocatedFrame, stringSetFrame,
    stringSetLocals, stringSetParam, Std.HashMap.getElem_insert, EvalResult.ofOption]

theorem stringSetStorageUnshadowed (symbol : Bool) (evm : State) (imms : Store)
    (bytes : ByteArray) :
    (stringSetOwnerFrame symbol evm imms bytes).locals.get? (stringViewField symbol) = none := by
  cases symbol <;> simp [stringSetOwnerFrame, stringSetAllocatedFrame, stringSetFrame,
    stringSetLocals, stringSetParam, stringViewField, Std.HashMap.getElem_insert]

theorem stringSetAssign (symbol : Bool) (evm : State) (imms : Store) (bytes : ByteArray)
    (hvalid : storageStringValid (storageStringHeader evm (stringViewSlot symbol))) :
    ExecStmt config (stringSetOwnerFrame symbol evm imms bytes) evm
      (stringSetAssignStatement symbol)
      (.ok (stringSetOwnerFrame symbol evm imms bytes)
        (storageStringWriteState evm (stringViewSlot symbol) bytes)) :=
  ExecStmt.assign (stringSetValueSource symbol evm evm imms bytes)
    (assignStorageString symbol evm _ imms bytes
      (stringSetStorageUnshadowed symbol evm imms bytes) hvalid)

theorem stringSetRevertsHeader (symbol : Bool) (evm : State) (imms : Store) (bytes : ByteArray)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (hsize : bytes.size < 2 ^ 64)
    (hfit : allocationFits ⟨128⟩ (UInt256.ofNat (32 + bytes.size)))
    (howner : ownerAddress evm = evm.executionEnv.source)
    (hbad : ¬ storageStringValid (storageStringHeader evm (stringViewSlot symbol))) :
    ExecTransitionBody config contract evm (stringSetLocals symbol bytes)
      (stringSetTransition symbol).body .reverted imms := by
  apply ExecFuncBody.execBlockRevert
  apply (stringSetOwnerPrefix symbol evm imms bytes hwv hhi hsize hfit howner).run
  exact ExecBlock.consRevert (ExecStmt.assignStoreRevert
    (stringSetValueSource symbol evm evm imms bytes)
    (assignStorageStringReverts symbol evm _ imms bytes
      (stringSetStorageUnshadowed symbol evm imms bytes) hbad))

theorem stringSetBodyStatic (symbol : Bool) (evm : State) (imms : Store) (bytes : ByteArray)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (hsize : bytes.size < 2 ^ 64)
    (hfit : allocationFits ⟨128⟩ (UInt256.ofNat (32 + bytes.size)))
    (howner : ownerAddress evm = evm.executionEnv.source)
    (hvalid : storageStringValid (storageStringHeader evm (stringViewSlot symbol)))
    (hperm : evm.executionEnv.perm = false) :
    ExecTransitionBody config contract evm (stringSetLocals symbol bytes)
      (stringSetTransition symbol).body .staticViolation imms := by
  apply ExecFuncBody.execBlockStatic
  apply (stringSetOwnerPrefix symbol evm imms bytes hwv hhi hsize hfit howner).run
  exact ExecBlock.consStatic (execStmt_assign_static
    (stringSetAssign symbol evm imms bytes hvalid) hperm)

theorem stringSetBodyReturns (symbol : Bool) (evm : State) (imms : Store) (bytes : ByteArray)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (hsize : bytes.size < 2 ^ 64)
    (hfit : allocationFits ⟨128⟩ (UInt256.ofNat (32 + bytes.size)))
    (howner : ownerAddress evm = evm.executionEnv.source)
    (hvalid : storageStringValid (storageStringHeader evm (stringViewSlot symbol))) :
    ExecTransitionBody config contract evm (stringSetLocals symbol bytes)
      (stringSetTransition symbol).body
      (.returned (stringSetOwnerFrame symbol evm imms bytes)
        (storageStringWriteState evm (stringViewSlot symbol) bytes) none) imms := by
  apply ExecFuncBody.execBlockOK
  apply (stringSetOwnerPrefix symbol evm imms bytes hwv hhi hsize hfit howner).run
  apply ExecBlock.consNormal (stringSetAssign symbol evm imms bytes hvalid)
  apply (ABlock.start.emitStep (vals := [.bytes bytes]) ?_).run
  · exact ExecBlock.nil
  · simp only [evalExprs?, stringSetValueSource, EvalResult.bind, bind, pure]

end Benchmarks.Morpho.MetaMorphoV1_1
