import Benchmarks.Morpho.MetaMorphoV1_1.StringStorageSource
import Benchmarks.Morpho.MetaMorphoV1_1.AllocationSource

/-! Source outcomes for the name and symbol getters, including compiler allocation failure. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory
open Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

namespace Benchmarks.Morpho.MetaMorphoV1_1

set_option maxRecDepth 2000

def stringViewTransition (symbol : Bool) : TransitionDecl :=
  if symbol then symbolTransition else nameTransition

def stringViewTail (symbol : Bool) : List Stmt :=
  [.letDecl stringValueName none (.storage ⟨stringViewField symbol, []⟩),
   .internalCall allocateFunction.name [.intLit 128, stringAllocationSizeExpr] "__c0",
   .return [.var stringValueName]]

theorem stringViewBodyShape (symbol : Bool) :
    (stringViewTransition symbol).body =
      (Syntax.contractSyntax.transitions[1]!).body.take 3 ++ stringViewTail symbol := by
  cases symbol <;> rfl

def stringViewFrame (evm : State) (imms : Store) : Frame :=
  ⟨contract, (∅ : Store).insert "__calldata" (.bytes evm.executionEnv.calldata), imms⟩

def stringViewLoadedFrame (evm : State) (imms : Store) (bytes : ByteArray) : Frame :=
  { stringViewFrame evm imms with
    locals := (stringViewFrame evm imms).locals.insert stringValueName (.bytes bytes) }

def stringViewFinalFrame (evm : State) (imms : Store) (bytes : ByteArray) : Frame :=
  { stringViewLoadedFrame evm imms bytes with
    locals := (stringViewLoadedFrame evm imms bytes).locals.insert "__c0"
      (uint256Value (nextCursor ⟨128⟩ (UInt256.ofNat (bytes.size + 32)))) }

theorem stringAllocationSizeSource (evm : State) (imms : Store) (bytes : ByteArray)
    (hfit : bytes.size + 32 < UInt256.size) :
    evalExpr? config (stringViewLoadedFrame evm imms bytes) evm stringAllocationSizeExpr =
      .ok (uint256Value (UInt256.ofNat (bytes.size + 32))) := by
  have hl : evalExpr? config (stringViewLoadedFrame evm imms bytes) evm
      (.arrayLength .localVar ⟨stringValueName, []⟩) = .ok (.int (Int.ofNat bytes.size)) := by
    simp only [evalExpr?, stringViewLoadedFrame, store_get_self, readLocalPath?, bind,
      EvalResult.bind, pure]
  have hr : evalExpr? config (stringViewLoadedFrame evm imms bytes) evm (.intLit 32) =
      .ok (.int (Int.ofNat 32)) := by simp only [evalExpr?, pure]; rfl
  simpa only [uint256Value, UInt256.toNat_ofNat_of_lt hfit] using naturalAddSource hl hr

theorem stringViewRevertsHeader (symbol : Bool) (evm : State) (imms : Store)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (hbad : ¬ storageStringValid (storageStringHeader evm (stringViewSlot symbol))) :
    ExecTransitionBody config contract evm ∅ (stringViewTransition symbol).body .reverted imms :=
    by
  rw [stringViewBodyShape]
  apply ExecFuncBody.execBlockRevert
  apply (nonpayableCalldataPrefix "__calldata" (2 ^ 255 + 4) hwv hhi).run
  exact ExecBlock.consRevert (ExecStmt.letDeclRevert
    (evalStorage_stringReverts symbol evm _ imms (by
      cases symbol <;> simp [stringViewField, stringViewFrame]) hbad))

theorem stringViewReadPrefix (symbol : Bool) (evm : State) (imms : Store)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (hvalid : storageStringValid (storageStringHeader evm (stringViewSlot symbol))) :
    ABlock config evm ⟨contract, ∅, imms⟩ (stringViewTransition symbol).body
      (stringViewLoadedFrame evm imms (storageStringBytes evm (stringViewSlot symbol)))
      [.internalCall allocateFunction.name [.intLit 128, stringAllocationSizeExpr] "__c0",
       .return [.var stringValueName]] := by
  rw [stringViewBodyShape]
  apply (nonpayableCalldataPrefix "__calldata" (2 ^ 255 + 4) hwv hhi).letStep
  exact evalStorage_string symbol evm _ imms (by
    cases symbol <;> simp [stringViewField, stringViewFrame]) hvalid

theorem stringViewBodyReturns (symbol : Bool) (evm : State) (imms : Store)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (hvalid : storageStringValid (storageStringHeader evm (stringViewSlot symbol)))
    (hfit : allocationFits ⟨128⟩
      (UInt256.ofNat ((storageStringBytes evm (stringViewSlot symbol)).size + 32))) :
    ExecTransitionBody config contract evm ∅ (stringViewTransition symbol).body
      (.returned (stringViewFinalFrame evm imms (storageStringBytes evm (stringViewSlot symbol)))
        evm (some [.bytes (storageStringBytes evm (stringViewSlot symbol))])) imms := by
  have hb : (storageStringBytes evm (stringViewSlot symbol)).size + 32 < UInt256.size := by
    rw [storageStringBytes_size]
    have := storageStringLength_lt (storageStringHeader evm (stringViewSlot symbol))
    change _ < 2 ^ 256
    omega
  apply ExecFuncBody.execBlockRet
  apply (stringViewReadPrefix symbol evm imms hwv hhi hvalid).run
  apply ExecBlock.consNormal (allocateCallReturns "__c0" rfl
    (by simp only [evalExpr?, pure]; rfl) (stringAllocationSizeSource evm imms _ hb) hfit)
  apply ExecBlock.consReturn (ExecStmt.return ?_)
  simp [evalExprs?, evalExpr?, stringViewLoadedFrame, stringViewFinalFrame, stringValueName,
    Std.HashMap.getElem_insert, EvalResult.ofOption, bind, EvalResult.bind, pure]

theorem stringViewRevertsAllocation (symbol : Bool) (evm : State) (imms : Store)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (hvalid : storageStringValid (storageStringHeader evm (stringViewSlot symbol)))
    (hbad : ¬ allocationFits ⟨128⟩
      (UInt256.ofNat ((storageStringBytes evm (stringViewSlot symbol)).size + 32))) :
    ExecTransitionBody config contract evm ∅ (stringViewTransition symbol).body .reverted imms :=
    by
  have hb : (storageStringBytes evm (stringViewSlot symbol)).size + 32 < UInt256.size := by
    rw [storageStringBytes_size]
    have := storageStringLength_lt (storageStringHeader evm (stringViewSlot symbol))
    change _ < 2 ^ 256
    omega
  apply ExecFuncBody.execBlockRevert
  apply (stringViewReadPrefix symbol evm imms hwv hhi hvalid).run
  exact ExecBlock.consRevert (allocateCallReverts "__c0" rfl
    (by simp only [evalExpr?, pure]; rfl) (stringAllocationSizeSource evm imms _ hb) hbad)

end Benchmarks.Morpho.MetaMorphoV1_1
