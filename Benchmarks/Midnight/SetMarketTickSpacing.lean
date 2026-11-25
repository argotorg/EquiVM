import Benchmarks.Midnight.Dispatch
import Benchmarks.Midnight.RoleSource
import Benchmarks.Midnight.SettlementFields
import Benchmarks.Midnight.PackedByte
import Benchmarks.Midnight.ModArithmetic
import Benchmarks.Midnight.PairDecode
import Benchmarks.Midnight.AddressDecode
import Benchmarks.Midnight.ScratchMemory

variable {fork : Ethereum.Fork}

/-!
# Midnight `setMarketTickSpacing(bytes32,uint256)`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Stele body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 1436; reach lemma `midnightReachSetMarketTickSpacingBody`.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

def tickArguments (id value : UInt256) : Store :=
  ((∅ : Store).insert "id" (wordBytes32Value id)).insert "newTickSpacing" (.int value.toNat)

def tickState (evm : EVM.State) (id value : UInt256) : EVM.State :=
  let slot := solcMappingSlot ⟨1⟩ id + ⟨2⟩
  Stele.EVM.storageStore evm evm.executionEnv.codeOwner slot
    (setUint8Offset18Word (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner slot) value)

def tickReadExpr : Expr := .storage { base := "marketState", steps :=
  [.mindex (.var "id"), .field "tickSpacing"] }

def tickChangeExpr : Expr := .binary .and (.binary .gt (.var "newTickSpacing") (.intLit 0))
  (.binary .eq (.binary .mod tickReadExpr (.var "newTickSpacing")) (.intLit 0))

def tickChangeAllowed (evm : EVM.State) (id value : UInt256) : Prop :=
  0 < value.toNat ∧ (marketTickSpacing (marketFeeWord evm id)).toNat % value.toNat = 0
instance (evm : EVM.State) (id value : UInt256) : Decidable (tickChangeAllowed evm id value) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem tickValueGet (evm : EVM.State) (id value : UInt256) :
    (calldataFrame contract (tickArguments id value) ∅ evm).locals.get? "newTickSpacing" =
      some (.int value.toNat) := by
  change (((tickArguments id value).insert "__calldata"
    (.bytes evm.executionEnv.calldata)).get? "newTickSpacing") = _
  rw [store_get_ne _ _ (by decide)]
  exact store_get_self _ _ _

theorem tickIdGet (evm : EVM.State) (id value : UInt256) :
    (calldataFrame contract (tickArguments id value) ∅ evm).locals.get? "id" =
      some (wordBytes32Value id) := by
  change (((tickArguments id value).insert "__calldata"
    (.bytes evm.executionEnv.calldata)).get? "id") = _
  rw [store_get_ne _ _ (by decide), tickArguments, store_get_ne _ _ (by decide), store_get_self]

theorem tickAuthEval (evm : EVM.State) (id value : UInt256) :
    evalExpr? config (calldataFrame contract (tickArguments id value) ∅ evm) evm
      (roleGuard "tickSpacingSetter") = .ok (.bool (decide (roleAllowed evm ⟨12⟩))) := by
  exact evalRoleGuard evm "tickSpacingSetter" ⟨12⟩ rfl
    (by simp [calldataFrame, tickArguments]) rfl rfl

theorem tickRead (evm : EVM.State) (id value : UInt256) :
    evalExpr? config (calldataFrame contract (tickArguments id value) ∅ evm) evm tickReadExpr =
      .ok (.int (marketTickSpacing (marketFeeWord evm id)).toNat) := by
  apply evalExpr_storage_scalar_value (layout := midnightStorageLayout)
    (er := { base := "marketState", steps := [.mindex
      (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE id)), .field "tickSpacing"] })
    (t := .int packedUInt8Int) (loc := packedUInt8Loc (solcMappingSlot ⟨1⟩ id + ⟨2⟩) 18)
  · simp [calldataFrame, tickArguments]
  · have hl : (EVM.Word.toBytesBE id).length = 32 := by
      simpa using word_toBytesBE_toByteArray_size id
    simp only [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, evalExpr?,
      tickIdGet, EvalResult.bind, EvalResult.ofOption, valueToKey?, wordBytes32Value, pure, bind,
      hl, show (abiBytes32Width : Nat) + 1 = 32 from rfl, ite_true]
  · rfl
  · rfl
  · change some (StorageAddr.leaf (packedUInt8Loc (solcMappingSlot ⟨1⟩
      (keyValueToWord (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE id))) + ⟨2⟩) 18)) = _
    simp only [abiBytes32Width, keyValueToWord_fixedBytes32]
  · exact storageLocLoad_uint8_offset18 evm _

theorem tickEnabledEval (evm : EVM.State) (id value : UInt256) :
    evalExpr? config (calldataFrame contract (tickArguments id value) ∅ evm) evm
      (.binary .gt tickReadExpr (.intLit 0)) =
      .ok (.bool (decide (0 < (marketTickSpacing (marketFeeWord evm id)).toNat))) := by
  rw [evalExpr_binary_nonshort (by decide : BinaryOp.gt ≠ .and) (by decide : BinaryOp.gt ≠ .or)]
  rw [tickRead]
  simp [evalExpr?, bind, pure, EvalResult.bind, evalBinaryOp?]

theorem tickChangeEval (evm : EVM.State) (id value : UInt256) :
    evalExpr? config (calldataFrame contract (tickArguments id value) ∅ evm) evm tickChangeExpr =
      .ok (.bool (decide (tickChangeAllowed evm id value))) := by
  have hv : evalExpr? config (calldataFrame contract (tickArguments id value) ∅ evm) evm
      (.var "newTickSpacing") = .ok (.int value.toNat) := by
    simp only [evalExpr?, tickValueGet, EvalResult.ofOption]
  have hp : evalExpr? config (calldataFrame contract (tickArguments id value) ∅ evm) evm
      (.binary .gt (.var "newTickSpacing") (.intLit 0)) =
      .ok (.bool (decide (0 < value.toNat))) := by
    simp only [evalExpr?, tickValueGet, EvalResult.ofOption, bind, pure, EvalResult.bind, evalBinaryOp?]
    norm_cast
  rw [tickChangeExpr, evalExpr?, hp]
  by_cases hpos : 0 < value.toNat
  · have hne : (value.toNat : Int) ≠ 0 := by omega
    rw [decide_eq_true hpos]
    simp only [bind, EvalResult.bind]
    rw [evalExpr_binary_nonshort (by decide : BinaryOp.eq ≠ .and) (by decide : BinaryOp.eq ≠ .or),
      evalExpr_binary_nonshort (by decide : BinaryOp.mod ≠ .and) (by decide : BinaryOp.mod ≠ .or),
      tickRead, hv]
    simp only [evalExpr?, bind, pure, EvalResult.bind, evalBinaryOp?, hne, if_false,
      Reasoning.VyperDispatch.value_int_beq, tickChangeAllowed, hpos, true_and]
    norm_cast
  · simp only [bind, pure, EvalResult.bind,
      tickChangeAllowed, hpos, false_and, decide_false]

theorem tickAssign (evm : EVM.State) (id value : UInt256) :
    assignStorageRef? config (calldataFrame contract (tickArguments id value) ∅ evm) evm .storage
      { base := "marketState", steps := [.mindex (.var "id"), .field "tickSpacing"] }
      (.int (Int.ofNat value.toNat % packedUInt8Modulus)) =
      .ok (calldataFrame contract (tickArguments id value) ∅ evm, tickState evm id value) := by
  apply assignStorageRef_storage_scalar_value (layout := midnightStorageLayout)
    (er := { base := "marketState", steps := [.mindex
      (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE id)), .field "tickSpacing"] })
    (ty := .elem (.int packedUInt8Int)) (loc := packedUInt8Loc (solcMappingSlot ⟨1⟩ id + ⟨2⟩) 18)
  · simp [calldataFrame, tickArguments]
  · have hl : (EVM.Word.toBytesBE id).length = 32 := by
      simpa using word_toBytesBE_toByteArray_size id
    simp only [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, evalExpr?,
      tickIdGet, EvalResult.bind, EvalResult.ofOption, valueToKey?, wordBytes32Value, pure, bind,
      hl, show (abiBytes32Width : Nat) + 1 = 32 from rfl, ite_true]
  · rfl
  · rfl
  · change some (StorageAddr.leaf (packedUInt8Loc (solcMappingSlot ⟨1⟩
      (keyValueToWord (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE id))) + ⟨2⟩) 18)) = _
    simp only [abiBytes32Width, keyValueToWord_fixedBytes32]
  · exact Or.inl ⟨_, rfl⟩
  · exact storageLocStore_uint8_offset18_word evm _ value

theorem tickCast (evm : EVM.State) (id value : UInt256) :
    evalExpr? config (calldataFrame contract (tickArguments id value) ∅ evm) evm
      (.cast (.var "newTickSpacing") (.elem (.int packedUInt8Int))) =
      .ok (.int (Int.ofNat value.toNat % packedUInt8Modulus)) := by
  exact evalExpr_cast_int (by simp only [evalExpr?, tickValueGet, EvalResult.ofOption]; rfl)

theorem tickGuards (evm : EVM.State) (id value : UInt256) (hauth : roleAllowed evm ⟨12⟩)
    (hspace : marketTickSpacing (marketFeeWord evm id) ≠ ⟨0⟩) :
    ABlock fork config evm (calldataFrame contract (tickArguments id value) ∅ evm)
      (setMarketTickSpacingTransition.body.drop 3)
      (calldataFrame contract (tickArguments id value) ∅ evm)
      (setMarketTickSpacingTransition.body.drop 5) := by
  have hpos : 0 < (marketTickSpacing (marketFeeWord evm id)).toNat := by
    by_contra h
    exact hspace (uint256_toNat_eq_zero (by omega))
  refine ⟨fun h ↦ ExecBlock.consNormal (ExecStmt.requireTrue ?_)
    (ExecBlock.consNormal (ExecStmt.requireTrue ?_) h)⟩
  · simpa only [decide_eq_true hauth] using tickAuthEval evm id value
  · simpa only [decide_eq_true hpos] using tickEnabledEval evm id value

theorem tickAuthReverts (evm : EVM.State) (id value : UInt256)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < calldataLimit) (hauth : ¬ roleAllowed evm ⟨12⟩) :
    ExecTransitionBody fork config contract evm (tickArguments id value)
      setMarketTickSpacingTransition.body .reverted := by
  apply ExecFuncBody.execBlockRevert
  apply guardedBodyBlock hwv hhi
  apply ExecBlock.consRevert
  apply ExecStmt.requireFalse
  simpa only [decide_eq_false hauth] using tickAuthEval evm id value

theorem tickDisabledReverts (evm : EVM.State) (id value : UInt256)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < calldataLimit) (hauth : roleAllowed evm ⟨12⟩)
    (hspace : marketTickSpacing (marketFeeWord evm id) = ⟨0⟩) :
    ExecTransitionBody fork config contract evm (tickArguments id value)
      setMarketTickSpacingTransition.body .reverted := by
  apply ExecFuncBody.execBlockRevert
  apply guardedBodyBlock hwv hhi
  refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
  · simpa only [decide_eq_true hauth] using tickAuthEval evm id value
  apply ExecBlock.consRevert
  apply ExecStmt.requireFalse
  simpa only [hspace, show (⟨0⟩ : UInt256).toNat = 0 from rfl, Nat.lt_irrefl, decide_false]
    using tickEnabledEval evm id value

theorem tickChangeReverts (evm : EVM.State) (id value : UInt256)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < calldataLimit) (hauth : roleAllowed evm ⟨12⟩)
    (hspace : marketTickSpacing (marketFeeWord evm id) ≠ ⟨0⟩)
    (hchange : ¬ tickChangeAllowed evm id value) :
    ExecTransitionBody fork config contract evm (tickArguments id value)
      setMarketTickSpacingTransition.body .reverted := by
  apply ExecFuncBody.execBlockRevert
  apply guardedBodyBlock hwv hhi
  apply (tickGuards evm id value hauth hspace).run
  apply ExecBlock.consRevert
  apply ExecStmt.requireFalse
  simpa only [decide_eq_false hchange] using tickChangeEval evm id value

theorem tickReturns (evm : EVM.State) (id value : UInt256)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < calldataLimit) (hauth : roleAllowed evm ⟨12⟩)
    (hspace : marketTickSpacing (marketFeeWord evm id) ≠ ⟨0⟩)
    (hchange : tickChangeAllowed evm id value) (hperm : evm.executionEnv.perm = true) :
    ExecTransitionBody fork config contract evm (tickArguments id value)
      setMarketTickSpacingTransition.body
      (.returned (calldataFrame contract (tickArguments id value) ∅ evm) (tickState evm id value) none) := by
  apply ExecFuncBody.execBlockOK
  apply guardedBodyBlock hwv hhi
  apply (tickGuards evm id value hauth hspace).run
  refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
  · simpa only [decide_eq_true hchange] using tickChangeEval evm id value
  apply ExecBlock.consNormal (ExecStmt.assign (Or.inr hperm) (tickCast evm id value) (tickAssign evm id value))
  apply ExecBlock.consNormal (ExecStmt.emit (vals := [wordBytes32Value id, .int value.toNat]) ?_ ?_)
    ExecBlock.nil
  · simpa only [tickState, storageStore_executionEnv] using hperm
  · simp only [evalExprs?, evalExpr?, tickIdGet, tickValueGet, EvalResult.ofOption, bind, pure, EvalResult.bind]

theorem tickStatic (evm : EVM.State) (id value : UInt256)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < calldataLimit) (hauth : roleAllowed evm ⟨12⟩)
    (hspace : marketTickSpacing (marketFeeWord evm id) ≠ ⟨0⟩)
    (hchange : tickChangeAllowed evm id value) (hperm : evm.executionEnv.perm = false) :
    ExecTransitionBody fork config contract evm (tickArguments id value)
      setMarketTickSpacingTransition.body .staticViolation := by
  apply ExecFuncBody.execBlockStatic
  apply guardedBodyBlock hwv hhi
  apply (tickGuards evm id value hauth hspace).run
  refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
  · simpa only [decide_eq_true hchange] using tickChangeEval evm id value
  apply ExecBlock.consStatic
  exact ExecStmt.assignStatic (tickCast evm id value) (tickAssign evm id value) hperm

theorem tickTraceStatic {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024) (hperm : I.perm = false)
    (rd : RD fork midnightBytecode I g s0 ⟨1516⟩ (x0 :: x1 :: R) mem aw rdata σ k C) :
    RDstatic fork midnightBytecode g s0 := by
  let r0 := rd
  have r1 := r0.push2 (UInt256.ofNat 800) (by native_decide) (by evm_ov)
  have r2 := r1.dup1 (by native_decide) (by evm_ov)
  have r3 := RD.genMload r2 (by native_decide) (by evm_ov)
  have r4 := r3.dup4 (by native_decide) (by evm_ov)
  have r5 := r4.swap1 (by native_decide) (by evm_ov)
  have r6 := RD.genMstore r5 (by native_decide) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r9 := r8.swap1 (by native_decide) (by evm_ov)
  have r10 := r9.dup2 (by native_decide) (by evm_ov)
  have r11 := RD.genMstore r10 (by native_decide) (by evm_ov)
  have r12 := r11.swap1 (by native_decide) (by evm_ov)
  have r13 := RD.genMload r12 (by native_decide) (by evm_ov)
  have r14 := r13.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r15 := r14.swap1 (by native_decide) (by evm_ov)
  have r16 := r15.dup2 (by native_decide) (by evm_ov)
  have r17 := r16.swap1 (by native_decide) (by evm_ov)
  have r18 := RD.genKeccak256 r17 (by native_decide) (by evm_ov)
  have r19 := r18.push1 (UInt256.ofNat 2) (by native_decide) (by evm_ov)
  have r20 := r19.add (by native_decide) (by evm_ov)
  have r21 := r20.dup1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r22⟩ := RD.sload r21 (by native_decide) (by evm_ov)
  have r23 := r22.push1 (UInt256.ofNat 255) (by native_decide) (by evm_ov)
  have r24 := r23.push1 (UInt256.ofNat 144) (by native_decide) (by evm_ov)
  have r25 := r24.shl (by native_decide) (by evm_ov)
  have r26 := r25.not (by native_decide) (by evm_ov)
  have r27 := r26.and (by native_decide) (by evm_ov)
  have r28 := r27.push1 (UInt256.ofNat 144) (by native_decide) (by evm_ov)
  have r29 := r28.dup6 (by native_decide) (by evm_ov)
  have r30 := r29.swap1 (by native_decide) (by evm_ov)
  have r31 := r30.shl (by native_decide) (by evm_ov)
  have r32 := r31.push1 (UInt256.ofNat 255) (by native_decide) (by evm_ov)
  have r33 := r32.push1 (UInt256.ofNat 144) (by native_decide) (by evm_ov)
  have r34 := r33.shl (by native_decide) (by evm_ov)
  have r35 := r34.and (by native_decide) (by evm_ov)
  have r36 := r35.or (by native_decide) (by evm_ov)
  have r37 := r36.swap1 (by native_decide) (by evm_ov)
  exact r37.sstoreStatic hperm (by native_decide) (by evm_ov)

theorem tickTraceReturn {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {value id : UInt256} {R : List UInt256}
    (hm : EntryScratch mem) (hstack : R.length + 9 ≤ 1024)
    (hperm : I.perm = true) (hvalue : value.toNat < 2 ^ 8)
    (rd : RD fork midnightBytecode I g s0 ⟨1516⟩ (value :: id :: R) mem aw rdata σ k C) :
    RDret fork midnightBytecode g s0
      (sstoreAccountMap I.codeOwner σ (solcMappingSlot ⟨1⟩ id + ⟨2⟩)
        (setUint8Offset18Word (solcSlotWordAt (solcMappingSlot ⟨1⟩ id + ⟨2⟩) σ I) value))
      ByteArray.empty := by
  have hr := midnightBlocks.midnight_block_1516 hstack hperm rd
  have hm' := hm.hash id (UInt256.ofNat 1)
  simp only [hm.zero, show (⟨0⟩ : UInt256).toNat = 0 from rfl,
    show (UInt256.ofNat 32).toNat = 32 from rfl, wordAt0_fold, twoWordHash_fold,
    hm'.zero, hm.hashValue id (UInt256.ofNat 1), hm'.freePtr] at hr
  rw [u256_add_comm (UInt256.ofNat 2)] at hr
  simp only [show UInt256.ofNat 2 = (⟨2⟩ : UInt256) from rfl,
    show UInt256.ofNat 255 = (⟨255⟩ : UInt256) from rfl,
    show UInt256.ofNat 144 = (⟨144⟩ : UInt256) from rfl,
    setUint8Offset18Word_solc _ _ hvalue] at hr
  change RDret fork _ _ _ _ ((writeWord (twoWordHashMem id (UInt256.ofNat 1) mem) 832 value).readWithPadding
    (memLoad (UInt256.ofNat 800) (writeWord (twoWordHashMem id (UInt256.ofNat 1) mem) 832 value)).toNat
    (memLoad (UInt256.ofNat 800) (writeWord (twoWordHashMem id (UInt256.ofNat 1) mem) 832 value)).toNat) at hr
  simpa only [hm'.writeZero value, show (⟨0⟩ : UInt256).toNat = 0 from rfl,
    byteArray_readWithPadding_zero] using hr

theorem tickTraceMarket {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {value id : UInt256} {R : List UInt256}
    (hm : EntryScratch mem) (hstack : R.length + 6 ≤ 1024)
    (hspace : marketTickSpacing (solcSlotWordAt (solcMappingSlot ⟨1⟩ id + ⟨2⟩) σ I) ≠ ⟨0⟩)
    (rd : RD fork midnightBytecode I g s0 ⟨1469⟩ (value :: id :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD fork midnightBytecode I g s0 ⟨1502⟩ (value :: id :: R)
      (twoWordHashMem id (UInt256.ofNat 1) mem) aw' rdata σ k' C' := by
  have hm' := hm.hash id (UInt256.ofNat 1)
  obtain ⟨k', C', rd'⟩ := midnightBlocks.midnight_block_1469_fallthrough hstack (by
    simp only [hm.zero, show (⟨0⟩ : UInt256).toNat = 0 from rfl,
      show (UInt256.ofNat 32).toNat = 32 from rfl, wordAt0_fold, twoWordHash_fold,
      hm'.zero, hm.hashValue id (UInt256.ofNat 1)]
    exact isZero_eq_zero_of_ne hspace) rd
  simp only [midnightBlocks.midnight_block_1469_fallthrough_memory, hm.zero,
    show (⟨0⟩ : UInt256).toNat = 0 from rfl,
    show (UInt256.ofNat 32).toNat = 32 from rfl, wordAt0_fold, twoWordHash_fold] at rd'
  exact ⟨_, _, _, rd'⟩

theorem tickTraceMarketRevert {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {value id : UInt256} {R : List UInt256}
    (hm : EntryScratch mem) (hstack : R.length + 6 ≤ 1024)
    (hspace : marketTickSpacing (solcSlotWordAt (solcMappingSlot ⟨1⟩ id + ⟨2⟩) σ I) = ⟨0⟩)
    (rd : RD fork midnightBytecode I g s0 ⟨1469⟩ (value :: id :: R) mem aw rdata σ k C) :
    RDrev fork midnightBytecode g s0 := by
  have hm' := hm.hash id (UInt256.ofNat 1)
  obtain ⟨k', C', rd'⟩ := midnightBlocks.midnight_block_1469_taken hstack (by
    simp only [hm.zero, show (⟨0⟩ : UInt256).toNat = 0 from rfl,
      show (UInt256.ofNat 32).toNat = 32 from rfl, wordAt0_fold, twoWordHash_fold,
      hm'.zero, hm.hashValue id (UInt256.ofNat 1)]
    change UInt256.isZero (marketTickSpacing (solcSlotWordAt (solcMappingSlot ⟨1⟩ id + ⟨2⟩) σ I)) ≠ ⟨0⟩
    rw [hspace]; decide) (by jump_dest) rd
  exact midnightBlocks.midnight_block_1275 (by simp; omega) rd'

theorem tickTraceModulo {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {value id : UInt256} {R : List UInt256}
    (hm : EntryScratch mem) (hstack : R.length + 9 ≤ 1024) (hvalue : value ≠ ⟨0⟩)
    (rd : RD fork midnightBytecode I g s0 ⟨1502⟩ (value :: id :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD fork midnightBytecode I g s0 ⟨1510⟩
      (UInt256.isZero (UInt256.mod
        (marketTickSpacing (solcSlotWordAt (solcMappingSlot ⟨1⟩ id + ⟨2⟩) σ I)) value) :: value :: id :: R)
      (twoWordHashMem id (UInt256.ofNat 1) mem) aw' rdata σ k' C' := by
  have hr1 := midnightBlocks.midnight_block_1502_taken (by simp; omega)
    (by rw [isZero_eq_zero_of_ne hvalue]; decide) (by jump_dest) rd
  simp only [midnightBlocks.midnight_block_1502_taken_stack] at hr1
  obtain ⟨k2, C2, hr2⟩ := midnightBlocks.midnight_block_1631 (by simp; omega) (by jump_dest) hr1
  have hm' := hm.hash id (UInt256.ofNat 1)
  simp only [midnightBlocks.midnight_block_1631_stack, midnightBlocks.midnight_block_1631_memory,
    hm.zero, show (⟨0⟩ : UInt256).toNat = 0 from rfl,
    show (UInt256.ofNat 32).toNat = 32 from rfl, wordAt0_fold, twoWordHash_fold,
    hm'.zero, hm.hashValue id (UInt256.ofNat 1)] at hr2
  obtain ⟨k3, C3, hr3⟩ := midnightCheckedMod (by simp; omega) hvalue (by jump_dest) hr2
  have hr4 := midnightBlocks.midnight_block_1669 (by simp; omega) (by jump_dest) hr3
  exact ⟨_, _, _, hr4⟩

theorem tickTraceZero {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {id : UInt256} {R : List UInt256} (hstack : R.length + 5 ≤ 1024)
    (rd : RD fork midnightBytecode I g s0 ⟨1502⟩ (⟨0⟩ :: id :: R) mem aw rdata σ k C) :
    RDrev fork midnightBytecode g s0 := by
  have hr1 := midnightBlocks.midnight_block_1502_fallthrough (by simp; omega) (by decide) rd
  simp only [midnightBlocks.midnight_block_1502_fallthrough_stack] at hr1
  have hr2 := midnightBlocks.midnight_block_1510_taken (by simp; omega) (by decide) (by jump_dest) hr1
  exact midnightBlocks.midnight_block_1610
    (by simp [midnightBlocks.midnight_block_1510_taken_stack]; omega) hr2

/-- `setMarketTickSpacing(bytes32,uint256)`: the theorem `Correct.lean` routes selector 53 to. -/
theorem midnightSetMarketTickSpacingBody {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = midnightBytecode) (hsize : I.calldata.size < UInt256.size)
    (hfork : fork ≥ .osaka)
    (hgas : midnightGasBound g)
    (hsel : selIs I (midnightSelBytes 53)) :
    runtimeRefinementFor fork config contract σ σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (midnightSelBytes 53) rfl hsel
  have hd : dispatchMsg contract I.calldata = some setMarketTickSpacingTransition := by
    apply midnightDispatch_setMarketTickSpacing <;>
      first | exact hsel | exact selectorNe_of_selIs hsel (by decide +kernel)
  obtain ⟨k, C, rd⟩ := midnightReachSetMarketTickSpacingBody
    (σ := σ) (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g) hcode hsz hsize hsel
  by_cases hwv : I.weiValue = ⟨0⟩
  · have rd1 := midnightBlocks.midnight_block_1436_fallthrough (by simp) hwv rd
    have rd2 := midnightBlocks.midnight_block_1442 (by simp) (by jump_dest) rd1
    simp only [midnightBlocks.midnight_block_1442_stack] at rd2
    by_cases hhi : I.calldata.size < calldataLimit
    · by_cases h68 : 68 ≤ I.calldata.size
      · have rd3 := midnightBlocks.midnight_block_18819_fallthrough (by simp)
          (entrySizeCheck_ok (bytes := 64) h68 hhi hsize) rd2
        simp only [midnightBlocks.midnight_block_18819_fallthrough_stack] at rd3
        have rd4 := midnightBlocks.midnight_block_18832 (by simp) (by jump_dest) rd3
        simp only [midnightBlocks.midnight_block_18832_stack] at rd4
        change RD fork _ _ _ _ _ [calldataWord I.calldata 36, calldataWord I.calldata 4,
          solcSelectorWord I] midnightEntryMemory _ _ _ _ _ at rd4
        have hdec := midnightDecodePair_ok "id" "newTickSpacing"
          (by decide) (by decide) (by decide) (by decide) h68 hhi hsize
          (decodeBytes32Word (off := 4) (by omega)) (decodeUint256Word (off := 36) h68)
        by_cases hauth : solcSourceWord I = UInt256.land (solcSlotWordAt ⟨12⟩ σ I) solcAddrMask
        · obtain ⟨k5, C5, rd5⟩ := midnightBlocks.midnight_block_1450_fallthrough (by simp)
            (by rw [addressMask_computed]; exact u256_sub_eq_zero_iff_eq.mpr hauth) rd4
          by_cases hspace : marketTickSpacing
              (solcSlotWordAt (solcMappingSlot ⟨1⟩ (calldataWord I.calldata 4) + ⟨2⟩) σ I) = ⟨0⟩
          · have hr := tickTraceMarketRevert midnightEntryScratch (by simp) hspace rd5
            exact hr.reEquivExecutionRevert hcode hd hdec
              (tickDisabledReverts (initState σ σ₀ (Sat256.ofUInt256 g) A I)
                (calldataWord I.calldata 4) (calldataWord I.calldata 36) hwv hhi hauth hspace)
          · obtain ⟨aw6, k6, C6, rd6⟩ := tickTraceMarket midnightEntryScratch (by simp) hspace rd5
            have hm1 := midnightEntryScratch.hash (calldataWord I.calldata 4) (UInt256.ofNat 1)
            by_cases hzero : calldataWord I.calldata 36 = ⟨0⟩
            · rw [hzero] at rd6
              have hr := tickTraceZero (by simp) rd6
              have hchange : ¬ tickChangeAllowed (initState σ σ₀ (Sat256.ofUInt256 g) A I)
                  (calldataWord I.calldata 4) (calldataWord I.calldata 36) := by
                intro h
                have hp := h.1
                rw [hzero] at hp
                exact Nat.not_lt_zero _ hp
              exact hr.reEquivExecutionRevert hcode hd hdec
                (tickChangeReverts (initState σ σ₀ (Sat256.ofUInt256 g) A I)
                  (calldataWord I.calldata 4) (calldataWord I.calldata 36) hwv hhi hauth hspace hchange)
            · obtain ⟨aw7, k7, C7, rd7⟩ := tickTraceModulo hm1 (by simp) hzero rd6
              have hm2 := hm1.hash (calldataWord I.calldata 4) (UInt256.ofNat 1)
              by_cases hmod : UInt256.mod (marketTickSpacing
                  (solcSlotWordAt (solcMappingSlot ⟨1⟩ (calldataWord I.calldata 4) + ⟨2⟩) σ I))
                  (calldataWord I.calldata 36) = ⟨0⟩
              · have rd8 := midnightBlocks.midnight_block_1510_fallthrough (by simp)
                  (by rw [hmod]; decide) rd7
                simp only [midnightBlocks.midnight_block_1510_fallthrough_stack] at rd8
                have hpos : 0 < (calldataWord I.calldata 36).toNat := by
                  by_contra h
                  exact hzero (uint256_toNat_eq_zero (by omega))
                have hchange : tickChangeAllowed (initState σ σ₀ (Sat256.ofUInt256 g) A I)
                    (calldataWord I.calldata 4) (calldataWord I.calldata 36) :=
                  ⟨hpos, (mod_eq_zero_iff _ _ hzero).mp hmod⟩
                have holdpos : 0 < (marketTickSpacing
                    (solcSlotWordAt (solcMappingSlot ⟨1⟩ (calldataWord I.calldata 4) + ⟨2⟩) σ I)).toNat := by
                  by_contra h
                  exact hspace (uint256_toNat_eq_zero (by omega))
                have hcanon : (calldataWord I.calldata 36).toNat < 2 ^ 8 := by
                  have hle := Nat.le_of_dvd holdpos (Nat.dvd_of_mod_eq_zero hchange.2)
                  have holdlt := lowByte_bound (UInt256.shiftRight
                    (solcSlotWordAt (solcMappingSlot ⟨1⟩ (calldataWord I.calldata 4) + ⟨2⟩) σ I) ⟨144⟩)
                  change (marketTickSpacing
                    (solcSlotWordAt (solcMappingSlot ⟨1⟩ (calldataWord I.calldata 4) + ⟨2⟩) σ I)).toNat <
                    2 ^ 8 at holdlt
                  exact lt_of_le_of_lt hle holdlt
                by_cases hperm : I.perm = true
                · have hr := tickTraceReturn hm2 (by simp) hperm hcanon rd8
                  have hac := storageWordWrite_accounts (σ := σ)
                    (evm := initState σ σ₀ (Sat256.ofUInt256 g) A I) rfl
                    (solcMappingSlot ⟨1⟩ (calldataWord I.calldata 4) + ⟨2⟩)
                    (fun old ↦ setUint8Offset18Word old (calldataWord I.calldata 36))
                  exact hr.reEquivExecutionGen hcode hd hdec
                    (tickReturns (initState σ σ₀ (Sat256.ofUInt256 g) A I)
                      (calldataWord I.calldata 4) (calldataWord I.calldata 36)
                      hwv hhi hauth hspace hchange hperm) hac voidReturnEquiv
                · have hp : I.perm = false := by cases h : I.perm <;> simp_all
                  have hr := tickTraceStatic (by simp) hp rd8
                  exact hr.reEquivStaticHalt hcode hd hdec
                    (tickStatic (initState σ σ₀ (Sat256.ofUInt256 g) A I)
                      (calldataWord I.calldata 4) (calldataWord I.calldata 36)
                      hwv hhi hauth hspace hchange hp)
              · have rd8 := midnightBlocks.midnight_block_1510_taken (by simp)
                  (by rw [isZero_eq_zero_of_ne hmod]; decide) (by jump_dest) rd7
                have hr := midnightBlocks.midnight_block_1610
                  (by simp [midnightBlocks.midnight_block_1510_taken_stack]) rd8
                have hchange : ¬ tickChangeAllowed (initState σ σ₀ (Sat256.ofUInt256 g) A I)
                    (calldataWord I.calldata 4) (calldataWord I.calldata 36) := by
                  intro h
                  exact hmod ((mod_eq_zero_iff _ _ hzero).mpr h.2)
                exact hr.reEquivExecutionRevert hcode hd hdec
                  (tickChangeReverts (initState σ σ₀ (Sat256.ofUInt256 g) A I)
                    (calldataWord I.calldata 4) (calldataWord I.calldata 36) hwv hhi hauth hspace hchange)
        · obtain ⟨k5, C5, rd5⟩ := midnightBlocks.midnight_block_1450_taken (by simp)
            (by rw [addressMask_computed]; exact fun h ↦ hauth (u256_sub_eq_zero_iff_eq.mp h))
            (by jump_dest) rd4
          have hr := midnightBlocks.midnight_block_1675 (by simp) rd5
          exact hr.reEquivExecutionRevert hcode hd hdec
            (tickAuthReverts (initState σ σ₀ (Sat256.ofUInt256 g) A I)
              (calldataWord I.calldata 4) (calldataWord I.calldata 36) hwv hhi hauth)
      · have rd3 := midnightBlocks.midnight_block_18819_taken (by simp)
          (by
            have hc : UInt256.slt
                (UInt256.lnot (UInt256.ofNat 3) + UInt256.ofNat I.calldata.size)
                (UInt256.ofNat 64) = ⟨1⟩ :=
              entrySizeCheck_short hsz (Nat.lt_of_not_ge h68) (by decide) hsize
            rw [hc]; decide) (by jump_dest) rd2
        have hr := midnightBlocks.midnight_block_6350 (by simp
          [midnightBlocks.midnight_block_18819_taken_stack]) rd3
        exact hr.reEquivDecodingFailed hcode hd
          (midnightDecodePair_none_short "id" "newTickSpacing" (.bytes abiBytes32Width)
            (.int (.uint ⟨256, by decide⟩)) hsz (Nat.lt_of_not_ge h68) hsize)
    · have rd3 := midnightBlocks.midnight_block_18819_taken (by simp)
        (by
          have hc : UInt256.slt
              (UInt256.lnot (UInt256.ofNat 3) + UInt256.ofNat I.calldata.size)
              (UInt256.ofNat 64) = ⟨1⟩ :=
            entrySizeCheck_huge (Nat.le_of_not_lt hhi) hsize (by decide)
          rw [hc]; decide) (by jump_dest) rd2
      have hr := midnightBlocks.midnight_block_6350 (by simp
        [midnightBlocks.midnight_block_18819_taken_stack]) rd3
      exact hr.reEquivDecodingFailed hcode hd
        (midnightDecodePair_none_huge "id" "newTickSpacing" (.bytes abiBytes32Width)
          (.int (.uint ⟨256, by decide⟩)) (Nat.le_of_not_lt hhi) hsize)
  · have rd1 := midnightBlocks.midnight_block_1436_taken (by simp) hwv (by jump_dest) rd
    have hr := midnightBlocks.midnight_block_712 (by simp) rd1
    cases hdec : config.externalABI.decodeCalldata? (setMarketTickSpacingTransition.params.map Param.name)
        (transitionSignature setMarketTickSpacingTransition).paramTypes I.calldata with
    | none => exact hr.reEquivDecodingFailed hcode hd hdec
    | some args =>
      exact hr.reEquivExecutionRevert hcode hd hdec (bodyReverts_nonPayable hwv)


end Benchmarks.Midnight
