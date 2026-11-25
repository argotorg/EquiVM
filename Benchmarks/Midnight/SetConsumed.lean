import Benchmarks.Midnight.Dispatch
import Benchmarks.Midnight.AuthorizationTrace
import Benchmarks.Midnight.TripleDecode
import Benchmarks.Midnight.UintDecode
import Benchmarks.Midnight.PackedUint128

variable {fork : Ethereum.Fork}

/-!
# Midnight `setConsumed(bytes32,uint128,address)`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Stele body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 1696; reach lemma `midnightReachSetConsumedBody`.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

def setConsumedArguments (group amount user : UInt256) : Store :=
  (((∅ : Store).insert "group" (wordBytes32Value group)).insert "amount"
    (.int (Int.ofNat amount.toNat))).insert "onBehalf" (.address (AccountAddress.ofNat user.toNat))

def consumedSlot (group user : UInt256) : UInt256 :=
  solcMappingSlot (solcMappingSlot ⟨2⟩ user) group

def consumedStored (evm : EVM.State) (group user : UInt256) : UInt256 :=
  UInt256.land (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner (consumedSlot group user)) uint128Mask

def setConsumedState (evm : EVM.State) (group amount user : UInt256) : EVM.State :=
  Stele.EVM.storageStore evm evm.executionEnv.codeOwner (consumedSlot group user)
    (setUint128LowWord (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner (consumedSlot group user)) amount)

def consumedRef : StorageRef :=
  { base := "consumed", steps := [.mindex (.var "onBehalf"), .mindex (.var "group")] }

theorem setConsumedGroupGet (evm : EVM.State) (group amount user : UInt256) :
    (calldataFrame contract (setConsumedArguments group amount user) ∅ evm).locals.get?
      "group" = some (wordBytes32Value group) := by
  change (((((∅ : Store).insert "group" _).insert "amount" _).insert "onBehalf" _).insert
    "__calldata" _).get? "group" = _
  rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide), store_get_ne _ _ (by decide), store_get_self]

theorem setConsumedAmountGet (evm : EVM.State) (group amount user : UInt256) :
    (calldataFrame contract (setConsumedArguments group amount user) ∅ evm).locals.get?
      "amount" = some (.int (Int.ofNat amount.toNat)) := by
  change (((((∅ : Store).insert "group" _).insert "amount" _).insert "onBehalf" _).insert
    "__calldata" _).get? "amount" = _
  rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide), store_get_self]

theorem setConsumedUserGet (evm : EVM.State) (group amount user : UInt256) :
    (calldataFrame contract (setConsumedArguments group amount user) ∅ evm).locals.get?
      "onBehalf" = some (.address (AccountAddress.ofNat user.toNat)) := by
  change (((((∅ : Store).insert "group" _).insert "amount" _).insert "onBehalf" _).insert
    "__calldata" _).get? "onBehalf" = _
  rw [store_get_ne _ _ (by decide), store_get_self]

theorem setConsumedGuardEval (evm : EVM.State) (group amount user : UInt256)
    (hc : user.toNat < EVM.addressModulus) :
    evalExpr? config (calldataFrame contract (setConsumedArguments group amount user) ∅ evm)
      evm onBehalfGuard = .ok (.bool (decide (onBehalfAllowed evm user))) := by
  exact evalOnBehalfGuard evm user hc rfl
    (by simp [calldataFrame, setConsumedArguments]) (setConsumedUserGet evm group amount user)

theorem setConsumedResolve (evm : EVM.State) (group amount user : UInt256) :
    evalStorageRef config (calldataFrame contract (setConsumedArguments group amount user) ∅ evm)
      evm consumedRef = .ok { base := "consumed", steps :=
        [.mindex (.address (AccountAddress.ofNat user.toNat)),
         .mindex (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE group))] } := by
  simp only [consumedRef, evalStorageRef, evalStorageRefSteps, evalStorageRefStep, evalExpr?,
    setConsumedUserGet, setConsumedGroupGet, EvalResult.ofOption, EvalResult.bind,
    valueToKey?, wordBytes32Value, pure, bind]
  have hlen : (EVM.Word.toBytesBE group).length = 32 := by
    simpa using word_toBytesBE_toByteArray_size group
  simp [hlen, abiBytes32Width]

theorem setConsumedLayout (group user : UInt256) (hc : user.toNat < EVM.addressModulus) :
    midnightStorageLayout { base := "consumed", steps :=
      [.mindex (.address (AccountAddress.ofNat user.toNat)),
       .mindex (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE group))] } =
      some (.leaf (uint128LowLoc (consumedSlot group user))) := by
  change some (StorageAddr.leaf {
      slot := solcMappingSlot
        (solcMappingSlot ⟨2⟩ (keyValueToWord (.address (AccountAddress.ofNat user.toNat))))
        (keyValueToWord (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE group))),
      offset := 0, size := 16, hbound := by decide, type := .int packedUInt128Int }) = _
  simp only [abiBytes32Width, keyValueToWord_fixedBytes32, keyValueToWord_address_of_canonical user hc]
  rfl

theorem setConsumedRead (evm : EVM.State) (group amount user : UInt256)
    (hc : user.toNat < EVM.addressModulus) :
    evalExpr? config (calldataFrame contract (setConsumedArguments group amount user) ∅ evm)
      evm (.storage consumedRef) = .ok (.int (Int.ofNat (consumedStored evm group user).toNat)) := by
  apply evalExpr_storage_scalar_value (loc := uint128LowLoc (consumedSlot group user))
    (er := { base := "consumed", steps := [.mindex (.address (AccountAddress.ofNat user.toNat)),
      .mindex (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE group))] }) (t := .int packedUInt128Int)
  · simp [calldataFrame, setConsumedArguments, consumedRef]
  · exact setConsumedResolve evm group amount user
  · rfl
  · rfl
  · exact setConsumedLayout group user hc
  · exact storageLocLoad_uint_offset0 evm _ 16 ⟨128, by decide⟩ (by decide) (by decide)

theorem setConsumedBoundEval (evm : EVM.State) (group amount user : UInt256)
    (hc : user.toNat < EVM.addressModulus) :
    evalExpr? config (calldataFrame contract (setConsumedArguments group amount user) ∅ evm)
      evm (.binary .ge (.var "amount") (.storage consumedRef)) =
      .ok (.bool (decide ((consumedStored evm group user).toNat ≤ amount.toNat))) := by
  rw [evalExpr_binary_nonshort (by decide : BinaryOp.ge ≠ .and) (by decide : BinaryOp.ge ≠ .or),
    setConsumedRead evm group amount user hc]
  simp only [evalExpr?, setConsumedAmountGet, EvalResult.ofOption, EvalResult.bind, bind, pure,
    evalBinaryOp?, Int.ofNat_eq_natCast]
  norm_cast

theorem setConsumedAssign (evm : EVM.State) (group amount user : UInt256)
    (hc : user.toNat < EVM.addressModulus) :
    assignStorageRef? config (calldataFrame contract (setConsumedArguments group amount user) ∅ evm)
      evm .storage consumedRef (.int (Int.ofNat amount.toNat)) =
      .ok (calldataFrame contract (setConsumedArguments group amount user) ∅ evm,
        setConsumedState evm group amount user) := by
  apply assignStorageRef_storage_scalar_value
    (er := { base := "consumed", steps := [.mindex (.address (AccountAddress.ofNat user.toNat)),
      .mindex (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE group))] })
    (ty := .elem (.int packedUInt128Int)) (loc := uint128LowLoc (consumedSlot group user))
    (layout := midnightStorageLayout)
  · simp [calldataFrame, setConsumedArguments, consumedRef]
  · exact setConsumedResolve evm group amount user
  · rfl
  · rfl
  · exact setConsumedLayout group user hc
  · exact Or.inl ⟨_, rfl⟩
  · exact storageLocStore_uint128_low_word evm _ amount

theorem setConsumedAuthReverts (evm : EVM.State) (group amount user : UInt256)
    (hc : user.toNat < EVM.addressModulus)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩) (hhi : evm.executionEnv.calldata.size < calldataLimit)
    (hauth : ¬ onBehalfAllowed evm user) :
    ExecTransitionBody fork config contract evm (setConsumedArguments group amount user)
      setConsumedTransition.body .reverted := by
  apply ExecFuncBody.execBlockRevert
  apply guardedBodyBlock hwv hhi
  apply ExecBlock.consRevert
  apply ExecStmt.requireFalse
  simpa only [decide_eq_false hauth] using setConsumedGuardEval evm group amount user hc

theorem setConsumedBoundReverts (evm : EVM.State) (group amount user : UInt256)
    (hc : user.toNat < EVM.addressModulus)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩) (hhi : evm.executionEnv.calldata.size < calldataLimit)
    (hauth : onBehalfAllowed evm user) (hbound : ¬ (consumedStored evm group user).toNat ≤ amount.toNat) :
    ExecTransitionBody fork config contract evm (setConsumedArguments group amount user)
      setConsumedTransition.body .reverted := by
  apply ExecFuncBody.execBlockRevert
  apply guardedBodyBlock hwv hhi
  refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
  · simpa only [decide_eq_true hauth] using setConsumedGuardEval evm group amount user hc
  apply ExecBlock.consRevert
  apply ExecStmt.requireFalse
  simpa only [decide_eq_false hbound] using setConsumedBoundEval evm group amount user hc

theorem setConsumedReturns (evm : EVM.State) (group amount user : UInt256)
    (hc : user.toNat < EVM.addressModulus)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩) (hhi : evm.executionEnv.calldata.size < calldataLimit)
    (hauth : onBehalfAllowed evm user) (hbound : (consumedStored evm group user).toNat ≤ amount.toNat)
    (hperm : evm.executionEnv.perm = true) :
    ExecTransitionBody fork config contract evm (setConsumedArguments group amount user)
      setConsumedTransition.body
      (.returned (calldataFrame contract (setConsumedArguments group amount user) ∅ evm)
        (setConsumedState evm group amount user) none) := by
  apply ExecFuncBody.execBlockOK
  apply guardedBodyBlock hwv hhi
  refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
  · simpa only [decide_eq_true hauth] using setConsumedGuardEval evm group amount user hc
  refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
  · simpa only [decide_eq_true hbound] using setConsumedBoundEval evm group amount user hc
  apply ExecBlock.consNormal (ExecStmt.assign (Or.inr hperm)
    (by simp only [evalExpr?, setConsumedAmountGet, EvalResult.ofOption])
    (setConsumedAssign evm group amount user hc))
  apply ExecBlock.consNormal (ExecStmt.emit (vals := [.address evm.executionEnv.source,
    wordBytes32Value group, .int (Int.ofNat amount.toNat),
    .address (AccountAddress.ofNat user.toNat)]) ?_ ?_) ExecBlock.nil
  · simpa only [setConsumedState, storageStore_executionEnv] using hperm
  · simp only [evalExprs?, evalExpr?, envValue, setConsumedState, storageStore_executionEnv,
      setConsumedGroupGet, setConsumedAmountGet, setConsumedUserGet,
      EvalResult.ofOption, EvalResult.bind, pure, bind]

theorem setConsumedStatic (evm : EVM.State) (group amount user : UInt256)
    (hc : user.toNat < EVM.addressModulus)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩) (hhi : evm.executionEnv.calldata.size < calldataLimit)
    (hauth : onBehalfAllowed evm user) (hbound : (consumedStored evm group user).toNat ≤ amount.toNat)
    (hperm : evm.executionEnv.perm = false) :
    ExecTransitionBody fork config contract evm (setConsumedArguments group amount user)
      setConsumedTransition.body .staticViolation := by
  apply ExecFuncBody.execBlockStatic
  apply guardedBodyBlock hwv hhi
  refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
  · simpa only [decide_eq_true hauth] using setConsumedGuardEval evm group amount user hc
  refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
  · simpa only [decide_eq_true hbound] using setConsumedBoundEval evm group amount user hc
  apply ExecBlock.consStatic
  exact ExecStmt.assignStatic
    (by simp only [evalExpr?, setConsumedAmountGet, EvalResult.ofOption])
    (setConsumedAssign evm group amount user hc) hperm

def consumedHashMemory (mem : ByteArray) (group user : UInt256) : ByteArray :=
  twoWordHashMem group (solcMappingSlot (UInt256.ofNat 2) user)
    (twoWordHashMem user (UInt256.ofNat 2) mem)

theorem consumedHashMemory_scratch {mem : ByteArray} (hm : EntryScratch mem) (group user : UInt256) :
    EntryScratch (consumedHashMemory mem group user) :=
  (hm.hash user (UInt256.ofNat 2)).hash group (solcMappingSlot (UInt256.ofNat 2) user)

theorem setConsumedTraceBound {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {group amount user : UInt256} {R : List UInt256}
    (hm : EntryScratch mem) (hstack : R.length + 6 ≤ 1024)
    (hbound : (UInt256.land (solcSlotWordAt (consumedSlot group user) σ I) uint128Mask).toNat ≤ amount.toNat)
    (rd : RD fork midnightBytecode I g s0 ⟨1772⟩ (amount :: group :: user :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD fork midnightBytecode I g s0 ⟨1822⟩ (amount :: group :: user :: R)
      (consumedHashMemory mem group user) aw' rdata σ k' C' := by
  have hm1 := hm.hash user (UInt256.ofNat 2)
  have hm2 := hm1.hash group (solcMappingSlot (UInt256.ofNat 2) user)
  obtain ⟨k1, C1, rd1⟩ := midnightBlocks.midnight_block_1772_fallthrough hstack (by
    simp only [hm.zero, show (⟨0⟩ : UInt256).toNat = 0 from rfl,
      show (UInt256.ofNat 32).toNat = 32 from rfl, wordAt0_fold, twoWordHash_fold,
      hm1.zero, hm.hashValue user (UInt256.ofNat 2), hm2.zero,
      hm1.hashValue group (solcMappingSlot (UInt256.ofNat 2) user), uint128Mask_computed]
    exact ult_zero hbound) rd
  simp only [midnightBlocks.midnight_block_1772_fallthrough_memory,
    hm.zero, show (⟨0⟩ : UInt256).toNat = 0 from rfl,
    show (UInt256.ofNat 32).toNat = 32 from rfl, wordAt0_fold, twoWordHash_fold,
    hm1.zero, hm.hashValue user (UInt256.ofNat 2)] at rd1
  exact ⟨_, _, _, rd1⟩

theorem setConsumedTraceBoundRevert {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {group amount user : UInt256} {R : List UInt256}
    (hm : EntryScratch mem) (hstack : R.length + 6 ≤ 1024)
    (hbound : ¬ (UInt256.land (solcSlotWordAt (consumedSlot group user) σ I) uint128Mask).toNat ≤ amount.toNat)
    (rd : RD fork midnightBytecode I g s0 ⟨1772⟩ (amount :: group :: user :: R) mem aw rdata σ k C) :
    RDrev fork midnightBytecode g s0 := by
  have hm1 := hm.hash user (UInt256.ofNat 2)
  have hm2 := hm1.hash group (solcMappingSlot (UInt256.ofNat 2) user)
  obtain ⟨k1, C1, rd1⟩ := midnightBlocks.midnight_block_1772_taken hstack (by
    simp only [hm.zero, show (⟨0⟩ : UInt256).toNat = 0 from rfl,
      show (UInt256.ofNat 32).toNat = 32 from rfl, wordAt0_fold, twoWordHash_fold,
      hm1.zero, hm.hashValue user (UInt256.ofNat 2), hm2.zero,
      hm1.hashValue group (solcMappingSlot (UInt256.ofNat 2) user), uint128Mask_computed]
    change UInt256.lt amount
      (UInt256.land (solcSlotWordAt (consumedSlot group user) σ I) uint128Mask) ≠ ⟨0⟩
    rw [ult_one (Nat.lt_of_not_ge hbound)]; decide) (by jump_dest) rd
  exact midnightBlocks.midnight_block_1922 (by simp; omega) rd1

theorem setConsumedTraceReturn {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {group amount user : UInt256} {R : List UInt256}
    (hm : EntryScratch mem) (hstack : R.length + 8 ≤ 1024)
    (hperm : I.perm = true) (hamount : amount.toNat < 2 ^ 128)
    (rd : RD fork midnightBytecode I g s0 ⟨1822⟩ (amount :: group :: user :: R) mem aw rdata σ k C) :
    RDret fork midnightBytecode g s0
      (sstoreAccountMap I.codeOwner σ (consumedSlot group user)
        (setUint128LowWord (solcSlotWordAt (consumedSlot group user) σ I) amount)) ByteArray.empty := by
  have hr := midnightBlocks.midnight_block_1822 hstack hperm rd
  have hm1 := hm.hash user (UInt256.ofNat 2)
  have hm2 := hm1.hash group (solcMappingSlot (UInt256.ofNat 2) user)
  simp only [hm.zero, show (⟨0⟩ : UInt256).toNat = 0 from rfl,
    show (UInt256.ofNat 32).toNat = 32 from rfl, wordAt0_fold, twoWordHash_fold,
    hm1.zero, hm.hashValue user (UInt256.ofNat 2), hm2.zero,
    hm1.hashValue group (solcMappingSlot (UInt256.ofNat 2) user), uint128Mask_computed,
    hm2.freePtr] at hr
  change RDret fork _ _ _ _ ((writeWord (consumedHashMemory mem group user) 832 amount).readWithPadding
    (memLoad (UInt256.ofNat 800) (writeWord (consumedHashMemory mem group user) 832 amount)).toNat
    (memLoad (UInt256.ofNat 800) (writeWord (consumedHashMemory mem group user) 832 amount)).toNat) at hr
  simp only [consumedHashMemory, hm2.writeZero amount, show (⟨0⟩ : UInt256).toNat = 0 from rfl,
    byteArray_readWithPadding_zero] at hr
  simpa only [setUint128LowWord, uint128Mask_clean hamount, u256_lor_comm] using hr

theorem setConsumedTraceStatic {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {group amount user : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024) (hperm : I.perm = false)
    (rd : RD fork midnightBytecode I g s0 ⟨1822⟩ (amount :: group :: user :: R)
      mem aw rdata σ k C) : RDstatic fork midnightBytecode g s0 := by
  let r0 := rd
  have r1 := r0.dup3 (by native_decide) (by evm_ov)
  have r2 := r1.push2 (UInt256.ofNat 800) (by native_decide) (by evm_ov)
  have r3 := RD.genMload r2 (by native_decide) (by evm_ov)
  have r4 := RD.genMstore r3 (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 2) (by native_decide) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r7 := RD.genMstore r6 (by native_decide) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r9 := r8.push2 (UInt256.ofNat 800) (by native_decide) (by evm_ov)
  have r10 := RD.genMload r9 (by native_decide) (by evm_ov)
  have r11 := RD.genKeccak256 r10 (by native_decide) (by evm_ov)
  have r12 := r11.dup3 (by native_decide) (by evm_ov)
  have r13 := r12.push2 (UInt256.ofNat 800) (by native_decide) (by evm_ov)
  have r14 := RD.genMload r13 (by native_decide) (by evm_ov)
  have r15 := RD.genMstore r14 (by native_decide) (by evm_ov)
  have r16 := r15.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r17 := RD.genMstore r16 (by native_decide) (by evm_ov)
  have r18 := r17.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r19 := r18.push2 (UInt256.ofNat 800) (by native_decide) (by evm_ov)
  have r20 := RD.genMload r19 (by native_decide) (by evm_ov)
  have r21 := RD.genKeccak256 r20 (by native_decide) (by evm_ov)
  have r22 := r21.dup2 (by native_decide) (by evm_ov)
  have r23 := r22.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r24 := r23.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r25 := r24.push1 (UInt256.ofNat 128) (by native_decide) (by evm_ov)
  have r26 := r25.shl (by native_decide) (by evm_ov)
  have r27 := r26.sub (by native_decide) (by evm_ov)
  have r28 := r27.not (by native_decide) (by evm_ov)
  have r29 := r28.dup3 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r30⟩ := RD.sload r29 (by native_decide) (by evm_ov)
  have r31 := r30.and (by native_decide) (by evm_ov)
  have r32 := r31.or (by native_decide) (by evm_ov)
  have r33 := r32.swap1 (by native_decide) (by evm_ov)
  exact r33.sstoreStatic hperm (by native_decide) (by evm_ov)

/-- `setConsumed(bytes32,uint128,address)`: the theorem `Correct.lean` routes selector 52 to. -/
theorem midnightSetConsumedBody {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = midnightBytecode) (hsize : I.calldata.size < UInt256.size)
    (hfork : fork ≥ .osaka)
    (hgas : midnightGasBound g)
    (hsel : selIs I (midnightSelBytes 52)) :
    runtimeRefinementFor fork config contract σ σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (midnightSelBytes 52) rfl hsel
  have hd : dispatchMsg contract I.calldata = some setConsumedTransition := by
    apply midnightDispatch_setConsumed <;>
      first | exact hsel | exact selectorNe_of_selIs hsel (by decide +kernel)
  obtain ⟨k, C, rd⟩ := midnightReachSetConsumedBody
    (σ := σ) (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g) hcode hsz hsize hsel
  by_cases hwv : I.weiValue = ⟨0⟩
  · have rd1 := midnightBlocks.midnight_block_1696_fallthrough (by simp) hwv rd
    by_cases hhi : I.calldata.size < calldataLimit
    · by_cases h100 : 100 ≤ I.calldata.size
      · have rd2 := midnightBlocks.midnight_block_1702_fallthrough (by simp)
          (entrySizeCheck_ok (bytes := 96) h100 hhi hsize) rd1
        change RD fork _ _ _ _ _ [solcSelectorWord I] midnightEntryMemory _ _ _ _ _ at rd2
        by_cases hamount : (calldataWord I.calldata 36).toNat < 2 ^ 128
        · have rd3 := midnightBlocks.midnight_block_1714_fallthrough (by simp)
            (by rw [uint128Mask_computed]
                exact u256_sub_eq_zero_iff_eq.mpr (uint128Mask_clean hamount).symm) rd2
          simp only [midnightBlocks.midnight_block_1714_fallthrough_stack, uint128Mask_computed] at rd3
          change RD fork _ _ _ _ _ [calldataWord I.calldata 4,
            UInt256.land (calldataWord I.calldata 36) uint128Mask, solcSelectorWord I] _ _ _ _ _ _ at rd3
          rw [uint128Mask_clean hamount] at rd3
          have rd4 := midnightBlocks.midnight_block_1739 (by simp) (by jump_dest) rd3
          simp only [midnightBlocks.midnight_block_1739_stack, addressMask_computed] at rd4
          by_cases hc : (calldataWord I.calldata 68).toNat < EVM.addressModulus
          · obtain ⟨k5, C5, rd5⟩ := midnightAddress68_ok (by simp) (by jump_dest) hc rd4
            have hdec := midnightDecodeTriple_ok "group" "amount" "onBehalf"
              (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h100 hhi hsize
              (decodeBytes32Word (off := 4) (by omega))
              (decodeUintWord ⟨128, by decide⟩ (off := 36) (by omega) hamount) (decodeAddressWord h100 hc)
            obtain ⟨check, mem6, aw6, k6, C6, hm6, hcheck, rd6⟩ :=
              onBehalfTraceGuard true midnightEntryScratch (by simp) hc rd5
            by_cases hauth : onBehalfAllowed (initState σ σ₀ (Sat256.ofUInt256 g) A I)
                (calldataWord I.calldata 68)
            · have rd7 := midnightBlocks.midnight_block_1766_fallthrough (by simp)
                (isZero_eq_zero_of_ne (hcheck.mpr hauth)) rd6
              simp only [midnightBlocks.midnight_block_1766_fallthrough_stack] at rd7
              by_cases hbound : (consumedStored (initState σ σ₀ (Sat256.ofUInt256 g) A I)
                  (calldataWord I.calldata 4) (calldataWord I.calldata 68)).toNat ≤
                  (calldataWord I.calldata 36).toNat
              · obtain ⟨aw8, k8, C8, rd8⟩ := setConsumedTraceBound hm6 (by simp) hbound rd7
                have hm8 := consumedHashMemory_scratch hm6 (calldataWord I.calldata 4) (calldataWord I.calldata 68)
                by_cases hperm : I.perm = true
                · have hr := setConsumedTraceReturn hm8 (by simp) hperm hamount rd8
                  have hac := storageWordWrite_accounts (σ := σ)
                    (evm := initState σ σ₀ (Sat256.ofUInt256 g) A I) rfl
                    (consumedSlot (calldataWord I.calldata 4) (calldataWord I.calldata 68))
                    (fun old ↦ setUint128LowWord old (calldataWord I.calldata 36))
                  exact hr.reEquivExecutionGen hcode hd hdec
                    (setConsumedReturns (initState σ σ₀ (Sat256.ofUInt256 g) A I)
                      (calldataWord I.calldata 4) (calldataWord I.calldata 36)
                      (calldataWord I.calldata 68) hc hwv hhi hauth hbound hperm) hac voidReturnEquiv
                · have hp : I.perm = false := by
                    cases h : I.perm
                    · rfl
                    · exact False.elim (hperm h)
                  have hr := setConsumedTraceStatic (by simp) hp rd8
                  exact hr.reEquivStaticHalt hcode hd hdec
                    (setConsumedStatic (initState σ σ₀ (Sat256.ofUInt256 g) A I)
                      (calldataWord I.calldata 4) (calldataWord I.calldata 36)
                      (calldataWord I.calldata 68) hc hwv hhi hauth hbound hp)
              · have hr := setConsumedTraceBoundRevert hm6 (by simp) hbound rd7
                exact hr.reEquivExecutionRevert hcode hd hdec
                  (setConsumedBoundReverts (initState σ σ₀ (Sat256.ofUInt256 g) A I)
                    (calldataWord I.calldata 4) (calldataWord I.calldata 36)
                    (calldataWord I.calldata 68) hc hwv hhi hauth hbound)
            · have hz : check = ⟨0⟩ := by
                by_contra hn
                exact hauth (hcheck.mp hn)
              have rd7 := midnightBlocks.midnight_block_1766_taken (by simp)
                (by rw [hz]; decide) (by jump_dest) rd6
              have hr := midnightBlocks.midnight_block_1943
                (by simp [midnightBlocks.midnight_block_1766_taken_stack]) rd7
              exact hr.reEquivExecutionRevert hcode hd hdec
                (setConsumedAuthReverts (initState σ σ₀ (Sat256.ofUInt256 g) A I)
                  (calldataWord I.calldata 4) (calldataWord I.calldata 36)
                  (calldataWord I.calldata 68) hc hwv hhi hauth)
          · have hr := midnightAddress68_revert (by simp) hc rd4
            exact hr.reEquivDecodingFailed hcode hd
              (midnightDecodeTriple_none_right "group" "amount" "onBehalf"
                (.bytes abiBytes32Width) (.int packedUInt128Int) .address h100 hhi hsize
                (decodeBytes32Word (off := 4) (by omega))
                (decodeUintWord ⟨128, by decide⟩ (off := 36) (by omega) hamount) (decodeAddressWord_none h100 hc))
        · have rd3 := midnightBlocks.midnight_block_1714_taken (by simp)
            (by
              rw [uint128Mask_computed]
              intro he
              apply hamount
              have hclean := u256_sub_eq_zero_iff_eq.mp he
              change calldataWord I.calldata 36 = UInt256.land (calldataWord I.calldata 36) uint128Mask at hclean
              have hm := u256LandMaskToNatLtOfToNat (calldataWord I.calldata 36) uint128Mask
                (by decide : uint128Mask.toNat = 2 ^ 128 - 1)
              rw [← hclean] at hm
              exact hm) (by jump_dest) rd2
          have hr := midnightBlocks.midnight_block_712
            (by simp [midnightBlocks.midnight_block_1714_taken_stack]) rd3
          exact hr.reEquivDecodingFailed hcode hd
            (midnightDecodeTriple_none_middle "group" "amount" "onBehalf"
              (.bytes abiBytes32Width) (.int packedUInt128Int) .address h100 hhi hsize
              (decodeBytes32Word (off := 4) (by omega)) (decodeUintWord_none ⟨128, by decide⟩ (by omega) hamount))
      · have rd2 := midnightBlocks.midnight_block_1702_taken (by simp)
          (by
            have hc : UInt256.slt
                (UInt256.lnot (UInt256.ofNat 3) + UInt256.ofNat I.calldata.size)
                (UInt256.ofNat 96) = ⟨1⟩ :=
              entrySizeCheck_short hsz (Nat.lt_of_not_ge h100) (by decide) hsize
            rw [hc]; decide) (by jump_dest) rd1
        have hr := midnightBlocks.midnight_block_712 (by simp) rd2
        exact hr.reEquivDecodingFailed hcode hd
          (midnightDecodeTriple_none_short "group" "amount" "onBehalf"
            (.bytes abiBytes32Width) (.int packedUInt128Int) .address hsz (Nat.lt_of_not_ge h100) hsize)
    · have rd2 := midnightBlocks.midnight_block_1702_taken (by simp)
        (by
          have hc : UInt256.slt
              (UInt256.lnot (UInt256.ofNat 3) + UInt256.ofNat I.calldata.size)
              (UInt256.ofNat 96) = ⟨1⟩ :=
            entrySizeCheck_huge (Nat.le_of_not_lt hhi) hsize (by decide)
          rw [hc]; decide) (by jump_dest) rd1
      have hr := midnightBlocks.midnight_block_712 (by simp) rd2
      exact hr.reEquivDecodingFailed hcode hd
        (midnightDecodeTriple_none_huge "group" "amount" "onBehalf"
          (.bytes abiBytes32Width) (.int packedUInt128Int) .address (Nat.le_of_not_lt hhi) hsize)
  · have rd1 := midnightBlocks.midnight_block_1696_taken (by simp) hwv (by jump_dest) rd
    have hr := midnightBlocks.midnight_block_712 (by simp) rd1
    cases hdec : config.externalABI.decodeCalldata? (setConsumedTransition.params.map Param.name)
        (transitionSignature setConsumedTransition).paramTypes I.calldata with
    | none => exact hr.reEquivDecodingFailed hcode hd hdec
    | some args => exact hr.reEquivExecutionRevert hcode hd hdec (bodyReverts_nonPayable hwv)

end Benchmarks.Midnight
