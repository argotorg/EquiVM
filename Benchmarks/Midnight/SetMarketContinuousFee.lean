import Benchmarks.Midnight.Dispatch
import Benchmarks.Midnight.ContinuousSource
import Benchmarks.Midnight.SettlementFields
import Benchmarks.Midnight.PackedFee
import Benchmarks.Midnight.PairDecode
import Benchmarks.Midnight.AddressDecode
import Benchmarks.Midnight.MappingMemory

variable {fork : Ethereum.Fork}

/-!
# Midnight `setMarketContinuousFee(bytes32,uint256)`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Stele body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 16758; reach lemma `midnightReachSetMarketContinuousFeeBody`.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

def marketFeeArguments (id value : UInt256) : Store :=
  ((∅ : Store).insert "id" (wordBytes32Value id)).insert "newContinuousFee" (.int value.toNat)

def marketFeeFrame (evm : EVM.State) (id value : UInt256) : Frame :=
  let frame := calldataFrame contract (marketFeeArguments id value) ∅ evm
  { frame with locals := frame.locals.insert "_marketState" (.storageRef (marketStateRef id) marketStateType) }

def marketFeeState (evm : EVM.State) (id value : UInt256) : EVM.State :=
  let slot := solcMappingSlot ⟨1⟩ id + ⟨2⟩
  Stele.EVM.storageStore evm evm.executionEnv.codeOwner slot
    (setUint32Offset14Word (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner slot) value)

theorem marketFeeBindAlias (evm : EVM.State) (id value : UInt256) :
    ABlock fork config evm (calldataFrame contract (marketFeeArguments id value) ∅ evm)
      (setMarketContinuousFeeTransition.body.drop 3) (marketFeeFrame evm id value)
      (setMarketContinuousFeeTransition.body.drop 4) := by
  refine ⟨fun h ↦ ExecBlock.consNormal (ExecStmt.letStorage ?_) h⟩
  apply resolveBytes32Mapping
  · simp [calldataFrame, marketFeeArguments]
  · change (((marketFeeArguments id value).insert "__calldata"
      (.bytes evm.executionEnv.calldata)).get? "id") = _
    rw [store_get_ne _ _ (by decide), marketFeeArguments, store_get_ne _ _ (by decide), store_get_self]
  · rfl

theorem marketFeeValueGet (evm : EVM.State) (id value : UInt256) :
    (marketFeeFrame evm id value).locals.get? "newContinuousFee" = some (.int value.toNat) := by
  change ((((marketFeeArguments id value).insert "__calldata" (.bytes evm.executionEnv.calldata)).insert
    "_marketState" (.storageRef (marketStateRef id) marketStateType)).get? "newContinuousFee") = _
  rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide)]
  exact store_get_self _ _ _

theorem marketFeeIdGet (evm : EVM.State) (id value : UInt256) :
    (marketFeeFrame evm id value).locals.get? "id" = some (wordBytes32Value id) := by
  change ((((marketFeeArguments id value).insert "__calldata" (.bytes evm.executionEnv.calldata)).insert
    "_marketState" (.storageRef (marketStateRef id) marketStateType)).get? "id") = _
  rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide), marketFeeArguments,
    store_get_ne _ _ (by decide), store_get_self]

theorem marketFeeAuthEval (evm : EVM.State) (id value : UInt256) :
    evalExpr? config (marketFeeFrame evm id value) evm (roleGuard "feeSetter") =
      .ok (.bool (decide (roleAllowed evm ⟨10⟩))) := by
  exact evalRoleGuard evm "feeSetter" ⟨10⟩ rfl
    (by simp [marketFeeFrame, calldataFrame, marketFeeArguments]) rfl rfl

theorem marketFeeEnabledEval (evm : EVM.State) (id value : UInt256) :
    evalExpr? config (marketFeeFrame evm id value) evm
      (.binary .gt (.storage { base := "_marketState", steps := [.field "tickSpacing"] }) (.intLit 0)) =
      .ok (.bool (decide (0 < (marketTickSpacing (marketFeeWord evm id)).toNat))) := by
  rw [evalExpr_binary_nonshort (by decide : BinaryOp.gt ≠ .and) (by decide : BinaryOp.gt ≠ .or)]
  rw [evalMarketAliasTickSpacing (id := id) (store_get_self _ _ _)]
  simp [evalExpr?, bind, pure, EvalResult.bind, evalBinaryOp?]

theorem marketFeeAssign (evm : EVM.State) (id value : UInt256) :
    assignStorageRef? config (marketFeeFrame evm id value) evm .storage
      { base := "_marketState", steps := [.field "continuousFee"] }
      (.int (Int.ofNat value.toNat % packedUInt32Modulus)) =
      .ok (marketFeeFrame evm id value, marketFeeState evm id value) := by
  apply assignStorageAliasField (er := marketStateRef id) (ty := marketStateType)
    (layout := midnightStorageLayout)
    (loc := packedUInt32Loc (solcMappingSlot ⟨1⟩ id + ⟨2⟩) 14 (by decide))
    (store_get_self _ _ _) rfl rfl ?_ (storageLocStore_uint32_offset14_word evm _ value)
  change some (StorageAddr.leaf (packedUInt32Loc (solcMappingSlot ⟨1⟩
    (keyValueToWord (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE id))) + ⟨2⟩) 14 (by decide))) = _
  simp only [abiBytes32Width, keyValueToWord_fixedBytes32]

theorem marketFeeAuthReverts (evm : EVM.State) (id value : UInt256)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < calldataLimit) (hauth : ¬ roleAllowed evm ⟨10⟩) :
    ExecTransitionBody fork config contract evm (marketFeeArguments id value)
      setMarketContinuousFeeTransition.body .reverted := by
  apply ExecFuncBody.execBlockRevert
  apply guardedBodyBlock hwv hhi
  apply (marketFeeBindAlias evm id value).run
  apply ExecBlock.consRevert
  apply ExecStmt.requireFalse
  simpa only [decide_eq_false hauth] using marketFeeAuthEval evm id value

theorem marketFeeBoundReverts (evm : EVM.State) (id value : UInt256)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < calldataLimit) (hauth : roleAllowed evm ⟨10⟩)
    (hbound : ¬ value.toNat ≤ 317097919) :
    ExecTransitionBody fork config contract evm (marketFeeArguments id value)
      setMarketContinuousFeeTransition.body .reverted := by
  apply ExecFuncBody.execBlockRevert
  apply guardedBodyBlock hwv hhi
  apply (marketFeeBindAlias evm id value).run
  refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
  · simpa only [decide_eq_true hauth] using marketFeeAuthEval evm id value
  apply ExecBlock.consRevert
  apply ExecStmt.requireFalse
  simpa only [decide_eq_false hbound] using
      evalContinuousFeeBound (evm := evm) (marketFeeValueGet evm id value)

theorem marketFeeReturns (evm : EVM.State) (id value : UInt256)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < calldataLimit) (hauth : roleAllowed evm ⟨10⟩)
    (hbound : value.toNat ≤ 317097919)
    (hspace : marketTickSpacing (marketFeeWord evm id) ≠ ⟨0⟩)
    (hperm : evm.executionEnv.perm = true) :
    ExecTransitionBody fork config contract evm (marketFeeArguments id value)
      setMarketContinuousFeeTransition.body
      (.returned (marketFeeFrame evm id value)
        (marketFeeState evm id value) none) := by
  apply ExecFuncBody.execBlockOK
  apply guardedBodyBlock hwv hhi
  apply (marketFeeBindAlias evm id value).run
  refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
  · simpa only [decide_eq_true hauth] using marketFeeAuthEval evm id value
  refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
  · simpa only [decide_eq_true hbound] using
      evalContinuousFeeBound (evm := evm) (marketFeeValueGet evm id value)
  have hpos : 0 < (marketTickSpacing (marketFeeWord evm id)).toNat := by
    by_contra h
    exact hspace (uint256_toNat_eq_zero (by omega))
  refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
  · rw [marketFeeEnabledEval, decide_eq_true hpos]
  apply ExecBlock.consNormal (ExecStmt.assign (Or.inr hperm)
    (evalContinuousFeeCast (marketFeeValueGet evm id value)) (marketFeeAssign evm id value))
  apply ExecBlock.consNormal (ExecStmt.emit
    (vals := [wordBytes32Value id, .int value.toNat]) ?_ ?_) ExecBlock.nil
  · simpa only [marketFeeState, storageStore_executionEnv] using hperm
  · simp only [evalExprs?, evalExpr?, marketFeeIdGet, marketFeeValueGet,
      EvalResult.ofOption, bind, pure, EvalResult.bind]

theorem marketFeeStatic (evm : EVM.State) (id value : UInt256)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < calldataLimit) (hauth : roleAllowed evm ⟨10⟩)
    (hbound : value.toNat ≤ 317097919)
    (hspace : marketTickSpacing (marketFeeWord evm id) ≠ ⟨0⟩)
    (hperm : evm.executionEnv.perm = false) :
    ExecTransitionBody fork config contract evm (marketFeeArguments id value)
      setMarketContinuousFeeTransition.body .staticViolation := by
  apply ExecFuncBody.execBlockStatic
  apply guardedBodyBlock hwv hhi
  apply (marketFeeBindAlias evm id value).run
  refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
  · simpa only [decide_eq_true hauth] using marketFeeAuthEval evm id value
  refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
  · simpa only [decide_eq_true hbound] using
      evalContinuousFeeBound (evm := evm) (marketFeeValueGet evm id value)
  have hpos : 0 < (marketTickSpacing (marketFeeWord evm id)).toNat := by
    by_contra h
    exact hspace (uint256_toNat_eq_zero (by omega))
  refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
  · rw [marketFeeEnabledEval, decide_eq_true hpos]
  apply ExecBlock.consStatic
  exact ExecStmt.assignStatic (evalContinuousFeeCast (marketFeeValueGet evm id value))
    (marketFeeAssign evm id value) hperm

theorem marketFeeDisabledReverts (evm : EVM.State) (id value : UInt256)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < calldataLimit) (hauth : roleAllowed evm ⟨10⟩)
    (hbound : value.toNat ≤ 317097919)
    (hspace : marketTickSpacing (marketFeeWord evm id) = ⟨0⟩) :
    ExecTransitionBody fork config contract evm (marketFeeArguments id value)
      setMarketContinuousFeeTransition.body .reverted := by
  apply ExecFuncBody.execBlockRevert
  apply guardedBodyBlock hwv hhi
  apply (marketFeeBindAlias evm id value).run
  refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
  · simpa only [decide_eq_true hauth] using marketFeeAuthEval evm id value
  refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
  · simpa only [decide_eq_true hbound] using
      evalContinuousFeeBound (evm := evm) (marketFeeValueGet evm id value)
  apply ExecBlock.consRevert
  apply ExecStmt.requireFalse
  rw [marketFeeEnabledEval, hspace]
  rfl

theorem marketFeeTraceStatic {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024) (hperm : I.perm = false)
    (rd : RD fork midnightBytecode I g s0 ⟨16830⟩ (x0 :: x1 :: x2 :: R) mem aw rdata σ k C) :
    RDstatic fork midnightBytecode g s0 := by
  let r0 := rd
  have r1 := r0.dup1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r2⟩ := RD.sload r1 (by native_decide) (by evm_ov)
  have r3 := r2.push4 (UInt256.ofNat 4294967295) (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 112) (by native_decide) (by evm_ov)
  have r5 := r4.shl (by native_decide) (by evm_ov)
  have r6 := r5.not (by native_decide) (by evm_ov)
  have r7 := r6.and (by native_decide) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 112) (by native_decide) (by evm_ov)
  have r9 := r8.dup4 (by native_decide) (by evm_ov)
  have r10 := r9.swap1 (by native_decide) (by evm_ov)
  have r11 := r10.shl (by native_decide) (by evm_ov)
  have r12 := r11.push4 (UInt256.ofNat 4294967295) (by native_decide) (by evm_ov)
  have r13 := r12.push1 (UInt256.ofNat 112) (by native_decide) (by evm_ov)
  have r14 := r13.shl (by native_decide) (by evm_ov)
  have r15 := r14.and (by native_decide) (by evm_ov)
  have r16 := r15.or (by native_decide) (by evm_ov)
  have r17 := r16.swap1 (by native_decide) (by evm_ov)
  exact r17.sstoreStatic hperm (by native_decide) (by evm_ov)

theorem marketFeeTraceReturn {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {slot value id : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024) (hperm : I.perm = true) (hvalue : value.toNat < 2 ^ 32)
    (rd : RD fork midnightBytecode I g s0 ⟨16830⟩ (slot :: value :: id :: R) mem aw rdata σ k C) :
    RDret fork midnightBytecode g s0
      (sstoreAccountMap I.codeOwner σ slot (setUint32Offset14Word (solcSlotWordAt slot σ I) value))
      ByteArray.empty := by
  have hr := midnightBlocks.midnight_block_16830 hstack hperm rd
  simpa only [show UInt256.ofNat 4294967295 = (⟨4294967295⟩ : UInt256) from rfl,
    show UInt256.ofNat 112 = (⟨112⟩ : UInt256) from rfl,
    setUint32Offset14Word_solc _ _ hvalue] using hr

/-- `setMarketContinuousFee(bytes32,uint256)`: the theorem `Correct.lean` routes selector 7 to. -/
theorem midnightSetMarketContinuousFeeBody {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = midnightBytecode) (hsize : I.calldata.size < UInt256.size)
    (hfork : fork ≥ .osaka)
    (hgas : midnightGasBound g)
    (hsel : selIs I (midnightSelBytes 7)) :
    runtimeRefinementFor fork config contract σ σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (midnightSelBytes 7) rfl hsel
  have hd : dispatchMsg contract I.calldata = some setMarketContinuousFeeTransition := by
    apply midnightDispatch_setMarketContinuousFee <;>
      first | exact hsel | exact selectorNe_of_selIs hsel (by decide +kernel)
  obtain ⟨k, C, rd⟩ := midnightReachSetMarketContinuousFeeBody
    (σ := σ) (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g) hcode hsz hsize hsel
  by_cases hwv : I.weiValue = ⟨0⟩
  · have rd1 := midnightBlocks.midnight_block_16758_fallthrough (by simp) hwv rd
    have rd2 := midnightBlocks.midnight_block_16764 (by simp) (by jump_dest) rd1
    simp only [midnightBlocks.midnight_block_16764_stack] at rd2
    by_cases hhi : I.calldata.size < calldataLimit
    · by_cases h68 : 68 ≤ I.calldata.size
      · have rd3 := midnightBlocks.midnight_block_18819_fallthrough (by simp)
          (entrySizeCheck_ok (bytes := 64) h68 hhi hsize) rd2
        simp only [midnightBlocks.midnight_block_18819_fallthrough_stack] at rd3
        have rd4 := midnightBlocks.midnight_block_18832 (by simp) (by jump_dest) rd3
        simp only [midnightBlocks.midnight_block_18832_stack] at rd4
        change RD fork _ _ _ _ _ [calldataWord I.calldata 36, calldataWord I.calldata 4,
          solcSelectorWord I] midnightEntryMemory _ _ _ _ _ at rd4
        have hdec := midnightDecodePair_ok "id" "newContinuousFee"
          (by decide) (by decide) (by decide) (by decide) h68 hhi hsize
          (decodeBytes32Word (off := 4) (by omega)) (decodeUint256Word (off := 36) h68)
        by_cases hauth : solcSourceWord I = UInt256.land (solcSlotWordAt ⟨10⟩ σ I) solcAddrMask
        · obtain ⟨k5, C5, rd5⟩ := midnightBlocks.midnight_block_16772_fallthrough (by simp)
            (by rw [addressMask_computed]; exact u256_sub_eq_zero_iff_eq.mpr hauth) rd4
          simp only [midnightBlocks.midnight_block_16772_fallthrough_stack,
            midnightBlocks.midnight_block_16772_fallthrough_memory,
            show (⟨0⟩ : UInt256).toNat = 0 from rfl,
            show (UInt256.ofNat 32).toNat = 32 from rfl,
            wordAt0_fold, twoWordHash_fold, mappingMemory_fold, mappingMemory_hash] at rd5
          change RD fork _ _ _ _ _ [solcMappingSlot ⟨1⟩ (calldataWord I.calldata 4),
            calldataWord I.calldata 36, calldataWord I.calldata 4, solcSelectorWord I] _ _ _ _ _ _ at rd5
          by_cases hbound : (calldataWord I.calldata 36).toNat ≤ 317097919
          · have rd6 := midnightBlocks.midnight_block_16803_fallthrough (by simp) (ugt_zero hbound) rd5
            by_cases hspace : marketTickSpacing
                (solcSlotWordAt (solcMappingSlot ⟨1⟩ (calldataWord I.calldata 4) + ⟨2⟩) σ I) = ⟨0⟩
            · obtain ⟨k7, C7, rd7⟩ := midnightBlocks.midnight_block_16814_taken (by simp)
                (by
                  rw [u256_add_comm (UInt256.ofNat 2)]
                  change UInt256.isZero (marketTickSpacing (solcSlotWordAt
                    (solcMappingSlot ⟨1⟩ (calldataWord I.calldata 4) + ⟨2⟩) σ I)) ≠ ⟨0⟩
                  rw [hspace]; decide) (by jump_dest) rd6
              have hr := midnightBlocks.midnight_block_16904
                (by simp [midnightBlocks.midnight_block_16814_taken_stack]) rd7
              exact hr.reEquivExecutionRevert hcode hd hdec
                (marketFeeDisabledReverts (initState σ σ₀ (Sat256.ofUInt256 g) A I)
                  (calldataWord I.calldata 4) (calldataWord I.calldata 36) hwv hhi hauth hbound hspace)
            · obtain ⟨k7, C7, rd7⟩ := midnightBlocks.midnight_block_16814_fallthrough (by simp)
                (by rw [u256_add_comm (UInt256.ofNat 2)]; exact isZero_eq_zero_of_ne hspace) rd6
              simp only [midnightBlocks.midnight_block_16814_fallthrough_stack] at rd7
              rw [u256_add_comm (UInt256.ofNat 2)] at rd7
              simp only [show UInt256.ofNat 2 = (⟨2⟩ : UInt256) from rfl] at rd7
              by_cases hperm : I.perm = true
              · have hr := marketFeeTraceReturn (by simp) hperm (by omega) rd7
                have hac := storageWordWrite_accounts (σ := σ)
                  (evm := initState σ σ₀ (Sat256.ofUInt256 g) A I) rfl
                  (solcMappingSlot ⟨1⟩ (calldataWord I.calldata 4) + ⟨2⟩)
                  (fun old ↦ setUint32Offset14Word old (calldataWord I.calldata 36))
                exact hr.reEquivExecutionGen hcode hd hdec
                  (marketFeeReturns (initState σ σ₀ (Sat256.ofUInt256 g) A I)
                    (calldataWord I.calldata 4) (calldataWord I.calldata 36) hwv hhi hauth hbound hspace hperm)
                  hac voidReturnEquiv
              · have hp : I.perm = false := by cases h : I.perm <;> simp_all
                have hr := marketFeeTraceStatic (by simp) hp rd7
                exact hr.reEquivStaticHalt hcode hd hdec
                  (marketFeeStatic (initState σ σ₀ (Sat256.ofUInt256 g) A I)
                    (calldataWord I.calldata 4) (calldataWord I.calldata 36) hwv hhi hauth hbound hspace hp)
          · have rd6 := midnightBlocks.midnight_block_16803_taken (by simp)
              (by rw [ugt_one (a := calldataWord I.calldata 36) (b := UInt256.ofNat 317097919)
                (Nat.lt_of_not_ge hbound)]; decide) (by jump_dest) rd5
            have hr := midnightBlocks.midnight_block_16919 (by simp) rd6
            exact hr.reEquivExecutionRevert hcode hd hdec
              (marketFeeBoundReverts (initState σ σ₀ (Sat256.ofUInt256 g) A I)
                (calldataWord I.calldata 4) (calldataWord I.calldata 36) hwv hhi hauth hbound)
        · obtain ⟨k5, C5, rd5⟩ := midnightBlocks.midnight_block_16772_taken (by simp)
            (by rw [addressMask_computed]; exact fun h ↦ hauth (u256_sub_eq_zero_iff_eq.mp h))
            (by jump_dest) rd4
          have hr := midnightBlocks.midnight_block_15431
            (by simp [midnightBlocks.midnight_block_16772_taken_stack]) rd5
          exact hr.reEquivExecutionRevert hcode hd hdec
            (marketFeeAuthReverts (initState σ σ₀ (Sat256.ofUInt256 g) A I)
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
          (midnightDecodePair_none_short "id" "newContinuousFee" (.bytes abiBytes32Width)
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
        (midnightDecodePair_none_huge "id" "newContinuousFee" (.bytes abiBytes32Width)
          (.int (.uint ⟨256, by decide⟩)) (Nat.le_of_not_lt hhi) hsize)
  · have rd1 := midnightBlocks.midnight_block_16758_taken (by simp) hwv (by jump_dest) rd
    have hr := midnightBlocks.midnight_block_6350 (by simp) rd1
    cases hdec : config.externalABI.decodeCalldata? (setMarketContinuousFeeTransition.params.map Param.name)
        (transitionSignature setMarketContinuousFeeTransition).paramTypes I.calldata with
    | none => exact hr.reEquivDecodingFailed hcode hd hdec
    | some args =>
      exact hr.reEquivExecutionRevert hcode hd hdec (bodyReverts_nonPayable hwv)

end Benchmarks.Midnight
