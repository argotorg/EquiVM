import Benchmarks.Midnight.Dispatch
import Benchmarks.Midnight.ContinuousSource
import Benchmarks.Midnight.PairDecode
import Benchmarks.Midnight.AddressDecode
import Benchmarks.Midnight.MappingMemory

/-!
# Midnight `setDefaultContinuousFee(address,uint256)`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Stele body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 18051; reach lemma `midnightReachSetDefaultContinuousFeeBody`.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

def defaultFeeArguments (token value : UInt256) : Store :=
  (((∅ : Store).insert "loanToken" (.address (AccountAddress.ofNat token.toNat))).insert
    "newContinuousFee" (.int value.toNat))

def defaultFeeState (evm : EVM.State) (token value : UInt256) : EVM.State :=
  let slot := solcMappingSlot ⟨5⟩ token
  Stele.EVM.storageStore evm evm.executionEnv.codeOwner slot
    (setUint32Offset0Word (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner slot) value)

theorem defaultFeeValueGet (evm : EVM.State) (token value : UInt256) :
    (calldataFrame contract (defaultFeeArguments token value) ∅ evm).locals.get?
      "newContinuousFee" = some (.int value.toNat) := by
  change (((defaultFeeArguments token value).insert "__calldata"
    (.bytes evm.executionEnv.calldata)).get? "newContinuousFee") = _
  rw [store_get_ne _ _ (by decide)]
  exact store_get_self _ _ _

theorem defaultFeeTokenGet (evm : EVM.State) (token value : UInt256) :
    (calldataFrame contract (defaultFeeArguments token value) ∅ evm).locals.get?
      "loanToken" = some (.address (AccountAddress.ofNat token.toNat)) := by
  change (((defaultFeeArguments token value).insert "__calldata"
    (.bytes evm.executionEnv.calldata)).get? "loanToken") = _
  rw [store_get_ne _ _ (by decide), defaultFeeArguments, store_get_ne _ _ (by decide), store_get_self]

theorem defaultFeeAuthEval (evm : EVM.State) (token value : UInt256) :
    evalExpr? config (calldataFrame contract (defaultFeeArguments token value) ∅ evm) evm
      (roleGuard "feeSetter") = .ok (.bool (decide (roleAllowed evm ⟨10⟩))) := by
  exact evalRoleGuard evm "feeSetter" ⟨10⟩ rfl
    (by simp [calldataFrame, defaultFeeArguments]) rfl rfl

theorem defaultFeeAssign (evm : EVM.State) (token value : UInt256)
    (hcanon : token.toNat < EVM.addressModulus) :
    assignStorageRef? config (calldataFrame contract (defaultFeeArguments token value) ∅ evm) evm
      .storage { base := "defaultContinuousFee", steps := [.mindex (.var "loanToken")] }
      (.int (Int.ofNat value.toNat % packedUInt32Modulus)) =
      .ok (calldataFrame contract (defaultFeeArguments token value) ∅ evm,
        defaultFeeState evm token value) := by
  apply assignStorageRef_storage_scalar_value
    (er := { base := "defaultContinuousFee", steps := [.mindex
      (.address (AccountAddress.ofNat token.toNat))] })
    (ty := .elem (.int packedUInt32Int))
    (loc := packedUInt32Loc (solcMappingSlot ⟨5⟩ token) 0 (by decide))
    (layout := midnightStorageLayout)
  · simp [calldataFrame, defaultFeeArguments]
  · simp only [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, evalExpr?,
      defaultFeeTokenGet, EvalResult.bind, EvalResult.ofOption, valueToKey?, pure, bind]
  · rfl
  · rfl
  · change some (StorageAddr.leaf (packedUInt32Loc (solcMappingSlot ⟨5⟩
      (keyValueToWord (.address (AccountAddress.ofNat token.toNat)))) 0 (by decide))) = _
    rw [keyValueToWord_address_of_canonical token hcanon]
  · exact Or.inl ⟨_, rfl⟩
  · exact storageLocStore_uint32_offset0_word evm _ value

theorem defaultFeeAuthReverts (evm : EVM.State) (token value : UInt256)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < calldataLimit) (hauth : ¬ roleAllowed evm ⟨10⟩) :
    ExecTransitionBody config contract evm (defaultFeeArguments token value)
      setDefaultContinuousFeeTransition.body .reverted := by
  apply ExecFuncBody.execBlockRevert
  apply guardedBodyBlock hwv hhi
  apply ExecBlock.consRevert
  apply ExecStmt.requireFalse
  simpa only [decide_eq_false hauth] using defaultFeeAuthEval evm token value

theorem defaultFeeBoundReverts (evm : EVM.State) (token value : UInt256)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < calldataLimit) (hauth : roleAllowed evm ⟨10⟩)
    (hbound : ¬ value.toNat ≤ 317097919) :
    ExecTransitionBody config contract evm (defaultFeeArguments token value)
      setDefaultContinuousFeeTransition.body .reverted := by
  apply ExecFuncBody.execBlockRevert
  apply guardedBodyBlock hwv hhi
  refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
  · simpa only [decide_eq_true hauth] using defaultFeeAuthEval evm token value
  apply ExecBlock.consRevert
  apply ExecStmt.requireFalse
  simpa only [decide_eq_false hbound] using
      evalContinuousFeeBound (evm := evm) (defaultFeeValueGet evm token value)

theorem defaultFeeReturns (evm : EVM.State) (token value : UInt256)
    (hcanon : token.toNat < EVM.addressModulus)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < calldataLimit) (hauth : roleAllowed evm ⟨10⟩)
    (hbound : value.toNat ≤ 317097919) (hperm : evm.executionEnv.perm = true) :
    ExecTransitionBody config contract evm (defaultFeeArguments token value)
      setDefaultContinuousFeeTransition.body
      (.returned (calldataFrame contract (defaultFeeArguments token value) ∅ evm)
        (defaultFeeState evm token value) none) := by
  apply ExecFuncBody.execBlockOK
  apply guardedBodyBlock hwv hhi
  refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
  · simpa only [decide_eq_true hauth] using defaultFeeAuthEval evm token value
  refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
  · simpa only [decide_eq_true hbound] using
      evalContinuousFeeBound (evm := evm) (defaultFeeValueGet evm token value)
  apply ExecBlock.consNormal (ExecStmt.assign (Or.inr hperm)
    (evalContinuousFeeCast (defaultFeeValueGet evm token value)) (defaultFeeAssign evm token value hcanon))
  apply ExecBlock.consNormal (ExecStmt.emit
    (vals := [.address (AccountAddress.ofNat token.toNat), .int value.toNat]) ?_ ?_) ExecBlock.nil
  · simpa only [defaultFeeState, storageStore_executionEnv] using hperm
  · simp only [evalExprs?, evalExpr?, defaultFeeTokenGet, defaultFeeValueGet,
      EvalResult.ofOption, bind, pure, EvalResult.bind]

theorem defaultFeeStatic (evm : EVM.State) (token value : UInt256)
    (hcanon : token.toNat < EVM.addressModulus)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < calldataLimit) (hauth : roleAllowed evm ⟨10⟩)
    (hbound : value.toNat ≤ 317097919) (hperm : evm.executionEnv.perm = false) :
    ExecTransitionBody config contract evm (defaultFeeArguments token value)
      setDefaultContinuousFeeTransition.body .staticViolation := by
  apply ExecFuncBody.execBlockStatic
  apply guardedBodyBlock hwv hhi
  refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
  · simpa only [decide_eq_true hauth] using defaultFeeAuthEval evm token value
  refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
  · simpa only [decide_eq_true hbound] using
      evalContinuousFeeBound (evm := evm) (defaultFeeValueGet evm token value)
  apply ExecBlock.consStatic
  exact ExecStmt.assignStatic (evalContinuousFeeCast (defaultFeeValueGet evm token value))
    (defaultFeeAssign evm token value hcanon) hperm

theorem defaultFeeTraceStatic {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024) (hperm : I.perm = false)
    (rd : RD midnightBytecode I g s0 ⟨18110⟩ (x0 :: x1 :: R) mem aw rdata σ k C) :
    RDstatic midnightBytecode g s0 := by
  let r0 := rd
  have r1 := r0.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r4 := r3.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r5 := r4.shl (by native_decide) (by evm_ov)
  have r6 := r5.sub (by native_decide) (by evm_ov)
  have r7 := r6.pushConst (UInt256.ofNat 39718144341694055941066774316026500087445325744986520979095994601084674811753) (width := 32) (op := .PUSH32) (by decide) (by native_decide) (by evm_ov)
  have r8 := r7.swap3 (by native_decide) (by evm_ov)
  have r9 := r8.and (by native_decide) (by evm_ov)
  have r10 := r9.swap3 (by native_decide) (by evm_ov)
  have r11 := r10.dup4 (by native_decide) (by evm_ov)
  have r12 := r11.push0 (by native_decide) (by evm_ov)
  have r13 := RD.genMstore r12 (by native_decide) (by evm_ov)
  have r14 := r13.push1 (UInt256.ofNat 5) (by native_decide) (by evm_ov)
  have r15 := r14.dup3 (by native_decide) (by evm_ov)
  have r16 := RD.genMstore r15 (by native_decide) (by evm_ov)
  have r17 := r16.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r18 := r17.push0 (by native_decide) (by evm_ov)
  have r19 := RD.genKeccak256 r18 (by native_decide) (by evm_ov)
  have r20 := r19.push4 (UInt256.ofNat 4294967295) (by native_decide) (by evm_ov)
  have r21 := r20.dup3 (by native_decide) (by evm_ov)
  have r22 := r21.and (by native_decide) (by evm_ov)
  have r23 := r22.push4 (UInt256.ofNat 4294967295) (by native_decide) (by evm_ov)
  have r24 := r23.not (by native_decide) (by evm_ov)
  have r25 := r24.dup3 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r26⟩ := RD.sload r25 (by native_decide) (by evm_ov)
  have r27 := r26.and (by native_decide) (by evm_ov)
  have r28 := r27.or (by native_decide) (by evm_ov)
  have r29 := r28.swap1 (by native_decide) (by evm_ov)
  exact r29.sstoreStatic hperm (by native_decide) (by evm_ov)

theorem defaultFeeTraceReturn {σ σ₀ A I} {g : Sat256} {k C : Nat} {aw token value : UInt256}
    (hcanon : token.toNat < EVM.addressModulus) (hperm : I.perm = true)
    (rd : RD midnightBytecode I g (initState σ σ₀ g A I) ⟨18110⟩
      [token, value, solcSelectorWord I] midnightEntryMemory aw ByteArray.empty σ k C) :
    RDret midnightBytecode g (initState σ σ₀ g A I)
      (sstoreAccountMap I.codeOwner σ (solcMappingSlot ⟨5⟩ token)
        (setUint32Offset0Word (solcSlotWordAt (solcMappingSlot ⟨5⟩ token) σ I) value))
      ByteArray.empty := by
  have hr := midnightBlocks.midnight_block_18110 (by simp) hperm rd
  simp only [addressMask_computed, solcAddrMask_clean hcanon,
    show (⟨0⟩ : UInt256).toNat = 0 from rfl, show (UInt256.ofNat 32).toNat = 32 from rfl,
    wordAt0_fold, twoWordHash_fold, mappingMemory_fold, mappingMemory_hash] at hr
  exact hr

/-- `setDefaultContinuousFee(address,uint256)`: the theorem `Correct.lean` routes selector 1 to. -/
theorem midnightSetDefaultContinuousFeeBody {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = midnightBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwf : midnightWF σ I)
    (hgas : midnightGasBound g)
    (hsel : selIs I (midnightSelBytes 1)) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (midnightSelBytes 1) rfl hsel
  have hd : dispatchMsg contract I.calldata = some setDefaultContinuousFeeTransition := by
    apply midnightDispatch_setDefaultContinuousFee <;>
      first | exact hsel | exact selectorNe_of_selIs hsel (by decide +kernel)
  obtain ⟨k, C, rd⟩ := midnightReachSetDefaultContinuousFeeBody
    (σ := σ) (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g) hcode hsz hsize hsel
  by_cases hwv : I.weiValue = ⟨0⟩
  · have rd1 := midnightBlocks.midnight_block_18051_fallthrough (by simp) hwv rd
    by_cases hhi : I.calldata.size < calldataLimit
    · by_cases h68 : 68 ≤ I.calldata.size
      · have rd2 := midnightBlocks.midnight_block_18057_fallthrough (by simp)
          (entrySizeCheck_ok (bytes := 64) h68 hhi hsize) rd1
        have rd3 := midnightBlocks.midnight_block_18069 (by simp) (by jump_dest) rd2
        simp only [midnightBlocks.midnight_block_18069_stack] at rd3
        by_cases hcanon : (calldataWord I.calldata 4).toNat < EVM.addressModulus
        · obtain ⟨k4, C4, rd4⟩ := midnightAddress4_ok (by simp) (by jump_dest) hcanon rd3
          have hdec := midnightDecodePair_ok "loanToken" "newContinuousFee"
            (by decide) (by decide) (by decide) (by decide) h68 hhi hsize
            (decodeAddressWord (by omega) hcanon) (decodeUint256Word h68)
          by_cases hauth : solcSourceWord I = UInt256.land (solcSlotWordAt ⟨10⟩ σ I) solcAddrMask
          · obtain ⟨k5, C5, rd5⟩ := midnightBlocks.midnight_block_18076_fallthrough (by simp)
              (by rw [addressMask_computed]; exact u256_sub_eq_zero_iff_eq.mpr hauth) rd4
            simp only [midnightBlocks.midnight_block_18076_fallthrough_stack] at rd5
            change RD _ _ _ _ _ [calldataWord I.calldata 4, calldataWord I.calldata 36,
              solcSelectorWord I] _ _ _ _ _ _ at rd5
            by_cases hbound : (calldataWord I.calldata 36).toNat ≤ 317097919
            · have rd6 := midnightBlocks.midnight_block_18099_fallthrough (by simp)
                (ugt_zero hbound) rd5
              by_cases hperm : I.perm = true
              · have hr := defaultFeeTraceReturn hcanon hperm rd6
                exact hr.reEquivExecutionGen hcode hd hdec
                  (defaultFeeReturns (initState σ σ₀ (Sat256.ofUInt256 g) A I)
                    (calldataWord I.calldata 4) (calldataWord I.calldata 36)
                    hcanon hwv hhi hauth hbound hperm)
                  (storageWordWrite_accounts (evm := initState σ σ₀ (Sat256.ofUInt256 g) A I) rfl
                    (solcMappingSlot ⟨5⟩ (calldataWord I.calldata 4))
                    (fun old ↦ setUint32Offset0Word old (calldataWord I.calldata 36)))
                  voidReturnEquiv
              · have hp : I.perm = false := by cases h : I.perm <;> simp_all
                have hr := defaultFeeTraceStatic (by simp) hp rd6
                exact hr.reEquivStaticHalt hcode hd hdec
                  (defaultFeeStatic (initState σ σ₀ (Sat256.ofUInt256 g) A I)
                    (calldataWord I.calldata 4) (calldataWord I.calldata 36)
                    hcanon hwv hhi hauth hbound hp)
            · have rd6 := midnightBlocks.midnight_block_18099_taken (by simp)
                (by rw [ugt_one (a := calldataWord I.calldata 36) (b := UInt256.ofNat 317097919)
                  (Nat.lt_of_not_ge hbound)]; decide) (by jump_dest) rd5
              have hr := midnightBlocks.midnight_block_16919 (by simp) rd6
              exact hr.reEquivExecutionRevert hcode hd hdec
                (defaultFeeBoundReverts (initState σ σ₀ (Sat256.ofUInt256 g) A I)
                  (calldataWord I.calldata 4) (calldataWord I.calldata 36) hwv hhi hauth hbound)
          · obtain ⟨k5, C5, rd5⟩ := midnightBlocks.midnight_block_18076_taken (by simp)
              (by rw [addressMask_computed]; exact fun h ↦ hauth (u256_sub_eq_zero_iff_eq.mp h))
              (by jump_dest) rd4
            have hr := midnightBlocks.midnight_block_15431
              (by simp [midnightBlocks.midnight_block_18076_taken_stack]) rd5
            exact hr.reEquivExecutionRevert hcode hd hdec
              (defaultFeeAuthReverts (initState σ σ₀ (Sat256.ofUInt256 g) A I)
                (calldataWord I.calldata 4) (calldataWord I.calldata 36) hwv hhi hauth)
        · have hr := midnightAddress4_revert (by simp) hcanon rd3
          exact hr.reEquivDecodingFailed hcode hd
            (midnightDecodePair_none_left "loanToken" "newContinuousFee" .address
              (.int (.uint ⟨256, by decide⟩)) h68 hhi hsize
              (decodeAddressWord_none (by omega) hcanon))
      · have rd2 := midnightBlocks.midnight_block_18057_taken (by simp)
          (by
            have hc : UInt256.slt
                (UInt256.lnot (UInt256.ofNat 3) + UInt256.ofNat I.calldata.size)
                (UInt256.ofNat 64) = ⟨1⟩ :=
              entrySizeCheck_short hsz (Nat.lt_of_not_ge h68) (by decide) hsize
            rw [hc]; decide) (by jump_dest) rd1
        have hr := midnightBlocks.midnight_block_6350 (by simp) rd2
        exact hr.reEquivDecodingFailed hcode hd
          (midnightDecodePair_none_short "loanToken" "newContinuousFee" .address
            (.int (.uint ⟨256, by decide⟩)) hsz (Nat.lt_of_not_ge h68) hsize)
    · have rd2 := midnightBlocks.midnight_block_18057_taken (by simp)
        (by
          have hc : UInt256.slt
              (UInt256.lnot (UInt256.ofNat 3) + UInt256.ofNat I.calldata.size)
              (UInt256.ofNat 64) = ⟨1⟩ := entrySizeCheck_huge (Nat.le_of_not_lt hhi) hsize (by decide)
          rw [hc]; decide) (by jump_dest) rd1
      have hr := midnightBlocks.midnight_block_6350 (by simp) rd2
      exact hr.reEquivDecodingFailed hcode hd
        (midnightDecodePair_none_huge "loanToken" "newContinuousFee" .address
          (.int (.uint ⟨256, by decide⟩)) (Nat.le_of_not_lt hhi) hsize)
  · have rd1 := midnightBlocks.midnight_block_18051_taken (by simp) hwv (by jump_dest) rd
    have hr := midnightBlocks.midnight_block_6350 (by simp) rd1
    cases hdec : config.externalABI.decodeCalldata? (setDefaultContinuousFeeTransition.params.map Param.name)
        (transitionSignature setDefaultContinuousFeeTransition).paramTypes I.calldata with
    | none => exact hr.reEquivDecodingFailed hcode hd hdec
    | some args => exact hr.reEquivExecutionRevert hcode hd hdec (bodyReverts_nonPayable hwv)

end Benchmarks.Midnight
