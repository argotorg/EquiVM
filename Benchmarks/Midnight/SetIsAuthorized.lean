import Benchmarks.Midnight.Dispatch
import Benchmarks.Midnight.AuthorizationTrace
import Benchmarks.Midnight.TripleDecode
import Benchmarks.Midnight.BoolDecode
import Benchmarks.Midnight.AddressDecode
import Benchmarks.Midnight.ScratchMemory

/-!
# Midnight `setIsAuthorized(address,bool,address)`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Stele body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 3063; reach lemma `midnightReachSetIsAuthorizedBody`.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

def setAuthorizationArguments (authorized flag user : UInt256) : Store :=
  (((∅ : Store).insert "authorized" (.address (AccountAddress.ofNat authorized.toNat))).insert
    "newIsAuthorized" (wordToElem .bool flag)).insert "onBehalf"
      (.address (AccountAddress.ofNat user.toNat))

def setAuthorizationState (evm : EVM.State) (authorized flag user : UInt256) : EVM.State :=
  Stele.EVM.storageStore evm evm.executionEnv.codeOwner (authorizationSlot user authorized)
    (setBoolOffset0Word (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner
      (authorizationSlot user authorized)) flag)

theorem setAuthorizationAuthorizedGet (evm : EVM.State) (authorized flag user : UInt256) :
    (calldataFrame contract (setAuthorizationArguments authorized flag user) ∅ evm).locals.get?
      "authorized" = some (.address (AccountAddress.ofNat authorized.toNat)) := by
  change (((((∅ : Store).insert "authorized" _).insert "newIsAuthorized" _).insert
    "onBehalf" _).insert "__calldata" _).get? "authorized" = _
  rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
    store_get_ne _ _ (by decide), store_get_self]

theorem setAuthorizationFlagGet (evm : EVM.State) (authorized flag user : UInt256) :
    (calldataFrame contract (setAuthorizationArguments authorized flag user) ∅ evm).locals.get?
      "newIsAuthorized" = some (wordToElem .bool flag) := by
  change (((((∅ : Store).insert "authorized" _).insert "newIsAuthorized" _).insert
    "onBehalf" _).insert "__calldata" _).get? "newIsAuthorized" = _
  rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide), store_get_self]

theorem setAuthorizationUserGet (evm : EVM.State) (authorized flag user : UInt256) :
    (calldataFrame contract (setAuthorizationArguments authorized flag user) ∅ evm).locals.get?
      "onBehalf" = some (.address (AccountAddress.ofNat user.toNat)) := by
  change (((((∅ : Store).insert "authorized" _).insert "newIsAuthorized" _).insert
    "onBehalf" _).insert "__calldata" _).get? "onBehalf" = _
  rw [store_get_ne _ _ (by decide), store_get_self]

theorem setAuthorizationGuardEval (evm : EVM.State) (authorized flag user : UInt256)
    (hc : user.toNat < EVM.addressModulus) :
    evalExpr? config (calldataFrame contract (setAuthorizationArguments authorized flag user) ∅ evm)
      evm onBehalfGuard = .ok (.bool (decide (onBehalfAllowed evm user))) := by
  exact evalOnBehalfGuard evm user hc rfl
    (by simp [calldataFrame, setAuthorizationArguments])
    (setAuthorizationUserGet evm authorized flag user)

theorem setAuthorizationAssign (evm : EVM.State) (authorized flag user : UInt256)
    (hc0 : authorized.toNat < EVM.addressModulus) (hc1 : user.toNat < EVM.addressModulus) :
    assignStorageRef? config (calldataFrame contract (setAuthorizationArguments authorized flag user) ∅ evm)
      evm .storage { base := "isAuthorized", steps := [.mindex (.var "onBehalf"),
        .mindex (.var "authorized")] } (wordToElem .bool flag) =
      .ok (calldataFrame contract (setAuthorizationArguments authorized flag user) ∅ evm,
        setAuthorizationState evm authorized flag user) := by
  apply assignStorageRef_storage_scalar_value
    (er := { base := "isAuthorized", steps :=
      [.mindex (.address (AccountAddress.ofNat user.toNat)),
       .mindex (.address (AccountAddress.ofNat authorized.toNat))] })
    (ty := .elem .bool) (loc := boolOffset0Loc (authorizationSlot user authorized))
    (layout := midnightStorageLayout)
  · simp [calldataFrame, setAuthorizationArguments]
  · simp only [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, evalExpr?,
      setAuthorizationUserGet, setAuthorizationAuthorizedGet, EvalResult.ofOption,
      EvalResult.bind, valueToKey?, pure, bind]
  · rfl
  · rfl
  · change some (StorageAddr.leaf (boolOffset0Loc (solcMappingSlot
      (solcMappingSlot ⟨3⟩ (keyValueToWord (.address (AccountAddress.ofNat user.toNat))))
      (keyValueToWord (.address (AccountAddress.ofNat authorized.toNat)))))) = _
    rw [keyValueToWord_address_of_canonical user hc1,
      keyValueToWord_address_of_canonical authorized hc0]
    rfl
  · exact Or.inl ⟨_, rfl⟩
  · exact storageLocStore_bool_word_offset0 evm _ flag

theorem setAuthorizationReverts (evm : EVM.State) (authorized flag user : UInt256)
    (hc : user.toNat < EVM.addressModulus)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩) (hhi : evm.executionEnv.calldata.size < calldataLimit)
    (hauth : ¬ onBehalfAllowed evm user) :
    ExecTransitionBody config contract evm (setAuthorizationArguments authorized flag user)
      setIsAuthorizedTransition.body .reverted := by
  apply ExecFuncBody.execBlockRevert
  apply guardedBodyBlock hwv hhi
  apply ExecBlock.consRevert
  apply ExecStmt.requireFalse
  simpa only [decide_eq_false hauth] using setAuthorizationGuardEval evm authorized flag user hc

theorem setAuthorizationReturns (evm : EVM.State) (authorized flag user : UInt256)
    (hc0 : authorized.toNat < EVM.addressModulus) (hc1 : user.toNat < EVM.addressModulus)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩) (hhi : evm.executionEnv.calldata.size < calldataLimit)
    (hauth : onBehalfAllowed evm user) (hperm : evm.executionEnv.perm = true) :
    ExecTransitionBody config contract evm (setAuthorizationArguments authorized flag user)
      setIsAuthorizedTransition.body
      (.returned (calldataFrame contract (setAuthorizationArguments authorized flag user) ∅ evm)
        (setAuthorizationState evm authorized flag user) none) := by
  apply ExecFuncBody.execBlockOK
  apply guardedBodyBlock hwv hhi
  refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
  · simpa only [decide_eq_true hauth] using setAuthorizationGuardEval evm authorized flag user hc1
  apply ExecBlock.consNormal (ExecStmt.assign (Or.inr hperm)
    (by simp only [evalExpr?, setAuthorizationFlagGet, EvalResult.ofOption])
    (setAuthorizationAssign evm authorized flag user hc0 hc1))
  apply ExecBlock.consNormal (ExecStmt.emit (vals := [.address evm.executionEnv.source,
    .address (AccountAddress.ofNat authorized.toNat), wordToElem .bool flag,
    .address (AccountAddress.ofNat user.toNat)]) ?_ ?_) ExecBlock.nil
  · simpa only [setAuthorizationState, storageStore_executionEnv] using hperm
  · simp only [evalExprs?, evalExpr?, envValue, setAuthorizationState, storageStore_executionEnv,
      setAuthorizationAuthorizedGet, setAuthorizationFlagGet, setAuthorizationUserGet,
      EvalResult.ofOption, EvalResult.bind, pure, bind]

theorem setAuthorizationStatic (evm : EVM.State) (authorized flag user : UInt256)
    (hc0 : authorized.toNat < EVM.addressModulus) (hc1 : user.toNat < EVM.addressModulus)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩) (hhi : evm.executionEnv.calldata.size < calldataLimit)
    (hauth : onBehalfAllowed evm user) (hperm : evm.executionEnv.perm = false) :
    ExecTransitionBody config contract evm (setAuthorizationArguments authorized flag user)
      setIsAuthorizedTransition.body .staticViolation := by
  apply ExecFuncBody.execBlockStatic
  apply guardedBodyBlock hwv hhi
  refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
  · simpa only [decide_eq_true hauth] using setAuthorizationGuardEval evm authorized flag user hc1
  apply ExecBlock.consStatic
  exact ExecStmt.assignStatic
    (by simp only [evalExpr?, setAuthorizationFlagGet, EvalResult.ofOption])
    (setAuthorizationAssign evm authorized flag user hc0 hc1) hperm

theorem setAuthorizationTraceReturn {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {authorized flag user : UInt256} {R : List UInt256}
    (hm : EntryScratch mem) (hstack : R.length + 8 ≤ 1024) (hperm : I.perm = true)
    (hcanon : authorized.toNat < EVM.addressModulus) (hbool : flag = ⟨0⟩ ∨ flag = ⟨1⟩)
    (rd : RD midnightBytecode I g s0 ⟨3136⟩ (authorized :: flag :: user :: R)
      mem aw rdata σ k C) :
    RDret midnightBytecode g s0
      (sstoreAccountMap I.codeOwner σ (authorizationSlot user authorized)
        (setBoolOffset0Word (solcSlotWordAt (authorizationSlot user authorized) σ I) flag))
      ByteArray.empty := by
  have hr := midnightBlocks.midnight_block_3136 hstack hperm rd
  have hm1 := hm.hash user (UInt256.ofNat 3)
  have hm2 := hm1.hash authorized (solcMappingSlot (UInt256.ofNat 3) user)
  simp only [addressMask_computed, solcAddrMask_clean hcanon, hm.zero,
    show (⟨0⟩ : UInt256).toNat = 0 from rfl,
    show (UInt256.ofNat 32).toNat = 32 from rfl, wordAt0_fold, twoWordHash_fold,
    hm1.zero, hm.hashValue user (UInt256.ofNat 3),
    hm1.hashValue authorized (solcMappingSlot (UInt256.ofNat 3) user), hm2.freePtr] at hr
  have hc : UInt256.land flag (UInt256.ofNat 255) = UInt256.isZero (UInt256.isZero flag) := by
    rcases hbool with rfl | rfl <;> decide
  rw [hc, u256_lor_comm] at hr
  change RDret _ _ _ _ ((writeWord
    (twoWordHashMem authorized (solcMappingSlot (UInt256.ofNat 3) user)
      (twoWordHashMem user (UInt256.ofNat 3) mem)) 832 flag).readWithPadding
    (memLoad (UInt256.ofNat 800) (writeWord
      (twoWordHashMem authorized (solcMappingSlot (UInt256.ofNat 3) user)
        (twoWordHashMem user (UInt256.ofNat 3) mem)) 832 flag)).toNat
    (memLoad (UInt256.ofNat 800) (writeWord
      (twoWordHashMem authorized (solcMappingSlot (UInt256.ofNat 3) user)
        (twoWordHashMem user (UInt256.ofNat 3) mem)) 832 flag)).toNat) at hr
  simpa only [hm2.writeZero flag, show (⟨0⟩ : UInt256).toNat = 0 from rfl,
    byteArray_readWithPadding_zero] using hr

theorem setAuthorizationTraceStatic {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {authorized flag user : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024) (hperm : I.perm = false)
    (rd : RD midnightBytecode I g s0 ⟨3136⟩ (authorized :: flag :: user :: R)
      mem aw rdata σ k C) : RDstatic midnightBytecode g s0 := by
  let r0 := rd
  have r1 := r0.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 1) (by native_decide) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 160) (by native_decide) (by evm_ov)
  have r4 := r3.shl (by native_decide) (by evm_ov)
  have r5 := r4.sub (by native_decide) (by evm_ov)
  have r6 := r5.swap1 (by native_decide) (by evm_ov)
  have r7 := r6.dup4 (by native_decide) (by evm_ov)
  have r8 := r7.push2 (UInt256.ofNat 800) (by native_decide) (by evm_ov)
  have r9 := RD.genMload r8 (by native_decide) (by evm_ov)
  have r10 := RD.genMstore r9 (by native_decide) (by evm_ov)
  have r11 := r10.push1 (UInt256.ofNat 3) (by native_decide) (by evm_ov)
  have r12 := r11.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r13 := RD.genMstore r12 (by native_decide) (by evm_ov)
  have r14 := r13.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r15 := r14.push2 (UInt256.ofNat 800) (by native_decide) (by evm_ov)
  have r16 := RD.genMload r15 (by native_decide) (by evm_ov)
  have r17 := RD.genKeccak256 r16 (by native_decide) (by evm_ov)
  have r18 := r17.dup3 (by native_decide) (by evm_ov)
  have r19 := r18.dup3 (by native_decide) (by evm_ov)
  have r20 := r19.and (by native_decide) (by evm_ov)
  have r21 := r20.push0 (by native_decide) (by evm_ov)
  have r22 := RD.genMstore r21 (by native_decide) (by evm_ov)
  have r23 := r22.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
  have r24 := RD.genMstore r23 (by native_decide) (by evm_ov)
  have r25 := r24.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
  have r26 := r25.push0 (by native_decide) (by evm_ov)
  have r27 := RD.genKeccak256 r26 (by native_decide) (by evm_ov)
  have r28 := r27.push1 (UInt256.ofNat 255) (by native_decide) (by evm_ov)
  have r29 := r28.not (by native_decide) (by evm_ov)
  have r30 := r29.dup2 (by native_decide) (by evm_ov)
  obtain ⟨_, _, r31⟩ := RD.sload r30 (by native_decide) (by evm_ov)
  have r32 := r31.and (by native_decide) (by evm_ov)
  have r33 := r32.push1 (UInt256.ofNat 255) (by native_decide) (by evm_ov)
  have r34 := r33.dup6 (by native_decide) (by evm_ov)
  have r35 := r34.and (by native_decide) (by evm_ov)
  have r36 := r35.or (by native_decide) (by evm_ov)
  have r37 := r36.swap1 (by native_decide) (by evm_ov)
  exact r37.sstoreStatic hperm (by native_decide) (by evm_ov)

/-- `setIsAuthorized(address,bool,address)`: the theorem `Correct.lean` routes selector 40 to. -/
theorem midnightSetIsAuthorizedBody {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = midnightBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwf : midnightWF σ I)
    (hgas : midnightGasBound g)
    (hsel : selIs I (midnightSelBytes 40)) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (midnightSelBytes 40) rfl hsel
  have hd : dispatchMsg contract I.calldata = some setIsAuthorizedTransition := by
    apply midnightDispatch_setIsAuthorized <;>
      first | exact hsel | exact selectorNe_of_selIs hsel (by decide +kernel)
  obtain ⟨k, C, rd⟩ := midnightReachSetIsAuthorizedBody
    (σ := σ) (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g) hcode hsz hsize hsel
  by_cases hwv : I.weiValue = ⟨0⟩
  · have rd1 := midnightBlocks.midnight_block_3063_fallthrough (by simp) hwv rd
    by_cases hhi : I.calldata.size < calldataLimit
    · by_cases h100 : 100 ≤ I.calldata.size
      · have rd2 := midnightBlocks.midnight_block_3069_fallthrough (by simp)
          (entrySizeCheck_ok (bytes := 96) h100 hhi hsize) rd1
        change RD _ _ _ _ _ [solcSelectorWord I] midnightEntryMemory _ _ _ _ _ at rd2
        have rd3 := midnightBlocks.midnight_block_3081 (by simp) (by jump_dest) rd2
        simp only [midnightBlocks.midnight_block_3081_stack] at rd3
        by_cases hc0 : (calldataWord I.calldata 4).toNat < EVM.addressModulus
        · obtain ⟨k4, C4, rd4⟩ := midnightAddress4_ok (by simp) (by jump_dest) hc0 rd3
          by_cases hb : calldataWord I.calldata 36 = ⟨0⟩ ∨ calldataWord I.calldata 36 = ⟨1⟩
          · have hclean := (boolWordClean_iff (calldataWord I.calldata 36)).mpr hb
            have rd5 := midnightBlocks.midnight_block_3088_fallthrough (by simp)
              (u256_sub_eq_zero_iff_eq.mpr hclean.symm) rd4
            change RD _ _ _ _ _ [UInt256.isZero (UInt256.isZero (calldataWord I.calldata 36)),
              calldataWord I.calldata 4, solcSelectorWord I] _ _ _ _ _ _ at rd5
            rw [hclean] at rd5
            have rd6 := midnightBlocks.midnight_block_3103 (by simp) (by jump_dest) rd5
            simp only [midnightBlocks.midnight_block_3103_stack, addressMask_computed] at rd6
            by_cases hc1 : (calldataWord I.calldata 68).toNat < EVM.addressModulus
            · obtain ⟨k7, C7, rd7⟩ := midnightAddress68_ok (by simp) (by jump_dest) hc1 rd6
              have hdec := midnightDecodeTriple_ok "authorized" "newIsAuthorized" "onBehalf"
                (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h100 hhi hsize
                (decodeAddressWord (off := 4) (by omega) hc0)
                (decodeBoolWord (off := 36) (by omega) hb) (decodeAddressWord h100 hc1)
              obtain ⟨check, mem8, aw8, k8, C8, hm8, hcheck, rd8⟩ :=
                onBehalfTraceGuard false midnightEntryScratch (by simp) hc1 rd7
              by_cases hauth : onBehalfAllowed (initState σ σ₀ (Sat256.ofUInt256 g) A I)
                  (calldataWord I.calldata 68)
              · have rd9 := midnightBlocks.midnight_block_3130_fallthrough (by simp)
                  (isZero_eq_zero_of_ne (hcheck.mpr hauth)) rd8
                simp only [midnightBlocks.midnight_block_3130_fallthrough_stack] at rd9
                by_cases hperm : I.perm = true
                · have hr := setAuthorizationTraceReturn hm8 (by simp) hperm hc0 hb rd9
                  have hac := storageWordWrite_accounts (σ := σ)
                    (evm := initState σ σ₀ (Sat256.ofUInt256 g) A I) rfl
                    (authorizationSlot (calldataWord I.calldata 68) (calldataWord I.calldata 4))
                    (fun old ↦ setBoolOffset0Word old (calldataWord I.calldata 36))
                  exact hr.reEquivExecutionGen hcode hd hdec
                    (setAuthorizationReturns (initState σ σ₀ (Sat256.ofUInt256 g) A I)
                      (calldataWord I.calldata 4) (calldataWord I.calldata 36)
                      (calldataWord I.calldata 68) hc0 hc1 hwv hhi hauth hperm) hac voidReturnEquiv
                · have hp : I.perm = false := by
                    cases h : I.perm
                    · rfl
                    · exact False.elim (hperm h)
                  have hr := setAuthorizationTraceStatic (by simp) hp rd9
                  exact hr.reEquivStaticHalt hcode hd hdec
                    (setAuthorizationStatic (initState σ σ₀ (Sat256.ofUInt256 g) A I)
                      (calldataWord I.calldata 4) (calldataWord I.calldata 36)
                      (calldataWord I.calldata 68) hc0 hc1 hwv hhi hauth hp)
              · have hz : check = ⟨0⟩ := by
                  by_contra hn
                  exact hauth (hcheck.mp hn)
                have rd9 := midnightBlocks.midnight_block_3130_taken (by simp)
                  (by rw [hz]; decide) (by jump_dest) rd8
                have hr := midnightBlocks.midnight_block_1943
                  (by simp [midnightBlocks.midnight_block_3130_taken_stack]) rd9
                exact hr.reEquivExecutionRevert hcode hd hdec
                  (setAuthorizationReverts (initState σ σ₀ (Sat256.ofUInt256 g) A I)
                    (calldataWord I.calldata 4) (calldataWord I.calldata 36)
                    (calldataWord I.calldata 68) hc1 hwv hhi hauth)
            · have hr := midnightAddress68_revert (by simp) hc1 rd6
              exact hr.reEquivDecodingFailed hcode hd
                (midnightDecodeTriple_none_right "authorized" "newIsAuthorized" "onBehalf"
                  .address .bool .address h100 hhi hsize
                  (decodeAddressWord (off := 4) (by omega) hc0)
                  (decodeBoolWord (off := 36) (by omega) hb) (decodeAddressWord_none h100 hc1))
          · have rd5 := midnightBlocks.midnight_block_3088_taken (by simp)
              (fun he ↦ hb ((boolWordClean_iff _).mp (u256_sub_eq_zero_iff_eq.mp he).symm))
              (by jump_dest) rd4
            have hr := midnightBlocks.midnight_block_712
              (by simp [midnightBlocks.midnight_block_3088_taken_stack]) rd5
            exact hr.reEquivDecodingFailed hcode hd
              (midnightDecodeTriple_none_middle "authorized" "newIsAuthorized" "onBehalf"
                .address .bool .address h100 hhi hsize
                (decodeAddressWord (off := 4) (by omega) hc0) (decodeBoolWord_none (by omega) hb))
        · have hr := midnightAddress4_revert (by simp) hc0 rd3
          exact hr.reEquivDecodingFailed hcode hd
            (midnightDecodeTriple_none_left "authorized" "newIsAuthorized" "onBehalf"
              .address .bool .address h100 hhi hsize (decodeAddressWord_none (by omega) hc0))
      · have rd2 := midnightBlocks.midnight_block_3069_taken (by simp)
          (by
            have hc : UInt256.slt
                (UInt256.lnot (UInt256.ofNat 3) + UInt256.ofNat I.calldata.size)
                (UInt256.ofNat 96) = ⟨1⟩ :=
              entrySizeCheck_short hsz (Nat.lt_of_not_ge h100) (by decide) hsize
            rw [hc]; decide) (by jump_dest) rd1
        have hr := midnightBlocks.midnight_block_712 (by simp) rd2
        exact hr.reEquivDecodingFailed hcode hd
          (midnightDecodeTriple_none_short "authorized" "newIsAuthorized" "onBehalf"
            .address .bool .address hsz (Nat.lt_of_not_ge h100) hsize)
    · have rd2 := midnightBlocks.midnight_block_3069_taken (by simp)
        (by
          have hc : UInt256.slt
              (UInt256.lnot (UInt256.ofNat 3) + UInt256.ofNat I.calldata.size)
              (UInt256.ofNat 96) = ⟨1⟩ :=
            entrySizeCheck_huge (Nat.le_of_not_lt hhi) hsize (by decide)
          rw [hc]; decide) (by jump_dest) rd1
      have hr := midnightBlocks.midnight_block_712 (by simp) rd2
      exact hr.reEquivDecodingFailed hcode hd
        (midnightDecodeTriple_none_huge "authorized" "newIsAuthorized" "onBehalf"
          .address .bool .address (Nat.le_of_not_lt hhi) hsize)
  · have rd1 := midnightBlocks.midnight_block_3063_taken (by simp) hwv (by jump_dest) rd
    have hr := midnightBlocks.midnight_block_712 (by simp) rd1
    cases hdec : config.externalABI.decodeCalldata? (setIsAuthorizedTransition.params.map Param.name)
        (transitionSignature setIsAuthorizedTransition).paramTypes I.calldata with
    | none => exact hr.reEquivDecodingFailed hcode hd hdec
    | some args => exact hr.reEquivExecutionRevert hcode hd hdec (bodyReverts_nonPayable hwv)

end Benchmarks.Midnight
