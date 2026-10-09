import Benchmarks.Morpho.MorphoBlue.ErrorRoutines
import Benchmarks.Morpho.MorphoBlue.AdminCommon

/-!
# Morpho `enableLltv(uint256)`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Solm body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 8981; reach lemma `morphoReachEnableLltvBody`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables

namespace Benchmarks.Morpho.MorphoBlue

set_option maxRecDepth 1000

def enableLltvArgs (cd : ByteArray) : Store :=
  (∅ : Store).insert "lltv" (.int (Int.ofNat (calldataWord cd 4).toNat))

def enableLltvFrame (v : MorphoImmutables) (cd : ByteArray) : Frame :=
  addressAdminFrame v (enableLltvArgs cd) cd

theorem enableLltvArg_eval (v : MorphoImmutables) (cd : ByteArray) (evm : EVM.State) :
    evalExpr? config (enableLltvFrame v cd) evm (.var "lltv") =
      .ok (.int (Int.ofNat (calldataWord cd 4).toNat)) := by
  simp only [evalExpr?, enableLltvFrame, addressAdminFrame, enableLltvArgs,
    store_get_ne (k := "__calldata") (a := "lltv") _ _ (by decide), store_get_self, EvalResult.ofOption]

theorem enableLltvLimit_eval (v : MorphoImmutables) (cd : ByteArray) (evm : EVM.State) :
    evalExpr? config (enableLltvFrame v cd) evm
      (.binary .lt (.var "lltv") (.intLit 1000000000000000000)) =
      .ok (.bool (decide ((calldataWord cd 4).toNat < 1000000000000000000))) := by
  simp only [evalExpr?, enableLltvArg_eval, pure, bind, EvalResult.bind,
    evalBinaryOp_lt_int_ok]
  change EvalResult.ok (Value.bool (decide (Int.ofNat (calldataWord cd 4).toNat <
    Int.ofNat 1000000000000000000))) = _
  simp only [Int.ofNat_eq_natCast, Int.ofNat_lt]

def lltvEnabledByte (σ : AccountMap) (I : ExecutionEnv) (w : UInt256) : UInt256 :=
  UInt256.land (solcSlotWordAt (solcMappingSlot ⟨5⟩ w) σ I) ⟨255⟩

theorem morphoEnableLltvBodySplit (v : MorphoImmutables) (evm : EVM.State)
    (hcv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsize : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (ho : solcSourceWord evm.executionEnv = solcAddressSlotWord ⟨0⟩ evm.accountMap evm.executionEnv)
    (hdisabled : lltvEnabledByte evm.accountMap evm.executionEnv
      (calldataWord evm.executionEnv.calldata 4) = ⟨0⟩)
    (hlimit : (calldataWord evm.executionEnv.calldata 4).toNat < 1000000000000000000) :
    ExecTransitionBody config contract evm (enableLltvArgs evm.executionEnv.calldata)
      enableLltvTransition.body
      (.returned (enableLltvFrame v evm.executionEnv.calldata)
        (Solm.EVM.storageStore evm evm.executionEnv.codeOwner
          (solcMappingSlot ⟨5⟩ (calldataWord evm.executionEnv.calldata 4))
          (UInt256.lor (UInt256.land (solcSlotWordAt
            (solcMappingSlot ⟨5⟩ (calldataWord evm.executionEnv.calldata 4))
            evm.accountMap evm.executionEnv) (UInt256.lnot ⟨255⟩)) ⟨1⟩)) none) (immStore v) ∧
    (evm.executionEnv.perm = false →
      ExecTransitionBody config contract evm (enableLltvArgs evm.executionEnv.calldata)
        enableLltvTransition.body .staticViolation (immStore v)) := by
  have howner := evalMorphoOwnerCheck evm (enableLltvFrame v evm.executionEnv.calldata).locals
    (immStore v) (by simp [enableLltvFrame, addressAdminFrame, enableLltvArgs])
  have hbase : (enableLltvFrame v evm.executionEnv.calldata).locals.get? "isLltvEnabled" = none := by
    simp [enableLltvFrame, addressAdminFrame, enableLltvArgs]
  have hkey := enableLltvArg_eval v evm.executionEnv.calldata evm
  have hload := evalMorphoLltvEnabled evm _ (immStore v) (.var "lltv") _ hbase hkey
  have hnot := evalNotBoolWord hload
  simp only [lltvEnabledByte] at hdisabled
  have hprefix : ABlock config evm
      { contract := contract, locals := enableLltvArgs evm.executionEnv.calldata, immutables := immStore v }
      enableLltvTransition.body (enableLltvFrame v evm.executionEnv.calldata)
      (enableLltvTransition.body.drop 6) :=
    (((calldataPrelude_ok hcv hsize).requireStep
      (by simpa only [ho, decide_true] using howner)).requireStep
      (by simpa only [hdisabled, decide_true] using hnot)).requireStep
      (by simpa only [hlimit, decide_true] using enableLltvLimit_eval v evm.executionEnv.calldata evm)
  have hassign := assignBoolMappingTrue hbase hkey rfl (by rfl) (by rfl)
    (morphoLayout_isLltvEnabled _)
  have htrue (state : EVM.State) : evalExpr? config (enableLltvFrame v evm.executionEnv.calldata)
      state (.boolLit true) = .ok (.bool true) := by simp only [evalExpr?, pure]
  constructor
  · apply ExecFuncBody.execBlockOK
    apply hprefix.run
    apply ExecBlock.consNormal (ExecStmt.assign (htrue evm) hassign)
    apply ExecBlock.consNormal (ExecStmt.emit (evalExprs?_singleton (enableLltvArg_eval v _ _)))
    exact ExecBlock.nil
  · intro hperm
    exact ExecFuncBody.execBlockStatic
      (hprefix.run (ExecBlock.consStatic (ExecStmt.assignStatic (htrue evm) hassign hperm)))

theorem morphoEnableLltvBodyRejects (v : MorphoImmutables) (evm : EVM.State)
    (hcv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsize : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (hbad : solcSourceWord evm.executionEnv ≠ solcAddressSlotWord ⟨0⟩ evm.accountMap evm.executionEnv ∨
      lltvEnabledByte evm.accountMap evm.executionEnv (calldataWord evm.executionEnv.calldata 4) ≠ ⟨0⟩ ∨
      ¬ (calldataWord evm.executionEnv.calldata 4).toNat < 1000000000000000000) :
    ExecTransitionBody config contract evm (enableLltvArgs evm.executionEnv.calldata)
      enableLltvTransition.body .reverted (immStore v) := by
  have howner := evalMorphoOwnerCheck evm (enableLltvFrame v evm.executionEnv.calldata).locals
    (immStore v) (by simp [enableLltvFrame, addressAdminFrame, enableLltvArgs])
  apply ExecFuncBody.execBlockRevert
  by_cases ho : solcSourceWord evm.executionEnv = solcAddressSlotWord ⟨0⟩ evm.accountMap evm.executionEnv
  · have hrest := hbad.resolve_left (not_not.mpr ho)
    have hload := evalMorphoLltvEnabled evm (enableLltvFrame v evm.executionEnv.calldata).locals
      (immStore v) (.var "lltv") _
      (by simp [enableLltvFrame, addressAdminFrame, enableLltvArgs]) (enableLltvArg_eval v _ evm)
    by_cases hd : lltvEnabledByte evm.accountMap evm.executionEnv (calldataWord evm.executionEnv.calldata 4) = ⟨0⟩
    · have hlimit := hrest.resolve_left (not_not.mpr hd)
      simp only [lltvEnabledByte] at hd
      exact (((calldataPrelude_ok hcv hsize).requireStep
        (by simpa only [ho, decide_true] using howner)).requireStep
        (by simpa only [hd, decide_true] using evalNotBoolWord hload)).requireRevert
        (by simpa only [hlimit, decide_false] using enableLltvLimit_eval v evm.executionEnv.calldata evm)
    · simp only [lltvEnabledByte] at hd
      exact ((calldataPrelude_ok hcv hsize).requireStep
        (by simpa only [ho, decide_true] using howner)).requireRevert
        (by simpa only [hd, decide_false] using evalNotBoolWord hload)
  · exact (calldataPrelude_ok hcv hsize).requireRevert
      (by simpa only [ho, decide_false] using howner)

def enableLltvTopic : UInt256 :=
  UInt256.ofNat 18763038649916306989046620579106042473926674683391721421162364941325853430073

abbrev lltvCheckMem (key : UInt256) : ByteArray := booleanAdminCheckMem ⟨5⟩ key

def lltvLimitMem (key : UInt256) : ByteArray :=
  morphoErrorMem (UInt256.ofNat 17)
    (UInt256.ofNat 49474313741174582105957151658253704231332233137603599106335920918818822553600)
    (morphoAlreadySetMem (lltvCheckMem key))

theorem morphoEnableLltvReachOwnerCheck {σ σ₀ A I} {g : Sat256} (v : MorphoImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (morphoSelBytes 7))
    (hcv : I.weiValue = ⟨0⟩) (hlen : 36 ≤ I.calldata.size)
    (hbound : I.calldata.size < 2 ^ 255 + 4) :
    ∃ aw k C, RD (deployedRuntime v) I g (initState σ σ₀ g A I) (UInt256.ofNat 12097)
      [UInt256.eq (solcSourceWord I) (solcAddressSlotWord ⟨0⟩ σ I),
       UInt256.ofNat 128, UInt256.ofNat 9104, calldataWord I.calldata 4,
       UInt256.ofNat 32, enableLltvTopic, ⟨0⟩]
      (morphoNotOwnerMem solcFreePtrMem) aw ByteArray.empty σ k C := by
  obtain ⟨k, C, rd⟩ := morphoReachEnableLltvBody (g := g) (σ := σ) (σ₀ := σ₀)
    (A := A) v hcode (by omega) hsize hsel
  change RD _ _ _ _ _ _ solcFreePtrMem _ _ _ _ _ at rd
  have rdGuard := morphoBlocks.morpho_block_8981_fallthrough
    (immWords := wordsOf (immStore v)) (by decide) hcv rd
  have hcond := solcCalldataStaticLenCheckOk (words := 1) hlen hbound hsize
  have rdBody := morphoBlocks.morpho_block_8988_fallthrough
    (immWords := wordsOf (immStore v)) (by decide)
    (by simpa only [wordAddNegFour] using hcond) rdGuard
  obtain ⟨kb, Cb, rdMessage⟩ := morphoBlocks.morpho_block_9030
    (immWords := wordsOf (immStore v)) (by simp)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rdBody
  obtain ⟨aw, km, Cm, rdCheck⟩ := morphoNotOwnerMessage (v := v) (by simp)
    (by rw [morphoPatchedValidJumps v]; jump_dest) (by native_decide) rdMessage
  have rdRequire := morphoBlocks.morpho_block_585
    (immWords := wordsOf (immStore v)) (by simp)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rdCheck
  have hptr : memLoad (UInt256.ofNat 64) solcFreePtrMem = UInt256.ofNat 128 := solcFreePtrMem_mload64
  exact ⟨_, _, _, by simpa only [morphoBlocks.morpho_block_585_stack, hptr] using rdRequire⟩

theorem morphoEnableLltvReachEnabledCheck {σ σ₀ A I} {g : Sat256} (v : MorphoImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (morphoSelBytes 7))
    (hcv : I.weiValue = ⟨0⟩) (hlen : 36 ≤ I.calldata.size)
    (hbound : I.calldata.size < 2 ^ 255 + 4)
    (ho : solcSourceWord I = solcAddressSlotWord ⟨0⟩ σ I) :
    ∃ aw k C, RD (deployedRuntime v) I g (initState σ σ₀ g A I) (UInt256.ofNat 12097)
      [UInt256.isZero (lltvEnabledByte σ I (calldataWord I.calldata 4)),
       UInt256.ofNat 192, UInt256.ofNat 9131, calldataWord I.calldata 4,
       UInt256.ofNat 32, enableLltvTopic, ⟨0⟩]
      (morphoAlreadySetMem (lltvCheckMem (calldataWord I.calldata 4))) aw ByteArray.empty σ k C := by
  obtain ⟨aw, k, C, rd⟩ := morphoEnableLltvReachOwnerCheck (g := g) (σ := σ) (σ₀ := σ₀)
    (A := A) v hcode hsize hsel hcv hlen hbound
  obtain ⟨kt, Ct, rdNext⟩ := morphoRequireTrue (v := v) (by simp)
    (by rw [morphoPatchedValidJumps v]; jump_dest)
    (by rw [ho, uInt256_eq_self]; decide) rd
  obtain ⟨kh, Ch, rdMessage⟩ := morphoBlocks.morpho_block_9104
    (immWords := wordsOf (immStore v)) (by simp)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rdNext
  change RD _ _ _ _ _
    [UInt256.ofNat 585,
      UInt256.isZero (UInt256.land (solcSlotWordAt
        (keccakWord ⟨0⟩ (UInt256.ofNat 64) (lltvCheckMem (calldataWord I.calldata 4))) σ I)
        (UInt256.ofNat 255)), UInt256.ofNat 9131, calldataWord I.calldata 4,
      UInt256.ofNat 32, enableLltvTopic, ⟨0⟩]
    (lltvCheckMem (calldataWord I.calldata 4)) _ _ _ _ _ at rdMessage
  have hslot : keccakWord ⟨0⟩ (UInt256.ofNat 64) (lltvCheckMem (calldataWord I.calldata 4)) =
      solcMappingSlot ⟨5⟩ (calldataWord I.calldata 4) := twoWordHashMem_solcMappingSlot_any _ _ _
  rw [hslot] at rdMessage
  obtain ⟨aw', km, Cm, rdCheck⟩ := morphoAlreadySetMessage (v := v) (by simp)
    (by rw [morphoPatchedValidJumps v]; jump_dest)
    (by rw [booleanAdminCheckMem_load64]; native_decide) rdMessage
  have rdRequire := morphoBlocks.morpho_block_585
    (immWords := wordsOf (immStore v)) (by simp)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rdCheck
  exact ⟨_, _, _, by simpa only [morphoBlocks.morpho_block_585_stack, booleanAdminCheckMem_load64] using rdRequire⟩

theorem lltvEnabledCheckMem_properties (key : UInt256) :
    (morphoAlreadySetMem (lltvCheckMem key)).size = 256 ∧
    memLoad (UInt256.ofNat 64) (morphoAlreadySetMem (lltvCheckMem key)) = UInt256.ofNat 256 ∧
    morphoErrorLength (morphoAlreadySetMem (lltvCheckMem key)) (UInt256.ofNat 192) = UInt256.ofNat 11 :=
  morphoErrorMem_properties _ _ (UInt256.ofNat 192) _ (booleanAdminCheckMem_size _ _)
    (booleanAdminCheckMem_load64 _ _) (by decide) (by decide)

theorem lltvLimitMem_length (key : UInt256) :
    morphoErrorLength (lltvLimitMem key) (UInt256.ofNat 256) = UInt256.ofNat 17 :=
  (morphoErrorMem_properties _ _ (UInt256.ofNat 256) _ (lltvEnabledCheckMem_properties key).1
    (lltvEnabledCheckMem_properties key).2.1 (by decide) (by decide)).2.2

theorem morphoEnableLltvReachLimitCheck {σ σ₀ A I} {g : Sat256} (v : MorphoImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (morphoSelBytes 7))
    (hcv : I.weiValue = ⟨0⟩) (hlen : 36 ≤ I.calldata.size)
    (hbound : I.calldata.size < 2 ^ 255 + 4)
    (ho : solcSourceWord I = solcAddressSlotWord ⟨0⟩ σ I)
    (hdisabled : lltvEnabledByte σ I (calldataWord I.calldata 4) = ⟨0⟩) :
    ∃ aw k C, RD (deployedRuntime v) I g (initState σ σ₀ g A I) (UInt256.ofNat 12097)
      [UInt256.lt (calldataWord I.calldata 4) (UInt256.ofNat 1000000000000000000),
       UInt256.ofNat 256, UInt256.ofNat 9203, calldataWord I.calldata 4,
       UInt256.ofNat 32, enableLltvTopic, ⟨0⟩]
      (lltvLimitMem (calldataWord I.calldata 4)) aw ByteArray.empty σ k C := by
  obtain ⟨aw, k, C, rd⟩ := morphoEnableLltvReachEnabledCheck (g := g) (σ := σ) (σ₀ := σ₀)
    (A := A) v hcode hsize hsel hcv hlen hbound ho
  obtain ⟨kt, Ct, rdNext⟩ := morphoRequireTrue (v := v) (by simp)
    (by rw [morphoPatchedValidJumps v]; jump_dest) (by rw [hdisabled]; decide) rd
  have rdAlloc := morphoBlocks.morpho_block_9131
    (immWords := wordsOf (immStore v)) (by simp)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rdNext
  have hptr := (lltvEnabledCheckMem_properties (calldataWord I.calldata 4)).2.1
  obtain ⟨aw', ka, Ca, rdMessage⟩ := morphoAlloc64 (v := v) (by simp)
    (by rw [morphoPatchedValidJumps v]; jump_dest) (by rw [hptr]; native_decide) rdAlloc
  have rdCheck := morphoBlocks.morpho_block_9146
    (immWords := wordsOf (immStore v)) (by simp)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rdMessage
  change RD _ _ _ _ _
    [UInt256.lt (calldataWord I.calldata 4) (UInt256.ofNat 1000000000000000000),
      memLoad (UInt256.ofNat 64) (morphoAlreadySetMem (lltvCheckMem (calldataWord I.calldata 4))),
      UInt256.ofNat 9203, calldataWord I.calldata 4, UInt256.ofNat 32, enableLltvTopic, ⟨0⟩]
    (lltvLimitMem (calldataWord I.calldata 4)) _ _ _ _ _ at rdCheck
  rw [hptr] at rdCheck
  exact ⟨_, _, _, rdCheck⟩

theorem morphoEnableLltvXRejects {σ σ₀ A I} {g : Sat256} (v : MorphoImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (morphoSelBytes 7))
    (hcv : I.weiValue = ⟨0⟩) (hlen : 36 ≤ I.calldata.size)
    (hbound : I.calldata.size < 2 ^ 255 + 4)
    (hbad : solcSourceWord I ≠ solcAddressSlotWord ⟨0⟩ σ I ∨
      lltvEnabledByte σ I (calldataWord I.calldata 4) ≠ ⟨0⟩ ∨
      ¬ (calldataWord I.calldata 4).toNat < 1000000000000000000) :
    RDrev (deployedRuntime v) g (initState σ σ₀ g A I) := by
  by_cases ho : solcSourceWord I = solcAddressSlotWord ⟨0⟩ σ I
  · have hrest := hbad.resolve_left (not_not.mpr ho)
    by_cases hd : lltvEnabledByte σ I (calldataWord I.calldata 4) = ⟨0⟩
    · have hlimit := hrest.resolve_left (not_not.mpr hd)
      obtain ⟨aw, k, C, rd⟩ := morphoEnableLltvReachLimitCheck (g := g) (σ := σ) (σ₀ := σ₀)
        (A := A) v hcode hsize hsel hcv hlen hbound ho hd
      exact morphoRequireFalseShort (v := v) (by simp)
        (ult_zero (by change 1000000000000000000 ≤ _; omega))
        (by rw [lltvLimitMem_length]; decide) (by rw [lltvLimitMem_length]; decide) rd
    · obtain ⟨aw, k, C, rd⟩ := morphoEnableLltvReachEnabledCheck (g := g) (σ := σ) (σ₀ := σ₀)
        (A := A) v hcode hsize hsel hcv hlen hbound ho
      have hmsg := (lltvEnabledCheckMem_properties (calldataWord I.calldata 4)).2.2
      exact morphoRequireFalseShort (v := v) (by simp)
        (isZero_eq_zero_of_ne hd) (by rw [hmsg]; decide) (by rw [hmsg]; decide) rd
  · obtain ⟨aw, k, C, rd⟩ := morphoEnableLltvReachOwnerCheck (g := g) (σ := σ) (σ₀ := σ₀)
      (A := A) v hcode hsize hsel hcv hlen hbound
    exact morphoRequireFalseShort (v := v) (by simp)
      (u256_eq_of_ne ho) (by native_decide) (by native_decide) rd

-- The provided summary assumes write permission; this prefix covers the static halt.
theorem morphoEnableLltvStoreStatic {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {σ : AccountMap} {k C : Nat} {key size topic zero : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024) (hperm : ee.perm = false)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 9203)
      (key :: size :: topic :: zero :: R) mem aw rdata σ k C) :
    RDstatic (deployedRuntime v) g s0 := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, wordsOf (immStore v), (⟨9203⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, morphoBlocks.immutableLayout_inBounds, morphoBlocks.immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.dup1 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, wordsOf (immStore v), (⟨9204⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, morphoBlocks.immutableLayout_inBounds, morphoBlocks.immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.dup5 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, wordsOf (immStore v), (⟨9205⟩ : UInt256), UInt8.ofNat 132, .DUP5, none, morphoBlocks.immutableLayout_inBounds, morphoBlocks.immutableTemplate_size64)) (by evm_ov)
  have r4 := RD.genMstore r3 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, wordsOf (immStore v), (⟨9206⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, morphoBlocks.immutableLayout_inBounds, morphoBlocks.immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 5) (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, wordsOf (immStore v), (⟨9207⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 5), 1), morphoBlocks.immutableLayout_inBounds, morphoBlocks.immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.dup3 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, wordsOf (immStore v), (⟨9209⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, morphoBlocks.immutableLayout_inBounds, morphoBlocks.immutableTemplate_size64)) (by evm_ov)
  have r7 := RD.genMstore r6 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, wordsOf (immStore v), (⟨9210⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, morphoBlocks.immutableLayout_inBounds, morphoBlocks.immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 64) (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, wordsOf (immStore v), (⟨9211⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1), morphoBlocks.immutableLayout_inBounds, morphoBlocks.immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.dup5 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, wordsOf (immStore v), (⟨9213⟩ : UInt256), UInt8.ofNat 132, .DUP5, none, morphoBlocks.immutableLayout_inBounds, morphoBlocks.immutableTemplate_size64)) (by evm_ov)
  have r10 := RD.genKeccak256 r9 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, wordsOf (immStore v), (⟨9214⟩ : UInt256), UInt8.ofNat 32, .KECCAK256, none, morphoBlocks.immutableLayout_inBounds, morphoBlocks.immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.push1 (UInt256.ofNat 1) (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, wordsOf (immStore v), (⟨9215⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), morphoBlocks.immutableLayout_inBounds, morphoBlocks.immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.pushConst (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639680) (width := 32) (op := .PUSH32) (by decide) (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, wordsOf (immStore v), (⟨9217⟩ : UInt256), UInt8.ofNat 127, .Push .PUSH32, some ((UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639680), 32), morphoBlocks.immutableLayout_inBounds, morphoBlocks.immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.dup3 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, wordsOf (immStore v), (⟨9250⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, morphoBlocks.immutableLayout_inBounds, morphoBlocks.immutableTemplate_size64)) (by evm_ov)
  obtain ⟨_, _, r14⟩ := RD.sload r13 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, wordsOf (immStore v), (⟨9251⟩ : UInt256), UInt8.ofNat 84, .SLOAD, none, morphoBlocks.immutableLayout_inBounds, morphoBlocks.immutableTemplate_size64)) (by evm_ov)
  have r15 := r14.and (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, wordsOf (immStore v), (⟨9252⟩ : UInt256), UInt8.ofNat 22, .AND, none, morphoBlocks.immutableLayout_inBounds, morphoBlocks.immutableTemplate_size64)) (by evm_ov)
  have r16 := r15.or (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, wordsOf (immStore v), (⟨9253⟩ : UInt256), UInt8.ofNat 23, .OR, none, morphoBlocks.immutableLayout_inBounds, morphoBlocks.immutableTemplate_size64)) (by evm_ov)
  have r17 := r16.swap1 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, wordsOf (immStore v), (⟨9254⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, morphoBlocks.immutableLayout_inBounds, morphoBlocks.immutableTemplate_size64)) (by evm_ov)
  exact RD.sstoreStatic r17 hperm (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, wordsOf (immStore v), (⟨9255⟩ : UInt256), UInt8.ofNat 85, .SSTORE, none, morphoBlocks.immutableLayout_inBounds, morphoBlocks.immutableTemplate_size64)) (by evm_ov)

theorem morphoEnableLltvXSplit {σ σ₀ A I} {g : Sat256} (v : MorphoImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (morphoSelBytes 7))
    (hcv : I.weiValue = ⟨0⟩) (hlen : 36 ≤ I.calldata.size)
    (hbound : I.calldata.size < 2 ^ 255 + 4)
    (ho : solcSourceWord I = solcAddressSlotWord ⟨0⟩ σ I)
    (hdisabled : lltvEnabledByte σ I (calldataWord I.calldata 4) = ⟨0⟩)
    (hlimit : (calldataWord I.calldata 4).toNat < 1000000000000000000) :
    (I.perm = true ∧ RDret (deployedRuntime v) g (initState σ σ₀ g A I)
      (sstoreAccountMap I.codeOwner σ (solcMappingSlot ⟨5⟩ (calldataWord I.calldata 4))
        (UInt256.lor (UInt256.land (solcSlotWordAt (solcMappingSlot ⟨5⟩
          (calldataWord I.calldata 4)) σ I) (UInt256.lnot ⟨255⟩)) ⟨1⟩)) ByteArray.empty) ∨
    (I.perm = false ∧ RDstatic (deployedRuntime v) g (initState σ σ₀ g A I)) := by
  obtain ⟨aw, k, C, rd⟩ := morphoEnableLltvReachLimitCheck (g := g) (σ := σ) (σ₀ := σ₀)
    (A := A) v hcode hsize hsel hcv hlen hbound ho hdisabled
  have hc : UInt256.lt (calldataWord I.calldata 4) (UInt256.ofNat 1000000000000000000) = ⟨1⟩ :=
    ult_one hlimit
  obtain ⟨kt, Ct, rdStore⟩ := morphoRequireTrue (v := v) (by simp)
    (by rw [morphoPatchedValidJumps v]; jump_dest) (by rw [hc]; decide) rd
  by_cases hperm : I.perm = true
  · refine .inl ⟨hperm, ?_⟩
    have ret := morphoBlocks.morpho_block_9203 (immWords := wordsOf (immStore v)) (by decide) hperm rdStore
    let mem := twoWordHashMem (calldataWord I.calldata 4) (UInt256.ofNat 5)
      (lltvLimitMem (calldataWord I.calldata 4))
    change RDret _ _ _ (sstoreAccountMap I.codeOwner σ (keccakWord ⟨0⟩ (UInt256.ofNat 64) mem)
      (UInt256.lor (UInt256.land (solcSlotWordAt (keccakWord ⟨0⟩ (UInt256.ofNat 64) mem) σ I)
        (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639680))
        (UInt256.ofNat 1)))
      (((calldataWord I.calldata 4).toByteArray.write 0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32).readWithPadding 0 0) at ret
    have hslot : keccakWord ⟨0⟩ (UInt256.ofNat 64) mem =
        solcMappingSlot ⟨5⟩ (calldataWord I.calldata 4) := twoWordHashMem_solcMappingSlot_any _ _ _
    rw [hslot, byteArray_readWithPadding_zero] at ret
    have hmask : UInt256.lnot ⟨255⟩ =
        UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639680 := by native_decide
    rw [hmask]
    exact ret
  · have hp : I.perm = false := Bool.eq_false_of_not_eq_true hperm
    exact .inr ⟨hp, morphoEnableLltvStoreStatic (v := v) (by decide) hp rdStore⟩

set_option maxRecDepth 10000 in
theorem morphoEnableLltvXReverts {σ σ₀ A I} {g : Sat256} (v : MorphoImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (morphoSelBytes 7))
    (hbad : I.weiValue ≠ ⟨0⟩ ∨ I.calldata.size < 36 ∨ 2 ^ 255 + 4 ≤ I.calldata.size) :
    RDrev (deployedRuntime v) g (initState σ σ₀ g A I) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (morphoSelBytes 7) rfl hsel
  obtain ⟨k, C, rd⟩ := morphoReachEnableLltvBody (g := g) (σ := σ) (σ₀ := σ₀)
    (A := A) v hcode hsz hsize hsel
  have hvalid : (D_J (deployedRuntime v) 0).contains (UInt256.ofNat 440) = true := by
    rw [morphoPatchedValidJumps v]
    jump_dest
  by_cases hcv : I.weiValue = ⟨0⟩
  · have hlen := hbad.resolve_left (not_not.mpr hcv)
    have rdGuard := morphoBlocks.morpho_block_8981_fallthrough
      (immWords := wordsOf (immStore v)) (by decide) hcv rd
    have hcond : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) (UInt256.ofNat 32) = ⟨1⟩ := by
      rcases hlen with hshort | hbig
      · exact solcCalldataStaticLenCheckShort (words := 1) hsz hshort hsize (by norm_num)
      · exact solcCalldataStaticLenCheckHuge (words := 1) hbig hsize (by norm_num)
    have rdRevert := morphoBlocks.morpho_block_8988_taken
      (immWords := wordsOf (immStore v)) (by decide)
      (by rw [wordAddNegFour, hcond]; decide) hvalid rdGuard
    exact morphoBlocks.morpho_block_440 (immWords := wordsOf (immStore v)) (by decide) rdRevert
  · have rdRevert := morphoBlocks.morpho_block_8981_taken
      (immWords := wordsOf (immStore v)) (by decide) hcv hvalid rd
    exact morphoBlocks.morpho_block_440 (immWords := wordsOf (immStore v)) (by decide) rdRevert

/-- `enableLltv(uint256)`: the theorem `Correct.lean` routes selector 7 to. -/
theorem morphoEnableLltvBody {σ σ₀ A I} {g : UInt256} (v : MorphoImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (morphoSelBytes 7)) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (morphoSelBytes 7) rfl hsel
  have hd : selectorDispatchMsg contract I.calldata = some enableLltvTransition :=
    morphoSelectorDispatch_of_selIs (by decide) hsel
  by_cases hlen : 36 ≤ I.calldata.size
  · by_cases hbound : I.calldata.size < 2 ^ 255 + 4
    · have hdec : decodeCalldataWithMode config.abiDecodeMode
          (enableLltvTransition.params.map Param.name)
          (transitionSignature enableLltvTransition).paramTypes I.calldata =
          some (enableLltvArgs I.calldata) := decodeCalldata_uint256_ok hlen hbound
      by_cases hcv : I.weiValue = ⟨0⟩
      · by_cases hguards : solcSourceWord I = solcAddressSlotWord ⟨0⟩ σ I ∧
            lltvEnabledByte σ I (calldataWord I.calldata 4) = ⟨0⟩ ∧
            (calldataWord I.calldata 4).toNat < 1000000000000000000
        · rcases hguards with ⟨ho, hdisabled, hlimit⟩
          have hbody := morphoEnableLltvBodySplit v (initState σ σ₀ (.ofUInt256 g) A I)
            hcv hbound ho hdisabled hlimit
          rcases morphoEnableLltvXSplit (g := .ofUInt256 g) (σ₀ := σ₀) (A := A)
            v hcode hsize hsel hcv hlen hbound ho hdisabled hlimit with ⟨hp, hx⟩ | ⟨hp, hx⟩
          · exact reEquivSelectorExecutionGen hcode hx hd hdec hbody.1
              (by rw [storageStore_accountMap]; rfl) (.fallthrough rfl rfl (by native_decide))
          · exact reEquivSelectorStatic hcode hx hd hdec (hbody.2 hp)
        · have hbad : solcSourceWord I ≠ solcAddressSlotWord ⟨0⟩ σ I ∨
              lltvEnabledByte σ I (calldataWord I.calldata 4) ≠ ⟨0⟩ ∨
              ¬ (calldataWord I.calldata 4).toNat < 1000000000000000000 := by tauto
          exact reEquivSelectorRevert hcode
            (morphoEnableLltvXRejects v hcode hsize hsel hcv hlen hbound hbad) hd hdec
            (morphoEnableLltvBodyRejects v _ hcv hbound hbad)
      · exact reEquivSelectorRevert hcode
          (morphoEnableLltvXReverts v hcode hsize hsel (.inl hcv)) hd hdec
          (bodyReverts_nonPayable hcv)
    · exact reEquivSelectorDecodingFailed hcode
        (morphoEnableLltvXReverts v hcode hsize hsel (.inr (.inr (by omega)))) hd
        (decodeCalldata_uint256_none_huge (by omega))
  · exact reEquivSelectorDecodingFailed hcode
      (morphoEnableLltvXReverts v hcode hsize hsel (.inr (.inl (by omega)))) hd
      (decodeCalldata_uint256_none_short (by omega))

end Benchmarks.Morpho.MorphoBlue
