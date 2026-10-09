import Benchmarks.Morpho.MorphoBlue.ErrorRoutines
import Benchmarks.Morpho.MorphoBlue.AdminCommon

/-!
# Morpho `setAuthorization(address,bool)`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Solm body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 443; reach lemma `morphoReachSetAuthorizationBody`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables

namespace Benchmarks.Morpho.MorphoBlue

set_option maxRecDepth 1000

def setAuthorizationArgs (cd : ByteArray) : Store :=
  ((∅ : Store).insert "authorized" (.address (AccountAddress.ofNat (calldataWord cd 4).toNat))).insert
    "newIsAuthorized" (wordToElem .bool (calldataWord cd 36))

def setAuthorizationFrame (v : MorphoImmutables) (cd : ByteArray) : Frame :=
  addressAdminFrame v (setAuthorizationArgs cd) cd

theorem setAuthorizationAddress_eval (v : MorphoImmutables) (cd : ByteArray) (evm : EVM.State) :
    evalExpr? config (setAuthorizationFrame v cd) evm (.var "authorized") =
      .ok (.address (AccountAddress.ofNat (calldataWord cd 4).toNat)) := by
  simp only [evalExpr?, setAuthorizationFrame, addressAdminFrame, setAuthorizationArgs,
    store_get_ne (k := "__calldata") (a := "authorized") _ _ (by decide),
    store_get_ne (k := "newIsAuthorized") (a := "authorized") _ _ (by decide),
    store_get_self, EvalResult.ofOption]

theorem setAuthorizationBool_eval (v : MorphoImmutables) (cd : ByteArray) (evm : EVM.State) :
    evalExpr? config (setAuthorizationFrame v cd) evm (.var "newIsAuthorized") =
      .ok (wordToElem .bool (calldataWord cd 36)) := by
  simp only [evalExpr?, setAuthorizationFrame, addressAdminFrame, setAuthorizationArgs,
    store_get_ne (k := "__calldata") (a := "newIsAuthorized") _ _ (by decide),
    store_get_self, EvalResult.ofOption]

def setAuthorizationOld (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.isZero (UInt256.isZero (UInt256.land (solcSlotWordAt
    (authorizationSlot (solcSourceWord I) (calldataWord I.calldata 4)) σ I) ⟨255⟩))

theorem setAuthorizationGuard_eval (v : MorphoImmutables) (evm : EVM.State)
    (hcanon : (calldataWord evm.executionEnv.calldata 4).toNat < EVM.addressModulus) :
    evalExpr? config (setAuthorizationFrame v evm.executionEnv.calldata) evm
      (.binary .ne (.var "newIsAuthorized")
        (.storage ⟨"isAuthorized", [.mindex (.env .caller), .mindex (.var "authorized")]⟩)) =
      .ok (.bool (decide (UInt256.isZero (UInt256.isZero (calldataWord evm.executionEnv.calldata 36)) ≠
        setAuthorizationOld evm.accountMap evm.executionEnv))) := by
  have hload := evalMorphoIsAuthorized evm (setAuthorizationFrame v evm.executionEnv.calldata).locals
    (immStore v) (.env .caller) (.var "authorized") _ _
    (by simp [setAuthorizationFrame, addressAdminFrame, setAuthorizationArgs])
    (evalCallerWord config _ evm) (setAuthorizationAddress_eval v _ evm)
    (solcSourceWord_canonical _) hcanon
  exact evalBoolWordNe (setAuthorizationBool_eval v _ evm) hload

theorem morphoSetAuthorizationBodySplit (v : MorphoImmutables) (evm : EVM.State)
    (hcv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsize : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (hcanon : (calldataWord evm.executionEnv.calldata 4).toNat < EVM.addressModulus)
    (hne : UInt256.isZero (UInt256.isZero (calldataWord evm.executionEnv.calldata 36)) ≠
      setAuthorizationOld evm.accountMap evm.executionEnv) :
    ExecTransitionBody config contract evm (setAuthorizationArgs evm.executionEnv.calldata)
      setAuthorizationTransition.body
      (.returned (setAuthorizationFrame v evm.executionEnv.calldata)
        (Solm.EVM.storageStore evm evm.executionEnv.codeOwner
          (authorizationSlot (solcSourceWord evm.executionEnv) (calldataWord evm.executionEnv.calldata 4))
          (setBoolOffset0Word (solcSlotWordAt
            (authorizationSlot (solcSourceWord evm.executionEnv) (calldataWord evm.executionEnv.calldata 4))
            evm.accountMap evm.executionEnv) (calldataWord evm.executionEnv.calldata 36))) none) (immStore v) ∧
    (evm.executionEnv.perm = false →
      ExecTransitionBody config contract evm (setAuthorizationArgs evm.executionEnv.calldata)
        setAuthorizationTransition.body .staticViolation (immStore v)) := by
  have hprefix : ABlock config evm
      { contract := contract, locals := setAuthorizationArgs evm.executionEnv.calldata, immutables := immStore v }
      setAuthorizationTransition.body (setAuthorizationFrame v evm.executionEnv.calldata)
      (setAuthorizationTransition.body.drop 4) :=
    (calldataPrelude_ok hcv hsize).requireStep
      (by simpa only [ne_eq, hne, not_false_eq_true, decide_true] using setAuthorizationGuard_eval v evm hcanon)
  have hassign := assignMorphoIsAuthorized evm (setAuthorizationFrame v evm.executionEnv.calldata).locals
    (immStore v) (.env .caller) (.var "authorized") _ _ (calldataWord evm.executionEnv.calldata 36)
    (by simp [setAuthorizationFrame, addressAdminFrame, setAuthorizationArgs])
    (evalCallerWord config _ evm) (setAuthorizationAddress_eval v _ evm)
    (solcSourceWord_canonical _) hcanon
  constructor
  · apply ExecFuncBody.execBlockOK
    apply hprefix.run
    apply ExecBlock.consNormal (ExecStmt.assign (setAuthorizationBool_eval v _ evm) hassign)
    apply ExecBlock.consNormal
    · apply ExecStmt.emit (vals := [.address evm.executionEnv.source, .address evm.executionEnv.source,
        .address (AccountAddress.ofNat (calldataWord evm.executionEnv.calldata 4).toNat),
        wordToElem .bool (calldataWord evm.executionEnv.calldata 36)])
      change evalExprs? config (setAuthorizationFrame v evm.executionEnv.calldata) _ _ = _
      simp only [evalExprs?, setAuthorizationAddress_eval, setAuthorizationBool_eval,
        evalExpr?, envValue, pure, bind, EvalResult.bind, storageStore_executionEnv]
    · exact ExecBlock.nil
  · intro hperm
    exact ExecFuncBody.execBlockStatic (hprefix.run (ExecBlock.consStatic
      (ExecStmt.assignStatic (setAuthorizationBool_eval v _ evm) hassign hperm)))

theorem morphoSetAuthorizationBodyRejects (v : MorphoImmutables) (evm : EVM.State)
    (hcv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsize : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (hcanon : (calldataWord evm.executionEnv.calldata 4).toNat < EVM.addressModulus)
    (heq : UInt256.isZero (UInt256.isZero (calldataWord evm.executionEnv.calldata 36)) =
      setAuthorizationOld evm.accountMap evm.executionEnv) :
    ExecTransitionBody config contract evm (setAuthorizationArgs evm.executionEnv.calldata)
      setAuthorizationTransition.body .reverted (immStore v) := by
  apply ExecFuncBody.execBlockRevert
  exact (calldataPrelude_ok hcv hsize).requireRevert
    (by simpa only [heq, ne_eq, not_true_eq_false, decide_false] using setAuthorizationGuard_eval v evm hcanon)

theorem morphoSetAuthorizationReachDecode {σ σ₀ A I} {g : Sat256} (v : MorphoImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (morphoSelBytes 25))
    (hcv : I.weiValue = ⟨0⟩) (hlen : 68 ≤ I.calldata.size)
    (hbound : I.calldata.size < 2 ^ 255 + 4) :
    ∃ k C, RD (deployedRuntime v) I g (initState σ σ₀ g A I) (UInt256.ofNat 11354)
      [UInt256.ofNat 499, ⟨0⟩]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C := by
  obtain ⟨k, C, rd⟩ := morphoReachSetAuthorizationBody (g := g) (σ := σ) (σ₀ := σ₀)
    (A := A) v hcode (by omega) hsize hsel
  have rdGuard := morphoBlocks.morpho_block_443_fallthrough
    (immWords := wordsOf (immStore v)) (by decide) hcv rd
  have hcond := solcCalldataStaticLenCheckOk (words := 2) hlen hbound hsize
  have rdCall := morphoBlocks.morpho_block_450_fallthrough
    (immWords := wordsOf (immStore v)) (by decide)
    (by simpa only [wordAddNegFour] using hcond) rdGuard
  have rdDecode := morphoBlocks.morpho_block_492
    (immWords := wordsOf (immStore v)) (by decide)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rdCall
  exact ⟨_, _, rdDecode⟩

def setAuthorizationCheckMem (I : ExecutionEnv) : ByteArray :=
  nestedMappingMem ⟨6⟩ (solcSourceWord I) (calldataWord I.calldata 4) solcFreePtrMem

theorem setAuthorizationCheckMem_size (I : ExecutionEnv) : (setAuthorizationCheckMem I).size = 96 := by
  rw [setAuthorizationCheckMem, nestedMappingMem_size _ _ _ _ (by native_decide)]
  exact solcFreePtrMem_size

theorem setAuthorizationCheckMem_load64 (I : ExecutionEnv) :
    memLoad (UInt256.ofNat 64) (setAuthorizationCheckMem I) = UInt256.ofNat 128 := by
  rw [setAuthorizationCheckMem, nestedMappingMem_load64 _ _ _ _ (by native_decide)]
  exact solcFreePtrMem_mload64

theorem setAuthorizationCheckMem_length (I : ExecutionEnv) :
    morphoErrorLength (morphoAlreadySetMem (setAuthorizationCheckMem I)) (UInt256.ofNat 128) = UInt256.ofNat 11 :=
  (morphoErrorMem_properties_of_gap _ _ (UInt256.ofNat 128) _
    (by rw [setAuthorizationCheckMem_size]; decide) (setAuthorizationCheckMem_load64 I)
    (by rw [setAuthorizationCheckMem_size])
    (by rw [setAuthorizationCheckMem_size]; exact lt_usize _ (by decide)) (by decide)).2.2

theorem morphoSetAuthorizationReachCheck {σ σ₀ A I} {g : Sat256} (v : MorphoImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (morphoSelBytes 25))
    (hcv : I.weiValue = ⟨0⟩) (hlen : 68 ≤ I.calldata.size)
    (hbound : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (calldataWord I.calldata 4).toNat < EVM.addressModulus)
    (hbool : calldataWord I.calldata 36 = ⟨0⟩ ∨ calldataWord I.calldata 36 = ⟨1⟩) :
    ∃ aw k C, RD (deployedRuntime v) I g (initState σ σ₀ g A I) (UInt256.ofNat 12097)
      [UInt256.isZero (UInt256.eq (UInt256.isZero (UInt256.isZero (calldataWord I.calldata 36)))
        (setAuthorizationOld σ I)), UInt256.ofNat 128, UInt256.ofNat 591,
       calldataWord I.calldata 36, UInt256.ofNat 663,
       UInt256.isZero (UInt256.isZero (calldataWord I.calldata 36)), calldataWord I.calldata 4, ⟨0⟩]
      (morphoAlreadySetMem (setAuthorizationCheckMem I)) aw ByteArray.empty σ k C := by
  obtain ⟨k, C, rd⟩ := morphoSetAuthorizationReachDecode (g := g) (σ := σ) (σ₀ := σ₀)
    (A := A) v hcode hsize hsel hcv hlen hbound
  obtain ⟨ka, Ca, rdBool⟩ := morphoDecodeAddress4Ok (v := v) (by simp)
    (by rw [morphoPatchedValidJumps v]; jump_dest) hcanon rd
  have rdBody := morphoBlocks.morpho_block_499_fallthrough
    (immWords := wordsOf (immStore v)) (by simp)
    (by change UInt256.sub (calldataWord I.calldata 36) (UInt256.isZero (UInt256.isZero (calldataWord I.calldata 36))) = _
        rw [(boolWordClean_iff _).mpr hbool, u256_sub_self]; rfl) rdBool
  obtain ⟨kb, Cb, rdMessage⟩ := morphoBlocks.morpho_block_514
    (immWords := wordsOf (immStore v)) (by simp)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rdBody
  change RD _ _ _ _ _
    [UInt256.ofNat 585, UInt256.isZero (UInt256.eq (UInt256.isZero (UInt256.isZero (calldataWord I.calldata 36)))
      (UInt256.isZero (UInt256.isZero (UInt256.land (solcSlotWordAt
        (keccakWord ⟨0⟩ (UInt256.ofNat 64) (nestedMappingMem ⟨6⟩ (solcSourceWord I)
          (UInt256.land (calldataWord I.calldata 4) solcAddrMask) solcFreePtrMem)) σ I) (UInt256.ofNat 255))))),
     UInt256.ofNat 591, calldataWord I.calldata 36, UInt256.ofNat 663,
     UInt256.isZero (UInt256.isZero (calldataWord I.calldata 36)),
     UInt256.land (calldataWord I.calldata 4) solcAddrMask, ⟨0⟩]
    (nestedMappingMem ⟨6⟩ (solcSourceWord I) (UInt256.land (calldataWord I.calldata 4) solcAddrMask)
      solcFreePtrMem) _ _ _ _ _ at rdMessage
  rw [solcAddrMask_clean hcanon, nestedMappingMem_hash] at rdMessage
  obtain ⟨aw, km, Cm, rdCheck⟩ := morphoAlreadySetMessage (v := v) (by simp)
    (by rw [morphoPatchedValidJumps v]; jump_dest)
    (by change UInt256.lor (UInt256.gt (memLoad (UInt256.ofNat 64) (setAuthorizationCheckMem I) + UInt256.ofNat 64) _)
          (UInt256.lt (memLoad (UInt256.ofNat 64) (setAuthorizationCheckMem I) + UInt256.ofNat 64)
            (memLoad (UInt256.ofNat 64) (setAuthorizationCheckMem I))) = _
        rw [setAuthorizationCheckMem_load64]; native_decide) rdMessage
  have rdRequire := morphoBlocks.morpho_block_585
    (immWords := wordsOf (immStore v)) (by simp)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rdCheck
  have hptr : memLoad (UInt256.ofNat 64)
      (nestedMappingMem ⟨6⟩ (solcSourceWord I) (calldataWord I.calldata 4) solcFreePtrMem) = UInt256.ofNat 128 :=
    setAuthorizationCheckMem_load64 I
  exact ⟨_, _, _, by simpa only [morphoBlocks.morpho_block_585_stack, hptr] using rdRequire⟩

theorem morphoSetAuthorizationXRejects {σ σ₀ A I} {g : Sat256} (v : MorphoImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (morphoSelBytes 25))
    (hcv : I.weiValue = ⟨0⟩) (hlen : 68 ≤ I.calldata.size)
    (hbound : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (calldataWord I.calldata 4).toNat < EVM.addressModulus)
    (hbool : calldataWord I.calldata 36 = ⟨0⟩ ∨ calldataWord I.calldata 36 = ⟨1⟩)
    (heq : UInt256.isZero (UInt256.isZero (calldataWord I.calldata 36)) = setAuthorizationOld σ I) :
    RDrev (deployedRuntime v) g (initState σ σ₀ g A I) := by
  obtain ⟨aw, k, C, rd⟩ := morphoSetAuthorizationReachCheck (g := g) (σ := σ) (σ₀ := σ₀)
    (A := A) v hcode hsize hsel hcv hlen hbound hcanon hbool
  exact morphoRequireFalseShort (v := v) (by simp)
    (by rw [heq, uInt256_eq_self]; decide)
    (by rw [setAuthorizationCheckMem_length]; decide) (by rw [setAuthorizationCheckMem_length]; decide) rd

-- The provided summary assumes write permission; this prefix covers the static halt.
theorem morphoSetAuthorizationStoreStatic {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {σ : AccountMap} {k C : Nat} {value ret norm key zero : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024) (hperm : ee.perm = false)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 591)
      (value :: ret :: norm :: key :: zero :: R) mem aw rdata σ k C) :
    RDstatic (deployedRuntime v) g s0 := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, wordsOf (immStore v), (⟨591⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, morphoBlocks.immutableLayout_inBounds, morphoBlocks.immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.caller (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, wordsOf (immStore v), (⟨592⟩ : UInt256), UInt8.ofNat 51, .CALLER, none, morphoBlocks.immutableLayout_inBounds, morphoBlocks.immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.dup6 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, wordsOf (immStore v), (⟨593⟩ : UInt256), UInt8.ofNat 133, .DUP6, none, morphoBlocks.immutableLayout_inBounds, morphoBlocks.immutableTemplate_size64)) (by evm_ov)
  have r4 := RD.genMstore r3 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, wordsOf (immStore v), (⟨594⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, morphoBlocks.immutableLayout_inBounds, morphoBlocks.immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 6) (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, wordsOf (immStore v), (⟨595⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 6), 1), morphoBlocks.immutableLayout_inBounds, morphoBlocks.immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 32) (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, wordsOf (immStore v), (⟨597⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 32), 1), morphoBlocks.immutableLayout_inBounds, morphoBlocks.immutableTemplate_size64)) (by evm_ov)
  have r7 := RD.genMstore r6 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, wordsOf (immStore v), (⟨599⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, morphoBlocks.immutableLayout_inBounds, morphoBlocks.immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 64) (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, wordsOf (immStore v), (⟨600⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1), morphoBlocks.immutableLayout_inBounds, morphoBlocks.immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.dup6 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, wordsOf (immStore v), (⟨602⟩ : UInt256), UInt8.ofNat 133, .DUP6, none, morphoBlocks.immutableLayout_inBounds, morphoBlocks.immutableTemplate_size64)) (by evm_ov)
  have r10 := RD.genKeccak256 r9 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, wordsOf (immStore v), (⟨603⟩ : UInt256), UInt8.ofNat 32, .KECCAK256, none, morphoBlocks.immutableLayout_inBounds, morphoBlocks.immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.dup5 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, wordsOf (immStore v), (⟨604⟩ : UInt256), UInt8.ofNat 132, .DUP5, none, morphoBlocks.immutableLayout_inBounds, morphoBlocks.immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.push1 (UInt256.ofNat 0) (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, wordsOf (immStore v), (⟨605⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 0), 1), morphoBlocks.immutableLayout_inBounds, morphoBlocks.immutableTemplate_size64)) (by evm_ov)
  have r13 := RD.genMstore r12 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, wordsOf (immStore v), (⟨607⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, morphoBlocks.immutableLayout_inBounds, morphoBlocks.immutableTemplate_size64)) (by evm_ov)
  have r14 := r13.push1 (UInt256.ofNat 32) (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, wordsOf (immStore v), (⟨608⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 32), 1), morphoBlocks.immutableLayout_inBounds, morphoBlocks.immutableTemplate_size64)) (by evm_ov)
  have r15 := RD.genMstore r14 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, wordsOf (immStore v), (⟨610⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, morphoBlocks.immutableLayout_inBounds, morphoBlocks.immutableTemplate_size64)) (by evm_ov)
  have r16 := r15.push1 (UInt256.ofNat 64) (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, wordsOf (immStore v), (⟨611⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1), morphoBlocks.immutableLayout_inBounds, morphoBlocks.immutableTemplate_size64)) (by evm_ov)
  have r17 := r16.push1 (UInt256.ofNat 0) (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, wordsOf (immStore v), (⟨613⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 0), 1), morphoBlocks.immutableLayout_inBounds, morphoBlocks.immutableTemplate_size64)) (by evm_ov)
  have r18 := RD.genKeccak256 r17 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, wordsOf (immStore v), (⟨615⟩ : UInt256), UInt8.ofNat 32, .KECCAK256, none, morphoBlocks.immutableLayout_inBounds, morphoBlocks.immutableTemplate_size64)) (by evm_ov)
  have r19 := r18.swap1 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, wordsOf (immStore v), (⟨616⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, morphoBlocks.immutableLayout_inBounds, morphoBlocks.immutableTemplate_size64)) (by evm_ov)
  have r20 := r19.push1 (UInt256.ofNat 255) (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, wordsOf (immStore v), (⟨617⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 255), 1), morphoBlocks.immutableLayout_inBounds, morphoBlocks.immutableTemplate_size64)) (by evm_ov)
  have r21 := r20.pushConst (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639680) (width := 32) (op := .PUSH32) (by decide) (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, wordsOf (immStore v), (⟨619⟩ : UInt256), UInt8.ofNat 127, .Push .PUSH32, some ((UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639680), 32), morphoBlocks.immutableLayout_inBounds, morphoBlocks.immutableTemplate_size64)) (by evm_ov)
  have r22 := r21.dup4 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, wordsOf (immStore v), (⟨652⟩ : UInt256), UInt8.ofNat 131, .DUP4, none, morphoBlocks.immutableLayout_inBounds, morphoBlocks.immutableTemplate_size64)) (by evm_ov)
  obtain ⟨_, _, r23⟩ := RD.sload r22 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, wordsOf (immStore v), (⟨653⟩ : UInt256), UInt8.ofNat 84, .SLOAD, none, morphoBlocks.immutableLayout_inBounds, morphoBlocks.immutableTemplate_size64)) (by evm_ov)
  have r24 := r23.and (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, wordsOf (immStore v), (⟨654⟩ : UInt256), UInt8.ofNat 22, .AND, none, morphoBlocks.immutableLayout_inBounds, morphoBlocks.immutableTemplate_size64)) (by evm_ov)
  have r25 := r24.swap2 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, wordsOf (immStore v), (⟨655⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none, morphoBlocks.immutableLayout_inBounds, morphoBlocks.immutableTemplate_size64)) (by evm_ov)
  have r26 := r25.iszero (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, wordsOf (immStore v), (⟨656⟩ : UInt256), UInt8.ofNat 21, .ISZERO, none, morphoBlocks.immutableLayout_inBounds, morphoBlocks.immutableTemplate_size64)) (by evm_ov)
  have r27 := r26.iszero (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, wordsOf (immStore v), (⟨657⟩ : UInt256), UInt8.ofNat 21, .ISZERO, none, morphoBlocks.immutableLayout_inBounds, morphoBlocks.immutableTemplate_size64)) (by evm_ov)
  have r28 := r27.and (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, wordsOf (immStore v), (⟨658⟩ : UInt256), UInt8.ofNat 22, .AND, none, morphoBlocks.immutableLayout_inBounds, morphoBlocks.immutableTemplate_size64)) (by evm_ov)
  have r29 := r28.or (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, wordsOf (immStore v), (⟨659⟩ : UInt256), UInt8.ofNat 23, .OR, none, morphoBlocks.immutableLayout_inBounds, morphoBlocks.immutableTemplate_size64)) (by evm_ov)
  have r30 := r29.swap1 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, wordsOf (immStore v), (⟨660⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, morphoBlocks.immutableLayout_inBounds, morphoBlocks.immutableTemplate_size64)) (by evm_ov)
  exact RD.sstoreStatic r30 hperm (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, wordsOf (immStore v), (⟨661⟩ : UInt256), UInt8.ofNat 85, .SSTORE, none, morphoBlocks.immutableLayout_inBounds, morphoBlocks.immutableTemplate_size64)) (by evm_ov)

theorem morphoSetAuthorizationXSplit {σ σ₀ A I} {g : Sat256} (v : MorphoImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (morphoSelBytes 25))
    (hcv : I.weiValue = ⟨0⟩) (hlen : 68 ≤ I.calldata.size)
    (hbound : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (calldataWord I.calldata 4).toNat < EVM.addressModulus)
    (hbool : calldataWord I.calldata 36 = ⟨0⟩ ∨ calldataWord I.calldata 36 = ⟨1⟩)
    (hne : UInt256.isZero (UInt256.isZero (calldataWord I.calldata 36)) ≠ setAuthorizationOld σ I) :
    (I.perm = true ∧ RDret (deployedRuntime v) g (initState σ σ₀ g A I)
      (sstoreAccountMap I.codeOwner σ (authorizationSlot (solcSourceWord I) (calldataWord I.calldata 4))
        (setBoolOffset0Word (solcSlotWordAt (authorizationSlot (solcSourceWord I)
          (calldataWord I.calldata 4)) σ I) (calldataWord I.calldata 36))) ByteArray.empty) ∨
    (I.perm = false ∧ RDstatic (deployedRuntime v) g (initState σ σ₀ g A I)) := by
  obtain ⟨aw, k, C, rd⟩ := morphoSetAuthorizationReachCheck (g := g) (σ := σ) (σ₀ := σ₀)
    (A := A) v hcode hsize hsel hcv hlen hbound hcanon hbool
  obtain ⟨kt, Ct, rdStore⟩ := morphoRequireTrue (v := v) (by simp)
    (by rw [morphoPatchedValidJumps v]; jump_dest) (by rw [u256_eq_of_ne hne]; decide) rd
  by_cases hperm : I.perm = true
  · refine .inl ⟨hperm, ?_⟩
    obtain ⟨kw, Cw, rdEvent⟩ := morphoBlocks.morpho_block_591
      (immWords := wordsOf (immStore v)) (by decide) hperm
      (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rdStore
    have ret := morphoBlocks.morpho_block_663 (immWords := wordsOf (immStore v)) (by decide) hperm rdEvent
    let mem := nestedMappingMem ⟨6⟩ (solcSourceWord I) (calldataWord I.calldata 4)
      (morphoAlreadySetMem (setAuthorizationCheckMem I))
    change RDret _ _ _ (sstoreAccountMap I.codeOwner σ (keccakWord ⟨0⟩ (UInt256.ofNat 64) mem)
      (UInt256.lor (UInt256.land (UInt256.isZero (UInt256.isZero (calldataWord I.calldata 36))) ⟨255⟩)
        (UInt256.land (solcSlotWordAt (keccakWord ⟨0⟩ (UInt256.ofNat 64) mem) σ I)
          (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639680))))
      (((UInt256.isZero (UInt256.isZero (calldataWord I.calldata 36))).toByteArray.write 0 mem
        (memLoad (UInt256.ofNat 64) mem).toNat 32).readWithPadding 0 0) at ret
    have hslot : keccakWord ⟨0⟩ (UInt256.ofNat 64) mem =
        authorizationSlot (solcSourceWord I) (calldataWord I.calldata 4) := nestedMappingMem_hash _ _ _ _
    rw [hslot, byteArray_readWithPadding_zero, boolWordClean_land255] at ret
    have hmask : UInt256.lnot ⟨255⟩ =
        UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639680 := by native_decide
    simpa only [setBoolOffset0Word, hmask, u256_lor_comm] using ret
  · have hp : I.perm = false := Bool.eq_false_of_not_eq_true hperm
    exact .inr ⟨hp, morphoSetAuthorizationStoreStatic (v := v) (by decide) hp rdStore⟩

set_option maxRecDepth 10000 in
theorem morphoSetAuthorizationXReverts {σ σ₀ A I} {g : Sat256} (v : MorphoImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (morphoSelBytes 25))
    (hbad : I.weiValue ≠ ⟨0⟩ ∨ I.calldata.size < 68 ∨ 2 ^ 255 + 4 ≤ I.calldata.size) :
    RDrev (deployedRuntime v) g (initState σ σ₀ g A I) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (morphoSelBytes 25) rfl hsel
  obtain ⟨k, C, rd⟩ := morphoReachSetAuthorizationBody (g := g) (σ := σ) (σ₀ := σ₀)
    (A := A) v hcode hsz hsize hsel
  have hvalid : (D_J (deployedRuntime v) 0).contains (UInt256.ofNat 440) = true := by
    rw [morphoPatchedValidJumps v]
    jump_dest
  by_cases hcv : I.weiValue = ⟨0⟩
  · have hlen := hbad.resolve_left (not_not.mpr hcv)
    have rdGuard := morphoBlocks.morpho_block_443_fallthrough
      (immWords := wordsOf (immStore v)) (by decide) hcv rd
    have hcond : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) (UInt256.ofNat 64) = ⟨1⟩ := by
      rcases hlen with hshort | hbig
      · exact solcCalldataStaticLenCheckShort (words := 2) hsz hshort hsize (by norm_num)
      · exact solcCalldataStaticLenCheckHuge (words := 2) hbig hsize (by norm_num)
    have rdRevert := morphoBlocks.morpho_block_450_taken
      (immWords := wordsOf (immStore v)) (by decide)
      (by rw [wordAddNegFour, hcond]; decide) hvalid rdGuard
    exact morphoBlocks.morpho_block_440 (immWords := wordsOf (immStore v)) (by decide) rdRevert
  · have rdRevert := morphoBlocks.morpho_block_443_taken
      (immWords := wordsOf (immStore v)) (by decide) hcv hvalid rd
    exact morphoBlocks.morpho_block_440 (immWords := wordsOf (immStore v)) (by decide) rdRevert

theorem morphoSetAuthorizationXNoncanonical {σ σ₀ A I} {g : Sat256} (v : MorphoImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (morphoSelBytes 25)) (hlen : 68 ≤ I.calldata.size)
    (hbound : I.calldata.size < 2 ^ 255 + 4)
    (hnc : ¬ ((calldataWord I.calldata 4).toNat < EVM.addressModulus ∧
      (calldataWord I.calldata 36 = ⟨0⟩ ∨ calldataWord I.calldata 36 = ⟨1⟩))) :
    RDrev (deployedRuntime v) g (initState σ σ₀ g A I) := by
  by_cases hcv : I.weiValue = ⟨0⟩
  · obtain ⟨k, C, rd⟩ := morphoSetAuthorizationReachDecode (g := g) (σ := σ) (σ₀ := σ₀)
      (A := A) v hcode hsize hsel hcv hlen hbound
    by_cases hc : (calldataWord I.calldata 4).toNat < EVM.addressModulus
    · obtain ⟨ka, Ca, rdBool⟩ := morphoDecodeAddress4Ok (v := v) (by simp)
        (by rw [morphoPatchedValidJumps v]; jump_dest) hc rd
      have rdRev := morphoBlocks.morpho_block_499_taken
        (immWords := wordsOf (immStore v)) (by simp)
        (by apply u256_sub_ne_zero_of_ne
            intro heq
            exact hnc ⟨hc, (boolWordClean_iff _).mp heq.symm⟩)
        (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rdBool
      exact morphoBlocks.morpho_block_712 (immWords := wordsOf (immStore v)) (by simp [morphoBlocks.morpho_block_499_taken_stack]) rdRev
    · exact morphoDecodeAddress4Revert (v := v) (by decide) hc rd
  · exact morphoSetAuthorizationXReverts v hcode hsize hsel (.inl hcv)

/-- `setAuthorization(address,bool)`: the theorem `Correct.lean` routes selector 25 to. -/
theorem morphoSetAuthorizationBody {σ σ₀ A I} {g : UInt256} (v : MorphoImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (morphoSelBytes 25)) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (morphoSelBytes 25) rfl hsel
  have hd : selectorDispatchMsg contract I.calldata = some setAuthorizationTransition :=
    morphoSelectorDispatch_of_selIs (by decide) hsel
  by_cases hlen : 68 ≤ I.calldata.size
  · by_cases hbound : I.calldata.size < 2 ^ 255 + 4
    · by_cases hcanon : (calldataWord I.calldata 4).toNat < EVM.addressModulus ∧
          (calldataWord I.calldata 36 = ⟨0⟩ ∨ calldataWord I.calldata 36 = ⟨1⟩)
      · have hdec : decodeCalldataWithMode config.abiDecodeMode
            (setAuthorizationTransition.params.map Param.name)
            (transitionSignature setAuthorizationTransition).paramTypes I.calldata =
            some (setAuthorizationArgs I.calldata) := decodeCalldata_addr_bool_ok hlen hbound hcanon.1 hcanon.2
        by_cases hcv : I.weiValue = ⟨0⟩
        · by_cases hne : UInt256.isZero (UInt256.isZero (calldataWord I.calldata 36)) ≠ setAuthorizationOld σ I
          · have hbody := morphoSetAuthorizationBodySplit v (initState σ σ₀ (.ofUInt256 g) A I)
              hcv hbound hcanon.1 hne
            rcases morphoSetAuthorizationXSplit (g := .ofUInt256 g) (σ₀ := σ₀) (A := A)
              v hcode hsize hsel hcv hlen hbound hcanon.1 hcanon.2 hne with ⟨hp, hx⟩ | ⟨hp, hx⟩
            · exact reEquivSelectorExecutionGen hcode hx hd hdec hbody.1
                (by rw [storageStore_accountMap]; rfl) (.fallthrough rfl rfl (by native_decide))
            · exact reEquivSelectorStatic hcode hx hd hdec (hbody.2 hp)
          · have heq := not_not.mp hne
            exact reEquivSelectorRevert hcode
              (morphoSetAuthorizationXRejects v hcode hsize hsel hcv hlen hbound hcanon.1 hcanon.2 heq) hd hdec
              (morphoSetAuthorizationBodyRejects v _ hcv hbound hcanon.1 heq)
        · exact reEquivSelectorRevert hcode
            (morphoSetAuthorizationXReverts v hcode hsize hsel (.inl hcv)) hd hdec
            (bodyReverts_nonPayable hcv)
      · apply reEquivSelectorDecodingFailed hcode
          (morphoSetAuthorizationXNoncanonical v hcode hsize hsel hlen hbound hcanon) hd
        by_cases hc : (calldataWord I.calldata 4).toNat < EVM.addressModulus
        · exact decodeCalldata_addr_bool_none_noncanon_bool hlen hbound hc
            (fun hz => hcanon ⟨hc, .inl hz⟩) (fun ho => hcanon ⟨hc, .inr ho⟩)
        · exact decodeCalldata_addr_bool_none_noncanon_addr hlen hbound hc
    · exact reEquivSelectorDecodingFailed hcode
        (morphoSetAuthorizationXReverts v hcode hsize hsel (.inr (.inr (by omega)))) hd
        (decodeCalldata_addr_bool_none_huge (by omega))
  · exact reEquivSelectorDecodingFailed hcode
      (morphoSetAuthorizationXReverts v hcode hsize hsel (.inr (.inl (by omega)))) hd
      (decodeCalldata_addr_bool_none_short hsz (by omega))

end Benchmarks.Morpho.MorphoBlue
