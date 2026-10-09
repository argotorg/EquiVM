import Benchmarks.Morpho.MorphoBlue.ErrorRoutines
import Benchmarks.Morpho.MorphoBlue.AdminCommon

/-!
# Morpho `enableIrm(address)`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Solm body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 8105; reach lemma `morphoReachEnableIrmBody`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables

namespace Benchmarks.Morpho.MorphoBlue

set_option maxRecDepth 2000000

def enableIrmArgs (cd : ByteArray) : Store :=
  (∅ : Store).insert "irm" (.address (AccountAddress.ofNat (calldataWord cd 4).toNat))

def enableIrmFrame (v : MorphoImmutables) (cd : ByteArray) : Frame :=
  addressAdminFrame v (enableIrmArgs cd) cd

theorem enableIrmArg_eval (v : MorphoImmutables) (cd : ByteArray) (evm : EVM.State) :
    evalExpr? config (enableIrmFrame v cd) evm (.var "irm") =
      .ok (.address (AccountAddress.ofNat (calldataWord cd 4).toNat)) := by
  simp only [evalExpr?, enableIrmFrame, addressAdminFrame, enableIrmArgs,
    store_get_ne (k := "__calldata") (a := "irm") _ _ (by decide), store_get_self, EvalResult.ofOption]

def irmEnabledByte (σ : AccountMap) (I : ExecutionEnv) (w : UInt256) : UInt256 :=
  UInt256.land (solcSlotWordAt (solcMappingSlot ⟨4⟩ w) σ I) ⟨255⟩

theorem morphoEnableIrmBodySplit (v : MorphoImmutables) (evm : EVM.State)
    (hcv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsize : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (hcanon : (calldataWord evm.executionEnv.calldata 4).toNat < EVM.addressModulus)
    (ho : solcSourceWord evm.executionEnv = solcAddressSlotWord ⟨0⟩ evm.accountMap evm.executionEnv)
    (hdisabled : irmEnabledByte evm.accountMap evm.executionEnv
      (calldataWord evm.executionEnv.calldata 4) = ⟨0⟩) :
    ExecTransitionBody config contract evm (enableIrmArgs evm.executionEnv.calldata)
      enableIrmTransition.body
      (.returned (enableIrmFrame v evm.executionEnv.calldata)
        (Solm.EVM.storageStore evm evm.executionEnv.codeOwner
          (solcMappingSlot ⟨4⟩ (calldataWord evm.executionEnv.calldata 4))
          (UInt256.lor (UInt256.land (solcSlotWordAt
            (solcMappingSlot ⟨4⟩ (calldataWord evm.executionEnv.calldata 4))
            evm.accountMap evm.executionEnv) (UInt256.lnot ⟨255⟩)) ⟨1⟩)) none) (immStore v) ∧
    (evm.executionEnv.perm = false →
      ExecTransitionBody config contract evm (enableIrmArgs evm.executionEnv.calldata)
        enableIrmTransition.body .staticViolation (immStore v)) := by
  have howner := evalMorphoOwnerCheck evm (enableIrmFrame v evm.executionEnv.calldata).locals
    (immStore v) (by simp [enableIrmFrame, addressAdminFrame, enableIrmArgs])
  have hbase : (enableIrmFrame v evm.executionEnv.calldata).locals.get? "isIrmEnabled" = none := by
    simp [enableIrmFrame, addressAdminFrame, enableIrmArgs]
  have hkey := enableIrmArg_eval v evm.executionEnv.calldata evm
  have hload := evalMorphoIrmEnabled evm _ (immStore v) (.var "irm") _ hbase hkey hcanon
  have hnot := evalNotBoolWord hload
  simp only [irmEnabledByte] at hdisabled
  have hprefix : ABlock config evm
      { contract := contract, locals := enableIrmArgs evm.executionEnv.calldata, immutables := immStore v }
      enableIrmTransition.body (enableIrmFrame v evm.executionEnv.calldata)
      (enableIrmTransition.body.drop 5) :=
    ((calldataPrelude_ok hcv hsize).requireStep
      (by simpa only [ho, decide_true] using howner)).requireStep
      (by simpa only [hdisabled, decide_true] using hnot)
  have hassign := assignBoolMappingTrue hbase hkey rfl (by rfl) (by rfl)
    (morphoLayout_isIrmEnabled _ hcanon)
  have htrue (state : EVM.State) : evalExpr? config (enableIrmFrame v evm.executionEnv.calldata)
      state (.boolLit true) = .ok (.bool true) := by simp only [evalExpr?, pure]
  constructor
  · apply ExecFuncBody.execBlockOK
    apply hprefix.run
    apply ExecBlock.consNormal (ExecStmt.assign (htrue evm) hassign)
    apply ExecBlock.consNormal (ExecStmt.emit (evalExprs?_singleton (enableIrmArg_eval v _ _)))
    exact ExecBlock.nil
  · intro hperm
    exact ExecFuncBody.execBlockStatic
      (hprefix.run (ExecBlock.consStatic (ExecStmt.assignStatic (htrue evm) hassign hperm)))

theorem morphoEnableIrmBodyRejects (v : MorphoImmutables) (evm : EVM.State)
    (hcv : evm.executionEnv.weiValue = ⟨0⟩)
    (hsize : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (hcanon : (calldataWord evm.executionEnv.calldata 4).toNat < EVM.addressModulus)
    (hbad : solcSourceWord evm.executionEnv ≠ solcAddressSlotWord ⟨0⟩ evm.accountMap evm.executionEnv ∨
      irmEnabledByte evm.accountMap evm.executionEnv (calldataWord evm.executionEnv.calldata 4) ≠ ⟨0⟩) :
    ExecTransitionBody config contract evm (enableIrmArgs evm.executionEnv.calldata)
      enableIrmTransition.body .reverted (immStore v) := by
  have howner := evalMorphoOwnerCheck evm (enableIrmFrame v evm.executionEnv.calldata).locals
    (immStore v) (by simp [enableIrmFrame, addressAdminFrame, enableIrmArgs])
  apply ExecFuncBody.execBlockRevert
  by_cases ho : solcSourceWord evm.executionEnv = solcAddressSlotWord ⟨0⟩ evm.accountMap evm.executionEnv
  · have hnz := hbad.resolve_left (not_not.mpr ho)
    simp only [irmEnabledByte] at hnz
    have hload := evalMorphoIrmEnabled evm (enableIrmFrame v evm.executionEnv.calldata).locals
      (immStore v) (.var "irm") _
      (by simp [enableIrmFrame, addressAdminFrame, enableIrmArgs]) (enableIrmArg_eval v _ evm) hcanon
    exact ((calldataPrelude_ok hcv hsize).requireStep
      (by simpa only [ho, decide_true] using howner)).requireRevert
      (by simpa only [hnz, decide_false] using evalNotBoolWord hload)
  · exact (calldataPrelude_ok hcv hsize).requireRevert
      (by simpa only [ho, decide_false] using howner)

set_option maxRecDepth 10000 in
theorem morphoEnableIrmReachDecode {σ σ₀ A I} {g : Sat256} (v : MorphoImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (morphoSelBytes 9))
    (hcv : I.weiValue = ⟨0⟩) (hlen : 36 ≤ I.calldata.size)
    (hbound : I.calldata.size < 2 ^ 255 + 4) :
    ∃ k C, RD (deployedRuntime v) I g (initState σ σ₀ g A I) (UInt256.ofNat 11354)
      [UInt256.ofNat 8161, ⟨0⟩]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C := by
  obtain ⟨k, C, rd⟩ := morphoReachEnableIrmBody (g := g) (σ := σ) (σ₀ := σ₀)
    (A := A) v hcode (by omega) hsize hsel
  have rdGuard := morphoBlocks.morpho_block_8105_fallthrough
    (immWords := wordsOf (immStore v)) (by decide) hcv rd
  have hcond := solcCalldataStaticLenCheckOk (words := 1) hlen hbound hsize
  have rdCall := morphoBlocks.morpho_block_8112_fallthrough
    (immWords := wordsOf (immStore v)) (by decide)
    (by simpa only [wordAddNegFour] using hcond) rdGuard
  have rdDecode := morphoBlocks.morpho_block_8154
    (immWords := wordsOf (immStore v)) (by decide)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rdCall
  exact ⟨_, _, rdDecode⟩

set_option maxRecDepth 1000 in
theorem morphoEnableIrmReachOwnerCheck {σ σ₀ A I} {g : Sat256} (v : MorphoImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (morphoSelBytes 9))
    (hcv : I.weiValue = ⟨0⟩) (hlen : 36 ≤ I.calldata.size)
    (hbound : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (calldataWord I.calldata 4).toNat < EVM.addressModulus) :
    ∃ aw k C, RD (deployedRuntime v) I g (initState σ σ₀ g A I) (UInt256.ofNat 12097)
      [UInt256.eq (solcSourceWord I) (solcAddressSlotWord ⟨0⟩ σ I),
       UInt256.ofNat 128, UInt256.ofNat 8200, calldataWord I.calldata 4,
       solcAddrMask, ⟨0⟩]
      (morphoNotOwnerMem solcFreePtrMem) aw ByteArray.empty σ k C := by
  obtain ⟨k, C, rd⟩ := morphoEnableIrmReachDecode (g := g) (σ := σ) (σ₀ := σ₀)
    (A := A) v hcode hsize hsel hcv hlen hbound
  obtain ⟨k', C', rdBody⟩ := morphoDecodeAddress4Ok (v := v) (by simp only [List.length_cons, List.length_nil]; decide)
    (by rw [morphoPatchedValidJumps v]; jump_dest) hcanon rd
  obtain ⟨kb, Cb, rdMessage⟩ := morphoBlocks.morpho_block_8161
    (immWords := wordsOf (immStore v)) (by simp only [List.length_cons, List.length_nil]; decide)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rdBody
  obtain ⟨aw, km, Cm, rdCheck⟩ := morphoNotOwnerMessage (v := v) (by simp only [List.length_cons, List.length_nil]; decide)
    (by rw [morphoPatchedValidJumps v]; jump_dest) (by native_decide) rdMessage
  have rdRequire := morphoBlocks.morpho_block_585
    (immWords := wordsOf (immStore v)) (by simp only [List.length_cons, List.length_nil]; decide)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rdCheck
  have hptr : memLoad (UInt256.ofNat 64) solcFreePtrMem = UInt256.ofNat 128 := solcFreePtrMem_mload64
  exact ⟨_, _, _, by simpa only [morphoBlocks.morpho_block_585_stack, hptr] using rdRequire⟩

abbrev irmCheckMem (key : UInt256) : ByteArray := booleanAdminCheckMem ⟨4⟩ key

theorem irmCheckMem_size (key : UInt256) : (irmCheckMem key).size = 192 :=
  booleanAdminCheckMem_size _ _

theorem irmCheckMem_load64 (key : UInt256) :
    memLoad (UInt256.ofNat 64) (irmCheckMem key) = UInt256.ofNat 192 :=
  booleanAdminCheckMem_load64 _ _

set_option maxRecDepth 1000 in
theorem morphoEnableIrmReachEnabledCheck {σ σ₀ A I} {g : Sat256} (v : MorphoImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (morphoSelBytes 9))
    (hcv : I.weiValue = ⟨0⟩) (hlen : 36 ≤ I.calldata.size)
    (hbound : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (calldataWord I.calldata 4).toNat < EVM.addressModulus)
    (ho : solcSourceWord I = solcAddressSlotWord ⟨0⟩ σ I) :
    ∃ aw k C, RD (deployedRuntime v) I g (initState σ σ₀ g A I) (UInt256.ofNat 12097)
      [UInt256.isZero (irmEnabledByte σ I (calldataWord I.calldata 4)),
       UInt256.ofNat 192, UInt256.ofNat 8229, calldataWord I.calldata 4, ⟨0⟩]
      (morphoAlreadySetMem (irmCheckMem (calldataWord I.calldata 4))) aw ByteArray.empty σ k C := by
  obtain ⟨aw, k, C, rd⟩ := morphoEnableIrmReachOwnerCheck (g := g) (σ := σ) (σ₀ := σ₀)
    (A := A) v hcode hsize hsel hcv hlen hbound hcanon
  obtain ⟨kt, Ct, rdNext⟩ := morphoRequireTrue (v := v) (by simp)
    (by rw [morphoPatchedValidJumps v]; jump_dest)
    (by rw [ho, uInt256_eq_self]; decide) rd
  obtain ⟨kh, Ch, rdMessage⟩ := morphoBlocks.morpho_block_8200
    (immWords := wordsOf (immStore v)) (by simp)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rdNext
  change RD _ _ _ _ _
    [UInt256.ofNat 585,
      UInt256.isZero (UInt256.land (solcSlotWordAt
        (keccakWord ⟨0⟩ (UInt256.ofNat 64)
          (irmCheckMem (UInt256.land (calldataWord I.calldata 4) solcAddrMask))) σ I)
        (UInt256.ofNat 255)), UInt256.ofNat 8229,
      UInt256.land (calldataWord I.calldata 4) solcAddrMask, ⟨0⟩]
    (irmCheckMem (UInt256.land (calldataWord I.calldata 4) solcAddrMask)) _ _ _ _ _ at rdMessage
  rw [solcAddrMask_clean hcanon] at rdMessage
  have hslot : keccakWord ⟨0⟩ (UInt256.ofNat 64) (irmCheckMem (calldataWord I.calldata 4)) =
      solcMappingSlot ⟨4⟩ (calldataWord I.calldata 4) := twoWordHashMem_solcMappingSlot_any _ _ _
  rw [hslot] at rdMessage
  obtain ⟨aw', km, Cm, rdCheck⟩ := morphoAlreadySetMessage (v := v) (by simp)
    (by rw [morphoPatchedValidJumps v]; jump_dest)
    (by rw [irmCheckMem_load64]; native_decide) rdMessage
  have rdRequire := morphoBlocks.morpho_block_585
    (immWords := wordsOf (immStore v)) (by simp)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rdCheck
  exact ⟨_, _, _, by simpa only [morphoBlocks.morpho_block_585_stack, irmCheckMem_load64] using rdRequire⟩

set_option maxRecDepth 1000 in
theorem morphoEnableIrmXRejects {σ σ₀ A I} {g : Sat256} (v : MorphoImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (morphoSelBytes 9))
    (hcv : I.weiValue = ⟨0⟩) (hlen : 36 ≤ I.calldata.size)
    (hbound : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (calldataWord I.calldata 4).toNat < EVM.addressModulus)
    (hbad : solcSourceWord I ≠ solcAddressSlotWord ⟨0⟩ σ I ∨
      irmEnabledByte σ I (calldataWord I.calldata 4) ≠ ⟨0⟩) :
    RDrev (deployedRuntime v) g (initState σ σ₀ g A I) := by
  by_cases ho : solcSourceWord I = solcAddressSlotWord ⟨0⟩ σ I
  · obtain ⟨aw, k, C, rd⟩ := morphoEnableIrmReachEnabledCheck (g := g) (σ := σ) (σ₀ := σ₀)
      (A := A) v hcode hsize hsel hcv hlen hbound hcanon ho
    have hnz := hbad.resolve_left (not_not.mpr ho)
    have hmsg : morphoErrorLength (morphoAlreadySetMem (irmCheckMem (calldataWord I.calldata 4)))
        (UInt256.ofNat 192) = UInt256.ofNat 11 :=
      morphoErrorMem192_length _ _ _ (irmCheckMem_size _) (irmCheckMem_load64 _)
    exact morphoRequireFalseShort (v := v) (by simp)
      (isZero_eq_zero_of_ne hnz) (by rw [hmsg]; decide) (by rw [hmsg]; decide) rd
  · obtain ⟨aw, k, C, rd⟩ := morphoEnableIrmReachOwnerCheck (g := g) (σ := σ) (σ₀ := σ₀)
      (A := A) v hcode hsize hsel hcv hlen hbound hcanon
    exact morphoRequireFalseShort (v := v) (by simp)
      (u256_eq_of_ne ho) (by native_decide) (by native_decide) rd

set_option maxRecDepth 1000 in
theorem morphoEnableIrmReachStore {σ σ₀ A I} {g : Sat256} (v : MorphoImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (morphoSelBytes 9))
    (hcv : I.weiValue = ⟨0⟩) (hlen : 36 ≤ I.calldata.size)
    (hbound : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (calldataWord I.calldata 4).toNat < EVM.addressModulus)
    (ho : solcSourceWord I = solcAddressSlotWord ⟨0⟩ σ I)
    (hdisabled : irmEnabledByte σ I (calldataWord I.calldata 4) = ⟨0⟩) :
    ∃ aw k C, RD (deployedRuntime v) I g (initState σ σ₀ g A I) (UInt256.ofNat 8229)
      [calldataWord I.calldata 4, ⟨0⟩]
      (morphoAlreadySetMem (irmCheckMem (calldataWord I.calldata 4))) aw ByteArray.empty σ k C := by
  obtain ⟨aw, k, C, rd⟩ := morphoEnableIrmReachEnabledCheck (g := g) (σ := σ) (σ₀ := σ₀)
    (A := A) v hcode hsize hsel hcv hlen hbound hcanon ho
  obtain ⟨k', C', rdStore⟩ := morphoRequireTrue (v := v) (by simp)
    (by rw [morphoPatchedValidJumps v]; jump_dest) (by rw [hdisabled]; decide) rd
  exact ⟨_, _, _, rdStore⟩

-- The provided summary assumes write permission; this prefix covers the static halt.
set_option maxRecDepth 1000 in
theorem morphoEnableIrmStoreStatic {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {σ : AccountMap} {k C : Nat} {key zero : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024) (hperm : ee.perm = false)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 8229)
      (key :: zero :: R) mem aw rdata σ k C) :
    RDstatic (deployedRuntime v) g s0 := by
  let r0 := h
  have r1 := r0.jumpdest (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, wordsOf (immStore v), (⟨8229⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none, morphoBlocks.immutableLayout_inBounds, morphoBlocks.immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.dup1 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, wordsOf (immStore v), (⟨8230⟩ : UInt256), UInt8.ofNat 128, .DUP1, none, morphoBlocks.immutableLayout_inBounds, morphoBlocks.immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.dup3 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, wordsOf (immStore v), (⟨8231⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, morphoBlocks.immutableLayout_inBounds, morphoBlocks.immutableTemplate_size64)) (by evm_ov)
  have r4 := RD.genMstore r3 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, wordsOf (immStore v), (⟨8232⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, morphoBlocks.immutableLayout_inBounds, morphoBlocks.immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 4) (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, wordsOf (immStore v), (⟨8233⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 4), 1), morphoBlocks.immutableLayout_inBounds, morphoBlocks.immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 32) (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, wordsOf (immStore v), (⟨8235⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 32), 1), morphoBlocks.immutableLayout_inBounds, morphoBlocks.immutableTemplate_size64)) (by evm_ov)
  have r7 := RD.genMstore r6 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, wordsOf (immStore v), (⟨8237⟩ : UInt256), UInt8.ofNat 82, .MSTORE, none, morphoBlocks.immutableLayout_inBounds, morphoBlocks.immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.push1 (UInt256.ofNat 64) (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, wordsOf (immStore v), (⟨8238⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 64), 1), morphoBlocks.immutableLayout_inBounds, morphoBlocks.immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.dup3 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, wordsOf (immStore v), (⟨8240⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, morphoBlocks.immutableLayout_inBounds, morphoBlocks.immutableTemplate_size64)) (by evm_ov)
  have r10 := RD.genKeccak256 r9 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, wordsOf (immStore v), (⟨8241⟩ : UInt256), UInt8.ofNat 32, .KECCAK256, none, morphoBlocks.immutableLayout_inBounds, morphoBlocks.immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.push1 (UInt256.ofNat 1) (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, wordsOf (immStore v), (⟨8242⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1), morphoBlocks.immutableLayout_inBounds, morphoBlocks.immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.pushConst (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639680) (width := 32) (op := .PUSH32) (by decide) (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, wordsOf (immStore v), (⟨8244⟩ : UInt256), UInt8.ofNat 127, .Push .PUSH32, some ((UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639680), 32), morphoBlocks.immutableLayout_inBounds, morphoBlocks.immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.dup3 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, wordsOf (immStore v), (⟨8277⟩ : UInt256), UInt8.ofNat 130, .DUP3, none, morphoBlocks.immutableLayout_inBounds, morphoBlocks.immutableTemplate_size64)) (by evm_ov)
  obtain ⟨_, _, r14⟩ := RD.sload r13 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, wordsOf (immStore v), (⟨8278⟩ : UInt256), UInt8.ofNat 84, .SLOAD, none, morphoBlocks.immutableLayout_inBounds, morphoBlocks.immutableTemplate_size64)) (by evm_ov)
  have r15 := r14.and (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, wordsOf (immStore v), (⟨8279⟩ : UInt256), UInt8.ofNat 22, .AND, none, morphoBlocks.immutableLayout_inBounds, morphoBlocks.immutableTemplate_size64)) (by evm_ov)
  have r16 := r15.or (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, wordsOf (immStore v), (⟨8280⟩ : UInt256), UInt8.ofNat 23, .OR, none, morphoBlocks.immutableLayout_inBounds, morphoBlocks.immutableTemplate_size64)) (by evm_ov)
  have r17 := r16.swap1 (by immutable_decode(Benchmarks.Morpho.MorphoBlue.immutableLayout, Benchmarks.Morpho.MorphoBlue.morphoBytecode, wordsOf (immStore v), (⟨8281⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none, morphoBlocks.immutableLayout_inBounds, morphoBlocks.immutableTemplate_size64)) (by evm_ov)
  exact r17.sstoreStatic hperm (by
    immutable_decode(immutableLayout, morphoBytecode, wordsOf (immStore v),
      (⟨8282⟩ : UInt256), UInt8.ofNat 85, .SSTORE, none,
      morphoBlocks.immutableLayout_inBounds, morphoBlocks.immutableTemplate_size64)) (by evm_ov)

set_option maxRecDepth 1000 in
theorem morphoEnableIrmXSplit {σ σ₀ A I} {g : Sat256} (v : MorphoImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (morphoSelBytes 9))
    (hcv : I.weiValue = ⟨0⟩) (hlen : 36 ≤ I.calldata.size)
    (hbound : I.calldata.size < 2 ^ 255 + 4)
    (hcanon : (calldataWord I.calldata 4).toNat < EVM.addressModulus)
    (ho : solcSourceWord I = solcAddressSlotWord ⟨0⟩ σ I)
    (hdisabled : irmEnabledByte σ I (calldataWord I.calldata 4) = ⟨0⟩) :
    (I.perm = true ∧ RDret (deployedRuntime v) g (initState σ σ₀ g A I)
      (sstoreAccountMap I.codeOwner σ (solcMappingSlot ⟨4⟩ (calldataWord I.calldata 4))
        (UInt256.lor (UInt256.land (solcSlotWordAt (solcMappingSlot ⟨4⟩
          (calldataWord I.calldata 4)) σ I) (UInt256.lnot ⟨255⟩)) ⟨1⟩)) ByteArray.empty) ∨
    (I.perm = false ∧ RDstatic (deployedRuntime v) g (initState σ σ₀ g A I)) := by
  obtain ⟨aw, k, C, rd⟩ := morphoEnableIrmReachStore (g := g) (σ := σ) (σ₀ := σ₀)
    (A := A) v hcode hsize hsel hcv hlen hbound hcanon ho hdisabled
  by_cases hperm : I.perm = true
  · refine .inl ⟨hperm, ?_⟩
    have ret := morphoBlocks.morpho_block_8229 (immWords := wordsOf (immStore v)) (by decide) hperm rd
    let mem := twoWordHashMem (calldataWord I.calldata 4) (UInt256.ofNat 4)
      (morphoAlreadySetMem (irmCheckMem (calldataWord I.calldata 4)))
    change RDret _ _ _ (sstoreAccountMap I.codeOwner σ (keccakWord ⟨0⟩ (UInt256.ofNat 64) mem)
      (UInt256.lor (UInt256.land (solcSlotWordAt (keccakWord ⟨0⟩ (UInt256.ofNat 64) mem) σ I)
        (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639680))
        (UInt256.ofNat 1))) (mem.readWithPadding 0 0) at ret
    have hslot : keccakWord ⟨0⟩ (UInt256.ofNat 64) mem =
        solcMappingSlot ⟨4⟩ (calldataWord I.calldata 4) := twoWordHashMem_solcMappingSlot_any _ _ _
    rw [hslot, byteArray_readWithPadding_zero] at ret
    have hmask : UInt256.lnot ⟨255⟩ =
        UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639680 := by native_decide
    rw [hmask]
    exact ret
  · have hp : I.perm = false := Bool.eq_false_of_not_eq_true hperm
    exact .inr ⟨hp, morphoEnableIrmStoreStatic (v := v) (by decide) hp rd⟩

set_option maxRecDepth 10000 in
theorem morphoEnableIrmXReverts {σ σ₀ A I} {g : Sat256} (v : MorphoImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (morphoSelBytes 9))
    (hbad : I.weiValue ≠ ⟨0⟩ ∨ I.calldata.size < 36 ∨ 2 ^ 255 + 4 ≤ I.calldata.size) :
    RDrev (deployedRuntime v) g (initState σ σ₀ g A I) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (morphoSelBytes 9) rfl hsel
  obtain ⟨k, C, rd⟩ := morphoReachEnableIrmBody (g := g) (σ := σ) (σ₀ := σ₀)
    (A := A) v hcode hsz hsize hsel
  have hvalid : (D_J (deployedRuntime v) 0).contains (UInt256.ofNat 440) = true := by
    rw [morphoPatchedValidJumps v]
    jump_dest
  by_cases hcv : I.weiValue = ⟨0⟩
  · have hlen := hbad.resolve_left (not_not.mpr hcv)
    have rdGuard := morphoBlocks.morpho_block_8105_fallthrough
      (immWords := wordsOf (immStore v)) (by decide) hcv rd
    have hcond : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) (UInt256.ofNat 32) = ⟨1⟩ := by
      rcases hlen with hshort | hbig
      · exact solcCalldataStaticLenCheckShort (words := 1) hsz hshort hsize (by norm_num)
      · exact solcCalldataStaticLenCheckHuge (words := 1) hbig hsize (by norm_num)
    have rdRevert := morphoBlocks.morpho_block_8112_taken
      (immWords := wordsOf (immStore v)) (by decide)
      (by rw [wordAddNegFour, hcond]; decide) hvalid rdGuard
    exact morphoBlocks.morpho_block_440 (immWords := wordsOf (immStore v)) (by decide) rdRevert
  · have rdRevert := morphoBlocks.morpho_block_8105_taken
      (immWords := wordsOf (immStore v)) (by decide) hcv hvalid rd
    exact morphoBlocks.morpho_block_440 (immWords := wordsOf (immStore v)) (by decide) rdRevert

set_option maxRecDepth 10000 in
theorem morphoEnableIrmXNoncanonical {σ σ₀ A I} {g : Sat256} (v : MorphoImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (morphoSelBytes 9)) (hlen : 36 ≤ I.calldata.size)
    (hbound : I.calldata.size < 2 ^ 255 + 4)
    (hnc : ¬ (calldataWord I.calldata 4).toNat < EVM.addressModulus) :
    RDrev (deployedRuntime v) g (initState σ σ₀ g A I) := by
  by_cases hcv : I.weiValue = ⟨0⟩
  · obtain ⟨k, C, rd⟩ := morphoEnableIrmReachDecode (g := g) (σ := σ) (σ₀ := σ₀)
      (A := A) v hcode hsize hsel hcv hlen hbound
    exact morphoDecodeAddress4Revert (by decide) hnc rd
  · exact morphoEnableIrmXReverts v hcode hsize hsel (.inl hcv)

/-- `enableIrm(address)`: the theorem `Correct.lean` routes selector 9 to. -/
theorem morphoEnableIrmBody {σ σ₀ A I} {g : UInt256} (v : MorphoImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (morphoSelBytes 9)) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (morphoSelBytes 9) rfl hsel
  have hd : selectorDispatchMsg contract I.calldata = some enableIrmTransition :=
    morphoSelectorDispatch_of_selIs (by decide) hsel
  by_cases hlen : 36 ≤ I.calldata.size
  · by_cases hbound : I.calldata.size < 2 ^ 255 + 4
    · by_cases hcanon : (calldataWord I.calldata 4).toNat < EVM.addressModulus
      · have hdec : decodeCalldataWithMode config.abiDecodeMode
            (enableIrmTransition.params.map Param.name)
            (transitionSignature enableIrmTransition).paramTypes I.calldata =
            some (enableIrmArgs I.calldata) := decodeCalldata_address_ok hlen hbound hcanon
        by_cases hcv : I.weiValue = ⟨0⟩
        · by_cases ho : solcSourceWord I = solcAddressSlotWord ⟨0⟩ σ I
          · by_cases hdisabled : irmEnabledByte σ I (calldataWord I.calldata 4) = ⟨0⟩
            · have hbody := morphoEnableIrmBodySplit v (initState σ σ₀ (.ofUInt256 g) A I)
                hcv hbound hcanon ho hdisabled
              rcases morphoEnableIrmXSplit (g := .ofUInt256 g) (σ₀ := σ₀) (A := A)
                v hcode hsize hsel hcv hlen hbound hcanon ho hdisabled with ⟨hp, hx⟩ | ⟨hp, hx⟩
              · exact reEquivSelectorExecutionGen hcode hx hd hdec hbody.1
                  (by rw [storageStore_accountMap]; rfl) (.fallthrough rfl rfl (by native_decide))
              · exact reEquivSelectorStatic hcode hx hd hdec (hbody.2 hp)
            · exact reEquivSelectorRevert hcode
                (morphoEnableIrmXRejects v hcode hsize hsel hcv hlen hbound hcanon (.inr hdisabled)) hd hdec
                (morphoEnableIrmBodyRejects v _ hcv hbound hcanon (.inr hdisabled))
          · exact reEquivSelectorRevert hcode
              (morphoEnableIrmXRejects v hcode hsize hsel hcv hlen hbound hcanon (.inl ho)) hd hdec
              (morphoEnableIrmBodyRejects v _ hcv hbound hcanon (.inl ho))
        · exact reEquivSelectorRevert hcode
            (morphoEnableIrmXReverts v hcode hsize hsel (.inl hcv)) hd hdec
            (bodyReverts_nonPayable hcv)
      · exact reEquivSelectorDecodingFailed hcode
          (morphoEnableIrmXNoncanonical v hcode hsize hsel hlen hbound hcanon) hd
          (decodeCalldata_address_none_noncanon hlen hbound hcanon)
    · exact reEquivSelectorDecodingFailed hcode
        (morphoEnableIrmXReverts v hcode hsize hsel (.inr (.inr (by omega)))) hd
        (decodeCalldata_address_none_huge (by omega))
  · exact reEquivSelectorDecodingFailed hcode
      (morphoEnableIrmXReverts v hcode hsize hsel (.inr (.inl (by omega)))) hd
      (decodeCalldata_address_none_short hsz (by omega))

end Benchmarks.Morpho.MorphoBlue
