import Benchmarks.Safe.ViaIR.Dispatch
import Benchmarks.Safe.ViaIR.Storage
import Benchmarks.Safe.ViaIR.Blocks.Runtime_005
import Benchmarks.Safe.ViaIR.Blocks.Runtime_019
import Reasoning.WordArithmetic

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.ViaIR.RuntimeBlocks

namespace Benchmarks.Safe.ViaIR

set_option maxRecDepth 100000

/-! The new signed length guard for zero-argument getters has a failure path absent from the
legacy bytecode. These lemmas check the artifact-specific decoder against that path. The huge
byte array is constructed symbolically, never evaluated.
-/

theorem safeDecodeCalldata_eq_modern_of_small {names : List Ident} {types : List ABIType}
    {cd : ByteArray} (hsize : cd.size < 2 ^ 255 + 4) :
    safeDecodeCalldata names types cd = ABI.decodeCalldataWithMode .modern names types cd := by
  have hguard : ¬ 2 ^ 255 ≤ cd.size - 4 := by omega
  simp only [safeDecodeCalldata, hguard, and_false, if_false, safeDecodeMode]

theorem safeDecodeCalldata_cons (names : List Ident) (ty : ABIType) (types : List ABIType)
    (cd : ByteArray) :
    safeDecodeCalldata names (ty :: types) cd =
      ABI.decodeCalldataWithMode .modern names (ty :: types) cd := rfl

theorem safeDecodeCalldata_empty_ok {cd : ByteArray}
    (hlong : 4 ≤ cd.size) (hsmall : cd.size < 2 ^ 255 + 4) :
    safeDecodeCalldata [] [] cd = some ∅ := by
  rw [safeDecodeCalldata_eq_modern_of_small hsmall]
  exact decodeCalldataWithMode_empty_ok hlong

theorem safeDecodeCalldata_empty_huge {cd : ByteArray}
    (hhuge : 2 ^ 255 + 4 ≤ cd.size) : safeDecodeCalldata [] [] cd = none := by
  have hguard : 2 ^ 255 ≤ cd.size - 4 := by omega
  unfold safeDecodeCalldata
  rw [if_pos ⟨rfl, hguard⟩]

theorem safeIRArgumentSize {size : Nat} (hlong : 4 ≤ size) (hsize : size < UInt256.size) :
    UInt256.ofNat size + UInt256.lnot ⟨3⟩ = UInt256.ofNat (size - 4) := by
  rw [u256_add_comm, lnot3_add_returnSize hlong hsize]

theorem safeIRArgumentSizeSub {size : Nat} (hlong : 4 ≤ size) (hsize : size < UInt256.size) :
    UInt256.lnot (UInt256.ofNat 3) + UInt256.ofNat size =
      UInt256.sub (UInt256.ofNat size) (UInt256.ofNat 4) := by
  change UInt256.lnot ⟨3⟩ + UInt256.ofNat size = _
  rw [lnot3_add_returnSize hlong hsize]
  apply u256_inj
  rw [ulit_toNat' _ (by omega), usub_ofNat_lit_toNat hlong hsize]

theorem safeIRLengthCheckOk {size : Nat} (hlong : 4 ≤ size)
    (hsmall : size < 2 ^ 255 + 4) (hsize : size < UInt256.size) :
    UInt256.slt (UInt256.ofNat size + UInt256.lnot ⟨3⟩) ⟨0⟩ = ⟨0⟩ := by
  rw [safeIRArgumentSize hlong hsize]
  apply slt_lit_zero (by decide)
  · exact Nat.zero_le _
  · rw [ulit_toNat' _ (by omega)]
    omega

theorem safeIRLengthCheckHuge {size : Nat} (hhuge : 2 ^ 255 + 4 ≤ size)
    (hsize : size < UInt256.size) :
    UInt256.slt (UInt256.ofNat size + UInt256.lnot ⟨3⟩) ⟨0⟩ = ⟨1⟩ := by
  rw [safeIRArgumentSize (by omega) hsize]
  apply slt_lit_one_high (by decide)
  rw [ulit_toNat' _ (by omega)]
  omega

def safeIRHugeNonceCalldata : ByteArray :=
  ⟨#[0xaf, 0xfe, 0xd0, 0xe0]⟩ ++ ByteArray.zeroes (2 ^ 255)

theorem safeIRHugeNonceCalldata_size : safeIRHugeNonceCalldata.size = 2 ^ 255 + 4 := by
  rw [safeIRHugeNonceCalldata, ByteArray.size_append, ByteArray_zeroes_size]
  rfl

theorem safeIRHugeNonceCalldata_bound : safeIRHugeNonceCalldata.size < UInt256.size := by
  rw [safeIRHugeNonceCalldata_size]
  decide +kernel

theorem safeIRHugeNonceCalldata_selector :
    safeIRHugeNonceCalldata.extract 0 4 = ⟨#[0xaf, 0xfe, 0xd0, 0xe0]⟩ := by
  exact ByteArray.extract_append_eq_left rfl

theorem safeIRHugeNonceCalldata_dispatch :
    selectorDispatchMsg contract safeIRHugeNonceCalldata = some nonceTransition := by
  simp only [selectorDispatchMsg_eq_dispatchList, contract, transitions, dispatchList_cons,
    selectorOf, safeIRHugeNonceCalldata_selector, versionSelectorBytes,
    addownerwiththresholdSelectorBytes, approvehashSelectorBytes, approvedhashesSelectorBytes,
    changethresholdSelectorBytes, checknsignaturesSelectorBytes,
    checknsignaturesAddressBytes32BytesUint256SelectorBytes, checksignaturesSelectorBytes,
    checksignaturesAddressBytes32BytesSelectorBytes, disablemoduleSelectorBytes,
    domainseparatorSelectorBytes, enablemoduleSelectorBytes, exectransactionSelectorBytes,
    exectransactionfrommoduleSelectorBytes, exectransactionfrommodulereturndataSelectorBytes,
    getmodulespaginatedSelectorBytes, getownersSelectorBytes, getstorageatSelectorBytes,
    getthresholdSelectorBytes, gettransactionhashSelectorBytes, ismoduleenabledSelectorBytes,
    isownerSelectorBytes, nonceSelectorBytes]
  rfl

theorem safeIRHugeNonceCalldata_decodingFailed :
    config.externalABI.decodeCalldata? (nonceTransition.params.map Param.name)
      (transitionSignature nonceTransition).paramTypes safeIRHugeNonceCalldata = none := by
  change safeDecodeCalldata [] [] safeIRHugeNonceCalldata = none
  simp [safeDecodeCalldata, safeIRHugeNonceCalldata_size]

/-- At the first rejected size, the generated guard agrees with the local decoder's rejection. -/
theorem safeIRHugeNonceLengthGuard {cd : ByteArray} (hs : cd.size = 2 ^ 255 + 4) :
    UInt256.slt (UInt256.ofNat cd.size + UInt256.lnot (UInt256.ofNat 3)) ⟨0⟩ = ⟨1⟩ := by
  rw [hs]
  decide +kernel

/-- The actual runtime follows the new length-failure path (or exhausts its gas). -/
theorem safeIRHugeNonceReverts {I : ExecutionEnv} {σ σ₀ : AccountMap} {A : Substate}
    {g : Sat256} (hcode : I.code = safeBytecode)
    (hsize : I.calldata.size = 2 ^ 255 + 4)
    (hdispatch : selectorDispatchMsg contract I.calldata = some nonceTransition)
    (hvalue : I.weiValue = ⟨0⟩) :
    RDrev fork safeBytecode g (initState σ σ₀ g A I) := by
  obtain ⟨hlong, hword⟩ := selectorDispatchFacts 0xaf 0xfe 0xd0 0xe0 ⟨0xaffed0e0⟩
    hdispatch nonceSelectorBytes (by decide)
  obtain ⟨k, C, h4018⟩ := safeReachEntry (fork := fork) (σ := σ) (σ₀ := σ₀) (A := A)
    (g := g) ⟨0xaffed0e0⟩ 15 ⟨4018⟩ hcode (by rw [hsize]; decide) hlong hword
    (by native_decide)
  have h4025 := safeRuntime_block_4018_fallthrough (by simp) hvalue h4018
  have h589 := safeRuntime_block_4025_taken (by simp)
    (by
      change UInt256.slt (UInt256.ofNat I.calldata.size + UInt256.lnot (UInt256.ofNat 3))
        ⟨0⟩ ≠ ⟨0⟩
      rw [safeIRHugeNonceLengthGuard hsize]
      decide)
    (by jump_dest) h4025
  exact safeRuntime_block_589 (by simp) h589

/-- The unchanged source body returns normally, independent of the unused calldata tail. -/
theorem safeIRNonceSourceReturns {I : ExecutionEnv} {σ σ₀ : AccountMap} {A : Substate}
    {g : Sat256} (hvalue : I.weiValue = ⟨0⟩) :
    ExecTransitionBody fork config contract (initState σ σ₀ g A I) ∅ nonceTransition.body
      (.returned { contract := contract, locals := ∅ } (initState σ σ₀ g A I)
        (some [.int (Int.ofNat (solcSlotWordAt ⟨5⟩ σ I).toNat)])) := by
  simpa only [nonceTransition, nonpayable, solcSlotWordAt, initState,
    Stele.EVM.storageLoad, State.lookupAccount] using
    uint256GetterBodyReturns (cfg := config) (c := contract)
      (initState σ σ₀ g A I) ∅ (ref := nonceRef) (er := { base := "nonce" }) (slot := ⟨5⟩)
      hvalue (by simp)
      (by simp [evalStorageRef, evalStorageRefSteps, nonceRef, EvalResult.bind, pure, bind])
      (by decide) rfl (by rfl)

private theorem nonpayableReturnCannotRevert {cfg : Config} {frame : Frame} {evm : State}
    {exprs : List Expr} {values : List Value}
    (hvalue : evm.executionEnv.weiValue = ⟨0⟩)
    (hreturn : evalExprs? cfg frame evm exprs = .ok values) :
    ¬ ExecFuncBody fork cfg frame evm
      [.require (.binary .eq (.env .callvalue) (.intLit 0)), .return exprs] .reverted := by
  intro h
  cases h with
  | execBlockRevert h =>
    cases h with
    | consNormal hguard htail =>
      cases hguard with
      | requireTrue _ =>
        cases htail with
        | consNormal hreturn _ => cases hreturn
        | consRevert hret =>
          cases hret with
          | returnRevert hbad => rw [hreturn] at hbad; cases hbad
    | consRevert hguard =>
      cases hguard with
      | requireFalse hbad => rw [evalCallvalueEq_true hvalue] at hbad; cases hbad
      | requireRevert hbad => rw [evalCallvalueEq_true hvalue] at hbad; cases hbad

theorem safeIRNonceSourceCannotRevert {I : ExecutionEnv} {σ σ₀ : AccountMap} {A : Substate}
    {g : Sat256} (hvalue : I.weiValue = ⟨0⟩) :
    ¬ ExecTransitionBody fork config contract (initState σ σ₀ g A I) ∅ nonceTransition.body
      .reverted := by
  apply nonpayableReturnCannotRevert
    (values := [.int (Int.ofNat (solcSlotWordAt ⟨5⟩ σ I).toNat)]) hvalue
  have hload := evalExpr_storage_scalar_value (cfg := config)
    (stele := { contract := contract, locals := ∅ }) (evm := initState σ σ₀ g A I)
    (slot := nonceRef) (er := { base := "nonce" }) (loc := uint256Loc ⟨5⟩)
    (t := .int (.uint ⟨256, by decide⟩))
    (by simp)
    (by simp [evalStorageRef, evalStorageRefSteps, nonceRef, EvalResult.bind, pure, bind])
    (by decide) rfl (by rfl) (storageLocLoad_uint256 (initState σ σ₀ g A I) ⟨5⟩)
  simp only [evalExprs?, hload, EvalResult.bind, pure, bind]
  rfl

end Benchmarks.Safe.ViaIR
