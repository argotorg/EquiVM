import Benchmarks.Dss.Vow.HealSuccess
import Benchmarks.Dss.Vow.VatSinCall

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.Vow

/-! ## `flap()` -/

theorem vowDispatch_flap {I : ExecutionEnv}
    (hsel : selIs I ⟨#[0x0e, 0x01, 0x19, 0x8b]⟩) :
    dispatchMsg contract I.calldata = some flapTransition := by
  apply dispatchMsg_eq_some_of_split (hfallback := by rfl)
    (pre := [AshTransition, SinTransition, bumpTransition, cageTransition, denyTransition,
      dumpTransition, fessTransition, fileUintTransition, fileAddressTransition])
    (post := [flapperTransition, flogTransition, flopTransition, flopperTransition,
      healTransition, humpTransition, kissTransition, liveTransition, relyTransition,
      sinTransition, sumpTransition, vatTransition, waitTransition, wardsTransition])
    (ti := flapTransition)
    (htr := by rfl)
  · intro t ht
    have hcd : I.calldata.extract 0 4 = (⟨#[0x0e, 0x01, 0x19, 0x8b]⟩ : ByteArray) :=
      (byteArray_eq_of_beq hsel).symm
    simp at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      simp [selectorOf, AshSelectorBytes, SinSelectorBytes, bumpSelectorBytes,
        cageSelectorBytes, denySelectorBytes, dumpSelectorBytes, fessSelectorBytes,
        fileUintSelectorBytes, fileAddressSelectorBytes, hcd]
      native_decide
  · rw [selectorOf, flapSelectorBytes]
    exact hsel

theorem vowDecode_flap {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (flapTransition.params.map Param.name)
      (transitionSignature flapTransition).paramTypes I.calldata = some ∅ := by
  show decodeCalldataWithMode config.abiDecodeMode [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz

theorem vowReachFlapBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = vowBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0x0e, 0x01, 0x19, 0x8b]⟩) :
    ∃ k C, RD vowBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨349⟩ [vowSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  have hword : vowSelWord I = ⟨234953099⟩ :=
    vowSelWord_eq_of_beq I hsz 0x0e 0x01 0x19 0x8b ⟨234953099⟩
      (by native_decide) hsel
  have hroot : UInt256.gt (armSelNat vowBytecode vowRootSplitPc) (vowSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  have hlow : UInt256.gt (armSelNat vowBytecode vowLowSplitPc) (vowSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  have heq0 : ∀ j, j < 0 →
      UInt256.eq (armSelNat vowBytecode (nthArmPc vowBytecode vowLowLowFirstArmPc j))
        (vowSelWord I) = ⟨0⟩ := by
    intro j hj
    omega
  have htake :
      UInt256.eq (armSelNat vowBytecode (nthArmPc vowBytecode vowLowLowFirstArmPc 0))
        (vowSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  exact vowReachLowLowBody 0 (by omega) ⟨349⟩ hcode hwv hsz hsize hroot hlow heq0
    htake (by jump_dest) (by native_decide)

theorem RD.vowFlapToSin0ExtcodesizeGuard
    {cA gh bl σ σ₀ A I} {g sel : UInt256}
    (hreach : ∃ k C, RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨349⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨921⟩
      (kissDaiTargetWord σ I :: kissDaiTargetWord σ I :: healSinOutPtr ::
        healSinInSize :: healSinOutPtr :: ⟨32⟩ :: healSinEndPtr :: healSinSelector ::
        kissDaiTargetWord σ I :: ⟨985⟩ :: ⟨993⟩ :: ⟨0⟩ :: ⟨357⟩ :: sel :: [])
      (healSinCalldataMem I solcFreePtrMem) (UInt256.ofNat 6) ByteArray.empty (cA, σ) k C := by
  let target := kissDaiTargetWord σ I
  let rawTarget := vowSlotWord ⟨1⟩ σ I
  obtain ⟨_, _, rd349⟩ := hreach
  have rd350 := rd349.jumpdest (by native_decide) (by evm_ov)
  have rd353 := rd350.push2 ⟨357⟩ (by native_decide) (by evm_ov)
  have rd356 := rd353.push2 ⟨847⟩ (by native_decide) (by evm_ov)
  have rd847 := by
    simpa using rd356.jump (by native_decide) (by jump_dest) (by evm_ov)
  have rd850 := rd847.jumpdest (by native_decide) (by evm_ov)
  have rd851 := rd850.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  obtain ⟨k851, C851, rd852₀⟩ := rd851.sload (by native_decide) (by evm_ov)
  have rd852 : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨851⟩
      (rawTarget :: ⟨357⟩ :: sel :: []) solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k851 C851 := by
    simpa [rawTarget, vowSlotWord, solcSlotWord] using rd852₀
  have hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ solcFreePtrMem.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 3 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (solcFreePtrMem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [solcFreePtrMem_size]; decide) (by decide)
      solcFreePtrMem_read64
  have hSinMem : (healSinCalldataMem I solcFreePtrMem).size = 164 :=
    initialHealSinCalldataMem_size I
  have hSinRead64 :
      (healSinCalldataMem I solcFreePtrMem).readWithPadding 64 32 =
        UInt256.toByteArray ⟨128⟩ :=
    initialHealSinCalldataMem_read64 I
  have hmload64Sin :
      (if (⟨64⟩ : UInt256).toNat ≥ (healSinCalldataMem I solcFreePtrMem).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          ((healSinCalldataMem I solcFreePtrMem).readWithPadding
            (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [hSinMem]; decide) (by decide) hSinRead64
  have rd921 := evm_run rd852 with [
    push1 ⟨64⟩,
    dup1,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide)
      mem_cost hmload64 (by decide) (by evm_ov),
    push4 ⟨2016186517⟩,
    push1 ⟨225⟩,
    shl,
    dup2,
    raw mstore 6 (healSinSelectorMem solcFreePtrMem) (UInt256.ofNat 5)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    uniswapAddress,
    push1 ⟨4⟩,
    dup3,
    add,
    raw mstore 3 (healSinCalldataMem I solcFreePtrMem) (UInt256.ofNat 6)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    swap1,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 6) (by native_decide)
      mem_cost hmload64Sin (by decide) (by evm_ov),
    push1 ⟨0⟩,
    swap3,
    push2 ⟨993⟩,
    swap3,
    push2 ⟨985⟩,
    swap3,
    push1 ⟨1⟩,
    push1 ⟨1⟩,
    push1 ⟨160⟩,
    shl,
    sub,
    swap1,
    swap3,
    and,
    swap2,
    push4 healSinSelector,
    swap2,
    push1 ⟨36⟩,
    dup1,
    dup3,
    add,
    swap3,
    push1 ⟨32⟩,
    swap3,
    swap1,
    swap2,
    swap1,
    dup3,
    swap1,
    sub,
    add,
    dup2,
    dup7,
    dup1]
  exact ⟨_, _, by
    simpa [target, rawTarget, kissDaiTargetWord, healSinSelectorShifted, healSinSelector,
      healSinSelectorMem, healSinCalldataMem, healSinOutPtr, healSinInSize, healSinEndPtr,
      vowSlotWord, solcSlotWord, solcAddrMask] using rd921⟩

theorem RD.vowFlapVatSin0NoCode
    {cA gh bl σ σ₀ A I} {g sel : UInt256}
    (hreach : ∃ k C, RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨349⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hcodeSize :
      Reasoning.Theory.uniswapExtCodeSizeWord σ (kissDaiTargetWord σ I) = ⟨0⟩) :
    RDrev vowBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) := by
  obtain ⟨_, _, rd921⟩ := RD.vowFlapToSin0ExtcodesizeGuard hreach
  exact RD.uniswapExtcodesizeGuardMissing (pc := ⟨921⟩) (okPc := ⟨933⟩) rd921
    hcodeSize
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by simp)

theorem vowFlapSourceVatSin0NoCode
    {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hvatNoCode :
      (UInt256.ofNat
        (((initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (kissVatAddress σ I)).option 0 (fun acc => acc.code.size))).toNat = 0) :
    let locals := (∅ : Store)
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals flapTransition.body .reverted := by
  intro locals evm0
  have hvat :
      evalExpr? config { contract := contract, locals := locals } evm0 (.storage vatRef) =
        .ok (.address (kissVatAddress σ I)) := by
    simpa [evm0, initState, kissVatAddress, vowAddressReturnWord, vowSlotWord] using
      evalExpr_kissVatStorage (evm := evm0) (locals := locals) (by simp [locals])
  have hguard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool false) := by
    exact evalExpr_kissVatCodeGuard_false hvat (by simpa [evm0] using hvatNoCode)
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 flapTransition.body
        .reverted := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    exact ExecBlock.consRevert (ExecStmt.requireFalse hguard)
  simpa [ExecTransitionBody, evm0, locals, flapTransition, nonpayable,
    checkedExternalCallStmts] using ExecFuncBody.execBlockRevert hblock

theorem vowFlapVatSin0NoCodeBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g sel : UInt256}
    (hcode : I.code = vowBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some flapTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (flapTransition.params.map Param.name)
        (transitionSignature flapTransition).paramTypes I.calldata = some ∅)
    (hreach : ∃ k C, RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨349⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hcodeSize :
      Reasoning.Theory.uniswapExtCodeSizeWord σ_evm (kissDaiTargetWord σ_evm I) = ⟨0⟩) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hrev := RD.vowFlapVatSin0NoCode hreach hcodeSize
  have hVat : vowSlotWord ⟨1⟩ σ_evm I = vowSlotWord ⟨1⟩ σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨1⟩ ⟨0⟩
  have hTarget : kissDaiTargetWord σ_evm I = kissDaiTargetWord σ_solm I := by
    simp [kissDaiTargetWord, hVat]
  have hcodeSizeSolm :
      Reasoning.Theory.uniswapExtCodeSizeWord σ_solm (kissDaiTargetWord σ_solm I) = ⟨0⟩ := by
    have hsame :=
      Reasoning.Theory.uniswapExtCodeSizeWord_accountMapEquiv hAccounts
        (kissDaiTargetWord σ_evm I)
    rw [← hTarget, ← hsame]
    exact hcodeSize
  have haddr :
      kissVatAddress σ_solm I =
        AccountAddress.ofUInt256 (kissDaiTargetWord σ_solm I) :=
    kissVatAddress_eq_daiTarget_account σ_solm I
  have hvatNoCode :
      (UInt256.ofNat
        (((initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (kissVatAddress σ_solm I)).option 0 (fun acc => acc.code.size))).toNat = 0 := by
    simpa [initState, State.lookupAccount] using
      uniswapExtCodeSizeWord_zero_lookup_code_zero
        (σ := σ_solm) (target := kissDaiTargetWord σ_solm I)
        (addr := kissVatAddress σ_solm I) haddr hcodeSizeSolm
  have hbody := vowFlapSourceVatSin0NoCode (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g) hwv hvatNoCode
  exact hrev.reEquivExecutionRevert hcode hdispatch hdecode (by simpa using hbody)

end Benchmarks.Dss.Vow
