import Benchmarks.Dss.Vow.HealSuccess
import Benchmarks.Dss.Vow.VatDaiCall
import Benchmarks.Dss.Vow.VatSinCall

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.Vow

/-! ## `flop()` -/

abbrev flopLocalsVatSin (vatSin : UInt256) : Store :=
  (∅ : Store).insert "vatSin" (.int (Int.ofNat vatSin.toNat))

abbrev flopLocalsVatSinFreeSin (vatSin freeSin : UInt256) : Store :=
  (flopLocalsVatSin vatSin).insert "freeSin" (.int (Int.ofNat freeSin.toNat))

abbrev flopLocalsVatSinFreeSinDebt (vatSin freeSin flopDebt : UInt256) : Store :=
  (flopLocalsVatSinFreeSin vatSin freeSin).insert "flopDebt"
    (.int (Int.ofNat flopDebt.toNat))

theorem flopLocalsVatSin_get_vatSin (vatSin : UInt256) :
    (flopLocalsVatSin vatSin).get? "vatSin" =
      some (.int (Int.ofNat vatSin.toNat)) := by
  rw [flopLocalsVatSin, store_get_self]

theorem flopLocalsVatSinFreeSin_get_vatSin (vatSin freeSin : UInt256) :
    (flopLocalsVatSinFreeSin vatSin freeSin).get? "vatSin" =
      some (.int (Int.ofNat vatSin.toNat)) := by
  rw [flopLocalsVatSinFreeSin, store_get_ne _ _ (by decide), flopLocalsVatSin_get_vatSin]

theorem flopLocalsVatSinFreeSin_get_freeSin (vatSin freeSin : UInt256) :
    (flopLocalsVatSinFreeSin vatSin freeSin).get? "freeSin" =
      some (.int (Int.ofNat freeSin.toNat)) := by
  rw [flopLocalsVatSinFreeSin, store_get_self]

theorem flopLocalsVatSinFreeSinDebt_get_freeSin
    (vatSin freeSin flopDebt : UInt256) :
    (flopLocalsVatSinFreeSinDebt vatSin freeSin flopDebt).get? "freeSin" =
      some (.int (Int.ofNat freeSin.toNat)) := by
  rw [flopLocalsVatSinFreeSinDebt, store_get_ne _ _ (by decide),
    flopLocalsVatSinFreeSin_get_freeSin]

theorem flopLocalsVatSinFreeSinDebt_get_flopDebt
    (vatSin freeSin flopDebt : UInt256) :
    (flopLocalsVatSinFreeSinDebt vatSin freeSin flopDebt).get? "flopDebt" =
      some (.int (Int.ofNat flopDebt.toNat)) := by
  rw [flopLocalsVatSinFreeSinDebt, store_get_self]

abbrev flopSumpEvaledRef : EvaledStorageRef :=
  { base := "sump", steps := [] }

theorem evalExpr_flopSumpStorage (evm : EVM.State) {locals : Store}
    (hbase : locals.get? "sump" = none) :
    evalExpr? config { contract := contract, locals := locals } evm (.storage sumpRef) =
      .ok (.int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨9⟩).toNat)) := by
  rw [evalExpr_storage_scalar (er := flopSumpEvaledRef) (t := .int uint256Int)
    (loc := wordLoc ⟨9⟩)]
  · exact congrArg EvalResult.ok (vowStorageLocLoad_uint256 _ ⟨9⟩)
  · exact hbase
  · simp [flopSumpEvaledRef, sumpRef, evalStorageRef, evalStorageRefSteps,
      EvalResult.bind, pure, bind]
  · simp [storageTypeAt?, contract, storageDecls, uint256St]
  · funext evm
    simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw, flopSumpEvaledRef]

theorem vowDispatch_flop {I : ExecutionEnv}
    (hsel : selIs I ⟨#[0xbb, 0xbb, 0x0d, 0x7b]⟩) :
    dispatchMsg contract I.calldata = some flopTransition := by
  apply dispatchMsg_eq_some_of_split (hfallback := by rfl)
    (pre := [AshTransition, SinTransition, bumpTransition, cageTransition, denyTransition,
      dumpTransition, fessTransition, fileUintTransition, fileAddressTransition, flapTransition,
      flapperTransition, flogTransition])
    (post := [flopperTransition, healTransition, humpTransition, kissTransition, liveTransition,
      relyTransition, sinTransition, sumpTransition, vatTransition, waitTransition,
      wardsTransition])
    (ti := flopTransition)
    (htr := by rfl)
  · intro t ht
    have hcd : I.calldata.extract 0 4 = (⟨#[0xbb, 0xbb, 0x0d, 0x7b]⟩ : ByteArray) :=
      (byteArray_eq_of_beq hsel).symm
    simp at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl
    all_goals
      simp [selectorOf, AshSelectorBytes, SinSelectorBytes, bumpSelectorBytes,
        cageSelectorBytes, denySelectorBytes, dumpSelectorBytes, fessSelectorBytes,
        fileUintSelectorBytes, fileAddressSelectorBytes, flapSelectorBytes, flapperSelectorBytes,
        flogSelectorBytes, hcd]
      native_decide
  · rw [selectorOf, flopSelectorBytes]
    exact hsel

theorem vowDecode_flop {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (flopTransition.params.map Param.name)
      (transitionSignature flopTransition).paramTypes I.calldata = some ∅ := by
  show decodeCalldataWithMode config.abiDecodeMode [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz

theorem vowReachFlopBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = vowBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0xbb, 0xbb, 0x0d, 0x7b]⟩) :
    ∃ k C, RD vowBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨646⟩ [vowSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  have hword : vowSelWord I = ⟨3149598075⟩ :=
    vowSelWord_eq_of_beq I hsz 0xbb 0xbb 0x0d 0x7b ⟨3149598075⟩
      (by native_decide) hsel
  have hroot : UInt256.gt (armSelNat vowBytecode vowRootSplitPc) (vowSelWord I) = ⟨0⟩ := by
    rw [hword]
    native_decide
  have hhigh : UInt256.gt (armSelNat vowBytecode vowHighSplitPc) (vowSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  have heq0 : ∀ j, j < 3 →
      UInt256.eq (armSelNat vowBytecode (nthArmPc vowBytecode vowHighLowFirstArmPc j))
        (vowSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j <;> rw [hword] <;> native_decide
  have htake :
      UInt256.eq (armSelNat vowBytecode (nthArmPc vowBytecode vowHighLowFirstArmPc 3))
        (vowSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  exact vowReachHighLowBody 3 (by omega) ⟨646⟩ hcode hwv hsz hsize hroot hhigh heq0
    htake (by jump_dest) (by native_decide)

theorem RD.vowFlopToSin0ExtcodesizeGuard
    {cA gh bl σ σ₀ A I} {g sel : UInt256}
    (hreach : ∃ k C, RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨646⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3663⟩
      (kissDaiTargetWord σ I :: kissDaiTargetWord σ I :: healSinOutPtr ::
        healSinInSize :: healSinOutPtr :: ⟨32⟩ :: healSinEndPtr :: healSinSelector ::
        kissDaiTargetWord σ I :: ⟨1325⟩ :: ⟨3675⟩ :: ⟨0⟩ :: ⟨357⟩ :: sel :: [])
      (healSinCalldataMem I solcFreePtrMem) (UInt256.ofNat 6) ByteArray.empty (cA, σ) k C := by
  let target := kissDaiTargetWord σ I
  let rawTarget := vowSlotWord ⟨1⟩ σ I
  obtain ⟨_, _, rd646⟩ := hreach
  have rd647 := rd646.jumpdest (by native_decide) (by evm_ov)
  have rd650 := rd647.push2 ⟨357⟩ (by native_decide) (by evm_ov)
  have rd653 := rd650.push2 ⟨3589⟩ (by native_decide) (by evm_ov)
  have rd3589 := by
    simpa using rd653.jump (by native_decide) (by jump_dest) (by evm_ov)
  have rd3590 := rd3589.jumpdest (by native_decide) (by evm_ov)
  have rd3592 := rd3590.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  obtain ⟨k3592, C3592, rd3593₀⟩ := rd3592.sload (by native_decide) (by evm_ov)
  have rd3593 : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3593⟩
      (rawTarget :: ⟨357⟩ :: sel :: []) solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k3592 C3592 := by
    simpa [rawTarget, vowSlotWord, solcSlotWord] using rd3593₀
  have hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ solcFreePtrMem.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 3 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (solcFreePtrMem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    solcFreePtrMem_mload64
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
  have rd3663 := evm_run rd3593 with [
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
    address,
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
    push2 ⟨3675⟩,
    swap3,
    push2 ⟨1325⟩,
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
      vowSlotWord, solcSlotWord, solcAddrMask] using rd3663⟩

theorem RD.vowFlopVatSin0NoCode
    {cA gh bl σ σ₀ A I} {g sel : UInt256}
    (hreach : ∃ k C, RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨646⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (kissDaiTargetWord σ I) = ⟨0⟩) :
    RDrev vowBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) := by
  obtain ⟨_, _, rd3663⟩ := RD.vowFlopToSin0ExtcodesizeGuard hreach
  exact RD.solcExtcodesizeGuardMissing (pc := ⟨3663⟩) (okPc := ⟨1273⟩) rd3663
    hcodeSize
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by simp)

theorem RD.vowFlopToSin0Staticcall
    {cA gh bl σ σ₀ A I} {g sel : UInt256}
    (hreach : ∃ k C, RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨646⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (kissDaiTargetWord σ I) ≠ ⟨0⟩) :
    ∃ gasWord k C, RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1276⟩
      (gasWord :: kissDaiTargetWord σ I :: healSinOutPtr ::
        healSinInSize :: healSinOutPtr :: ⟨32⟩ :: healSinEndPtr :: healSinSelector ::
        kissDaiTargetWord σ I :: ⟨1325⟩ :: ⟨3675⟩ :: ⟨0⟩ :: ⟨357⟩ :: sel :: [])
      (healSinCalldataMem I solcFreePtrMem) (UInt256.ofNat 6) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd3663⟩ := RD.vowFlopToSin0ExtcodesizeGuard hreach
  obtain ⟨gasWord, k, C, rd1276⟩ :=
    RD.solcExtcodesizeGuardOkGas (pc := ⟨3663⟩) (okPc := ⟨1273⟩) rd3663
      hcodeSize
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by jump_dest) (by native_decide)
      (by native_decide) (by native_decide) (by evm_ov)
  exact ⟨gasWord, k, C, rd1276⟩

theorem RD.vowFlopSin0PostCall
    {cA gh bl σ σ₀ A I} {g sel : UInt256}
    (hreach : ∃ k C, RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨646⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (kissDaiTargetWord σ I) ≠ ⟨0⟩)
    (hdepth : I.depth.val < 1024) :
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap) (z : Bool)
      (o : ByteArray) (A' : Substate) (k C : ℕ),
      RD vowBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1277⟩
        ((if z then ⟨1⟩ else ⟨0⟩) :: healSinEndPtr :: healSinSelector ::
          kissDaiTargetWord σ I :: ⟨1325⟩ :: ⟨3675⟩ :: ⟨0⟩ :: ⟨357⟩ :: sel :: [])
        (o.write 0 (healSinCalldataMem I solcFreePtrMem) 128
          (min (⟨32⟩ : UInt256) (UInt256.ofNat o.size)).toNat)
        (UInt256.ofNat 6) o (cA', σ') k C
    ∧ typedCallViaEVM config (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (kissVatAddress σ I)) "sin" 0 [.address I.codeOwner]
        (z, { initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := σ', substate := A', createdAccounts := cA' }, o) false
    ∧ o.size < UInt256.size := by
  obtain ⟨gasWord, _, _, rd1276⟩ :=
    RD.vowFlopToSin0Staticcall hreach hcodeSize
  obtain ⟨cA', σ', z, o, A_in, callGas, k1277, C1277, hΘpack, rd1277raw, hosz⟩ :=
    RD.solcStaticcall rd1276 (by native_decide) hdepth (by evm_ov)
  obtain ⟨g'', A', hΘ⟩ := hΘpack
  refine ⟨cA', σ', z, o, A', k1277, C1277, ?_, ?_, hosz⟩
  · have haw :
        UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 6).toNat
          healSinOutPtr.toNat healSinInSize.toNat)
          healSinOutPtr.toNat (⟨32⟩ : UInt256).toNat) = UInt256.ofNat 6 := by
      rw [healSinInSize_eq]
      native_decide
    have hoff : healSinOutPtr.toNat = 128 := by
      native_decide
    have rd1277 : RD vowBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1277⟩
        ((if z then ⟨1⟩ else ⟨0⟩) :: healSinEndPtr :: healSinSelector ::
          kissDaiTargetWord σ I :: ⟨1325⟩ :: ⟨3675⟩ :: ⟨0⟩ :: ⟨357⟩ :: sel :: [])
        (o.write 0 (healSinCalldataMem I solcFreePtrMem) healSinOutPtr.toNat
          (min (⟨32⟩ : UInt256) (UInt256.ofNat o.size)).toNat)
        (UInt256.ofNat 6) o (cA', σ') k1277 C1277 :=
      haw ▸ rd1277raw
    rw [hoff] at rd1277
    exact rd1277
  · refine callCoincides (A_in := A_in) (g'' := g'') (callGas := callGas)
      (callPerm := false) (targetWord := kissDaiTargetWord σ I)
      (mem := healSinCalldataMem I solcFreePtrMem) (inOff := healSinOutPtr)
      (inSize := healSinInSize)
      (fun h => absurd hdepth (by rw [show I.depth = (1024 : Fin 1025) from h]; decide))
      (kissVatAddress_eq_daiTarget σ I) (initialHealSinEncode_eq I) ?_
    simpa [initState] using hΘ

theorem vowFlopSourceVatSin0NoCode
    {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hvatNoCode :
      (UInt256.ofNat
        (((initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (kissVatAddress σ I)).option 0 (fun acc => acc.code.size))).toNat = 0) :
    let locals := (∅ : Store)
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals flopTransition.body .reverted := by
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
      ExecBlock config { contract := contract, locals := locals } evm0 flopTransition.body
        .reverted := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    exact ExecBlock.consRevert (ExecStmt.requireFalse hguard)
  simpa [ExecTransitionBody, evm0, locals, flopTransition, nonpayable,
    checkedExternalCallStmts] using ExecFuncBody.execBlockRevert hblock

theorem vowFlopSourceVatSin0CallFailure
    {cA gh bl σ σ₀ A I} {g : UInt256} {evmSin : EVM.State} {outSin : ByteArray}
    (hwv : I.weiValue = ⟨0⟩)
    (hvatCode :
      0 < (UInt256.ofNat
        (((initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (kissVatAddress σ I)).option 0 (fun acc => acc.code.size))).toNat)
    (hcallSin :
      typedCallViaEVM config (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (kissVatAddress σ I)) "sin" 0 [.address I.codeOwner]
        (false, evmSin, outSin) false) :
    let locals := (∅ : Store)
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals flopTransition.body .reverted := by
  intro locals evm0
  have hvat :
      evalExpr? config { contract := contract, locals := locals } evm0 (.storage vatRef) =
        .ok (.address (kissVatAddress σ I)) := by
    simpa [evm0, initState, kissVatAddress, vowAddressReturnWord, vowSlotWord] using
      evalExpr_kissVatStorage (evm := evm0) (locals := locals) (by simp [locals])
  have hguard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool true) := by
    exact evalExpr_kissVatCodeGuard_true hvat (by simpa [evm0] using hvatCode)
  have hargs :
      evalExprs? config { contract := contract, locals := locals } evm0 [thisAddr] =
        .ok [.address I.codeOwner] := by
    simpa [evm0, initState] using evalExprs_kissThis evm0 locals
  have hcallStmt :
      ExecStmt config { contract := contract, locals := locals } evm0
        (.externalCall (.storage vatRef) "sin" (.intLit 0) [thisAddr] "vatSin"
          (perm := false))
        .reverted := by
    exact ExecStmt.externalCallFailure hvat (by simp [evalExpr?, pure]) hargs hcallSin
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 flopTransition.body
        .reverted := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
    exact ExecBlock.consRevert hcallStmt
  simpa [ExecTransitionBody, evm0, locals, flopTransition, nonpayable,
    checkedExternalCallStmts] using ExecFuncBody.execBlockRevert hblock

theorem RD.vowFlopSin0ReturnDecodeShortReverts
    {cA gh bl σ σ₀ A I} {g : UInt256} {sel : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {k C : ℕ} {d0 d1 d2 : UInt256}
    (rd : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1295⟩
      (d0 :: d1 :: d2 :: ⟨1325⟩ :: ⟨3675⟩ :: ⟨0⟩ :: ⟨357⟩ :: sel :: [])
      mem (UInt256.ofNat 6) o acc k C)
    (hshort : o.size < 32)
    (hhi : o.size < UInt256.size)
    (hMload64Value :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩) :
    RDrev vowBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) := by
  exact RD.solcUint256ReturnWordDecodeShortReverts (pc := ⟨1295⟩) (okPc := ⟨1315⟩) rd
    hshort hhi
    mem_cost (by decide) hMload64Value
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by simp)

theorem RD.vowFlopSin0ReturnDecodeOk
    {cA gh bl σ σ₀ A I} {g : UInt256} {sel retWord : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {k C : ℕ} {d0 d1 d2 : UInt256}
    (rd : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1295⟩
      (d0 :: d1 :: d2 :: ⟨1325⟩ :: ⟨3675⟩ :: ⟨0⟩ :: ⟨357⟩ :: sel :: [])
      mem (UInt256.ofNat 6) o acc k C)
    (hlo : 32 ≤ o.size)
    (hhi : o.size < UInt256.size)
    (hMload64Value :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩)
    (hMload128Value :
      (if (⟨128⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨128⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding (⟨128⟩ : UInt256).toNat 32))) =
        retWord) :
    ∃ k' C', RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1318⟩
      (retWord :: ⟨1325⟩ :: ⟨3675⟩ :: ⟨0⟩ :: ⟨357⟩ :: sel :: [])
      mem (UInt256.ofNat 6) o acc k' C' := by
  exact RD.solcUint256ReturnWordDecodeOk (pc := ⟨1295⟩) (okPc := ⟨1315⟩) rd
    hlo hhi
    mem_cost (by decide) hMload64Value hMload128Value mem_cost (by decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by jump_dest) (by native_decide) (by native_decide) (by native_decide) (by evm_ov)

theorem RD.vowFlopFreeSinSubUnderflow
    {cA gh bl σ σ₀ A I} {g sel vatSin : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {k C : ℕ}
    (rd : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1318⟩
      (vatSin :: ⟨1325⟩ :: ⟨3675⟩ :: ⟨0⟩ :: ⟨357⟩ :: sel :: [])
      mem (UInt256.ofNat 6) o acc k C)
    (hlt : vatSin.toNat < (vowSlotWord ⟨5⟩ acc.2 I).toNat) :
    RDrev vowBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) := by
  let SinVal := vowSlotWord ⟨5⟩ acc.2 I
  have rd1320 := rd.push1 ⟨5⟩ (by native_decide) (by evm_ov)
  obtain ⟨k1321, C1321, rd1321Raw⟩ := rd1320.sload (by native_decide) (by evm_ov)
  have rd1321 : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1321⟩
      (SinVal :: vatSin :: ⟨1325⟩ :: ⟨3675⟩ :: ⟨0⟩ :: ⟨357⟩ :: sel :: [])
      mem (UInt256.ofNat 6) o acc k1321 C1321 := by
    simpa [SinVal, vowSlotWord, solcSlotWord] using rd1321Raw
  have rd1324 := rd1321.push2 ⟨5096⟩ (by native_decide) (by evm_ov)
  have rd5096 := rd1324.jump (by native_decide) (by jump_dest) (by evm_ov)
  exact RD.solcCheckedSubEmptyRevertAnyWords
    (code := vowBytecode) (pc := ⟨5096⟩) (okPc := ⟨5090⟩)
    (a := vatSin) (b := SinVal) (ret := ⟨1325⟩)
    (R := [⟨3675⟩, ⟨0⟩, ⟨357⟩, sel])
    (by simpa [SinVal] using rd5096)
    (by
      unfold solcCheckedSubEmptyRevertWf solcCheckedSubSuccessWf
      repeat' first | apply And.intro | native_decide)
    (by simpa [SinVal] using hlt)
    (by simp)

theorem RD.vowFlopFreeSinSubSuccess
    {cA gh bl σ σ₀ A I} {g sel vatSin : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {k C : ℕ}
    (rd : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1318⟩
      (vatSin :: ⟨1325⟩ :: ⟨3675⟩ :: ⟨0⟩ :: ⟨357⟩ :: sel :: [])
      mem (UInt256.ofNat 6) o acc k C)
    (hle : (vowSlotWord ⟨5⟩ acc.2 I).toNat ≤ vatSin.toNat) :
    ∃ k' C', RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1325⟩
      (UInt256.sub vatSin (vowSlotWord ⟨5⟩ acc.2 I) ::
        ⟨3675⟩ :: ⟨0⟩ :: ⟨357⟩ :: sel :: [])
      mem (UInt256.ofNat 6) o acc k' C' := by
  let SinVal := vowSlotWord ⟨5⟩ acc.2 I
  have rd1320 := rd.push1 ⟨5⟩ (by native_decide) (by evm_ov)
  obtain ⟨k1321, C1321, rd1321Raw⟩ := rd1320.sload (by native_decide) (by evm_ov)
  have rd1321 : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1321⟩
      (SinVal :: vatSin :: ⟨1325⟩ :: ⟨3675⟩ :: ⟨0⟩ :: ⟨357⟩ :: sel :: [])
      mem (UInt256.ofNat 6) o acc k1321 C1321 := by
    simpa [SinVal, vowSlotWord, solcSlotWord] using rd1321Raw
  have rd1324 := rd1321.push2 ⟨5096⟩ (by native_decide) (by evm_ov)
  have rd5096 := rd1324.jump (by native_decide) (by jump_dest) (by evm_ov)
  obtain ⟨k1325, C1325, rd1325⟩ := RD.solcCheckedSubSuccess
    (code := vowBytecode) (pc := ⟨5096⟩) (okPc := ⟨5090⟩)
    (a := vatSin) (b := SinVal) (ret := ⟨1325⟩)
    (R := [⟨3675⟩, ⟨0⟩, ⟨357⟩, sel])
    (by simpa [SinVal] using rd5096)
    (by
      unfold solcCheckedSubSuccessWf
      repeat' first | apply And.intro | native_decide)
    (by simpa [SinVal] using hle) (by jump_dest) (by jump_dest) (by simp)
  exact ⟨k1325, C1325, by simpa [SinVal] using rd1325⟩

theorem RD.vowFlopDebtSubUnderflow
    {cA gh bl σ σ₀ A I} {g sel freeSin : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {k C : ℕ}
    (rd : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1325⟩
      (freeSin :: ⟨3675⟩ :: ⟨0⟩ :: ⟨357⟩ :: sel :: [])
      mem (UInt256.ofNat 6) o acc k C)
    (hlt : freeSin.toNat < (vowSlotWord ⟨6⟩ acc.2 I).toNat) :
    RDrev vowBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) := by
  let AshVal := vowSlotWord ⟨6⟩ acc.2 I
  have rd1326 := rd.jumpdest (by native_decide) (by evm_ov)
  have rd1328 := rd1326.push1 ⟨6⟩ (by native_decide) (by evm_ov)
  obtain ⟨k1329, C1329, rd1329Raw⟩ := rd1328.sload (by native_decide) (by evm_ov)
  have rd1329 : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1329⟩
      (AshVal :: freeSin :: ⟨3675⟩ :: ⟨0⟩ :: ⟨357⟩ :: sel :: [])
      mem (UInt256.ofNat 6) o acc k1329 C1329 := by
    simpa [AshVal, vowSlotWord, solcSlotWord] using rd1329Raw
  have rd1332 := rd1329.push2 ⟨5096⟩ (by native_decide) (by evm_ov)
  have rd5096 := rd1332.jump (by native_decide) (by jump_dest) (by evm_ov)
  exact RD.solcCheckedSubEmptyRevertAnyWords
    (code := vowBytecode) (pc := ⟨5096⟩) (okPc := ⟨5090⟩)
    (a := freeSin) (b := AshVal) (ret := ⟨3675⟩)
    (R := [⟨0⟩, ⟨357⟩, sel])
    (by simpa [AshVal] using rd5096)
    (by
      unfold solcCheckedSubEmptyRevertWf solcCheckedSubSuccessWf
      repeat' first | apply And.intro | native_decide)
    (by simpa [AshVal] using hlt)
    (by simp)

theorem RD.vowFlopDebtSubSuccess
    {cA gh bl σ σ₀ A I} {g sel freeSin : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {k C : ℕ}
    (rd : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1325⟩
      (freeSin :: ⟨3675⟩ :: ⟨0⟩ :: ⟨357⟩ :: sel :: [])
      mem (UInt256.ofNat 6) o acc k C)
    (hle : (vowSlotWord ⟨6⟩ acc.2 I).toNat ≤ freeSin.toNat) :
    ∃ k' C', RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3675⟩
      (UInt256.sub freeSin (vowSlotWord ⟨6⟩ acc.2 I) :: ⟨0⟩ :: ⟨357⟩ :: sel :: [])
      mem (UInt256.ofNat 6) o acc k' C' := by
  let AshVal := vowSlotWord ⟨6⟩ acc.2 I
  have rd1326 := rd.jumpdest (by native_decide) (by evm_ov)
  have rd1328 := rd1326.push1 ⟨6⟩ (by native_decide) (by evm_ov)
  obtain ⟨k1329, C1329, rd1329Raw⟩ := rd1328.sload (by native_decide) (by evm_ov)
  have rd1329 : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1329⟩
      (AshVal :: freeSin :: ⟨3675⟩ :: ⟨0⟩ :: ⟨357⟩ :: sel :: [])
      mem (UInt256.ofNat 6) o acc k1329 C1329 := by
    simpa [AshVal, vowSlotWord, solcSlotWord] using rd1329Raw
  have rd1332 := rd1329.push2 ⟨5096⟩ (by native_decide) (by evm_ov)
  have rd5096 := rd1332.jump (by native_decide) (by jump_dest) (by evm_ov)
  obtain ⟨k3675, C3675, rd3675⟩ := RD.solcCheckedSubSuccess
    (code := vowBytecode) (pc := ⟨5096⟩) (okPc := ⟨5090⟩)
    (a := freeSin) (b := AshVal) (ret := ⟨3675⟩)
    (R := [⟨0⟩, ⟨357⟩, sel])
    (by simpa [AshVal] using rd5096)
    (by
      unfold solcCheckedSubSuccessWf
      repeat' first | apply And.intro | native_decide)
    (by simpa [AshVal] using hle) (by jump_dest) (by jump_dest) (by simp)
  exact ⟨k3675, C3675, by simpa [AshVal] using rd3675⟩

set_option maxHeartbeats 1000000 in
theorem RD.vowFlopInsufficientDebt
    {cA gh bl σ σ₀ A I} {g : UInt256} {sel flopDebt : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {k C : ℕ}
    (rd : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3675⟩
      (flopDebt :: ⟨0⟩ :: ⟨357⟩ :: sel :: [])
      mem (UInt256.ofNat 6) o acc k C)
    (hinsuff : flopDebt.toNat < (vowSlotWord ⟨9⟩ acc.2 I).toNat)
    (hmem : mem.size = 164)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    RDrev vowBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) := by
  let SumpVal := vowSlotWord ⟨9⟩ acc.2 I
  have rd3676 := rd.jumpdest (by native_decide) (by evm_ov)
  have rd3678 := rd3676.push1 ⟨9⟩ (by native_decide) (by evm_ov)
  obtain ⟨k3679, C3679, rd3679Raw⟩ := rd3678.sload (by native_decide) (by evm_ov)
  have rd3679 : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3679⟩
      (SumpVal :: flopDebt :: ⟨0⟩ :: ⟨357⟩ :: sel :: [])
      mem (UInt256.ofNat 6) o acc k3679 C3679 := by
    simpa [SumpVal, vowSlotWord, solcSlotWord] using rd3679Raw
  have rd3680₀ := rd3679.gt (by native_decide) (by evm_ov)
  have hgt : UInt256.gt SumpVal flopDebt = ⟨1⟩ :=
    ugt_one (by simpa [SumpVal] using hinsuff)
  have rd3680 := rd3680₀
  rw [hgt] at rd3680
  have rd3681₀ := rd3680.iszero (by native_decide) (by evm_ov)
  have rd3681 := rd3681₀
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd3681
  have rd3684 := rd3681.push2 ⟨3753⟩ (by native_decide) (by evm_ov)
  have rd3685 := rd3684.jumpiNT (by native_decide)
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩) (by evm_ov)
  have rd3689 := evm_run rd3685 with [
    push1 ⟨64⟩,
    dup1,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 6) (by native_decide)
      mem_cost
      (mloadFreePtrValue (by rw [hmem]; decide) (by decide) hread64)
      (by decide) (by evm_ov)]
  have rd3693 := rd3689.pushConst (⟨4594637⟩ : UInt256)
    (width := 3) (op := .PUSH3) (by decide) (by native_decide) (by evm_ov)
  have rd3712 := evm_run rd3693 with [
    push1 ⟨229⟩,
    shl,
    dup2,
    raw mstore 0 (solcErrorStringMem0 mem) (UInt256.ofNat 6) (by native_decide)
      mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨32⟩,
    push1 ⟨4⟩,
    dup3,
    add,
    raw mstore 0 (solcErrorStringMem1 mem) (UInt256.ofNat 6) (by native_decide)
      mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨21⟩,
    push1 ⟨36⟩,
    dup3,
    add,
    raw mstore 3 (solcErrorStringMem2 (⟨21⟩ : UInt256) mem)
      (UInt256.ofNat 7) (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov)]
  have rd3734 := rd3712.pushConst vowInsufficientDebtRawWord
    (width := 21) (op := .PUSH21) (by decide) (by native_decide) (by evm_ov)
  have rd3737₀ := evm_run rd3734 with [
    push1 ⟨90⟩,
    shl]
  have rd3737 := rd3737₀
  rw [show UInt256.shiftLeft vowInsufficientDebtRawWord ⟨90⟩ =
      vowInsufficientDebtStringWord from rfl] at rd3737
  exact evm_run rd3737 with [
    push1 ⟨68⟩,
    dup3,
    add,
    raw mstore 3
      (solcErrorStringMem3 (⟨21⟩ : UInt256) vowInsufficientDebtStringWord mem)
      (UInt256.ofNat 8) (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    swap1,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) (by native_decide)
      mem_cost
      (solcErrorStringMem3_mload64_of_size164 (⟨21⟩ : UInt256)
        vowInsufficientDebtStringWord hmem hread64)
      (by decide) (by evm_ov),
    swap1,
    dup2,
    swap1,
    sub,
    push1 ⟨100⟩,
    add,
    swap1,
    raw rev 0 (by native_decide) mem_cost (by evm_ov)]

theorem RD.vowFlopDebtEnough
    {cA gh bl σ σ₀ A I} {g : UInt256} {sel flopDebt : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {k C : ℕ}
    (rd : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3675⟩
      (flopDebt :: ⟨0⟩ :: ⟨357⟩ :: sel :: [])
      mem (UInt256.ofNat 6) o acc k C)
    (henough : (vowSlotWord ⟨9⟩ acc.2 I).toNat ≤ flopDebt.toNat) :
    ∃ k' C', RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3753⟩
      (⟨0⟩ :: ⟨357⟩ :: sel :: []) mem (UInt256.ofNat 6) o acc k' C' := by
  let SumpVal := vowSlotWord ⟨9⟩ acc.2 I
  have rd3676 := rd.jumpdest (by native_decide) (by evm_ov)
  have rd3678 := rd3676.push1 ⟨9⟩ (by native_decide) (by evm_ov)
  obtain ⟨k3679, C3679, rd3679Raw⟩ := rd3678.sload (by native_decide) (by evm_ov)
  have rd3679 : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3679⟩
      (SumpVal :: flopDebt :: ⟨0⟩ :: ⟨357⟩ :: sel :: [])
      mem (UInt256.ofNat 6) o acc k3679 C3679 := by
    simpa [SumpVal, vowSlotWord, solcSlotWord] using rd3679Raw
  have rd3680₀ := rd3679.gt (by native_decide) (by evm_ov)
  have hgt : UInt256.gt SumpVal flopDebt = ⟨0⟩ :=
    ugt_zero (by simpa [SumpVal] using henough)
  have rd3680 := rd3680₀
  rw [hgt] at rd3680
  have rd3681₀ := rd3680.iszero (by native_decide) (by evm_ov)
  have rd3681 := rd3681₀
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd3681
  have rd3684 := rd3681.push2 ⟨3753⟩ (by native_decide) (by evm_ov)
  exact ⟨_, _, rd3684.jumpiT (by native_decide)
    (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩) (by jump_dest) (by evm_ov)⟩

theorem RD.vowFlopToDai1ExtcodesizeGuard
    {cA gh bl σ σ₀ A I} {g sel flopDebt : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {k C : ℕ}
    (rd : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3675⟩
      (flopDebt :: ⟨0⟩ :: ⟨357⟩ :: sel :: [])
      mem (UInt256.ofNat 6) o acc k C)
    (henough : (vowSlotWord ⟨9⟩ acc.2 I).toNat ≤ flopDebt.toNat)
    (hmem : mem.size = 164)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    ∃ k' C', RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3816⟩
      (kissDaiTargetWord acc.2 I :: kissDaiTargetWord acc.2 I :: ⟨128⟩ ::
        ⟨36⟩ :: ⟨128⟩ :: ⟨32⟩ :: ⟨164⟩ :: ⟨1814410054⟩ ::
        kissDaiTargetWord acc.2 I :: ⟨0⟩ :: ⟨357⟩ :: sel :: [])
      (vatDaiCalldataMem I mem) (UInt256.ofNat 6) o acc k' C' := by
  let target := kissDaiTargetWord acc.2 I
  let rawTarget := vowSlotWord ⟨1⟩ acc.2 I
  obtain ⟨_, _, rd3753⟩ := RD.vowFlopDebtEnough rd henough
  have rd3754 := rd3753.jumpdest (by native_decide) (by evm_ov)
  have rd3756 := rd3754.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  obtain ⟨k3757, C3757, rd3757Raw⟩ := rd3756.sload (by native_decide) (by evm_ov)
  have rd3757 : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3757⟩
      (rawTarget :: ⟨0⟩ :: ⟨357⟩ :: sel :: [])
      mem (UInt256.ofNat 6) o acc k3757 C3757 := by
    simpa [rawTarget, vowSlotWord, solcSlotWord] using rd3757Raw
  have hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [hmem]; decide) (by decide) hread64
  have hDaiMem : (vatDaiCalldataMem I mem).size = 164 :=
    vatDaiCalldataMem_size I hmem
  have hDaiRead64 :
      (vatDaiCalldataMem I mem).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ :=
    vatDaiCalldataMem_read64 I hmem hread64
  have hmload64Dai :
      (if (⟨64⟩ : UInt256).toNat ≥ (vatDaiCalldataMem I mem).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          ((vatDaiCalldataMem I mem).readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [hDaiMem]; decide) (by decide) hDaiRead64
  have rd3816 := evm_run rd3757 with [
    push1 ⟨64⟩,
    dup1,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 6) (by native_decide)
      mem_cost hmload64 (by decide) (by evm_ov),
    push4 ⟨907205027⟩,
    push1 ⟨225⟩,
    shl,
    dup2,
    raw mstore 0 (vatDaiSelectorMem mem) (UInt256.ofNat 6)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    address,
    push1 ⟨4⟩,
    dup3,
    add,
    raw mstore 0 (vatDaiCalldataMem I mem) (UInt256.ofNat 6)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    swap1,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 6) (by native_decide)
      mem_cost hmload64Dai (by decide) (by evm_ov),
    push1 ⟨1⟩,
    push1 ⟨1⟩,
    push1 ⟨160⟩,
    shl,
    sub,
    swap1,
    swap3,
    and,
    swap2,
    push4 ⟨1814410054⟩,
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
    simpa [target, rawTarget, kissDaiTargetWord, kissDaiSelectorShifted,
      vatDaiSelectorMem, vatDaiCalldataMem, vowSlotWord, solcSlotWord, solcAddrMask]
      using rd3816⟩

theorem RD.vowFlopDai1NoCode
    {cA gh bl σ σ₀ A I} {g sel flopDebt : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {k C : ℕ}
    (rd : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3675⟩
      (flopDebt :: ⟨0⟩ :: ⟨357⟩ :: sel :: [])
      mem (UInt256.ofNat 6) o acc k C)
    (henough : (vowSlotWord ⟨9⟩ acc.2 I).toNat ≤ flopDebt.toNat)
    (hmem : mem.size = 164)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord acc.2 (kissDaiTargetWord acc.2 I) = ⟨0⟩) :
    RDrev vowBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) := by
  obtain ⟨_, _, rd3816⟩ :=
    RD.vowFlopToDai1ExtcodesizeGuard rd henough hmem hread64
  exact RD.solcExtcodesizeGuardMissing (pc := ⟨3816⟩) (okPc := ⟨3828⟩) rd3816
    hcodeSize
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by simp)

theorem RD.vowFlopToDai1Staticcall
    {cA gh bl σ σ₀ A I} {g sel flopDebt : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {k C : ℕ}
    (rd : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3675⟩
      (flopDebt :: ⟨0⟩ :: ⟨357⟩ :: sel :: [])
      mem (UInt256.ofNat 6) o acc k C)
    (henough : (vowSlotWord ⟨9⟩ acc.2 I).toNat ≤ flopDebt.toNat)
    (hmem : mem.size = 164)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord acc.2 (kissDaiTargetWord acc.2 I) ≠ ⟨0⟩) :
    ∃ gasWord k' C', RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3831⟩
      (gasWord :: kissDaiTargetWord acc.2 I :: ⟨128⟩ :: ⟨36⟩ ::
        ⟨128⟩ :: ⟨32⟩ :: ⟨164⟩ :: ⟨1814410054⟩ ::
        kissDaiTargetWord acc.2 I :: ⟨0⟩ :: ⟨357⟩ :: sel :: [])
      (vatDaiCalldataMem I mem) (UInt256.ofNat 6) o acc k' C' := by
  obtain ⟨_, _, rd3816⟩ :=
    RD.vowFlopToDai1ExtcodesizeGuard rd henough hmem hread64
  obtain ⟨gasWord, k3831, C3831, rd3831⟩ :=
    RD.solcExtcodesizeGuardOkGas (pc := ⟨3816⟩) (okPc := ⟨3828⟩) rd3816
      hcodeSize
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by jump_dest) (by native_decide)
      (by native_decide) (by native_decide) (by evm_ov)
  exact ⟨gasWord, k3831, C3831, rd3831⟩

theorem vowFlopSourceVatSin0DecodeRevert
    {cA gh bl σ σ₀ A I} {g : UInt256} {evmSin : EVM.State} {outSin : ByteArray}
    (hwv : I.weiValue = ⟨0⟩)
    (hvatCode :
      0 < (UInt256.ofNat
        (((initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (kissVatAddress σ I)).option 0 (fun acc => acc.code.size))).toNat)
    (hcallSin :
      typedCallViaEVM config (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (kissVatAddress σ I)) "sin" 0 [.address I.codeOwner]
        (true, evmSin, outSin) false)
    (hdecSin : config.externalABI.decode? "sin" outSin = none) :
    let locals := (∅ : Store)
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals flopTransition.body .reverted := by
  intro locals evm0
  have hvat :
      evalExpr? config { contract := contract, locals := locals } evm0 (.storage vatRef) =
        .ok (.address (kissVatAddress σ I)) := by
    simpa [evm0, initState, kissVatAddress, vowAddressReturnWord, vowSlotWord] using
      evalExpr_kissVatStorage (evm := evm0) (locals := locals) (by simp [locals])
  have hguard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool true) := by
    exact evalExpr_kissVatCodeGuard_true hvat (by simpa [evm0] using hvatCode)
  have hargs :
      evalExprs? config { contract := contract, locals := locals } evm0 [thisAddr] =
        .ok [.address I.codeOwner] := by
    simpa [evm0, initState] using evalExprs_kissThis evm0 locals
  have hcallStmt :
      ExecStmt config { contract := contract, locals := locals } evm0
        (.externalCall (.storage vatRef) "sin" (.intLit 0) [thisAddr] "vatSin"
          (perm := false))
        .reverted := by
    exact ExecStmt.externalCallReturnDecodeRevert hvat (by simp [evalExpr?, pure])
      hargs hcallSin hdecSin
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 flopTransition.body
        .reverted := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
    exact ExecBlock.consRevert hcallStmt
  simpa [ExecTransitionBody, evm0, locals, flopTransition, nonpayable,
    checkedExternalCallStmts] using ExecFuncBody.execBlockRevert hblock

theorem vowFlopSourceFreeSinUnderflow
    {cA gh bl σ σ₀ A I} {g : UInt256} {evmSin : EVM.State}
    {outSin : ByteArray} {vatSin SinVal : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hvatCode :
      0 < (UInt256.ofNat
        (((initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (kissVatAddress σ I)).option 0 (fun acc => acc.code.size))).toNat)
    (hcallSin :
      typedCallViaEVM config (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (kissVatAddress σ I)) "sin" 0 [.address I.codeOwner]
        (true, evmSin, outSin) false)
    (hdecSin :
      config.externalABI.decode? "sin" outSin =
        some [.int (Int.ofNat vatSin.toNat)])
    (hSinLoad :
      Solm.EVM.storageLoad evmSin evmSin.executionEnv.codeOwner ⟨5⟩ = SinVal)
    (hlt : vatSin.toNat < SinVal.toNat) :
    let locals := (∅ : Store)
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals flopTransition.body .reverted := by
  intro locals evm0
  let locals1 := flopLocalsVatSin vatSin
  have hvat :
      evalExpr? config { contract := contract, locals := locals } evm0 (.storage vatRef) =
        .ok (.address (kissVatAddress σ I)) := by
    simpa [evm0, initState, kissVatAddress, vowAddressReturnWord, vowSlotWord] using
      evalExpr_kissVatStorage (evm := evm0) (locals := locals) (by simp [locals])
  have hguard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool true) := by
    exact evalExpr_kissVatCodeGuard_true hvat (by simpa [evm0] using hvatCode)
  have hargsSin :
      evalExprs? config { contract := contract, locals := locals } evm0 [thisAddr] =
        .ok [.address I.codeOwner] := by
    simpa [evm0, initState] using evalExprs_kissThis evm0 locals
  have hcallSinStmt :
      ExecStmt config { contract := contract, locals := locals } evm0
        (.externalCall (.storage vatRef) "sin" (.intLit 0) [thisAddr] "vatSin"
          (perm := false))
        (.ok { contract := contract, locals := locals1 } evmSin) := by
    simpa [locals, locals1, flopLocalsVatSin, collapseReturns] using
      ExecStmt.externalCallSuccess hvat (by simp [evalExpr?, pure]) hargsSin hcallSin hdecSin
  have hvatSinVar :
      evalExpr? config { contract := contract, locals := locals1 } evmSin (.var "vatSin") =
        .ok (.int (Int.ofNat vatSin.toNat)) := by
    simpa [locals1] using
      evalExpr_varUInt256 (evm := evmSin) (locals := flopLocalsVatSin vatSin)
        (name := "vatSin") (value := vatSin) (flopLocalsVatSin_get_vatSin vatSin)
  have hSin :
      evalExpr? config { contract := contract, locals := locals1 } evmSin (.storage SinRef) =
        .ok (.int (Int.ofNat SinVal.toNat)) := by
    simpa [locals1, hSinLoad] using
      evalExpr_healSinCapitalStorage (evm := evmSin) (locals := locals1)
        (by simp [locals1, flopLocalsVatSin])
  have hargsSub :
      evalExprs? config { contract := contract, locals := locals1 } evmSin
        [.var "vatSin", .storage SinRef] =
          .ok [.int (Int.ofNat vatSin.toNat), .int (Int.ofNat SinVal.toNat)] := by
    simp [evalExprs?, hvatSinVar, hSin, EvalResult.bind, bind, pure]
  have hbind :
      bindParams? subFunction.params
          [.int (Int.ofNat vatSin.toNat), .int (Int.ofNat SinVal.toNat)] =
        some (uintBinaryLocals vatSin SinVal) := by
    simp [subFunction, uint256, bindParams?, uintBinaryLocals]
  have hsubStmt :
      ExecStmt config { contract := contract, locals := locals1 } evmSin
        (.internalCall "sub" [.var "vatSin", .storage SinRef] "freeSin") .reverted := by
    have hbody := execSubFunctionRevert (evm := evmSin) (x := vatSin) (y := SinVal) hlt
    exact internalCallFunctionRevert
      (cfg := config) (caller := { contract := contract, locals := locals1 })
      (evm := evmSin) (name := "sub") (retVar := "freeSin")
      (args := [.var "vatSin", .storage SinRef])
      (argVals := [.int (Int.ofNat vatSin.toNat), .int (Int.ofNat SinVal.toNat)])
      (callee := subFunction) (locals := uintBinaryLocals vatSin SinVal)
      hargsSub (by rfl) hbind hbody
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 flopTransition.body
        .reverted := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
    refine ExecBlock.consNormal hcallSinStmt ?_
    exact ExecBlock.consRevert hsubStmt
  simpa [ExecTransitionBody, evm0, locals, flopTransition, nonpayable,
    checkedExternalCallStmts] using ExecFuncBody.execBlockRevert hblock

theorem vowFlopSourceDebtUnderflow
    {cA gh bl σ σ₀ A I} {g : UInt256} {evmSin : EVM.State}
    {outSin : ByteArray} {vatSin SinVal freeSin AshVal : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hvatCode :
      0 < (UInt256.ofNat
        (((initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (kissVatAddress σ I)).option 0 (fun acc => acc.code.size))).toNat)
    (hcallSin :
      typedCallViaEVM config (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (kissVatAddress σ I)) "sin" 0 [.address I.codeOwner]
        (true, evmSin, outSin) false)
    (hdecSin :
      config.externalABI.decode? "sin" outSin =
        some [.int (Int.ofNat vatSin.toNat)])
    (hSinLoad :
      Solm.EVM.storageLoad evmSin evmSin.executionEnv.codeOwner ⟨5⟩ = SinVal)
    (hfree : freeSin = UInt256.sub vatSin SinVal)
    (hfreeOk : SinVal.toNat ≤ vatSin.toNat)
    (hAshLoad :
      Solm.EVM.storageLoad evmSin evmSin.executionEnv.codeOwner ⟨6⟩ = AshVal)
    (hlt : freeSin.toNat < AshVal.toNat) :
    let locals := (∅ : Store)
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals flopTransition.body .reverted := by
  intro locals evm0
  let locals1 := flopLocalsVatSin vatSin
  let locals2 := flopLocalsVatSinFreeSin vatSin freeSin
  have hvat :
      evalExpr? config { contract := contract, locals := locals } evm0 (.storage vatRef) =
        .ok (.address (kissVatAddress σ I)) := by
    simpa [evm0, initState, kissVatAddress, vowAddressReturnWord, vowSlotWord] using
      evalExpr_kissVatStorage (evm := evm0) (locals := locals) (by simp [locals])
  have hguard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool true) := by
    exact evalExpr_kissVatCodeGuard_true hvat (by simpa [evm0] using hvatCode)
  have hargsSin :
      evalExprs? config { contract := contract, locals := locals } evm0 [thisAddr] =
        .ok [.address I.codeOwner] := by
    simpa [evm0, initState] using evalExprs_kissThis evm0 locals
  have hcallSinStmt :
      ExecStmt config { contract := contract, locals := locals } evm0
        (.externalCall (.storage vatRef) "sin" (.intLit 0) [thisAddr] "vatSin"
          (perm := false))
        (.ok { contract := contract, locals := locals1 } evmSin) := by
    simpa [locals, locals1, flopLocalsVatSin, collapseReturns] using
      ExecStmt.externalCallSuccess hvat (by simp [evalExpr?, pure]) hargsSin hcallSin hdecSin
  have hvatSinVar :
      evalExpr? config { contract := contract, locals := locals1 } evmSin (.var "vatSin") =
        .ok (.int (Int.ofNat vatSin.toNat)) := by
    simpa [locals1] using
      evalExpr_varUInt256 (evm := evmSin) (locals := flopLocalsVatSin vatSin)
        (name := "vatSin") (value := vatSin) (flopLocalsVatSin_get_vatSin vatSin)
  have hSin :
      evalExpr? config { contract := contract, locals := locals1 } evmSin (.storage SinRef) =
        .ok (.int (Int.ofNat SinVal.toNat)) := by
    simpa [locals1, hSinLoad] using
      evalExpr_healSinCapitalStorage (evm := evmSin) (locals := locals1)
        (by simp [locals1, flopLocalsVatSin])
  have hargsFree :
      evalExprs? config { contract := contract, locals := locals1 } evmSin
        [.var "vatSin", .storage SinRef] =
          .ok [.int (Int.ofNat vatSin.toNat), .int (Int.ofNat SinVal.toNat)] := by
    simp [evalExprs?, hvatSinVar, hSin, EvalResult.bind, bind, pure]
  have hbindFree :
      bindParams? subFunction.params
          [.int (Int.ofNat vatSin.toNat), .int (Int.ofNat SinVal.toNat)] =
        some (uintBinaryLocals vatSin SinVal) := by
    simp [subFunction, uint256, bindParams?, uintBinaryLocals]
  have hfreeStmt :
      ExecStmt config { contract := contract, locals := locals1 } evmSin
        (.internalCall "sub" [.var "vatSin", .storage SinRef] "freeSin")
        (.ok { contract := contract, locals := locals2 } evmSin) := by
    have hbody := execSubFunctionReturn (evm := evmSin) (x := vatSin) (y := SinVal)
      (diff := freeSin) hfree hfreeOk
    simpa [locals1, locals2, flopLocalsVatSinFreeSin, resumeAfterInternalCall] using
      (internalCallFunctionReturn
        (cfg := config) (caller := { contract := contract, locals := locals1 })
        (evm := evmSin) (calleeEvm := evmSin) (name := "sub") (retVar := "freeSin")
        (args := [.var "vatSin", .storage SinRef])
        (argVals := [.int (Int.ofNat vatSin.toNat), .int (Int.ofNat SinVal.toNat)])
        (callee := subFunction) (locals := uintBinaryLocals vatSin SinVal)
        (calleeSolm := { contract := contract, locals := uintBinaryLocalsZ vatSin SinVal freeSin })
        (value := some [.int (Int.ofNat freeSin.toNat)]) hargsFree (by rfl) hbindFree hbody)
  have hfreeVar :
      evalExpr? config { contract := contract, locals := locals2 } evmSin (.var "freeSin") =
        .ok (.int (Int.ofNat freeSin.toNat)) := by
    simpa [locals2] using
      evalExpr_varUInt256 (evm := evmSin)
        (locals := flopLocalsVatSinFreeSin vatSin freeSin)
        (name := "freeSin") (value := freeSin)
        (flopLocalsVatSinFreeSin_get_freeSin vatSin freeSin)
  have hAsh :
      evalExpr? config { contract := contract, locals := locals2 } evmSin (.storage AshRef) =
        .ok (.int (Int.ofNat AshVal.toNat)) := by
    simpa [locals2, hAshLoad] using
      evalExpr_kissAshStorage (evm := evmSin) (locals := locals2)
        (by simp [locals2, flopLocalsVatSinFreeSin, flopLocalsVatSin])
  have hargsDebt :
      evalExprs? config { contract := contract, locals := locals2 } evmSin
        [.var "freeSin", .storage AshRef] =
          .ok [.int (Int.ofNat freeSin.toNat), .int (Int.ofNat AshVal.toNat)] := by
    simp [evalExprs?, hfreeVar, hAsh, EvalResult.bind, bind, pure]
  have hbindDebt :
      bindParams? subFunction.params
          [.int (Int.ofNat freeSin.toNat), .int (Int.ofNat AshVal.toNat)] =
        some (uintBinaryLocals freeSin AshVal) := by
    simp [subFunction, uint256, bindParams?, uintBinaryLocals]
  have hdebtStmt :
      ExecStmt config { contract := contract, locals := locals2 } evmSin
        (.internalCall "sub" [.var "freeSin", .storage AshRef] "flopDebt") .reverted := by
    have hbody := execSubFunctionRevert (evm := evmSin) (x := freeSin) (y := AshVal) hlt
    exact internalCallFunctionRevert
      (cfg := config) (caller := { contract := contract, locals := locals2 })
      (evm := evmSin) (name := "sub") (retVar := "flopDebt")
      (args := [.var "freeSin", .storage AshRef])
      (argVals := [.int (Int.ofNat freeSin.toNat), .int (Int.ofNat AshVal.toNat)])
      (callee := subFunction) (locals := uintBinaryLocals freeSin AshVal)
      hargsDebt (by rfl) hbindDebt hbody
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 flopTransition.body
        .reverted := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
    refine ExecBlock.consNormal hcallSinStmt ?_
    refine ExecBlock.consNormal hfreeStmt ?_
    exact ExecBlock.consRevert hdebtStmt
  simpa [ExecTransitionBody, evm0, locals, flopTransition, nonpayable,
    checkedExternalCallStmts] using ExecFuncBody.execBlockRevert hblock

theorem vowFlopSourceInsufficientDebt
    {cA gh bl σ σ₀ A I} {g : UInt256} {evmSin : EVM.State}
    {outSin : ByteArray}
    {vatSin SinVal freeSin AshVal flopDebt SumpVal : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hvatCode :
      0 < (UInt256.ofNat
        (((initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (kissVatAddress σ I)).option 0 (fun acc => acc.code.size))).toNat)
    (hcallSin :
      typedCallViaEVM config (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (kissVatAddress σ I)) "sin" 0 [.address I.codeOwner]
        (true, evmSin, outSin) false)
    (hdecSin :
      config.externalABI.decode? "sin" outSin =
        some [.int (Int.ofNat vatSin.toNat)])
    (hSinLoad :
      Solm.EVM.storageLoad evmSin evmSin.executionEnv.codeOwner ⟨5⟩ = SinVal)
    (hfree : freeSin = UInt256.sub vatSin SinVal)
    (hfreeOk : SinVal.toNat ≤ vatSin.toNat)
    (hAshLoad :
      Solm.EVM.storageLoad evmSin evmSin.executionEnv.codeOwner ⟨6⟩ = AshVal)
    (hdebt : flopDebt = UInt256.sub freeSin AshVal)
    (hdebtOk : AshVal.toNat ≤ freeSin.toNat)
    (hSumpLoad :
      Solm.EVM.storageLoad evmSin evmSin.executionEnv.codeOwner ⟨9⟩ = SumpVal)
    (hinsuff : flopDebt.toNat < SumpVal.toNat) :
    let locals := (∅ : Store)
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals flopTransition.body .reverted := by
  intro locals evm0
  let locals1 := flopLocalsVatSin vatSin
  let locals2 := flopLocalsVatSinFreeSin vatSin freeSin
  let locals3 := flopLocalsVatSinFreeSinDebt vatSin freeSin flopDebt
  have hvat :
      evalExpr? config { contract := contract, locals := locals } evm0 (.storage vatRef) =
        .ok (.address (kissVatAddress σ I)) := by
    simpa [evm0, initState, kissVatAddress, vowAddressReturnWord, vowSlotWord] using
      evalExpr_kissVatStorage (evm := evm0) (locals := locals) (by simp [locals])
  have hguard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool true) := by
    exact evalExpr_kissVatCodeGuard_true hvat (by simpa [evm0] using hvatCode)
  have hargsSin :
      evalExprs? config { contract := contract, locals := locals } evm0 [thisAddr] =
        .ok [.address I.codeOwner] := by
    simpa [evm0, initState] using evalExprs_kissThis evm0 locals
  have hcallSinStmt :
      ExecStmt config { contract := contract, locals := locals } evm0
        (.externalCall (.storage vatRef) "sin" (.intLit 0) [thisAddr] "vatSin"
          (perm := false))
        (.ok { contract := contract, locals := locals1 } evmSin) := by
    simpa [locals, locals1, flopLocalsVatSin, collapseReturns] using
      ExecStmt.externalCallSuccess hvat (by simp [evalExpr?, pure]) hargsSin hcallSin hdecSin
  have hvatSinVar :
      evalExpr? config { contract := contract, locals := locals1 } evmSin (.var "vatSin") =
        .ok (.int (Int.ofNat vatSin.toNat)) := by
    simpa [locals1] using
      evalExpr_varUInt256 (evm := evmSin) (locals := flopLocalsVatSin vatSin)
        (name := "vatSin") (value := vatSin) (flopLocalsVatSin_get_vatSin vatSin)
  have hSin :
      evalExpr? config { contract := contract, locals := locals1 } evmSin (.storage SinRef) =
        .ok (.int (Int.ofNat SinVal.toNat)) := by
    simpa [locals1, hSinLoad] using
      evalExpr_healSinCapitalStorage (evm := evmSin) (locals := locals1)
        (by simp [locals1, flopLocalsVatSin])
  have hargsFree :
      evalExprs? config { contract := contract, locals := locals1 } evmSin
        [.var "vatSin", .storage SinRef] =
          .ok [.int (Int.ofNat vatSin.toNat), .int (Int.ofNat SinVal.toNat)] := by
    simp [evalExprs?, hvatSinVar, hSin, EvalResult.bind, bind, pure]
  have hbindFree :
      bindParams? subFunction.params
          [.int (Int.ofNat vatSin.toNat), .int (Int.ofNat SinVal.toNat)] =
        some (uintBinaryLocals vatSin SinVal) := by
    simp [subFunction, uint256, bindParams?, uintBinaryLocals]
  have hfreeStmt :
      ExecStmt config { contract := contract, locals := locals1 } evmSin
        (.internalCall "sub" [.var "vatSin", .storage SinRef] "freeSin")
        (.ok { contract := contract, locals := locals2 } evmSin) := by
    have hbody := execSubFunctionReturn (evm := evmSin) (x := vatSin) (y := SinVal)
      (diff := freeSin) hfree hfreeOk
    simpa [locals1, locals2, flopLocalsVatSinFreeSin, resumeAfterInternalCall] using
      (internalCallFunctionReturn
        (cfg := config) (caller := { contract := contract, locals := locals1 })
        (evm := evmSin) (calleeEvm := evmSin) (name := "sub") (retVar := "freeSin")
        (args := [.var "vatSin", .storage SinRef])
        (argVals := [.int (Int.ofNat vatSin.toNat), .int (Int.ofNat SinVal.toNat)])
        (callee := subFunction) (locals := uintBinaryLocals vatSin SinVal)
        (calleeSolm := { contract := contract, locals := uintBinaryLocalsZ vatSin SinVal freeSin })
        (value := some [.int (Int.ofNat freeSin.toNat)]) hargsFree (by rfl) hbindFree hbody)
  have hfreeVar :
      evalExpr? config { contract := contract, locals := locals2 } evmSin (.var "freeSin") =
        .ok (.int (Int.ofNat freeSin.toNat)) := by
    simpa [locals2] using
      evalExpr_varUInt256 (evm := evmSin)
        (locals := flopLocalsVatSinFreeSin vatSin freeSin)
        (name := "freeSin") (value := freeSin)
        (flopLocalsVatSinFreeSin_get_freeSin vatSin freeSin)
  have hAsh :
      evalExpr? config { contract := contract, locals := locals2 } evmSin (.storage AshRef) =
        .ok (.int (Int.ofNat AshVal.toNat)) := by
    simpa [locals2, hAshLoad] using
      evalExpr_kissAshStorage (evm := evmSin) (locals := locals2)
        (by simp [locals2, flopLocalsVatSinFreeSin, flopLocalsVatSin])
  have hargsDebt :
      evalExprs? config { contract := contract, locals := locals2 } evmSin
        [.var "freeSin", .storage AshRef] =
          .ok [.int (Int.ofNat freeSin.toNat), .int (Int.ofNat AshVal.toNat)] := by
    simp [evalExprs?, hfreeVar, hAsh, EvalResult.bind, bind, pure]
  have hbindDebt :
      bindParams? subFunction.params
          [.int (Int.ofNat freeSin.toNat), .int (Int.ofNat AshVal.toNat)] =
        some (uintBinaryLocals freeSin AshVal) := by
    simp [subFunction, uint256, bindParams?, uintBinaryLocals]
  have hdebtStmt :
      ExecStmt config { contract := contract, locals := locals2 } evmSin
        (.internalCall "sub" [.var "freeSin", .storage AshRef] "flopDebt")
        (.ok { contract := contract, locals := locals3 } evmSin) := by
    have hbody := execSubFunctionReturn (evm := evmSin) (x := freeSin) (y := AshVal)
      (diff := flopDebt) hdebt hdebtOk
    simpa [locals2, locals3, flopLocalsVatSinFreeSinDebt, resumeAfterInternalCall] using
      (internalCallFunctionReturn
        (cfg := config) (caller := { contract := contract, locals := locals2 })
        (evm := evmSin) (calleeEvm := evmSin) (name := "sub") (retVar := "flopDebt")
        (args := [.var "freeSin", .storage AshRef])
        (argVals := [.int (Int.ofNat freeSin.toNat), .int (Int.ofNat AshVal.toNat)])
        (callee := subFunction) (locals := uintBinaryLocals freeSin AshVal)
        (calleeSolm := { contract := contract, locals := uintBinaryLocalsZ freeSin AshVal flopDebt })
        (value := some [.int (Int.ofNat flopDebt.toNat)]) hargsDebt (by rfl) hbindDebt hbody)
  have hsump :
      evalExpr? config { contract := contract, locals := locals3 } evmSin (.storage sumpRef) =
        .ok (.int (Int.ofNat SumpVal.toNat)) := by
    simpa [locals3, hSumpLoad] using
      evalExpr_flopSumpStorage (evm := evmSin) (locals := locals3)
        (by simp [locals3, flopLocalsVatSinFreeSinDebt, flopLocalsVatSinFreeSin,
          flopLocalsVatSin])
  have hflopDebt :
      evalExpr? config { contract := contract, locals := locals3 } evmSin (.var "flopDebt") =
        .ok (.int (Int.ofNat flopDebt.toNat)) := by
    simpa [locals3] using
      evalExpr_varUInt256 (evm := evmSin)
        (locals := flopLocalsVatSinFreeSinDebt vatSin freeSin flopDebt)
        (name := "flopDebt") (value := flopDebt)
        (flopLocalsVatSinFreeSinDebt_get_flopDebt vatSin freeSin flopDebt)
  have hreqDebt :
      evalExpr? config { contract := contract, locals := locals3 } evmSin
        (.binary .le (.storage sumpRef) (.var "flopDebt")) = .ok (.bool false) :=
    evalExpr_le_uint256_false hsump hflopDebt hinsuff
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 flopTransition.body
        .reverted := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
    refine ExecBlock.consNormal hcallSinStmt ?_
    refine ExecBlock.consNormal hfreeStmt ?_
    refine ExecBlock.consNormal hdebtStmt ?_
    exact ExecBlock.consRevert (ExecStmt.requireFalse hreqDebt)
  simpa [ExecTransitionBody, evm0, locals, flopTransition, nonpayable,
    checkedExternalCallStmts] using ExecFuncBody.execBlockRevert hblock

theorem vowFlopVatSin0NoCodeBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g sel : UInt256}
    (hcode : I.code = vowBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some flopTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (flopTransition.params.map Param.name)
        (transitionSignature flopTransition).paramTypes I.calldata = some ∅)
    (hreach : ∃ k C, RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨646⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ_evm (kissDaiTargetWord σ_evm I) = ⟨0⟩) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hrev := RD.vowFlopVatSin0NoCode hreach hcodeSize
  have hVat : vowSlotWord ⟨1⟩ σ_evm I = vowSlotWord ⟨1⟩ σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨1⟩ ⟨0⟩
  have hTarget : kissDaiTargetWord σ_evm I = kissDaiTargetWord σ_solm I := by
    simp [kissDaiTargetWord, hVat]
  have hcodeSizeSolm :
      Reasoning.Theory.extCodeSizeWord σ_solm (kissDaiTargetWord σ_solm I) = ⟨0⟩ := by
    have hsame :=
      Reasoning.Theory.extCodeSizeWord_accountMapEquiv hAccounts
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
      extCodeSizeWord_zero_lookup_code_zero
        (σ := σ_solm) (target := kissDaiTargetWord σ_solm I)
        (addr := kissVatAddress σ_solm I) haddr hcodeSizeSolm
  have hbody := vowFlopSourceVatSin0NoCode (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g) hwv hvatNoCode
  exact hrev.reEquivExecutionRevert hcode hdispatch hdecode (by simpa using hbody)

theorem vowFlopSin0CallFailureBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g sel target : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {evmSin : EVM.State} {mem outSin rdata : ByteArray}
    {aw : UInt256} {k C : ℕ}
    (hcode : I.code = vowBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some flopTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (flopTransition.params.map Param.name)
        (transitionSignature flopTransition).paramTypes I.calldata = some ∅)
    (rd1277 : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1277⟩
      (⟨0⟩ :: healSinEndPtr :: healSinSelector :: target ::
        ⟨1325⟩ :: ⟨3675⟩ :: ⟨0⟩ :: ⟨357⟩ :: sel :: [])
      mem aw rdata acc k C)
    (hrdataSize : rdata.size < UInt256.size)
    (hvatCode :
      0 < (UInt256.ofNat
        (((initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (kissVatAddress σ_solm I)).option 0 (fun acc => acc.code.size))).toNat)
    (hcallSin :
      typedCallViaEVM config (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (kissVatAddress σ_solm I)) "sin" 0 [.address I.codeOwner]
        (false, evmSin, outSin) false) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hrev := RD.vowHealSinCallFailure rd1277 hrdataSize (by simp)
  have hbody := vowFlopSourceVatSin0CallFailure (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (evmSin := evmSin) (outSin := outSin) hwv hvatCode hcallSin
  exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem vowFlopSin0DecodeShortBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g sel target : UInt256}
    {cA' : Batteries.RBSet AccountAddress compare} {σ'_evm : AccountMap}
    {A'_evm : Substate} {outSin : ByteArray} {k C : ℕ}
    (hcode : I.code = vowBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some flopTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (flopTransition.params.map Param.name)
        (transitionSignature flopTransition).paramTypes I.calldata = some ∅)
    (rd1277 : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1277⟩
      (⟨1⟩ :: healSinEndPtr :: healSinSelector :: target ::
        ⟨1325⟩ :: ⟨3675⟩ :: ⟨0⟩ :: ⟨357⟩ :: sel :: [])
      (outSin.write 0 (healSinCalldataMem I solcFreePtrMem) 128
        (min (⟨32⟩ : UInt256) (UInt256.ofNat outSin.size)).toNat)
      (UInt256.ofNat 6) outSin (cA', σ'_evm) k C)
    (hcallSin :
      typedCallViaEVM config (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (kissVatAddress σ_solm I)) "sin" 0 [.address I.codeOwner]
        (true,
          { initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := σ'_evm
              substate := A'_evm
              createdAccounts := cA' },
          outSin) false)
    (hosz : outSin.size < UInt256.size)
    (hshort : outSin.size < 32)
    (hvatCode :
      0 < (UInt256.ofNat
        (((initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (kissVatAddress σ_solm I)).option 0 (fun acc => acc.code.size))).toNat) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hmin : (min (⟨32⟩ : UInt256) (UInt256.ofNat outSin.size)).toNat = outSin.size :=
    kissDaiMin32_toNat_of_lt hshort
  have rd1277' := rd1277
  rw [hmin] at rd1277'
  obtain ⟨_, _, rd1295⟩ :=
    RD.vowHealSinCallSuccessToDecode rd1277' (by simp)
  have hmem : (outSin.write 0 (healSinCalldataMem I solcFreePtrMem) 128 outSin.size).size =
      164 :=
    initialHealSinWrite_size I outSin outSin.size (by omega) (by omega)
  have hread64 :
      (outSin.write 0 (healSinCalldataMem I solcFreePtrMem) 128 outSin.size).readWithPadding
        64 32 = UInt256.toByteArray ⟨128⟩ :=
    initialHealSinWrite_read64 I outSin outSin.size (by omega) (by omega)
  have hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥
            (outSin.write 0 (healSinCalldataMem I solcFreePtrMem) 128 outSin.size).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          ((outSin.write 0 (healSinCalldataMem I solcFreePtrMem) 128 outSin.size).readWithPadding
            (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [hmem]; decide) (by decide) hread64
  have hrev := RD.vowFlopSin0ReturnDecodeShortReverts rd1295 hshort hosz hmload64
  have hdecSin : config.externalABI.decode? "sin" outSin = none :=
    vatSinDecode_none_short hshort
  have hbody := vowFlopSourceVatSin0DecodeRevert (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (evmSin :=
      { initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I with
          accountMap := σ'_evm
          substate := A'_evm
          createdAccounts := cA' })
    (outSin := outSin) hwv hvatCode hcallSin hdecSin
  exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem vowFlopFreeSinUnderflowBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g sel target vatSin SinVal : UInt256}
    {cA' : Batteries.RBSet AccountAddress compare} {σ'_evm : AccountMap}
    {evmSin : EVM.State} {outSin : ByteArray} {k C : ℕ}
    (hcode : I.code = vowBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some flopTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (flopTransition.params.map Param.name)
        (transitionSignature flopTransition).paramTypes I.calldata = some ∅)
    (rd1277 : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1277⟩
      (⟨1⟩ :: healSinEndPtr :: healSinSelector :: target ::
        ⟨1325⟩ :: ⟨3675⟩ :: ⟨0⟩ :: ⟨357⟩ :: sel :: [])
      (outSin.write 0 (healSinCalldataMem I solcFreePtrMem) 128
        (min (⟨32⟩ : UInt256) (UInt256.ofNat outSin.size)).toNat)
      (UInt256.ofNat 6) outSin (cA', σ'_evm) k C)
    (hcallSin :
      typedCallViaEVM config (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (kissVatAddress σ_solm I)) "sin" 0 [.address I.codeOwner]
        (true, evmSin, outSin) false)
    (hosz : outSin.size < UInt256.size)
    (ho32 : 32 ≤ outSin.size)
    (hvatCode :
      0 < (UInt256.ofNat
        (((initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (kissVatAddress σ_solm I)).option 0 (fun acc => acc.code.size))).toNat)
    (hSinLoad :
      Solm.EVM.storageLoad evmSin evmSin.executionEnv.codeOwner ⟨5⟩ = SinVal)
    (hSinEvm : vowSlotWord ⟨5⟩ σ'_evm I = SinVal)
    (hlt : vatSin.toNat < SinVal.toNat)
    (hvatSin :
      vatSin = UInt256.ofNat (fromByteArrayBigEndian (outSin.extract 0 32))) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hmin : (min (⟨32⟩ : UInt256) (UInt256.ofNat outSin.size)).toNat = 32 :=
    kissDaiMin32_toNat_of_ge ho32 hosz
  have rd1277' := rd1277
  rw [hmin] at rd1277'
  obtain ⟨_, _, rd1295⟩ :=
    RD.vowHealSinCallSuccessToDecode rd1277' (by simp)
  have hmem : (outSin.write 0 (healSinCalldataMem I solcFreePtrMem) 128 32).size =
      164 :=
    initialHealSinWrite_size I outSin 32 (by omega) ho32
  have hread64 :
      (outSin.write 0 (healSinCalldataMem I solcFreePtrMem) 128 32).readWithPadding
        64 32 = UInt256.toByteArray ⟨128⟩ :=
    initialHealSinWrite_read64 I outSin 32 (by omega) ho32
  have hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥
            (outSin.write 0 (healSinCalldataMem I solcFreePtrMem) 128 32).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          ((outSin.write 0 (healSinCalldataMem I solcFreePtrMem) 128 32).readWithPadding
            (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [hmem]; decide) (by decide) hread64
  have hmload128 :
      (if (⟨128⟩ : UInt256).toNat ≥
            (outSin.write 0 (healSinCalldataMem I solcFreePtrMem) 128 32).size
          ∨ (⟨128⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          ((outSin.write 0 (healSinCalldataMem I solcFreePtrMem) 128 32).readWithPadding
            (⟨128⟩ : UInt256).toNat 32))) =
        UInt256.ofNat (fromByteArrayBigEndian (outSin.extract 0 32)) := by
    have hnot :
        ¬ ((⟨128⟩ : UInt256).toNat ≥
              (outSin.write 0 (healSinCalldataMem I solcFreePtrMem) 128 32).size
            ∨ (⟨128⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩) := by
      rw [hmem]
      native_decide
    rw [if_neg hnot, show (⟨128⟩ : UInt256).toNat = 128 from by decide,
      initialHealSinWrite_read128_32 I outSin ho32]
  obtain ⟨_, _, rd1318⟩ :=
    RD.vowFlopSin0ReturnDecodeOk
      (retWord := UInt256.ofNat (fromByteArrayBigEndian (outSin.extract 0 32)))
      rd1295 ho32 hosz hmload64 hmload128
  have hrev := RD.vowFlopFreeSinSubUnderflow (vatSin := vatSin)
    (by simpa [hvatSin] using rd1318)
    (by simpa [hvatSin, hSinEvm] using hlt)
  have hdecSin :
      config.externalABI.decode? "sin" outSin = some [.int (Int.ofNat vatSin.toNat)] := by
    simpa [hvatSin] using vatSinDecode_ok (o := outSin) ho32
  have hbody := vowFlopSourceFreeSinUnderflow (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (evmSin := evmSin) (outSin := outSin) (vatSin := vatSin) (SinVal := SinVal)
    hwv hvatCode hcallSin hdecSin hSinLoad hlt
  exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem vowFlopDebtUnderflowBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g sel vatSin freeSin : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {evmSin : EVM.State} {mem outSin : ByteArray} {k C : ℕ}
    (hcode : I.code = vowBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some flopTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (flopTransition.params.map Param.name)
        (transitionSignature flopTransition).paramTypes I.calldata = some ∅)
    (rd1325 : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1325⟩
      (freeSin :: ⟨3675⟩ :: ⟨0⟩ :: ⟨357⟩ :: sel :: [])
      mem (UInt256.ofNat 6) outSin acc k C)
    (hunder : freeSin.toNat < (vowSlotWord ⟨6⟩ acc.2 I).toNat)
    (hvatCode :
      0 < (UInt256.ofNat
        (((initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (kissVatAddress σ_solm I)).option 0 (fun acc => acc.code.size))).toNat)
    (hcallSin :
      typedCallViaEVM config (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (kissVatAddress σ_solm I)) "sin" 0 [.address I.codeOwner]
        (true, evmSin, outSin) false)
    (hdecSin :
      config.externalABI.decode? "sin" outSin =
        some [.int (Int.ofNat vatSin.toNat)])
    (hSinLoad :
      Solm.EVM.storageLoad evmSin evmSin.executionEnv.codeOwner ⟨5⟩ =
        vowSlotWord ⟨5⟩ acc.2 I)
    (hfree : freeSin = UInt256.sub vatSin (vowSlotWord ⟨5⟩ acc.2 I))
    (hfreeOk : (vowSlotWord ⟨5⟩ acc.2 I).toNat ≤ vatSin.toNat)
    (hAshLoad :
      Solm.EVM.storageLoad evmSin evmSin.executionEnv.codeOwner ⟨6⟩ =
        vowSlotWord ⟨6⟩ acc.2 I) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hrev := RD.vowFlopDebtSubUnderflow rd1325 hunder
  have hbody := vowFlopSourceDebtUnderflow (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (evmSin := evmSin) (outSin := outSin) (vatSin := vatSin)
    (SinVal := vowSlotWord ⟨5⟩ acc.2 I) (freeSin := freeSin)
    (AshVal := vowSlotWord ⟨6⟩ acc.2 I)
    hwv hvatCode hcallSin hdecSin hSinLoad hfree hfreeOk hAshLoad hunder
  exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem vowFlopInsufficientDebtBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g sel vatSin freeSin flopDebt : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {evmSin : EVM.State} {mem outSin : ByteArray} {k C : ℕ}
    (hcode : I.code = vowBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some flopTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (flopTransition.params.map Param.name)
        (transitionSignature flopTransition).paramTypes I.calldata = some ∅)
    (rd3675 : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨3675⟩
      (flopDebt :: ⟨0⟩ :: ⟨357⟩ :: sel :: [])
      mem (UInt256.ofNat 6) outSin acc k C)
    (hinsuff : flopDebt.toNat < (vowSlotWord ⟨9⟩ acc.2 I).toNat)
    (hmem : mem.size = 164)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hvatCode :
      0 < (UInt256.ofNat
        (((initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (kissVatAddress σ_solm I)).option 0 (fun acc => acc.code.size))).toNat)
    (hcallSin :
      typedCallViaEVM config (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (kissVatAddress σ_solm I)) "sin" 0 [.address I.codeOwner]
        (true, evmSin, outSin) false)
    (hdecSin :
      config.externalABI.decode? "sin" outSin =
        some [.int (Int.ofNat vatSin.toNat)])
    (hSinLoad :
      Solm.EVM.storageLoad evmSin evmSin.executionEnv.codeOwner ⟨5⟩ =
        vowSlotWord ⟨5⟩ acc.2 I)
    (hfree : freeSin = UInt256.sub vatSin (vowSlotWord ⟨5⟩ acc.2 I))
    (hfreeOk : (vowSlotWord ⟨5⟩ acc.2 I).toNat ≤ vatSin.toNat)
    (hAshLoad :
      Solm.EVM.storageLoad evmSin evmSin.executionEnv.codeOwner ⟨6⟩ =
        vowSlotWord ⟨6⟩ acc.2 I)
    (hdebt : flopDebt = UInt256.sub freeSin (vowSlotWord ⟨6⟩ acc.2 I))
    (hdebtOk : (vowSlotWord ⟨6⟩ acc.2 I).toNat ≤ freeSin.toNat)
    (hSumpLoad :
      Solm.EVM.storageLoad evmSin evmSin.executionEnv.codeOwner ⟨9⟩ =
        vowSlotWord ⟨9⟩ acc.2 I) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hrev := RD.vowFlopInsufficientDebt rd3675 hinsuff hmem hread64
  have hbody := vowFlopSourceInsufficientDebt (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (evmSin := evmSin) (outSin := outSin) (vatSin := vatSin)
    (SinVal := vowSlotWord ⟨5⟩ acc.2 I) (freeSin := freeSin)
    (AshVal := vowSlotWord ⟨6⟩ acc.2 I) (flopDebt := flopDebt)
    (SumpVal := vowSlotWord ⟨9⟩ acc.2 I)
    hwv hvatCode hcallSin hdecSin hSinLoad hfree hfreeOk hAshLoad hdebt hdebtOk
    hSumpLoad hinsuff
  exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody

end Benchmarks.Dss.Vow
