import Benchmarks.Dss.Clipper.Common
import Benchmarks.Dss.Clipper.Fallback

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement
open Benchmarks.Dss.Clipper.Immutables

namespace Benchmarks.Dss.Clipper

set_option linter.unusedTactic false

theorem clipperListSelectorWord {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size)
    (hsel : selIs I (clipperSelBytes 15)) :
    clipperSelWord I = clipperSelNat 15 := by
  simpa [clipperSelWord, solcSelectorWord, clipperSelNat] using
    solcSelectorWord_eq_of_beq I hsz 0x0f 0x56 0x0c 0xd7 (clipperSelNat 15)
      (by native_decide) (by simpa [clipperSelBytes, selIs] using hsel)

theorem clipperDispatch_list (v : ClipperImmutables) {I : ExecutionEnv}
    (hsel : selIs I (clipperSelBytes 15)) :
    dispatchMsg (contract v) I.calldata = some listTransition := by
  refine dispatchMsg_eq_some_of_split (contract := contract v)
    (pre :=
      [activeTransition, bufTransition, calcTransition, chipTransition, chostTransition,
        countTransition, cuspTransition, denyTransition, dogTransition, fileUintTransition,
        fileAddressTransition, getStatusTransition, ilkTransition v, kickTransition v,
        kicksTransition])
    (post :=
      [redoTransition v, relyTransition, salesTransition, spotterTransition, stoppedTransition,
        tailTransition, takeTransition v, tipTransition, upchostTransition v, vatTransition v,
        vowTransition, wardsTransition, yankTransition v])
    (ti := listTransition) (cd := I.calldata) (by rfl) ?_ ?_ ?_ (by rfl)
  · rfl
  · intro t ht
    simp only [List.mem_cons, List.mem_nil_iff] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      | rfl | rfl | rfl | rfl | hfalse
    · rw [selectorOf, activeSelectorBytes, ← byteArray_eq_of_beq hsel]
      native_decide
    · rw [selectorOf, bufSelectorBytes, ← byteArray_eq_of_beq hsel]
      native_decide
    · rw [selectorOf, calcSelectorBytes, ← byteArray_eq_of_beq hsel]
      native_decide
    · rw [selectorOf, chipSelectorBytes, ← byteArray_eq_of_beq hsel]
      native_decide
    · rw [selectorOf, chostSelectorBytes, ← byteArray_eq_of_beq hsel]
      native_decide
    · rw [selectorOf, countSelectorBytes, ← byteArray_eq_of_beq hsel]
      native_decide
    · rw [selectorOf, cuspSelectorBytes, ← byteArray_eq_of_beq hsel]
      native_decide
    · rw [selectorOf, denySelectorBytes, ← byteArray_eq_of_beq hsel]
      native_decide
    · rw [selectorOf, dogSelectorBytes, ← byteArray_eq_of_beq hsel]
      native_decide
    · rw [selectorOf, fileUintSelectorBytes, ← byteArray_eq_of_beq hsel]
      native_decide
    · rw [selectorOf, fileAddressSelectorBytes, ← byteArray_eq_of_beq hsel]
      native_decide
    · rw [selectorOf, getStatusSelectorBytes, ← byteArray_eq_of_beq hsel]
      native_decide
    · rw [selectorOf, ilkSelectorBytes v, ← byteArray_eq_of_beq hsel]
      native_decide
    · rw [selectorOf, kickSelectorBytes v, ← byteArray_eq_of_beq hsel]
      native_decide
    · rw [selectorOf, kicksSelectorBytes, ← byteArray_eq_of_beq hsel]
      native_decide
    · cases hfalse
  · rw [selectorOf, listSelectorBytes]
    simpa [clipperSelBytes] using hsel

theorem clipperDecode_list (v : ClipperImmutables) {I : ExecutionEnv}
    (hsz : 4 ≤ I.calldata.size) :
    decodeCalldataWithMode (config v).abiDecodeMode (listTransition.params.map Param.name)
      (transitionSignature listTransition).paramTypes I.calldata = some ∅ := by
  show decodeCalldataWithMode (config v).abiDecodeMode [] [] I.calldata = some ∅
  exact decodeCalldataWithMode_empty_ok hsz

theorem clipperEvalActiveArray (v : ClipperImmutables) (evm : EVM.State) (locals : Store)
    (hbase : locals.get? "active" = none) :
    evalExpr? (config v) { contract := contract v, locals := locals } evm (.storage activeRef) =
      readStorage? (config v) evm ({ base := "active", steps := [] } : EvaledStorageRef)
        (.dynamicArray uint256St) := by
  let er : EvaledStorageRef := { base := "active", steps := [] }
  have her : evalStorageRef (config v)
      { contract := contract v, locals := locals } evm activeRef = .ok er := by
    unfold evalStorageRef activeRef
    simp only [evalStorageRefSteps]
    rfl
  have hty : storageTypeAt? (contract v).storage er = some (.dynamicArray uint256St) := by
    simp [er, storageTypeAt?, contract, storageDecls]
  have hres :
      resolveStorageRef? (config v)
        { contract := contract v, locals := locals } evm activeRef =
        .ok (er, .dynamicArray uint256St) :=
    resolveStorageRef?_ok hbase her hty
  rw [evalExpr?]
  simp only [hres, bind, EvalResult.bind]
  rfl

def clipperActiveArrayValuesFrom (evm : EVM.State) : Nat → Nat → List Value
  | _, 0 => []
  | k, n + 1 =>
      .int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (activeSlot (.int (Int.ofNat k)))).toNat) ::
      clipperActiveArrayValuesFrom evm (k + 1) n

abbrev clipperActiveArrayValues (evm : EVM.State) : List Value :=
  clipperActiveArrayValuesFrom evm 0
    (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨11⟩).toNat

def clipperActiveArrayWordBytesFrom (evm : EVM.State) : Nat → Nat → List UInt8
  | _, 0 => []
  | k, n + 1 =>
      EVM.Word.toBytesBE (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (activeSlot (.int (Int.ofNat k)))) ++
      clipperActiveArrayWordBytesFrom evm (k + 1) n

abbrev clipperActiveArrayReturnBytes (evm : EVM.State) : ByteArray :=
  ⟨(ABI.natBytes 32 ++
    (ABI.natBytes (clipperActiveArrayValues evm).length ++
      clipperActiveArrayWordBytesFrom evm 0
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨11⟩).toNat)).toArray⟩

theorem clipperActiveArrayValuesFrom_length (evm : EVM.State) :
    ∀ k n, (clipperActiveArrayValuesFrom evm k n).length = n
  | _, 0 => rfl
  | k, n + 1 => by
      simp [clipperActiveArrayValuesFrom, clipperActiveArrayValuesFrom_length evm (k + 1) n]

theorem clipperEncodeActiveArrayElemsFrom (evm : EVM.State) :
    ∀ k n,
      encodeABIStaticArrayElems? uint256 (clipperActiveArrayValuesFrom evm k n) =
        some (clipperActiveArrayWordBytesFrom evm k n)
  | _, 0 => by
      simp [clipperActiveArrayValuesFrom, clipperActiveArrayWordBytesFrom,
        encodeABIStaticArrayElems?]
  | k, n + 1 => by
      simp only [clipperActiveArrayValuesFrom, clipperActiveArrayWordBytesFrom,
        encodeABIStaticArrayElems?, bind, Option.bind]
      rw [clipperEncodeABIValue_uint256,
        clipperEncodeActiveArrayElemsFrom evm (k + 1) n]

theorem clipperActiveArrayReturnEncoding (evm : EVM.State) :
    encodeReturnValue? uint256Array (.array (clipperActiveArrayValues evm)) =
      some (clipperActiveArrayReturnBytes evm) := by
  have hstatic : isDynamicABIType uint256 = false := by rfl
  rw [show encodeReturnValue? uint256Array (.array (clipperActiveArrayValues evm)) =
      encodeReturnValues? [uint256Array] [(.array (clipperActiveArrayValues evm))] from rfl]
  unfold encodeReturnValues?
  rw [show encodeABIValues? [uint256Array] [(.array (clipperActiveArrayValues evm))] =
      (encodeABIStaticArrayElems? uint256 (clipperActiveArrayValues evm)).bind
        (fun e => some (ABI.natBytes 32 ++
          (ABI.natBytes (clipperActiveArrayValues evm).length ++ e))) from by
        simpa [uint256Array] using
          (encodeABIValues_single_dynArray_static
            (elemTy := uint256) (vs := clipperActiveArrayValues evm) hstatic)]
  unfold clipperActiveArrayValues
  rw [clipperEncodeActiveArrayElemsFrom]
  rfl

theorem clipperListReturnEquiv (evm : EVM.State) :
    returnEquiv (clipperActiveArrayReturnBytes evm)
      (some [(.array (clipperActiveArrayValues evm))]) listTransition.returnType := by
  rw [show listTransition.returnType = [uint256Array] from rfl]
  exact returnEquiv_of_encode (clipperActiveArrayReturnEncoding evm)

theorem clipperActiveArrayValuesFrom_accountMapEquiv
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : Sat256}
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    ∀ k n,
      clipperActiveArrayValuesFrom (initState cA gh bl σ_evm σ₀ g A I) k n =
        clipperActiveArrayValuesFrom (initState cA gh bl σ_solm σ₀ g A I) k n
  | _, 0 => rfl
  | k, n + 1 => by
      have hslot :
          Solm.EVM.storageLoad (initState cA gh bl σ_evm σ₀ g A I)
              (initState cA gh bl σ_evm σ₀ g A I).executionEnv.codeOwner
              (activeSlot (.int (Int.ofNat k))) =
            Solm.EVM.storageLoad (initState cA gh bl σ_solm σ₀ g A I)
              (initState cA gh bl σ_solm σ₀ g A I).executionEnv.codeOwner
              (activeSlot (.int (Int.ofNat k))) := by
        simpa [initState, Solm.EVM.storageLoad, State.lookupAccount] using
          accountMapEquiv_storage_findD hAccounts I.codeOwner
            (activeSlot (.int (Int.ofNat k))) ⟨0⟩
      simp only [clipperActiveArrayValuesFrom, List.cons.injEq]
      constructor
      · rw [hslot]
      · exact clipperActiveArrayValuesFrom_accountMapEquiv hAccounts (k + 1) n

theorem clipperActiveArrayValues_accountMapEquiv
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : Sat256}
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    clipperActiveArrayValues (initState cA gh bl σ_evm σ₀ g A I) =
      clipperActiveArrayValues (initState cA gh bl σ_solm σ₀ g A I) := by
  have hlen :
      Solm.EVM.storageLoad (initState cA gh bl σ_evm σ₀ g A I)
          (initState cA gh bl σ_evm σ₀ g A I).executionEnv.codeOwner ⟨11⟩ =
        Solm.EVM.storageLoad (initState cA gh bl σ_solm σ₀ g A I)
          (initState cA gh bl σ_solm σ₀ g A I).executionEnv.codeOwner ⟨11⟩ := by
    simpa [initState, Solm.EVM.storageLoad, State.lookupAccount] using
      accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨11⟩ ⟨0⟩
  unfold clipperActiveArrayValues
  rw [hlen]
  exact clipperActiveArrayValuesFrom_accountMapEquiv hAccounts 0
    (Solm.EVM.storageLoad (initState cA gh bl σ_solm σ₀ g A I)
      (initState cA gh bl σ_solm σ₀ g A I).executionEnv.codeOwner ⟨11⟩).toNat

theorem clipperActiveArrayWordBytesFrom_accountMapEquiv
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : Sat256}
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    ∀ k n,
      clipperActiveArrayWordBytesFrom (initState cA gh bl σ_evm σ₀ g A I) k n =
        clipperActiveArrayWordBytesFrom (initState cA gh bl σ_solm σ₀ g A I) k n
  | _, 0 => rfl
  | k, n + 1 => by
      have hslot :
          Solm.EVM.storageLoad (initState cA gh bl σ_evm σ₀ g A I)
              (initState cA gh bl σ_evm σ₀ g A I).executionEnv.codeOwner
              (activeSlot (.int (Int.ofNat k))) =
            Solm.EVM.storageLoad (initState cA gh bl σ_solm σ₀ g A I)
              (initState cA gh bl σ_solm σ₀ g A I).executionEnv.codeOwner
              (activeSlot (.int (Int.ofNat k))) := by
        simpa [initState, Solm.EVM.storageLoad, State.lookupAccount] using
          accountMapEquiv_storage_findD hAccounts I.codeOwner
            (activeSlot (.int (Int.ofNat k))) ⟨0⟩
      simp only [clipperActiveArrayWordBytesFrom]
      rw [hslot, clipperActiveArrayWordBytesFrom_accountMapEquiv hAccounts (k + 1) n]

theorem clipperActiveArrayReturnBytes_accountMapEquiv
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : Sat256}
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    clipperActiveArrayReturnBytes (initState cA gh bl σ_evm σ₀ g A I) =
      clipperActiveArrayReturnBytes (initState cA gh bl σ_solm σ₀ g A I) := by
  have hlen :
      Solm.EVM.storageLoad (initState cA gh bl σ_evm σ₀ g A I)
          (initState cA gh bl σ_evm σ₀ g A I).executionEnv.codeOwner ⟨11⟩ =
        Solm.EVM.storageLoad (initState cA gh bl σ_solm σ₀ g A I)
          (initState cA gh bl σ_solm σ₀ g A I).executionEnv.codeOwner ⟨11⟩ := by
    simpa [initState, Solm.EVM.storageLoad, State.lookupAccount] using
      accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨11⟩ ⟨0⟩
  unfold clipperActiveArrayReturnBytes clipperActiveArrayValues
  rw [hlen]
  simp [clipperActiveArrayValuesFrom_accountMapEquiv hAccounts,
    clipperActiveArrayWordBytesFrom_accountMapEquiv hAccounts]

theorem clipperListReturnEquiv_accountMapEquiv
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : Sat256}
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    returnEquiv (clipperActiveArrayReturnBytes (initState cA gh bl σ_evm σ₀ g A I))
      (some [(.array (clipperActiveArrayValues (initState cA gh bl σ_solm σ₀ g A I)))])
      listTransition.returnType := by
  rw [clipperActiveArrayReturnBytes_accountMapEquiv hAccounts]
  exact clipperListReturnEquiv (initState cA gh bl σ_solm σ₀ g A I)

theorem clipperReadActiveElemAt (v : ClipperImmutables) (evm : EVM.State) (k : Nat) :
    readStorage? (config v) evm
      ({ base := "active", steps := [.aindex (.int (Int.ofNat k))] } : EvaledStorageRef)
      uint256St =
      .ok (.int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (activeSlot (.int (Int.ofNat k)))).toNat)) := by
  simp [readStorage?, config, storageLayout, solidityStorageLayout, storageLayoutRaw,
    clipperStorageLocLoad_uint256, uint256St]

theorem clipperReadActiveArrayElemsFrom (v : ClipperImmutables) (evm : EVM.State) :
    ∀ k n,
      readArrayElems? (config v) evm ({ base := "active", steps := [] } : EvaledStorageRef)
        uint256St k n = .ok (clipperActiveArrayValuesFrom evm k n)
  | _k, 0 => by
      rw [readArrayElems?]
      rfl
  | k, n + 1 => by
      rw [readArrayElems?]
      simp only [List.nil_append]
      change (do
          let elem ← readStorage? (config v) evm
            ({ base := "active",
               steps := [EvaledStorageRefStep.aindex (KeyValue.int (Int.ofNat k))] } :
              EvaledStorageRef)
            uint256St
          let vrest ← readArrayElems? (config v) evm
            ({ base := "active", steps := [] } : EvaledStorageRef) uint256St (k + 1) n
          pure (elem :: vrest)) = .ok (clipperActiveArrayValuesFrom evm k (n + 1))
      rw [clipperReadActiveElemAt v evm k]
      simp only [bind, EvalResult.bind, pure]
      rw [clipperReadActiveArrayElemsFrom v evm (k + 1) n]
      rfl

theorem clipperReadActiveArray (v : ClipperImmutables) (evm : EVM.State) :
    readStorage? (config v) evm ({ base := "active", steps := [] } : EvaledStorageRef)
      (.dynamicArray uint256St) = .ok (.array (clipperActiveArrayValues evm)) := by
  rw [readStorage?]
  change (match (config v).storage.layout
      ({ base := "active", steps := [.length] } : EvaledStorageRef) evm with
    | some lenLoc =>
        match storageLocLoad evm lenLoc with
        | Value.int len => do
            let vs <- readArrayElems? (config v) evm
              ({ base := "active", steps := [] } : EvaledStorageRef) uint256St 0 len.toNat
            pure (Value.array vs)
        | _ => EvalResult.error .storageError
    | none => EvalResult.error .storageError) =
      .ok (Value.array (clipperActiveArrayValues evm))
  rw [show (config v).storage.layout
      ({ base := "active", steps := [.length] } : EvaledStorageRef) evm =
        some (wordLoc ⟨11⟩) from rfl]
  simp only [clipperStorageLocLoad_uint256, bind, EvalResult.bind]
  change (do
      let vs ← readArrayElems? (config v) evm
        ({ base := "active", steps := [] } : EvaledStorageRef) uint256St 0
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨11⟩).toNat
      pure (Value.array vs)) = .ok (Value.array (clipperActiveArrayValues evm))
  rw [clipperReadActiveArrayElemsFrom v evm 0
    (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨11⟩).toNat]
  rfl

theorem clipperListBodyReturns (v : ClipperImmutables) (evm : EVM.State) (locals : Store)
    (h : evm.executionEnv.weiValue = ⟨0⟩) (hbase : locals.get? "active" = none)
    {value : Value}
    (hread :
      readStorage? (config v) evm ({ base := "active", steps := [] } : EvaledStorageRef)
        (.dynamicArray uint256St) = .ok value) :
    ExecTransitionBody (config v) (contract v) evm locals listTransition.body
      (.returned { contract := contract v, locals := locals } evm (some [value])) := by
  simpa [listTransition] using
    nonpayableReturnExprBodyReturns (cfg := config v) (contract := contract v) h
      ((clipperEvalActiveArray v evm locals hbase).trans hread)

theorem clipperListBodyReturnsActive (v : ClipperImmutables) (evm : EVM.State) (locals : Store)
    (h : evm.executionEnv.weiValue = ⟨0⟩) (hbase : locals.get? "active" = none) :
    ExecTransitionBody (config v) (contract v) evm locals listTransition.body
      (.returned { contract := contract v, locals := locals } evm
        (some [(.array (clipperActiveArrayValues evm))])) := by
  exact clipperListBodyReturns v evm locals h hbase (clipperReadActiveArray v evm)

set_option maxHeartbeats 1000000 in
theorem clipperReachListBody {cA gh bl σ σ₀ A I} {g : Sat256} (v : ClipperImmutables)
    {code : ByteArray} (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    (hcode : I.code = code) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (clipperSelBytes 15)) :
    ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I) (⟨504⟩ : UInt256)
      [clipperSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, h32⟩ := clipperReachRoot (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) v hpatch hcode hwv hsz hsize
  have hword := clipperListSelectorWord hsz hsel
  have h260 := clipperSplitTaken (pc := (⟨32⟩ : UInt256)) (pivot := clipperSelNat 20)
    (tgt := (⟨260⟩ : UInt256)) h32
    (by
        change decode code (⟨32⟩ : UInt256) = some (.DUP1, .none)
        clipper_decode)
    (by
        change decode code (selArmPush4Pc (⟨32⟩ : UInt256)) =
          some (.Push .PUSH4, some (clipperSelNat 20, 4))
        clipper_decode)
    (by
        change decode code (selArmEqPc (⟨32⟩ : UInt256)) = some (.GT, .none)
        clipper_decode)
    (by decide)
    (by
        change decode code (selArmPushTgtPc (⟨32⟩ : UInt256)) =
          some (.Push .PUSH2, some (⟨260⟩, 2))
        clipper_decode)
    (by
        change decode code (selArmJumpiPc (⟨32⟩ : UInt256) 2) = some (.JUMPI, .none)
        clipper_decode)
    (by rw [hword]; native_decide)
    (clipperJumpDestBeforeFirstPatch v hpatch (⟨260⟩ : UInt256) (by native_decide))
    (by simp)
  have h369 := clipperSplitTaken (pc := (⟨261⟩ : UInt256)) (pivot := clipperSelNat 9)
    (tgt := (⟨369⟩ : UInt256))
    (h260.jumpdest
      (by
          change decode code (⟨260⟩ : UInt256) = some (.JUMPDEST, .none)
          clipper_decode)
      (by simp))
    (by
        change decode code (⟨261⟩ : UInt256) = some (.DUP1, .none)
        clipper_decode)
    (by
        change decode code (selArmPush4Pc (⟨261⟩ : UInt256)) =
          some (.Push .PUSH4, some (clipperSelNat 9, 4))
        clipper_decode)
    (by
        change decode code (selArmEqPc (⟨261⟩ : UInt256)) = some (.GT, .none)
        clipper_decode)
    (by decide)
    (by
        change decode code (selArmPushTgtPc (⟨261⟩ : UInt256)) =
          some (.Push .PUSH2, some (⟨369⟩, 2))
        clipper_decode)
    (by
        change decode code (selArmJumpiPc (⟨261⟩ : UInt256) 2) = some (.JUMPI, .none)
        clipper_decode)
    (by rw [hword]; native_decide)
    (clipperJumpDestBeforeFirstPatch v hpatch (⟨369⟩ : UInt256) (by native_decide))
    (by simp)
  have h429 := clipperSplitTaken (pc := (⟨370⟩ : UInt256)) (pivot := clipperSelNat 21)
    (tgt := (⟨429⟩ : UInt256))
    (h369.jumpdest
      (by
          change decode code (⟨369⟩ : UInt256) = some (.JUMPDEST, .none)
          clipper_decode)
      (by simp))
    (by
        change decode code (⟨370⟩ : UInt256) = some (.DUP1, .none)
        clipper_decode)
    (by
        change decode code (selArmPush4Pc (⟨370⟩ : UInt256)) =
          some (.Push .PUSH4, some (clipperSelNat 21, 4))
        clipper_decode)
    (by
        change decode code (selArmEqPc (⟨370⟩ : UInt256)) = some (.GT, .none)
        clipper_decode)
    (by decide)
    (by
        change decode code (selArmPushTgtPc (⟨370⟩ : UInt256)) =
          some (.Push .PUSH2, some (⟨429⟩, 2))
        clipper_decode)
    (by
        change decode code (selArmJumpiPc (⟨370⟩ : UInt256) 2) = some (.JUMPI, .none)
        clipper_decode)
    (by rw [hword]; native_decide)
    (clipperJumpDestBeforeFirstPatch v hpatch (⟨429⟩ : UInt256) (by native_decide))
    (by simp)
  have h441 := clipperArmNotTaken (pc := (⟨430⟩ : UInt256))
    (next := (⟨441⟩ : UInt256)) (sel := clipperSelNat 5)
    (tgt := (⟨468⟩ : UInt256))
    (h429.jumpdest
      (by
          change decode code (⟨429⟩ : UInt256) = some (.JUMPDEST, .none)
          clipper_decode)
      (by simp))
    (by
        change decode code (⟨430⟩ : UInt256) = some (.DUP1, .none)
        clipper_decode)
    (by
        change decode code (selArmPush4Pc (⟨430⟩ : UInt256)) =
          some (.Push .PUSH4, some (clipperSelNat 5, 4))
        clipper_decode)
    (by
        change decode code (selArmEqPc (⟨430⟩ : UInt256)) = some (.EQ, .none)
        clipper_decode)
    (by decide)
    (by
        change decode code (selArmPushTgtPc (⟨430⟩ : UInt256)) =
          some (.Push .PUSH2, some (⟨468⟩, 2))
        clipper_decode)
    (by
        change decode code (selArmJumpiPc (⟨430⟩ : UInt256) 2) = some (.JUMPI, .none)
        clipper_decode)
    (by rw [hword]; native_decide)
    (by native_decide)
    (by simp)
  have h452 := clipperArmNotTaken (pc := (⟨441⟩ : UInt256))
    (next := (⟨452⟩ : UInt256)) (sel := clipperSelNat 24)
    (tgt := (⟨494⟩ : UInt256)) h441
    (by
        change decode code (⟨441⟩ : UInt256) = some (.DUP1, .none)
        clipper_decode)
    (by
        change decode code (selArmPush4Pc (⟨441⟩ : UInt256)) =
          some (.Push .PUSH4, some (clipperSelNat 24, 4))
        clipper_decode)
    (by
        change decode code (selArmEqPc (⟨441⟩ : UInt256)) = some (.EQ, .none)
        clipper_decode)
    (by decide)
    (by
        change decode code (selArmPushTgtPc (⟨441⟩ : UInt256)) =
          some (.Push .PUSH2, some (⟨494⟩, 2))
        clipper_decode)
    (by
        change decode code (selArmJumpiPc (⟨441⟩ : UInt256) 2) = some (.JUMPI, .none)
        clipper_decode)
    (by rw [hword]; native_decide)
    (by native_decide)
    (by simp)
  have h504 := clipperArmTaken (pc := (⟨452⟩ : UInt256)) (sel := clipperSelNat 15)
    (tgt := (⟨504⟩ : UInt256)) h452
    (by
        change decode code (⟨452⟩ : UInt256) = some (.DUP1, .none)
        clipper_decode)
    (by
        change decode code (selArmPush4Pc (⟨452⟩ : UInt256)) =
          some (.Push .PUSH4, some (clipperSelNat 15, 4))
        clipper_decode)
    (by
        change decode code (selArmEqPc (⟨452⟩ : UInt256)) = some (.EQ, .none)
        clipper_decode)
    (by decide)
    (by
        change decode code (selArmPushTgtPc (⟨452⟩ : UInt256)) =
          some (.Push .PUSH2, some (⟨504⟩, 2))
        clipper_decode)
    (by
        change decode code (selArmJumpiPc (⟨452⟩ : UInt256) 2) = some (.JUMPI, .none)
        clipper_decode)
    (by rw [hword]; native_decide)
    (clipperJumpDestBeforeFirstPatch v hpatch (⟨504⟩ : UInt256) (by native_decide))
    (by simp)
  exact ⟨_, _, h504⟩

theorem clipperListEntryWf (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    solcGetterEntryWf code (⟨504⟩ : UInt256) (⟨512⟩ : UInt256)
      (⟨1812⟩ : UInt256) := by
  unfold solcGetterEntryWf
  repeat' first | apply And.intro
  all_goals
    rw [clipperDecodeBeforeFirstPatch v hpatch _ (by native_decide)]
    native_decide

theorem clipperJumpDest1812 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨1812⟩ : UInt256) = true := by
  apply patchRuntime_D_J_contains_of_patchScanReaches (fuel := 4000) hpatch
  unfold patches patchesFrom offsets immValues
  simp only [List.foldrM_cons, List.foldrM_nil, List.lookup_cons]
  cases hIlk : wordBytes? v.ilk with
  | none =>
      simp [hIlk]
      native_decide
  | some bs =>
      simp [hIlk]
      native_decide

theorem clipperJumpDest512 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨512⟩ : UInt256) = true :=
  clipperJumpDestBeforeFirstPatch v hpatch (⟨512⟩ : UInt256) (by native_decide)

theorem clipperJumpDest548 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨548⟩ : UInt256) = true :=
  clipperJumpDestBeforeFirstPatch v hpatch (⟨548⟩ : UInt256) (by native_decide)

theorem clipperJumpDest572 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨572⟩ : UInt256) = true :=
  clipperJumpDestBeforeFirstPatch v hpatch (⟨572⟩ : UInt256) (by native_decide)

theorem clipperJumpDest1870 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨1870⟩ : UInt256) = true := by
  apply patchRuntime_D_J_contains_of_patchScanReaches (fuel := 4000) hpatch
  unfold patches patchesFrom offsets immValues
  simp only [List.foldrM_cons, List.foldrM_nil, List.lookup_cons]
  cases hIlk : wordBytes? v.ilk with
  | none =>
      simp [hIlk]
      native_decide
  | some bs =>
      simp [hIlk]
      native_decide

theorem clipperJumpDest1890 (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    (D_J code 0).contains (⟨1890⟩ : UInt256) = true := by
  apply patchRuntime_D_J_contains_of_patchScanReaches (fuel := 4000) hpatch
  unfold patches patchesFrom offsets immValues
  simp only [List.foldrM_cons, List.foldrM_nil, List.lookup_cons]
  cases hIlk : wordBytes? v.ilk with
  | none =>
      simp [hIlk]
      native_decide
  | some bs =>
      simp [hIlk]
      native_decide

theorem clipperX_list_entry (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code)
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hreach : ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I)
      (⟨504⟩ : UInt256) [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C) :
    ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I) (⟨1812⟩ : UInt256)
      ((⟨512⟩ : UInt256) :: [sel]) solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C :=
  RD.solcGetterThunk hreach (clipperListEntryWf v hpatch) (clipperJumpDest1812 v hpatch)

@[reducible] def clipperListReturnFromMemWf (code : ByteArray) : Prop :=
  decode code (⟨512⟩ : UInt256) = some (.JUMPDEST, .none)
  ∧ decode code (⟨513⟩ : UInt256) = some (.Push .PUSH1, some (⟨64⟩, 1))
  ∧ decode code (⟨515⟩ : UInt256) = some (.DUP1, .none)
  ∧ decode code (⟨516⟩ : UInt256) = some (.MLOAD, .none)
  ∧ decode code (⟨517⟩ : UInt256) = some (.Push .PUSH1, some (⟨32⟩, 1))
  ∧ decode code (⟨519⟩ : UInt256) = some (.DUP1, .none)
  ∧ decode code (⟨520⟩ : UInt256) = some (.DUP3, .none)
  ∧ decode code (⟨521⟩ : UInt256) = some (.MSTORE, .none)
  ∧ decode code (⟨522⟩ : UInt256) = some (.DUP4, .none)
  ∧ decode code (⟨523⟩ : UInt256) = some (.MLOAD, .none)
  ∧ decode code (⟨524⟩ : UInt256) = some (.DUP2, .none)
  ∧ decode code (⟨525⟩ : UInt256) = some (.DUP4, .none)
  ∧ decode code (⟨526⟩ : UInt256) = some (.ADD, .none)
  ∧ decode code (⟨527⟩ : UInt256) = some (.MSTORE, .none)
  ∧ decode code (⟨528⟩ : UInt256) = some (.DUP4, .none)
  ∧ decode code (⟨529⟩ : UInt256) = some (.MLOAD, .none)
  ∧ decode code (⟨530⟩ : UInt256) = some (.SWAP2, .none)
  ∧ decode code (⟨531⟩ : UInt256) = some (.SWAP3, .none)
  ∧ decode code (⟨532⟩ : UInt256) = some (.DUP4, .none)
  ∧ decode code (⟨533⟩ : UInt256) = some (.SWAP3, .none)
  ∧ decode code (⟨534⟩ : UInt256) = some (.SWAP1, .none)
  ∧ decode code (⟨535⟩ : UInt256) = some (.DUP4, .none)
  ∧ decode code (⟨536⟩ : UInt256) = some (.ADD, .none)
  ∧ decode code (⟨537⟩ : UInt256) = some (.SWAP2, .none)
  ∧ decode code (⟨538⟩ : UInt256) = some (.DUP6, .none)
  ∧ decode code (⟨539⟩ : UInt256) = some (.DUP2, .none)
  ∧ decode code (⟨540⟩ : UInt256) = some (.ADD, .none)
  ∧ decode code (⟨541⟩ : UInt256) = some (.SWAP2, .none)
  ∧ decode code (⟨542⟩ : UInt256) = some (.MUL, .none)
  ∧ decode code (⟨543⟩ : UInt256) = some (.DUP1, .none)
  ∧ decode code (⟨544⟩ : UInt256) = some (.DUP4, .none)
  ∧ decode code (⟨545⟩ : UInt256) = some (.DUP4, .none)
  ∧ decode code (⟨546⟩ : UInt256) = some (.Push .PUSH1, some (⟨0⟩, 1))
  ∧ decode code (⟨548⟩ : UInt256) = some (.JUMPDEST, .none)
  ∧ decode code (⟨549⟩ : UInt256) = some (.DUP4, .none)
  ∧ decode code (⟨550⟩ : UInt256) = some (.DUP2, .none)
  ∧ decode code (⟨551⟩ : UInt256) = some (.LT, .none)
  ∧ decode code (⟨552⟩ : UInt256) = some (.ISZERO, .none)
  ∧ decode code (⟨553⟩ : UInt256) = some (.Push .PUSH2, some (⟨572⟩, 2))
  ∧ decode code (⟨556⟩ : UInt256) = some (.JUMPI, .none)
  ∧ decode code (⟨557⟩ : UInt256) = some (.DUP2, .none)
  ∧ decode code (⟨558⟩ : UInt256) = some (.DUP2, .none)
  ∧ decode code (⟨559⟩ : UInt256) = some (.ADD, .none)
  ∧ decode code (⟨560⟩ : UInt256) = some (.MLOAD, .none)
  ∧ decode code (⟨561⟩ : UInt256) = some (.DUP4, .none)
  ∧ decode code (⟨562⟩ : UInt256) = some (.DUP3, .none)
  ∧ decode code (⟨563⟩ : UInt256) = some (.ADD, .none)
  ∧ decode code (⟨564⟩ : UInt256) = some (.MSTORE, .none)
  ∧ decode code (⟨565⟩ : UInt256) = some (.Push .PUSH1, some (⟨32⟩, 1))
  ∧ decode code (⟨567⟩ : UInt256) = some (.ADD, .none)
  ∧ decode code (⟨568⟩ : UInt256) = some (.Push .PUSH2, some (⟨548⟩, 2))
  ∧ decode code (⟨571⟩ : UInt256) = some (.JUMP, .none)
  ∧ decode code (⟨572⟩ : UInt256) = some (.JUMPDEST, .none)
  ∧ decode code (⟨573⟩ : UInt256) = some (.POP, .none)
  ∧ decode code (⟨574⟩ : UInt256) = some (.POP, .none)
  ∧ decode code (⟨575⟩ : UInt256) = some (.POP, .none)
  ∧ decode code (⟨576⟩ : UInt256) = some (.POP, .none)
  ∧ decode code (⟨577⟩ : UInt256) = some (.SWAP1, .none)
  ∧ decode code (⟨578⟩ : UInt256) = some (.POP, .none)
  ∧ decode code (⟨579⟩ : UInt256) = some (.ADD, .none)
  ∧ decode code (⟨580⟩ : UInt256) = some (.SWAP3, .none)
  ∧ decode code (⟨581⟩ : UInt256) = some (.POP, .none)
  ∧ decode code (⟨582⟩ : UInt256) = some (.POP, .none)
  ∧ decode code (⟨583⟩ : UInt256) = some (.POP, .none)
  ∧ decode code (⟨584⟩ : UInt256) = some (.Push .PUSH1, some (⟨64⟩, 1))
  ∧ decode code (⟨586⟩ : UInt256) = some (.MLOAD, .none)
  ∧ decode code (⟨587⟩ : UInt256) = some (.DUP1, .none)
  ∧ decode code (⟨588⟩ : UInt256) = some (.SWAP2, .none)
  ∧ decode code (⟨589⟩ : UInt256) = some (.SUB, .none)
  ∧ decode code (⟨590⟩ : UInt256) = some (.SWAP1, .none)
  ∧ decode code (⟨591⟩ : UInt256) = some (.RETURN, .none)

theorem clipperListReturnFromMemWfPatched (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    clipperListReturnFromMemWf code := by
  unfold clipperListReturnFromMemWf
  repeat' first | apply And.intro
  all_goals
    rw [clipperDecodeBeforeFirstPatch v hpatch _ (by native_decide)]
    native_decide

noncomputable def clipperListReturnOffsetMem (fmp : UInt256) (mem : ByteArray) :
    ByteArray :=
  (UInt256.toByteArray (⟨32⟩ : UInt256)).write 0 mem fmp.toNat 32

noncomputable def clipperListReturnLengthMem (len fmp : UInt256) (mem : ByteArray) :
    ByteArray :=
  (UInt256.toByteArray len).write 0 (clipperListReturnOffsetMem fmp mem)
    (fmp + (⟨32⟩ : UInt256)).toNat 32

abbrev clipperListReturnMload64Aw (aw : UInt256) : UInt256 :=
  UInt256.ofNat (MachineState.M aw.toNat (⟨64⟩ : UInt256).toNat 32)

abbrev clipperListReturnOffsetAw (aw fmp : UInt256) : UInt256 :=
  UInt256.ofNat (MachineState.M (clipperListReturnMload64Aw aw).toNat fmp.toNat 32)

abbrev clipperListReturnArrayMloadAw (aw fmp arrPtr : UInt256) : UInt256 :=
  UInt256.ofNat (MachineState.M (clipperListReturnOffsetAw aw fmp).toNat arrPtr.toNat 32)

abbrev clipperListReturnLengthAw (aw fmp arrPtr : UInt256) : UInt256 :=
  UInt256.ofNat
    (MachineState.M (clipperListReturnArrayMloadAw aw fmp arrPtr).toNat
      (fmp + (⟨32⟩ : UInt256)).toNat 32)

abbrev clipperListReturnFinalAw (aw fmp arrPtr : UInt256) : UInt256 :=
  UInt256.ofNat (MachineState.M (clipperListReturnLengthAw aw fmp arrPtr).toNat arrPtr.toNat 32)

abbrev clipperListReturnCopyMloadAw (aw src i : UInt256) : UInt256 :=
  UInt256.ofNat (MachineState.M aw.toNat (i + src).toNat 32)

abbrev clipperListReturnCopyStepAw (aw src dst i : UInt256) : UInt256 :=
  UInt256.ofNat (MachineState.M (clipperListReturnCopyMloadAw aw src i).toNat
    (i + dst).toNat 32)

noncomputable def clipperListReturnCopyStepMem
    (word dst i : UInt256) (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray word).write 0 mem (i + dst).toNat 32

set_option maxHeartbeats 1000000 in
theorem clipperListReturnFromMemToCopyLoop {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {arrPtr fmp len : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD code ee g s0 (⟨512⟩ : UInt256) (arrPtr :: R) mem aw rdata acc k C)
    (hwf : clipperListReturnFromMemWf code)
    (hload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32)))
        = fmp)
    (hloadArr :
      (if arrPtr.toNat ≥ (clipperListReturnOffsetMem fmp mem).size
          ∨ arrPtr ≥ clipperListReturnOffsetAw aw fmp * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
           ((clipperListReturnOffsetMem fmp mem).readWithPadding arrPtr.toNat 32)))
        = len)
    (hloadArrTail :
      (if arrPtr.toNat ≥ (clipperListReturnLengthMem len fmp mem).size
          ∨ arrPtr ≥ clipperListReturnLengthAw aw fmp arrPtr * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
           ((clipperListReturnLengthMem len fmp mem).readWithPadding arrPtr.toNat 32)))
        = len)
    (hov : R.length + 10 ≤ 1024) :
    ∃ k' C', RD code ee g s0 (⟨548⟩ : UInt256)
      ((⟨0⟩ : UInt256) :: ((⟨32⟩ : UInt256) + arrPtr) ::
        (fmp + (⟨64⟩ : UInt256)) :: (len * (⟨32⟩ : UInt256)) ::
        (len * (⟨32⟩ : UInt256)) :: ((⟨32⟩ : UInt256) + arrPtr) ::
        (fmp + (⟨64⟩ : UInt256)) :: fmp :: fmp :: arrPtr :: R)
      (clipperListReturnLengthMem len fmp mem) (clipperListReturnFinalAw aw fmp arrPtr)
      rdata acc k' C' := by
  rcases hwf with
    ⟨hd512, hd513, hd515, hd516, hd517, hd519, hd520, hd521, hd522, hd523,
      hd524, hd525, hd526, hd527, hd528, hd529, hd530, hd531, hd532, hd533,
      hd534, hd535, hd536, hd537, hd538, hd539, hd540, hd541, hd542, hd543,
      hd544, hd545, hd546, _⟩
  have rd513 := h.jumpdest hd512 (by evm_ov)
  have rd515 := rd513.push1 ⟨64⟩ hd513 (by evm_ov)
  have rd516 := rd515.dup1 hd515 (by evm_ov)
  have rd517 := rd516.mload (Cₘ (clipperListReturnMload64Aw aw) - Cₘ aw) fmp
    (clipperListReturnMload64Aw aw) hd516
    (by
      intro s haw hstk
      exact mloadCost_of_stack (aw := aw) (off := (⟨64⟩ : UInt256))
        (t := (⟨64⟩ : UInt256) :: arrPtr :: R) haw hstk (by rfl))
    hload64 (by rfl) (by evm_ov)
  have rd519 := rd517.push1 ⟨32⟩ hd517 (by evm_ov)
  have rd520 := rd519.dup1 hd519 (by evm_ov)
  have rd521 := rd520.dup3 hd520 (by evm_ov)
  have rd522 := rd521.mstore
    (Cₘ (clipperListReturnOffsetAw aw fmp) - Cₘ (clipperListReturnMload64Aw aw))
    (clipperListReturnOffsetMem fmp mem) (clipperListReturnOffsetAw aw fmp) hd521
    (by
      intro s haw hstk
      exact mstoreCost_of_stack (aw := clipperListReturnMload64Aw aw) (off := fmp)
        (val := (⟨32⟩ : UInt256))
        (t := (⟨32⟩ : UInt256) :: fmp :: (⟨64⟩ : UInt256) :: arrPtr :: R)
        haw hstk (by rfl))
    (by rfl) (by rfl) (by evm_ov)
  have rd523 := rd522.dup4 hd522 (by evm_ov)
  have rd524 := rd523.mload
    (Cₘ (clipperListReturnArrayMloadAw aw fmp arrPtr) -
      Cₘ (clipperListReturnOffsetAw aw fmp))
    len (clipperListReturnArrayMloadAw aw fmp arrPtr) hd523
    (by
      intro s haw hstk
      exact mloadCost_of_stack (aw := clipperListReturnOffsetAw aw fmp) (off := arrPtr)
        (t := (⟨32⟩ : UInt256) :: fmp :: (⟨64⟩ : UInt256) :: arrPtr :: R)
        haw hstk (by rfl))
    hloadArr (by rfl) (by evm_ov)
  have rd525 := rd524.dup2 hd524 (by evm_ov)
  have rd526 := rd525.dup4 hd525 (by evm_ov)
  have rd527 := rd526.add hd526 (by evm_ov)
  have rd528 := rd527.mstore
    (Cₘ (clipperListReturnLengthAw aw fmp arrPtr) -
      Cₘ (clipperListReturnArrayMloadAw aw fmp arrPtr))
    (clipperListReturnLengthMem len fmp mem) (clipperListReturnLengthAw aw fmp arrPtr)
    hd527
    (by
      intro s haw hstk
      exact mstoreCost_of_stack (aw := clipperListReturnArrayMloadAw aw fmp arrPtr)
        (off := fmp + (⟨32⟩ : UInt256)) (val := len)
        (t := (⟨32⟩ : UInt256) :: fmp :: (⟨64⟩ : UInt256) :: arrPtr :: R)
        haw hstk (by rfl))
    (by rfl) (by rfl) (by evm_ov)
  have rd529 := rd528.dup4 hd528 (by evm_ov)
  have rd530 := rd529.mload
    (Cₘ (clipperListReturnFinalAw aw fmp arrPtr) -
      Cₘ (clipperListReturnLengthAw aw fmp arrPtr))
    len (clipperListReturnFinalAw aw fmp arrPtr) hd529
    (by
      intro s haw hstk
      exact mloadCost_of_stack (aw := clipperListReturnLengthAw aw fmp arrPtr)
        (off := arrPtr)
        (t := (⟨32⟩ : UInt256) :: fmp :: (⟨64⟩ : UInt256) :: arrPtr :: R)
        haw hstk (by rfl))
    hloadArrTail (by rfl) (by evm_ov)
  have rd531 := rd530.swap2 hd530 (by evm_ov)
  have rd532 := rd531.swap3 hd531 (by evm_ov)
  have rd533 := rd532.dup4 hd532 (by evm_ov)
  have rd534 := rd533.swap3 hd533 (by evm_ov)
  have rd535 := rd534.swap1 hd534 (by evm_ov)
  have rd536 := rd535.dup4 hd535 (by evm_ov)
  have rd537 := rd536.add hd536 (by evm_ov)
  have rd538 := rd537.swap2 hd537 (by evm_ov)
  have rd539 := rd538.dup6 hd538 (by evm_ov)
  have rd540 := rd539.dup2 hd539 (by evm_ov)
  have rd541 := rd540.add hd540 (by evm_ov)
  have rd542 := rd541.swap2 hd541 (by evm_ov)
  have rd543 := rd542.mul hd542 (by evm_ov)
  have rd544 := rd543.dup1 hd543 (by evm_ov)
  have rd545 := rd544.dup4 hd544 (by evm_ov)
  have rd546 := rd545.dup4 hd545 (by evm_ov)
  have rd548 := rd546.push1 ⟨0⟩ hd546 (by evm_ov)
  exact ⟨_, _, by
    simpa [clipperListReturnOffsetMem, clipperListReturnLengthMem] using rd548⟩

set_option maxHeartbeats 1000000 in
theorem clipperListReturnCopyLoopStep {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {i src dst bound word : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD code ee g s0 (⟨548⟩ : UInt256) (i :: src :: dst :: bound :: R)
      mem aw rdata acc k C)
    (hwf : clipperListReturnFromMemWf code)
    (h548 : (D_J code 0).contains (⟨548⟩ : UInt256) = true)
    (hcont : UInt256.isZero (UInt256.lt i bound) = ⟨0⟩)
    (hload :
      (if (i + src).toNat ≥ mem.size ∨ (i + src) ≥ aw * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding (i + src).toNat 32))) = word)
    (hov : R.length + 8 ≤ 1024) :
    ∃ k' C', RD code ee g s0 (⟨548⟩ : UInt256)
      (((⟨32⟩ : UInt256) + i) :: src :: dst :: bound :: R)
      (clipperListReturnCopyStepMem word dst i mem)
      (clipperListReturnCopyStepAw aw src dst i) rdata acc k' C' := by
  rcases hwf with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      _, _, _, _, hd548, hd549, hd550, hd551, hd552, hd553, hd556, hd557, hd558,
      hd559, hd560, hd561, hd562, hd563, hd564, hd565, hd567, hd568, hd571, _⟩
  have rd549 := h.jumpdest hd548 (by evm_ov)
  have rd550 := rd549.dup4 hd549 (by evm_ov)
  have rd551 := rd550.dup2 hd550 (by evm_ov)
  have rd552 := rd551.lt hd551 (by evm_ov)
  have rd553raw := rd552.iszero hd552 (by evm_ov)
  have rd553 := by
    simpa [hcont] using rd553raw
  have rd556 := rd553.push2 ⟨572⟩ hd553 (by evm_ov)
  have rd557 := rd556.jumpiNT hd556 rfl (by evm_ov)
  have rd558 := rd557.dup2 hd557 (by evm_ov)
  have rd559 := rd558.dup2 hd558 (by evm_ov)
  have rd560 := rd559.add hd559 (by evm_ov)
  have rd561 := rd560.mload (Cₘ (clipperListReturnCopyMloadAw aw src i) - Cₘ aw)
    word (clipperListReturnCopyMloadAw aw src i) hd560
    (by
      intro s haw hstk
      exact mloadCost_of_stack (aw := aw) (off := i + src)
        (t := i :: src :: dst :: bound :: R) haw hstk (by rfl))
    hload (by rfl) (by evm_ov)
  have rd562 := rd561.dup4 hd561 (by evm_ov)
  have rd563 := rd562.dup3 hd562 (by evm_ov)
  have rd564 := rd563.add hd563 (by evm_ov)
  have rd565 := rd564.mstore
    (Cₘ (clipperListReturnCopyStepAw aw src dst i) -
      Cₘ (clipperListReturnCopyMloadAw aw src i))
    (clipperListReturnCopyStepMem word dst i mem)
    (clipperListReturnCopyStepAw aw src dst i) hd564
    (by
      intro s haw hstk
      exact mstoreCost_of_stack (aw := clipperListReturnCopyMloadAw aw src i)
        (off := i + dst) (val := word) (t := i :: src :: dst :: bound :: R)
        haw hstk (by rfl))
    (by rfl) (by rfl) (by evm_ov)
  have rd567 := rd565.push1 ⟨32⟩ hd565 (by evm_ov)
  have rd568 := rd567.add hd567 (by evm_ov)
  have rd571 := rd568.push2 ⟨548⟩ hd568 (by evm_ov)
  exact ⟨_, _, by
    simpa [clipperListReturnCopyStepMem, clipperListReturnCopyMloadAw,
      clipperListReturnCopyStepAw] using rd571.jump hd571 h548 (by evm_ov)⟩

set_option maxHeartbeats 1000000 in
theorem clipperListReturnCopyLoopExit {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {i src dst bound fmp arrPtr : UInt256}
    {R : List UInt256} {mem rdata oval : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD code ee g s0 (⟨548⟩ : UInt256)
      (i :: src :: dst :: bound :: bound :: src :: dst :: fmp :: fmp :: arrPtr :: R)
      mem aw rdata acc k C)
    (hwf : clipperListReturnFromMemWf code)
    (h572 : (D_J code 0).contains (⟨572⟩ : UInt256) = true)
    (hdone : UInt256.isZero (UInt256.lt i bound) ≠ ⟨0⟩)
    (hload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32)))
        = fmp)
    (hreturn :
      mem.readWithPadding fmp.toNat (UInt256.sub (bound + dst) fmp).toNat = oval)
    (hov : R.length + 12 ≤ 1024) :
    RDret code g s0 acc oval := by
  rcases hwf with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      _, _, _, _, hd548, hd549, hd550, hd551, hd552, hd553, hd556, hd557, hd558,
      hd559, hd560, hd561, hd562, hd563, hd564, hd565, hd567, hd568, hd571,
      hd572, hd573, hd574, hd575, hd576, hd577, hd578, hd579, hd580, hd581,
      hd582, hd583, hd584, hd586, hd587, hd588, hd589, hd590, hd591⟩
  have rd549 := h.jumpdest hd548 (by evm_ov)
  have rd550 := rd549.dup4 hd549 (by evm_ov)
  have rd551 := rd550.dup2 hd550 (by evm_ov)
  have rd552 := rd551.lt hd551 (by evm_ov)
  have rd553 := rd552.iszero hd552 (by evm_ov)
  have rd556 := rd553.push2 ⟨572⟩ hd553 (by evm_ov)
  have rd572 := rd556.jumpiT hd556 hdone h572 (by evm_ov)
  have rd573 := rd572.jumpdest hd572 (by evm_ov)
  have rd574 := rd573.pop hd573 (by evm_ov)
  have rd575 := rd574.pop hd574 (by evm_ov)
  have rd576 := rd575.pop hd575 (by evm_ov)
  have rd577 := rd576.pop hd576 (by evm_ov)
  have rd578 := rd577.swap1 hd577 (by evm_ov)
  have rd579 := rd578.pop hd578 (by evm_ov)
  have rd580 := rd579.add hd579 (by evm_ov)
  have rd581 := rd580.swap3 hd580 (by evm_ov)
  have rd582 := rd581.pop hd581 (by evm_ov)
  have rd583 := rd582.pop hd582 (by evm_ov)
  have rd584 := rd583.pop hd583 (by evm_ov)
  have rd586 := rd584.push1 ⟨64⟩ hd584 (by evm_ov)
  have rd587 := rd586.mload (Cₘ (clipperListReturnMload64Aw aw) - Cₘ aw) fmp
    (clipperListReturnMload64Aw aw) hd586
    (by
      intro s haw hstk
      exact mloadCost_of_stack (aw := aw) (off := (⟨64⟩ : UInt256))
        (t := (bound + dst) :: R) haw hstk (by rfl))
    hload64 (by rfl) (by evm_ov)
  have rd588 := rd587.dup1 hd587 (by evm_ov)
  have rd589 := rd588.swap2 hd588 (by evm_ov)
  have rd590 := rd589.sub hd589 (by evm_ov)
  have rd591 := rd590.swap1 hd590 (by evm_ov)
  exact rd591.ret
    (Cₘ (UInt256.ofNat
          (MachineState.M (clipperListReturnMload64Aw aw).toNat fmp.toNat
            (UInt256.sub (bound + dst) fmp).toNat)) -
        Cₘ (clipperListReturnMload64Aw aw))
    oval hd591
    (by
      intro s haw hstk
      exact returnCost_of_stack (aw := clipperListReturnMload64Aw aw) (off := fmp)
        (len := UInt256.sub (bound + dst) fmp) (t := R) haw hstk (by rfl))
    hreturn (by omega)

theorem clipperListPatchesWindowDisjoint32 (v : ClipperImmutables) {lo hi : Nat}
    (hlo : 1693 ≤ lo) (hhi : hi ≤ 2221) :
    PatchesWindowDisjoint32 lo hi (patches v) := by
  unfold PatchesWindowDisjoint32 PatchWindowDisjoint32 patches patchesFrom offsets immValues
  simp only [List.foldrM_cons, List.foldrM_nil, List.lookup_cons]
  cases hIlk : wordBytes? v.ilk with
  | none =>
      simp [hIlk]
  | some bs =>
      simp [hIlk]
      omega

@[reducible] def clipperListStorageArrayGetterWf (code : ByteArray) : Prop :=
  decode code (⟨1812⟩ : UInt256) = some (.JUMPDEST, .none)
  ∧ decode code (⟨1813⟩ : UInt256) = some (.Push .PUSH1, some (⟨96⟩, 1))
  ∧ decode code (⟨1815⟩ : UInt256) = some (.Push .PUSH1, some (⟨11⟩, 1))
  ∧ decode code (⟨1817⟩ : UInt256) = some (.DUP1, .none)
  ∧ decode code (⟨1818⟩ : UInt256) = some (.SLOAD, .none)
  ∧ decode code (⟨1819⟩ : UInt256) = some (.DUP1, .none)
  ∧ decode code (⟨1820⟩ : UInt256) = some (.Push .PUSH1, some (⟨32⟩, 1))
  ∧ decode code (⟨1822⟩ : UInt256) = some (.MUL, .none)
  ∧ decode code (⟨1823⟩ : UInt256) = some (.Push .PUSH1, some (⟨32⟩, 1))
  ∧ decode code (⟨1825⟩ : UInt256) = some (.ADD, .none)
  ∧ decode code (⟨1826⟩ : UInt256) = some (.Push .PUSH1, some (⟨64⟩, 1))
  ∧ decode code (⟨1828⟩ : UInt256) = some (.MLOAD, .none)
  ∧ decode code (⟨1829⟩ : UInt256) = some (.SWAP1, .none)
  ∧ decode code (⟨1830⟩ : UInt256) = some (.DUP2, .none)
  ∧ decode code (⟨1831⟩ : UInt256) = some (.ADD, .none)
  ∧ decode code (⟨1832⟩ : UInt256) = some (.Push .PUSH1, some (⟨64⟩, 1))
  ∧ decode code (⟨1834⟩ : UInt256) = some (.MSTORE, .none)
  ∧ decode code (⟨1835⟩ : UInt256) = some (.DUP1, .none)
  ∧ decode code (⟨1836⟩ : UInt256) = some (.SWAP3, .none)
  ∧ decode code (⟨1837⟩ : UInt256) = some (.SWAP2, .none)
  ∧ decode code (⟨1838⟩ : UInt256) = some (.SWAP1, .none)
  ∧ decode code (⟨1839⟩ : UInt256) = some (.DUP2, .none)
  ∧ decode code (⟨1840⟩ : UInt256) = some (.DUP2, .none)
  ∧ decode code (⟨1841⟩ : UInt256) = some (.MSTORE, .none)
  ∧ decode code (⟨1842⟩ : UInt256) = some (.Push .PUSH1, some (⟨32⟩, 1))
  ∧ decode code (⟨1844⟩ : UInt256) = some (.ADD, .none)
  ∧ decode code (⟨1845⟩ : UInt256) = some (.DUP3, .none)
  ∧ decode code (⟨1846⟩ : UInt256) = some (.DUP1, .none)
  ∧ decode code (⟨1847⟩ : UInt256) = some (.SLOAD, .none)
  ∧ decode code (⟨1848⟩ : UInt256) = some (.DUP1, .none)
  ∧ decode code (⟨1849⟩ : UInt256) = some (.ISZERO, .none)
  ∧ decode code (⟨1850⟩ : UInt256) = some (.Push .PUSH2, some (⟨1890⟩, 2))
  ∧ decode code (⟨1853⟩ : UInt256) = some (.JUMPI, .none)
  ∧ decode code (⟨1854⟩ : UInt256) = some (.Push .PUSH1, some (⟨32⟩, 1))
  ∧ decode code (⟨1856⟩ : UInt256) = some (.MUL, .none)
  ∧ decode code (⟨1857⟩ : UInt256) = some (.DUP3, .none)
  ∧ decode code (⟨1858⟩ : UInt256) = some (.ADD, .none)
  ∧ decode code (⟨1859⟩ : UInt256) = some (.SWAP2, .none)
  ∧ decode code (⟨1860⟩ : UInt256) = some (.SWAP1, .none)
  ∧ decode code (⟨1861⟩ : UInt256) = some (.Push .PUSH1, some (⟨0⟩, 1))
  ∧ decode code (⟨1863⟩ : UInt256) = some (.MSTORE, .none)
  ∧ decode code (⟨1864⟩ : UInt256) = some (.Push .PUSH1, some (⟨32⟩, 1))
  ∧ decode code (⟨1866⟩ : UInt256) = some (.Push .PUSH1, some (⟨0⟩, 1))
  ∧ decode code (⟨1868⟩ : UInt256) = some (.KECCAK256, .none)
  ∧ decode code (⟨1869⟩ : UInt256) = some (.SWAP1, .none)
  ∧ decode code (⟨1870⟩ : UInt256) = some (.JUMPDEST, .none)
  ∧ decode code (⟨1871⟩ : UInt256) = some (.DUP2, .none)
  ∧ decode code (⟨1872⟩ : UInt256) = some (.SLOAD, .none)
  ∧ decode code (⟨1873⟩ : UInt256) = some (.DUP2, .none)
  ∧ decode code (⟨1874⟩ : UInt256) = some (.MSTORE, .none)
  ∧ decode code (⟨1875⟩ : UInt256) = some (.Push .PUSH1, some (⟨32⟩, 1))
  ∧ decode code (⟨1877⟩ : UInt256) = some (.ADD, .none)
  ∧ decode code (⟨1878⟩ : UInt256) = some (.SWAP1, .none)
  ∧ decode code (⟨1879⟩ : UInt256) = some (.Push .PUSH1, some (⟨1⟩, 1))
  ∧ decode code (⟨1881⟩ : UInt256) = some (.ADD, .none)
  ∧ decode code (⟨1882⟩ : UInt256) = some (.SWAP1, .none)
  ∧ decode code (⟨1883⟩ : UInt256) = some (.DUP1, .none)
  ∧ decode code (⟨1884⟩ : UInt256) = some (.DUP4, .none)
  ∧ decode code (⟨1885⟩ : UInt256) = some (.GT, .none)
  ∧ decode code (⟨1886⟩ : UInt256) = some (.Push .PUSH2, some (⟨1870⟩, 2))
  ∧ decode code (⟨1889⟩ : UInt256) = some (.JUMPI, .none)
  ∧ decode code (⟨1890⟩ : UInt256) = some (.JUMPDEST, .none)
  ∧ decode code (⟨1891⟩ : UInt256) = some (.POP, .none)
  ∧ decode code (⟨1892⟩ : UInt256) = some (.POP, .none)
  ∧ decode code (⟨1893⟩ : UInt256) = some (.POP, .none)
  ∧ decode code (⟨1894⟩ : UInt256) = some (.POP, .none)
  ∧ decode code (⟨1895⟩ : UInt256) = some (.POP, .none)
  ∧ decode code (⟨1896⟩ : UInt256) = some (.SWAP1, .none)
  ∧ decode code (⟨1897⟩ : UInt256) = some (.POP, .none)
  ∧ decode code (⟨1898⟩ : UInt256) = some (.SWAP1, .none)
  ∧ decode code (⟨1899⟩ : UInt256) = some (.JUMP, .none)

theorem clipperListStorageArrayGetterWfPatched (v : ClipperImmutables) {code : ByteArray}
    (hpatch : patchRuntime clipperBytecode (patches v) = some code) :
    clipperListStorageArrayGetterWf code := by
  unfold clipperListStorageArrayGetterWf
  repeat' first | apply And.intro
  all_goals
    exact patchRuntime_decode_disjoint_of_decode_res hpatch
      (by apply clipperListPatchesWindowDisjoint32 v <;> native_decide)
      (by apply clipperListPatchesWindowDisjoint32 v <;> native_decide)
      (by native_decide)
      (by native_decide)
      (by native_decide)

theorem clipperListStorageArrayCleanup {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {a b c d e base ret : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD code ee g s0 (⟨1890⟩ : UInt256)
      (a :: b :: c :: d :: e :: base :: (⟨96⟩ : UInt256) :: ret :: R)
      mem aw rdata acc k C)
    (hwf : clipperListStorageArrayGetterWf code)
    (hret : (D_J code 0).contains ret = true)
    (hov : R.length + 8 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ret (base :: R) mem aw rdata acc k' C' := by
  rcases hwf with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      _, _, _, _,
      hd1890, hd1891, hd1892, hd1893, hd1894, hd1895, hd1896, hd1897, hd1898,
      hd1899⟩
  have rd1891 := h.jumpdest hd1890 (by evm_ov)
  have rd1892 := rd1891.pop hd1891 (by evm_ov)
  have rd1893 := rd1892.pop hd1892 (by evm_ov)
  have rd1894 := rd1893.pop hd1893 (by evm_ov)
  have rd1895 := rd1894.pop hd1894 (by evm_ov)
  have rd1896 := rd1895.pop hd1895 (by evm_ov)
  have rd1897 := rd1896.swap1 hd1896 (by evm_ov)
  have rd1898 := rd1897.pop hd1897 (by evm_ov)
  have rd1899 := rd1898.swap1 hd1898 (by evm_ov)
  exact ⟨_, _, rd1899.jump hd1899 hret (by evm_ov)⟩

abbrev clipperListArrayBasePtr : UInt256 := ⟨128⟩

abbrev clipperListArrayDataPtr : UInt256 := (⟨32⟩ : UInt256) + clipperListArrayBasePtr

abbrev clipperListArrayAllocSize (len : UInt256) : UInt256 :=
  (⟨32⟩ : UInt256) + UInt256.mul (⟨32⟩ : UInt256) len

abbrev clipperListArrayFreePtr (len : UInt256) : UInt256 :=
  clipperListArrayBasePtr + clipperListArrayAllocSize len

noncomputable def clipperListArrayAllocMem (len : UInt256) : ByteArray :=
  (UInt256.toByteArray (clipperListArrayFreePtr len)).write 0 solcFreePtrMem 64 32

noncomputable def clipperListArrayLengthMem (len : UInt256) : ByteArray :=
  (UInt256.toByteArray len).write 0 (clipperListArrayAllocMem len) 128 32

theorem clipperListArrayAllocMem_size (len : UInt256) :
    (clipperListArrayAllocMem len).size = 96 := by
  unfold clipperListArrayAllocMem
  exact writeWord_size_of_96 solcFreePtrMem (clipperListArrayFreePtr len) 64
    solcFreePtrMem_size (by omega)

theorem clipperListArrayAllocMem_read64 (len : UInt256) :
    (clipperListArrayAllocMem len).readWithPadding 64 32 =
      UInt256.toByteArray (clipperListArrayFreePtr len) := by
  unfold clipperListArrayAllocMem
  rw [toByteArray_write32_read_back _ _ 64 (by rw [solcFreePtrMem_size]; omega)]

theorem clipperListArrayLengthMem_size (len : UInt256) :
    (clipperListArrayLengthMem len).size = 160 := by
  unfold clipperListArrayLengthMem
  rw [toByteArray_write32_size_of_ge _ len 128 96 160
    (clipperListArrayAllocMem_size len) (by omega) (by native_decide) (by omega)]

theorem clipperListArrayLengthMem_read64 (len : UInt256) :
    (clipperListArrayLengthMem len).readWithPadding 64 32 =
      UInt256.toByteArray (clipperListArrayFreePtr len) := by
  unfold clipperListArrayLengthMem
  rw [toByteArray_write_read_below_of_gap len (clipperListArrayAllocMem len) 128 64
    (by rw [clipperListArrayAllocMem_size]) (by omega)
    (by rw [clipperListArrayAllocMem_size]; native_decide)]
  exact clipperListArrayAllocMem_read64 len

theorem clipperListArrayLengthMem_read128 (len : UInt256) :
    (clipperListArrayLengthMem len).readWithPadding 128 32 = UInt256.toByteArray len := by
  unfold clipperListArrayLengthMem
  rw [toByteArray_write_read_back_of_gap len (clipperListArrayAllocMem len) 128
    (by rw [clipperListArrayAllocMem_size]; native_decide)]

theorem clipperListArrayLengthMem_mload64 (len : UInt256) :
    (if (⟨64⟩ : UInt256).toNat ≥ (clipperListArrayLengthMem len).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 5 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
         ((clipperListArrayLengthMem len).readWithPadding (⟨64⟩ : UInt256).toNat 32)))
      = clipperListArrayFreePtr len := by
  exact mloadWordValue_of_readWithPadding
    (by rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide,
      clipperListArrayLengthMem_size]; omega)
    (by native_decide)
    (by simpa [show (⟨64⟩ : UInt256).toNat = 64 from by decide] using
      clipperListArrayLengthMem_read64 len)

theorem clipperListArrayLengthMem_mload128 (len : UInt256) :
    (if clipperListArrayBasePtr.toNat ≥ (clipperListArrayLengthMem len).size
        ∨ clipperListArrayBasePtr ≥ UInt256.ofNat 5 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
         ((clipperListArrayLengthMem len).readWithPadding clipperListArrayBasePtr.toNat 32)))
      = len := by
  exact mloadWordValue_of_readWithPadding
    (by rw [show clipperListArrayBasePtr.toNat = 128 from by decide,
      clipperListArrayLengthMem_size]; omega)
    (by native_decide)
    (by simpa [show clipperListArrayBasePtr.toNat = 128 from by decide] using
      clipperListArrayLengthMem_read128 len)

abbrev clipperListArrayEndPtr (len : UInt256) : UInt256 :=
  clipperListArrayDataPtr + UInt256.mul (⟨32⟩ : UInt256) len

theorem clipperListArrayDataPtr_toNat :
    clipperListArrayDataPtr.toNat = 160 := by
  native_decide

theorem clipperStorageWF_mul32_lt {σ : AccountMap} {I : ExecutionEnv}
    (hwf : clipperStorageWF σ I) :
    32 * (solcSlotWord σ I ⟨11⟩).toNat < UInt256.size := by
  unfold clipperStorageWF at hwf
  omega

theorem clipperStorageWF_alloc_lt {σ : AccountMap} {I : ExecutionEnv}
    (hwf : clipperStorageWF σ I) :
    32 + 32 * (solcSlotWord σ I ⟨11⟩).toNat < UInt256.size := by
  unfold clipperStorageWF at hwf
  omega

theorem clipperStorageWF_freePtr_lt {σ : AccountMap} {I : ExecutionEnv}
    (hwf : clipperStorageWF σ I) :
    160 + 32 * (solcSlotWord σ I ⟨11⟩).toNat < UInt256.size := by
  unfold clipperStorageWF at hwf
  omega

theorem clipperStorageWF_returnDst_lt {σ : AccountMap} {I : ExecutionEnv}
    (hwf : clipperStorageWF σ I) :
    224 + 32 * (solcSlotWord σ I ⟨11⟩).toNat < UInt256.size := by
  unfold clipperStorageWF at hwf
  omega

theorem clipperStorageWF_returnEnd_lt {σ : AccountMap} {I : ExecutionEnv}
    (hwf : clipperStorageWF σ I) :
    224 + 64 * (solcSlotWord σ I ⟨11⟩).toNat < UInt256.size := by
  simpa [clipperStorageWF] using hwf.1

theorem clipperListArrayAllocSize_toNat_of_wf {σ : AccountMap} {I : ExecutionEnv}
    (hwf : clipperStorageWF σ I) :
    (clipperListArrayAllocSize (solcSlotWord σ I ⟨11⟩)).toNat =
      32 + 32 * (solcSlotWord σ I ⟨11⟩).toNat := by
  rw [clipperListArrayAllocSize, uadd_toNat, u256_mul_toNat,
    show (⟨32⟩ : UInt256).toNat = 32 from by decide]
  rw [Nat.mod_eq_of_lt (clipperStorageWF_mul32_lt hwf)]
  exact Nat.mod_eq_of_lt (clipperStorageWF_alloc_lt hwf)

theorem clipperListArrayFreePtr_toNat_of_wf {σ : AccountMap} {I : ExecutionEnv}
    (hwf : clipperStorageWF σ I) :
    (clipperListArrayFreePtr (solcSlotWord σ I ⟨11⟩)).toNat =
      160 + 32 * (solcSlotWord σ I ⟨11⟩).toNat := by
  rw [clipperListArrayFreePtr, uadd_toNat,
    show clipperListArrayBasePtr.toNat = 128 from by decide,
    clipperListArrayAllocSize_toNat_of_wf hwf]
  rw [show 128 + (32 + 32 * (solcSlotWord σ I ⟨11⟩).toNat) =
    160 + 32 * (solcSlotWord σ I ⟨11⟩).toNat by omega]
  exact Nat.mod_eq_of_lt (clipperStorageWF_freePtr_lt hwf)

theorem clipperListArrayEndPtr_toNat_of_wf {σ : AccountMap} {I : ExecutionEnv}
    (hwf : clipperStorageWF σ I) :
    (clipperListArrayEndPtr (solcSlotWord σ I ⟨11⟩)).toNat =
      160 + 32 * (solcSlotWord σ I ⟨11⟩).toNat := by
  rw [clipperListArrayEndPtr, uadd_toNat, u256_mul_toNat,
    clipperListArrayDataPtr_toNat,
    show (⟨32⟩ : UInt256).toNat = 32 from by decide]
  rw [Nat.mod_eq_of_lt (clipperStorageWF_mul32_lt hwf)]
  exact Nat.mod_eq_of_lt (clipperStorageWF_freePtr_lt hwf)

theorem clipperListReturnBound_toNat_of_wf {σ : AccountMap} {I : ExecutionEnv}
    (hwf : clipperStorageWF σ I) :
    ((solcSlotWord σ I ⟨11⟩) * (⟨32⟩ : UInt256)).toNat =
      32 * (solcSlotWord σ I ⟨11⟩).toNat := by
  rw [umul_toNat]
  · rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide]
    omega
  · rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide]
    have h := clipperStorageWF_mul32_lt hwf
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using h

theorem clipperListReturnDst_toNat_of_wf {σ : AccountMap} {I : ExecutionEnv}
    (hwf : clipperStorageWF σ I) :
    (clipperListArrayFreePtr (solcSlotWord σ I ⟨11⟩) + (⟨64⟩ : UInt256)).toNat =
      224 + 32 * (solcSlotWord σ I ⟨11⟩).toNat := by
  rw [uadd_toNat, clipperListArrayFreePtr_toNat_of_wf hwf,
    show (⟨64⟩ : UInt256).toNat = 64 from by decide]
  rw [show 160 + 32 * (solcSlotWord σ I ⟨11⟩).toNat + 64 =
    224 + 32 * (solcSlotWord σ I ⟨11⟩).toNat by omega]
  exact Nat.mod_eq_of_lt (clipperStorageWF_returnDst_lt hwf)

theorem clipperListArrayFreePtrAdd32_toNat_of_wf {σ : AccountMap} {I : ExecutionEnv}
    (hwf : clipperStorageWF σ I) :
    (clipperListArrayFreePtr (solcSlotWord σ I ⟨11⟩) + (⟨32⟩ : UInt256)).toNat =
      192 + 32 * (solcSlotWord σ I ⟨11⟩).toNat := by
  rw [uadd_toNat, clipperListArrayFreePtr_toNat_of_wf hwf,
    show (⟨32⟩ : UInt256).toNat = 32 from by decide]
  rw [show 160 + 32 * (solcSlotWord σ I ⟨11⟩).toNat + 32 =
    192 + 32 * (solcSlotWord σ I ⟨11⟩).toNat by omega]
  rw [Nat.mod_eq_of_lt (by
    have h := clipperStorageWF_returnDst_lt hwf
    omega)]

theorem clipperListReturnEnd_toNat_of_wf {σ : AccountMap} {I : ExecutionEnv}
    (hwf : clipperStorageWF σ I) :
    (((solcSlotWord σ I ⟨11⟩) * (⟨32⟩ : UInt256)) +
        (clipperListArrayFreePtr (solcSlotWord σ I ⟨11⟩) + (⟨64⟩ : UInt256))).toNat =
      224 + 64 * (solcSlotWord σ I ⟨11⟩).toNat := by
  rw [uadd_toNat, clipperListReturnBound_toNat_of_wf hwf,
    clipperListReturnDst_toNat_of_wf hwf]
  rw [show 32 * (solcSlotWord σ I ⟨11⟩).toNat +
      (224 + 32 * (solcSlotWord σ I ⟨11⟩).toNat) =
    224 + 64 * (solcSlotWord σ I ⟨11⟩).toNat by omega]
  exact Nat.mod_eq_of_lt (clipperStorageWF_returnEnd_lt hwf)

theorem clipperListReturnSize_toNat_of_wf {σ : AccountMap} {I : ExecutionEnv}
    (hwf : clipperStorageWF σ I) :
    (UInt256.sub
        (((solcSlotWord σ I ⟨11⟩) * (⟨32⟩ : UInt256)) +
          (clipperListArrayFreePtr (solcSlotWord σ I ⟨11⟩) + (⟨64⟩ : UInt256)))
        (clipperListArrayFreePtr (solcSlotWord σ I ⟨11⟩))).toNat =
      64 + 32 * (solcSlotWord σ I ⟨11⟩).toNat := by
  rw [usub_toNat]
  · rw [clipperListReturnEnd_toNat_of_wf hwf, clipperListArrayFreePtr_toNat_of_wf hwf]
    omega
  · rw [clipperListReturnEnd_toNat_of_wf hwf, clipperListArrayFreePtr_toNat_of_wf hwf]
    omega

noncomputable def clipperListArrayHashMem (len : UInt256) : ByteArray :=
  wordAt0Mem (⟨11⟩ : UInt256) (clipperListArrayLengthMem len)

noncomputable def clipperListArrayCopyStepMem
    (σ : AccountMap) (ee : ExecutionEnv) (slot dest : UInt256) (mem : ByteArray) :
    ByteArray :=
  (UInt256.toByteArray (solcSlotWord σ ee slot)).write 0 mem dest.toNat 32

abbrev clipperListArrayCopyStepAw (aw dest : UInt256) : UInt256 :=
  UInt256.ofNat (MachineState.M aw.toNat dest.toNat 32)

theorem clipperListArrayHashMem_size (len : UInt256) :
    (clipperListArrayHashMem len).size = 160 := by
  unfold clipperListArrayHashMem wordAt0Mem
  exact toByteArray_write32_size_of_le
    (clipperListArrayLengthMem len) (⟨11⟩ : UInt256) 0 160 160
    (clipperListArrayLengthMem_size len) (by omega) (by omega)

theorem clipperListArrayHashMem_read64 (len : UInt256) :
    (clipperListArrayHashMem len).readWithPadding 64 32 =
      UInt256.toByteArray (clipperListArrayFreePtr len) := by
  unfold clipperListArrayHashMem wordAt0Mem
  rw [write32_read_above _ _ 0 64 (by rw [toByteArray_size])
    (by rw [clipperListArrayLengthMem_size]; omega)
    (by omega) (by rw [clipperListArrayLengthMem_size]; native_decide)]
  exact clipperListArrayLengthMem_read64 len

theorem clipperListArrayHashMem_read128 (len : UInt256) :
    (clipperListArrayHashMem len).readWithPadding 128 32 =
      UInt256.toByteArray len := by
  unfold clipperListArrayHashMem wordAt0Mem
  rw [write32_read_above _ _ 0 128 (by rw [toByteArray_size])
    (by rw [clipperListArrayLengthMem_size]; omega)
    (by omega) (by rw [clipperListArrayLengthMem_size])]
  exact clipperListArrayLengthMem_read128 len

def clipperListArraySlot : Nat → UInt256
  | 0 => activeDataSlot
  | n + 1 => (⟨1⟩ : UInt256) + clipperListArraySlot n

noncomputable def clipperListArrayCopiedMem
    (σ : AccountMap) (ee : ExecutionEnv) (len : UInt256) : Nat → ByteArray
  | 0 => clipperListArrayHashMem len
  | n + 1 =>
      (UInt256.toByteArray
        (solcSlotWord σ ee (clipperListArraySlot n))).write 0
        (clipperListArrayCopiedMem σ ee len n) (160 + 32 * n) 32

theorem clipperListArrayCopiedMem_size
    (σ : AccountMap) (ee : ExecutionEnv) (len : UInt256) :
    ∀ n, (clipperListArrayCopiedMem σ ee len n).size = 160 + 32 * n
  | 0 => by
      rw [clipperListArrayCopiedMem, clipperListArrayHashMem_size]
  | n + 1 => by
      rw [clipperListArrayCopiedMem]
      exact toByteArray_write32_size_of_ge
        (clipperListArrayCopiedMem σ ee len n)
        (solcSlotWord σ ee (clipperListArraySlot n))
        (160 + 32 * n) (160 + 32 * n) (160 + 32 * (n + 1))
        (clipperListArrayCopiedMem_size σ ee len n) (by omega)
        (by
          have hU : 0 < USize.size := by native_decide
          omega)
        (by omega)

theorem clipperListArrayCopiedMem_read64
    (σ : AccountMap) (ee : ExecutionEnv) (len : UInt256) :
    ∀ n, (clipperListArrayCopiedMem σ ee len n).readWithPadding 64 32 =
      UInt256.toByteArray (clipperListArrayFreePtr len)
  | 0 => by
      rw [clipperListArrayCopiedMem]
      exact clipperListArrayHashMem_read64 len
  | n + 1 => by
      rw [clipperListArrayCopiedMem]
      rw [toByteArray_write_read_below_of_gap
        (solcSlotWord σ ee (clipperListArraySlot n))
        (clipperListArrayCopiedMem σ ee len n) (160 + 32 * n) 64
        (by rw [clipperListArrayCopiedMem_size]; omega)
        (by omega)
        (by
          rw [clipperListArrayCopiedMem_size]
          have hU : 0 < USize.size := by native_decide
          omega)]
      exact clipperListArrayCopiedMem_read64 σ ee len n

theorem clipperListArrayCopiedMem_read128
    (σ : AccountMap) (ee : ExecutionEnv) (len : UInt256) :
    ∀ n, (clipperListArrayCopiedMem σ ee len n).readWithPadding 128 32 =
      UInt256.toByteArray len
  | 0 => by
      rw [clipperListArrayCopiedMem]
      exact clipperListArrayHashMem_read128 len
  | n + 1 => by
      rw [clipperListArrayCopiedMem]
      rw [toByteArray_write_read_below_of_gap
        (solcSlotWord σ ee (clipperListArraySlot n))
        (clipperListArrayCopiedMem σ ee len n) (160 + 32 * n) 128
        (by rw [clipperListArrayCopiedMem_size]; omega)
        (by omega)
        (by
          rw [clipperListArrayCopiedMem_size]
          have hU : 0 < USize.size := by native_decide
          omega)]
      exact clipperListArrayCopiedMem_read128 σ ee len n

theorem clipperListArrayCopiedMem_read_elem
    (σ : AccountMap) (ee : ExecutionEnv) (len : UInt256) :
    ∀ n i, i < n →
      (clipperListArrayCopiedMem σ ee len n).readWithPadding (160 + 32 * i) 32 =
        UInt256.toByteArray (solcSlotWord σ ee (clipperListArraySlot i))
  | 0, i, hi => by omega
  | n + 1, i, hi => by
      rw [clipperListArrayCopiedMem]
      by_cases hlast : i = n
      · subst i
        rw [toByteArray_write_read_back_of_gap
          (solcSlotWord σ ee (clipperListArraySlot n))
          (clipperListArrayCopiedMem σ ee len n) (160 + 32 * n)
          (by
            rw [clipperListArrayCopiedMem_size]
            have hU : 0 < USize.size := by native_decide
            omega)]
      · have hi' : i < n := by omega
        rw [toByteArray_write_read_below_of_gap
          (solcSlotWord σ ee (clipperListArraySlot n))
          (clipperListArrayCopiedMem σ ee len n) (160 + 32 * n) (160 + 32 * i)
          (by rw [clipperListArrayCopiedMem_size]; omega)
          (by omega)
          (by
            rw [clipperListArrayCopiedMem_size]
            have hU : 0 < USize.size := by native_decide
            omega)]
        exact clipperListArrayCopiedMem_read_elem σ ee len n i hi'

abbrev clipperListArrayDest (n : Nat) : UInt256 :=
  UInt256.ofNat (160 + 32 * n)

def clipperListArrayCopiedAw : Nat → UInt256
  | 0 => UInt256.ofNat 5
  | n + 1 => clipperListArrayCopyStepAw (clipperListArrayCopiedAw n) (clipperListArrayDest n)

theorem clipperListArrayCopiedAw_toNat {n : Nat}
    (h : 160 + 32 * n < UInt256.size) :
    (clipperListArrayCopiedAw n).toNat = 5 + n := by
  induction n with
  | zero =>
      native_decide
  | succ n ih =>
      have hprev : (clipperListArrayCopiedAw n).toNat = 5 + n := ih (by omega)
      have hdest : (clipperListArrayDest n).toNat = 160 + 32 * n :=
        ulit_toNat' _ (by omega)
      change (UInt256.ofNat
        (MachineState.M (clipperListArrayCopiedAw n).toNat
          (clipperListArrayDest n).toNat 32)).toNat = 5 + (n + 1)
      rw [hprev, hdest]
      change (UInt256.ofNat (MachineState.M (5 + n) (160 + 32 * n) 32)).toNat =
        5 + (n + 1)
      have hM : MachineState.M (5 + n) (160 + 32 * n) 32 = 5 + (n + 1) := by
        unfold MachineState.M
        have hdiv : (160 + 32 * n + 32 + 31) / 32 = 5 + (n + 1) := by
          rw [show 160 + 32 * n + 32 + 31 = 31 + (5 + (n + 1)) * 32 by omega]
          rw [Nat.add_mul_div_right _ _ (by omega)]
          rw [Nat.div_eq_of_lt (by omega)]
          omega
        simp only
        rw [hdiv]
        exact max_eq_right (by omega)
      rw [hM]
      exact ulit_toNat' _ (by omega)

theorem clipperListArrayCopiedAw_eq_of_wf {σ : AccountMap} {I : ExecutionEnv}
    (hwf : clipperStorageWF σ I) :
    clipperListArrayCopiedAw (solcSlotWord σ I ⟨11⟩).toNat =
      UInt256.ofNat (5 + (solcSlotWord σ I ⟨11⟩).toNat) := by
  apply u256_inj
  rw [clipperListArrayCopiedAw_toNat (clipperStorageWF_freePtr_lt hwf),
    ulit_toNat']
  unfold clipperStorageWF at hwf
  omega

theorem clipperListArrayDest_zero :
    clipperListArrayDest 0 = clipperListArrayDataPtr := by
  native_decide

theorem clipperListArrayDest_toNat {n : Nat}
    (h : 160 + 32 * n < UInt256.size) :
    (clipperListArrayDest n).toNat = 160 + 32 * n :=
  ulit_toNat' _ h

theorem clipperListArrayDest_succ {n : Nat}
    (h : 160 + 32 * (n + 1) < UInt256.size) :
    (⟨32⟩ : UInt256) + clipperListArrayDest n = clipperListArrayDest (n + 1) := by
  apply u256_inj
  rw [uadd_toNat, clipperListArrayDest_toNat (n := n) (by omega),
    show (⟨32⟩ : UInt256).toNat = 32 from by decide,
    clipperListArrayDest_toNat (n := n + 1) h]
  rw [show 32 + (160 + 32 * n) = 160 + 32 * (n + 1) by omega]
  rw [Nat.mod_eq_of_lt h]

theorem clipperListArrayEndPtr_eq_dest_of_wf {σ : AccountMap} {I : ExecutionEnv}
    (hwf : clipperStorageWF σ I) :
    clipperListArrayEndPtr (solcSlotWord σ I ⟨11⟩) =
      clipperListArrayDest (solcSlotWord σ I ⟨11⟩).toNat := by
  apply u256_inj
  rw [clipperListArrayEndPtr_toNat_of_wf hwf,
    clipperListArrayDest_toNat (clipperStorageWF_freePtr_lt hwf)]

theorem clipperListArrayCopyStepMem_eq_copied {σ : AccountMap} {ee : ExecutionEnv}
    {len : UInt256} {n : Nat}
    (h : 160 + 32 * n < UInt256.size) :
    clipperListArrayCopyStepMem σ ee (clipperListArraySlot n) (clipperListArrayDest n)
        (clipperListArrayCopiedMem σ ee len n) =
      clipperListArrayCopiedMem σ ee len (n + 1) := by
  simp [clipperListArrayCopyStepMem, clipperListArrayCopiedMem,
    clipperListArrayDest_toNat h]

abbrev clipperListReturnCopyIndex (n : Nat) : UInt256 :=
  UInt256.ofNat (32 * n)

end Benchmarks.Dss.Clipper
