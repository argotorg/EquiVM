import Benchmarks.WETH9.Routines

/-!
# WETH9 `approve(address,uint256)` refinement

`approve` peels its non-payable callvalue guard, decodes `(address guy, uint256 wad)`, stores
`allowance[msg.sender][guy] = wad` (a caller-keyed nested-mapping store over slot 4), emits the
`Approval` event (`LOG3`), and ABI-encodes the constant `true`.  The body is structurally the
DappHub/Dai `approve` (caller-keyed outer hash, masked-argument inner hash) over slot 4.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

namespace Benchmarks.WETH9

/-! ## ABI decode and source-level body for `approve(address,uint256)` -/

abbrev approveGuyWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

abbrev approveGuyMaskedWord (I : ExecutionEnv) : UInt256 :=
  UInt256.land solcAddrMask (approveGuyWord I)

abbrev approveWadWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 36

abbrev approveGuyValue (I : ExecutionEnv) : Value :=
  .address (AccountAddress.ofNat (approveGuyWord I).toNat)

abbrev approveWadValue (I : ExecutionEnv) : Value :=
  .int (Int.ofNat (approveWadWord I).toNat)

abbrev approveOwnerKey (I : ExecutionEnv) : KeyValue :=
  .address I.source

abbrev approveGuyKey (I : ExecutionEnv) : KeyValue :=
  .address (AccountAddress.ofNat (approveGuyWord I).toNat)

abbrev approveStore (I : ExecutionEnv) : Store :=
  ((∅ : Store).insert "guy" (approveGuyValue I)).insert "wad" (approveWadValue I)

def approveStorageSlot (I : ExecutionEnv) : UInt256 :=
  allowanceSlot (approveOwnerKey I) (approveGuyKey I)

def approvePostState (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner (approveStorageSlot I) (approveWadWord I)

abbrev approveEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "allowance", steps := [.mindex (approveOwnerKey I), .mindex (approveGuyKey I)] }

theorem approveStore_get_guy (I : ExecutionEnv) :
    (approveStore I).get? "guy" = some (approveGuyValue I) := by
  unfold approveStore
  rw [store_get_ne
    (L := (∅ : Store).insert "guy" (approveGuyValue I))
    (k := "wad") (a := "guy") (approveWadValue I) (by native_decide)]
  simp

theorem approveStore_get_wad (I : ExecutionEnv) :
    (approveStore I).get? "wad" = some (approveWadValue I) := by
  unfold approveStore
  simp

theorem approveStore_allowance (I : ExecutionEnv) :
    (approveStore I).get? "allowance" = none := by
  unfold approveStore
  rw [store_get_ne _ _ (by native_decide), store_get_ne _ _ (by native_decide)]
  simp

theorem approveStore_index_guy (I : ExecutionEnv) :
    (approveStore I)["guy"] = approveGuyValue I := by
  unfold approveStore
  rw [Std.HashMap.getElem_insert]
  simp

theorem approveGuyMaskedWord_canonical (I : ExecutionEnv) :
    (approveGuyMaskedWord I).toNat < EVM.addressModulus := by
  unfold approveGuyMaskedWord
  rw [u256_land_comm solcAddrMask (approveGuyWord I)]
  exact solcAddrMask_result_canonical (approveGuyWord I)

theorem approveStorageSlot_eq_mapSlot_masked (I : ExecutionEnv) :
    approveStorageSlot I =
      mapSlot (approveGuyMaskedWord I) (mapSlot (solcSourceWord I) ⟨4⟩) := by
  unfold approveStorageSlot allowanceSlot allowanceOwnerSlot approveOwnerKey approveGuyKey
    approveGuyMaskedWord
  rw [keyValueToWord_address_ofNat_mask, keyValueToWord_address]

theorem weth9SelectorDispatchApprove {I : ExecutionEnv} (hsel : selIs I (weth9SelBytes 1)) :
    selectorDispatchMsg contract I.calldata = some approveTransition := by
  have hcd : I.calldata.extract 0 4 = weth9SelBytes 1 := (byteArray_eq_of_beq hsel).symm
  rw [selectorDispatchMsg_eq_dispatchList contract I.calldata]
  simp only [contract, dispatchList, selectorOf, hcd,
    weth9NameSelectorBytes, weth9ApproveSelectorBytes]
  native_decide

theorem weth9Decode_approve_ok {I : ExecutionEnv} (hsz68 : 68 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (approveTransition.params.map Param.name)
      (transitionSignature approveTransition).paramTypes I.calldata =
        some (approveStore I) := by
  show decodeCalldataWithMode config.abiDecodeMode ["guy", "wad"] [addr, uint256]
    I.calldata = _
  simpa [approveStore, approveGuyValue, approveWadValue, approveGuyWord, approveWadWord,
    calldataWord]
    using decodeCalldata_legacyAddress_uint256_ok
      (cd := I.calldata) (x := "guy") (y := "wad") hsz68

theorem weth9Decode_approve_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 68) :
    decodeCalldataWithMode config.abiDecodeMode (approveTransition.params.map Param.name)
      (transitionSignature approveTransition).paramTypes I.calldata = none := by
  show decodeCalldataWithMode config.abiDecodeMode ["guy", "wad"] [addr, uint256]
    I.calldata = none
  simpa using decodeCalldata_legacyAddress_uint256_none_short
    (cd := I.calldata) (x := "guy") (y := "wad") hsz4 hshort

theorem evalExpr_approve_wad (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := approveStore I } evm
      (.var "wad") = .ok (approveWadValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [approveStore_get_wad]

theorem evalStorageRef_approve_allowance (evm : EVM.State) (I : ExecutionEnv)
    (hsrc : evm.executionEnv.source = I.source) :
    evalStorageRef config { contract := contract, locals := approveStore I } evm
      (allowanceRef sender (.var "guy")) = .ok (approveEvaledRef I) := by
  simp [evalStorageRef, evalStorageRefStep, allowanceRef, sender, envValue, approveEvaledRef, hsrc,
    approveGuyValue, approveOwnerKey, approveGuyKey, valueToKey?,
    EvalResult.bind, EvalResult.ofOption, bind, pure, evalExpr?,
    approveStore_index_guy]

theorem approveAssign (evm : EVM.State) (I : ExecutionEnv)
    (hsrc : evm.executionEnv.source = I.source) :
    assignStorageRef? config { contract := contract, locals := approveStore I } evm
      .storage (allowanceRef sender (.var "guy")) (approveWadValue I) =
        .ok ({ contract := contract, locals := approveStore I }, approvePostState evm I) := by
  simp only [allowanceRef]
  apply assignStorageRef_storage_scalar
      (ty := uint256St)
      (loc := wordLoc (approveStorageSlot I))
      (hbase := approveStore_allowance I)
      (her := evalStorageRef_approve_allowance evm I hsrc)
      (hty := by
        simp [storageTypeAt?, storageTypeStep?, contract, storageDecls,
          approveOwnerKey, approveGuyKey, uint256St])
      (hloc := by rfl)
  simpa [approvePostState, wordLoc, uint256Loc, uint256Int] using
    storageLocStore_uint256 evm (approveStorageSlot I) (approveWadWord I)

/-- The Solm `approve(address,uint256)` body stores `allowance[msg.sender][guy] = wad` and returns
    `true`. -/
theorem weth9ApproveBodyReturns (evm : EVM.State) (I : ExecutionEnv)
    (h : evm.executionEnv.weiValue = ⟨0⟩)
    (hsrc : evm.executionEnv.source = I.source) :
    ExecTransitionBody config contract evm (approveStore I) approveTransition.body
      (.returned { contract := contract, locals := approveStore I }
        (approvePostState evm I) (some [.bool true])) := by
  refine ExecFuncBody.execBlockRet ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true h)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_approve_wad evm I) (approveAssign evm I hsrc)) ?_
  exact ExecBlock.consReturn
    (ExecStmt.return (evalExprs?_singleton (by simp [evalExpr?, pure])))

/-! ## EVM trace : scratch-memory abbreviations -/

noncomputable abbrev approveInnerMem (I : ExecutionEnv) : ByteArray :=
  twoWordHashMem (solcSourceWord I) ⟨4⟩ solcFreePtrMem

noncomputable abbrev approveInnerSlot (I : ExecutionEnv) : UInt256 :=
  mapSlot (solcSourceWord I) ⟨4⟩

noncomputable abbrev approveHashMem (I : ExecutionEnv) : ByteArray :=
  twoWordHashMem (approveGuyMaskedWord I) (approveInnerSlot I) (approveInnerMem I)

noncomputable abbrev approveLogMem (I : ExecutionEnv) : ByteArray :=
  solcScratchReturnMem (approveHashMem I) (approveWadWord I)

noncomputable abbrev approveBoolReturnMem (I : ExecutionEnv) : ByteArray :=
  (UInt256.toByteArray (UInt256.isZero (UInt256.isZero (⟨1⟩ : UInt256)))).write 0
    (approveLogMem I) 128 32

theorem approveStorageSlot_eq_innerSlot (I : ExecutionEnv) :
    approveStorageSlot I = mapSlot (approveGuyMaskedWord I) (approveInnerSlot I) := by
  simpa [approveInnerSlot] using approveStorageSlot_eq_mapSlot_masked I

theorem approveInnerMem_size (I : ExecutionEnv) :
    (approveInnerMem I).size = 96 :=
  twoWordHashMem_size_96 (solcSourceWord I) ⟨4⟩ solcFreePtrMem_size

theorem approveInnerMem_read64 (I : ExecutionEnv) :
    (approveInnerMem I).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ :=
  twoWordHashMem_read64 (solcSourceWord I) ⟨4⟩ solcFreePtrMem_size solcFreePtrMem_read64

theorem approveHashMem_size (I : ExecutionEnv) :
    (approveHashMem I).size = 96 :=
  twoWordHashMem_size_96 (approveGuyMaskedWord I) (approveInnerSlot I) (approveInnerMem_size I)

theorem approveHashMem_read64 (I : ExecutionEnv) :
    (approveHashMem I).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ :=
  twoWordHashMem_read64 (approveGuyMaskedWord I) (approveInnerSlot I)
    (approveInnerMem_size I) (approveInnerMem_read64 I)

theorem approveHashMem_mload64 (I : ExecutionEnv) :
    (if (⟨64⟩ : UInt256).toNat ≥ (approveHashMem I).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 3 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((approveHashMem I).readWithPadding (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ :=
  mloadFreePtrValue (by rw [approveHashMem_size]; decide) (by decide)
    (approveHashMem_read64 I)

theorem approveLogMem_size (I : ExecutionEnv) :
    (approveLogMem I).size = 160 :=
  solcScratchReturnMem_size (approveWadWord I) (approveHashMem_size I)

theorem approveLogMem_read64 (I : ExecutionEnv) :
    (approveLogMem I).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ :=
  solcScratchReturnMem_read64 (approveWadWord I) (approveHashMem_size I)
    (approveHashMem_read64 I)

theorem approveLogMem_mload64 (I : ExecutionEnv) :
    (if (⟨64⟩ : UInt256).toNat ≥ (approveLogMem I).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 5 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((approveLogMem I).readWithPadding (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ :=
  solcScratchReturnMem_mload64 (approveWadWord I) (approveHashMem_size I)
    (approveHashMem_read64 I)

theorem approveBoolReturnMem_size (I : ExecutionEnv) :
    (approveBoolReturnMem I).size = 160 := by
  unfold approveBoolReturnMem
  exact toByteArray_write32_size_of_le (approveLogMem I)
    (UInt256.isZero (UInt256.isZero (⟨1⟩ : UInt256))) 128 160 160
    (approveLogMem_size I) (by rw [approveLogMem_size]; decide) (by decide)

theorem approveBoolReturnMem_read64 (I : ExecutionEnv) :
    (approveBoolReturnMem I).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold approveBoolReturnMem
  rw [write32_read_below _ _ 128 64 (by rw [toByteArray_size])
      (by rw [approveLogMem_size]; omega) (by omega)]
  exact approveLogMem_read64 I

theorem approveBoolReturnMem_mload64 (I : ExecutionEnv) :
    (if (⟨64⟩ : UInt256).toNat ≥ (approveBoolReturnMem I).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 5 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((approveBoolReturnMem I).readWithPadding (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ :=
  mloadFreePtrValue (by rw [approveBoolReturnMem_size]; decide) (by decide)
    (approveBoolReturnMem_read64 I)

theorem approveBoolReturnMem_read128 (I : ExecutionEnv) :
    (approveBoolReturnMem I).readWithPadding 128 32 =
      UInt256.toByteArray (UInt256.isZero (UInt256.isZero (⟨1⟩ : UInt256))) := by
  unfold approveBoolReturnMem
  exact toByteArray_write32_read_back (approveLogMem I)
    (UInt256.isZero (UInt256.isZero (⟨1⟩ : UInt256))) 128
    (by rw [approveLogMem_size]; decide)

abbrev approveApprovalTopic : UInt256 :=
  ⟨0x8c5be1e5ebec7d5bd14f71427d1e84f3dd0314c0f7b2291e5b200ac8c7c3b925⟩

/-! ## EVM trace : reach the body, store + log, and encode the bool -/

/-- Peel the callvalue guard (304 → 318), pass the `size ≥ 68` decode guard, decode
    `(address guy, uint256 wad)`, and jump to the body entry (pc 981). -/
theorem weth9ApproveReachDecode {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = weth9Bytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (weth9SelBytes 1)) :
    ∃ k C, RD weth9Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨981⟩
      [approveWadWord I, approveGuyMaskedWord I, ⟨361⟩, weth9SelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, h304⟩ := weth9ReachApprove (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode (by omega) hsize hsel
  obtain ⟨_, _, h318⟩ := weth9GuardPeelOk (gt := ⟨316⟩) h304 hwv
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by jump_dest) (by native_decide) (by native_decide)
  have hlt : UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨0⟩ :=
    solcDecodeLenCheckOkUnsigned (by simpa using hsz68) hsize
  have h339 := h318.push2 ⟨361⟩ (by native_decide) (by simp)
    |>.push1 ⟨4⟩ (by native_decide) (by simp)
    |>.dup1 (by native_decide) (by simp)
    |>.calldatasize (by native_decide) (by simp)
    |>.sub (by native_decide) (by simp)
    |>.push1 ⟨64⟩ (by native_decide) (by simp)
    |>.dup2 (by native_decide) (by simp)
    |>.lt (by native_decide) (by simp)
    |>.iszero (by native_decide) (by simp)
    |>.push2 ⟨339⟩ (by native_decide) (by simp)
    |>.jumpiT (by native_decide) (by rw [hlt]; decide) (by jump_dest) (by simp)
  obtain ⟨_, _, h981⟩ := RD.solcAddressUint256ExternalMaskAndJumpMasked (routine := ⟨981⟩) h339
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by jump_dest) (by simp only [List.length_singleton]; omega)
  exact ⟨_, _, by
    simpa [approveWadWord, approveGuyMaskedWord, approveGuyWord, calldataWord] using h981⟩

/-- The store + `Approval` log (981 → 361): store `allowance[caller][guy] = wad` and emit `LOG3`,
    reaching the bool-return encoder at pc 361 with the constant `1` on the stack. -/
theorem weth9ApproveStoreLog {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (hperm : I.perm = true)
    (h : RD weth9Bytecode I g s0 ⟨981⟩
      [approveWadWord I, approveGuyMaskedWord I, ⟨361⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD weth9Bytecode I g s0 ⟨361⟩ [⟨1⟩, sel]
      (approveLogMem I) (UInt256.ofNat 5) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ (approveStorageSlot I) (approveWadWord I)) k' C' := by
  have hinnerSlot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((approveInnerMem I).readWithPadding 0 64))) =
        approveInnerSlot I := by
    simpa [approveInnerMem, approveInnerSlot, mapSlot, solcMappingSlot] using
      twoWordHashMem_solcMappingSlot (⟨4⟩ : UInt256) (solcSourceWord I) solcFreePtrMem_size
  have houterSlot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((approveHashMem I).readWithPadding 0 64))) =
        mapSlot (approveGuyMaskedWord I) (approveInnerSlot I) := by
    simpa [approveHashMem, mapSlot, solcMappingSlot] using
      twoWordHashMem_solcMappingSlot (approveInnerSlot I) (approveGuyMaskedWord I)
        (approveInnerMem_size I)
  have rd982pre := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw caller (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd987 := rd982pre.mstore 0 (wordAt0Mem (solcSourceWord I) solcFreePtrMem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd993pre := evm_run rd987 with [
    raw push1 ⟨4⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd994 := rd993pre.mstore 0 (approveInnerMem I) (UInt256.ofNat 3)
    (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd998pre := evm_run rd994 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov)]
  have rd999 := rd998pre.keccak256 0 (approveInnerSlot I) (UInt256.ofNat 3)
    (by native_decide) mem_cost hinnerSlot (by native_decide) (by evm_ov)
  have rd1011pre := evm_run rd999 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw dup8 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup6 (by native_decide) (by evm_ov)]
  have hmask :
      UInt256.land (approveGuyMaskedWord I)
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩)
        = approveGuyMaskedWord I := by
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide]
    exact solcAddrMask_clean (approveGuyMaskedWord_canonical I)
  rw [hmask] at rd1011pre
  have rd1012 := rd1011pre.mstore 0 (wordAt0Mem (approveGuyMaskedWord I) (approveInnerMem I))
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd1014pre := evm_run rd1012 with [
    raw swap1 (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov)]
  have rd1015 := rd1014pre.mstore 0 (approveHashMem I) (UInt256.ofNat 3)
    (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd1017pre := evm_run rd1015 with [
    raw dup2 (by native_decide) (by evm_ov),
    raw dup5 (by native_decide) (by evm_ov)]
  have rd1018 := rd1017pre.keccak256 0
    (mapSlot (approveGuyMaskedWord I) (approveInnerSlot I)) (UInt256.ofNat 3)
    (by native_decide) mem_cost houterSlot (by native_decide) (by evm_ov)
  have rd1020pre := evm_run rd1018 with [
    raw dup7 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  obtain ⟨_, _, rd1021raw⟩ := rd1020pre.sstore hperm (by native_decide)
    (by change 9 ≤ 1024; decide)
  have rd1026pre := evm_run rd1021raw with [
    raw dup2 (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide) mem_cost
      (approveHashMem_mload64 I) (by decide) (by evm_ov),
    raw dup7 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd1026 := rd1026pre.mstore 6 (approveLogMem I) (UInt256.ofNat 5)
    (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd1034pre := evm_run rd1026 with [
    raw swap2 (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) (by native_decide) mem_cost
      (approveLogMem_mload64 I) (by decide) (by evm_ov),
    raw swap4 (by native_decide) (by evm_ov),
    raw swap5 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap4 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov)]
  have rd1035 := rd1034pre.pushConst approveApprovalTopic (width := 32) (op := .PUSH32)
    (by decide) (by native_decide) (by evm_ov)
  have rd1074pre := evm_run rd1035 with [
    raw swap3 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd1074 := rd1074pre.log3 0 (UInt256.ofNat 5) (by native_decide) hperm
    mem_cost (by decide) (by change 5 ≤ 1024; decide)
  have rd1082pre := evm_run rd1074 with [
    raw pop (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov)]
  exact ⟨_, _, by
    simpa [approveStorageSlot_eq_innerSlot I] using
      rd1082pre.jump (by native_decide) (by jump_dest) (by evm_ov)⟩

/-- The full `approve` EVM run (68 ≤ calldata): stores `allowance[caller][guy] = wad`, logs, and
    returns the ABI encoding of `true`. -/
theorem weth9ApproveX_ok {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = weth9Bytecode) (hwv : I.weiValue = ⟨0⟩) (hperm : I.perm = true)
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (weth9SelBytes 1)) :
    RDret weth9Bytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, sstoreAccountMap I.codeOwner σ (approveStorageSlot I) (approveWadWord I))
      (UInt256.toByteArray ⟨1⟩) := by
  obtain ⟨_, _, h981⟩ := weth9ApproveReachDecode (g := g) hcode hwv hsz68 hsize hsel
  obtain ⟨_, _, h361⟩ := weth9ApproveStoreLog (I := I) hperm h981
  have hretWf : solcReturnBoolFromMemWf weth9Bytecode ⟨361⟩ := by
    unfold solcReturnBoolFromMemWf
    repeat' first | apply And.intro | native_decide
  have hbool : UInt256.isZero (UInt256.isZero (⟨1⟩ : UInt256)) = ⟨1⟩ := by native_decide
  simpa [hbool] using
    RD.solcReturnBoolFromMem h361 hretWf (approveLogMem_mload64 I) (by rfl)
      (approveBoolReturnMem_mload64 I) (approveBoolReturnMem_read128 I)
      (by simp only [List.length_singleton]; omega)

/-! ## Refinement -/

theorem weth9ApproveBodyCoreOk {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = weth9Bytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsz68 : 68 ≤ I.calldata.size)
    (hsel : selIs I (weth9SelBytes 1))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) (approveStore I)
        approveTransition.body
        (.returned { contract := contract, locals := approveStore I }
          (approvePostState (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I)
          (some [.bool true])) :=
    weth9ApproveBodyReturns (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I
      (by simp only [initState]; exact hwv) (by simp [initState])
  refine weth9ReEquivExecGen (t := approveTransition) hcode
    (weth9ApproveX_ok (g := Sat256.ofUInt256 g) hcode hwv hperm hsz68 hsize hsel)
    (weth9SelectorDispatchApprove hsel) (weth9Decode_approve_ok hsz68) hbody ?_ ?_ ?_
  · simp [approvePostState, initState, storageStore_createdAccounts]
  · simpa [approvePostState, initState, storageStore_accountMap] using
      accountMapEquiv_sstoreAccountMap I.codeOwner (approveStorageSlot I)
        (approveWadWord I) hAccounts
  · exact returnEquiv_of_encode (by simpa [boolTy] using boolTrueReturnEncoding)

theorem weth9ApproveBodyCoreDecodeFailed_short {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = weth9Bytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩) (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 68)
    (hsel : selIs I (weth9SelBytes 1)) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  obtain ⟨_, _, h304⟩ := weth9ReachApprove (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
    (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g) hcode hsz4 hsize hsel
  obtain ⟨_, _, h318⟩ := weth9GuardPeelOk (gt := ⟨316⟩) h304 hwv
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by jump_dest) (by native_decide) (by native_decide)
  have hltShort : UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨1⟩ := by
    apply ult_one
    rw [usub_ofNat_word_toNat (show (⟨4⟩ : UInt256).toNat ≤ I.calldata.size by simpa using hsz4)
      hsize]
    simp only [show (⟨64⟩ : UInt256).toNat = 64 from rfl,
      show (⟨4⟩ : UInt256).toNat = 4 from rfl]; omega
  have hrev : RDrev weth9Bytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) :=
    h318.push2 ⟨361⟩ (by native_decide) (by simp)
      |>.push1 ⟨4⟩ (by native_decide) (by simp)
      |>.dup1 (by native_decide) (by simp)
      |>.calldatasize (by native_decide) (by simp)
      |>.sub (by native_decide) (by simp)
      |>.push1 ⟨64⟩ (by native_decide) (by simp)
      |>.dup2 (by native_decide) (by simp)
      |>.lt (by native_decide) (by simp)
      |>.iszero (by native_decide) (by simp)
      |>.push2 ⟨339⟩ (by native_decide) (by simp)
      |>.jumpiNT (by native_decide) (by rw [hltShort]; decide) (by simp)
      |>.uniswapPush1Dup1Revert0 (by native_decide) (by native_decide) (by native_decide) (by simp)
  exact weth9ReEquivDecodeFailed hcode hrev (weth9SelectorDispatchApprove hsel)
    (weth9Decode_approve_none_short hsz4 hshort)

/-- `approve(address,uint256)` body refines its Solm transition (all branches). -/
theorem weth9ApproveBodyCore {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = weth9Bytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hsel : selIs I (weth9SelBytes 1))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (weth9SelBytes 1) (by native_decide) hsel
  by_cases hwv : I.weiValue = ⟨0⟩
  · by_cases hsz68 : 68 ≤ I.calldata.size
    · exact weth9ApproveBodyCoreOk hcode hsize hperm hwv hsz68 hsel hAccounts
    · exact weth9ApproveBodyCoreDecodeFailed_short hcode hsize hwv hsz4 (by omega) hsel
  · obtain ⟨_, _, h304⟩ := weth9ReachApprove (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
      (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g) hcode hsz4 hsize hsel
    have hrev := weth9GuardPeelRev (gt := ⟨316⟩) h304 hwv
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    exact weth9NonpayableRevert hcode hrev (weth9SelectorDispatchApprove hsel)
      (fun callargs _ => bodyReverts_nonPayable (by simp only [initState]; exact hwv))

end Benchmarks.WETH9
