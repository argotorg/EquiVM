import Benchmarks.WETH9.Routines

/-!
# WETH9 `allowance(address,address)` refinement

`allowance` is a public nested-mapping getter over slot 4.  The runtime peels its non-payable guard,
decodes two address arguments, hashes the nested slot (`keccak(guy ‖ keccak(owner ‖ 4))`), loads it,
and ABI-encodes the `uint256`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

namespace Benchmarks.WETH9

/-! ## ABI decode and source-level body -/

abbrev allowanceOwnerWord (I : ExecutionEnv) : UInt256 := calldataWord I.calldata 4
abbrev allowanceOwnerMaskedWord (I : ExecutionEnv) : UInt256 :=
  UInt256.land solcAddrMask (allowanceOwnerWord I)
abbrev allowanceGuyWord (I : ExecutionEnv) : UInt256 := calldataWord I.calldata 36
abbrev allowanceGuyMaskedWord (I : ExecutionEnv) : UInt256 :=
  UInt256.land solcAddrMask (allowanceGuyWord I)

abbrev allowanceOwnerValue (I : ExecutionEnv) : Value :=
  .address (AccountAddress.ofNat (allowanceOwnerWord I).toNat)
abbrev allowanceGuyValue (I : ExecutionEnv) : Value :=
  .address (AccountAddress.ofNat (allowanceGuyWord I).toNat)
abbrev allowanceOwnerKey (I : ExecutionEnv) : KeyValue :=
  .address (AccountAddress.ofNat (allowanceOwnerWord I).toNat)
abbrev allowanceGuyKey (I : ExecutionEnv) : KeyValue :=
  .address (AccountAddress.ofNat (allowanceGuyWord I).toNat)

abbrev allowanceStore (I : ExecutionEnv) : Store :=
  ((∅ : Store).insert "owner" (allowanceOwnerValue I)).insert "guy" (allowanceGuyValue I)

theorem allowanceStore_index_owner (I : ExecutionEnv) :
    (allowanceStore I)["owner"] = allowanceOwnerValue I := by
  unfold allowanceStore
  rw [Std.HashMap.getElem_insert]; simp

def allowanceStorageSlot (I : ExecutionEnv) : UInt256 :=
  allowanceSlot (allowanceOwnerKey I) (allowanceGuyKey I)

def allowanceWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  σ.find? I.codeOwner |>.option ⟨0⟩
    (fun acc => acc.storage.findD (allowanceStorageSlot I) ⟨0⟩)

abbrev allowanceEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "allowance",
    steps := [.mindex (allowanceOwnerKey I), .mindex (allowanceGuyKey I)] }

theorem allowanceStorageSlot_eq (I : ExecutionEnv) :
    allowanceStorageSlot I =
      solcMappingSlot (solcMappingSlot ⟨4⟩ (allowanceOwnerMaskedWord I)) (allowanceGuyMaskedWord I) := by
  unfold allowanceStorageSlot allowanceSlot allowanceOwnerSlot allowanceOwnerKey
    allowanceGuyKey allowanceOwnerMaskedWord allowanceGuyMaskedWord
  rw [keyValueToWord_address_ofNat_mask, keyValueToWord_address_ofNat_mask]
  rfl

theorem weth9SelectorDispatchAllowance {I : ExecutionEnv} (hsel : selIs I (weth9SelBytes 10)) :
    selectorDispatchMsg contract I.calldata = some allowanceTransition := by
  have hcd : I.calldata.extract 0 4 = weth9SelBytes 10 := (byteArray_eq_of_beq hsel).symm
  rw [selectorDispatchMsg_eq_dispatchList contract I.calldata]
  simp only [contract, dispatchList, selectorOf, hcd,
    weth9NameSelectorBytes, weth9ApproveSelectorBytes, weth9TotalSupplySelectorBytes,
    weth9TransferFromSelectorBytes, weth9WithdrawSelectorBytes, weth9DecimalsSelectorBytes,
    weth9BalanceOfSelectorBytes, weth9SymbolSelectorBytes, weth9TransferSelectorBytes,
    weth9DepositSelectorBytes, weth9AllowanceSelectorBytes]
  native_decide

theorem weth9Decode_allowance_ok {I : ExecutionEnv} (hsz68 : 68 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (allowanceTransition.params.map Param.name)
      (transitionSignature allowanceTransition).paramTypes I.calldata = some (allowanceStore I) := by
  show decodeCalldataWithMode config.abiDecodeMode ["owner", "guy"] [addr, addr] I.calldata = _
  simpa [allowanceStore, allowanceOwnerValue, allowanceGuyValue, allowanceOwnerWord,
    allowanceGuyWord, calldataWord]
    using decodeCalldata_legacyAddress_legacyAddress_ok
      (cd := I.calldata) (x := "owner") (y := "guy") hsz68

theorem weth9Decode_allowance_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 68) :
    decodeCalldataWithMode config.abiDecodeMode (allowanceTransition.params.map Param.name)
      (transitionSignature allowanceTransition).paramTypes I.calldata = none := by
  show decodeCalldataWithMode config.abiDecodeMode ["owner", "guy"] [addr, addr] I.calldata = none
  simpa using decodeCalldata_legacyAddress_legacyAddress_none_short
    (cd := I.calldata) (x := "owner") (y := "guy") hsz4 hshort

/-- The Solm `allowance(address,address)` body returns `allowance[owner][guy]`. -/
theorem weth9AllowanceBodyReturns (evm : EVM.State) (I : ExecutionEnv)
    (h : evm.executionEnv.weiValue = ⟨0⟩) :
    ExecTransitionBody config contract evm (allowanceStore I) allowanceTransition.body
      (.returned { contract := contract, locals := allowanceStore I } evm
        (some [(.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
            (allowanceStorageSlot I)).toNat))])) := by
  exact ExecFuncBody.execBlockRet <|
    (ABlock.start.requireStep (evalCallvalueEq_true h)).returns (by
      rw [evalExpr_storage_scalar_value
        (cfg := config)
        (solm := { contract := contract, locals := allowanceStore I })
        (slot := allowanceRef (.var "owner") (.var "guy"))
        (er := allowanceEvaledRef I)
        (t := .int uint256Int)
        (loc := wordLoc (allowanceStorageSlot I))
        (value := .int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
            (allowanceStorageSlot I)).toNat))
        (hbase := by simp [allowanceStore, allowanceRef])
        (her := by
          simp [evalStorageRef, evalStorageRefStep, allowanceRef, allowanceEvaledRef,
            allowanceOwnerValue, allowanceGuyValue, allowanceOwnerKey, allowanceGuyKey,
            valueToKey?, EvalResult.bind, EvalResult.ofOption, bind, pure, evalExpr?,
            allowanceStore_index_owner])
        (hty := by
          simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, allowanceOwnerKey,
            allowanceGuyKey, uint256St])
        (hloc := by rfl)
        (hload := by
          simpa [wordLoc, uint256Loc, uint256Int] using
            storageLocLoad_uint256 evm (allowanceStorageSlot I))])

/-! ## EVM trace -/

/-- allowance: peel guard, decode two addresses, jump to the nested getter (pc 1681). -/
theorem weth9AllowanceReachGetter {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = weth9Bytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (weth9SelBytes 10)) :
    ∃ k C, RD weth9Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1681⟩
      (allowanceGuyMaskedWord I :: allowanceOwnerMaskedWord I :: ⟨402⟩ :: [weth9SelWord I])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, h701⟩ := weth9ReachAllowance (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode (by omega) hsize hsel
  obtain ⟨_, _, h715⟩ := weth9GuardPeelOk (gt := ⟨713⟩) h701 hwv
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by jump_dest) (by native_decide) (by native_decide)
  have hlt : UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨0⟩ :=
    solcDecodeLenCheckOkUnsigned (by simpa using hsz68) hsize
  have h736 := h715.push2 ⟨402⟩ (by native_decide) (by simp)
    |>.push1 ⟨4⟩ (by native_decide) (by simp)
    |>.dup1 (by native_decide) (by simp)
    |>.calldatasize (by native_decide) (by simp)
    |>.sub (by native_decide) (by simp)
    |>.push1 ⟨64⟩ (by native_decide) (by simp)
    |>.dup2 (by native_decide) (by simp)
    |>.lt (by native_decide) (by simp)
    |>.iszero (by native_decide) (by simp)
    |>.push2 ⟨736⟩ (by native_decide) (by simp)
    |>.jumpiT (by native_decide) (by rw [hlt]; decide) (by jump_dest) (by simp)
  exact RD.solcTwoAddressExternalMaskAndJumpMasked (routine := ⟨1681⟩) h736
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
    (by simp only [List.length_singleton]; omega)

theorem weth9AllowanceX_ok {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = weth9Bytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (weth9SelBytes 10)) :
    RDret weth9Bytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (allowanceWord σ I)) := by
  obtain ⟨_, _, h1681⟩ := weth9AllowanceReachGetter (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hwv hsz68 hsize hsel
  obtain ⟨_, _, h402⟩ := weth9NestedMappingGetter (baseSlot := ⟨4⟩)
    (owner := allowanceOwnerMaskedWord I) (spender := allowanceGuyMaskedWord I)
    (ret := ⟨402⟩) (R := [weth9SelWord I]) h1681
    (by dsimp [solcNestedMappingGetterWf]; repeat' first | apply And.intro | native_decide)
    (by jump_dest) (by simp only [List.length_singleton]; omega)
  have hval : solcSlotWord σ I
      (solcMappingSlot (solcMappingSlot ⟨4⟩ (allowanceOwnerMaskedWord I))
        (allowanceGuyMaskedWord I)) = allowanceWord σ I := by
    unfold allowanceWord solcSlotWord
    rw [allowanceStorageSlot_eq]
  rw [← hval]
  exact RD.solcReturnWordFromMem h402
    (by dsimp [solcReturnWordFromMemWf]; repeat' first | apply And.intro | native_decide)
    (solcNestedMappingHashMem_mload64 ⟨4⟩ (allowanceOwnerMaskedWord I) (allowanceGuyMaskedWord I))
    rfl
    (solcScratchReturnMem_mload64 _
      (solcNestedMappingHashMem_size ⟨4⟩ (allowanceOwnerMaskedWord I) (allowanceGuyMaskedWord I))
      (solcNestedMappingHashMem_read64 ⟨4⟩ (allowanceOwnerMaskedWord I) (allowanceGuyMaskedWord I)))
    (solcScratchReturnMem_read128 _
      (solcNestedMappingHashMem_size ⟨4⟩ (allowanceOwnerMaskedWord I) (allowanceGuyMaskedWord I)))
    (by simp only [List.length_singleton]; omega)

/-! ## Refinement -/

theorem weth9AllowanceBodyCoreOk {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = weth9Bytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (weth9SelBytes 10))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (weth9SelBytes 10) (by native_decide) hsel
  have hdisp := weth9SelectorDispatchAllowance hsel
  by_cases hsz68 : 68 ≤ I.calldata.size
  · have hword : allowanceWord σ_evm I = allowanceWord σ_solm I :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner (allowanceStorageSlot I) ⟨0⟩
    have hbody :
        ExecTransitionBody config contract
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) (allowanceStore I)
          allowanceTransition.body
          (.returned { contract := contract, locals := allowanceStore I }
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
            (some [(.int (Int.ofNat (allowanceWord σ_solm I).toNat))])) := by
      simpa [allowanceWord, allowanceStorageSlot, initState, Solm.EVM.storageLoad,
        State.lookupAccount] using
        weth9AllowanceBodyReturns (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I
          (by simp only [initState]; exact hwv)
    exact weth9ReEquivExecTransport hcode
      (weth9AllowanceX_ok (g := Sat256.ofUInt256 g) hcode hwv hsz68 hsize hsel)
      hdisp (weth9Decode_allowance_ok hsz68) hbody (by rw [← hword]) hAccounts
      (returnEquiv_of_encode (by simpa [uint256] using uint256ReturnEncoding (allowanceWord σ_evm I)))
  · have hsz : I.calldata.size < 68 := by omega
    obtain ⟨_, _, h701⟩ := weth9ReachAllowance (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
      (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g) hcode hsz4 hsize hsel
    obtain ⟨_, _, h715⟩ := weth9GuardPeelOk (gt := ⟨713⟩) h701 hwv
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
      h715.push2 ⟨402⟩ (by native_decide) (by simp)
        |>.push1 ⟨4⟩ (by native_decide) (by simp)
        |>.dup1 (by native_decide) (by simp)
        |>.calldatasize (by native_decide) (by simp)
        |>.sub (by native_decide) (by simp)
        |>.push1 ⟨64⟩ (by native_decide) (by simp)
        |>.dup2 (by native_decide) (by simp)
        |>.lt (by native_decide) (by simp)
        |>.iszero (by native_decide) (by simp)
        |>.push2 ⟨736⟩ (by native_decide) (by simp)
        |>.jumpiNT (by native_decide) (by rw [hltShort]; decide) (by simp)
        |>.solcPush1Dup1Revert0 (by native_decide) (by native_decide) (by native_decide) (by simp)
    exact weth9ReEquivDecodeFailed hcode hrev hdisp (weth9Decode_allowance_none_short hsz4 hsz)

/-- `allowance(address,address)` body refines its Solm transition (both callvalue branches). -/
theorem weth9AllowanceBodyCore {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = weth9Bytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true)
    (hsel : selIs I (weth9SelBytes 10))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  by_cases hwv : I.weiValue = ⟨0⟩
  · exact weth9AllowanceBodyCoreOk hcode hsize hwv hsel hAccounts
  · have hsz4 : 4 ≤ I.calldata.size :=
      calldata_size_ge_of_selIs I (weth9SelBytes 10) (by native_decide) hsel
    obtain ⟨_, _, h701⟩ := weth9ReachAllowance (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
      (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g) hcode hsz4 hsize hsel
    have hrev := weth9GuardPeelRev (gt := ⟨713⟩) h701 hwv
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    exact weth9NonpayableRevert hcode hrev (weth9SelectorDispatchAllowance hsel)
      (fun callargs _ => bodyReverts_nonPayable (by simp only [initState]; exact hwv))

end Benchmarks.WETH9
