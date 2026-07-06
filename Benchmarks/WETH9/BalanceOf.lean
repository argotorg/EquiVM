import Benchmarks.WETH9.Routines

/-!
# WETH9 `balanceOf(address)` refinement

`balanceOf` is a public mapping getter over slot 3.  The runtime peels its own non-payable guard,
decodes one address argument, hashes the mapping slot, loads it, and ABI-encodes the `uint256`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 1000000

namespace Benchmarks.WETH9

/-! ## ABI decode and source-level body -/

abbrev balanceOfArgWord (I : ExecutionEnv) : UInt256 := calldataWord I.calldata 4

abbrev balanceOfArgMaskedWord (I : ExecutionEnv) : UInt256 :=
  UInt256.land solcAddrMask (balanceOfArgWord I)

abbrev balanceOfArgValue (I : ExecutionEnv) : Value :=
  .address (AccountAddress.ofNat (balanceOfArgWord I).toNat)

abbrev balanceOfArgKey (I : ExecutionEnv) : KeyValue :=
  .address (AccountAddress.ofNat (balanceOfArgWord I).toNat)

abbrev balanceOfStore (I : ExecutionEnv) : Store :=
  (∅ : Store).insert "owner" (balanceOfArgValue I)

def balanceOfStorageSlot (I : ExecutionEnv) : UInt256 :=
  balanceOfSlot (balanceOfArgKey I)

def balanceOfWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  σ.find? I.codeOwner |>.option ⟨0⟩
    (fun acc => acc.storage.findD (balanceOfStorageSlot I) ⟨0⟩)

theorem balanceOfStorageSlot_eq (I : ExecutionEnv) :
    balanceOfStorageSlot I = solcMappingSlot ⟨3⟩ (balanceOfArgMaskedWord I) := by
  unfold balanceOfStorageSlot balanceOfSlot balanceOfArgKey balanceOfArgMaskedWord
  rw [keyValueToWord_address_ofNat_mask]
  rfl

theorem weth9SelectorDispatchBalanceOf {I : ExecutionEnv} (hsel : selIs I (weth9SelBytes 6)) :
    selectorDispatchMsg contract I.calldata = some balanceOfTransition := by
  have hcd : I.calldata.extract 0 4 = weth9SelBytes 6 := (byteArray_eq_of_beq hsel).symm
  rw [selectorDispatchMsg_eq_dispatchList contract I.calldata]
  simp only [contract, dispatchList, selectorOf, hcd,
    weth9NameSelectorBytes, weth9ApproveSelectorBytes, weth9TotalSupplySelectorBytes,
    weth9TransferFromSelectorBytes, weth9WithdrawSelectorBytes, weth9DecimalsSelectorBytes,
    weth9BalanceOfSelectorBytes]
  native_decide

theorem weth9Decode_balanceOf_ok {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (balanceOfTransition.params.map Param.name)
      (transitionSignature balanceOfTransition).paramTypes I.calldata = some (balanceOfStore I) := by
  show decodeCalldataWithMode config.abiDecodeMode ["owner"] [addr] I.calldata = _
  simpa [balanceOfStore, balanceOfArgValue, balanceOfArgWord, calldataWord]
    using decodeCalldata_legacyAddress_ok (cd := I.calldata) (x := "owner") hsz36

theorem weth9Decode_balanceOf_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36) :
    decodeCalldataWithMode config.abiDecodeMode (balanceOfTransition.params.map Param.name)
      (transitionSignature balanceOfTransition).paramTypes I.calldata = none := by
  show decodeCalldataWithMode config.abiDecodeMode ["owner"] [addr] I.calldata = none
  simpa using decodeCalldata_legacyAddress_none_short (cd := I.calldata) (x := "owner") hsz4 hshort

/-- The Solm `balanceOf(address)` body returns `balanceOf[owner]`. -/
theorem weth9BalanceOfBodyReturns (evm : EVM.State) (I : ExecutionEnv)
    (h : evm.executionEnv.weiValue = ⟨0⟩) :
    ExecTransitionBody config contract evm (balanceOfStore I) balanceOfTransition.body
      (.returned { contract := contract, locals := balanceOfStore I } evm
        (some [(.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
            (balanceOfStorageSlot I)).toNat))])) := by
  exact ExecFuncBody.execBlockRet <|
    (ABlock.start.requireStep (evalCallvalueEq_true h)).returns (by
      rw [evalExpr_storage_scalar_value
        (cfg := config)
        (solm := { contract := contract, locals := balanceOfStore I })
        (slot := balanceOfRef (.var "owner"))
        (er := ({ base := "balanceOf", steps := [.mindex (balanceOfArgKey I)] } :
          EvaledStorageRef))
        (t := .int uint256Int)
        (loc := wordLoc (balanceOfStorageSlot I))
        (value := .int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
            (balanceOfStorageSlot I)).toNat))
        (hbase := by simp [balanceOfStore, balanceOfRef])
        (her := by
          simp [evalStorageRef, evalStorageRefStep, balanceOfRef, balanceOfStore,
            balanceOfArgValue, balanceOfArgKey, valueToKey?, EvalResult.bind,
            EvalResult.ofOption, bind, pure, evalExpr?])
        (hty := by
          simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, balanceOfArgKey,
            uint256St])
        (hloc := by rfl)
        (hload := by
          simpa [wordLoc, uint256Loc, uint256Int] using
            storageLocLoad_uint256 evm (balanceOfStorageSlot I))])

/-! ## EVM trace -/

/-- balanceOf: peel guard, decode the address, and jump to the mapping getter (pc 1553). -/
theorem weth9BalanceOfReachGetter {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = weth9Bytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (weth9SelBytes 6)) :
    ∃ k C, RD weth9Bytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1553⟩
      (UInt256.land solcAddrMask (calldataWord I.calldata 4) :: ⟨402⟩ :: [weth9SelWord I])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, h572⟩ := weth9ReachBalanceOf (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode (by omega) hsize hsel
  obtain ⟨_, _, h586⟩ := weth9GuardPeelOk (gt := ⟨584⟩) h572 hwv
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by jump_dest) (by native_decide) (by native_decide)
  have hlt : UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨0⟩ :=
    solcDecodeLenCheckOkUnsigned (by simpa using hsz36) hsize
  have h607 := h586.push2 ⟨402⟩ (by native_decide) (by simp)
    |>.push1 ⟨4⟩ (by native_decide) (by simp)
    |>.dup1 (by native_decide) (by simp)
    |>.calldatasize (by native_decide) (by simp)
    |>.sub (by native_decide) (by simp)
    |>.push1 ⟨32⟩ (by native_decide) (by simp)
    |>.dup2 (by native_decide) (by simp)
    |>.lt (by native_decide) (by simp)
    |>.iszero (by native_decide) (by simp)
    |>.push2 ⟨607⟩ (by native_decide) (by simp)
    |>.jumpiT (by native_decide) (by rw [hlt]; decide) (by jump_dest) (by simp)
  exact RD.solcOneAddressExternalMaskAndJumpMasked (routine := ⟨1553⟩) h607
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by simp only [List.length_singleton]; omega)

theorem weth9BalanceOfX_ok {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = weth9Bytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (weth9SelBytes 6)) :
    RDret weth9Bytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (balanceOfWord σ I)) := by
  obtain ⟨_, _, h1553⟩ := weth9BalanceOfReachGetter (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hwv hsz36 hsize hsel
  obtain ⟨_, _, h402⟩ := RD.solcSingleMappingGetter (baseSlot := ⟨3⟩)
    (key := balanceOfArgMaskedWord I) (ret := ⟨402⟩) (R := [weth9SelWord I]) h1553
    (by dsimp [solcSingleMappingGetterWf]; repeat' first | apply And.intro | native_decide)
    (by jump_dest) (by simp only [List.length_singleton]; omega)
  have hval : solcSlotWord σ I (solcMappingSlot ⟨3⟩ (balanceOfArgMaskedWord I)) = balanceOfWord σ I := by
    unfold balanceOfWord solcSlotWord
    rw [balanceOfStorageSlot_eq]
  rw [← hval]
  exact RD.solcReturnWordFromMem h402
    (by dsimp [solcReturnWordFromMemWf]; repeat' first | apply And.intro | native_decide)
    (solcMappingHashMem_mload64 ⟨3⟩ (balanceOfArgMaskedWord I))
    rfl
    (solcScratchReturnMem_mload64 (solcSlotWord σ I (solcMappingSlot ⟨3⟩ (balanceOfArgMaskedWord I)))
      (solcMappingHashMem_size ⟨3⟩ (balanceOfArgMaskedWord I))
      (solcMappingHashMem_read64 ⟨3⟩ (balanceOfArgMaskedWord I)))
    (solcScratchReturnMem_read128 (solcSlotWord σ I (solcMappingSlot ⟨3⟩ (balanceOfArgMaskedWord I)))
      (solcMappingHashMem_size ⟨3⟩ (balanceOfArgMaskedWord I)))
    (by simp only [List.length_singleton]; omega)

/-! ## Refinement -/

theorem weth9BalanceOfBodyCoreOk {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = weth9Bytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (weth9SelBytes 6))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (weth9SelBytes 6) (by native_decide) hsel
  have hdisp := weth9SelectorDispatchBalanceOf hsel
  by_cases hsz36 : 36 ≤ I.calldata.size
  · have hword : balanceOfWord σ_evm I = balanceOfWord σ_solm I :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner (balanceOfStorageSlot I) ⟨0⟩
    have hbody :
        ExecTransitionBody config contract
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) (balanceOfStore I)
          balanceOfTransition.body
          (.returned { contract := contract, locals := balanceOfStore I }
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
            (some [(.int (Int.ofNat (balanceOfWord σ_solm I).toNat))])) := by
      simpa [balanceOfWord, balanceOfStorageSlot, initState, Solm.EVM.storageLoad,
        State.lookupAccount] using
        weth9BalanceOfBodyReturns (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I
          (by simp only [initState]; exact hwv)
    exact weth9ReEquivExecTransport hcode
      (weth9BalanceOfX_ok (g := Sat256.ofUInt256 g) hcode hwv hsz36 hsize hsel)
      hdisp (weth9Decode_balanceOf_ok hsz36) hbody (by rw [← hword]) hAccounts
      (returnEquiv_of_encode (by simpa [uint256] using uint256ReturnEncoding (balanceOfWord σ_evm I)))
  · have hsz : I.calldata.size < 36 := by omega
    obtain ⟨_, _, h572⟩ := weth9ReachBalanceOf (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
      (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g) hcode hsz4 hsize hsel
    obtain ⟨_, _, h586⟩ := weth9GuardPeelOk (gt := ⟨584⟩) h572 hwv
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by jump_dest) (by native_decide) (by native_decide)
    have hltShort : UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨1⟩ := by
      apply ult_one
      rw [usub_ofNat_word_toNat (show (⟨4⟩ : UInt256).toNat ≤ I.calldata.size by simpa using hsz4)
        hsize]
      simp only [show (⟨32⟩ : UInt256).toNat = 32 from rfl,
        show (⟨4⟩ : UInt256).toNat = 4 from rfl]; omega
    have hrev : RDrev weth9Bytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) :=
      h586.push2 ⟨402⟩ (by native_decide) (by simp)
        |>.push1 ⟨4⟩ (by native_decide) (by simp)
        |>.dup1 (by native_decide) (by simp)
        |>.calldatasize (by native_decide) (by simp)
        |>.sub (by native_decide) (by simp)
        |>.push1 ⟨32⟩ (by native_decide) (by simp)
        |>.dup2 (by native_decide) (by simp)
        |>.lt (by native_decide) (by simp)
        |>.iszero (by native_decide) (by simp)
        |>.push2 ⟨607⟩ (by native_decide) (by simp)
        |>.jumpiNT (by native_decide) (by rw [hltShort]; decide) (by simp)
        |>.uniswapPush1Dup1Revert0 (by native_decide) (by native_decide) (by native_decide) (by simp)
    exact weth9ReEquivDecodeFailed hcode hrev hdisp (weth9Decode_balanceOf_none_short hsz4 hsz)

/-- `balanceOf(address)` body refines its Solm transition (handling both callvalue branches). -/
theorem weth9BalanceOfBodyCore {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = weth9Bytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true)
    (hsel : selIs I (weth9SelBytes 6))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  by_cases hwv : I.weiValue = ⟨0⟩
  · exact weth9BalanceOfBodyCoreOk hcode hsize hwv hsel hAccounts
  · have hsz4 : 4 ≤ I.calldata.size :=
      calldata_size_ge_of_selIs I (weth9SelBytes 6) (by native_decide) hsel
    obtain ⟨_, _, h572⟩ := weth9ReachBalanceOf (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
      (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g) hcode hsz4 hsize hsel
    have hrev := weth9GuardPeelRev (gt := ⟨584⟩) h572 hwv
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    exact weth9NonpayableRevert hcode hrev (weth9SelectorDispatchBalanceOf hsel)
      (fun callargs _ => bodyReverts_nonPayable (by simp only [initState]; exact hwv))

end Benchmarks.WETH9
