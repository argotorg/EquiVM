import Benchmarks.Dss.End.Common
import Benchmarks.Dss.End.FileUint

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace Benchmarks.Dss.End

attribute [local simp]
  endWardsSelectorBytes
  endVatSelectorBytes
  endCatSelectorBytes
  endDogSelectorBytes
  endVowSelectorBytes
  endPotSelectorBytes
  endSpotSelectorBytes
  endCureSelectorBytes
  endLiveSelectorBytes
  endWhenSelectorBytes
  endWaitSelectorBytes
  endDebtSelectorBytes
  endTagSelectorBytes
  endGapSelectorBytes
  endArtSelectorBytes
  endFixSelectorBytes
  endBagSelectorBytes
  endOutSelectorBytes
  endRelySelectorBytes
  endDenySelectorBytes
  endFileAddressSelectorBytes
  endFileUintSelectorBytes
  endCageSelectorBytes
  endCageIlkSelectorBytes
  endSnipSelectorBytes
  endSkipSelectorBytes
  endSkimSelectorBytes
  endFreeSelectorBytes
  endThawSelectorBytes
  endFlowSelectorBytes
  endPackSelectorBytes
  endCashSelectorBytes

attribute [local simp] storageStore_executionEnv storageStore_createdAccounts

/-! ## `cage()` -/

abbrev endCageConcreteSelector : ByteArray := selectorBytes 0x69 0x24 0x50 0x09

abbrev endCageEntryPc : UInt256 := ⟨798⟩
abbrev endCageReturnPc : UInt256 := ⟨562⟩
abbrev endCageAuthPc : UInt256 := ⟨5433⟩
abbrev endCageLivePc : UInt256 := ⟨5522⟩
abbrev endCageStorePc : UInt256 := ⟨5592⟩

abbrev endCageCallSelectorWord : UInt256 := ⟨0x69245009⟩
abbrev endCageCallSelectorShifted : UInt256 :=
  ⟨0x6924500900000000000000000000000000000000000000000000000000000000⟩
abbrev endCageCallOutPtr : UInt256 := ⟨128⟩
abbrev endCageCallInSize : UInt256 := ⟨4⟩
abbrev endCageCallOutSize : UInt256 := ⟨0⟩
abbrev endCageCallEndPtr : UInt256 := ⟨132⟩
abbrev endCageFinalLogTopic : UInt256 :=
  ⟨15846720854843032105251646702598932867924719938341352344186736728916659600346⟩

abbrev endCageCallTargetWord (slot : UInt256) (σ : AccountMap) (I : ExecutionEnv) :
    UInt256 :=
  endAddressReturnWord slot σ I

abbrev endCageCallTargetAddr (slot : UInt256) (σ : AccountMap) (I : ExecutionEnv) :
    AccountAddress :=
  AccountAddress.ofNat (endCageCallTargetWord slot σ I).toNat

noncomputable def endCageCallCalldataMem (mem : ByteArray) : ByteArray :=
  endCageCallSelectorShifted.toByteArray.write 0 mem endCageCallOutPtr.toNat 32

theorem endCageCallCalldataMem_size_auth (I : ExecutionEnv) :
    (endCageCallCalldataMem (endRelyAuthHashMem I)).size = 160 := by
  unfold endCageCallCalldataMem endCageCallOutPtr
  exact toByteArray_write32_size_of_ge (endRelyAuthHashMem I) endCageCallSelectorShifted
    128 96 160 (endRelyAuthHashMem_size I) (by omega)
    (by simpa using lt_usize 32 (by norm_num)) (by omega)

theorem endCageCallCalldataMem_read64_auth (I : ExecutionEnv) :
    (endCageCallCalldataMem (endRelyAuthHashMem I)).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold endCageCallCalldataMem endCageCallOutPtr
  change
    ByteArray.readWithPadding
        (endCageCallSelectorShifted.toByteArray.write 0 (endRelyAuthHashMem I) 128 32)
        64 32 =
      UInt256.toByteArray ⟨128⟩
  rw [toByteArray_write_read_below_of_gap endCageCallSelectorShifted
    (endRelyAuthHashMem I) 128 64
    (by rw [endRelyAuthHashMem_size I]) (by omega)
    (by rw [endRelyAuthHashMem_size I]; exact lt_usize _ (by norm_num))]
  exact endRelyAuthHashMem_read64 I

theorem endCage_byteArray_extract_empty_of_le (b : ByteArray) {i j : ℕ} (h : j ≤ i) :
    b.extract i j = ByteArray.empty := by
  apply ByteArray.ext
  rw [ByteArray.data_extract]
  exact Array.extract_eq_empty_of_le (le_trans (Nat.min_le_left j b.data.size) h)

theorem endCageCallCalldataMem_overwrite_auth (I : ExecutionEnv) :
    endCageCallSelectorShifted.toByteArray.write 0
        (endCageCallCalldataMem (endRelyAuthHashMem I)) endCageCallOutPtr.toNat 32 =
      endCageCallCalldataMem (endRelyAuthHashMem I) := by
  unfold endCageCallCalldataMem endCageCallOutPtr
  change
    endCageCallSelectorShifted.toByteArray.write 0
        (endCageCallSelectorShifted.toByteArray.write 0 (endRelyAuthHashMem I) 128 32)
        128 32 =
      endCageCallSelectorShifted.toByteArray.write 0 (endRelyAuthHashMem I) 128 32
  have hbaseSize : (endRelyAuthHashMem I).size = 96 := endRelyAuthHashMem_size I
  have hshape :
      endCageCallSelectorShifted.toByteArray.write 0 (endRelyAuthHashMem I) 128 32 =
        (endRelyAuthHashMem I) ++ ffi.ByteArray.zeroes 32 ++
          endCageCallSelectorShifted.toByteArray := by
    simpa [hbaseSize] using
      (toByteArray_write_eq endCageCallSelectorShifted (endRelyAuthHashMem I) 128
        (by rw [hbaseSize]; omega)
        (by rw [hbaseSize]; exact lt_usize 32 (by norm_num)))
  rw [hshape]
  rw [write32_eq endCageCallSelectorShifted.toByteArray
      ((endRelyAuthHashMem I) ++ ffi.ByteArray.zeroes 32 ++
        endCageCallSelectorShifted.toByteArray) 128
      (by rw [toByteArray_size])
      (by
        rw [ByteArray.size_append, ByteArray.size_append, hbaseSize, ByteArray_zeroes_size,
          toByteArray_size]
        omega)]
  have hzeroSize : (ffi.ByteArray.zeroes 32).size = 32 := by
    rw [ByteArray_zeroes_size]
  have hprefix :
      (((endRelyAuthHashMem I) ++ ffi.ByteArray.zeroes 32 ++
      endCageCallSelectorShifted.toByteArray).extract 0 128) =
        (endRelyAuthHashMem I) ++ ffi.ByteArray.zeroes 32 := by
    have hprefixSize :
        ((endRelyAuthHashMem I) ++ ffi.ByteArray.zeroes 32).size = 128 := by
      rw [ByteArray.size_append, hbaseSize, hzeroSize]
    rw [extract_append_left ((endRelyAuthHashMem I) ++ ffi.ByteArray.zeroes 32)
      endCageCallSelectorShifted.toByteArray 0 128
      (by rw [ByteArray.size_append, hbaseSize, hzeroSize])]
    simpa [hprefixSize] using
      byteArray_extract_self ((endRelyAuthHashMem I) ++ ffi.ByteArray.zeroes 32)
  have hword : endCageCallSelectorShifted.toByteArray.extract 0 32 =
      endCageCallSelectorShifted.toByteArray := by
    exact toByteArray_extract_all endCageCallSelectorShifted
  have htail :
      (((endRelyAuthHashMem I) ++ ffi.ByteArray.zeroes 32 ++
          endCageCallSelectorShifted.toByteArray).extract (128 + 32)
        ((endRelyAuthHashMem I) ++ ffi.ByteArray.zeroes 32 ++
          endCageCallSelectorShifted.toByteArray).size) =
        ByteArray.empty := by
    apply endCage_byteArray_extract_empty_of_le
    rw [ByteArray.size_append, ByteArray.size_append, hbaseSize, hzeroSize, toByteArray_size]
  rw [hprefix, hword, htail, ByteArray.append_empty]

theorem endCageCallCalldataMem_read128_4 {mem : ByteArray}
    (hgap : endCageCallOutPtr.toNat - mem.size < USize.size) :
    (endCageCallCalldataMem mem).readWithPadding endCageCallOutPtr.toNat
        endCageCallInSize.toNat =
      cageSelector := by
  unfold endCageCallCalldataMem endCageCallOutPtr endCageCallInSize
  change
    (endCageCallSelectorShifted.toByteArray.write 0 mem 128 32).readWithPadding 128 4 =
      cageSelector
  rw [toByteArray_write_read_window_of_gap endCageCallSelectorShifted mem 128 0 4
    (by omega) (by omega) (by omega) hgap]
  unfold endCageCallSelectorShifted cageSelector selectorBytes
  native_decide

theorem endCageCallEncode_eq {mem : ByteArray}
    (hgap : endCageCallOutPtr.toNat - mem.size < USize.size) :
    config.externalABI.encode? "cage" [] =
      some ((endCageCallCalldataMem mem).readWithPadding endCageCallOutPtr.toNat
        endCageCallInSize.toNat) := by
  rw [endCageCallCalldataMem_read128_4 hgap]
  simp [config, externalABI, cageSelector]

theorem endCageCallTargetWord_accountMapEquiv {σ τ : AccountMap} {I : ExecutionEnv}
    (slot : UInt256) (hAccounts : accountMapEquiv σ τ) :
    endCageCallTargetWord slot σ I = endCageCallTargetWord slot τ I := by
  simp [endCageCallTargetWord, endAddressReturnWord, endSlotWord, solcSlotWord,
    accountMapEquiv_storage_findD hAccounts I.codeOwner slot ⟨0⟩]

theorem endCageCallTargetCodeSize_ne_accountMapEquiv {σ τ : AccountMap} {I : ExecutionEnv}
    (slot : UInt256) (hAccounts : accountMapEquiv σ τ)
    (hne :
      Reasoning.Theory.extCodeSizeWord σ (endCageCallTargetWord slot σ I) ≠ ⟨0⟩) :
    Reasoning.Theory.extCodeSizeWord τ (endCageCallTargetWord slot τ I) ≠ ⟨0⟩ := by
  intro hzero
  apply hne
  have hsame :=
    Reasoning.Theory.extCodeSizeWord_accountMapEquiv hAccounts
      (endCageCallTargetWord slot σ I)
  have htarget : endCageCallTargetWord slot σ I = endCageCallTargetWord slot τ I :=
    endCageCallTargetWord_accountMapEquiv slot hAccounts
  rw [hsame, htarget]
  exact hzero

theorem endCageCallTargetCodeSize_zero_accountMapEquiv {σ τ : AccountMap} {I : ExecutionEnv}
    (slot : UInt256) (hAccounts : accountMapEquiv σ τ)
    (hzero :
      Reasoning.Theory.extCodeSizeWord σ (endCageCallTargetWord slot σ I) = ⟨0⟩) :
    Reasoning.Theory.extCodeSizeWord τ (endCageCallTargetWord slot τ I) = ⟨0⟩ := by
  have hsame :=
    Reasoning.Theory.extCodeSizeWord_accountMapEquiv hAccounts
      (endCageCallTargetWord slot σ I)
  have htarget : endCageCallTargetWord slot σ I = endCageCallTargetWord slot τ I :=
    endCageCallTargetWord_accountMapEquiv slot hAccounts
  rw [← htarget, ← hsame]
  exact hzero

theorem endCageCallTargetAddr_eq_ofUInt256 (slot : UInt256) (σ : AccountMap)
    (I : ExecutionEnv) :
    endCageCallTargetAddr slot σ I =
      AccountAddress.ofUInt256 (endCageCallTargetWord slot σ I) := by
  simpa [endCageCallTargetAddr] using
    (accountAddress_ofUInt256_eq_ofNat_toNat (endCageCallTargetWord slot σ I)).symm

theorem endCage_EVM_address_id (a : AccountAddress) : EVM.address a = a := by
  apply Fin.ext
  show ↑a % EVM.twoPow 160 = ↑a
  rw [Nat.mod_eq_of_lt]
  exact a.isLt

theorem endCageCallTargetAddr_source_eq_evmWord {σ τ : AccountMap} {I : ExecutionEnv}
    (slot : UInt256) (hAccounts : accountMapEquiv σ τ) :
    EVM.address (endCageCallTargetAddr slot τ I) =
      AccountAddress.ofUInt256 (endCageCallTargetWord slot σ I) := by
  have hword : endCageCallTargetWord slot σ I = endCageCallTargetWord slot τ I :=
    endCageCallTargetWord_accountMapEquiv slot hAccounts
  rw [hword]
  rw [endCageCallTargetAddr_eq_ofUInt256]
  exact endCage_EVM_address_id (AccountAddress.ofUInt256 (endCageCallTargetWord slot τ I))

theorem endCageCallEncode_auth (I : ExecutionEnv) :
    config.externalABI.encode? "cage" [] =
      some ((endCageCallCalldataMem (endRelyAuthHashMem I)).readWithPadding
        endCageCallOutPtr.toNat endCageCallInSize.toNat) := by
  exact endCageCallEncode_eq (mem := endRelyAuthHashMem I)
    (by rw [endRelyAuthHashMem_size I]; native_decide)

theorem endCageCallMadeBridge {evmE evmS : EVM.State} {slot : UInt256}
    {cA' : Batteries.RBSet AccountAddress compare} {σ' : AccountMap}
    {A' Ain : Substate} {z : Bool} {out : ByteArray} {g'' callGas : UInt256}
    (hdepth : evmE.executionEnv.depth ≠ 1024)
    (hΘ : (cA', σ', g'', A', z, out) =
        Ethereum.EVM.Θ evmE.executionEnv.blobVersionedHashes evmE.createdAccounts
          evmE.genesisBlockHeader evmE.blocks evmE.accountMap evmE.σ₀ Ain
          (AccountAddress.ofUInt256 (UInt256.ofNat evmE.executionEnv.codeOwner))
          evmE.executionEnv.sender
          (AccountAddress.ofUInt256
            (endCageCallTargetWord slot evmE.accountMap evmE.executionEnv))
          (toExecute evmE.accountMap
            (AccountAddress.ofUInt256
              (endCageCallTargetWord slot evmE.accountMap evmE.executionEnv)))
          callGas (UInt256.ofNat evmE.executionEnv.gasPrice) ⟨0⟩ ⟨0⟩
          ((endCageCallCalldataMem (endRelyAuthHashMem evmE.executionEnv)).readWithPadding
            endCageCallOutPtr.toNat endCageCallInSize.toNat)
          (evmE.executionEnv.depth + 1) evmE.executionEnv.header true)
    (hAccounts : accountMapEquiv evmE.accountMap evmS.accountMap)
    (hOriginalAccounts : evmE.σ₀ = evmS.σ₀)
    (hCreated : evmS.createdAccounts = evmE.createdAccounts)
    (hGenesis : evmS.genesisBlockHeader = evmE.genesisBlockHeader)
    (hBlocks : evmS.blocks = evmE.blocks)
    (hEnv : evmS.executionEnv = evmE.executionEnv) :
    ∃ (σ'_solm : AccountMap) (A'_solm : Substate),
      typedCallViaEVM config evmS
        (EVM.address (endCageCallTargetAddr slot evmS.accountMap evmS.executionEnv))
        "cage" 0 [] (z,
          { evmS with
              accountMap := σ'_solm
              substate := A'_solm
              createdAccounts := cA' },
          out) true ∧
      EVMStateEquiv
        { evmE with accountMap := σ', substate := A', createdAccounts := cA' }
        { evmS with
            accountMap := σ'_solm
            substate := A'_solm
            createdAccounts := cA' } := by
  have htgt :
      EVM.address (endCageCallTargetAddr slot evmS.accountMap evmS.executionEnv) =
        AccountAddress.ofUInt256
          (endCageCallTargetWord slot evmE.accountMap evmE.executionEnv) := by
    rw [hEnv]
    exact endCageCallTargetAddr_source_eq_evmWord slot hAccounts
  obtain ⟨σ'_solm, A'_solm, hcall, hAccountsPost, hSubstate⟩ :=
    endCallMade_accountMapEquiv_with_substate
      (cfg := config) (evm_evm := evmE) (evm_solm := evmS)
      (tgt := EVM.address (endCageCallTargetAddr slot evmS.accountMap evmS.executionEnv))
      (targetWord := endCageCallTargetWord slot evmE.accountMap evmE.executionEnv)
      (name := "cage") (args := [])
      (cA' := cA') (σ' := σ') (A' := A') (A_in := Ain)
      (z := z) (out := out) (g'' := g'') (callGas := callGas)
      (mem := endCageCallCalldataMem (endRelyAuthHashMem evmE.executionEnv))
      (inOff := endCageCallOutPtr) (inSize := endCageCallInSize)
      (callPerm := true)
      hdepth htgt (endCageCallEncode_auth evmE.executionEnv) hΘ hAccounts
      hOriginalAccounts hCreated hGenesis hBlocks hEnv
  refine ⟨σ'_solm, A'_solm, hcall, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · simp [hEnv]
  · rfl
  · exact hAccountsPost

theorem endCageCallNotMadeDepthLimit (evm : EVM.State) (slot : UInt256)
    (hdepth : evm.executionEnv.depth = 1024) :
    let tgt := EVM.address (endCageCallTargetAddr slot evm.accountMap evm.executionEnv)
    let A_call := (evm.addAccessedAccount tgt).substate
    typedCallViaEVM config evm tgt "cage" 0 []
      (false, { evm with substate := A_call }, ByteArray.empty) true := by
  intro tgt A_call
  simpa [tgt, A_call] using
    (callNotMade_depthLimit (cfg := config) (evm := evm)
      (tgt := EVM.address (endCageCallTargetAddr slot evm.accountMap evm.executionEnv))
      (name := "cage") (args := []) (callPerm := true)
      (endCageCallEncode_auth evm.executionEnv) hdepth)

theorem endCageCallTargetCode_zero_of_codeSize_zero {σ : AccountMap} {I : ExecutionEnv}
    (slot : UInt256)
    (hzero :
      Reasoning.Theory.extCodeSizeWord σ (endCageCallTargetWord slot σ I) = ⟨0⟩) :
    (UInt256.ofNat
      ((σ.find? (endCageCallTargetAddr slot σ I)).option 0 (fun acc => acc.code.size))).toNat =
        0 := by
  simpa [State.lookupAccount] using
    endUniswapExtCodeSizeWord_zero_lookup_code_zero
      (σ := σ) (target := endCageCallTargetWord slot σ I)
      (addr := endCageCallTargetAddr slot σ I)
      (endCageCallTargetAddr_eq_ofUInt256 slot σ I) hzero

theorem endCageCallTargetCode_pos_of_codeSize_ne {σ : AccountMap} {I : ExecutionEnv}
    (slot : UInt256)
    (hne :
      Reasoning.Theory.extCodeSizeWord σ (endCageCallTargetWord slot σ I) ≠ ⟨0⟩) :
    0 < (UInt256.ofNat
      ((σ.find? (endCageCallTargetAddr slot σ I)).option 0 (fun acc => acc.code.size))).toNat := by
  simpa [State.lookupAccount] using
    endUniswapExtCodeSizeWord_ne_zero_lookup_code_pos
      (σ := σ) (target := endCageCallTargetWord slot σ I)
      (addr := endCageCallTargetAddr slot σ I)
      (endCageCallTargetAddr_eq_ofUInt256 slot σ I) hne

theorem endCage_u256_div_one (w : UInt256) :
    UInt256.div w ⟨1⟩ = w := by
  apply u256_inj
  rw [udiv_toNat]
  exact Nat.div_one w.toNat

theorem endCage_solcAddrMask_idem_right (w : UInt256) :
    UInt256.land (UInt256.land w solcAddrMask) solcAddrMask =
      UInt256.land w solcAddrMask := by
  exact solcAddrMask_clean (solcAddrMask_result_canonical w)

theorem endCage_solcAddrMask_idem_left_left (w : UInt256) :
    UInt256.land solcAddrMask (UInt256.land solcAddrMask w) =
      UInt256.land solcAddrMask w := by
  rw [u256_land_comm solcAddrMask w]
  exact solcAddrMask_clean_left (solcAddrMask_result_canonical w)

theorem endDecode_cage {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (cageTransition.params.map Param.name)
      (transitionSignature cageTransition).paramTypes I.calldata = some ∅ := by
  show decodeCalldataWithMode config.abiDecodeMode [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz

theorem endDispatchCage {I : ExecutionEnv}
    (hsel : selIs I (selectorOf cageTransition)) :
    dispatchMsg contract I.calldata = some cageTransition := by
  have hsel' : selIs I endCageConcreteSelector := by
    simpa [endCageSelectorBytes, endCageConcreteSelector] using hsel
  have hcd : I.calldata.extract 0 4 = endCageConcreteSelector :=
    (byteArray_eq_of_beq hsel').symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some cageTransition
  unfold transitions
  simp [dispatchList, hcd, endCageConcreteSelector, selectorBytes]
  native_decide

theorem endReachCageBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = endBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I endCageConcreteSelector) :
    ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I)
        endCageEntryPc [endSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
  have hword : endSelWord I = ⟨0x69245009⟩ :=
    endSelWord_eq_of_beq I hsz 0x69 0x24 0x50 0x09 ⟨0x69245009⟩
      (by native_decide) (by simpa [selIs, endCageConcreteSelector, selectorBytes] using hsel)
  obtain ⟨_, _, hfirst⟩ :=
    endReachGroup294FirstArm (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize
      (by rw [hword]; native_decide)
      (by rw [hword]; native_decide)
      (by rw [hword]; native_decide)
  exact RD.dispatchTo endCageEntryPc 0 hfirst
    (fun j hj => endGroup294ArmsWellFormed j (by omega))
    (by intro j hj; omega)
    (by rw [hword]; native_decide)
    (by jump_dest)
    (by native_decide)
    (by simp)

theorem endCageX_entry {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hreach : ∃ k C, RD endBytecode I g
      (initState cA gh bl σ σ₀ g A I) endCageEntryPc [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD endBytecode I g
      (initState cA gh bl σ σ₀ g A I) endCageAuthPc [endCageReturnPc, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  simpa [endCageEntryPc, endCageReturnPc, endCageAuthPc] using
    RD.solcGetterThunk (code := endBytecode) (cA := cA) (gh := gh) (bl := bl)
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) (sel := sel)
      (entry := endCageEntryPc) (returnPc := endCageReturnPc) (routine := endCageAuthPc)
      hreach
      (by
        unfold solcGetterEntryWf
        repeat' first | apply And.intro | native_decide)
      (by jump_dest)

theorem endCageX_authorized {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (hauth : endRelyAuthWord σ I = ⟨1⟩)
    (h : RD endBytecode I g s0 endCageAuthPc [endCageReturnPc, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD endBytecode I g s0 endCageLivePc [endCageReturnPc, sel]
      (endRelyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have hauthSolc :
      solcSlotWord σ I (solcMappingSlot ⟨0⟩ (solcSourceWord I)) = ⟨1⟩ := by
    simpa [endRelyAuthWord, endSlotWord, endRelyAuthStorageSlot_eq_mapSlot_source I,
      mapSlot] using hauth
  simpa [endRelyAuthHashMem] using
    RD.endAuthCheckOk
      (code := endBytecode) (pc := endCageAuthPc) (okPc := endCageLivePc)
      (key := endCageReturnPc) (ret := sel) (R := [])
      h
      (by
        unfold endAuthCheckWf
        repeat' first | apply And.intro | native_decide)
      hauthSolc (by jump_dest) (by simp)

theorem endCageX_unauthorized {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (hauth : endRelyAuthWord σ I ≠ ⟨1⟩)
    (h : RD endBytecode I g s0 endCageAuthPc [endCageReturnPc, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev endBytecode g s0 := by
  have hauthSolc :
      solcSlotWord σ I (solcMappingSlot ⟨0⟩ (solcSourceWord I)) ≠ ⟨1⟩ := by
    simpa [endRelyAuthWord, endSlotWord, endRelyAuthStorageSlot_eq_mapSlot_source I,
      mapSlot] using hauth
  exact RD.endAuthCheckRevert
    (code := endBytecode) (pc := endCageAuthPc) (okPc := endCageLivePc)
    (key := endCageReturnPc) (ret := sel) (R := [])
    h
    (by
      unfold endAuthCheckWf
      repeat' first | apply And.intro | native_decide)
    (by
      unfold solcErrorStringRevertTailWf endAuthTailPc endNotAuthorizedRawWord
      repeat' first | apply And.intro | native_decide)
    hauthSolc (by simp)

theorem endCageX_live {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (hlive : endSlotWord ⟨8⟩ σ I = ⟨1⟩)
    (h : RD endBytecode I g s0 endCageLivePc [endCageReturnPc, sel]
      (endRelyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD endBytecode I g s0 endCageStorePc [endCageReturnPc, sel]
      (endRelyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have hliveSolc : solcSlotWord σ I ⟨8⟩ = ⟨1⟩ := by
    simpa [endSlotWord] using hlive
  exact RD.endLiveGuardOk
    (code := endBytecode) (pc := endCageLivePc) (okPc := endCageStorePc)
    (key := endCageReturnPc) (ret := sel) (R := [])
    h
    (by
      unfold endLiveGuardWf
      repeat' first | apply And.intro | native_decide)
    hliveSolc (by jump_dest) (by simp)

theorem endCageX_notLive {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (hlive : endSlotWord ⟨8⟩ σ I ≠ ⟨1⟩)
    (h : RD endBytecode I g s0 endCageLivePc [endCageReturnPc, sel]
      (endRelyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev endBytecode g s0 := by
  have hliveSolc : solcSlotWord σ I ⟨8⟩ ≠ ⟨1⟩ := by
    simpa [endSlotWord] using hlive
  exact RD.endLiveGuardRevert
    (code := endBytecode) (pc := endCageLivePc) (okPc := endCageStorePc)
    (key := endCageReturnPc) (ret := sel) (R := [])
    h
    (by
      unfold endLiveGuardWf
      repeat' first | apply And.intro | native_decide)
    (by
      unfold solcErrorStringRevertTailWf endLiveGuardTailPc endNotLiveRawWord
      repeat' first | apply And.intro | native_decide)
    hliveSolc (endRelyAuthHashMem_size I) (endRelyAuthHashMem_read64 I) (by simp)

theorem evalStorageRef_endCage_auth (evm : EVM.State) (I : ExecutionEnv)
    (hsrc : evm.executionEnv.source = I.source) :
    evalStorageRef config { contract := contract, locals := ∅ } evm
      (wardsRef sender) = .ok (endRelyAuthEvaledRef I) := by
  simp [evalStorageRef, evalStorageRefStep, wardsRef, sender, envValue, endRelyAuthEvaledRef,
    endRelyAuthKey, hsrc, valueToKey?, EvalResult.bind, EvalResult.ofOption, bind, pure,
    evalExpr?]

theorem evalExpr_endCage_auth_true (evm : EVM.State) (I : ExecutionEnv)
    (hsrc : evm.executionEnv.source = I.source)
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (endRelyAuthStorageSlot I) =
        ⟨1⟩) :
    evalExpr? config { contract := contract, locals := ∅ } evm
      (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) = .ok (.bool true) := by
  have hstorage :
      evalExpr? config { contract := contract, locals := ∅ } evm
        (.storage (wardsRef sender)) = .ok (.int 1) := by
    rw [evalExpr_storage_scalar_value
      (cfg := config)
      (solm := { contract := contract, locals := ∅ })
      (slot := wardsRef sender)
      (er := endRelyAuthEvaledRef I)
      (t := .int uint256Int)
      (loc := wordLoc (endRelyAuthStorageSlot I))
      (value := .int 1)
      (hbase := by simp [wardsRef])
      (her := evalStorageRef_endCage_auth evm I hsrc)
      (hty := by simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, uint256St])
      (hloc := by rfl)
      (hload := by
        simpa [hload] using endStorageLocLoad_uint256 evm (endRelyAuthStorageSlot I))]
  simp only [evalExpr?, hstorage, EvalResult.bind, bind, pure]
  rfl

theorem evalExpr_endCage_auth_false (evm : EVM.State) (I : ExecutionEnv)
    (hsrc : evm.executionEnv.source = I.source)
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (endRelyAuthStorageSlot I) ≠
        ⟨1⟩) :
    evalExpr? config { contract := contract, locals := ∅ } evm
      (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) = .ok (.bool false) := by
  have hstorage :
      evalExpr? config { contract := contract, locals := ∅ } evm
        (.storage (wardsRef sender)) =
          .ok (.int (Int.ofNat
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
              (endRelyAuthStorageSlot I)).toNat)) := by
    exact evalExpr_storage_scalar_value
      (cfg := config)
      (solm := { contract := contract, locals := ∅ })
      (slot := wardsRef sender)
      (er := endRelyAuthEvaledRef I)
      (t := .int uint256Int)
      (loc := wordLoc (endRelyAuthStorageSlot I))
      (hbase := by simp [wardsRef])
      (her := evalStorageRef_endCage_auth evm I hsrc)
      (hty := by simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, uint256St])
      (hloc := by rfl)
      (hload := by exact endStorageLocLoad_uint256 evm (endRelyAuthStorageSlot I))
  have hne :
      Value.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
            (endRelyAuthStorageSlot I)).toNat) ≠ Value.int 1 := by
    intro hbad
    rw [Value.int.injEq] at hbad
    apply hload
    exact endUInt256_toNat_eq_one (Int.ofNat.inj hbad)
  have hbeq :
      (Value.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
            (endRelyAuthStorageSlot I)).toNat) == Value.int 1) = false := by
    exact beq_eq_false_iff_ne.mpr hne
  simp only [evalExpr?, hstorage, EvalResult.bind, bind, pure]
  change evalBinaryOp? BinaryOp.eq
      (Value.int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
          (endRelyAuthStorageSlot I)).toNat))
      (Value.int 1) = .ok (.bool false)
  simp only [evalBinaryOp?]
  rw [hbeq]

theorem evalStorageRef_endCage_live (evm : EVM.State) :
    evalStorageRef config { contract := contract, locals := ∅ } evm
      liveRef = .ok endLiveEvaledRef := by
  simp [endLiveEvaledRef, liveRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind,
    pure, bind]

theorem evalExpr_endCage_live_true (evm : EVM.State)
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩ = ⟨1⟩) :
    evalExpr? config { contract := contract, locals := ∅ } evm
      (.binary .eq (.storage liveRef) (.intLit 1)) = .ok (.bool true) := by
  have hstorage :
      evalExpr? config { contract := contract, locals := ∅ } evm
        (.storage liveRef) = .ok (.int 1) := by
    rw [evalExpr_storage_scalar_value
      (cfg := config)
      (solm := { contract := contract, locals := ∅ })
      (slot := liveRef)
      (er := endLiveEvaledRef)
      (t := .int uint256Int)
      (loc := wordLoc ⟨8⟩)
      (value := .int 1)
      (hbase := by simp [liveRef])
      (her := evalStorageRef_endCage_live evm)
      (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
      (hloc := by rfl)
      (hload := by simpa [hload] using endStorageLocLoad_uint256 evm ⟨8⟩)]
  simp only [evalExpr?, hstorage, EvalResult.bind, bind, pure]
  rfl

theorem evalExpr_endCage_live_false (evm : EVM.State)
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩ ≠ ⟨1⟩) :
    evalExpr? config { contract := contract, locals := ∅ } evm
      (.binary .eq (.storage liveRef) (.intLit 1)) = .ok (.bool false) := by
  have hstorage :
      evalExpr? config { contract := contract, locals := ∅ } evm
        (.storage liveRef) =
          .ok (.int (Int.ofNat
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩).toNat)) := by
    exact evalExpr_storage_scalar_value
      (cfg := config)
      (solm := { contract := contract, locals := ∅ })
      (slot := liveRef)
      (er := endLiveEvaledRef)
      (t := .int uint256Int)
      (loc := wordLoc ⟨8⟩)
      (hbase := by simp [liveRef])
      (her := evalStorageRef_endCage_live evm)
      (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
      (hloc := by rfl)
      (hload := by exact endStorageLocLoad_uint256 evm ⟨8⟩)
  have hne :
      Value.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩).toNat) ≠
        Value.int 1 := by
    intro hbad
    rw [Value.int.injEq] at hbad
    apply hload
    exact endUInt256_toNat_eq_one (Int.ofNat.inj hbad)
  have hbeq :
      (Value.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩).toNat) ==
        Value.int 1) = false := by
    exact beq_eq_false_iff_ne.mpr hne
  simp only [evalExpr?, hstorage, EvalResult.bind, bind, pure]
  change evalBinaryOp? BinaryOp.eq
      (Value.int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩).toNat))
      (Value.int 1) = .ok (.bool false)
  simp only [evalBinaryOp?]
  rw [hbeq]

abbrev endCageTimestampWord (evm : EVM.State) : UInt256 :=
  UInt256.ofNat evm.executionEnv.header.timestamp

@[simp] theorem endCage_storageStore_σ₀
    (evm : EVM.State) (addr : AccountAddress) (slot val : UInt256) :
    (Solm.EVM.storageStore evm addr slot val).σ₀ = evm.σ₀ := by
  simp only [Solm.EVM.storageStore, State.lookupAccount]
  cases evm.accountMap.find? addr <;> simp [Option.option, State.setAccount]

@[simp] theorem endCage_storageStore_genesisBlockHeader
    (evm : EVM.State) (addr : AccountAddress) (slot val : UInt256) :
    (Solm.EVM.storageStore evm addr slot val).genesisBlockHeader =
      evm.genesisBlockHeader := by
  simp only [Solm.EVM.storageStore, State.lookupAccount]
  cases evm.accountMap.find? addr <;> simp [Option.option, State.setAccount]

@[simp] theorem endCage_storageStore_blocks
    (evm : EVM.State) (addr : AccountAddress) (slot val : UInt256) :
    (Solm.EVM.storageStore evm addr slot val).blocks = evm.blocks := by
  simp only [Solm.EVM.storageStore, State.lookupAccount]
  cases evm.accountMap.find? addr <;> simp [Option.option, State.setAccount]

def endCagePostStoresState (evm : EVM.State) : EVM.State :=
  Solm.EVM.storageStore
    (Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨8⟩ ⟨0⟩)
    evm.executionEnv.codeOwner ⟨9⟩ (endCageTimestampWord evm)

def endCageStoredAccountMap (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap I.codeOwner
    (sstoreAccountMap I.codeOwner σ ⟨8⟩ ⟨0⟩) ⟨9⟩ (UInt256.ofNat I.header.timestamp)

theorem evalExpr_endCage_timestamp (evm : EVM.State) :
    evalExpr? config { contract := contract, locals := ∅ } evm nowT =
      .ok (.int (Int.ofNat (endCageTimestampWord evm).toNat)) := by
  simp [nowT, evalExpr?, envValue, endCageTimestampWord, pure]

theorem endCageAssignLive (evm : EVM.State) :
    assignStorageRef? config { contract := contract, locals := ∅ } evm
      .storage liveRef (.int 0) =
        .ok ({ contract := contract, locals := ∅ },
          Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨8⟩ ⟨0⟩) := by
  apply assignStorageRef_storage_scalar
      (ty := uint256St)
      (er := endLiveEvaledRef)
      (loc := wordLoc ⟨8⟩)
      (hbase := by simp [liveRef])
      (her := evalStorageRef_endCage_live evm)
      (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
      (hloc := by rfl)
  simpa using endStorageLocStore_uint256 evm ⟨8⟩ ⟨0⟩

theorem endCageAssignWhen (evm : EVM.State) :
    assignStorageRef? config { contract := contract, locals := ∅ }
      (Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨8⟩ ⟨0⟩)
      .storage whenRef (.int (Int.ofNat (endCageTimestampWord evm).toNat)) =
        .ok ({ contract := contract, locals := ∅ }, endCagePostStoresState evm) := by
  apply assignStorageRef_storage_scalar
      (ty := uint256St)
      (er := ({ base := "when", steps := [] } : EvaledStorageRef))
      (loc := wordLoc ⟨9⟩)
      (hbase := by simp [whenRef])
      (her := by simp [whenRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind,
        pure, bind])
      (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
      (hloc := by rfl)
  simpa [endCagePostStoresState, endCageTimestampWord, storageStore_executionEnv] using
    endStorageLocStore_uint256
      (Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨8⟩ ⟨0⟩) ⟨9⟩
      (endCageTimestampWord evm)

theorem endCageX_storePrefix {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (hperm : I.perm = true)
    (h : RD endBytecode I g s0 endCageStorePc [endCageReturnPc, sel]
      (endRelyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD endBytecode I g s0 ⟨5604⟩ [⟨0⟩, endCageReturnPc, sel]
      (endRelyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty
      (cA, endCageStoredAccountMap σ I) k' C' := by
  have rdStoreLiveCursor := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨8⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  obtain ⟨_, _, rdAfterLive⟩ := rdStoreLiveCursor.sstore hperm (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdTimestamp := rdAfterLive.timestamp (by native_decide) (by evm_ov)
  have rdPush9 := rdTimestamp.push1 ⟨9⟩ (by native_decide) (by evm_ov)
  obtain ⟨_, _, rdAfterWhen⟩ := rdPush9.sstore hperm (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact ⟨_, _, by simpa [endCageStoredAccountMap] using rdAfterWhen⟩

theorem endCageX_vatExtcodesizeGuard {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256}
    (h : RD endBytecode I g s0 ⟨5604⟩ [⟨0⟩, endCageReturnPc, sel]
      (endRelyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD endBytecode I g s0 ⟨5655⟩
      (endCageCallTargetWord ⟨1⟩ σ I :: endCageCallTargetWord ⟨1⟩ σ I ::
        ⟨0⟩ :: endCageCallOutPtr :: endCageCallInSize :: endCageCallOutPtr ::
        endCageCallOutSize :: endCageCallEndPtr :: endCageCallSelectorWord ::
        endCageCallTargetWord ⟨1⟩ σ I :: endCageReturnPc :: sel :: [])
      (endCageCallCalldataMem (endRelyAuthHashMem I)) (UInt256.ofNat 5)
      ByteArray.empty (cA, σ) k' C' := by
  have hmload64Auth :
      (if (⟨64⟩ : UInt256).toNat ≥ (endRelyAuthHashMem I).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 3 * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian
            ((endRelyAuthHashMem I).readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [endRelyAuthHashMem_size I]; decide) (by decide)
      (endRelyAuthHashMem_read64 I)
  have hmload64Call :
      (if (⟨64⟩ : UInt256).toNat ≥
            (endCageCallCalldataMem (endRelyAuthHashMem I)).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 5 * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian
            ((endCageCallCalldataMem (endRelyAuthHashMem I)).readWithPadding
              (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [endCageCallCalldataMem_size_auth I]; decide) (by decide)
      (endCageCallCalldataMem_read64_auth I)
  have hselectorShift :
      UInt256.shiftLeft endCageCallSelectorWord ⟨224⟩ =
        endCageCallSelectorShifted := by
    native_decide
  have haddrMask :
      UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask := by
    native_decide
  obtain ⟨_, _, rd5607raw⟩ :=
    (evm_run h with [raw push1 ⟨1⟩ (by native_decide) (by evm_ov)]).sload
      (by native_decide) (by evm_ov)
  have rd5607 : ∃ k' C',
      RD endBytecode I g s0 ⟨5607⟩
        (endSlotWord ⟨1⟩ σ I :: ⟨0⟩ :: endCageReturnPc :: sel :: [])
        (endRelyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
    exact ⟨_, _, by simpa [endSlotWord, solcSlotWord] using rd5607raw⟩
  obtain ⟨_, _, rd5607⟩ := rd5607
  have rd5620pre := evm_run rd5607 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide)
      mem_cost hmload64Auth (by decide) (by evm_ov),
    raw push4 endCageCallSelectorWord (by native_decide) (by evm_ov),
    raw push1 ⟨224⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd5621 := rd5620pre.mstore 6
    (endCageCallCalldataMem (endRelyAuthHashMem I)) (UInt256.ofNat 5)
    (by native_decide) mem_cost
    (by rw [hselectorShift]; rfl) (by decide) (by evm_ov)
  have rd5655raw := evm_run rd5621 with [
    raw swap1 (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) (by native_decide)
      mem_cost hmload64Call (by decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw push4 endCageCallSelectorWord (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw push1 endCageCallInSize (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup5 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw swap4 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw dup8 (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov)]
  exact ⟨_, _, by
    simpa [endCageCallTargetWord, endCageCallOutPtr, endCageCallInSize,
      endCageCallOutSize, endCageCallEndPtr, endCageCallSelectorWord,
      endCageCallSelectorShifted, endAddressReturnWord, endSlotWord, solcSlotWord,
      haddrMask, solcAddrMask, u256_land_comm] using rd5655raw⟩

theorem endCageX_vatNoCode {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256}
    (h : RD endBytecode I g s0 ⟨5604⟩ [⟨0⟩, endCageReturnPc, sel]
      (endRelyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (endCageCallTargetWord ⟨1⟩ σ I) =
        ⟨0⟩) :
    RDrev endBytecode g s0 := by
  obtain ⟨_, _, rd5655⟩ := endCageX_vatExtcodesizeGuard h
  exact RD.solcExtcodesizeGuardMissing (pc := ⟨5655⟩) (okPc := ⟨5667⟩) rd5655
    hcodeSize
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by simp only [List.length_cons, List.length_nil]; omega)

theorem endCageX_vatCallReady {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256}
    (h : RD endBytecode I g s0 ⟨5604⟩ [⟨0⟩, endCageReturnPc, sel]
      (endRelyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (endCageCallTargetWord ⟨1⟩ σ I) ≠
        ⟨0⟩) :
    ∃ gasWord k' C', RD endBytecode I g s0 ⟨5670⟩
      (gasWord :: endCageCallTargetWord ⟨1⟩ σ I :: ⟨0⟩ :: endCageCallOutPtr ::
        endCageCallInSize :: endCageCallOutPtr :: endCageCallOutSize ::
        endCageCallEndPtr :: endCageCallSelectorWord ::
        endCageCallTargetWord ⟨1⟩ σ I :: endCageReturnPc :: sel :: [])
      (endCageCallCalldataMem (endRelyAuthHashMem I)) (UInt256.ofNat 5)
      ByteArray.empty (cA, σ) k' C' := by
  obtain ⟨_, _, rd5655⟩ := endCageX_vatExtcodesizeGuard h
  obtain ⟨gasWord, k', C', rd5670⟩ :=
    RD.solcExtcodesizeGuardOkGas (pc := ⟨5655⟩) (okPc := ⟨5667⟩) rd5655
      hcodeSize
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by jump_dest) (by native_decide)
      (by native_decide) (by native_decide) (by simp)
  exact ⟨gasWord, k', C', by simpa using rd5670⟩

theorem endCageX_vatPostCall {cA gh bl σ σ₀ A I} {g : UInt256}
    {sel gasWord : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (h : RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨5670⟩
      (gasWord :: endCageCallTargetWord ⟨1⟩ acc.2 I :: ⟨0⟩ :: endCageCallOutPtr ::
        endCageCallInSize :: endCageCallOutPtr :: endCageCallOutSize ::
        endCageCallEndPtr :: endCageCallSelectorWord ::
        endCageCallTargetWord ⟨1⟩ acc.2 I :: endCageReturnPc :: sel :: [])
      (endCageCallCalldataMem (endRelyAuthHashMem I)) (UInt256.ofNat 5)
      ByteArray.empty acc k C)
    (hdepth : I.depth.val < 1024) :
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap)
      (z : Bool) (out : ByteArray) (Ain : Substate) (callGas : UInt256) (k' C' : ℕ),
      (∃ (g'' : UInt256) (A' : Substate),
        (cA', σ', g'', A', z, out) =
          Ethereum.EVM.Θ I.blobVersionedHashes acc.1 gh bl acc.2 σ₀ Ain
          (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner)) I.sender
          (AccountAddress.ofUInt256 (endCageCallTargetWord ⟨1⟩ acc.2 I))
          (toExecute acc.2
            (AccountAddress.ofUInt256 (endCageCallTargetWord ⟨1⟩ acc.2 I)))
          callGas (UInt256.ofNat I.gasPrice) ⟨0⟩ ⟨0⟩
          ((endCageCallCalldataMem (endRelyAuthHashMem I)).readWithPadding
            endCageCallOutPtr.toNat endCageCallInSize.toNat)
          (I.depth + 1) I.header I.perm)
      ∧ RD endBytecode I (Sat256.ofUInt256 g)
          (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨5671⟩
          ((if z then ⟨1⟩ else ⟨0⟩) :: endCageCallEndPtr ::
            endCageCallSelectorWord :: endCageCallTargetWord ⟨1⟩ acc.2 I ::
            endCageReturnPc :: sel :: [])
          (endCageCallCalldataMem (endRelyAuthHashMem I)) (UInt256.ofNat 5)
          out (cA', σ') k' C'
      ∧ out.size < UInt256.size := by
  obtain ⟨cA', σ', z, out, Ain, callGas, k', C', hΘ, rd5671raw, hout⟩ :=
    RD.call h (by native_decide) hdepth (by evm_ov)
  refine ⟨cA', σ', z, out, Ain, callGas, k', C', ?_, ?_, hout⟩
  · cases acc
    simpa [initState] using hΘ
  · have hmin : (min endCageCallOutSize (UInt256.ofNat out.size)).toNat = 0 := by
      have hle : endCageCallOutSize ≤ UInt256.ofNat out.size := by
        show (0 : Nat) ≤ (UInt256.ofNat out.size).toNat
        exact Nat.zero_le _
      simp [endCageCallOutSize, min, hle]
    have haw :
        UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 5).toNat
          endCageCallOutPtr.toNat endCageCallInSize.toNat)
          endCageCallOutPtr.toNat endCageCallOutSize.toNat) = UInt256.ofNat 5 := by
      unfold endCageCallOutPtr endCageCallInSize endCageCallOutSize
      native_decide
    simpa [endCageCallOutPtr, endCageCallInSize, endCageCallOutSize,
      endCageCallEndPtr, hmin, byteArray_write_len_zero, haw] using rd5671raw

theorem endCageX_vatCallDepthLimit {cA gh bl σ σ₀ A I} {g : UInt256}
    {sel gasWord : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (h : RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨5670⟩
      (gasWord :: endCageCallTargetWord ⟨1⟩ acc.2 I :: ⟨0⟩ :: endCageCallOutPtr ::
        endCageCallInSize :: endCageCallOutPtr :: endCageCallOutSize ::
        endCageCallEndPtr :: endCageCallSelectorWord ::
        endCageCallTargetWord ⟨1⟩ acc.2 I :: endCageReturnPc :: sel :: [])
      (endCageCallCalldataMem (endRelyAuthHashMem I)) (UInt256.ofNat 5)
      ByteArray.empty acc k C)
    (hdepth : I.depth = 1024) :
    ∃ k' C', RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨5671⟩
      (⟨0⟩ :: endCageCallEndPtr :: endCageCallSelectorWord ::
        endCageCallTargetWord ⟨1⟩ acc.2 I :: endCageReturnPc :: sel :: [])
      (endCageCallCalldataMem (endRelyAuthHashMem I)) (UInt256.ofNat 5)
      ByteArray.empty acc k' C' := by
  obtain ⟨k', C', rd5671raw⟩ :=
    RD.callDepthLimit h (by native_decide) hdepth
      (by simp only [List.length_cons, List.length_nil]; omega)
  refine ⟨k', C', ?_⟩
  have hmin : (min endCageCallOutSize (UInt256.ofNat ByteArray.empty.size)).toNat = 0 := by
    decide
  have haw :
      UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 5).toNat
        endCageCallOutPtr.toNat endCageCallInSize.toNat)
        endCageCallOutPtr.toNat endCageCallOutSize.toNat) = UInt256.ofNat 5 := by
    unfold endCageCallOutPtr endCageCallInSize endCageCallOutSize
    native_decide
  cases acc
  simpa [endCageCallOutPtr, endCageCallInSize, endCageCallOutSize,
    endCageCallEndPtr, hmin, byteArray_write_len_zero, haw] using rd5671raw

theorem endCageX_vatCallFailed {cA cA' gh bl σ σCall σ' σ₀ A I} {g : UInt256}
    {sel : UInt256} {mem rdata : ByteArray} {k C : ℕ}
    (h : RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨5671⟩
      (⟨0⟩ :: endCageCallEndPtr :: endCageCallSelectorWord ::
        endCageCallTargetWord ⟨1⟩ σCall I :: endCageReturnPc :: sel :: [])
      mem (UInt256.ofNat 5) rdata (cA', σ') k C)
    (hrdataSize : rdata.size < UInt256.size) :
    RDrev endBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) := by
  exact RD.solcCallSuccessGuardMissing (pc := ⟨5671⟩) (okPc := ⟨5687⟩) h
    rfl
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    hrdataSize (by simp only [List.length_cons, List.length_nil]; omega)

theorem endCageX_vatCallSucceeded {cA gh bl σ σCall σ₀ A I} {g : UInt256}
    {sel : UInt256} {mem rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (h : RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨5671⟩
      (⟨1⟩ :: endCageCallEndPtr :: endCageCallSelectorWord ::
        endCageCallTargetWord ⟨1⟩ σCall I :: endCageReturnPc :: sel :: [])
      mem (UInt256.ofNat 5) rdata acc k C) :
    ∃ k' C', RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨5689⟩
      (endCageCallEndPtr :: endCageCallSelectorWord ::
        endCageCallTargetWord ⟨1⟩ σCall I :: endCageReturnPc :: sel :: [])
      mem (UInt256.ofNat 5) rdata acc k' C' := by
  exact RD.solcCallSuccessGuardOk (pc := ⟨5671⟩) (okPc := ⟨5687⟩) h
    (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by jump_dest) (by native_decide) (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem endCageX_vatCleanup {cA gh bl σ σCall σ₀ A I} {g : UInt256}
    {sel : UInt256} {mem rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (h : RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨5689⟩
      (endCageCallEndPtr :: endCageCallSelectorWord ::
        endCageCallTargetWord ⟨1⟩ σCall I :: endCageReturnPc :: sel :: [])
      mem (UInt256.ofNat 5) rdata acc k C) :
    ∃ k' C', RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨5692⟩
      [endCageReturnPc, sel] mem (UInt256.ofNat 5) rdata acc k' C' := by
  have rd5692 := evm_run h with [
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov)]
  exact ⟨_, _, by simpa using rd5692⟩

theorem endCageX_catExtcodesizeGuard {cA gh bl σ σ₀ A I} {g : UInt256}
    {sel : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (h : RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨5692⟩
      [endCageReturnPc, sel]
      (endCageCallCalldataMem (endRelyAuthHashMem I)) (UInt256.ofNat 5)
      rdata acc k C) :
    ∃ k' C', RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨5759⟩
      (endCageCallTargetWord ⟨2⟩ acc.2 I :: endCageCallTargetWord ⟨2⟩ acc.2 I ::
        ⟨0⟩ :: endCageCallOutPtr :: endCageCallInSize :: endCageCallOutPtr ::
        endCageCallOutSize :: endCageCallEndPtr :: endCageCallSelectorWord ::
        endCageCallTargetWord ⟨2⟩ acc.2 I :: endCageReturnPc :: sel :: [])
      (endCageCallCalldataMem (endRelyAuthHashMem I)) (UInt256.ofNat 5)
      rdata acc k' C' := by
  have hmload64Call :
      (if (⟨64⟩ : UInt256).toNat ≥
            (endCageCallCalldataMem (endRelyAuthHashMem I)).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 5 * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian
            ((endCageCallCalldataMem (endRelyAuthHashMem I)).readWithPadding
              (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [endCageCallCalldataMem_size_auth I]; decide) (by decide)
      (endCageCallCalldataMem_read64_auth I)
  have hselectorMask :
      UInt256.land endCageCallSelectorWord ⟨0xffffffff⟩ = endCageCallSelectorWord := by
    native_decide
  have hselectorMaskLeft :
      UInt256.land ⟨0xffffffff⟩ endCageCallSelectorWord = endCageCallSelectorWord := by
    native_decide
  have hselectorShift :
      UInt256.shiftLeft endCageCallSelectorWord ⟨224⟩ =
        endCageCallSelectorShifted := by
    native_decide
  have haddrMask :
      UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask := by
    native_decide
  have hexp0 : UInt256.exp (⟨256⟩ : UInt256) ⟨0⟩ = ⟨1⟩ := by
    native_decide
  have hendPtr : endCageCallInSize + endCageCallOutPtr = endCageCallEndPtr := by
    native_decide
  have hcomputedInSize :
      UInt256.sub (endCageCallInSize + endCageCallOutPtr) endCageCallOutPtr =
        endCageCallInSize := by
    native_decide
  have rd5697pre := evm_run h with [
    raw push1 ⟨2⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  obtain ⟨_, _, rd5698raw⟩ := rd5697pre.sload (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd5698 : ∃ k' C',
      RD endBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨5698⟩
        (endSlotWord ⟨2⟩ acc.2 I :: ⟨0⟩ :: endCageReturnPc :: sel :: [])
        (endCageCallCalldataMem (endRelyAuthHashMem I)) (UInt256.ofNat 5)
        rdata acc k' C' := by
    exact ⟨_, _, by
      cases acc
      simpa [endSlotWord, solcSlotWord] using rd5698raw⟩
  obtain ⟨_, _, rd5698⟩ := rd5698
  have rd5742pre := evm_run rd5698 with [
    raw swap1 (by native_decide) (by evm_ov),
    raw push2 ⟨256⟩ (by native_decide) (by evm_ov),
    raw exp (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw div (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw push4 endCageCallSelectorWord (by native_decide) (by evm_ov),
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) (by native_decide)
      mem_cost hmload64Call (by decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw push4 ⟨0xffffffff⟩ (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw push1 ⟨224⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd5743 := rd5742pre.mstore 0
    (endCageCallCalldataMem (endRelyAuthHashMem I)) (UInt256.ofNat 5)
    (by native_decide) mem_cost
    (by
      rw [hselectorMaskLeft, hselectorShift]
      simpa [endCageCallOutPtr] using endCageCallCalldataMem_overwrite_auth I)
    (by decide) (by evm_ov)
  have rd5759raw := evm_run rd5743 with [
    raw push1 endCageCallInSize (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) (by native_decide)
      mem_cost hmload64Call (by decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup8 (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov)]
  exact ⟨_, _, by
    cases acc
    simpa [endCageCallTargetWord, endCageCallOutPtr, endCageCallInSize,
      endCageCallOutSize, endCageCallEndPtr, endCageCallSelectorWord,
      endCageCallSelectorShifted, endAddressReturnWord, endSlotWord, solcSlotWord,
      haddrMask, hexp0, endCage_u256_div_one, endCage_solcAddrMask_idem_right,
      endCage_solcAddrMask_idem_left_left, hendPtr, hcomputedInSize, u256_land_comm]
      using rd5759raw⟩

theorem endCageX_catNoCode {cA gh bl σ σ₀ A I} {g : UInt256}
    {sel : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (h : RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨5692⟩
      [endCageReturnPc, sel]
      (endCageCallCalldataMem (endRelyAuthHashMem I)) (UInt256.ofNat 5)
      rdata acc k C)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord acc.2
        (endCageCallTargetWord ⟨2⟩ acc.2 I) = ⟨0⟩) :
    RDrev endBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) := by
  obtain ⟨_, _, rd5759⟩ := endCageX_catExtcodesizeGuard h
  exact RD.solcExtcodesizeGuardMissing (pc := ⟨5759⟩) (okPc := ⟨5771⟩) rd5759
    hcodeSize
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by simp only [List.length_cons, List.length_nil]; omega)

theorem endCageX_catCallReady {cA gh bl σ σ₀ A I} {g : UInt256}
    {sel : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (h : RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨5692⟩
      [endCageReturnPc, sel]
      (endCageCallCalldataMem (endRelyAuthHashMem I)) (UInt256.ofNat 5)
      rdata acc k C)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord acc.2
        (endCageCallTargetWord ⟨2⟩ acc.2 I) ≠ ⟨0⟩) :
    ∃ gasWord k' C', RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨5774⟩
      (gasWord :: endCageCallTargetWord ⟨2⟩ acc.2 I :: ⟨0⟩ ::
        endCageCallOutPtr :: endCageCallInSize :: endCageCallOutPtr ::
        endCageCallOutSize :: endCageCallEndPtr :: endCageCallSelectorWord ::
        endCageCallTargetWord ⟨2⟩ acc.2 I :: endCageReturnPc :: sel :: [])
      (endCageCallCalldataMem (endRelyAuthHashMem I)) (UInt256.ofNat 5)
      rdata acc k' C' := by
  obtain ⟨_, _, rd5759⟩ := endCageX_catExtcodesizeGuard h
  obtain ⟨gasWord, k', C', rd5774⟩ :=
    RD.solcExtcodesizeGuardOkGas (pc := ⟨5759⟩) (okPc := ⟨5771⟩) rd5759
      hcodeSize
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by jump_dest) (by native_decide)
      (by native_decide) (by native_decide) (by simp)
  exact ⟨gasWord, k', C', by simpa using rd5774⟩

theorem endCageX_catPostCall {cA gh bl σ σ₀ A I} {g : UInt256}
    {sel gasWord : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (h : RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨5774⟩
      (gasWord :: endCageCallTargetWord ⟨2⟩ acc.2 I :: ⟨0⟩ ::
        endCageCallOutPtr :: endCageCallInSize :: endCageCallOutPtr ::
        endCageCallOutSize :: endCageCallEndPtr :: endCageCallSelectorWord ::
        endCageCallTargetWord ⟨2⟩ acc.2 I :: endCageReturnPc :: sel :: [])
      (endCageCallCalldataMem (endRelyAuthHashMem I)) (UInt256.ofNat 5)
      rdata acc k C)
    (hdepth : I.depth.val < 1024) :
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap)
      (z : Bool) (out : ByteArray) (Ain : Substate) (callGas : UInt256) (k' C' : ℕ),
      (∃ (g'' : UInt256) (A' : Substate),
        (cA', σ', g'', A', z, out) =
          Ethereum.EVM.Θ I.blobVersionedHashes acc.1 gh bl acc.2 σ₀ Ain
            (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner)) I.sender
            (AccountAddress.ofUInt256 (endCageCallTargetWord ⟨2⟩ acc.2 I))
            (toExecute acc.2
              (AccountAddress.ofUInt256 (endCageCallTargetWord ⟨2⟩ acc.2 I)))
            callGas (UInt256.ofNat I.gasPrice) ⟨0⟩ ⟨0⟩
            ((endCageCallCalldataMem (endRelyAuthHashMem I)).readWithPadding
              endCageCallOutPtr.toNat endCageCallInSize.toNat)
            (I.depth + 1) I.header I.perm)
      ∧ RD endBytecode I (Sat256.ofUInt256 g)
          (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨5775⟩
          ((if z then ⟨1⟩ else ⟨0⟩) :: endCageCallEndPtr ::
            endCageCallSelectorWord :: endCageCallTargetWord ⟨2⟩ acc.2 I ::
            endCageReturnPc :: sel :: [])
          (endCageCallCalldataMem (endRelyAuthHashMem I)) (UInt256.ofNat 5)
          out (cA', σ') k' C'
      ∧ out.size < UInt256.size := by
  obtain ⟨cA', σ', z, out, Ain, callGas, k', C', hΘ, rd5775raw, hout⟩ :=
    RD.call h (by native_decide) hdepth (by evm_ov)
  refine ⟨cA', σ', z, out, Ain, callGas, k', C', ?_, ?_, hout⟩
  · cases acc
    simpa [initState] using hΘ
  · have hmin : (min endCageCallOutSize (UInt256.ofNat out.size)).toNat = 0 := by
      have hle : endCageCallOutSize ≤ UInt256.ofNat out.size := by
        show (0 : Nat) ≤ (UInt256.ofNat out.size).toNat
        exact Nat.zero_le _
      simp [endCageCallOutSize, min, hle]
    have haw :
        UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 5).toNat
          endCageCallOutPtr.toNat endCageCallInSize.toNat)
          endCageCallOutPtr.toNat endCageCallOutSize.toNat) = UInt256.ofNat 5 := by
      unfold endCageCallOutPtr endCageCallInSize endCageCallOutSize
      native_decide
    cases acc
    simpa [endCageCallOutPtr, endCageCallInSize, endCageCallOutSize,
      endCageCallEndPtr, hmin, byteArray_write_len_zero, haw] using rd5775raw

theorem endCageX_catCallDepthLimit {cA gh bl σ σ₀ A I} {g : UInt256}
    {sel gasWord : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (h : RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨5774⟩
      (gasWord :: endCageCallTargetWord ⟨2⟩ acc.2 I :: ⟨0⟩ ::
        endCageCallOutPtr :: endCageCallInSize :: endCageCallOutPtr ::
        endCageCallOutSize :: endCageCallEndPtr :: endCageCallSelectorWord ::
        endCageCallTargetWord ⟨2⟩ acc.2 I :: endCageReturnPc :: sel :: [])
      (endCageCallCalldataMem (endRelyAuthHashMem I)) (UInt256.ofNat 5)
      rdata acc k C)
    (hdepth : I.depth = 1024) :
    ∃ k' C', RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨5775⟩
      (⟨0⟩ :: endCageCallEndPtr :: endCageCallSelectorWord ::
        endCageCallTargetWord ⟨2⟩ acc.2 I :: endCageReturnPc :: sel :: [])
      (endCageCallCalldataMem (endRelyAuthHashMem I)) (UInt256.ofNat 5)
      ByteArray.empty acc k' C' := by
  obtain ⟨k', C', rd5775raw⟩ :=
    RD.callDepthLimit h (by native_decide) hdepth
      (by simp only [List.length_cons, List.length_nil]; omega)
  refine ⟨k', C', ?_⟩
  have hmin : (min endCageCallOutSize (UInt256.ofNat ByteArray.empty.size)).toNat = 0 := by
    decide
  have haw :
      UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 5).toNat
        endCageCallOutPtr.toNat endCageCallInSize.toNat)
        endCageCallOutPtr.toNat endCageCallOutSize.toNat) = UInt256.ofNat 5 := by
    unfold endCageCallOutPtr endCageCallInSize endCageCallOutSize
    native_decide
  cases acc
  simpa [endCageCallOutPtr, endCageCallInSize, endCageCallOutSize,
    endCageCallEndPtr, hmin, byteArray_write_len_zero, haw] using rd5775raw

theorem endCageX_catCallFailed {cA cA' gh bl σ σCall σ' σ₀ A I} {g : UInt256}
    {sel : UInt256} {mem rdata : ByteArray} {k C : ℕ}
    (h : RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨5775⟩
      (⟨0⟩ :: endCageCallEndPtr :: endCageCallSelectorWord ::
        endCageCallTargetWord ⟨2⟩ σCall I :: endCageReturnPc :: sel :: [])
      mem (UInt256.ofNat 5) rdata (cA', σ') k C)
    (hrdataSize : rdata.size < UInt256.size) :
    RDrev endBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) := by
  exact RD.solcCallSuccessGuardMissing (pc := ⟨5775⟩) (okPc := ⟨5791⟩) h
    rfl
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    hrdataSize (by simp only [List.length_cons, List.length_nil]; omega)

theorem endCageX_catCallSucceeded {cA gh bl σ σCall σ₀ A I} {g : UInt256}
    {sel : UInt256} {mem rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (h : RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨5775⟩
      (⟨1⟩ :: endCageCallEndPtr :: endCageCallSelectorWord ::
        endCageCallTargetWord ⟨2⟩ σCall I :: endCageReturnPc :: sel :: [])
      mem (UInt256.ofNat 5) rdata acc k C) :
    ∃ k' C', RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨5793⟩
      (endCageCallEndPtr :: endCageCallSelectorWord ::
        endCageCallTargetWord ⟨2⟩ σCall I :: endCageReturnPc :: sel :: [])
      mem (UInt256.ofNat 5) rdata acc k' C' := by
  exact RD.solcCallSuccessGuardOk (pc := ⟨5775⟩) (okPc := ⟨5791⟩) h
    (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by jump_dest) (by native_decide) (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem endCageX_catCleanup {cA gh bl σ σCall σ₀ A I} {g : UInt256}
    {sel : UInt256} {mem rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (h : RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨5793⟩
      (endCageCallEndPtr :: endCageCallSelectorWord ::
        endCageCallTargetWord ⟨2⟩ σCall I :: endCageReturnPc :: sel :: [])
      mem (UInt256.ofNat 5) rdata acc k C) :
    ∃ k' C', RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨5796⟩
      [endCageReturnPc, sel] mem (UInt256.ofNat 5) rdata acc k' C' := by
  have rd5796 := evm_run h with [
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov)]
  exact ⟨_, _, by simpa using rd5796⟩

theorem endCageX_dogExtcodesizeGuard {cA gh bl σ σ₀ A I} {g : UInt256}
    {sel : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (h : RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨5796⟩
      [endCageReturnPc, sel]
      (endCageCallCalldataMem (endRelyAuthHashMem I)) (UInt256.ofNat 5)
      rdata acc k C) :
    ∃ k' C', RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨5863⟩
      (endCageCallTargetWord ⟨3⟩ acc.2 I :: endCageCallTargetWord ⟨3⟩ acc.2 I ::
        ⟨0⟩ :: endCageCallOutPtr :: endCageCallInSize :: endCageCallOutPtr ::
        endCageCallOutSize :: endCageCallEndPtr :: endCageCallSelectorWord ::
        endCageCallTargetWord ⟨3⟩ acc.2 I :: endCageReturnPc :: sel :: [])
      (endCageCallCalldataMem (endRelyAuthHashMem I)) (UInt256.ofNat 5)
      rdata acc k' C' := by
  have hmload64Call :
      (if (⟨64⟩ : UInt256).toNat ≥
            (endCageCallCalldataMem (endRelyAuthHashMem I)).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 5 * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian
            ((endCageCallCalldataMem (endRelyAuthHashMem I)).readWithPadding
              (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [endCageCallCalldataMem_size_auth I]; decide) (by decide)
      (endCageCallCalldataMem_read64_auth I)
  have hselectorMaskLeft :
      UInt256.land ⟨0xffffffff⟩ endCageCallSelectorWord = endCageCallSelectorWord := by
    native_decide
  have hselectorShift :
      UInt256.shiftLeft endCageCallSelectorWord ⟨224⟩ =
        endCageCallSelectorShifted := by
    native_decide
  have haddrMask :
      UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask := by
    native_decide
  have hexp0 : UInt256.exp (⟨256⟩ : UInt256) ⟨0⟩ = ⟨1⟩ := by
    native_decide
  have hendPtr : endCageCallInSize + endCageCallOutPtr = endCageCallEndPtr := by
    native_decide
  have hcomputedInSize :
      UInt256.sub (endCageCallInSize + endCageCallOutPtr) endCageCallOutPtr =
        endCageCallInSize := by
    native_decide
  have rd5801pre := evm_run h with [
    raw push1 ⟨3⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  obtain ⟨_, _, rd5802raw⟩ := rd5801pre.sload (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd5802 : ∃ k' C',
      RD endBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨5802⟩
        (endSlotWord ⟨3⟩ acc.2 I :: ⟨0⟩ :: endCageReturnPc :: sel :: [])
        (endCageCallCalldataMem (endRelyAuthHashMem I)) (UInt256.ofNat 5)
        rdata acc k' C' := by
    exact ⟨_, _, by
      cases acc
      simpa [endSlotWord, solcSlotWord] using rd5802raw⟩
  obtain ⟨_, _, rd5802⟩ := rd5802
  have rd5846pre := evm_run rd5802 with [
    raw swap1 (by native_decide) (by evm_ov),
    raw push2 ⟨256⟩ (by native_decide) (by evm_ov),
    raw exp (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw div (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw push4 endCageCallSelectorWord (by native_decide) (by evm_ov),
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) (by native_decide)
      mem_cost hmload64Call (by decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw push4 ⟨0xffffffff⟩ (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw push1 ⟨224⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd5847 := rd5846pre.mstore 0
    (endCageCallCalldataMem (endRelyAuthHashMem I)) (UInt256.ofNat 5)
    (by native_decide) mem_cost
    (by
      rw [hselectorMaskLeft, hselectorShift]
      simpa [endCageCallOutPtr] using endCageCallCalldataMem_overwrite_auth I)
    (by decide) (by evm_ov)
  have rd5863raw := evm_run rd5847 with [
    raw push1 endCageCallInSize (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) (by native_decide)
      mem_cost hmload64Call (by decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup8 (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov)]
  exact ⟨_, _, by
    cases acc
    simpa [endCageCallTargetWord, endCageCallOutPtr, endCageCallInSize,
      endCageCallOutSize, endCageCallEndPtr, endCageCallSelectorWord,
      endCageCallSelectorShifted, endAddressReturnWord, endSlotWord, solcSlotWord,
      haddrMask, hexp0, endCage_u256_div_one, endCage_solcAddrMask_idem_right,
      endCage_solcAddrMask_idem_left_left, hendPtr, hcomputedInSize, u256_land_comm]
      using rd5863raw⟩

theorem endCageX_dogNoCode {cA gh bl σ σ₀ A I} {g : UInt256}
    {sel : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (h : RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨5796⟩
      [endCageReturnPc, sel]
      (endCageCallCalldataMem (endRelyAuthHashMem I)) (UInt256.ofNat 5)
      rdata acc k C)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord acc.2
        (endCageCallTargetWord ⟨3⟩ acc.2 I) = ⟨0⟩) :
    RDrev endBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) := by
  obtain ⟨_, _, rd5863⟩ := endCageX_dogExtcodesizeGuard h
  exact RD.solcExtcodesizeGuardMissing (pc := ⟨5863⟩) (okPc := ⟨5875⟩) rd5863
    hcodeSize
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by simp only [List.length_cons, List.length_nil]; omega)

theorem endCageX_dogCallReady {cA gh bl σ σ₀ A I} {g : UInt256}
    {sel : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (h : RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨5796⟩
      [endCageReturnPc, sel]
      (endCageCallCalldataMem (endRelyAuthHashMem I)) (UInt256.ofNat 5)
      rdata acc k C)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord acc.2
        (endCageCallTargetWord ⟨3⟩ acc.2 I) ≠ ⟨0⟩) :
    ∃ gasWord k' C', RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨5878⟩
      (gasWord :: endCageCallTargetWord ⟨3⟩ acc.2 I :: ⟨0⟩ ::
        endCageCallOutPtr :: endCageCallInSize :: endCageCallOutPtr ::
        endCageCallOutSize :: endCageCallEndPtr :: endCageCallSelectorWord ::
        endCageCallTargetWord ⟨3⟩ acc.2 I :: endCageReturnPc :: sel :: [])
      (endCageCallCalldataMem (endRelyAuthHashMem I)) (UInt256.ofNat 5)
      rdata acc k' C' := by
  obtain ⟨_, _, rd5863⟩ := endCageX_dogExtcodesizeGuard h
  obtain ⟨gasWord, k', C', rd5878⟩ :=
    RD.solcExtcodesizeGuardOkGas (pc := ⟨5863⟩) (okPc := ⟨5875⟩) rd5863
      hcodeSize
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by jump_dest) (by native_decide)
      (by native_decide) (by native_decide) (by simp)
  exact ⟨gasWord, k', C', by simpa using rd5878⟩

theorem endCageX_dogPostCall {cA gh bl σ σ₀ A I} {g : UInt256}
    {sel gasWord : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (h : RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨5878⟩
      (gasWord :: endCageCallTargetWord ⟨3⟩ acc.2 I :: ⟨0⟩ ::
        endCageCallOutPtr :: endCageCallInSize :: endCageCallOutPtr ::
        endCageCallOutSize :: endCageCallEndPtr :: endCageCallSelectorWord ::
        endCageCallTargetWord ⟨3⟩ acc.2 I :: endCageReturnPc :: sel :: [])
      (endCageCallCalldataMem (endRelyAuthHashMem I)) (UInt256.ofNat 5)
      rdata acc k C)
    (hdepth : I.depth.val < 1024) :
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap)
      (z : Bool) (out : ByteArray) (Ain : Substate) (callGas : UInt256) (k' C' : ℕ),
      (∃ (g'' : UInt256) (A' : Substate),
        (cA', σ', g'', A', z, out) =
          Ethereum.EVM.Θ I.blobVersionedHashes acc.1 gh bl acc.2 σ₀ Ain
            (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner)) I.sender
            (AccountAddress.ofUInt256 (endCageCallTargetWord ⟨3⟩ acc.2 I))
            (toExecute acc.2
              (AccountAddress.ofUInt256 (endCageCallTargetWord ⟨3⟩ acc.2 I)))
            callGas (UInt256.ofNat I.gasPrice) ⟨0⟩ ⟨0⟩
            ((endCageCallCalldataMem (endRelyAuthHashMem I)).readWithPadding
              endCageCallOutPtr.toNat endCageCallInSize.toNat)
            (I.depth + 1) I.header I.perm)
      ∧ RD endBytecode I (Sat256.ofUInt256 g)
          (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨5879⟩
          ((if z then ⟨1⟩ else ⟨0⟩) :: endCageCallEndPtr ::
            endCageCallSelectorWord :: endCageCallTargetWord ⟨3⟩ acc.2 I ::
            endCageReturnPc :: sel :: [])
          (endCageCallCalldataMem (endRelyAuthHashMem I)) (UInt256.ofNat 5)
          out (cA', σ') k' C'
      ∧ out.size < UInt256.size := by
  obtain ⟨cA', σ', z, out, Ain, callGas, k', C', hΘ, rd5879raw, hout⟩ :=
    RD.call h (by native_decide) hdepth (by evm_ov)
  refine ⟨cA', σ', z, out, Ain, callGas, k', C', ?_, ?_, hout⟩
  · cases acc
    simpa [initState] using hΘ
  · have hmin : (min endCageCallOutSize (UInt256.ofNat out.size)).toNat = 0 := by
      have hle : endCageCallOutSize ≤ UInt256.ofNat out.size := by
        show (0 : Nat) ≤ (UInt256.ofNat out.size).toNat
        exact Nat.zero_le _
      simp [endCageCallOutSize, min, hle]
    have haw :
        UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 5).toNat
          endCageCallOutPtr.toNat endCageCallInSize.toNat)
          endCageCallOutPtr.toNat endCageCallOutSize.toNat) = UInt256.ofNat 5 := by
      unfold endCageCallOutPtr endCageCallInSize endCageCallOutSize
      native_decide
    cases acc
    simpa [endCageCallOutPtr, endCageCallInSize, endCageCallOutSize,
      endCageCallEndPtr, hmin, byteArray_write_len_zero, haw] using rd5879raw

theorem endCageX_dogCallDepthLimit {cA gh bl σ σ₀ A I} {g : UInt256}
    {sel gasWord : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (h : RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨5878⟩
      (gasWord :: endCageCallTargetWord ⟨3⟩ acc.2 I :: ⟨0⟩ ::
        endCageCallOutPtr :: endCageCallInSize :: endCageCallOutPtr ::
        endCageCallOutSize :: endCageCallEndPtr :: endCageCallSelectorWord ::
        endCageCallTargetWord ⟨3⟩ acc.2 I :: endCageReturnPc :: sel :: [])
      (endCageCallCalldataMem (endRelyAuthHashMem I)) (UInt256.ofNat 5)
      rdata acc k C)
    (hdepth : I.depth = 1024) :
    ∃ k' C', RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨5879⟩
      (⟨0⟩ :: endCageCallEndPtr :: endCageCallSelectorWord ::
        endCageCallTargetWord ⟨3⟩ acc.2 I :: endCageReturnPc :: sel :: [])
      (endCageCallCalldataMem (endRelyAuthHashMem I)) (UInt256.ofNat 5)
      ByteArray.empty acc k' C' := by
  obtain ⟨k', C', rd5879raw⟩ :=
    RD.callDepthLimit h (by native_decide) hdepth
      (by simp only [List.length_cons, List.length_nil]; omega)
  refine ⟨k', C', ?_⟩
  have hmin : (min endCageCallOutSize (UInt256.ofNat ByteArray.empty.size)).toNat = 0 := by
    decide
  have haw :
      UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 5).toNat
        endCageCallOutPtr.toNat endCageCallInSize.toNat)
        endCageCallOutPtr.toNat endCageCallOutSize.toNat) = UInt256.ofNat 5 := by
    unfold endCageCallOutPtr endCageCallInSize endCageCallOutSize
    native_decide
  cases acc
  simpa [endCageCallOutPtr, endCageCallInSize, endCageCallOutSize,
    endCageCallEndPtr, hmin, byteArray_write_len_zero, haw] using rd5879raw

theorem endCageX_dogCallFailed {cA cA' gh bl σ σCall σ' σ₀ A I} {g : UInt256}
    {sel : UInt256} {mem rdata : ByteArray} {k C : ℕ}
    (h : RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨5879⟩
      (⟨0⟩ :: endCageCallEndPtr :: endCageCallSelectorWord ::
        endCageCallTargetWord ⟨3⟩ σCall I :: endCageReturnPc :: sel :: [])
      mem (UInt256.ofNat 5) rdata (cA', σ') k C)
    (hrdataSize : rdata.size < UInt256.size) :
    RDrev endBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) := by
  exact RD.solcCallSuccessGuardMissing (pc := ⟨5879⟩) (okPc := ⟨5895⟩) h
    rfl
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    hrdataSize (by simp only [List.length_cons, List.length_nil]; omega)

theorem endCageX_dogCallSucceeded {cA gh bl σ σCall σ₀ A I} {g : UInt256}
    {sel : UInt256} {mem rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (h : RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨5879⟩
      (⟨1⟩ :: endCageCallEndPtr :: endCageCallSelectorWord ::
        endCageCallTargetWord ⟨3⟩ σCall I :: endCageReturnPc :: sel :: [])
      mem (UInt256.ofNat 5) rdata acc k C) :
    ∃ k' C', RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨5897⟩
      (endCageCallEndPtr :: endCageCallSelectorWord ::
        endCageCallTargetWord ⟨3⟩ σCall I :: endCageReturnPc :: sel :: [])
      mem (UInt256.ofNat 5) rdata acc k' C' := by
  exact RD.solcCallSuccessGuardOk (pc := ⟨5879⟩) (okPc := ⟨5895⟩) h
    (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by jump_dest) (by native_decide) (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem endCageX_dogCleanup {cA gh bl σ σCall σ₀ A I} {g : UInt256}
    {sel : UInt256} {mem rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (h : RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨5897⟩
      (endCageCallEndPtr :: endCageCallSelectorWord ::
        endCageCallTargetWord ⟨3⟩ σCall I :: endCageReturnPc :: sel :: [])
      mem (UInt256.ofNat 5) rdata acc k C) :
    ∃ k' C', RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨5898⟩
      (endCageCallSelectorWord :: endCageCallTargetWord ⟨3⟩ σCall I ::
        endCageReturnPc :: sel :: [])
      mem (UInt256.ofNat 5) rdata acc k' C' := by
  have rd5898 := evm_run h with [
    raw pop (by native_decide) (by evm_ov)]
  exact ⟨_, _, by simpa using rd5898⟩

theorem endCageX_vowExtcodesizeGuard {cA gh bl σ σ₀ A I} {g : UInt256}
    {sel dogWord : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (h : RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨5898⟩
      (endCageCallSelectorWord :: dogWord :: endCageReturnPc :: sel :: [])
      (endCageCallCalldataMem (endRelyAuthHashMem I)) (UInt256.ofNat 5)
      rdata acc k C) :
    ∃ k' C', RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨5954⟩
      (endCageCallTargetWord ⟨4⟩ acc.2 I :: endCageCallTargetWord ⟨4⟩ acc.2 I ::
        ⟨0⟩ :: endCageCallOutPtr :: endCageCallInSize :: endCageCallOutPtr ::
        endCageCallOutSize :: endCageCallEndPtr :: endCageCallSelectorWord ::
        endCageCallTargetWord ⟨4⟩ acc.2 I :: endCageReturnPc :: sel :: [])
      (endCageCallCalldataMem (endRelyAuthHashMem I)) (UInt256.ofNat 5)
      rdata acc k' C' := by
  have hmload64Call :
      (if (⟨64⟩ : UInt256).toNat ≥
            (endCageCallCalldataMem (endRelyAuthHashMem I)).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 5 * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian
            ((endCageCallCalldataMem (endRelyAuthHashMem I)).readWithPadding
              (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [endCageCallCalldataMem_size_auth I]; decide) (by decide)
      (endCageCallCalldataMem_read64_auth I)
  have hselectorShift :
      UInt256.shiftLeft endCageCallSelectorWord ⟨224⟩ =
        endCageCallSelectorShifted := by
    native_decide
  have haddrMask :
      UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask := by
    native_decide
  have hendPtr : endCageCallInSize + endCageCallOutPtr = endCageCallEndPtr := by
    native_decide
  have hcomputedInSize :
      UInt256.sub (endCageCallInSize + endCageCallOutPtr) endCageCallOutPtr =
        endCageCallInSize := by
    native_decide
  have rd5901pre := evm_run h with [
    raw push1 ⟨4⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov)]
  obtain ⟨_, _, rd5902raw⟩ := rd5901pre.sload (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd5902 : ∃ k' C',
      RD endBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨5902⟩
        (endSlotWord ⟨4⟩ acc.2 I :: ⟨4⟩ :: endCageCallSelectorWord ::
          dogWord :: endCageReturnPc :: sel :: [])
        (endCageCallCalldataMem (endRelyAuthHashMem I)) (UInt256.ofNat 5)
        rdata acc k' C' := by
    exact ⟨_, _, by
      cases acc
      simpa [endSlotWord, solcSlotWord] using rd5902raw⟩
  obtain ⟨_, _, rd5902⟩ := rd5902
  have rd5915pre := evm_run rd5902 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) (by native_decide)
      mem_cost hmload64Call (by decide) (by evm_ov),
    raw push4 endCageCallSelectorWord (by native_decide) (by evm_ov),
    raw push1 ⟨224⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd5916 := rd5915pre.mstore 0
    (endCageCallCalldataMem (endRelyAuthHashMem I)) (UInt256.ofNat 5)
    (by native_decide) mem_cost
    (by
      rw [hselectorShift]
      simpa [endCageCallOutPtr] using endCageCallCalldataMem_overwrite_auth I)
    (by decide) (by evm_ov)
  have rd5954raw := evm_run rd5916 with [
    raw swap1 (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) (by native_decide)
      mem_cost hmload64Call (by decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw swap5 (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw push4 endCageCallSelectorWord (by native_decide) (by evm_ov),
    raw swap4 (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw dup8 (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov)]
  exact ⟨_, _, by
    cases acc
    simpa [endCageCallTargetWord, endCageCallOutPtr, endCageCallInSize,
      endCageCallOutSize, endCageCallEndPtr, endCageCallSelectorWord,
      endCageCallSelectorShifted, endAddressReturnWord, endSlotWord, solcSlotWord,
      haddrMask, solcAddrMask, hendPtr, hcomputedInSize, u256_land_comm]
      using rd5954raw⟩

theorem endCageX_vowNoCode {cA gh bl σ σ₀ A I} {g : UInt256}
    {sel dogWord : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (h : RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨5898⟩
      (endCageCallSelectorWord :: dogWord :: endCageReturnPc :: sel :: [])
      (endCageCallCalldataMem (endRelyAuthHashMem I)) (UInt256.ofNat 5)
      rdata acc k C)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord acc.2
        (endCageCallTargetWord ⟨4⟩ acc.2 I) = ⟨0⟩) :
    RDrev endBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) := by
  obtain ⟨_, _, rd5954⟩ := endCageX_vowExtcodesizeGuard h
  exact RD.solcExtcodesizeGuardMissing (pc := ⟨5954⟩) (okPc := ⟨5966⟩) rd5954
    hcodeSize
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by simp only [List.length_cons, List.length_nil]; omega)

theorem endCageX_vowCallReady {cA gh bl σ σ₀ A I} {g : UInt256}
    {sel dogWord : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (h : RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨5898⟩
      (endCageCallSelectorWord :: dogWord :: endCageReturnPc :: sel :: [])
      (endCageCallCalldataMem (endRelyAuthHashMem I)) (UInt256.ofNat 5)
      rdata acc k C)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord acc.2
        (endCageCallTargetWord ⟨4⟩ acc.2 I) ≠ ⟨0⟩) :
    ∃ gasWord k' C', RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨5969⟩
      (gasWord :: endCageCallTargetWord ⟨4⟩ acc.2 I :: ⟨0⟩ ::
        endCageCallOutPtr :: endCageCallInSize :: endCageCallOutPtr ::
        endCageCallOutSize :: endCageCallEndPtr :: endCageCallSelectorWord ::
        endCageCallTargetWord ⟨4⟩ acc.2 I :: endCageReturnPc :: sel :: [])
      (endCageCallCalldataMem (endRelyAuthHashMem I)) (UInt256.ofNat 5)
      rdata acc k' C' := by
  obtain ⟨_, _, rd5954⟩ := endCageX_vowExtcodesizeGuard h
  obtain ⟨gasWord, k', C', rd5969⟩ :=
    RD.solcExtcodesizeGuardOkGas (pc := ⟨5954⟩) (okPc := ⟨5966⟩) rd5954
      hcodeSize
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by jump_dest) (by native_decide)
      (by native_decide) (by native_decide) (by simp)
  exact ⟨gasWord, k', C', by simpa using rd5969⟩

theorem endCageX_vowPostCall {cA gh bl σ σ₀ A I} {g : UInt256}
    {sel gasWord : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (h : RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨5969⟩
      (gasWord :: endCageCallTargetWord ⟨4⟩ acc.2 I :: ⟨0⟩ ::
        endCageCallOutPtr :: endCageCallInSize :: endCageCallOutPtr ::
        endCageCallOutSize :: endCageCallEndPtr :: endCageCallSelectorWord ::
        endCageCallTargetWord ⟨4⟩ acc.2 I :: endCageReturnPc :: sel :: [])
      (endCageCallCalldataMem (endRelyAuthHashMem I)) (UInt256.ofNat 5)
      rdata acc k C)
    (hdepth : I.depth.val < 1024) :
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap)
      (z : Bool) (out : ByteArray) (Ain : Substate) (callGas : UInt256) (k' C' : ℕ),
      (∃ (g'' : UInt256) (A' : Substate),
        (cA', σ', g'', A', z, out) =
          Ethereum.EVM.Θ I.blobVersionedHashes acc.1 gh bl acc.2 σ₀ Ain
            (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner)) I.sender
            (AccountAddress.ofUInt256 (endCageCallTargetWord ⟨4⟩ acc.2 I))
            (toExecute acc.2
              (AccountAddress.ofUInt256 (endCageCallTargetWord ⟨4⟩ acc.2 I)))
            callGas (UInt256.ofNat I.gasPrice) ⟨0⟩ ⟨0⟩
            ((endCageCallCalldataMem (endRelyAuthHashMem I)).readWithPadding
              endCageCallOutPtr.toNat endCageCallInSize.toNat)
            (I.depth + 1) I.header I.perm)
      ∧ RD endBytecode I (Sat256.ofUInt256 g)
          (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨5970⟩
          ((if z then ⟨1⟩ else ⟨0⟩) :: endCageCallEndPtr ::
            endCageCallSelectorWord :: endCageCallTargetWord ⟨4⟩ acc.2 I ::
            endCageReturnPc :: sel :: [])
          (endCageCallCalldataMem (endRelyAuthHashMem I)) (UInt256.ofNat 5)
          out (cA', σ') k' C'
      ∧ out.size < UInt256.size := by
  obtain ⟨cA', σ', z, out, Ain, callGas, k', C', hΘ, rd5970raw, hout⟩ :=
    RD.call h (by native_decide) hdepth (by evm_ov)
  refine ⟨cA', σ', z, out, Ain, callGas, k', C', ?_, ?_, hout⟩
  · cases acc
    simpa [initState] using hΘ
  · have hmin : (min endCageCallOutSize (UInt256.ofNat out.size)).toNat = 0 := by
      have hle : endCageCallOutSize ≤ UInt256.ofNat out.size := by
        show (0 : Nat) ≤ (UInt256.ofNat out.size).toNat
        exact Nat.zero_le _
      simp [endCageCallOutSize, min, hle]
    have haw :
        UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 5).toNat
          endCageCallOutPtr.toNat endCageCallInSize.toNat)
          endCageCallOutPtr.toNat endCageCallOutSize.toNat) = UInt256.ofNat 5 := by
      unfold endCageCallOutPtr endCageCallInSize endCageCallOutSize
      native_decide
    cases acc
    simpa [endCageCallOutPtr, endCageCallInSize, endCageCallOutSize,
      endCageCallEndPtr, hmin, byteArray_write_len_zero, haw] using rd5970raw

theorem endCageX_vowCallDepthLimit {cA gh bl σ σ₀ A I} {g : UInt256}
    {sel gasWord : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (h : RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨5969⟩
      (gasWord :: endCageCallTargetWord ⟨4⟩ acc.2 I :: ⟨0⟩ ::
        endCageCallOutPtr :: endCageCallInSize :: endCageCallOutPtr ::
        endCageCallOutSize :: endCageCallEndPtr :: endCageCallSelectorWord ::
        endCageCallTargetWord ⟨4⟩ acc.2 I :: endCageReturnPc :: sel :: [])
      (endCageCallCalldataMem (endRelyAuthHashMem I)) (UInt256.ofNat 5)
      rdata acc k C)
    (hdepth : I.depth = 1024) :
    ∃ k' C', RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨5970⟩
      (⟨0⟩ :: endCageCallEndPtr :: endCageCallSelectorWord ::
        endCageCallTargetWord ⟨4⟩ acc.2 I :: endCageReturnPc :: sel :: [])
      (endCageCallCalldataMem (endRelyAuthHashMem I)) (UInt256.ofNat 5)
      ByteArray.empty acc k' C' := by
  obtain ⟨k', C', rd5970raw⟩ :=
    RD.callDepthLimit h (by native_decide) hdepth
      (by simp only [List.length_cons, List.length_nil]; omega)
  refine ⟨k', C', ?_⟩
  have hmin : (min endCageCallOutSize (UInt256.ofNat ByteArray.empty.size)).toNat = 0 := by
    decide
  have haw :
      UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 5).toNat
        endCageCallOutPtr.toNat endCageCallInSize.toNat)
        endCageCallOutPtr.toNat endCageCallOutSize.toNat) = UInt256.ofNat 5 := by
    unfold endCageCallOutPtr endCageCallInSize endCageCallOutSize
    native_decide
  cases acc
  simpa [endCageCallOutPtr, endCageCallInSize, endCageCallOutSize,
    endCageCallEndPtr, hmin, byteArray_write_len_zero, haw] using rd5970raw

theorem endCageX_vowCallFailed {cA cA' gh bl σ σCall σ' σ₀ A I} {g : UInt256}
    {sel : UInt256} {mem rdata : ByteArray} {k C : ℕ}
    (h : RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨5970⟩
      (⟨0⟩ :: endCageCallEndPtr :: endCageCallSelectorWord ::
        endCageCallTargetWord ⟨4⟩ σCall I :: endCageReturnPc :: sel :: [])
      mem (UInt256.ofNat 5) rdata (cA', σ') k C)
    (hrdataSize : rdata.size < UInt256.size) :
    RDrev endBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) := by
  exact RD.solcCallSuccessGuardMissing (pc := ⟨5970⟩) (okPc := ⟨5986⟩) h
    rfl
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    hrdataSize (by simp only [List.length_cons, List.length_nil]; omega)

theorem endCageX_vowCallSucceeded {cA gh bl σ σCall σ₀ A I} {g : UInt256}
    {sel : UInt256} {mem rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (h : RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨5970⟩
      (⟨1⟩ :: endCageCallEndPtr :: endCageCallSelectorWord ::
        endCageCallTargetWord ⟨4⟩ σCall I :: endCageReturnPc :: sel :: [])
      mem (UInt256.ofNat 5) rdata acc k C) :
    ∃ k' C', RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨5988⟩
      (endCageCallEndPtr :: endCageCallSelectorWord ::
        endCageCallTargetWord ⟨4⟩ σCall I :: endCageReturnPc :: sel :: [])
      mem (UInt256.ofNat 5) rdata acc k' C' := by
  exact RD.solcCallSuccessGuardOk (pc := ⟨5970⟩) (okPc := ⟨5986⟩) h
    (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by jump_dest) (by native_decide) (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem endCageX_vowCleanup {cA gh bl σ σCall σ₀ A I} {g : UInt256}
    {sel : UInt256} {mem rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (h : RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨5988⟩
      (endCageCallEndPtr :: endCageCallSelectorWord ::
        endCageCallTargetWord ⟨4⟩ σCall I :: endCageReturnPc :: sel :: [])
      mem (UInt256.ofNat 5) rdata acc k C) :
    ∃ k' C', RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨5991⟩
      [endCageReturnPc, sel] mem (UInt256.ofNat 5) rdata acc k' C' := by
  have rd5991 := evm_run h with [
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov)]
  exact ⟨_, _, by simpa using rd5991⟩

theorem endCageX_spotExtcodesizeGuard {cA gh bl σ σ₀ A I} {g : UInt256}
    {sel : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (h : RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨5991⟩
      [endCageReturnPc, sel]
      (endCageCallCalldataMem (endRelyAuthHashMem I)) (UInt256.ofNat 5)
      rdata acc k C) :
    ∃ k' C', RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨6058⟩
      (endCageCallTargetWord ⟨6⟩ acc.2 I :: endCageCallTargetWord ⟨6⟩ acc.2 I ::
        ⟨0⟩ :: endCageCallOutPtr :: endCageCallInSize :: endCageCallOutPtr ::
        endCageCallOutSize :: endCageCallEndPtr :: endCageCallSelectorWord ::
        endCageCallTargetWord ⟨6⟩ acc.2 I :: endCageReturnPc :: sel :: [])
      (endCageCallCalldataMem (endRelyAuthHashMem I)) (UInt256.ofNat 5)
      rdata acc k' C' := by
  have hmload64Call :
      (if (⟨64⟩ : UInt256).toNat ≥
            (endCageCallCalldataMem (endRelyAuthHashMem I)).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 5 * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian
            ((endCageCallCalldataMem (endRelyAuthHashMem I)).readWithPadding
              (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [endCageCallCalldataMem_size_auth I]; decide) (by decide)
      (endCageCallCalldataMem_read64_auth I)
  have hselectorMaskLeft :
      UInt256.land ⟨0xffffffff⟩ endCageCallSelectorWord = endCageCallSelectorWord := by
    native_decide
  have hselectorShift :
      UInt256.shiftLeft endCageCallSelectorWord ⟨224⟩ =
        endCageCallSelectorShifted := by
    native_decide
  have haddrMask :
      UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask := by
    native_decide
  have hexp0 : UInt256.exp (⟨256⟩ : UInt256) ⟨0⟩ = ⟨1⟩ := by
    native_decide
  have hendPtr : endCageCallInSize + endCageCallOutPtr = endCageCallEndPtr := by
    native_decide
  have hcomputedInSize :
      UInt256.sub (endCageCallInSize + endCageCallOutPtr) endCageCallOutPtr =
        endCageCallInSize := by
    native_decide
  have rd5996pre := evm_run h with [
    raw push1 ⟨6⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  obtain ⟨_, _, rd5997raw⟩ := rd5996pre.sload (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd5997 : ∃ k' C',
      RD endBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨5997⟩
        (endSlotWord ⟨6⟩ acc.2 I :: ⟨0⟩ :: endCageReturnPc :: sel :: [])
        (endCageCallCalldataMem (endRelyAuthHashMem I)) (UInt256.ofNat 5)
        rdata acc k' C' := by
    exact ⟨_, _, by
      cases acc
      simpa [endSlotWord, solcSlotWord] using rd5997raw⟩
  obtain ⟨_, _, rd5997⟩ := rd5997
  have rd6041pre := evm_run rd5997 with [
    raw swap1 (by native_decide) (by evm_ov),
    raw push2 ⟨256⟩ (by native_decide) (by evm_ov),
    raw exp (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw div (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw push4 endCageCallSelectorWord (by native_decide) (by evm_ov),
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) (by native_decide)
      mem_cost hmload64Call (by decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw push4 ⟨0xffffffff⟩ (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw push1 ⟨224⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd6042 := rd6041pre.mstore 0
    (endCageCallCalldataMem (endRelyAuthHashMem I)) (UInt256.ofNat 5)
    (by native_decide) mem_cost
    (by
      rw [hselectorMaskLeft, hselectorShift]
      simpa [endCageCallOutPtr] using endCageCallCalldataMem_overwrite_auth I)
    (by decide) (by evm_ov)
  have rd6058raw := evm_run rd6042 with [
    raw push1 endCageCallInSize (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) (by native_decide)
      mem_cost hmload64Call (by decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup8 (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov)]
  exact ⟨_, _, by
    cases acc
    simpa [endCageCallTargetWord, endCageCallOutPtr, endCageCallInSize,
      endCageCallOutSize, endCageCallEndPtr, endCageCallSelectorWord,
      endCageCallSelectorShifted, endAddressReturnWord, endSlotWord, solcSlotWord,
      haddrMask, hexp0, endCage_u256_div_one, endCage_solcAddrMask_idem_right,
      endCage_solcAddrMask_idem_left_left, hendPtr, hcomputedInSize, u256_land_comm]
      using rd6058raw⟩

theorem endCageX_spotNoCode {cA gh bl σ σ₀ A I} {g : UInt256}
    {sel : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (h : RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨5991⟩
      [endCageReturnPc, sel]
      (endCageCallCalldataMem (endRelyAuthHashMem I)) (UInt256.ofNat 5)
      rdata acc k C)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord acc.2
        (endCageCallTargetWord ⟨6⟩ acc.2 I) = ⟨0⟩) :
    RDrev endBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) := by
  obtain ⟨_, _, rd6058⟩ := endCageX_spotExtcodesizeGuard h
  exact RD.solcExtcodesizeGuardMissing (pc := ⟨6058⟩) (okPc := ⟨6070⟩) rd6058
    hcodeSize
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by simp only [List.length_cons, List.length_nil]; omega)

theorem endCageX_spotCallReady {cA gh bl σ σ₀ A I} {g : UInt256}
    {sel : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (h : RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨5991⟩
      [endCageReturnPc, sel]
      (endCageCallCalldataMem (endRelyAuthHashMem I)) (UInt256.ofNat 5)
      rdata acc k C)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord acc.2
        (endCageCallTargetWord ⟨6⟩ acc.2 I) ≠ ⟨0⟩) :
    ∃ gasWord k' C', RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨6073⟩
      (gasWord :: endCageCallTargetWord ⟨6⟩ acc.2 I :: ⟨0⟩ ::
        endCageCallOutPtr :: endCageCallInSize :: endCageCallOutPtr ::
        endCageCallOutSize :: endCageCallEndPtr :: endCageCallSelectorWord ::
        endCageCallTargetWord ⟨6⟩ acc.2 I :: endCageReturnPc :: sel :: [])
      (endCageCallCalldataMem (endRelyAuthHashMem I)) (UInt256.ofNat 5)
      rdata acc k' C' := by
  obtain ⟨_, _, rd6058⟩ := endCageX_spotExtcodesizeGuard h
  obtain ⟨gasWord, k', C', rd6073⟩ :=
    RD.solcExtcodesizeGuardOkGas (pc := ⟨6058⟩) (okPc := ⟨6070⟩) rd6058
      hcodeSize
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by jump_dest) (by native_decide)
      (by native_decide) (by native_decide) (by simp)
  exact ⟨gasWord, k', C', by simpa using rd6073⟩

theorem endCageX_spotPostCall {cA gh bl σ σ₀ A I} {g : UInt256}
    {sel gasWord : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (h : RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨6073⟩
      (gasWord :: endCageCallTargetWord ⟨6⟩ acc.2 I :: ⟨0⟩ ::
        endCageCallOutPtr :: endCageCallInSize :: endCageCallOutPtr ::
        endCageCallOutSize :: endCageCallEndPtr :: endCageCallSelectorWord ::
        endCageCallTargetWord ⟨6⟩ acc.2 I :: endCageReturnPc :: sel :: [])
      (endCageCallCalldataMem (endRelyAuthHashMem I)) (UInt256.ofNat 5)
      rdata acc k C)
    (hdepth : I.depth.val < 1024) :
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap)
      (z : Bool) (out : ByteArray) (Ain : Substate) (callGas : UInt256) (k' C' : ℕ),
      (∃ (g'' : UInt256) (A' : Substate),
        (cA', σ', g'', A', z, out) =
          Ethereum.EVM.Θ I.blobVersionedHashes acc.1 gh bl acc.2 σ₀ Ain
            (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner)) I.sender
            (AccountAddress.ofUInt256 (endCageCallTargetWord ⟨6⟩ acc.2 I))
            (toExecute acc.2
              (AccountAddress.ofUInt256 (endCageCallTargetWord ⟨6⟩ acc.2 I)))
            callGas (UInt256.ofNat I.gasPrice) ⟨0⟩ ⟨0⟩
            ((endCageCallCalldataMem (endRelyAuthHashMem I)).readWithPadding
              endCageCallOutPtr.toNat endCageCallInSize.toNat)
            (I.depth + 1) I.header I.perm)
      ∧ RD endBytecode I (Sat256.ofUInt256 g)
          (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨6074⟩
          ((if z then ⟨1⟩ else ⟨0⟩) :: endCageCallEndPtr ::
            endCageCallSelectorWord :: endCageCallTargetWord ⟨6⟩ acc.2 I ::
            endCageReturnPc :: sel :: [])
          (endCageCallCalldataMem (endRelyAuthHashMem I)) (UInt256.ofNat 5)
          out (cA', σ') k' C'
      ∧ out.size < UInt256.size := by
  obtain ⟨cA', σ', z, out, Ain, callGas, k', C', hΘ, rd6074raw, hout⟩ :=
    RD.call h (by native_decide) hdepth (by evm_ov)
  refine ⟨cA', σ', z, out, Ain, callGas, k', C', ?_, ?_, hout⟩
  · cases acc
    simpa [initState] using hΘ
  · have hmin : (min endCageCallOutSize (UInt256.ofNat out.size)).toNat = 0 := by
      have hle : endCageCallOutSize ≤ UInt256.ofNat out.size := by
        show (0 : Nat) ≤ (UInt256.ofNat out.size).toNat
        exact Nat.zero_le _
      simp [endCageCallOutSize, min, hle]
    have haw :
        UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 5).toNat
          endCageCallOutPtr.toNat endCageCallInSize.toNat)
          endCageCallOutPtr.toNat endCageCallOutSize.toNat) = UInt256.ofNat 5 := by
      unfold endCageCallOutPtr endCageCallInSize endCageCallOutSize
      native_decide
    cases acc
    simpa [endCageCallOutPtr, endCageCallInSize, endCageCallOutSize,
      endCageCallEndPtr, hmin, byteArray_write_len_zero, haw] using rd6074raw

theorem endCageX_spotCallDepthLimit {cA gh bl σ σ₀ A I} {g : UInt256}
    {sel gasWord : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (h : RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨6073⟩
      (gasWord :: endCageCallTargetWord ⟨6⟩ acc.2 I :: ⟨0⟩ ::
        endCageCallOutPtr :: endCageCallInSize :: endCageCallOutPtr ::
        endCageCallOutSize :: endCageCallEndPtr :: endCageCallSelectorWord ::
        endCageCallTargetWord ⟨6⟩ acc.2 I :: endCageReturnPc :: sel :: [])
      (endCageCallCalldataMem (endRelyAuthHashMem I)) (UInt256.ofNat 5)
      rdata acc k C)
    (hdepth : I.depth = 1024) :
    ∃ k' C', RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨6074⟩
      (⟨0⟩ :: endCageCallEndPtr :: endCageCallSelectorWord ::
        endCageCallTargetWord ⟨6⟩ acc.2 I :: endCageReturnPc :: sel :: [])
      (endCageCallCalldataMem (endRelyAuthHashMem I)) (UInt256.ofNat 5)
      ByteArray.empty acc k' C' := by
  obtain ⟨k', C', rd6074raw⟩ :=
    RD.callDepthLimit h (by native_decide) hdepth
      (by simp only [List.length_cons, List.length_nil]; omega)
  refine ⟨k', C', ?_⟩
  have hmin : (min endCageCallOutSize (UInt256.ofNat ByteArray.empty.size)).toNat = 0 := by
    decide
  have haw :
      UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 5).toNat
        endCageCallOutPtr.toNat endCageCallInSize.toNat)
        endCageCallOutPtr.toNat endCageCallOutSize.toNat) = UInt256.ofNat 5 := by
    unfold endCageCallOutPtr endCageCallInSize endCageCallOutSize
    native_decide
  cases acc
  simpa [endCageCallOutPtr, endCageCallInSize, endCageCallOutSize,
    endCageCallEndPtr, hmin, byteArray_write_len_zero, haw] using rd6074raw

theorem endCageX_spotCallFailed {cA cA' gh bl σ σCall σ' σ₀ A I} {g : UInt256}
    {sel : UInt256} {mem rdata : ByteArray} {k C : ℕ}
    (h : RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨6074⟩
      (⟨0⟩ :: endCageCallEndPtr :: endCageCallSelectorWord ::
        endCageCallTargetWord ⟨6⟩ σCall I :: endCageReturnPc :: sel :: [])
      mem (UInt256.ofNat 5) rdata (cA', σ') k C)
    (hrdataSize : rdata.size < UInt256.size) :
    RDrev endBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) := by
  exact RD.solcCallSuccessGuardMissing (pc := ⟨6074⟩) (okPc := ⟨6090⟩) h
    rfl
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    hrdataSize (by simp only [List.length_cons, List.length_nil]; omega)

theorem endCageX_spotCallSucceeded {cA gh bl σ σCall σ₀ A I} {g : UInt256}
    {sel : UInt256} {mem rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (h : RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨6074⟩
      (⟨1⟩ :: endCageCallEndPtr :: endCageCallSelectorWord ::
        endCageCallTargetWord ⟨6⟩ σCall I :: endCageReturnPc :: sel :: [])
      mem (UInt256.ofNat 5) rdata acc k C) :
    ∃ k' C', RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨6092⟩
      (endCageCallEndPtr :: endCageCallSelectorWord ::
        endCageCallTargetWord ⟨6⟩ σCall I :: endCageReturnPc :: sel :: [])
      mem (UInt256.ofNat 5) rdata acc k' C' := by
  exact RD.solcCallSuccessGuardOk (pc := ⟨6074⟩) (okPc := ⟨6090⟩) h
    (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by jump_dest) (by native_decide) (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem endCageX_spotCleanup {cA gh bl σ σCall σ₀ A I} {g : UInt256}
    {sel : UInt256} {mem rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (h : RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨6092⟩
      (endCageCallEndPtr :: endCageCallSelectorWord ::
        endCageCallTargetWord ⟨6⟩ σCall I :: endCageReturnPc :: sel :: [])
      mem (UInt256.ofNat 5) rdata acc k C) :
    ∃ k' C', RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨6095⟩
      [endCageReturnPc, sel] mem (UInt256.ofNat 5) rdata acc k' C' := by
  have rd6095 := evm_run h with [
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov)]
  exact ⟨_, _, by simpa using rd6095⟩

theorem endCageX_potExtcodesizeGuard {cA gh bl σ σ₀ A I} {g : UInt256}
    {sel : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (h : RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨6095⟩
      [endCageReturnPc, sel]
      (endCageCallCalldataMem (endRelyAuthHashMem I)) (UInt256.ofNat 5)
      rdata acc k C) :
    ∃ k' C', RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨6162⟩
      (endCageCallTargetWord ⟨5⟩ acc.2 I :: endCageCallTargetWord ⟨5⟩ acc.2 I ::
        ⟨0⟩ :: endCageCallOutPtr :: endCageCallInSize :: endCageCallOutPtr ::
        endCageCallOutSize :: endCageCallEndPtr :: endCageCallSelectorWord ::
        endCageCallTargetWord ⟨5⟩ acc.2 I :: endCageReturnPc :: sel :: [])
      (endCageCallCalldataMem (endRelyAuthHashMem I)) (UInt256.ofNat 5)
      rdata acc k' C' := by
  have hmload64Call :
      (if (⟨64⟩ : UInt256).toNat ≥
            (endCageCallCalldataMem (endRelyAuthHashMem I)).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 5 * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian
            ((endCageCallCalldataMem (endRelyAuthHashMem I)).readWithPadding
              (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [endCageCallCalldataMem_size_auth I]; decide) (by decide)
      (endCageCallCalldataMem_read64_auth I)
  have hselectorMaskLeft :
      UInt256.land ⟨0xffffffff⟩ endCageCallSelectorWord = endCageCallSelectorWord := by
    native_decide
  have hselectorShift :
      UInt256.shiftLeft endCageCallSelectorWord ⟨224⟩ =
        endCageCallSelectorShifted := by
    native_decide
  have haddrMask :
      UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask := by
    native_decide
  have hexp0 : UInt256.exp (⟨256⟩ : UInt256) ⟨0⟩ = ⟨1⟩ := by
    native_decide
  have hendPtr : endCageCallInSize + endCageCallOutPtr = endCageCallEndPtr := by
    native_decide
  have hcomputedInSize :
      UInt256.sub (endCageCallInSize + endCageCallOutPtr) endCageCallOutPtr =
        endCageCallInSize := by
    native_decide
  have rd6100pre := evm_run h with [
    raw push1 ⟨5⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  obtain ⟨_, _, rd6101raw⟩ := rd6100pre.sload (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd6101 : ∃ k' C',
      RD endBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨6101⟩
        (endSlotWord ⟨5⟩ acc.2 I :: ⟨0⟩ :: endCageReturnPc :: sel :: [])
        (endCageCallCalldataMem (endRelyAuthHashMem I)) (UInt256.ofNat 5)
        rdata acc k' C' := by
    exact ⟨_, _, by
      cases acc
      simpa [endSlotWord, solcSlotWord] using rd6101raw⟩
  obtain ⟨_, _, rd6101⟩ := rd6101
  have rd6145pre := evm_run rd6101 with [
    raw swap1 (by native_decide) (by evm_ov),
    raw push2 ⟨256⟩ (by native_decide) (by evm_ov),
    raw exp (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw div (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw push4 endCageCallSelectorWord (by native_decide) (by evm_ov),
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) (by native_decide)
      mem_cost hmload64Call (by decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw push4 ⟨0xffffffff⟩ (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw push1 ⟨224⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd6146 := rd6145pre.mstore 0
    (endCageCallCalldataMem (endRelyAuthHashMem I)) (UInt256.ofNat 5)
    (by native_decide) mem_cost
    (by
      rw [hselectorMaskLeft, hselectorShift]
      simpa [endCageCallOutPtr] using endCageCallCalldataMem_overwrite_auth I)
    (by decide) (by evm_ov)
  have rd6162raw := evm_run rd6146 with [
    raw push1 endCageCallInSize (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) (by native_decide)
      mem_cost hmload64Call (by decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup8 (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov)]
  exact ⟨_, _, by
    cases acc
    simpa [endCageCallTargetWord, endCageCallOutPtr, endCageCallInSize,
      endCageCallOutSize, endCageCallEndPtr, endCageCallSelectorWord,
      endCageCallSelectorShifted, endAddressReturnWord, endSlotWord, solcSlotWord,
      haddrMask, hexp0, endCage_u256_div_one, endCage_solcAddrMask_idem_right,
      endCage_solcAddrMask_idem_left_left, hendPtr, hcomputedInSize, u256_land_comm]
      using rd6162raw⟩

theorem endCageX_potNoCode {cA gh bl σ σ₀ A I} {g : UInt256}
    {sel : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (h : RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨6095⟩
      [endCageReturnPc, sel]
      (endCageCallCalldataMem (endRelyAuthHashMem I)) (UInt256.ofNat 5)
      rdata acc k C)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord acc.2
        (endCageCallTargetWord ⟨5⟩ acc.2 I) = ⟨0⟩) :
    RDrev endBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) := by
  obtain ⟨_, _, rd6162⟩ := endCageX_potExtcodesizeGuard h
  exact RD.solcExtcodesizeGuardMissing (pc := ⟨6162⟩) (okPc := ⟨6174⟩) rd6162
    hcodeSize
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by simp only [List.length_cons, List.length_nil]; omega)

theorem endCageX_potCallReady {cA gh bl σ σ₀ A I} {g : UInt256}
    {sel : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (h : RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨6095⟩
      [endCageReturnPc, sel]
      (endCageCallCalldataMem (endRelyAuthHashMem I)) (UInt256.ofNat 5)
      rdata acc k C)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord acc.2
        (endCageCallTargetWord ⟨5⟩ acc.2 I) ≠ ⟨0⟩) :
    ∃ gasWord k' C', RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨6177⟩
      (gasWord :: endCageCallTargetWord ⟨5⟩ acc.2 I :: ⟨0⟩ ::
        endCageCallOutPtr :: endCageCallInSize :: endCageCallOutPtr ::
        endCageCallOutSize :: endCageCallEndPtr :: endCageCallSelectorWord ::
        endCageCallTargetWord ⟨5⟩ acc.2 I :: endCageReturnPc :: sel :: [])
      (endCageCallCalldataMem (endRelyAuthHashMem I)) (UInt256.ofNat 5)
      rdata acc k' C' := by
  obtain ⟨_, _, rd6162⟩ := endCageX_potExtcodesizeGuard h
  obtain ⟨gasWord, k', C', rd6177⟩ :=
    RD.solcExtcodesizeGuardOkGas (pc := ⟨6162⟩) (okPc := ⟨6174⟩) rd6162
      hcodeSize
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by jump_dest) (by native_decide)
      (by native_decide) (by native_decide) (by simp)
  exact ⟨gasWord, k', C', by simpa using rd6177⟩

theorem endCageX_potPostCall {cA gh bl σ σ₀ A I} {g : UInt256}
    {sel gasWord : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (h : RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨6177⟩
      (gasWord :: endCageCallTargetWord ⟨5⟩ acc.2 I :: ⟨0⟩ ::
        endCageCallOutPtr :: endCageCallInSize :: endCageCallOutPtr ::
        endCageCallOutSize :: endCageCallEndPtr :: endCageCallSelectorWord ::
        endCageCallTargetWord ⟨5⟩ acc.2 I :: endCageReturnPc :: sel :: [])
      (endCageCallCalldataMem (endRelyAuthHashMem I)) (UInt256.ofNat 5)
      rdata acc k C)
    (hdepth : I.depth.val < 1024) :
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap)
      (z : Bool) (out : ByteArray) (Ain : Substate) (callGas : UInt256) (k' C' : ℕ),
      (∃ (g'' : UInt256) (A' : Substate),
        (cA', σ', g'', A', z, out) =
          Ethereum.EVM.Θ I.blobVersionedHashes acc.1 gh bl acc.2 σ₀ Ain
            (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner)) I.sender
            (AccountAddress.ofUInt256 (endCageCallTargetWord ⟨5⟩ acc.2 I))
            (toExecute acc.2
              (AccountAddress.ofUInt256 (endCageCallTargetWord ⟨5⟩ acc.2 I)))
            callGas (UInt256.ofNat I.gasPrice) ⟨0⟩ ⟨0⟩
            ((endCageCallCalldataMem (endRelyAuthHashMem I)).readWithPadding
              endCageCallOutPtr.toNat endCageCallInSize.toNat)
            (I.depth + 1) I.header I.perm)
      ∧ RD endBytecode I (Sat256.ofUInt256 g)
          (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨6178⟩
          ((if z then ⟨1⟩ else ⟨0⟩) :: endCageCallEndPtr ::
            endCageCallSelectorWord :: endCageCallTargetWord ⟨5⟩ acc.2 I ::
            endCageReturnPc :: sel :: [])
          (endCageCallCalldataMem (endRelyAuthHashMem I)) (UInt256.ofNat 5)
          out (cA', σ') k' C'
      ∧ out.size < UInt256.size := by
  obtain ⟨cA', σ', z, out, Ain, callGas, k', C', hΘ, rd6178raw, hout⟩ :=
    RD.call h (by native_decide) hdepth (by evm_ov)
  refine ⟨cA', σ', z, out, Ain, callGas, k', C', ?_, ?_, hout⟩
  · cases acc
    simpa [initState] using hΘ
  · have hmin : (min endCageCallOutSize (UInt256.ofNat out.size)).toNat = 0 := by
      have hle : endCageCallOutSize ≤ UInt256.ofNat out.size := by
        show (0 : Nat) ≤ (UInt256.ofNat out.size).toNat
        exact Nat.zero_le _
      simp [endCageCallOutSize, min, hle]
    have haw :
        UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 5).toNat
          endCageCallOutPtr.toNat endCageCallInSize.toNat)
          endCageCallOutPtr.toNat endCageCallOutSize.toNat) = UInt256.ofNat 5 := by
      unfold endCageCallOutPtr endCageCallInSize endCageCallOutSize
      native_decide
    cases acc
    simpa [endCageCallOutPtr, endCageCallInSize, endCageCallOutSize,
      endCageCallEndPtr, hmin, byteArray_write_len_zero, haw] using rd6178raw

theorem endCageX_potCallDepthLimit {cA gh bl σ σ₀ A I} {g : UInt256}
    {sel gasWord : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (h : RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨6177⟩
      (gasWord :: endCageCallTargetWord ⟨5⟩ acc.2 I :: ⟨0⟩ ::
        endCageCallOutPtr :: endCageCallInSize :: endCageCallOutPtr ::
        endCageCallOutSize :: endCageCallEndPtr :: endCageCallSelectorWord ::
        endCageCallTargetWord ⟨5⟩ acc.2 I :: endCageReturnPc :: sel :: [])
      (endCageCallCalldataMem (endRelyAuthHashMem I)) (UInt256.ofNat 5)
      rdata acc k C)
    (hdepth : I.depth = 1024) :
    ∃ k' C', RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨6178⟩
      (⟨0⟩ :: endCageCallEndPtr :: endCageCallSelectorWord ::
        endCageCallTargetWord ⟨5⟩ acc.2 I :: endCageReturnPc :: sel :: [])
      (endCageCallCalldataMem (endRelyAuthHashMem I)) (UInt256.ofNat 5)
      ByteArray.empty acc k' C' := by
  obtain ⟨k', C', rd6178raw⟩ :=
    RD.callDepthLimit h (by native_decide) hdepth
      (by simp only [List.length_cons, List.length_nil]; omega)
  refine ⟨k', C', ?_⟩
  have hmin : (min endCageCallOutSize (UInt256.ofNat ByteArray.empty.size)).toNat = 0 := by
    decide
  have haw :
      UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 5).toNat
        endCageCallOutPtr.toNat endCageCallInSize.toNat)
        endCageCallOutPtr.toNat endCageCallOutSize.toNat) = UInt256.ofNat 5 := by
    unfold endCageCallOutPtr endCageCallInSize endCageCallOutSize
    native_decide
  cases acc
  simpa [endCageCallOutPtr, endCageCallInSize, endCageCallOutSize,
    endCageCallEndPtr, hmin, byteArray_write_len_zero, haw] using rd6178raw

theorem endCageX_potCallFailed {cA cA' gh bl σ σCall σ' σ₀ A I} {g : UInt256}
    {sel : UInt256} {mem rdata : ByteArray} {k C : ℕ}
    (h : RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨6178⟩
      (⟨0⟩ :: endCageCallEndPtr :: endCageCallSelectorWord ::
        endCageCallTargetWord ⟨5⟩ σCall I :: endCageReturnPc :: sel :: [])
      mem (UInt256.ofNat 5) rdata (cA', σ') k C)
    (hrdataSize : rdata.size < UInt256.size) :
    RDrev endBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) := by
  exact RD.solcCallSuccessGuardMissing (pc := ⟨6178⟩) (okPc := ⟨6194⟩) h
    rfl
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    hrdataSize (by simp only [List.length_cons, List.length_nil]; omega)

theorem endCageX_potCallSucceeded {cA gh bl σ σCall σ₀ A I} {g : UInt256}
    {sel : UInt256} {mem rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (h : RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨6178⟩
      (⟨1⟩ :: endCageCallEndPtr :: endCageCallSelectorWord ::
        endCageCallTargetWord ⟨5⟩ σCall I :: endCageReturnPc :: sel :: [])
      mem (UInt256.ofNat 5) rdata acc k C) :
    ∃ k' C', RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨6196⟩
      (endCageCallEndPtr :: endCageCallSelectorWord ::
        endCageCallTargetWord ⟨5⟩ σCall I :: endCageReturnPc :: sel :: [])
      mem (UInt256.ofNat 5) rdata acc k' C' := by
  exact RD.solcCallSuccessGuardOk (pc := ⟨6178⟩) (okPc := ⟨6194⟩) h
    (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by jump_dest) (by native_decide) (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem endCageX_potCleanup {cA gh bl σ σCall σ₀ A I} {g : UInt256}
    {sel : UInt256} {mem rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (h : RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨6196⟩
      (endCageCallEndPtr :: endCageCallSelectorWord ::
        endCageCallTargetWord ⟨5⟩ σCall I :: endCageReturnPc :: sel :: [])
      mem (UInt256.ofNat 5) rdata acc k C) :
    ∃ k' C', RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨6199⟩
      [endCageReturnPc, sel] mem (UInt256.ofNat 5) rdata acc k' C' := by
  have rd6199 := evm_run h with [
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov)]
  exact ⟨_, _, by simpa using rd6199⟩

theorem endCageX_cureExtcodesizeGuard {cA gh bl σ σ₀ A I} {g : UInt256}
    {sel : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (h : RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨6199⟩
      [endCageReturnPc, sel]
      (endCageCallCalldataMem (endRelyAuthHashMem I)) (UInt256.ofNat 5)
      rdata acc k C) :
    ∃ k' C', RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨6266⟩
      (endCageCallTargetWord ⟨7⟩ acc.2 I :: endCageCallTargetWord ⟨7⟩ acc.2 I ::
        ⟨0⟩ :: endCageCallOutPtr :: endCageCallInSize :: endCageCallOutPtr ::
        endCageCallOutSize :: endCageCallEndPtr :: endCageCallSelectorWord ::
        endCageCallTargetWord ⟨7⟩ acc.2 I :: endCageReturnPc :: sel :: [])
      (endCageCallCalldataMem (endRelyAuthHashMem I)) (UInt256.ofNat 5)
      rdata acc k' C' := by
  have hmload64Call :
      (if (⟨64⟩ : UInt256).toNat ≥
            (endCageCallCalldataMem (endRelyAuthHashMem I)).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 5 * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian
            ((endCageCallCalldataMem (endRelyAuthHashMem I)).readWithPadding
              (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [endCageCallCalldataMem_size_auth I]; decide) (by decide)
      (endCageCallCalldataMem_read64_auth I)
  have hselectorMaskLeft :
      UInt256.land ⟨0xffffffff⟩ endCageCallSelectorWord = endCageCallSelectorWord := by
    native_decide
  have hselectorShift :
      UInt256.shiftLeft endCageCallSelectorWord ⟨224⟩ =
        endCageCallSelectorShifted := by
    native_decide
  have haddrMask :
      UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask := by
    native_decide
  have hexp0 : UInt256.exp (⟨256⟩ : UInt256) ⟨0⟩ = ⟨1⟩ := by
    native_decide
  have hendPtr : endCageCallInSize + endCageCallOutPtr = endCageCallEndPtr := by
    native_decide
  have hcomputedInSize :
      UInt256.sub (endCageCallInSize + endCageCallOutPtr) endCageCallOutPtr =
        endCageCallInSize := by
    native_decide
  have rd6204pre := evm_run h with [
    raw push1 ⟨7⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  obtain ⟨_, _, rd6205raw⟩ := rd6204pre.sload (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd6205 : ∃ k' C',
      RD endBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨6205⟩
        (endSlotWord ⟨7⟩ acc.2 I :: ⟨0⟩ :: endCageReturnPc :: sel :: [])
        (endCageCallCalldataMem (endRelyAuthHashMem I)) (UInt256.ofNat 5)
        rdata acc k' C' := by
    exact ⟨_, _, by
      cases acc
      simpa [endSlotWord, solcSlotWord] using rd6205raw⟩
  obtain ⟨_, _, rd6205⟩ := rd6205
  have rd6249pre := evm_run rd6205 with [
    raw swap1 (by native_decide) (by evm_ov),
    raw push2 ⟨256⟩ (by native_decide) (by evm_ov),
    raw exp (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw div (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw push4 endCageCallSelectorWord (by native_decide) (by evm_ov),
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) (by native_decide)
      mem_cost hmload64Call (by decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw push4 ⟨0xffffffff⟩ (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw push1 ⟨224⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd6250 := rd6249pre.mstore 0
    (endCageCallCalldataMem (endRelyAuthHashMem I)) (UInt256.ofNat 5)
    (by native_decide) mem_cost
    (by
      rw [hselectorMaskLeft, hselectorShift]
      simpa [endCageCallOutPtr] using endCageCallCalldataMem_overwrite_auth I)
    (by decide) (by evm_ov)
  have rd6266raw := evm_run rd6250 with [
    raw push1 endCageCallInSize (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) (by native_decide)
      mem_cost hmload64Call (by decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup8 (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov)]
  exact ⟨_, _, by
    cases acc
    simpa [endCageCallTargetWord, endCageCallOutPtr, endCageCallInSize,
      endCageCallOutSize, endCageCallEndPtr, endCageCallSelectorWord,
      endCageCallSelectorShifted, endAddressReturnWord, endSlotWord, solcSlotWord,
      haddrMask, hexp0, endCage_u256_div_one, endCage_solcAddrMask_idem_right,
      endCage_solcAddrMask_idem_left_left, hendPtr, hcomputedInSize, u256_land_comm]
      using rd6266raw⟩

theorem endCageX_cureNoCode {cA gh bl σ σ₀ A I} {g : UInt256}
    {sel : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (h : RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨6199⟩
      [endCageReturnPc, sel]
      (endCageCallCalldataMem (endRelyAuthHashMem I)) (UInt256.ofNat 5)
      rdata acc k C)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord acc.2
        (endCageCallTargetWord ⟨7⟩ acc.2 I) = ⟨0⟩) :
    RDrev endBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) := by
  obtain ⟨_, _, rd6266⟩ := endCageX_cureExtcodesizeGuard h
  exact RD.solcExtcodesizeGuardMissing (pc := ⟨6266⟩) (okPc := ⟨6278⟩) rd6266
    hcodeSize
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by simp only [List.length_cons, List.length_nil]; omega)

theorem endCageX_cureCallReady {cA gh bl σ σ₀ A I} {g : UInt256}
    {sel : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (h : RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨6199⟩
      [endCageReturnPc, sel]
      (endCageCallCalldataMem (endRelyAuthHashMem I)) (UInt256.ofNat 5)
      rdata acc k C)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord acc.2
        (endCageCallTargetWord ⟨7⟩ acc.2 I) ≠ ⟨0⟩) :
    ∃ gasWord k' C', RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨6281⟩
      (gasWord :: endCageCallTargetWord ⟨7⟩ acc.2 I :: ⟨0⟩ ::
        endCageCallOutPtr :: endCageCallInSize :: endCageCallOutPtr ::
        endCageCallOutSize :: endCageCallEndPtr :: endCageCallSelectorWord ::
        endCageCallTargetWord ⟨7⟩ acc.2 I :: endCageReturnPc :: sel :: [])
      (endCageCallCalldataMem (endRelyAuthHashMem I)) (UInt256.ofNat 5)
      rdata acc k' C' := by
  obtain ⟨_, _, rd6266⟩ := endCageX_cureExtcodesizeGuard h
  obtain ⟨gasWord, k', C', rd6281⟩ :=
    RD.solcExtcodesizeGuardOkGas (pc := ⟨6266⟩) (okPc := ⟨6278⟩) rd6266
      hcodeSize
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by jump_dest) (by native_decide)
      (by native_decide) (by native_decide) (by simp)
  exact ⟨gasWord, k', C', by simpa using rd6281⟩

theorem endCageX_curePostCall {cA gh bl σ σ₀ A I} {g : UInt256}
    {sel gasWord : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (h : RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨6281⟩
      (gasWord :: endCageCallTargetWord ⟨7⟩ acc.2 I :: ⟨0⟩ ::
        endCageCallOutPtr :: endCageCallInSize :: endCageCallOutPtr ::
        endCageCallOutSize :: endCageCallEndPtr :: endCageCallSelectorWord ::
        endCageCallTargetWord ⟨7⟩ acc.2 I :: endCageReturnPc :: sel :: [])
      (endCageCallCalldataMem (endRelyAuthHashMem I)) (UInt256.ofNat 5)
      rdata acc k C)
    (hdepth : I.depth.val < 1024) :
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap)
      (z : Bool) (out : ByteArray) (Ain : Substate) (callGas : UInt256) (k' C' : ℕ),
      (∃ (g'' : UInt256) (A' : Substate),
        (cA', σ', g'', A', z, out) =
          Ethereum.EVM.Θ I.blobVersionedHashes acc.1 gh bl acc.2 σ₀ Ain
            (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner)) I.sender
            (AccountAddress.ofUInt256 (endCageCallTargetWord ⟨7⟩ acc.2 I))
            (toExecute acc.2
              (AccountAddress.ofUInt256 (endCageCallTargetWord ⟨7⟩ acc.2 I)))
            callGas (UInt256.ofNat I.gasPrice) ⟨0⟩ ⟨0⟩
            ((endCageCallCalldataMem (endRelyAuthHashMem I)).readWithPadding
              endCageCallOutPtr.toNat endCageCallInSize.toNat)
            (I.depth + 1) I.header I.perm)
      ∧ RD endBytecode I (Sat256.ofUInt256 g)
          (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨6282⟩
          ((if z then ⟨1⟩ else ⟨0⟩) :: endCageCallEndPtr ::
            endCageCallSelectorWord :: endCageCallTargetWord ⟨7⟩ acc.2 I ::
            endCageReturnPc :: sel :: [])
          (endCageCallCalldataMem (endRelyAuthHashMem I)) (UInt256.ofNat 5)
          out (cA', σ') k' C'
      ∧ out.size < UInt256.size := by
  obtain ⟨cA', σ', z, out, Ain, callGas, k', C', hΘ, rd6282raw, hout⟩ :=
    RD.call h (by native_decide) hdepth (by evm_ov)
  refine ⟨cA', σ', z, out, Ain, callGas, k', C', ?_, ?_, hout⟩
  · cases acc
    simpa [initState] using hΘ
  · have hmin : (min endCageCallOutSize (UInt256.ofNat out.size)).toNat = 0 := by
      have hle : endCageCallOutSize ≤ UInt256.ofNat out.size := by
        show (0 : Nat) ≤ (UInt256.ofNat out.size).toNat
        exact Nat.zero_le _
      simp [endCageCallOutSize, min, hle]
    have haw :
        UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 5).toNat
          endCageCallOutPtr.toNat endCageCallInSize.toNat)
          endCageCallOutPtr.toNat endCageCallOutSize.toNat) = UInt256.ofNat 5 := by
      unfold endCageCallOutPtr endCageCallInSize endCageCallOutSize
      native_decide
    cases acc
    simpa [endCageCallOutPtr, endCageCallInSize, endCageCallOutSize,
      endCageCallEndPtr, hmin, byteArray_write_len_zero, haw] using rd6282raw

theorem endCageX_cureCallDepthLimit {cA gh bl σ σ₀ A I} {g : UInt256}
    {sel gasWord : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (h : RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨6281⟩
      (gasWord :: endCageCallTargetWord ⟨7⟩ acc.2 I :: ⟨0⟩ ::
        endCageCallOutPtr :: endCageCallInSize :: endCageCallOutPtr ::
        endCageCallOutSize :: endCageCallEndPtr :: endCageCallSelectorWord ::
        endCageCallTargetWord ⟨7⟩ acc.2 I :: endCageReturnPc :: sel :: [])
      (endCageCallCalldataMem (endRelyAuthHashMem I)) (UInt256.ofNat 5)
      rdata acc k C)
    (hdepth : I.depth = 1024) :
    ∃ k' C', RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨6282⟩
      (⟨0⟩ :: endCageCallEndPtr :: endCageCallSelectorWord ::
        endCageCallTargetWord ⟨7⟩ acc.2 I :: endCageReturnPc :: sel :: [])
      (endCageCallCalldataMem (endRelyAuthHashMem I)) (UInt256.ofNat 5)
      ByteArray.empty acc k' C' := by
  obtain ⟨k', C', rd6282raw⟩ :=
    RD.callDepthLimit h (by native_decide) hdepth
      (by simp only [List.length_cons, List.length_nil]; omega)
  refine ⟨k', C', ?_⟩
  have hmin : (min endCageCallOutSize (UInt256.ofNat ByteArray.empty.size)).toNat = 0 := by
    decide
  have haw :
      UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 5).toNat
        endCageCallOutPtr.toNat endCageCallInSize.toNat)
        endCageCallOutPtr.toNat endCageCallOutSize.toNat) = UInt256.ofNat 5 := by
    unfold endCageCallOutPtr endCageCallInSize endCageCallOutSize
    native_decide
  cases acc
  simpa [endCageCallOutPtr, endCageCallInSize, endCageCallOutSize,
    endCageCallEndPtr, hmin, byteArray_write_len_zero, haw] using rd6282raw

theorem endCageX_cureCallFailed {cA cA' gh bl σ σCall σ' σ₀ A I} {g : UInt256}
    {sel : UInt256} {mem rdata : ByteArray} {k C : ℕ}
    (h : RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨6282⟩
      (⟨0⟩ :: endCageCallEndPtr :: endCageCallSelectorWord ::
        endCageCallTargetWord ⟨7⟩ σCall I :: endCageReturnPc :: sel :: [])
      mem (UInt256.ofNat 5) rdata (cA', σ') k C)
    (hrdataSize : rdata.size < UInt256.size) :
    RDrev endBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) := by
  exact RD.solcCallSuccessGuardMissing (pc := ⟨6282⟩) (okPc := ⟨6298⟩) h
    rfl
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    hrdataSize (by simp only [List.length_cons, List.length_nil]; omega)

theorem endCageX_cureCallSucceeded {cA gh bl σ σCall σ₀ A I} {g : UInt256}
    {sel : UInt256} {mem rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (h : RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨6282⟩
      (⟨1⟩ :: endCageCallEndPtr :: endCageCallSelectorWord ::
        endCageCallTargetWord ⟨7⟩ σCall I :: endCageReturnPc :: sel :: [])
      mem (UInt256.ofNat 5) rdata acc k C) :
    ∃ k' C', RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨6300⟩
      (endCageCallEndPtr :: endCageCallSelectorWord ::
        endCageCallTargetWord ⟨7⟩ σCall I :: endCageReturnPc :: sel :: [])
      mem (UInt256.ofNat 5) rdata acc k' C' := by
  exact RD.solcCallSuccessGuardOk (pc := ⟨6282⟩) (okPc := ⟨6298⟩) h
    (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by jump_dest) (by native_decide) (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem endCageX_finish {cA cA' gh bl σ σCall σ' σ₀ A I} {g : UInt256}
    {sel : UInt256} {rdata : ByteArray} {k C : ℕ}
    (hperm : I.perm = true)
    (h : RD endBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨6300⟩
      (endCageCallEndPtr :: endCageCallSelectorWord ::
        endCageCallTargetWord ⟨7⟩ σCall I :: endCageReturnPc :: sel :: [])
      (endCageCallCalldataMem (endRelyAuthHashMem I)) (UInt256.ofNat 5)
      rdata (cA', σ') k C) :
    RDret endBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) (cA', σ')
      ByteArray.empty := by
  have hmload64Call :
      (if (⟨64⟩ : UInt256).toNat ≥
            (endCageCallCalldataMem (endRelyAuthHashMem I)).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 5 * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian
            ((endCageCallCalldataMem (endRelyAuthHashMem I)).readWithPadding
              (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [endCageCallCalldataMem_size_auth I]; decide) (by decide)
      (endCageCallCalldataMem_read64_auth I)
  have rd6304pre := evm_run h with [
    raw pop (by native_decide) (by evm_ov),
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) (by native_decide)
      mem_cost hmload64Call (by decide) (by evm_ov)]
  have rd6337 := rd6304pre.pushConst endCageFinalLogTopic
    (width := 32) (op := .PUSH32) (by native_decide) (by native_decide) (by evm_ov)
  have rd6343pre := evm_run rd6337 with [
    raw swap3 (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov)]
  have rdLog := RD.log1
    (a := ⟨128⟩) (b := ⟨0⟩) (c := endCageFinalLogTopic)
    (t := [endCageReturnPc, sel])
    0
    (UInt256.ofNat
      (MachineState.M (UInt256.ofNat 5).toNat (⟨128⟩ : UInt256).toNat
        (⟨0⟩ : UInt256).toNat))
    rd6343pre (by native_decide) hperm mem_cost (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd562 := RD.jump (a := endCageReturnPc) (t := [sel]) rdLog
    (by native_decide) (by jump_dest) (by evm_ov)
  have rd563 := RD.jumpdest (pc := endCageReturnPc) (stk := [sel]) rd562
    (by native_decide) (by evm_ov)
  exact RD.stop rd563 (by native_decide) (by evm_ov)

theorem endCageSourceStoresPrefix {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hauth : endRelyAuthWord σ I = ⟨1⟩)
    (hlive : endSlotWord ⟨8⟩ σ I = ⟨1⟩) :
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    let evmStores := endCagePostStoresState evm0
    ExecBlock config { contract := contract, locals := ∅ } evm0
      (nonpayable ++ auth ++
        [ .require (.binary .eq (.storage liveRef) (.intLit 1)),
          .assign .storage liveRef (.intLit 0),
          .assign .storage whenRef nowT ])
      (.ok { contract := contract, locals := ∅ } evmStores) := by
  intro evm0 evmStores
  let evmLive := Solm.EVM.storageStore evm0 evm0.executionEnv.codeOwner ⟨8⟩ ⟨0⟩
  have hguardAuth :
      evalExpr? config { contract := contract, locals := ∅ } evm0
        (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) = .ok (.bool true) := by
    simpa [evm0, endRelyAuthWord, endSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      evalExpr_endCage_auth_true evm0 I (by simp [evm0, initState]) hauth
  have hguardLive :
      evalExpr? config { contract := contract, locals := ∅ } evm0
        (.binary .eq (.storage liveRef) (.intLit 1)) = .ok (.bool true) := by
    simpa [evm0, endSlotWord, initState, Solm.EVM.storageLoad, State.lookupAccount] using
      evalExpr_endCage_live_true evm0 hlive
  have hassignLive :
      assignStorageRef? config { contract := contract, locals := ∅ } evm0
        .storage liveRef (.int 0) =
          .ok ({ contract := contract, locals := ∅ }, evmLive) := by
    simpa [evmLive] using endCageAssignLive evm0
  have htimestamp :
      evalExpr? config { contract := contract, locals := ∅ } evmLive nowT =
        .ok (.int (Int.ofNat (endCageTimestampWord evm0).toNat)) := by
    simpa [evmLive, endCageTimestampWord, storageStore_executionEnv] using
      evalExpr_endCage_timestamp evmLive
  have hassignWhen :
      assignStorageRef? config { contract := contract, locals := ∅ } evmLive
        .storage whenRef (.int (Int.ofNat (endCageTimestampWord evm0).toNat)) =
          .ok ({ contract := contract, locals := ∅ }, evmStores) := by
    simpa [evmLive, evmStores] using endCageAssignWhen evm0
  simp only [nonpayable, auth, List.cons_append, List.nil_append]
  refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
  · exact evalCallvalueEq_true (by simp only [evm0, initState]; exact hwv)
  refine ExecBlock.consNormal (ExecStmt.requireTrue hguardAuth) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue hguardLive) ?_
  refine ExecBlock.consNormal (ExecStmt.assign (by simp [evalExpr?, pure]) hassignLive) ?_
  exact ExecBlock.consNormal (ExecStmt.assign htimestamp hassignWhen) ExecBlock.nil

theorem evalExpr_endCage_storageAddr {evm : EVM.State} {locals : Store}
    {ref : StorageRef} {er : EvaledStorageRef} {slot : UInt256}
    (hbase : locals.get? ref.base = none)
    (her : evalStorageRef config { contract := contract, locals := locals } evm ref = .ok er)
    (hty : storageTypeAt? contract.storage er = some (.elem .address))
    (hloc : config.storage.layout er = fun _ => some (addrLoc slot)) :
    evalExpr? config { contract := contract, locals := locals } evm (.storage ref) =
      .ok (.address (endCageCallTargetAddr slot evm.accountMap evm.executionEnv)) := by
  rw [evalExpr_storage_scalar_value
    (cfg := config)
    (solm := { contract := contract, locals := locals })
    (slot := ref)
    (er := er)
    (t := .address)
    (loc := addrLoc slot)
    (hbase := hbase)
    (her := her)
    (hty := hty)
    (hloc := hloc)
    (hload := by exact endStorageLocLoad_address_offset0 evm slot)]
  simp [endCageCallTargetAddr, endCageCallTargetWord, endAddressReturnWord, endSlotWord,
    solcSlotWord, Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage]

theorem endCageCheckedCallNoCode {evm : EVM.State} {locals : Store}
    {ref : StorageRef} {er : EvaledStorageRef} {slot : UInt256} {retVar : Ident}
    (hbase : locals.get? ref.base = none)
    (her : evalStorageRef config { contract := contract, locals := locals } evm ref = .ok er)
    (hty : storageTypeAt? contract.storage er = some (.elem .address))
    (hloc : config.storage.layout er = fun _ => some (addrLoc slot))
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord evm.accountMap
        (endCageCallTargetWord slot evm.accountMap evm.executionEnv) = ⟨0⟩) :
    ExecBlock config { contract := contract, locals := locals } evm
      (checkedExternalCallStmts (.storage ref) "cage" (.intLit 0) [] retVar)
      .reverted := by
  have hreceiver :=
    evalExpr_endCage_storageAddr (evm := evm) (locals := locals)
      (ref := ref) (er := er) (slot := slot) hbase her hty hloc
  have hcodeZero :
      (UInt256.ofNat
        ((evm.lookupAccount (endCageCallTargetAddr slot evm.accountMap evm.executionEnv)).option
          0 (fun acc => acc.code.size))).toNat = 0 := by
    simpa [State.lookupAccount] using
      endCageCallTargetCode_zero_of_codeSize_zero
        (σ := evm.accountMap) (I := evm.executionEnv) slot hcodeSize
  have hguard :
      evalExpr? config { contract := contract, locals := locals } evm
        (.binary .gt (.extCodeSize (.storage ref)) (.intLit 0)) = .ok (.bool false) :=
    endEvalExpr_extCodeGuard_false hreceiver hcodeZero
  simpa [checkedExternalCallStmts] using
    checkedExternalCallNoCode
      (cfg := config) (C := contract) (evm := evm)
      (locals := locals) (receiver := .storage ref)
      (retVar := retVar) (name := "cage") (sendVal := 0)
      (args := []) (perm := true) hguard

theorem endCageCheckedCallFailed {evm evm' : EVM.State} {locals : Store}
    {ref : StorageRef} {er : EvaledStorageRef} {slot : UInt256} {retVar : Ident}
    {out : ByteArray}
    (hbase : locals.get? ref.base = none)
    (her : evalStorageRef config { contract := contract, locals := locals } evm ref = .ok er)
    (hty : storageTypeAt? contract.storage er = some (.elem .address))
    (hloc : config.storage.layout er = fun _ => some (addrLoc slot))
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord evm.accountMap
        (endCageCallTargetWord slot evm.accountMap evm.executionEnv) ≠ ⟨0⟩)
    (hcall :
      typedCallViaEVM config evm
        (EVM.address (endCageCallTargetAddr slot evm.accountMap evm.executionEnv)) "cage" 0
        [] (false, evm', out) true) :
    ExecBlock config { contract := contract, locals := locals } evm
      (checkedExternalCallStmts (.storage ref) "cage" (.intLit 0) [] retVar)
      .reverted := by
  have hreceiver :=
    evalExpr_endCage_storageAddr (evm := evm) (locals := locals)
      (ref := ref) (er := er) (slot := slot) hbase her hty hloc
  have hcodePos :
      0 < (UInt256.ofNat
        ((evm.lookupAccount (endCageCallTargetAddr slot evm.accountMap evm.executionEnv)).option
          0 (fun acc => acc.code.size))).toNat := by
    simpa [State.lookupAccount] using
      endCageCallTargetCode_pos_of_codeSize_ne
        (σ := evm.accountMap) (I := evm.executionEnv) slot hcodeSize
  have hguard :
      evalExpr? config { contract := contract, locals := locals } evm
        (.binary .gt (.extCodeSize (.storage ref)) (.intLit 0)) = .ok (.bool true) :=
    endEvalExpr_extCodeGuard_true hreceiver hcodePos
  have hargs :
      evalExprs? config { contract := contract, locals := locals } evm [] = .ok [] := by
    rfl
  simpa [checkedExternalCallStmts] using
    checkedExternalCallFailure
      (cfg := config) (C := contract) (evm := evm) (evm' := evm')
      (locals := locals) (receiver := .storage ref)
      (retVar := retVar) (name := "cage")
      (target := endCageCallTargetAddr slot evm.accountMap evm.executionEnv)
      (sendVal := 0) (args := []) (argVals := []) (out := out) (perm := true)
      hguard hreceiver hargs hcall

theorem endCageCheckedCallSuccess {evm evm' : EVM.State} {locals : Store}
    {ref : StorageRef} {er : EvaledStorageRef} {slot : UInt256} {retVar : Ident}
    {out : ByteArray}
    (hbase : locals.get? ref.base = none)
    (her : evalStorageRef config { contract := contract, locals := locals } evm ref = .ok er)
    (hty : storageTypeAt? contract.storage er = some (.elem .address))
    (hloc : config.storage.layout er = fun _ => some (addrLoc slot))
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord evm.accountMap
        (endCageCallTargetWord slot evm.accountMap evm.executionEnv) ≠ ⟨0⟩)
    (hcall :
      typedCallViaEVM config evm
        (EVM.address (endCageCallTargetAddr slot evm.accountMap evm.executionEnv)) "cage" 0
        [] (true, evm', out) true) :
    ExecBlock config { contract := contract, locals := locals } evm
      (checkedExternalCallStmts (.storage ref) "cage" (.intLit 0) [] retVar)
      (.ok { contract := contract, locals := locals.insert retVar .unit } evm') := by
  have hreceiver :=
    evalExpr_endCage_storageAddr (evm := evm) (locals := locals)
      (ref := ref) (er := er) (slot := slot) hbase her hty hloc
  have hcodePos :
      0 < (UInt256.ofNat
        ((evm.lookupAccount (endCageCallTargetAddr slot evm.accountMap evm.executionEnv)).option
          0 (fun acc => acc.code.size))).toNat := by
    simpa [State.lookupAccount] using
      endCageCallTargetCode_pos_of_codeSize_ne
        (σ := evm.accountMap) (I := evm.executionEnv) slot hcodeSize
  have hguard :
      evalExpr? config { contract := contract, locals := locals } evm
        (.binary .gt (.extCodeSize (.storage ref)) (.intLit 0)) = .ok (.bool true) :=
    endEvalExpr_extCodeGuard_true hreceiver hcodePos
  have hargs :
      evalExprs? config { contract := contract, locals := locals } evm [] = .ok [] := by
    rfl
  have hdec : config.externalABI.decode? "cage" out = some [] := by
    simp [config, externalABI, decodeVoid?]
  have hblock := checkedExternalCallSuccess
    (cfg := config) (C := contract) (evm := evm) (evm' := evm')
    (locals := locals) (receiver := .storage ref)
    (retVar := retVar) (name := "cage")
    (target := endCageCallTargetAddr slot evm.accountMap evm.executionEnv)
    (sendVal := 0) (args := []) (argVals := []) (out := out) (perm := true)
    (value := []) hguard hreceiver hargs hcall hdec
  simpa [checkedExternalCallStmts, collapseReturns] using hblock

abbrev endCageSourceStorePrefixStmts : List Stmt :=
  nonpayable ++ auth ++
    [ .require (.binary .eq (.storage liveRef) (.intLit 1)),
      .assign .storage liveRef (.intLit 0),
      .assign .storage whenRef nowT ]

abbrev endCageSourceVatStmts : List Stmt :=
  checkedExternalCallStmts (.storage vatRef) "cage" (.intLit 0) [] "_vatCage"

abbrev endCageSourceCatStmts : List Stmt :=
  checkedExternalCallStmts (.storage catRef) "cage" (.intLit 0) [] "_catCage"

abbrev endCageSourceDogStmts : List Stmt :=
  checkedExternalCallStmts (.storage dogRef) "cage" (.intLit 0) [] "_dogCage"

abbrev endCageSourceVowStmts : List Stmt :=
  checkedExternalCallStmts (.storage vowRef) "cage" (.intLit 0) [] "_vowCage"

abbrev endCageSourceSpotStmts : List Stmt :=
  checkedExternalCallStmts (.storage spotRef) "cage" (.intLit 0) [] "_spotCage"

abbrev endCageSourcePotStmts : List Stmt :=
  checkedExternalCallStmts (.storage potRef) "cage" (.intLit 0) [] "_potCage"

abbrev endCageSourceCureStmts : List Stmt :=
  checkedExternalCallStmts (.storage cureRef) "cage" (.intLit 0) [] "_cureCage"

abbrev endCageSourceCallStmts : List Stmt :=
  endCageSourceVatStmts ++ endCageSourceCatStmts ++ endCageSourceDogStmts ++
    endCageSourceVowStmts ++ endCageSourceSpotStmts ++ endCageSourcePotStmts ++
    endCageSourceCureStmts

theorem endCageSourceBody_eq :
    cageTransition.body = endCageSourceStorePrefixStmts ++ endCageSourceCallStmts := by
  simp [cageTransition, endCageSourceStorePrefixStmts, endCageSourceCallStmts,
    endCageSourceVatStmts, endCageSourceCatStmts, endCageSourceDogStmts,
    endCageSourceVowStmts, endCageSourceSpotStmts, endCageSourcePotStmts,
    endCageSourceCureStmts, checkedExternalCallStmts, nonpayable, auth]

theorem endCageExecBlock_append_revert {f f1 : Frame} {e e1 : EVM.State}
    {s1 s2 tail : List Stmt}
    (h1 : ExecBlock config f e s1 (.ok f1 e1))
    (h2 : ExecBlock config f1 e1 s2 .reverted) :
    ExecBlock config f e (s1 ++ s2 ++ tail) .reverted := by
  have h2tail :
      ExecBlock config f1 e1 (s2 ++ tail) .reverted :=
   .execBlock_append_term
      (s2 := tail) h2 (by intro f' e' h; cases h)
  simpa [List.append_assoc] using
   .execBlock_append (s2 := s2 ++ tail) h1 h2tail

theorem endCageSourceAuthReverts {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hauth : endRelyAuthWord σ I ≠ ⟨1⟩) :
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 ∅ cageTransition.body .reverted := by
  intro evm0
  have hguard :
      evalExpr? config { contract := contract, locals := ∅ } evm0
        (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) = .ok (.bool false) := by
    simpa [evm0, endRelyAuthWord, endSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      evalExpr_endCage_auth_false evm0 I (by simp [evm0, initState]) hauth
  refine ExecFuncBody.execBlockRevert ?_
  simpa [cageTransition, nonpayable, auth, checkedExternalCallStmts] using
    nonpayableSecondRequireReverts
      (cfg := config)
      (solm := { contract := contract, locals := ∅ })
      (evm := evm0)
      (guard := .binary .eq (.storage (wardsRef sender)) (.intLit 1))
      (rest :=
        [ .require (.binary .eq (.storage liveRef) (.intLit 1)),
          .assign .storage liveRef (.intLit 0),
          .assign .storage whenRef nowT ] ++
        checkedExternalCallStmts (.storage vatRef) "cage" (.intLit 0) [] "_vatCage" ++
        checkedExternalCallStmts (.storage catRef) "cage" (.intLit 0) [] "_catCage" ++
        checkedExternalCallStmts (.storage dogRef) "cage" (.intLit 0) [] "_dogCage" ++
        checkedExternalCallStmts (.storage vowRef) "cage" (.intLit 0) [] "_vowCage" ++
        checkedExternalCallStmts (.storage spotRef) "cage" (.intLit 0) [] "_spotCage" ++
        checkedExternalCallStmts (.storage potRef) "cage" (.intLit 0) [] "_potCage" ++
        checkedExternalCallStmts (.storage cureRef) "cage" (.intLit 0) [] "_cureCage")
      (by simp [evm0, initState]; exact hwv)
      hguard

theorem endCageSourceLiveReverts {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hauth : endRelyAuthWord σ I = ⟨1⟩)
    (hlive : endSlotWord ⟨8⟩ σ I ≠ ⟨1⟩) :
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 ∅ cageTransition.body .reverted := by
  intro evm0
  have hguardAuth :
      evalExpr? config { contract := contract, locals := ∅ } evm0
        (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) = .ok (.bool true) := by
    simpa [evm0, endRelyAuthWord, endSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      evalExpr_endCage_auth_true evm0 I (by simp [evm0, initState]) hauth
  have hguardLive :
      evalExpr? config { contract := contract, locals := ∅ } evm0
        (.binary .eq (.storage liveRef) (.intLit 1)) = .ok (.bool false) := by
    simpa [evm0, endSlotWord, initState, Solm.EVM.storageLoad, State.lookupAccount] using
      evalExpr_endCage_live_false evm0 hlive
  have hblock :
      ExecBlock config { contract := contract, locals := ∅ } evm0 cageTransition.body
        .reverted := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguardAuth) ?_
    exact ExecBlock.consRevert (ExecStmt.requireFalse hguardLive)
  simpa [ExecTransitionBody, cageTransition, nonpayable, auth, checkedExternalCallStmts, evm0]
    using ExecFuncBody.execBlockRevert hblock

theorem endCageBody {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = endBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (selectorOf cageTransition))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsel' : selIs I endCageConcreteSelector := by
    simpa [endCageSelectorBytes, endCageConcreteSelector] using hsel
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I endCageConcreteSelector (by rfl) hsel'
  have hdispatch : dispatchMsg contract I.calldata = some cageTransition :=
    endDispatchCage hsel
  have hdecode := endDecode_cage (I := I) hsz4
  have hreach := endReachCageBody (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz4 hsize hsel'
  obtain ⟨_, _, hAuthPc⟩ := endCageX_entry hreach
  let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  by_cases hauth : endRelyAuthWord σ_evm I = ⟨1⟩
  · have hauthSolm : endRelyAuthWord σ_solm I = ⟨1⟩ := by
      have hword : endRelyAuthWord σ_evm I = endRelyAuthWord σ_solm I := by
        simpa [endRelyAuthWord, endSlotWord, solcSlotWord] using
          accountMapEquiv_storage_findD hAccounts I.codeOwner
            (endRelyAuthStorageSlot I) ⟨0⟩
      rw [← hword]
      exact hauth
    obtain ⟨_, _, hLivePc⟩ := endCageX_authorized hauth hAuthPc
    by_cases hlive : endSlotWord ⟨8⟩ σ_evm I = ⟨1⟩
    · have hliveSolm : endSlotWord ⟨8⟩ σ_solm I = ⟨1⟩ := by
        have hword : endSlotWord ⟨8⟩ σ_evm I = endSlotWord ⟨8⟩ σ_solm I := by
          simpa [endSlotWord, solcSlotWord] using
            accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨8⟩ ⟨0⟩
        rw [← hword]
        exact hlive
      obtain ⟨_, _, hStorePc⟩ := endCageX_live hlive hLivePc
      obtain ⟨_, _, hVatStart⟩ := endCageX_storePrefix hperm hStorePc
      let evmS0 := endCagePostStoresState evmSolm
      let evmE0 := endCagePostStoresState
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
      let l0 : Store := ∅
      let lVat := l0.insert "_vatCage" .unit
      let lCat := lVat.insert "_catCage" .unit
      let lDog := lCat.insert "_dogCage" .unit
      let lVow := lDog.insert "_vowCage" .unit
      let lSpot := lVow.insert "_spotCage" .unit
      let lPot := lSpot.insert "_potCage" .unit
      let lCure := lPot.insert "_cureCage" .unit
      have hSrc0 :
          ExecBlock config { contract := contract, locals := ∅ } evmSolm
            endCageSourceStorePrefixStmts
            (.ok { contract := contract, locals := ∅ } evmS0) := by
        simpa [evmSolm, evmS0, endCageSourceStorePrefixStmts] using
          endCageSourceStoresPrefix (cA := cA) (gh := gh) (bl := bl)
            (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
            hwv hauthSolm hliveSolm
      have hAccounts0 : accountMapEquiv evmE0.accountMap evmS0.accountMap := by
        simpa [evmE0, evmS0, evmSolm, endCagePostStoresState, initState,
          storageStore_accountMap, endCageStoredAccountMap] using
          accountMapEquiv_sstoreAccountMap_two I.codeOwner I.codeOwner
            ⟨8⟩ ⟨0⟩ ⟨9⟩ (UInt256.ofNat I.header.timestamp) hAccounts
      have hState0 : EVMStateEquiv evmE0 evmS0 := by
        refine ⟨?_, ?_, ?_⟩
        · simp [evmE0, evmS0, evmSolm, endCagePostStoresState, initState,
            storageStore_executionEnv]
        · simp [evmE0, evmS0, evmSolm, endCagePostStoresState, initState,
            storageStore_createdAccounts]
        · exact hAccounts0
      have mkRevert
          {f1 : Frame} {e1 : EVM.State} {s1 s2 tail : List Stmt}
          (h1 :
            ExecBlock config { contract := contract, locals := ∅ } evmSolm s1
              (.ok f1 e1))
          (h2 : ExecBlock config f1 e1 s2 .reverted)
          (hshape : cageTransition.body = s1 ++ s2 ++ tail) :
          ExecTransitionBody config contract evmSolm ∅ cageTransition.body .reverted := by
        have hblock :
            ExecBlock config { contract := contract, locals := ∅ } evmSolm
              cageTransition.body .reverted := by
          rw [hshape]
          exact endCageExecBlock_append_revert (tail := tail) h1 h2
        simpa [ExecTransitionBody] using ExecFuncBody.execBlockRevert hblock
      by_cases hVatCodeE :
          Reasoning.Theory.extCodeSizeWord evmE0.accountMap
            (endCageCallTargetWord ⟨1⟩ evmE0.accountMap evmE0.executionEnv) = ⟨0⟩
      · have hVatCodeS :
            Reasoning.Theory.extCodeSizeWord evmS0.accountMap
              (endCageCallTargetWord ⟨1⟩ evmS0.accountMap evmS0.executionEnv) = ⟨0⟩ := by
          have hcodeS :=
            endCageCallTargetCodeSize_zero_accountMapEquiv
              (slot := ⟨1⟩) hAccounts0 hVatCodeE
          simpa [hState0.executionEnv] using hcodeS
        have hVatBlock :
            ExecBlock config { contract := contract, locals := l0 } evmS0
              endCageSourceVatStmts .reverted := by
          simpa [endCageSourceVatStmts] using
            endCageCheckedCallNoCode
              (evm := evmS0) (locals := l0)
              (ref := vatRef) (er := ({ base := "vat", steps := [] } : EvaledStorageRef))
              (slot := ⟨1⟩) (retVar := "_vatCage")
              (by simp [l0, vatRef])
              (by simp [evalStorageRef, evalStorageRefSteps, vatRef, EvalResult.bind,
                pure, bind])
              (by simp [storageTypeAt?, contract, storageDecls, addrSt])
              (by rfl)
              hVatCodeS
        have hbody :
            ExecTransitionBody config contract evmSolm ∅ cageTransition.body .reverted :=
          mkRevert
            (s1 := endCageSourceStorePrefixStmts)
            (s2 := endCageSourceVatStmts)
            (tail := endCageSourceCatStmts ++ endCageSourceDogStmts ++
              endCageSourceVowStmts ++ endCageSourceSpotStmts ++
              endCageSourcePotStmts ++ endCageSourceCureStmts)
            hSrc0 (by simpa [l0] using hVatBlock)
            (by simp [endCageSourceBody_eq, endCageSourceCallStmts, List.append_assoc])
        exact (endCageX_vatNoCode hVatStart
            (by
              simpa [evmE0, endCagePostStoresState, initState, storageStore_accountMap,
                storageStore_executionEnv, endCageStoredAccountMap] using hVatCodeE))
          |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
      · have hVatCodeSNE :
            Reasoning.Theory.extCodeSizeWord evmS0.accountMap
              (endCageCallTargetWord ⟨1⟩ evmS0.accountMap evmS0.executionEnv) ≠
                ⟨0⟩ := by
          have hcodeS :=
            endCageCallTargetCodeSize_ne_accountMapEquiv
              (slot := ⟨1⟩) hAccounts0 hVatCodeE
          simpa [hState0.executionEnv] using hcodeS
        obtain ⟨gasVat, _, _, hVatReady⟩ :=
          endCageX_vatCallReady hVatStart
            (by
              simpa [evmE0, endCagePostStoresState, initState, storageStore_accountMap,
                storageStore_executionEnv, endCageStoredAccountMap] using hVatCodeE)
        by_cases hdepthLt : I.depth.val < 1024
        · have hdepthNe0 : evmE0.executionEnv.depth ≠ 1024 := by
            intro hbad
            have hbadI : I.depth = 1024 := by
              simpa [evmE0, endCagePostStoresState, initState,
                storageStore_executionEnv] using hbad
            have hbadVal : I.depth.val = 1024 := congrArg Fin.val hbadI
            omega
          obtain ⟨cA1, σ1, z1, out1, Ain1, callGas1, _, _, hΘ1, rdVatPost, hout1⟩ :=
            endCageX_vatPostCall (acc := (cA, endCageStoredAccountMap σ_evm I))
              hVatReady hdepthLt
          rcases hΘ1 with ⟨g1'', A1, hΘ1eq⟩
          let evmE1 := { evmE0 with accountMap := σ1, substate := A1, createdAccounts := cA1 }
          have hΘ1bridge :
              (cA1, σ1, g1'', A1, z1, out1) =
                Ethereum.EVM.Θ evmE0.executionEnv.blobVersionedHashes evmE0.createdAccounts
                  evmE0.genesisBlockHeader evmE0.blocks evmE0.accountMap evmE0.σ₀ Ain1
                  (AccountAddress.ofUInt256 (UInt256.ofNat evmE0.executionEnv.codeOwner))
                  evmE0.executionEnv.sender
                  (AccountAddress.ofUInt256
                    (endCageCallTargetWord ⟨1⟩ evmE0.accountMap evmE0.executionEnv))
                  (toExecute evmE0.accountMap
                    (AccountAddress.ofUInt256
                      (endCageCallTargetWord ⟨1⟩ evmE0.accountMap evmE0.executionEnv)))
                  callGas1 (UInt256.ofNat evmE0.executionEnv.gasPrice) ⟨0⟩ ⟨0⟩
                  ((endCageCallCalldataMem
                    (endRelyAuthHashMem evmE0.executionEnv)).readWithPadding
                      endCageCallOutPtr.toNat endCageCallInSize.toNat)
                  (evmE0.executionEnv.depth + 1) evmE0.executionEnv.header true := by
            simpa [evmE0, endCagePostStoresState, initState, storageStore_accountMap,
              storageStore_createdAccounts, storageStore_executionEnv, endCageStoredAccountMap,
              hperm] using hΘ1eq
          obtain ⟨σ1s, A1s, hcall1Solm, hState1⟩ :=
            endCageCallMadeBridge (slot := ⟨1⟩)
              (evmE := evmE0) (evmS := evmS0)
              (cA' := cA1) (σ' := σ1) (A' := A1) (Ain := Ain1)
              (z := z1) (out := out1) (g'' := g1'') (callGas := callGas1)
              hdepthNe0 hΘ1bridge hAccounts0
              (by simp [evmE0, evmS0, evmSolm, endCagePostStoresState, initState])
              (by simp [evmE0, evmS0, evmSolm, endCagePostStoresState, initState,
                storageStore_createdAccounts])
              (by simp [evmE0, evmS0, evmSolm, endCagePostStoresState, initState])
              (by simp [evmE0, evmS0, evmSolm, endCagePostStoresState, initState])
              (by simp [evmE0, evmS0, evmSolm, endCagePostStoresState, initState,
                storageStore_executionEnv])
          let evmS1 := { evmS0 with accountMap := σ1s, substate := A1s, createdAccounts := cA1 }
          cases z1
          · have rdVatFail := rdVatPost
            simp at rdVatFail
            have hVatBlock :
                ExecBlock config { contract := contract, locals := l0 } evmS0
                  endCageSourceVatStmts .reverted := by
              simpa [endCageSourceVatStmts] using
                endCageCheckedCallFailed
                  (evm := evmS0) (evm' := evmS1) (locals := l0)
                  (ref := vatRef)
                  (er := ({ base := "vat", steps := [] } : EvaledStorageRef))
                  (slot := ⟨1⟩) (retVar := "_vatCage") (out := out1)
                  (by simp [l0, vatRef])
                  (by simp [evalStorageRef, evalStorageRefSteps, vatRef, EvalResult.bind,
                    pure, bind])
                  (by simp [storageTypeAt?, contract, storageDecls, addrSt])
                  (by rfl)
                  hVatCodeSNE
                  (by simpa [evmS1] using hcall1Solm)
            have hbody :
                ExecTransitionBody config contract evmSolm ∅ cageTransition.body .reverted :=
              mkRevert
                (s1 := endCageSourceStorePrefixStmts)
                (s2 := endCageSourceVatStmts)
                (tail := endCageSourceCatStmts ++ endCageSourceDogStmts ++
                  endCageSourceVowStmts ++ endCageSourceSpotStmts ++
                  endCageSourcePotStmts ++ endCageSourceCureStmts)
                hSrc0 (by simpa [l0] using hVatBlock)
                (by simp [endCageSourceBody_eq, endCageSourceCallStmts, List.append_assoc])
            exact (endCageX_vatCallFailed rdVatFail hout1)
              |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
          · have rdVatSucc := rdVatPost
            simp at rdVatSucc
            obtain ⟨_, _, rdVatClean0⟩ := endCageX_vatCallSucceeded rdVatSucc
            obtain ⟨_, _, hCatStart⟩ := endCageX_vatCleanup rdVatClean0
            have hVatBlock :
                ExecBlock config { contract := contract, locals := l0 } evmS0
                  endCageSourceVatStmts
                  (.ok { contract := contract, locals := lVat } evmS1) := by
              simpa [endCageSourceVatStmts, lVat, l0] using
                endCageCheckedCallSuccess
                  (evm := evmS0) (evm' := evmS1) (locals := l0)
                  (ref := vatRef)
                  (er := ({ base := "vat", steps := [] } : EvaledStorageRef))
                  (slot := ⟨1⟩) (retVar := "_vatCage") (out := out1)
                  (by simp [l0, vatRef])
                  (by simp [evalStorageRef, evalStorageRefSteps, vatRef, EvalResult.bind,
                    pure, bind])
                  (by simp [storageTypeAt?, contract, storageDecls, addrSt])
                  (by rfl)
                  hVatCodeSNE
                  (by simpa [evmS1] using hcall1Solm)
            have hSrcVat :
                ExecBlock config { contract := contract, locals := ∅ } evmSolm
                  (endCageSourceStorePrefixStmts ++ endCageSourceVatStmts)
                  (.ok { contract := contract, locals := lVat } evmS1) := by
              simpa [l0, List.append_assoc] using
               .execBlock_append (s2 := endCageSourceVatStmts)
                  hSrc0 hVatBlock
            by_cases hCatCodeE :
                Reasoning.Theory.extCodeSizeWord evmE1.accountMap
                  (endCageCallTargetWord ⟨2⟩ evmE1.accountMap evmE1.executionEnv) =
                    ⟨0⟩
            · have hCatCodeS :
                  Reasoning.Theory.extCodeSizeWord evmS1.accountMap
                    (endCageCallTargetWord ⟨2⟩ evmS1.accountMap evmS1.executionEnv) =
                      ⟨0⟩ := by
                have hcodeS :=
                  endCageCallTargetCodeSize_zero_accountMapEquiv
                    (slot := ⟨2⟩) hState1.accountMap hCatCodeE
                rw [hState1.executionEnv] at hcodeS
                simpa [evmS1] using hcodeS
              have hCatBlock :
                  ExecBlock config { contract := contract, locals := lVat } evmS1
                    endCageSourceCatStmts .reverted := by
                simpa [endCageSourceCatStmts] using
                  endCageCheckedCallNoCode
                    (evm := evmS1) (locals := lVat)
                    (ref := catRef)
                    (er := ({ base := "cat", steps := [] } : EvaledStorageRef))
                    (slot := ⟨2⟩) (retVar := "_catCage")
                    (by simp [lVat, l0, catRef])
                    (by simp [evalStorageRef, evalStorageRefSteps, catRef, EvalResult.bind,
                      pure, bind])
                    (by simp [storageTypeAt?, contract, storageDecls, addrSt])
                    (by rfl)
                    hCatCodeS
              have hbody :
                  ExecTransitionBody config contract evmSolm ∅ cageTransition.body .reverted :=
                mkRevert
                  (s1 := endCageSourceStorePrefixStmts ++ endCageSourceVatStmts)
                  (s2 := endCageSourceCatStmts)
                  (tail := endCageSourceDogStmts ++ endCageSourceVowStmts ++
                    endCageSourceSpotStmts ++ endCageSourcePotStmts ++
                    endCageSourceCureStmts)
                  hSrcVat hCatBlock
                  (by simp [endCageSourceBody_eq, endCageSourceCallStmts, List.append_assoc])
              exact (endCageX_catNoCode hCatStart
                  (by simpa [evmE1, evmE0, endCagePostStoresState, initState] using hCatCodeE))
                |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
            · have hCatCodeSNE :
                  Reasoning.Theory.extCodeSizeWord evmS1.accountMap
                    (endCageCallTargetWord ⟨2⟩ evmS1.accountMap evmS1.executionEnv) ≠
                      ⟨0⟩ := by
                have hcodeS :=
                  endCageCallTargetCodeSize_ne_accountMapEquiv
                    (slot := ⟨2⟩) hState1.accountMap hCatCodeE
                rw [hState1.executionEnv] at hcodeS
                simpa [evmS1] using hcodeS
              obtain ⟨gasCat, _, _, hCatReady⟩ :=
                endCageX_catCallReady hCatStart (by simpa [evmE1, evmE0, endCagePostStoresState, initState] using hCatCodeE)
              obtain ⟨cA2, σ2, z2, out2, Ain2, callGas2, _, _, hΘ2, rdCatPost, hout2⟩ :=
                endCageX_catPostCall hCatReady hdepthLt
              rcases hΘ2 with ⟨g2'', A2, hΘ2eq⟩
              let evmE2 :=
                { evmE1 with accountMap := σ2, substate := A2, createdAccounts := cA2 }
              have hdepthNe1 : evmE1.executionEnv.depth ≠ 1024 := by
                simpa [evmE1] using hdepthNe0
              have hΘ2bridge :
                  (cA2, σ2, g2'', A2, z2, out2) =
                    Ethereum.EVM.Θ evmE1.executionEnv.blobVersionedHashes
                      evmE1.createdAccounts evmE1.genesisBlockHeader evmE1.blocks
                      evmE1.accountMap evmE1.σ₀ Ain2
                      (AccountAddress.ofUInt256 (UInt256.ofNat evmE1.executionEnv.codeOwner))
                      evmE1.executionEnv.sender
                      (AccountAddress.ofUInt256
                        (endCageCallTargetWord ⟨2⟩ evmE1.accountMap evmE1.executionEnv))
                      (toExecute evmE1.accountMap
                        (AccountAddress.ofUInt256
                          (endCageCallTargetWord ⟨2⟩ evmE1.accountMap evmE1.executionEnv)))
                      callGas2 (UInt256.ofNat evmE1.executionEnv.gasPrice) ⟨0⟩ ⟨0⟩
                      ((endCageCallCalldataMem
                        (endRelyAuthHashMem evmE1.executionEnv)).readWithPadding
                          endCageCallOutPtr.toNat endCageCallInSize.toNat)
                      (evmE1.executionEnv.depth + 1) evmE1.executionEnv.header true := by
                simpa [evmE1, evmE0, endCagePostStoresState, initState,
                  storageStore_accountMap, storageStore_createdAccounts,
                  storageStore_executionEnv, endCageStoredAccountMap, endCageTimestampWord, hperm] using hΘ2eq
              obtain ⟨σ2s, A2s, hcall2Solm, hState2⟩ :=
                endCageCallMadeBridge (slot := ⟨2⟩)
                  (evmE := evmE1) (evmS := evmS1)
                  (cA' := cA2) (σ' := σ2) (A' := A2) (Ain := Ain2)
                  (z := z2) (out := out2) (g'' := g2'') (callGas := callGas2)
                  hdepthNe1 hΘ2bridge hState1.accountMap
                  (by simp [evmE1, evmS1, evmE0, evmS0, evmSolm, endCagePostStoresState,
                    initState])
                  (by simpa [evmE1, evmS1] using hState1.createdAccounts.symm)
                  (by simp [evmE1, evmS1, evmE0, evmS0, evmSolm, endCagePostStoresState,
                    initState])
                  (by simp [evmE1, evmS1, evmE0, evmS0, evmSolm, endCagePostStoresState,
                    initState])
                  (by simpa [evmE1, evmS1] using hState1.executionEnv.symm)
              let evmS2 :=
                { evmS1 with accountMap := σ2s, substate := A2s, createdAccounts := cA2 }
              cases z2
              · have rdCatFail := rdCatPost
                simp at rdCatFail
                have hCatBlock :
                    ExecBlock config { contract := contract, locals := lVat } evmS1
                      endCageSourceCatStmts .reverted := by
                  simpa [endCageSourceCatStmts] using
                    endCageCheckedCallFailed
                      (evm := evmS1) (evm' := evmS2) (locals := lVat)
                      (ref := catRef)
                      (er := ({ base := "cat", steps := [] } : EvaledStorageRef))
                      (slot := ⟨2⟩) (retVar := "_catCage") (out := out2)
                      (by simp [lVat, l0, catRef])
                      (by simp [evalStorageRef, evalStorageRefSteps, catRef,
                        EvalResult.bind, pure, bind])
                      (by simp [storageTypeAt?, contract, storageDecls, addrSt])
                      (by rfl)
                      hCatCodeSNE
                      (by simpa [evmS2] using hcall2Solm)
                have hbody :
                    ExecTransitionBody config contract evmSolm ∅ cageTransition.body
                      .reverted :=
                  mkRevert
                    (s1 := endCageSourceStorePrefixStmts ++ endCageSourceVatStmts)
                    (s2 := endCageSourceCatStmts)
                    (tail := endCageSourceDogStmts ++ endCageSourceVowStmts ++
                      endCageSourceSpotStmts ++ endCageSourcePotStmts ++
                      endCageSourceCureStmts)
                    hSrcVat hCatBlock
                    (by simp [endCageSourceBody_eq, endCageSourceCallStmts,
                      List.append_assoc])
                exact (endCageX_catCallFailed rdCatFail hout2)
                  |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
              · have rdCatSucc := rdCatPost
                simp at rdCatSucc
                obtain ⟨_, _, rdCatClean0⟩ := endCageX_catCallSucceeded rdCatSucc
                obtain ⟨_, _, hDogStart⟩ := endCageX_catCleanup rdCatClean0
                have hCatBlock :
                    ExecBlock config { contract := contract, locals := lVat } evmS1
                      endCageSourceCatStmts
                      (.ok { contract := contract, locals := lCat } evmS2) := by
                  simpa [endCageSourceCatStmts, lCat] using
                    endCageCheckedCallSuccess
                      (evm := evmS1) (evm' := evmS2) (locals := lVat)
                      (ref := catRef)
                      (er := ({ base := "cat", steps := [] } : EvaledStorageRef))
                      (slot := ⟨2⟩) (retVar := "_catCage") (out := out2)
                      (by simp [lVat, l0, catRef])
                      (by simp [evalStorageRef, evalStorageRefSteps, catRef,
                        EvalResult.bind, pure, bind])
                      (by simp [storageTypeAt?, contract, storageDecls, addrSt])
                      (by rfl)
                      hCatCodeSNE
                      (by simpa [evmS2] using hcall2Solm)
                have hSrcCat :
                    ExecBlock config { contract := contract, locals := ∅ } evmSolm
                      (endCageSourceStorePrefixStmts ++ endCageSourceVatStmts ++
                        endCageSourceCatStmts)
                      (.ok { contract := contract, locals := lCat } evmS2) := by
                  simpa [List.append_assoc] using
                   .execBlock_append (s2 := endCageSourceCatStmts)
                      hSrcVat hCatBlock
                by_cases hDogCodeE :
                    Reasoning.Theory.extCodeSizeWord evmE2.accountMap
                      (endCageCallTargetWord ⟨3⟩ evmE2.accountMap evmE2.executionEnv) =
                        ⟨0⟩
                · have hDogCodeS :
                      Reasoning.Theory.extCodeSizeWord evmS2.accountMap
                        (endCageCallTargetWord ⟨3⟩ evmS2.accountMap evmS2.executionEnv) =
                          ⟨0⟩ := by
                    have hcodeS :=
                      endCageCallTargetCodeSize_zero_accountMapEquiv
                        (slot := ⟨3⟩) hState2.accountMap hDogCodeE
                    rw [hState2.executionEnv] at hcodeS
                    simpa [evmS2] using hcodeS
                  have hDogBlock :
                      ExecBlock config { contract := contract, locals := lCat } evmS2
                        endCageSourceDogStmts .reverted := by
                    simpa [endCageSourceDogStmts] using
                      endCageCheckedCallNoCode
                        (evm := evmS2) (locals := lCat)
                        (ref := dogRef)
                        (er := ({ base := "dog", steps := [] } : EvaledStorageRef))
                        (slot := ⟨3⟩) (retVar := "_dogCage")
                        (by simp [lCat, lVat, l0, dogRef])
                        (by simp [evalStorageRef, evalStorageRefSteps, dogRef,
                          EvalResult.bind, pure, bind])
                        (by simp [storageTypeAt?, contract, storageDecls, addrSt])
                        (by rfl)
                        hDogCodeS
                  have hbody :
                      ExecTransitionBody config contract evmSolm ∅ cageTransition.body
                        .reverted :=
                    mkRevert
                      (s1 := endCageSourceStorePrefixStmts ++ endCageSourceVatStmts ++
                        endCageSourceCatStmts)
                      (s2 := endCageSourceDogStmts)
                      (tail := endCageSourceVowStmts ++ endCageSourceSpotStmts ++
                        endCageSourcePotStmts ++ endCageSourceCureStmts)
                      hSrcCat hDogBlock
                      (by simp [endCageSourceBody_eq, endCageSourceCallStmts,
                        List.append_assoc])
                  exact (endCageX_dogNoCode hDogStart
                      (by simpa [evmE2, evmE1, evmE0, endCagePostStoresState, initState] using hDogCodeE))
                    |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
                · have hDogCodeSNE :
                      Reasoning.Theory.extCodeSizeWord evmS2.accountMap
                        (endCageCallTargetWord ⟨3⟩ evmS2.accountMap evmS2.executionEnv) ≠
                          ⟨0⟩ := by
                    have hcodeS :=
                      endCageCallTargetCodeSize_ne_accountMapEquiv
                        (slot := ⟨3⟩) hState2.accountMap hDogCodeE
                    rw [hState2.executionEnv] at hcodeS
                    simpa [evmS2] using hcodeS
                  obtain ⟨gasDog, _, _, hDogReady⟩ :=
                    endCageX_dogCallReady hDogStart (by simpa [evmE2, evmE1, evmE0, endCagePostStoresState, initState] using hDogCodeE)
                  obtain ⟨cA3, σ3, z3, out3, Ain3, callGas3, _, _, hΘ3, rdDogPost,
                      hout3⟩ :=
                    endCageX_dogPostCall hDogReady hdepthLt
                  rcases hΘ3 with ⟨g3'', A3, hΘ3eq⟩
                  let evmE3 := { evmE2 with accountMap := σ3, substate := A3, createdAccounts := cA3 }
                  have hdepthNe2 : evmE2.executionEnv.depth ≠ 1024 := by
                    simpa [evmE2, evmE1] using hdepthNe0
                  have hΘ3bridge :
                      (cA3, σ3, g3'', A3, z3, out3) =
                        Ethereum.EVM.Θ evmE2.executionEnv.blobVersionedHashes
                          evmE2.createdAccounts evmE2.genesisBlockHeader evmE2.blocks
                          evmE2.accountMap evmE2.σ₀ Ain3
                          (AccountAddress.ofUInt256
                            (UInt256.ofNat evmE2.executionEnv.codeOwner))
                          evmE2.executionEnv.sender
                          (AccountAddress.ofUInt256
                            (endCageCallTargetWord ⟨3⟩ evmE2.accountMap
                              evmE2.executionEnv))
                          (toExecute evmE2.accountMap
                            (AccountAddress.ofUInt256
                              (endCageCallTargetWord ⟨3⟩ evmE2.accountMap
                                evmE2.executionEnv)))
                          callGas3 (UInt256.ofNat evmE2.executionEnv.gasPrice) ⟨0⟩ ⟨0⟩
                          ((endCageCallCalldataMem
                            (endRelyAuthHashMem evmE2.executionEnv)).readWithPadding
                              endCageCallOutPtr.toNat endCageCallInSize.toNat)
                          (evmE2.executionEnv.depth + 1) evmE2.executionEnv.header true := by
                    simpa [evmE2, evmE1, evmE0, endCagePostStoresState, initState,
                      storageStore_accountMap, storageStore_createdAccounts,
                      storageStore_executionEnv, endCageStoredAccountMap, endCageTimestampWord, hperm] using hΘ3eq
                  obtain ⟨σ3s, A3s, hcall3Solm, hState3⟩ :=
                    endCageCallMadeBridge (slot := ⟨3⟩)
                      (evmE := evmE2) (evmS := evmS2)
                      (cA' := cA3) (σ' := σ3) (A' := A3) (Ain := Ain3)
                      (z := z3) (out := out3) (g'' := g3'') (callGas := callGas3)
                      hdepthNe2 hΘ3bridge hState2.accountMap
                      (by simp [evmE2, evmS2, evmE1, evmS1, evmE0, evmS0, evmSolm,
                        endCagePostStoresState, initState])
                      (by simpa [evmE2, evmS2] using hState2.createdAccounts.symm)
                      (by simp [evmE2, evmS2, evmE1, evmS1, evmE0, evmS0, evmSolm,
                        endCagePostStoresState, initState])
                      (by simp [evmE2, evmS2, evmE1, evmS1, evmE0, evmS0, evmSolm,
                        endCagePostStoresState, initState])
                      (by simpa [evmE2, evmS2] using hState2.executionEnv.symm)
                  let evmS3 := { evmS2 with accountMap := σ3s, substate := A3s, createdAccounts := cA3 }
                  cases z3
                  · have rdDogFail := rdDogPost
                    simp at rdDogFail
                    have hDogBlock :
                        ExecBlock config { contract := contract, locals := lCat } evmS2
                          endCageSourceDogStmts .reverted := by
                      simpa [endCageSourceDogStmts] using
                        endCageCheckedCallFailed
                          (evm := evmS2) (evm' := evmS3) (locals := lCat)
                          (ref := dogRef)
                          (er := ({ base := "dog", steps := [] } : EvaledStorageRef))
                          (slot := ⟨3⟩) (retVar := "_dogCage") (out := out3)
                          (by simp [lCat, lVat, l0, dogRef])
                          (by simp [evalStorageRef, evalStorageRefSteps, dogRef,
                            EvalResult.bind, pure, bind])
                          (by simp [storageTypeAt?, contract, storageDecls, addrSt])
                          (by rfl)
                          hDogCodeSNE
                          (by simpa [evmS3] using hcall3Solm)
                    have hbody :
                        ExecTransitionBody config contract evmSolm ∅ cageTransition.body
                          .reverted :=
                      mkRevert
                        (s1 := endCageSourceStorePrefixStmts ++ endCageSourceVatStmts ++
                          endCageSourceCatStmts)
                        (s2 := endCageSourceDogStmts)
                        (tail := endCageSourceVowStmts ++ endCageSourceSpotStmts ++
                          endCageSourcePotStmts ++ endCageSourceCureStmts)
                        hSrcCat hDogBlock
                        (by simp [endCageSourceBody_eq, endCageSourceCallStmts,
                          List.append_assoc])
                    exact (endCageX_dogCallFailed rdDogFail hout3)
                      |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
                  · have rdDogSucc := rdDogPost
                    simp at rdDogSucc
                    obtain ⟨_, _, rdDogClean0⟩ := endCageX_dogCallSucceeded rdDogSucc
                    obtain ⟨_, _, hVowStart⟩ := endCageX_dogCleanup rdDogClean0
                    have hDogBlock :
                        ExecBlock config { contract := contract, locals := lCat } evmS2
                          endCageSourceDogStmts
                          (.ok { contract := contract, locals := lDog } evmS3) := by
                      simpa [endCageSourceDogStmts, lDog] using
                        endCageCheckedCallSuccess
                          (evm := evmS2) (evm' := evmS3) (locals := lCat)
                          (ref := dogRef)
                          (er := ({ base := "dog", steps := [] } : EvaledStorageRef))
                          (slot := ⟨3⟩) (retVar := "_dogCage") (out := out3)
                          (by simp [lCat, lVat, l0, dogRef])
                          (by simp [evalStorageRef, evalStorageRefSteps, dogRef,
                            EvalResult.bind, pure, bind])
                          (by simp [storageTypeAt?, contract, storageDecls, addrSt])
                          (by rfl)
                          hDogCodeSNE
                          (by simpa [evmS3] using hcall3Solm)
                    have hSrcDog :
                        ExecBlock config { contract := contract, locals := ∅ } evmSolm
                          (endCageSourceStorePrefixStmts ++ endCageSourceVatStmts ++
                            endCageSourceCatStmts ++ endCageSourceDogStmts)
                          (.ok { contract := contract, locals := lDog } evmS3) := by
                      simpa [List.append_assoc] using
                       .execBlock_append
                          (s2 := endCageSourceDogStmts) hSrcCat hDogBlock
                    by_cases hVowCodeE :
                        Reasoning.Theory.extCodeSizeWord evmE3.accountMap
                          (endCageCallTargetWord ⟨4⟩ evmE3.accountMap
                            evmE3.executionEnv) = ⟨0⟩
                    · have hVowCodeS :
                          Reasoning.Theory.extCodeSizeWord evmS3.accountMap
                            (endCageCallTargetWord ⟨4⟩ evmS3.accountMap
                              evmS3.executionEnv) = ⟨0⟩ := by
                        have hcodeS :=
                          endCageCallTargetCodeSize_zero_accountMapEquiv
                            (slot := ⟨4⟩) hState3.accountMap hVowCodeE
                        rw [hState3.executionEnv] at hcodeS
                        simpa [evmS3] using hcodeS
                      have hVowBlock :
                          ExecBlock config { contract := contract, locals := lDog } evmS3
                            endCageSourceVowStmts .reverted := by
                        simpa [endCageSourceVowStmts] using
                          endCageCheckedCallNoCode
                            (evm := evmS3) (locals := lDog)
                            (ref := vowRef)
                            (er := ({ base := "vow", steps := [] } : EvaledStorageRef))
                            (slot := ⟨4⟩) (retVar := "_vowCage")
                            (by simp [lDog, lCat, lVat, l0, vowRef])
                            (by simp [evalStorageRef, evalStorageRefSteps, vowRef,
                              EvalResult.bind, pure, bind])
                            (by simp [storageTypeAt?, contract, storageDecls, addrSt])
                            (by rfl)
                            hVowCodeS
                      have hbody :
                          ExecTransitionBody config contract evmSolm ∅ cageTransition.body
                            .reverted :=
                        mkRevert
                          (s1 := endCageSourceStorePrefixStmts ++ endCageSourceVatStmts ++
                            endCageSourceCatStmts ++ endCageSourceDogStmts)
                          (s2 := endCageSourceVowStmts)
                          (tail := endCageSourceSpotStmts ++ endCageSourcePotStmts ++
                            endCageSourceCureStmts)
                          hSrcDog hVowBlock
                          (by simp [endCageSourceBody_eq, endCageSourceCallStmts,
                            List.append_assoc])
                      exact (endCageX_vowNoCode hVowStart
                          (by simpa [evmE3, evmE2, evmE1, evmE0, endCagePostStoresState, initState] using hVowCodeE))
                        |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
                    · have hVowCodeSNE :
                          Reasoning.Theory.extCodeSizeWord evmS3.accountMap
                            (endCageCallTargetWord ⟨4⟩ evmS3.accountMap
                              evmS3.executionEnv) ≠ ⟨0⟩ := by
                        have hcodeS :=
                          endCageCallTargetCodeSize_ne_accountMapEquiv
                            (slot := ⟨4⟩) hState3.accountMap hVowCodeE
                        rw [hState3.executionEnv] at hcodeS
                        simpa [evmS3] using hcodeS
                      obtain ⟨gasVow, _, _, hVowReady⟩ :=
                        endCageX_vowCallReady hVowStart
                          (by simpa [evmE3, evmE2, evmE1, evmE0, endCagePostStoresState, initState] using hVowCodeE)
                      obtain ⟨cA4, σ4, z4, out4, Ain4, callGas4, _, _, hΘ4,
                          rdVowPost, hout4⟩ :=
                        endCageX_vowPostCall hVowReady hdepthLt
                      rcases hΘ4 with ⟨g4'', A4, hΘ4eq⟩
                      let evmE4 := { evmE3 with accountMap := σ4, substate := A4, createdAccounts := cA4 }
                      have hdepthNe3 : evmE3.executionEnv.depth ≠ 1024 := by
                        simpa [evmE3, evmE2, evmE1] using hdepthNe0
                      have hΘ4bridge :
                          (cA4, σ4, g4'', A4, z4, out4) =
                            Ethereum.EVM.Θ evmE3.executionEnv.blobVersionedHashes
                              evmE3.createdAccounts evmE3.genesisBlockHeader evmE3.blocks
                              evmE3.accountMap evmE3.σ₀ Ain4
                              (AccountAddress.ofUInt256
                                (UInt256.ofNat evmE3.executionEnv.codeOwner))
                              evmE3.executionEnv.sender
                              (AccountAddress.ofUInt256
                                (endCageCallTargetWord ⟨4⟩ evmE3.accountMap
                                  evmE3.executionEnv))
                              (toExecute evmE3.accountMap
                                (AccountAddress.ofUInt256
                                  (endCageCallTargetWord ⟨4⟩ evmE3.accountMap
                                    evmE3.executionEnv)))
                              callGas4 (UInt256.ofNat evmE3.executionEnv.gasPrice)
                              ⟨0⟩ ⟨0⟩
                              ((endCageCallCalldataMem
                                (endRelyAuthHashMem evmE3.executionEnv)).readWithPadding
                                  endCageCallOutPtr.toNat endCageCallInSize.toNat)
                              (evmE3.executionEnv.depth + 1) evmE3.executionEnv.header
                              true := by
                        simpa [evmE3, evmE2, evmE1, evmE0, endCagePostStoresState,
                          initState, storageStore_accountMap, storageStore_createdAccounts,
                          storageStore_executionEnv, endCageStoredAccountMap, endCageTimestampWord, hperm] using
                          hΘ4eq
                      obtain ⟨σ4s, A4s, hcall4Solm, hState4⟩ :=
                        endCageCallMadeBridge (slot := ⟨4⟩)
                          (evmE := evmE3) (evmS := evmS3)
                          (cA' := cA4) (σ' := σ4) (A' := A4) (Ain := Ain4)
                          (z := z4) (out := out4) (g'' := g4'') (callGas := callGas4)
                          hdepthNe3 hΘ4bridge hState3.accountMap
                          (by simp [evmE3, evmS3, evmE2, evmS2, evmE1, evmS1,
                            evmE0, evmS0, evmSolm, endCagePostStoresState, initState])
                          (by simpa [evmE3, evmS3] using hState3.createdAccounts.symm)
                          (by simp [evmE3, evmS3, evmE2, evmS2, evmE1, evmS1,
                            evmE0, evmS0, evmSolm, endCagePostStoresState, initState])
                          (by simp [evmE3, evmS3, evmE2, evmS2, evmE1, evmS1,
                            evmE0, evmS0, evmSolm, endCagePostStoresState, initState])
                          (by simpa [evmE3, evmS3] using hState3.executionEnv.symm)
                      let evmS4 := { evmS3 with accountMap := σ4s, substate := A4s, createdAccounts := cA4 }
                      cases z4
                      · have rdVowFail := rdVowPost
                        simp at rdVowFail
                        have hVowBlock :
                            ExecBlock config { contract := contract, locals := lDog }
                              evmS3 endCageSourceVowStmts .reverted := by
                          simpa [endCageSourceVowStmts] using
                            endCageCheckedCallFailed
                              (evm := evmS3) (evm' := evmS4) (locals := lDog)
                              (ref := vowRef)
                              (er := ({ base := "vow", steps := [] } : EvaledStorageRef))
                              (slot := ⟨4⟩) (retVar := "_vowCage") (out := out4)
                              (by simp [lDog, lCat, lVat, l0, vowRef])
                              (by simp [evalStorageRef, evalStorageRefSteps, vowRef,
                                EvalResult.bind, pure, bind])
                              (by simp [storageTypeAt?, contract, storageDecls, addrSt])
                              (by rfl)
                              hVowCodeSNE
                              (by simpa [evmS4] using hcall4Solm)
                        have hbody :
                            ExecTransitionBody config contract evmSolm ∅ cageTransition.body
                              .reverted :=
                          mkRevert
                            (s1 := endCageSourceStorePrefixStmts ++
                              endCageSourceVatStmts ++ endCageSourceCatStmts ++
                              endCageSourceDogStmts)
                            (s2 := endCageSourceVowStmts)
                            (tail := endCageSourceSpotStmts ++ endCageSourcePotStmts ++
                              endCageSourceCureStmts)
                            hSrcDog hVowBlock
                            (by simp [endCageSourceBody_eq, endCageSourceCallStmts,
                              List.append_assoc])
                        exact (endCageX_vowCallFailed rdVowFail hout4)
                          |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
                      · have rdVowSucc := rdVowPost
                        simp at rdVowSucc
                        obtain ⟨_, _, rdVowClean0⟩ := endCageX_vowCallSucceeded rdVowSucc
                        obtain ⟨_, _, hSpotStart⟩ := endCageX_vowCleanup rdVowClean0
                        have hVowBlock :
                            ExecBlock config { contract := contract, locals := lDog }
                              evmS3 endCageSourceVowStmts
                              (.ok { contract := contract, locals := lVow } evmS4) := by
                          simpa [endCageSourceVowStmts, lVow] using
                            endCageCheckedCallSuccess
                              (evm := evmS3) (evm' := evmS4) (locals := lDog)
                              (ref := vowRef)
                              (er := ({ base := "vow", steps := [] } : EvaledStorageRef))
                              (slot := ⟨4⟩) (retVar := "_vowCage") (out := out4)
                              (by simp [lDog, lCat, lVat, l0, vowRef])
                              (by simp [evalStorageRef, evalStorageRefSteps, vowRef,
                                EvalResult.bind, pure, bind])
                              (by simp [storageTypeAt?, contract, storageDecls, addrSt])
                              (by rfl)
                              hVowCodeSNE
                              (by simpa [evmS4] using hcall4Solm)
                        have hSrcVow :
                            ExecBlock config { contract := contract, locals := ∅ } evmSolm
                              (endCageSourceStorePrefixStmts ++ endCageSourceVatStmts ++
                                endCageSourceCatStmts ++ endCageSourceDogStmts ++
                                endCageSourceVowStmts)
                              (.ok { contract := contract, locals := lVow } evmS4) := by
                          simpa [List.append_assoc] using
                           .execBlock_append
                              (s2 := endCageSourceVowStmts) hSrcDog hVowBlock
                        by_cases hSpotCodeE :
                            Reasoning.Theory.extCodeSizeWord evmE4.accountMap
                              (endCageCallTargetWord ⟨6⟩ evmE4.accountMap
                                evmE4.executionEnv) = ⟨0⟩
                        · have hSpotCodeS :
                              Reasoning.Theory.extCodeSizeWord evmS4.accountMap
                                (endCageCallTargetWord ⟨6⟩ evmS4.accountMap
                                  evmS4.executionEnv) = ⟨0⟩ := by
                            have hcodeS :=
                              endCageCallTargetCodeSize_zero_accountMapEquiv
                                (slot := ⟨6⟩) hState4.accountMap hSpotCodeE
                            rw [hState4.executionEnv] at hcodeS
                            simpa [evmS4] using hcodeS
                          have hSpotBlock :
                              ExecBlock config { contract := contract, locals := lVow }
                                evmS4 endCageSourceSpotStmts .reverted := by
                            simpa [endCageSourceSpotStmts] using
                              endCageCheckedCallNoCode
                                (evm := evmS4) (locals := lVow)
                                (ref := spotRef)
                                (er := ({ base := "spot", steps := [] } :
                                  EvaledStorageRef))
                                (slot := ⟨6⟩) (retVar := "_spotCage")
                                (by simp [lVow, lDog, lCat, lVat, l0, spotRef])
                                (by simp [evalStorageRef, evalStorageRefSteps, spotRef,
                                  EvalResult.bind, pure, bind])
                                (by simp [storageTypeAt?, contract, storageDecls, addrSt])
                                (by rfl)
                                hSpotCodeS
                          have hbody :
                              ExecTransitionBody config contract evmSolm ∅ cageTransition.body
                                .reverted :=
                            mkRevert
                              (s1 := endCageSourceStorePrefixStmts ++
                                endCageSourceVatStmts ++ endCageSourceCatStmts ++
                                endCageSourceDogStmts ++ endCageSourceVowStmts)
                              (s2 := endCageSourceSpotStmts)
                              (tail := endCageSourcePotStmts ++ endCageSourceCureStmts)
                              hSrcVow hSpotBlock
                              (by simp [endCageSourceBody_eq, endCageSourceCallStmts,
                                List.append_assoc])
                          exact (endCageX_spotNoCode hSpotStart
                              (by simpa [evmE4, evmE3, evmE2, evmE1, evmE0, endCagePostStoresState, initState] using hSpotCodeE))
                            |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
                        · have hSpotCodeSNE :
                              Reasoning.Theory.extCodeSizeWord evmS4.accountMap
                                (endCageCallTargetWord ⟨6⟩ evmS4.accountMap
                                  evmS4.executionEnv) ≠ ⟨0⟩ := by
                            have hcodeS :=
                              endCageCallTargetCodeSize_ne_accountMapEquiv
                                (slot := ⟨6⟩) hState4.accountMap hSpotCodeE
                            rw [hState4.executionEnv] at hcodeS
                            simpa [evmS4] using hcodeS
                          obtain ⟨gasSpot, _, _, hSpotReady⟩ :=
                            endCageX_spotCallReady hSpotStart
                              (by simpa [evmE4, evmE3, evmE2, evmE1, evmE0, endCagePostStoresState, initState] using hSpotCodeE)
                          obtain ⟨cA5, σ5, z5, out5, Ain5, callGas5, _, _, hΘ5,
                              rdSpotPost, hout5⟩ :=
                            endCageX_spotPostCall hSpotReady hdepthLt
                          rcases hΘ5 with ⟨g5'', A5, hΘ5eq⟩
                          let evmE5 := { evmE4 with accountMap := σ5, substate := A5, createdAccounts := cA5 }
                          have hdepthNe4 : evmE4.executionEnv.depth ≠ 1024 := by
                            simpa [evmE4, evmE3, evmE2, evmE1] using hdepthNe0
                          have hΘ5bridge :
                              (cA5, σ5, g5'', A5, z5, out5) =
                                Ethereum.EVM.Θ evmE4.executionEnv.blobVersionedHashes
                                  evmE4.createdAccounts evmE4.genesisBlockHeader
                                  evmE4.blocks evmE4.accountMap evmE4.σ₀ Ain5
                                  (AccountAddress.ofUInt256
                                    (UInt256.ofNat evmE4.executionEnv.codeOwner))
                                  evmE4.executionEnv.sender
                                  (AccountAddress.ofUInt256
                                    (endCageCallTargetWord ⟨6⟩ evmE4.accountMap
                                      evmE4.executionEnv))
                                  (toExecute evmE4.accountMap
                                    (AccountAddress.ofUInt256
                                      (endCageCallTargetWord ⟨6⟩ evmE4.accountMap
                                        evmE4.executionEnv)))
                                  callGas5 (UInt256.ofNat evmE4.executionEnv.gasPrice)
                                  ⟨0⟩ ⟨0⟩
                                  ((endCageCallCalldataMem
                                    (endRelyAuthHashMem evmE4.executionEnv)).readWithPadding
                                      endCageCallOutPtr.toNat endCageCallInSize.toNat)
                                  (evmE4.executionEnv.depth + 1) evmE4.executionEnv.header
                                  true := by
                            simpa [evmE4, evmE3, evmE2, evmE1, evmE0,
                              endCagePostStoresState, initState, storageStore_accountMap,
                              storageStore_createdAccounts, storageStore_executionEnv,
                              endCageStoredAccountMap, endCageTimestampWord, hperm] using hΘ5eq
                          obtain ⟨σ5s, A5s, hcall5Solm, hState5⟩ :=
                            endCageCallMadeBridge (slot := ⟨6⟩)
                              (evmE := evmE4) (evmS := evmS4)
                              (cA' := cA5) (σ' := σ5) (A' := A5) (Ain := Ain5)
                              (z := z5) (out := out5) (g'' := g5'')
                              (callGas := callGas5)
                              hdepthNe4 hΘ5bridge hState4.accountMap
                              (by simp [evmE4, evmS4, evmE3, evmS3, evmE2, evmS2,
                                evmE1, evmS1, evmE0, evmS0, evmSolm,
                                endCagePostStoresState, initState])
                              (by simpa [evmE4, evmS4] using hState4.createdAccounts.symm)
                              (by simp [evmE4, evmS4, evmE3, evmS3, evmE2, evmS2,
                                evmE1, evmS1, evmE0, evmS0, evmSolm,
                                endCagePostStoresState, initState])
                              (by simp [evmE4, evmS4, evmE3, evmS3, evmE2, evmS2,
                                evmE1, evmS1, evmE0, evmS0, evmSolm,
                                endCagePostStoresState, initState])
                              (by simpa [evmE4, evmS4] using hState4.executionEnv.symm)
                          let evmS5 := { evmS4 with accountMap := σ5s, substate := A5s, createdAccounts := cA5 }
                          cases z5
                          · have rdSpotFail := rdSpotPost
                            simp at rdSpotFail
                            have hSpotBlock :
                                ExecBlock config { contract := contract, locals := lVow }
                                  evmS4 endCageSourceSpotStmts .reverted := by
                              simpa [endCageSourceSpotStmts] using
                                endCageCheckedCallFailed
                                  (evm := evmS4) (evm' := evmS5) (locals := lVow)
                                  (ref := spotRef)
                                  (er := ({ base := "spot", steps := [] } :
                                    EvaledStorageRef))
                                  (slot := ⟨6⟩) (retVar := "_spotCage") (out := out5)
                                  (by simp [lVow, lDog, lCat, lVat, l0, spotRef])
                                  (by simp [evalStorageRef, evalStorageRefSteps, spotRef,
                                    EvalResult.bind, pure, bind])
                                  (by simp [storageTypeAt?, contract, storageDecls, addrSt])
                                  (by rfl)
                                  hSpotCodeSNE
                                  (by simpa [evmS5] using hcall5Solm)
                            have hbody :
                                ExecTransitionBody config contract evmSolm ∅
                                  cageTransition.body .reverted :=
                              mkRevert
                                (s1 := endCageSourceStorePrefixStmts ++
                                  endCageSourceVatStmts ++ endCageSourceCatStmts ++
                                  endCageSourceDogStmts ++ endCageSourceVowStmts)
                                (s2 := endCageSourceSpotStmts)
                                (tail := endCageSourcePotStmts ++ endCageSourceCureStmts)
                                hSrcVow hSpotBlock
                                (by simp [endCageSourceBody_eq, endCageSourceCallStmts,
                                  List.append_assoc])
                            exact (endCageX_spotCallFailed rdSpotFail hout5)
                              |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
                          · have rdSpotSucc := rdSpotPost
                            simp at rdSpotSucc
                            obtain ⟨_, _, rdSpotClean0⟩ :=
                              endCageX_spotCallSucceeded rdSpotSucc
                            obtain ⟨_, _, hPotStart⟩ := endCageX_spotCleanup rdSpotClean0
                            have hSpotBlock :
                                ExecBlock config { contract := contract, locals := lVow }
                                  evmS4 endCageSourceSpotStmts
                                  (.ok { contract := contract, locals := lSpot }
                                    evmS5) := by
                              simpa [endCageSourceSpotStmts, lSpot] using
                                endCageCheckedCallSuccess
                                  (evm := evmS4) (evm' := evmS5) (locals := lVow)
                                  (ref := spotRef)
                                  (er := ({ base := "spot", steps := [] } :
                                    EvaledStorageRef))
                                  (slot := ⟨6⟩) (retVar := "_spotCage") (out := out5)
                                  (by simp [lVow, lDog, lCat, lVat, l0, spotRef])
                                  (by simp [evalStorageRef, evalStorageRefSteps, spotRef,
                                    EvalResult.bind, pure, bind])
                                  (by simp [storageTypeAt?, contract, storageDecls, addrSt])
                                  (by rfl)
                                  hSpotCodeSNE
                                  (by simpa [evmS5] using hcall5Solm)
                            have hSrcSpot :
                                ExecBlock config { contract := contract, locals := ∅ }
                                  evmSolm
                                  (endCageSourceStorePrefixStmts ++ endCageSourceVatStmts ++
                                    endCageSourceCatStmts ++ endCageSourceDogStmts ++
                                    endCageSourceVowStmts ++ endCageSourceSpotStmts)
                                  (.ok { contract := contract, locals := lSpot }
                                    evmS5) := by
                              simpa [List.append_assoc] using
                               .execBlock_append
                                  (s2 := endCageSourceSpotStmts) hSrcVow hSpotBlock
                            by_cases hPotCodeE :
                                Reasoning.Theory.extCodeSizeWord evmE5.accountMap
                                  (endCageCallTargetWord ⟨5⟩ evmE5.accountMap
                                    evmE5.executionEnv) = ⟨0⟩
                            · have hPotCodeS :
                                  Reasoning.Theory.extCodeSizeWord evmS5.accountMap
                                    (endCageCallTargetWord ⟨5⟩ evmS5.accountMap
                                      evmS5.executionEnv) = ⟨0⟩ := by
                                have hcodeS :=
                                  endCageCallTargetCodeSize_zero_accountMapEquiv
                                    (slot := ⟨5⟩) hState5.accountMap hPotCodeE
                                rw [hState5.executionEnv] at hcodeS
                                simpa [evmS5] using hcodeS
                              have hPotBlock :
                                  ExecBlock config { contract := contract, locals := lSpot }
                                    evmS5 endCageSourcePotStmts .reverted := by
                                simpa [endCageSourcePotStmts] using
                                  endCageCheckedCallNoCode
                                    (evm := evmS5) (locals := lSpot)
                                    (ref := potRef)
                                    (er := ({ base := "pot", steps := [] } :
                                      EvaledStorageRef))
                                    (slot := ⟨5⟩) (retVar := "_potCage")
                                    (by simp [lSpot, lVow, lDog, lCat, lVat, l0, potRef])
                                    (by simp [evalStorageRef, evalStorageRefSteps, potRef,
                                      EvalResult.bind, pure, bind])
                                    (by simp [storageTypeAt?, contract, storageDecls, addrSt])
                                    (by rfl)
                                    hPotCodeS
                              have hbody :
                                  ExecTransitionBody config contract evmSolm ∅
                                    cageTransition.body .reverted :=
                                mkRevert
                                  (s1 := endCageSourceStorePrefixStmts ++
                                    endCageSourceVatStmts ++ endCageSourceCatStmts ++
                                    endCageSourceDogStmts ++ endCageSourceVowStmts ++
                                    endCageSourceSpotStmts)
                                  (s2 := endCageSourcePotStmts)
                                  (tail := endCageSourceCureStmts)
                                  hSrcSpot hPotBlock
                                  (by simp [endCageSourceBody_eq, endCageSourceCallStmts,
                                    List.append_assoc])
                              exact (endCageX_potNoCode hPotStart
                                  (by simpa [evmE5, evmE4, evmE3, evmE2, evmE1, evmE0, endCagePostStoresState, initState] using hPotCodeE))
                                |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
                            · have hPotCodeSNE :
                                  Reasoning.Theory.extCodeSizeWord evmS5.accountMap
                                    (endCageCallTargetWord ⟨5⟩ evmS5.accountMap
                                      evmS5.executionEnv) ≠ ⟨0⟩ := by
                                have hcodeS :=
                                  endCageCallTargetCodeSize_ne_accountMapEquiv
                                    (slot := ⟨5⟩) hState5.accountMap hPotCodeE
                                rw [hState5.executionEnv] at hcodeS
                                simpa [evmS5] using hcodeS
                              obtain ⟨gasPot, _, _, hPotReady⟩ :=
                                endCageX_potCallReady hPotStart
                                  (by simpa [evmE5, evmE4, evmE3, evmE2, evmE1, evmE0, endCagePostStoresState, initState] using hPotCodeE)
                              obtain ⟨cA6, σ6, z6, out6, Ain6, callGas6, _, _, hΘ6,
                                  rdPotPost, hout6⟩ :=
                                endCageX_potPostCall hPotReady hdepthLt
                              rcases hΘ6 with ⟨g6'', A6, hΘ6eq⟩
                              let evmE6 := { evmE5 with accountMap := σ6, substate := A6, createdAccounts := cA6 }
                              have hdepthNe5 : evmE5.executionEnv.depth ≠ 1024 := by
                                simpa [evmE5, evmE4, evmE3, evmE2, evmE1] using hdepthNe0
                              have hΘ6bridge :
                                  (cA6, σ6, g6'', A6, z6, out6) =
                                    Ethereum.EVM.Θ evmE5.executionEnv.blobVersionedHashes
                                      evmE5.createdAccounts evmE5.genesisBlockHeader
                                      evmE5.blocks evmE5.accountMap evmE5.σ₀ Ain6
                                      (AccountAddress.ofUInt256
                                        (UInt256.ofNat evmE5.executionEnv.codeOwner))
                                      evmE5.executionEnv.sender
                                      (AccountAddress.ofUInt256
                                        (endCageCallTargetWord ⟨5⟩ evmE5.accountMap
                                          evmE5.executionEnv))
                                      (toExecute evmE5.accountMap
                                        (AccountAddress.ofUInt256
                                          (endCageCallTargetWord ⟨5⟩ evmE5.accountMap
                                            evmE5.executionEnv)))
                                      callGas6
                                      (UInt256.ofNat evmE5.executionEnv.gasPrice)
                                      ⟨0⟩ ⟨0⟩
                                      ((endCageCallCalldataMem
                                        (endRelyAuthHashMem
                                          evmE5.executionEnv)).readWithPadding
                                          endCageCallOutPtr.toNat endCageCallInSize.toNat)
                                      (evmE5.executionEnv.depth + 1)
                                      evmE5.executionEnv.header true := by
                                simpa [evmE5, evmE4, evmE3, evmE2, evmE1, evmE0,
                                  endCagePostStoresState, initState, storageStore_accountMap,
                                  storageStore_createdAccounts, storageStore_executionEnv,
                                  endCageStoredAccountMap, endCageTimestampWord, hperm] using hΘ6eq
                              obtain ⟨σ6s, A6s, hcall6Solm, hState6⟩ :=
                                endCageCallMadeBridge (slot := ⟨5⟩)
                                  (evmE := evmE5) (evmS := evmS5)
                                  (cA' := cA6) (σ' := σ6) (A' := A6) (Ain := Ain6)
                                  (z := z6) (out := out6) (g'' := g6'')
                                  (callGas := callGas6)
                                  hdepthNe5 hΘ6bridge hState5.accountMap
                                  (by simp [evmE5, evmS5, evmE4, evmS4, evmE3, evmS3,
                                    evmE2, evmS2, evmE1, evmS1, evmE0, evmS0, evmSolm,
                                    endCagePostStoresState, initState])
                                  (by simpa [evmE5, evmS5] using
                                    hState5.createdAccounts.symm)
                                  (by simp [evmE5, evmS5, evmE4, evmS4, evmE3, evmS3,
                                    evmE2, evmS2, evmE1, evmS1, evmE0, evmS0, evmSolm,
                                    endCagePostStoresState, initState])
                                  (by simp [evmE5, evmS5, evmE4, evmS4, evmE3, evmS3,
                                    evmE2, evmS2, evmE1, evmS1, evmE0, evmS0, evmSolm,
                                    endCagePostStoresState, initState])
                                  (by simpa [evmE5, evmS5] using
                                    hState5.executionEnv.symm)
                              let evmS6 := { evmS5 with accountMap := σ6s, substate := A6s, createdAccounts := cA6 }
                              cases z6
                              · have rdPotFail := rdPotPost
                                simp at rdPotFail
                                have hPotBlock :
                                    ExecBlock config
                                      { contract := contract, locals := lSpot } evmS5
                                      endCageSourcePotStmts .reverted := by
                                  simpa [endCageSourcePotStmts] using
                                    endCageCheckedCallFailed
                                      (evm := evmS5) (evm' := evmS6)
                                      (locals := lSpot)
                                      (ref := potRef)
                                      (er := ({ base := "pot", steps := [] } :
                                        EvaledStorageRef))
                                      (slot := ⟨5⟩) (retVar := "_potCage") (out := out6)
                                      (by simp [lSpot, lVow, lDog, lCat, lVat, l0,
                                        potRef])
                                      (by simp [evalStorageRef, evalStorageRefSteps, potRef,
                                        EvalResult.bind, pure, bind])
                                      (by simp [storageTypeAt?, contract, storageDecls, addrSt])
                                      (by rfl)
                                      hPotCodeSNE
                                      (by simpa [evmS6] using hcall6Solm)
                                have hbody :
                                    ExecTransitionBody config contract evmSolm ∅
                                      cageTransition.body .reverted :=
                                  mkRevert
                                    (s1 := endCageSourceStorePrefixStmts ++
                                      endCageSourceVatStmts ++ endCageSourceCatStmts ++
                                      endCageSourceDogStmts ++ endCageSourceVowStmts ++
                                      endCageSourceSpotStmts)
                                    (s2 := endCageSourcePotStmts)
                                    (tail := endCageSourceCureStmts)
                                    hSrcSpot hPotBlock
                                    (by simp [endCageSourceBody_eq, endCageSourceCallStmts,
                                      List.append_assoc])
                                exact (endCageX_potCallFailed rdPotFail hout6)
                                  |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
                              · have rdPotSucc := rdPotPost
                                simp at rdPotSucc
                                obtain ⟨_, _, rdPotClean0⟩ :=
                                  endCageX_potCallSucceeded rdPotSucc
                                obtain ⟨_, _, hCureStart⟩ := endCageX_potCleanup rdPotClean0
                                have hPotBlock :
                                    ExecBlock config
                                      { contract := contract, locals := lSpot } evmS5
                                      endCageSourcePotStmts
                                      (.ok { contract := contract, locals := lPot }
                                        evmS6) := by
                                  simpa [endCageSourcePotStmts, lPot] using
                                    endCageCheckedCallSuccess
                                      (evm := evmS5) (evm' := evmS6)
                                      (locals := lSpot)
                                      (ref := potRef)
                                      (er := ({ base := "pot", steps := [] } :
                                        EvaledStorageRef))
                                      (slot := ⟨5⟩) (retVar := "_potCage") (out := out6)
                                      (by simp [lSpot, lVow, lDog, lCat, lVat, l0,
                                        potRef])
                                      (by simp [evalStorageRef, evalStorageRefSteps, potRef,
                                        EvalResult.bind, pure, bind])
                                      (by simp [storageTypeAt?, contract, storageDecls, addrSt])
                                      (by rfl)
                                      hPotCodeSNE
                                      (by simpa [evmS6] using hcall6Solm)
                                have hSrcPot :
                                    ExecBlock config { contract := contract, locals := ∅ }
                                      evmSolm
                                      (endCageSourceStorePrefixStmts ++
                                        endCageSourceVatStmts ++ endCageSourceCatStmts ++
                                        endCageSourceDogStmts ++ endCageSourceVowStmts ++
                                        endCageSourceSpotStmts ++ endCageSourcePotStmts)
                                      (.ok { contract := contract, locals := lPot }
                                        evmS6) := by
                                  simpa [List.append_assoc] using
                                   .execBlock_append
                                      (s2 := endCageSourcePotStmts) hSrcSpot hPotBlock
                                by_cases hCureCodeE :
                                    Reasoning.Theory.extCodeSizeWord evmE6.accountMap
                                      (endCageCallTargetWord ⟨7⟩ evmE6.accountMap
                                        evmE6.executionEnv) = ⟨0⟩
                                · have hCureCodeS :
                                      Reasoning.Theory.extCodeSizeWord
                                        evmS6.accountMap
                                        (endCageCallTargetWord ⟨7⟩ evmS6.accountMap
                                          evmS6.executionEnv) = ⟨0⟩ := by
                                    have hcodeS :=
                                      endCageCallTargetCodeSize_zero_accountMapEquiv
                                        (slot := ⟨7⟩) hState6.accountMap hCureCodeE
                                    rw [hState6.executionEnv] at hcodeS
                                    simpa [evmS6] using hcodeS
                                  have hCureBlock :
                                      ExecBlock config
                                        { contract := contract, locals := lPot } evmS6
                                        endCageSourceCureStmts .reverted := by
                                    simpa [endCageSourceCureStmts] using
                                      endCageCheckedCallNoCode
                                        (evm := evmS6) (locals := lPot)
                                        (ref := cureRef)
                                        (er := ({ base := "cure", steps := [] } :
                                          EvaledStorageRef))
                                        (slot := ⟨7⟩) (retVar := "_cureCage")
                                        (by simp [lPot, lSpot, lVow, lDog, lCat, lVat,
                                          l0, cureRef])
                                        (by simp [evalStorageRef, evalStorageRefSteps,
                                          cureRef, EvalResult.bind, pure, bind])
                                        (by simp [storageTypeAt?, contract, storageDecls, addrSt])
                                        (by rfl)
                                        hCureCodeS
                                  have hbody :
                                      ExecTransitionBody config contract evmSolm ∅
                                        cageTransition.body .reverted :=
                                    mkRevert
                                      (s1 := endCageSourceStorePrefixStmts ++
                                        endCageSourceVatStmts ++ endCageSourceCatStmts ++
                                        endCageSourceDogStmts ++ endCageSourceVowStmts ++
                                        endCageSourceSpotStmts ++ endCageSourcePotStmts)
                                      (s2 := endCageSourceCureStmts)
                                      (tail := [])
                                      hSrcPot hCureBlock
                                      (by simp [endCageSourceBody_eq,
                                        endCageSourceCallStmts, List.append_assoc])
                                  exact (endCageX_cureNoCode hCureStart
                                      (by simpa [evmE6, evmE5, evmE4, evmE3, evmE2, evmE1, evmE0, endCagePostStoresState, initState] using hCureCodeE))
                                    |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
                                · have hCureCodeSNE :
                                      Reasoning.Theory.extCodeSizeWord
                                        evmS6.accountMap
                                        (endCageCallTargetWord ⟨7⟩ evmS6.accountMap
                                          evmS6.executionEnv) ≠ ⟨0⟩ := by
                                    have hcodeS :=
                                      endCageCallTargetCodeSize_ne_accountMapEquiv
                                        (slot := ⟨7⟩) hState6.accountMap hCureCodeE
                                    rw [hState6.executionEnv] at hcodeS
                                    simpa [evmS6] using hcodeS
                                  obtain ⟨gasCure, _, _, hCureReady⟩ :=
                                    endCageX_cureCallReady hCureStart
                                      (by simpa [evmE6, evmE5, evmE4, evmE3, evmE2, evmE1, evmE0, endCagePostStoresState, initState] using hCureCodeE)
                                  obtain ⟨cA7, σ7, z7, out7, Ain7, callGas7, _, _, hΘ7,
                                      rdCurePost, hout7⟩ :=
                                    endCageX_curePostCall hCureReady hdepthLt
                                  rcases hΘ7 with ⟨g7'', A7, hΘ7eq⟩
                                  let evmE7 := { evmE6 with accountMap := σ7, substate := A7, createdAccounts := cA7 }
                                  have hdepthNe6 : evmE6.executionEnv.depth ≠ 1024 := by
                                    simpa [evmE6, evmE5, evmE4, evmE3, evmE2, evmE1]
                                      using hdepthNe0
                                  have hΘ7bridge :
                                      (cA7, σ7, g7'', A7, z7, out7) =
                                        Ethereum.EVM.Θ
                                          evmE6.executionEnv.blobVersionedHashes
                                          evmE6.createdAccounts evmE6.genesisBlockHeader
                                          evmE6.blocks evmE6.accountMap evmE6.σ₀ Ain7
                                          (AccountAddress.ofUInt256
                                            (UInt256.ofNat
                                              evmE6.executionEnv.codeOwner))
                                          evmE6.executionEnv.sender
                                          (AccountAddress.ofUInt256
                                            (endCageCallTargetWord ⟨7⟩
                                              evmE6.accountMap evmE6.executionEnv))
                                          (toExecute evmE6.accountMap
                                            (AccountAddress.ofUInt256
                                              (endCageCallTargetWord ⟨7⟩
                                                evmE6.accountMap evmE6.executionEnv)))
                                          callGas7
                                          (UInt256.ofNat evmE6.executionEnv.gasPrice)
                                          ⟨0⟩ ⟨0⟩
                                          ((endCageCallCalldataMem
                                            (endRelyAuthHashMem
                                              evmE6.executionEnv)).readWithPadding
                                              endCageCallOutPtr.toNat
                                              endCageCallInSize.toNat)
                                          (evmE6.executionEnv.depth + 1)
                                          evmE6.executionEnv.header true := by
                                    simpa [evmE6, evmE5, evmE4, evmE3, evmE2, evmE1,
                                      evmE0, endCagePostStoresState, initState,
                                      storageStore_accountMap, storageStore_createdAccounts,
                                      storageStore_executionEnv, endCageStoredAccountMap,
                                      hperm] using hΘ7eq
                                  obtain ⟨σ7s, A7s, hcall7Solm, hState7⟩ :=
                                    endCageCallMadeBridge (slot := ⟨7⟩)
                                      (evmE := evmE6) (evmS := evmS6)
                                      (cA' := cA7) (σ' := σ7) (A' := A7)
                                      (Ain := Ain7) (z := z7) (out := out7)
                                      (g'' := g7'') (callGas := callGas7)
                                      hdepthNe6 hΘ7bridge hState6.accountMap
                                      (by simp [evmE6, evmS6, evmE5, evmS5, evmE4,
                                        evmS4, evmE3, evmS3, evmE2, evmS2, evmE1,
                                        evmS1, evmE0, evmS0, evmSolm,
                                        endCagePostStoresState, initState])
                                      (by simpa [evmE6, evmS6] using
                                        hState6.createdAccounts.symm)
                                      (by simp [evmE6, evmS6, evmE5, evmS5, evmE4,
                                        evmS4, evmE3, evmS3, evmE2, evmS2, evmE1,
                                        evmS1, evmE0, evmS0, evmSolm,
                                        endCagePostStoresState, initState])
                                      (by simp [evmE6, evmS6, evmE5, evmS5, evmE4,
                                        evmS4, evmE3, evmS3, evmE2, evmS2, evmE1,
                                        evmS1, evmE0, evmS0, evmSolm,
                                        endCagePostStoresState, initState])
                                      (by simpa [evmE6, evmS6] using
                                        hState6.executionEnv.symm)
                                  let evmS7 := { evmS6 with accountMap := σ7s, substate := A7s, createdAccounts := cA7 }
                                  cases z7
                                  · have rdCureFail := rdCurePost
                                    simp at rdCureFail
                                    have hCureBlock :
                                        ExecBlock config
                                          { contract := contract, locals := lPot } evmS6
                                          endCageSourceCureStmts .reverted := by
                                      simpa [endCageSourceCureStmts] using
                                        endCageCheckedCallFailed
                                          (evm := evmS6) (evm' := evmS7)
                                          (locals := lPot)
                                          (ref := cureRef)
                                          (er := ({ base := "cure", steps := [] } :
                                            EvaledStorageRef))
                                          (slot := ⟨7⟩) (retVar := "_cureCage")
                                          (out := out7)
                                          (by simp [lPot, lSpot, lVow, lDog, lCat, lVat,
                                            l0, cureRef])
                                          (by simp [evalStorageRef, evalStorageRefSteps,
                                            cureRef, EvalResult.bind, pure, bind])
                                          (by simp [storageTypeAt?, contract, storageDecls, addrSt])
                                          (by rfl)
                                          hCureCodeSNE
                                          (by simpa [evmS7] using hcall7Solm)
                                    have hbody :
                                        ExecTransitionBody config contract evmSolm ∅
                                          cageTransition.body .reverted :=
                                      mkRevert
                                        (s1 := endCageSourceStorePrefixStmts ++
                                          endCageSourceVatStmts ++
                                          endCageSourceCatStmts ++
                                          endCageSourceDogStmts ++
                                          endCageSourceVowStmts ++
                                          endCageSourceSpotStmts ++
                                          endCageSourcePotStmts)
                                        (s2 := endCageSourceCureStmts)
                                        (tail := [])
                                        hSrcPot hCureBlock
                                        (by simp [endCageSourceBody_eq,
                                          endCageSourceCallStmts, List.append_assoc])
                                    exact (endCageX_cureCallFailed rdCureFail hout7)
                                      |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
                                  · have rdCureSucc := rdCurePost
                                    simp at rdCureSucc
                                    obtain ⟨_, _, rd6300⟩ :=
                                      endCageX_cureCallSucceeded rdCureSucc
                                    have hCureBlock :
                                        ExecBlock config
                                          { contract := contract, locals := lPot } evmS6
                                          endCageSourceCureStmts
                                          (.ok { contract := contract, locals := lCure }
                                            evmS7) := by
                                      simpa [endCageSourceCureStmts, lCure] using
                                        endCageCheckedCallSuccess
                                          (evm := evmS6) (evm' := evmS7)
                                          (locals := lPot)
                                          (ref := cureRef)
                                          (er := ({ base := "cure", steps := [] } :
                                            EvaledStorageRef))
                                          (slot := ⟨7⟩) (retVar := "_cureCage")
                                          (out := out7)
                                          (by simp [lPot, lSpot, lVow, lDog, lCat, lVat,
                                            l0, cureRef])
                                          (by simp [evalStorageRef, evalStorageRefSteps,
                                            cureRef, EvalResult.bind, pure, bind])
                                          (by simp [storageTypeAt?, contract, storageDecls, addrSt])
                                          (by rfl)
                                          hCureCodeSNE
                                          (by simpa [evmS7] using hcall7Solm)
                                    have hSrcCure :
                                        ExecBlock config
                                          { contract := contract, locals := ∅ } evmSolm
                                          (endCageSourceStorePrefixStmts ++
                                            endCageSourceVatStmts ++
                                            endCageSourceCatStmts ++
                                            endCageSourceDogStmts ++
                                            endCageSourceVowStmts ++
                                            endCageSourceSpotStmts ++
                                            endCageSourcePotStmts ++
                                            endCageSourceCureStmts)
                                          (.ok { contract := contract, locals := lCure }
                                            evmS7) := by
                                      simpa [List.append_assoc] using
                                       .execBlock_append
                                          (s2 := endCageSourceCureStmts) hSrcPot
                                          hCureBlock
                                    have hbody :
                                        ExecTransitionBody config contract evmSolm ∅
                                          cageTransition.body
                                          (.returned
                                            { contract := contract, locals := lCure }
                                            evmS7 none) := by
                                      have hblock :
                                          ExecBlock config
                                            { contract := contract, locals := ∅ } evmSolm
                                            cageTransition.body
                                            (.ok { contract := contract, locals := lCure }
                                              evmS7) := by
                                        simpa [endCageSourceBody_eq,
                                          endCageSourceCallStmts, List.append_assoc] using
                                          hSrcCure
                                      simpa [ExecTransitionBody] using
                                        ExecFuncBody.execBlockOK hblock
                                    have hret := endCageX_finish hperm rd6300
                                    exact hret.reEquivExecutionGenEVMStateEquiv
                                      (evm'_evm := evmE7) (evm'_solm := evmS7)
                                      hcode hdispatch hdecode hbody
                                      (by simp [evmE7])
                                      (by simpa [evmE7] using accountMapEquiv.refl σ7)
                                      hState7
                                      (by
                                        simpa [cageTransition] using
                                          (returnEquiv.fallthrough
                                            (o := ByteArray.empty) (r := none) (t := [])
                                            (dvs := []) rfl (by native_decide)
                                            (by native_decide)))
        · rw [not_lt] at hdepthLt
          have hdepthEq : I.depth = 1024 :=
            Fin.ext (by have := I.depth.isLt; omega)
          obtain ⟨_, _, rdVatDepth⟩ :=
            endCageX_vatCallDepthLimit (acc := (cA, endCageStoredAccountMap σ_evm I))
              hVatReady hdepthEq
          have hcallDepth :
              typedCallViaEVM config evmS0
                (EVM.address
                  (endCageCallTargetAddr ⟨1⟩ evmS0.accountMap evmS0.executionEnv))
                "cage" 0 []
                (false,
                  { evmS0 with
                    substate :=
                      (evmS0.addAccessedAccount
                        (EVM.address
                          (endCageCallTargetAddr ⟨1⟩ evmS0.accountMap
                            evmS0.executionEnv))).substate },
                  ByteArray.empty) true := by
            simpa using
              endCageCallNotMadeDepthLimit evmS0 ⟨1⟩
                (by
                  simpa [evmS0, evmSolm, endCagePostStoresState, initState,
                    storageStore_executionEnv] using hdepthEq)
          have hVatBlock :
              ExecBlock config { contract := contract, locals := l0 } evmS0
                endCageSourceVatStmts .reverted := by
            simpa [endCageSourceVatStmts] using
              endCageCheckedCallFailed
                (evm := evmS0)
                (evm' :=
                  { evmS0 with
                    substate :=
                      (evmS0.addAccessedAccount
                        (EVM.address
                          (endCageCallTargetAddr ⟨1⟩ evmS0.accountMap
                            evmS0.executionEnv))).substate })
                (locals := l0)
                (ref := vatRef) (er := ({ base := "vat", steps := [] } : EvaledStorageRef))
                (slot := ⟨1⟩) (retVar := "_vatCage") (out := ByteArray.empty)
                (by simp [l0, vatRef])
                (by simp [evalStorageRef, evalStorageRefSteps, vatRef, EvalResult.bind,
                  pure, bind])
                (by simp [storageTypeAt?, contract, storageDecls, addrSt])
                (by rfl)
                hVatCodeSNE
                hcallDepth
          have hbody :
              ExecTransitionBody config contract evmSolm ∅ cageTransition.body .reverted :=
            mkRevert
              (s1 := endCageSourceStorePrefixStmts)
              (s2 := endCageSourceVatStmts)
              (tail := endCageSourceCatStmts ++ endCageSourceDogStmts ++
                endCageSourceVowStmts ++ endCageSourceSpotStmts ++
                endCageSourcePotStmts ++ endCageSourceCureStmts)
              hSrc0 (by simpa [l0] using hVatBlock)
              (by simp [endCageSourceBody_eq, endCageSourceCallStmts, List.append_assoc])
          exact (endCageX_vatCallFailed rdVatDepth (by native_decide))
            |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
    · have hliveSolm : endSlotWord ⟨8⟩ σ_solm I ≠ ⟨1⟩ := by
        intro hbad
        exact hlive (by
          have hword : endSlotWord ⟨8⟩ σ_evm I = endSlotWord ⟨8⟩ σ_solm I := by
            simpa [endSlotWord, solcSlotWord] using
              accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨8⟩ ⟨0⟩
          rw [hword]
          exact hbad)
      have hbody :
          ExecTransitionBody config contract evmSolm ∅ cageTransition.body .reverted := by
        simpa [evmSolm] using
          endCageSourceLiveReverts (cA := cA) (gh := gh) (bl := bl)
            (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
            hwv hauthSolm hliveSolm
      exact (endCageX_notLive hlive hLivePc)
        |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
  · have hauthSolm : endRelyAuthWord σ_solm I ≠ ⟨1⟩ := by
      intro hbad
      exact hauth (by
        have hword : endRelyAuthWord σ_evm I = endRelyAuthWord σ_solm I := by
          simpa [endRelyAuthWord, endSlotWord, solcSlotWord] using
            accountMapEquiv_storage_findD hAccounts I.codeOwner
              (endRelyAuthStorageSlot I) ⟨0⟩
        rw [hword]
        exact hbad)
    have hbody :
        ExecTransitionBody config contract evmSolm ∅ cageTransition.body .reverted := by
      simpa [evmSolm] using
        endCageSourceAuthReverts (cA := cA) (gh := gh) (bl := bl)
          (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
          hwv hauthSolm
    exact (endCageX_unauthorized hauth hAuthPc)
      |>.reEquivExecutionRevert hcode hdispatch hdecode hbody

end Benchmarks.Dss.End
