import Examples.UniswapV2Pair.RawCallSource
import Examples.UniswapV2Pair.SkimCommon
import Examples.UniswapV2Pair.SkimSafeTransferDynamicRuntime
import Examples.UniswapV2Pair.SkimDynamicSecondRuntime
import Examples.UniswapV2Pair.SkimSecondSafeTransferDynamicRuntime
import Examples.UniswapV2Pair.SkimSecondSafeTransferDynamicOffsetRuntime
import Examples.UniswapV2Pair.SkimSecondSafeTransferDynamicOffsetReturnRuntime
import Examples.UniswapV2Pair.SkimSecondSafeTransferDynamicCalldataRuntime
import Examples.UniswapV2Pair.SkimSource
import Reasoning.ExternalCall
import Ethereum.Theory.StaticStorage

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace UniswapV2Pair

/-! ## `skim(address)` refinement slices -/

theorem uniswapStorageStore_sigma0 (evm : EVM.State) (a : AccountAddress)
    (slot val : UInt256) :
    (Solm.EVM.storageStore evm a slot val).σ₀ = evm.σ₀ := by
  unfold Solm.EVM.storageStore State.lookupAccount
  cases evm.accountMap.find? a <;>
    simp [Option.option, State.setAccount, Account.updateStorage]

theorem uniswapStorageStore_genesisBlockHeader (evm : EVM.State) (a : AccountAddress)
    (slot val : UInt256) :
    (Solm.EVM.storageStore evm a slot val).genesisBlockHeader = evm.genesisBlockHeader := by
  unfold Solm.EVM.storageStore State.lookupAccount
  cases evm.accountMap.find? a <;>
    simp [Option.option, State.setAccount, Account.updateStorage]

theorem uniswapStorageStore_blocks (evm : EVM.State) (a : AccountAddress)
    (slot val : UInt256) :
    (Solm.EVM.storageStore evm a slot val).blocks = evm.blocks := by
  unfold Solm.EVM.storageStore State.lookupAccount
  cases evm.accountMap.find? a <;>
    simp [Option.option, State.setAccount, Account.updateStorage]

theorem uniswapStorageStore_substate (evm : EVM.State) (a : AccountAddress)
    (slot val : UInt256) :
    (Solm.EVM.storageStore evm a slot val).substate = evm.substate := by
  unfold Solm.EVM.storageStore State.lookupAccount
  cases evm.accountMap.find? a <;>
    simp [Option.option, State.setAccount, Account.updateStorage]


theorem uniswapSkimBalanceOfDecode_ok {returndata : ByteArray} (hlo : 32 ≤ returndata.size) :
    config.externalABI.decode? "balanceOf" returndata =
      some [skimBalanceValue
        (UInt256.ofNat (fromByteArrayBigEndian (returndata.extract 0 32)))] := by
  have hword :
      (UInt256.ofNat (fromByteArrayBigEndian (returndata.extract 0 32))).toNat =
        fromByteArrayBigEndian (returndata.extract 0 32) := by
    exact UInt256.toNat_ofNat_of_lt (fromByteArrayBigEndian_extract0_32_lt hlo)
  change uniswapExternalABI.decode? "balanceOf" returndata = _
  rw [show
      some [skimBalanceValue
        (UInt256.ofNat (fromByteArrayBigEndian (returndata.extract 0 32)))] =
      some [(.int (Int.ofNat (fromByteArrayBigEndian (returndata.extract 0 32))))] by
      simp only [skimBalanceValue, uniswapUint256Value, uint256Value, hword]]
  simpa [uniswapExternalABI, uint256, uint256Int, abiUInt256] using
    (decodeReturnValueWithMode_legacy_uint256_ok (returndata := returndata) hlo)

theorem uniswapSkimBalanceTypedCallFromState_source
    {cA1 gh bl σ1 σ₀ I} {evm1S : EVM.State}
    {cA2 : Batteries.RBSet AccountAddress compare} {σ2 : AccountMap}
    {z2 : Bool} {out2 calldataMem : ByteArray} {A_in2 : Substate}
    {callGas2 targetWord inOff : UInt256}
    (hPost : accountMapEquiv σ1 evm1S.accountMap)
    (hcreated : evm1S.createdAccounts = cA1)
    (hσ0 : evm1S.σ₀ = σ₀)
    (hgenesis : evm1S.genesisBlockHeader = gh)
    (hblocks : evm1S.blocks = bl)
    (henv : evm1S.executionEnv = I)
    (hdepth : I.depth.val < 1024)
    (hcd :
      config.externalABI.encode? "balanceOf" [.address I.codeOwner] =
        some (calldataMem.readWithPadding inOff.toNat 36))
    (hΘ :
      ∃ (g'' : UInt256) (A'_evm : Substate),
        (cA2, σ2, g'', A'_evm, z2, out2) =
          Ethereum.EVM.Θ I.blobVersionedHashes cA1 gh bl σ1 σ₀ A_in2
            (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner.val)) I.sender
            (AccountAddress.ofUInt256 targetWord)
            (toExecute σ1 (AccountAddress.ofUInt256 targetWord))
            callGas2 (UInt256.ofNat I.gasPrice) ⟨0⟩ ⟨0⟩
            (calldataMem.readWithPadding inOff.toNat 36)
            (I.depth + 1) I.header false) :
    ∃ evm2S : EVM.State,
      typedCallViaEVM config evm1S
        (AccountAddress.ofUInt256 targetWord)
        "balanceOf" 0 [.address evm1S.executionEnv.codeOwner]
        (z2, evm2S, out2) false ∧
      accountMapEquiv σ2 evm2S.accountMap ∧
      evm2S.createdAccounts = cA2 ∧
      evm2S.σ₀ = σ₀ ∧
      evm2S.genesisBlockHeader = gh ∧
      evm2S.blocks = bl ∧
      evm2S.executionEnv = evm1S.executionEnv := by
  obtain ⟨g'', A'_evm, hΘeq⟩ := hΘ
  let evmE : EVM.State :=
    { evm1S with
      accountMap := σ1
      createdAccounts := cA1
      σ₀ := σ₀
      genesisBlockHeader := gh
      blocks := bl
      executionEnv := I }
  let target : EVM.Address := AccountAddress.ofUInt256 targetWord
  have hdepthE : evmE.executionEnv.depth.val < 1024 := by
    simpa [evmE] using hdepth
  have hdepthNe : evmE.executionEnv.depth ≠ 1024 := by
    intro hEq
    rw [hEq] at hdepthE
    exact absurd hdepthE (by decide)
  have hcdE :
      config.externalABI.encode? "balanceOf" [.address evmE.executionEnv.codeOwner] =
        some (calldataMem.readWithPadding inOff.toNat 36) := by
    simpa [evmE] using hcd
  have hΘE :
      (cA2, σ2, g'', A'_evm, z2, out2) =
        Ethereum.EVM.Θ evmE.executionEnv.blobVersionedHashes
          evmE.createdAccounts evmE.genesisBlockHeader evmE.blocks evmE.accountMap evmE.σ₀ A_in2
          (AccountAddress.ofUInt256 (UInt256.ofNat evmE.executionEnv.codeOwner))
          evmE.executionEnv.sender target
          (toExecute evmE.accountMap target)
          callGas2 (UInt256.ofNat evmE.executionEnv.gasPrice) ⟨0⟩ ⟨0⟩
          (calldataMem.readWithPadding inOff.toNat 36)
          (evmE.executionEnv.depth + 1) evmE.executionEnv.header false := by
    simpa [evmE, target] using hΘeq
  obtain ⟨σ2S, A2S, hcallSolm, hPost2⟩ :=
    typedCallViaEVM_callMade_accountMapEquiv
      (cfg := config) (evm_evm := evmE) (evm_solm := evm1S)
      (tgt := target) (targetWord := targetWord)
      (name := "balanceOf") (args := [.address evmE.executionEnv.codeOwner])
      (cA' := cA2) (σ' := σ2) (A' := A'_evm) (A_in := A_in2)
      (z := z2) (out := out2) (g'' := g'') (callGas := callGas2)
      (mem := calldataMem) (inOff := inOff) (inSize := ⟨36⟩) (callPerm := false)
      hdepthNe rfl hcdE hΘE
      (by simpa [evmE] using hPost)
      (by simp [evmE, hσ0])
      (by simp [evmE, hcreated])
      (by simp [evmE, hgenesis])
      (by simp [evmE, hblocks])
      (by simp [evmE])
      (by simp [evmE, henv])
  let evm2S : EVM.State :=
    { evm1S with
      accountMap := σ2S
      substate := A2S
      createdAccounts := cA2 }
  refine ⟨evm2S, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [evm2S, evmE, target, henv] using hcallSolm
  · simpa [evm2S] using hPost2
  · simp [evm2S]
  · simp [evm2S, hσ0]
  · simp [evm2S, hgenesis]
  · simp [evm2S, hblocks]
  · simp [evm2S]

theorem uniswapSkimFirstBalanceTypedCall_source
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {cA' : Batteries.RBSet AccountAddress compare} {σ' : AccountMap}
    {z : Bool} {o : ByteArray} {A_in : Substate} {callGas : UInt256}
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hdepth : I.depth.val < 1024)
    (hΘ :
      ∃ (g'' : UInt256) (A'_evm : Substate),
        (cA', σ', g'', A'_evm, z, o) = Ethereum.EVM.Θ I.blobVersionedHashes cA gh bl
          (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) σ₀ A_in
          (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner.val)) I.sender
          (AccountAddress.ofUInt256
            (UInt256.land solcAddrMask
              (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I)))
          (toExecute (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩)
            (AccountAddress.ofUInt256
              (UInt256.land solcAddrMask
                (uniswapSlotWord ⟨6⟩
                  (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I))))
          callGas (UInt256.ofNat I.gasPrice) ⟨0⟩ ⟨0⟩
          ((balanceOfThisCalldataMem (UInt256.ofNat I.codeOwner.val)).readWithPadding 128 36)
          (I.depth + 1) I.header false) :
    ∃ evm0S : EVM.State,
      typedCallViaEVM config
        (uniswapLockEnteredState
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I))
        (EVM.address
          (uniswapAddressAtSlot
            (uniswapLockEnteredState
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)) ⟨6⟩))
        "balanceOf" 0
        [.address
          (uniswapLockEnteredState
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)).executionEnv.codeOwner]
        (z, evm0S, o) false ∧
      accountMapEquiv σ' evm0S.accountMap ∧
      evm0S.createdAccounts = cA' ∧
      evm0S.σ₀ = σ₀ ∧
      evm0S.genesisBlockHeader = gh ∧
      evm0S.blocks = bl ∧
      evm0S.executionEnv =
        (uniswapLockEnteredState
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)).executionEnv := by
  let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmSL := uniswapLockEnteredState evmS
  let σLockE := sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩
  let σLockS := sstoreAccountMap I.codeOwner σ_solm ⟨12⟩ ⟨0⟩
  let token0WordE := uniswapSlotWord ⟨6⟩ σLockE I
  let token0WordS := uniswapSlotWord ⟨6⟩ σLockS I
  let token0CleanE := UInt256.land solcAddrMask token0WordE
  let target : EVM.Address := AccountAddress.ofUInt256 token0CleanE
  have hLockAccounts : accountMapEquiv σLockE σLockS := by
    exact accountMapEquiv_sstoreAccountMap I.codeOwner ⟨12⟩ ⟨0⟩ hAccounts
  have hslot : token0WordE = token0WordS := by
    simpa [σLockE, σLockS, token0WordE, token0WordS] using
      accountMapEquiv_storage_findD hLockAccounts I.codeOwner ⟨6⟩ ⟨0⟩
  have htargetSource :
      target = EVM.address (uniswapAddressAtSlot evmSL ⟨6⟩) := by
    have haddr :
        AccountAddress.ofUInt256 token0CleanE =
          uniswapAddressAtSlot evmSL ⟨6⟩ := by
      simpa [target, token0CleanE, token0WordE, token0WordS, σLockS, evmSL, evmS,
        uniswapLockEnteredState, uniswapUnlockedState, initState, storageStore_accountMap,
        storageStore_executionEnv, State.lookupAccount, Account.lookupStorage, Solm.EVM.storageLoad,
        uniswapAddressAtSlot, uniswapSlotWord, hslot, accountAddress_ofUInt256_eq_ofNat_toNat,
        u256_land_comm]
    change AccountAddress.ofUInt256 token0CleanE =
      EVM.address (uniswapAddressAtSlot evmSL ⟨6⟩)
    rw [haddr]
    exact (uniswapAddress_self (uniswapAddressAtSlot evmSL ⟨6⟩)).symm
  have hcd :
      config.externalABI.encode? "balanceOf" [.address I.codeOwner] =
        some ((balanceOfThisCalldataMem (UInt256.ofNat I.codeOwner.val))
          |>.readWithPadding 128 36) := by
    exact balanceOfThisCalldataMem_encode I.codeOwner
  have hLockStateAccounts : accountMapEquiv σLockE evmSL.accountMap := by
    simpa [evmSL, evmS, σLockS,
      uniswapLockEnteredState, uniswapUnlockedState, initState,
      storageStore_accountMap] using hLockAccounts
  obtain ⟨evm0S, hcallSolm, hPostAccounts, hcreated0, hσ0, hgenesis0, hblocks0, henv0⟩ :=
    uniswapSkimBalanceTypedCallFromState_source
      (cA1 := cA) (gh := gh) (bl := bl) (σ1 := σLockE) (σ₀ := σ₀)
      (I := I) (evm1S := evmSL) (cA2 := cA') (σ2 := σ')
      (z2 := z) (out2 := o) (A_in2 := A_in) (callGas2 := callGas)
      (targetWord := token0CleanE)
      (calldataMem := balanceOfThisCalldataMem (UInt256.ofNat I.codeOwner.val))
      (inOff := ⟨128⟩)
      hLockStateAccounts
      (by simp [evmSL, evmS, uniswapLockEnteredState, uniswapUnlockedState, initState,
        storageStore_createdAccounts])
      (by simp [evmSL, evmS, uniswapLockEnteredState, uniswapUnlockedState, initState,
        uniswapStorageStore_sigma0])
      (by simp [evmSL, evmS, uniswapLockEnteredState, uniswapUnlockedState, initState,
        uniswapStorageStore_genesisBlockHeader])
      (by simp [evmSL, evmS, uniswapLockEnteredState, uniswapUnlockedState, initState,
        uniswapStorageStore_blocks])
      (by simp [evmSL, evmS, uniswapLockEnteredState, uniswapUnlockedState, initState,
        storageStore_executionEnv])
      hdepth hcd hΘ
  have htargetSource' :
      AccountAddress.ofUInt256 token0CleanE =
        EVM.address (uniswapAddressAtSlot evmSL ⟨6⟩) := by
    simpa [target] using htargetSource
  refine ⟨evm0S, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [evmSL, evmS, htargetSource'] using hcallSolm
  · exact hPostAccounts
  · exact hcreated0
  · exact hσ0
  · exact hgenesis0
  · exact hblocks0
  · simpa [evmSL, evmS] using henv0

theorem uniswapSkimFirstBalanceReturn_source
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {cA' : Batteries.RBSet AccountAddress compare} {σ' : AccountMap}
    {z : Bool} {o : ByteArray} {A_in : Substate} {callGas : UInt256}
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hdepth : I.depth.val < 1024)
    (hΘ :
      ∃ (g'' : UInt256) (A'_evm : Substate),
        (cA', σ', g'', A'_evm, z, o) = Ethereum.EVM.Θ I.blobVersionedHashes cA gh bl
          (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) σ₀ A_in
          (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner.val)) I.sender
          (AccountAddress.ofUInt256
            (UInt256.land solcAddrMask
              (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I)))
          (toExecute (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩)
            (AccountAddress.ofUInt256
              (UInt256.land solcAddrMask
                (uniswapSlotWord ⟨6⟩
                  (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I))))
          callGas (UInt256.ofNat I.gasPrice) ⟨0⟩ ⟨0⟩
          ((balanceOfThisCalldataMem (UInt256.ofNat I.codeOwner.val)).readWithPadding 128 36)
          (I.depth + 1) I.header false)
    (hz : z = true) (ho32 : 32 ≤ o.size) :
    ∃ (evm0S : EVM.State) (balance0 : UInt256),
      typedCallViaEVM config
        (uniswapLockEnteredState
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I))
        (EVM.address
          (uniswapAddressAtSlot
            (uniswapLockEnteredState
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)) ⟨6⟩))
        "balanceOf" 0
        [.address
          (uniswapLockEnteredState
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)).executionEnv.codeOwner]
        (true, evm0S, o) false ∧
      config.externalABI.decode? "balanceOf" o = some [skimBalanceValue balance0] ∧
      accountMapEquiv σ' evm0S.accountMap ∧
      evm0S.createdAccounts = cA' ∧
      evm0S.σ₀ = σ₀ ∧
      evm0S.genesisBlockHeader = gh ∧
      evm0S.blocks = bl ∧
      evm0S.executionEnv =
        (uniswapLockEnteredState
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)).executionEnv ∧
      uniswapReserve0Word evm0S = UInt256.land (uniswapSlotWord ⟨8⟩ σ' I) reserve112Mask ∧
      balance0 = UInt256.ofNat (fromByteArrayBigEndian (o.extract 0 32)) := by
  obtain ⟨evm0S, hcallAll, hPostAccounts, hcreated0, hσ0, hgenesis0, hblocks0,
    henv0⟩ :=
    uniswapSkimFirstBalanceTypedCall_source
      (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
      (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
      (cA' := cA') (σ' := σ') (z := z) (o := o)
      (A_in := A_in) (callGas := callGas) hAccounts hdepth hΘ
  let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let balance0 := UInt256.ofNat (fromByteArrayBigEndian (o.extract 0 32))
  have hcall0 : typedCallViaEVM config (uniswapLockEnteredState evmS)
      (EVM.address (uniswapAddressAtSlot (uniswapLockEnteredState evmS) ⟨6⟩))
      "balanceOf" 0 [.address (uniswapLockEnteredState evmS).executionEnv.codeOwner]
      (true, evm0S, o) false := by
    simpa [evmS, hz] using hcallAll
  have hdecode :
      config.externalABI.decode? "balanceOf" o = some [skimBalanceValue balance0] := by
    simpa [balance0] using uniswapSkimBalanceOfDecode_ok (returndata := o) ho32
  have howner : evm0S.executionEnv.codeOwner = I.codeOwner := by
    have henv := typedCallViaEVM_executionEnv_eq hcall0
    simpa [evmS, uniswapLockEnteredState, uniswapUnlockedState, initState,
      storageStore_executionEnv] using congrArg ExecutionEnv.codeOwner henv
  have hslot := accountMapEquiv_storage_findD hPostAccounts I.codeOwner ⟨8⟩ ⟨0⟩
  have hreserve :
      uniswapReserve0Word evm0S = UInt256.land (uniswapSlotWord ⟨8⟩ σ' I) reserve112Mask := by
    simpa [uniswapReserve0Word, Solm.EVM.storageLoad, State.lookupAccount,
      Account.lookupStorage, uniswapSlotWord, howner] using
      (congrArg (fun w => UInt256.land w reserve112Mask) hslot).symm
  exact ⟨evm0S, balance0, hcall0, hdecode, hPostAccounts, hcreated0, hσ0, hgenesis0,
    hblocks0, henv0, hreserve, rfl⟩

theorem uniswapSkimFirstBalanceStaticReserve0
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {evm0S : EVM.State} {target : EVM.Address} {name : Ident}
    {args : List Value} {out0 : ByteArray} {z : Bool}
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hcall0 : typedCallViaEVM config
      (uniswapLockEnteredState
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I))
      target name 0 args (z, evm0S, out0) false) :
    uniswapReserve0Word evm0S =
      UInt256.land
        (uniswapSlotWord ⟨8⟩ (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I)
        reserve112Mask := by
  let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmL := uniswapLockEnteredState evmS
  let σLockE := sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩
  let σLockS := sstoreAccountMap I.codeOwner σ_solm ⟨12⟩ ⟨0⟩
  have hLockAccounts : accountMapEquiv σLockE σLockS :=
    accountMapEquiv_sstoreAccountMap I.codeOwner ⟨12⟩ ⟨0⟩ hAccounts
  have hLockStateAccounts : accountMapEquiv σLockE evmL.accountMap := by
    simpa [evmL, evmS, σLockS, uniswapLockEnteredState, uniswapUnlockedState, initState,
      storageStore_accountMap] using hLockAccounts
  have hslot :=
    typedCallViaEVM_static_storage_findD_of_accountMapEquiv
      (cfg := config) (σ := σLockE) (evm := evmL) (evm' := evm0S)
      (slot := ⟨8⟩) (default := ⟨0⟩) hLockStateAccounts hcall0
  simpa [uniswapReserve0Word, Solm.EVM.storageLoad, State.lookupAccount,
    Account.lookupStorage, uniswapSlotWord, σLockE, evmL, evmS,
    uniswapLockEnteredState, uniswapUnlockedState, initState, storageStore_executionEnv] using
    congrArg (fun w => UInt256.land w reserve112Mask) hslot

theorem uniswapSkimSecondBalanceTypedCall_source
    {cA1 gh bl σ1 σ₀ I} {evm1S : EVM.State}
    {cA2 : Batteries.RBSet AccountAddress compare} {σ2 : AccountMap}
    {z2 : Bool} {out2 : ByteArray} {A_in2 : Substate} {callGas2 : UInt256}
    {o : ByteArray} {toWord value token1 : UInt256}
    (hPost : accountMapEquiv σ1 evm1S.accountMap)
    (hcreated : evm1S.createdAccounts = cA1)
    (hσ0 : evm1S.σ₀ = σ₀)
    (hgenesis : evm1S.genesisBlockHeader = gh)
    (hblocks : evm1S.blocks = bl)
    (henv : evm1S.executionEnv = I)
    (hdepth : I.depth.val < 1024)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hΘ :
      ∃ (g'' : UInt256) (A'_evm : Substate),
        (cA2, σ2, g'', A'_evm, z2, out2) = Ethereum.EVM.Θ I.blobVersionedHashes cA1
          gh bl σ1 σ₀ A_in2
          (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner.val)) I.sender
          (AccountAddress.ofUInt256 (UInt256.land token1 solcAddrMask))
          (toExecute σ1 (AccountAddress.ofUInt256 (UInt256.land token1 solcAddrMask)))
          callGas2 (UInt256.ofNat I.gasPrice) ⟨0⟩ ⟨0⟩
          ((skimSecondBalanceCalldataMem (UInt256.ofNat I.codeOwner.val) o toWord value)
            |>.readWithPadding 292 36)
          (I.depth + 1) I.header false) :
    ∃ evm2S : EVM.State,
      typedCallViaEVM config evm1S
        (AccountAddress.ofUInt256 (UInt256.land token1 solcAddrMask))
        "balanceOf" 0 [.address evm1S.executionEnv.codeOwner]
        (z2, evm2S, out2) false ∧
      accountMapEquiv σ2 evm2S.accountMap ∧
      evm2S.createdAccounts = cA2 ∧
      evm2S.σ₀ = σ₀ ∧
      evm2S.genesisBlockHeader = gh ∧
      evm2S.blocks = bl ∧
      evm2S.executionEnv = evm1S.executionEnv := by
  have hcd :
      config.externalABI.encode? "balanceOf" [.address I.codeOwner] =
        some ((skimSecondBalanceCalldataMem (UInt256.ofNat I.codeOwner.val) o toWord value)
          |>.readWithPadding 292 36) := by
    exact skimSecondBalanceCalldataMem_encode I.codeOwner toWord value ho32 hoSize
  exact uniswapSkimBalanceTypedCallFromState_source
    (targetWord := UInt256.land token1 solcAddrMask)
    (calldataMem := skimSecondBalanceCalldataMem (UInt256.ofNat I.codeOwner.val) o toWord value)
    (inOff := ⟨292⟩)
    hPost hcreated hσ0 hgenesis hblocks henv hdepth hcd hΘ

theorem uniswapSkimSecondBalanceTypedCall_source_dynamic
    {cA1 gh bl σ1 σ₀ I} {evm1S : EVM.State}
    {cA2 : Batteries.RBSet AccountAddress compare} {σ2 : AccountMap}
    {z2 : Bool} {out2 : ByteArray} {A_in2 : Substate} {callGas2 : UInt256}
    {o out1 : ByteArray} {toWord value token1 : UInt256}
    (hPost : accountMapEquiv σ1 evm1S.accountMap)
    (hcreated : evm1S.createdAccounts = cA1)
    (hσ0 : evm1S.σ₀ = σ₀)
    (hgenesis : evm1S.genesisBlockHeader = gh)
    (hblocks : evm1S.blocks = bl)
    (henv : evm1S.executionEnv = I)
    (hdepth : I.depth.val < 1024)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hout1Ne : out1.size ≠ 0) (hout1Size : out1.size < 2 ^ 255)
    (hΘ :
      ∃ (g'' : UInt256) (A'_evm : Substate),
        (cA2, σ2, g'', A'_evm, z2, out2) = Ethereum.EVM.Θ I.blobVersionedHashes cA1
          gh bl σ1 σ₀ A_in2
          (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner.val)) I.sender
          (AccountAddress.ofUInt256 (UInt256.land token1 solcAddrMask))
          (toExecute σ1 (AccountAddress.ofUInt256 (UInt256.land token1 solcAddrMask)))
          callGas2 (UInt256.ofNat I.gasPrice) ⟨0⟩ ⟨0⟩
          ((skimSecondBalanceDynamicCalldataMem (UInt256.ofNat I.codeOwner.val) o
              toWord value out1)
            |>.readWithPadding (skimSafeTransferReturnDataPtr out1).toNat 36)
          (I.depth + 1) I.header false) :
    ∃ evm2S : EVM.State,
      typedCallViaEVM config evm1S
        (AccountAddress.ofUInt256 (UInt256.land token1 solcAddrMask))
        "balanceOf" 0 [.address evm1S.executionEnv.codeOwner]
        (z2, evm2S, out2) false ∧
      accountMapEquiv σ2 evm2S.accountMap ∧
      evm2S.createdAccounts = cA2 ∧
      evm2S.σ₀ = σ₀ ∧
      evm2S.genesisBlockHeader = gh ∧
      evm2S.blocks = bl ∧
      evm2S.executionEnv = evm1S.executionEnv := by
  have hcd :
      config.externalABI.encode? "balanceOf" [.address I.codeOwner] =
        some ((skimSecondBalanceDynamicCalldataMem (UInt256.ofNat I.codeOwner.val) o
            toWord value out1)
          |>.readWithPadding (skimSafeTransferReturnDataPtr out1).toNat 36) := by
    exact skimSecondBalanceDynamicCalldataMem_encode I.codeOwner toWord value
      ho32 hoSize hout1Ne hout1Size
  exact uniswapSkimBalanceTypedCallFromState_source
    (targetWord := UInt256.land token1 solcAddrMask)
    (calldataMem := skimSecondBalanceDynamicCalldataMem (UInt256.ofNat I.codeOwner.val) o
      toWord value out1)
    (inOff := skimSafeTransferReturnDataPtr out1)
    hPost hcreated hσ0 hgenesis hblocks henv hdepth hcd hΘ

theorem uniswapSkimSecondBalanceStaticReserve1 {σ1 : AccountMap}
    {evm1S evm2S : EVM.State} {I : ExecutionEnv}
    {target : EVM.Address} {args : List Value} {z2 : Bool} {out2 : ByteArray}
    (hPost : accountMapEquiv σ1 evm1S.accountMap)
    (henv : evm1S.executionEnv = I)
    (hcall1 : typedCallViaEVM config evm1S target "balanceOf" 0 args
      (z2, evm2S, out2) false) :
    uniswapReserve1Word evm2S =
      UInt256.land
        (UInt256.div (uniswapSlotWord ⟨8⟩ σ1 I) reserve112Shift)
        reserve112Mask := by
  have hslot :=
    typedCallViaEVM_static_storage_findD_of_accountMapEquiv
      (cfg := config) (σ := σ1) (evm := evm1S) (evm' := evm2S)
      (slot := ⟨8⟩) (default := ⟨0⟩) hPost hcall1
  simpa [uniswapReserve1Word, Solm.EVM.storageLoad, State.lookupAccount,
    Account.lookupStorage, uniswapSlotWord, henv] using
    congrArg (fun w => UInt256.land (UInt256.div w reserve112Shift) reserve112Mask) hslot

theorem accountAddressOfNat_word_eq_mask (w : UInt256) :
    UInt256.ofNat (AccountAddress.ofNat w.toNat).val = UInt256.land solcAddrMask w := by
  apply u256_inj
  rw [u256_land_toNat]
  rw [show solcAddrMask.toNat = 2 ^ 160 - 1 by native_decide]
  rw [nat_land_comm, nat_land_mask_eq_mod]
  have hleft :
      (UInt256.ofNat (AccountAddress.ofNat w.toNat).val).toNat = w.toNat % 2 ^ 160 := by
    simp only [AccountAddress.ofNat, UInt256.ofNat, UInt256.toNat, Fin.ofNat]
    change (w.toNat % AccountAddress.size) % UInt256.size = w.toNat % 2 ^ 160
    have hlt : w.toNat % AccountAddress.size < UInt256.size := by
      exact lt_of_lt_of_le (Nat.mod_lt w.toNat (show 0 < AccountAddress.size by decide))
        (show AccountAddress.size ≤ UInt256.size by decide)
    rw [Nat.mod_eq_of_lt hlt]
    simp [AccountAddress.size]
  have hright : w.toNat % 2 ^ 160 % UInt256.size = w.toNat % 2 ^ 160 := by
    rw [Nat.mod_eq_of_lt]
    exact lt_trans (Nat.mod_lt w.toNat (show 0 < 2 ^ 160 by norm_num))
      (by norm_num [UInt256.size])
  rw [hright]
  exact hleft

theorem skimToAddress_word_eq_mask (I : ExecutionEnv) :
    UInt256.ofNat (skimToAddress I).val = UInt256.land solcAddrMask (skimToWord I) := by
  simpa [skimToAddress] using accountAddressOfNat_word_eq_mask (skimToWord I)

theorem skimToAddress_word_eq_masked (I : ExecutionEnv) :
    UInt256.ofNat (skimToAddress I).val =
      UInt256.land solcAddrMask (skimToMaskedWord I) := by
  rw [skimToAddress_word_eq_mask I, skimToMaskedWord]
  rw [u256_land_comm solcAddrMask (skimToWord I)]
  exact (solcAddrMask_clean_left (solcAddrMask_result_canonical (skimToWord I))).symm

theorem skimExcess0Word_eq_sub_of_reserve {evm : EVM.State} {balance0 reserve0 : UInt256}
    (hreserve : uniswapReserve0Word evm = reserve0)
    (hle : reserve0.toNat ≤ balance0.toNat) :
    skimExcess0Word evm balance0 = UInt256.sub balance0 reserve0 := by
  simpa [skimExcess0Word, hreserve] using skimExcessWord_eq_sub (reserve := reserve0) hle

theorem skimExcess1Word_eq_sub_of_reserve {evm : EVM.State} {balance1 reserve1 : UInt256}
    (hreserve : uniswapReserve1Word evm = reserve1)
    (hle : reserve1.toNat ≤ balance1.toNat) :
    skimExcess1Word evm balance1 = UInt256.sub balance1 reserve1 := by
  simpa [skimExcess1Word, hreserve] using skimExcessWord_eq_sub (reserve := reserve1) hle

theorem skimFirstSafeTransferCalldata {evm0S : EVM.State}
    {I : ExecutionEnv} {balance0 reserve0 toWord : UInt256}
    (hto : UInt256.ofNat (skimToAddress I).val = UInt256.land solcAddrMask toWord)
    (hreserve : uniswapReserve0Word evm0S = reserve0)
    (hle : reserve0.toNat ≤ balance0.toNat) :
    transferCalldata? (skimToAddress I) (skimExcess0Word evm0S balance0) =
      some ((transferCalldataMem (UInt256.land solcAddrMask toWord)
        (UInt256.sub balance0 reserve0)).readWithPadding 128 68) := by
  have hexcess : skimExcess0Word evm0S balance0 = UInt256.sub balance0 reserve0 :=
    skimExcess0Word_eq_sub_of_reserve hreserve hle
  simpa [transferCalldata?, transferCallArgs, hexcess, hto] using
    transferCalldataMem_encode (skimToAddress I) (skimExcess0Word evm0S balance0)

theorem skimSecondSafeTransferCalldata {evm2S : EVM.State}
    {I : ExecutionEnv} {o out2 : ByteArray} {balance1 reserve1 prevValue toWord : UInt256}
    (hto : UInt256.ofNat (skimToAddress I).val = UInt256.land solcAddrMask toWord)
    (hreserve : uniswapReserve1Word evm2S = reserve1)
    (hle : reserve1.toNat ≤ balance1.toNat)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hout32 : 32 ≤ out2.size) (houtSize : out2.size < UInt256.size) :
    transferCalldata? (skimToAddress I) (skimExcess1Word evm2S balance1) =
      some ((skimSecondSafeTransferCallMem2 (UInt256.ofNat I.codeOwner.val) o toWord
        prevValue out2 (UInt256.sub balance1 reserve1)).readWithPadding 456 68) := by
  have hexcess : skimExcess1Word evm2S balance1 = UInt256.sub balance1 reserve1 :=
    skimExcess1Word_eq_sub_of_reserve hreserve hle
  rw [skimSecondSafeTransferCallMem2_read456_68
    (UInt256.ofNat I.codeOwner.val) toWord prevValue (UInt256.sub balance1 reserve1)
    ho32 hoSize hout32 houtSize]
  simpa [transferCalldata?, transferCallArgs, hexcess, hto] using
    transferCalldataMem_encode (skimToAddress I) (skimExcess1Word evm2S balance1)

theorem skimSecondSafeTransferCalldata_dynamic {evm2S : EVM.State}
    {I : ExecutionEnv} {o out1 out2 : ByteArray}
    {balance1 reserve1 prevValue toWord : UInt256}
    (hto : UInt256.ofNat (skimToAddress I).val = UInt256.land solcAddrMask toWord)
    (hreserve : uniswapReserve1Word evm2S = reserve1)
    (hle : reserve1.toNat ≤ balance1.toNat)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hout1Ne : out1.size ≠ 0) (hout1Size : out1.size < 2 ^ 255)
    (hout32 : 32 ≤ out2.size) (houtSize : out2.size < UInt256.size) :
    transferCalldata? (skimToAddress I) (skimExcess1Word evm2S balance1) =
      some ((skimSecondSafeTransferDynamicCallMem2 (UInt256.ofNat I.codeOwner.val) o
        toWord prevValue out1 out2 (UInt256.sub balance1 reserve1)).readWithPadding
        (skimSecondSafeTransferDynamicCallPtr out1).toNat 68) := by
  have hexcess : skimExcess1Word evm2S balance1 = UInt256.sub balance1 reserve1 :=
    skimExcess1Word_eq_sub_of_reserve hreserve hle
  rw [skimSecondSafeTransferDynamicCallMem2_read_callPtr_68
    (UInt256.ofNat I.codeOwner.val) toWord prevValue
    (UInt256.sub balance1 reserve1) ho32 hoSize hout1Ne hout1Size hout32 houtSize]
  simpa [transferCalldata?, transferCallArgs, hexcess, hto] using
    transferCalldataMem_encode (skimToAddress I) (skimExcess1Word evm2S balance1)

theorem skimToken1GuardAfterFirstTransfer_false {σ : AccountMap}
    {evm evm0 evm1 : EVM.State} {I : ExecutionEnv} {balance0 token1 : UInt256}
    (hPost : accountMapEquiv σ evm1.accountMap)
    (htarget :
      AccountAddress.ofUInt256 (UInt256.land token1 solcAddrMask) =
        uniswapAddressAtSlot (uniswapLockEnteredState evm) ⟨7⟩)
    (hnoCode : extCodeSizeWord σ (UInt256.land token1 solcAddrMask) = ⟨0⟩) :
    evalExpr? config
      { contract := contract, locals := skimFirstSafeTransferStore evm evm0 I balance0 } evm1
      (.binary .gt (.extCodeSize (.var "_token1")) (.intLit 0)) = .ok (.bool false) := by
  let target := UInt256.land token1 solcAddrMask
  let addr := uniswapAddressAtSlot (uniswapLockEnteredState evm) ⟨7⟩
  have hsame := extCodeSizeWord_accountMapEquiv hPost target
  have hnoEvm : extCodeSizeWord evm1.accountMap target = ⟨0⟩ := by
    rw [← hsame]
    exact hnoCode
  have hcodeWord :
      EVM.Word.ofNat ((evm1.lookupAccount addr).option 0 (fun acc => acc.code.size)) = ⟨0⟩ := by
    change EVM.Word.ofNat
      ((evm1.accountMap.find? addr).option 0 (fun acc => acc.code.size)) = ⟨0⟩
    cases hacc : evm1.accountMap.find? addr with
    | none =>
        rfl
    | some acc =>
        have hnoAcc : UInt256.ofNat acc.code.size = ⟨0⟩ := by
          simpa [target, addr, htarget, extCodeSizeWord, hacc] using hnoEvm
        simpa [hacc] using hnoAcc
  have hvar :
      evalExpr? config
        { contract := contract, locals := skimFirstSafeTransferStore evm evm0 I balance0 } evm1
        (.var "_token1") = .ok (.address addr) := by
    simpa [addr, evalExpr?, EvalResult.ofOption] using
      skimFirstSafeTransferStore_token1 evm evm0 I balance0
  change
    evalExpr? config
      { contract := contract, locals := skimFirstSafeTransferStore evm evm0 I balance0 } evm1
      (.binary .gt (.extCodeSize (.var "_token1")) (.intLit 0)) = .ok (.bool false)
  simp [evalExpr?, hvar, EvalResult.bind, bind, pure, evalBinaryOp?, hcodeWord]

theorem skimToken1GuardAfterFirstTransfer_true {σ : AccountMap}
    {evm evm0 evm1 : EVM.State} {I : ExecutionEnv} {balance0 token1 : UInt256}
    (hPost : accountMapEquiv σ evm1.accountMap)
    (htarget :
      AccountAddress.ofUInt256 (UInt256.land token1 solcAddrMask) =
        uniswapAddressAtSlot (uniswapLockEnteredState evm) ⟨7⟩)
    (hcode : extCodeSizeWord σ (UInt256.land token1 solcAddrMask) ≠ ⟨0⟩) :
    evalExpr? config
      { contract := contract, locals := skimFirstSafeTransferStore evm evm0 I balance0 } evm1
      (.binary .gt (.extCodeSize (.var "_token1")) (.intLit 0)) = .ok (.bool true) := by
  let target := UInt256.land token1 solcAddrMask
  let addr := uniswapAddressAtSlot (uniswapLockEnteredState evm) ⟨7⟩
  have hsame := extCodeSizeWord_accountMapEquiv hPost target
  have hcodeEvm : extCodeSizeWord evm1.accountMap target ≠ ⟨0⟩ := by
    intro hzero
    apply hcode
    rw [hsame]
    exact hzero
  have hcodeWord :
      EVM.Word.ofNat ((evm1.lookupAccount addr).option 0 (fun acc => acc.code.size)) ≠ ⟨0⟩ := by
    change EVM.Word.ofNat
      ((evm1.accountMap.find? addr).option 0 (fun acc => acc.code.size)) ≠ ⟨0⟩
    intro hzero
    apply hcodeEvm
    cases hacc : evm1.accountMap.find? addr with
    | none =>
        unfold extCodeSizeWord
        rw [show AccountAddress.ofUInt256 target = addr by simpa [target, addr] using htarget,
          hacc]
        rfl
    | some acc =>
        have hzeroAcc : UInt256.ofNat acc.code.size = ⟨0⟩ := by
          simpa [hacc] using hzero
        simpa [target, addr, htarget, extCodeSizeWord, hacc] using hzeroAcc
  have hpositive :
      0 <
        (EVM.Word.ofNat ((evm1.lookupAccount addr).option 0 (fun acc => acc.code.size))).toNat :=
    Nat.pos_of_ne_zero (by
      intro hzeroNat
      apply hcodeWord
      apply u256_inj
      simpa using hzeroNat)
  have hvar :
      evalExpr? config
        { contract := contract, locals := skimFirstSafeTransferStore evm evm0 I balance0 } evm1
        (.var "_token1") = .ok (.address addr) := by
    simpa [addr, evalExpr?, EvalResult.ofOption] using
      skimFirstSafeTransferStore_token1 evm evm0 I balance0
  change
    evalExpr? config
      { contract := contract, locals := skimFirstSafeTransferStore evm evm0 I balance0 } evm1
      (.binary .gt (.extCodeSize (.var "_token1")) (.intLit 0)) = .ok (.bool true)
  simp [evalExpr?, hvar, EvalResult.bind, bind, pure, evalBinaryOp?]
  exact hpositive

theorem skimToken0GuardFalse_initState_of_noCode
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : Sat256}
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (htoken0NoCode :
      extCodeSizeWord (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩)
        (UInt256.land solcAddrMask
          (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I)) =
        ⟨0⟩) :
    skimToken0GuardFalse (initState cA gh bl σ_solm σ₀ g A I) I := by
  let σLockE := sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩
  let σLockS := sstoreAccountMap I.codeOwner σ_solm ⟨12⟩ ⟨0⟩
  let token0WordE := uniswapSlotWord ⟨6⟩ σLockE I
  let token0WordS := uniswapSlotWord ⟨6⟩ σLockS I
  have hLockAccounts : accountMapEquiv σLockE σLockS := by
    exact accountMapEquiv_sstoreAccountMap I.codeOwner ⟨12⟩ ⟨0⟩ hAccounts
  have hslot : token0WordE = token0WordS := by
    simpa [σLockE, σLockS, token0WordE, token0WordS] using
      accountMapEquiv_storage_findD hLockAccounts I.codeOwner ⟨6⟩ ⟨0⟩
  have hnoSolm :
      extCodeSizeWord σLockS (UInt256.land solcAddrMask token0WordS) = ⟨0⟩ := by
    have hsame :=
      extCodeSizeWord_accountMapEquiv hLockAccounts
        (UInt256.land solcAddrMask token0WordE)
    have hnoE :
        extCodeSizeWord σLockE (UInt256.land solcAddrMask token0WordE) = ⟨0⟩ := by
      simpa [σLockE, token0WordE] using htoken0NoCode
    rw [← hslot]
    rw [← hsame]
    exact hnoE
  unfold skimToken0GuardFalse
  let evmS := initState cA gh bl σ_solm σ₀ g A I
  let evmL := uniswapLockEnteredState evmS
  have hstorage :
      evalExpr? config { contract := contract, locals := skimStore I } evmL
        (.storage token0Ref) = .ok (.address (uniswapAddressAtSlot evmL ⟨6⟩)) := by
    exact evalExpr_uniswap_storage_address evmL (skimStore I)
      (er := { base := "token0", steps := [] }) (slot := ⟨6⟩)
      (by simp [skimStore, token0Ref])
      (by simp [evalStorageRef, evalStorageRefSteps, token0Ref, EvalResult.bind, pure, bind])
      (by decide) (by rfl)
  have hnoSource :
      (evmL.lookupAccount (uniswapAddressAtSlot evmL ⟨6⟩)).option (⟨0⟩ : UInt256)
          (fun acc => EVM.Word.ofNat acc.code.size) =
        ⟨0⟩ := by
    have hnoSolmRight :
        extCodeSizeWord σLockS (UInt256.land token0WordS solcAddrMask) = ⟨0⟩ := by
      simpa [u256_land_comm] using hnoSolm
    simpa [evmL, evmS, uniswapLockEnteredState, uniswapUnlockedState, initState,
      storageStore_accountMap, storageStore_executionEnv, State.lookupAccount, Solm.EVM.storageLoad,
      Account.lookupStorage, uniswapAddressAtSlot, extCodeSizeWord, uniswapSlotWord, σLockS,
      token0WordS, accountAddress_ofUInt256_eq_ofNat_toNat] using hnoSolmRight
  have hnoSourceWord :
      EVM.Word.ofNat
          ((evmL.lookupAccount (uniswapAddressAtSlot evmL ⟨6⟩)).option 0
            (fun acc => acc.code.size)) =
        ⟨0⟩ := by
    cases hacc : evmL.lookupAccount (uniswapAddressAtSlot evmL ⟨6⟩) with
    | none =>
        exact UInt256_ofNat_0
    | some acc =>
        simpa [hacc, Option.option] using hnoSource
  change
    evalExpr? config { contract := contract, locals := skimStore I } evmL
      (.binary .gt (.extCodeSize (.storage token0Ref)) (.intLit 0)) =
        .ok (.bool false)
  simp [evalExpr?, hstorage, EvalResult.bind, bind, pure, evalBinaryOp?, hnoSourceWord]

theorem skimToken0GuardTrue_initState_of_code
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : Sat256}
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (htoken0Code :
      extCodeSizeWord (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩)
        (UInt256.land solcAddrMask
          (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I)) ≠
        ⟨0⟩) :
    skimToken0GuardTrue (initState cA gh bl σ_solm σ₀ g A I) I := by
  let σLockE := sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩
  let σLockS := sstoreAccountMap I.codeOwner σ_solm ⟨12⟩ ⟨0⟩
  let token0WordE := uniswapSlotWord ⟨6⟩ σLockE I
  let token0WordS := uniswapSlotWord ⟨6⟩ σLockS I
  have hLockAccounts : accountMapEquiv σLockE σLockS := by
    exact accountMapEquiv_sstoreAccountMap I.codeOwner ⟨12⟩ ⟨0⟩ hAccounts
  have hslot : token0WordE = token0WordS := by
    simpa [σLockE, σLockS, token0WordE, token0WordS] using
      accountMapEquiv_storage_findD hLockAccounts I.codeOwner ⟨6⟩ ⟨0⟩
  have hcodeSolm :
      extCodeSizeWord σLockS (UInt256.land solcAddrMask token0WordS) ≠ ⟨0⟩ := by
    have hsame :=
      extCodeSizeWord_accountMapEquiv hLockAccounts
        (UInt256.land solcAddrMask token0WordE)
    have hcodeE :
        extCodeSizeWord σLockE (UInt256.land solcAddrMask token0WordE) ≠ ⟨0⟩ := by
      simpa [σLockE, token0WordE] using htoken0Code
    intro hzero
    apply hcodeE
    rw [hsame]
    rwa [hslot]
  unfold skimToken0GuardTrue
  let evmS := initState cA gh bl σ_solm σ₀ g A I
  let evmL := uniswapLockEnteredState evmS
  have hstorage :
      evalExpr? config { contract := contract, locals := skimStore I } evmL
        (.storage token0Ref) = .ok (.address (uniswapAddressAtSlot evmL ⟨6⟩)) := by
    exact evalExpr_uniswap_storage_address evmL (skimStore I)
      (er := { base := "token0", steps := [] }) (slot := ⟨6⟩)
      (by simp [skimStore, token0Ref])
      (by simp [evalStorageRef, evalStorageRefSteps, token0Ref, EvalResult.bind, pure, bind])
      (by decide) (by rfl)
  have hcodeSource :
      (evmL.lookupAccount (uniswapAddressAtSlot evmL ⟨6⟩)).option (⟨0⟩ : UInt256)
          (fun acc => EVM.Word.ofNat acc.code.size) ≠
        ⟨0⟩ := by
    have hcodeSolmRight :
        extCodeSizeWord σLockS (UInt256.land token0WordS solcAddrMask) ≠ ⟨0⟩ := by
      simpa [u256_land_comm] using hcodeSolm
    simpa [evmL, evmS, uniswapLockEnteredState, uniswapUnlockedState, initState,
      storageStore_accountMap, storageStore_executionEnv, State.lookupAccount, Solm.EVM.storageLoad,
      Account.lookupStorage, uniswapAddressAtSlot, extCodeSizeWord, uniswapSlotWord, σLockS,
      token0WordS, accountAddress_ofUInt256_eq_ofNat_toNat] using hcodeSolmRight
  have hcodeSourceWord :
      EVM.Word.ofNat
          ((evmL.lookupAccount (uniswapAddressAtSlot evmL ⟨6⟩)).option 0
            (fun acc => acc.code.size)) ≠
        ⟨0⟩ := by
    intro hzero
    cases hacc : evmL.lookupAccount (uniswapAddressAtSlot evmL ⟨6⟩) with
    | none =>
        exact hcodeSource (by simp [hacc, Option.option])
    | some acc =>
        exact hcodeSource (by simpa [hacc, Option.option] using hzero)
  have hpositive :
      0 <
        (EVM.Word.ofNat
          ((evmL.lookupAccount (uniswapAddressAtSlot evmL ⟨6⟩)).option 0
            (fun acc => acc.code.size))).toNat := by
    have hnz :
        (EVM.Word.ofNat
            ((evmL.lookupAccount (uniswapAddressAtSlot evmL ⟨6⟩)).option 0
              (fun acc => acc.code.size))).toNat ≠
          0 := by
      intro hz
      apply hcodeSourceWord
      apply u256_inj
      simpa using hz
    simpa using Nat.pos_of_ne_zero hnz
  change
    evalExpr? config { contract := contract, locals := skimStore I } evmL
      (.binary .gt (.extCodeSize (.storage token0Ref)) (.intLit 0)) =
        .ok (.bool true)
  simp [evalExpr?, hstorage, EvalResult.bind, bind, pure, evalBinaryOp?]
  exact hpositive

theorem uniswapSkimBodyCoreRevert_locked
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (maskFn : UInt256 → UInt256)
    (hcode : I.code = uniswapV2PairBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hlocked :
      (σ_evm.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨12⟩ ⟨0⟩)) ≠
        ⟨1⟩)
    (hdispatch : dispatchMsg contract I.calldata = some skimTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (skimTransition.params.map Param.name)
        (transitionSignature skimTransition).paramTypes I.calldata = some (skimStore I))
    (hRuntime :
      RDrev uniswapV2PairBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let _toWord := maskFn (skimToWord I)
  have hlockedSolm :
      Solm.EVM.storageLoad evmS evmS.executionEnv.codeOwner ⟨12⟩ ≠ ⟨1⟩ := by
    simpa [evmS] using
      (initState_codeOwner_storageLoad_ne_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
        (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
        (slot := ⟨12⟩) (val := ⟨1⟩) hAccounts hlocked)
  have hbody :
      ExecTransitionBody config contract evmS (skimStore I) skimTransition.body .reverted := by
    exact uniswapSkimBodyReverts_locked evmS I
      (by simp only [evmS, initState]; exact hwv)
      hlockedSolm
  exact hRuntime.reEquivExecutionRevert hcode hdispatch hdecode hbody

/-- Short-calldata decode-failure refinement slice for `skim(address)`.

The `skim` transition uses legacy address decoding, so non-canonical words are accepted at the
source level. The success path still needs the longer masked wrapper trace; the early locked and
first-no-code reverts are handled separately below.
-/
theorem uniswapSkimBodyCoreDecodeFailed_short
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36)
    (hdispatch : dispatchMsg contract I.calldata = some skimTransition)
    (hreach : ∃ k C, RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1286⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hdec := uniswapDecode_skim_none_short (I := I) hsz4 hshort
  exact (uniswapSkimX_shortarg (g := Sat256.ofUInt256 g)
      hsz4 hsize hshort hreach)
    |>.reEquivDecodingFailed hcode hdispatch hdec

theorem uniswapSkimBodyCoreRevert_firstNoCode
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (maskFn : UInt256 → UInt256)
    (hcode : I.code = uniswapV2PairBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hunlocked :
      (σ_evm.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD ⟨12⟩ ⟨0⟩)) = ⟨1⟩)
    (htoken0NoCode :
      extCodeSizeWord (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩)
        (UInt256.land solcAddrMask
          (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I)) =
        ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some skimTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (skimTransition.params.map Param.name)
        (transitionSignature skimTransition).paramTypes I.calldata = some (skimStore I))
    (hRuntime :
      RDrev uniswapV2PairBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let _toWord := maskFn (skimToWord I)
  have hunlockedSolm :
      Solm.EVM.storageLoad evmS evmS.executionEnv.codeOwner ⟨12⟩ = ⟨1⟩ := by
    have hword := accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨12⟩ ⟨0⟩
    simpa [evmS, initState, Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage]
      using (hword ▸ hunlocked)
  have hguard0 : skimToken0GuardFalse evmS I :=
    skimToken0GuardFalse_initState_of_noCode hAccounts htoken0NoCode
  have hbody :
      ExecTransitionBody config contract evmS (skimStore I) skimTransition.body .reverted := by
    exact uniswapSkimBodyReverts_firstNoCode evmS I
      (by simp only [evmS, initState]; exact hwv)
      hunlockedSolm hguard0
  exact hRuntime.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem uniswapSkimBodyCoreRevert_firstCallDepth
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (maskFn : UInt256 → UInt256)
    (hcode : I.code = uniswapV2PairBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hdepth : I.depth = 1024)
    (hunlocked :
      (σ_evm.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD ⟨12⟩ ⟨0⟩)) = ⟨1⟩)
    (htoken0Code :
      extCodeSizeWord (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩)
        (UInt256.land solcAddrMask
          (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I)) ≠
        ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some skimTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (skimTransition.params.map Param.name)
        (transitionSignature skimTransition).paramTypes I.calldata = some (skimStore I))
    (hRuntime :
      RDrev uniswapV2PairBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmL := uniswapLockEnteredState evmS
  let target := EVM.address (uniswapAddressAtSlot evmL ⟨6⟩)
  let _toWord := maskFn (skimToWord I)
  have hunlockedSolm :
      Solm.EVM.storageLoad evmS evmS.executionEnv.codeOwner ⟨12⟩ = ⟨1⟩ := by
    have hword := accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨12⟩ ⟨0⟩
    simpa [evmS, initState, Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage]
      using (hword ▸ hunlocked)
  have hguard0 : skimToken0GuardTrue evmS I :=
    skimToken0GuardTrue_initState_of_code hAccounts htoken0Code
  have hdepthSolm : evmL.executionEnv.depth = 1024 := by
    simpa [evmL, evmS, uniswapLockEnteredState, uniswapUnlockedState, initState,
      storageStore_executionEnv] using hdepth
  have hcall0 : typedCallViaEVM config evmL target "balanceOf" 0
      [.address evmL.executionEnv.codeOwner]
      (false, { evmL with substate := (evmL.addAccessedAccount target).substate },
        ByteArray.empty) false := by
    exact callNotMade_depthLimit
      (cfg := config) (evm := evmL) (tgt := target)
      (name := "balanceOf") (args := [.address evmL.executionEnv.codeOwner])
      (callPerm := false)
      (balanceOfThisCalldataMem_encode evmL.executionEnv.codeOwner)
      hdepthSolm
  have hbody :
      ExecTransitionBody config contract evmS (skimStore I) skimTransition.body .reverted := by
    exact uniswapSkimBodyReverts_firstCallFailure evmS
      { evmL with substate := (evmL.addAccessedAccount target).substate } I
      (by simp only [evmS, initState]; exact hwv)
      hunlockedSolm hguard0 hcall0
  exact hRuntime.reEquivExecutionRevert hcode hdispatch hdecode hbody

/-- Locked-revert `skim(address)` refinement slice, packaged from selector dispatch through the
body core. -/
theorem uniswapSkimBodyRevert_locked
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (maskFn : UInt256 → UInt256)
    (hcode : I.code = uniswapV2PairBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hlocked :
      (σ_evm.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨12⟩ ⟨0⟩)) ≠
        ⟨1⟩)
    (hdispatch : dispatchMsg contract I.calldata = some skimTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (skimTransition.params.map Param.name)
        (transitionSignature skimTransition).paramTypes I.calldata = some (skimStore I))
    (hRuntime :
      RDrev uniswapV2PairBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  exact uniswapSkimBodyCoreRevert_locked maskFn hcode hwv hlocked hdispatch hdecode
    hRuntime hAccounts

/-- Short-calldata decode-failure `skim(address)` refinement slice, packaged from selector
dispatch through the body core. -/
theorem uniswapSkimBodyDecodeFailed_short
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩) (hsel : selIs I ⟨#[0xbc, 0x25, 0xcf, 0x77]⟩)
    (hshort : I.calldata.size < 36)
    (hdispatch : dispatchMsg contract I.calldata = some skimTransition) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I ⟨#[0xbc, 0x25, 0xcf, 0x77]⟩ rfl hsel
  exact uniswapSkimBodyCoreDecodeFailed_short hcode hsize hsz4 hshort hdispatch
    (uniswapReachSkimBody (g := Sat256.ofUInt256 g) hcode hwv hsz4 hsize hsel)

theorem uniswapSkimBodyRevert_firstNoCode
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (maskFn : UInt256 → UInt256)
    (hcode : I.code = uniswapV2PairBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hunlocked :
      (σ_evm.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD ⟨12⟩ ⟨0⟩)) = ⟨1⟩)
    (htoken0NoCode :
      extCodeSizeWord (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩)
        (UInt256.land solcAddrMask
          (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I)) =
        ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some skimTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (skimTransition.params.map Param.name)
        (transitionSignature skimTransition).paramTypes I.calldata = some (skimStore I))
    (hRuntime :
      RDrev uniswapV2PairBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  exact uniswapSkimBodyCoreRevert_firstNoCode maskFn hcode hwv hunlocked htoken0NoCode
    hdispatch hdecode hRuntime hAccounts

end UniswapV2Pair
