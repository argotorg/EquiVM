import Examples.UniswapV2Pair.Sync
import Reasoning.ExternalCall

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace UniswapV2Pair

theorem balanceCallStorageStore_sigma0
    (evm : EVM.State) (a : AccountAddress) (slot val : UInt256) :
    (Solm.EVM.storageStore evm a slot val).σ₀ = evm.σ₀ := by
  unfold Solm.EVM.storageStore State.lookupAccount
  cases evm.accountMap.find? a with
  | none => rfl
  | some acc =>
      change (State.setAccount evm a (acc.updateStorage slot val)).σ₀ = evm.σ₀
      rfl

theorem balanceCallStorageStore_genesisBlockHeader
    (evm : EVM.State) (a : AccountAddress) (slot val : UInt256) :
    (Solm.EVM.storageStore evm a slot val).genesisBlockHeader = evm.genesisBlockHeader := by
  unfold Solm.EVM.storageStore State.lookupAccount
  cases evm.accountMap.find? a with
  | none => rfl
  | some acc =>
      change
        (State.setAccount evm a (acc.updateStorage slot val)).genesisBlockHeader =
          evm.genesisBlockHeader
      rfl

theorem balanceCallStorageStore_blocks
    (evm : EVM.State) (a : AccountAddress) (slot val : UInt256) :
    (Solm.EVM.storageStore evm a slot val).blocks = evm.blocks := by
  unfold Solm.EVM.storageStore State.lookupAccount
  cases evm.accountMap.find? a with
  | none => rfl
  | some acc =>
      change (State.setAccount evm a (acc.updateStorage slot val)).blocks = evm.blocks
      rfl

theorem balanceCallAddress_self (a : AccountAddress) : EVM.address a.val = a := by
  apply Fin.ext
  show a.val % EVM.addressModulus = a.val
  rw [show EVM.addressModulus = AccountAddress.size from by decide]
  exact Nat.mod_eq_of_lt a.isLt

theorem uniswapBalanceOfDecode_ok {returndata : ByteArray} (hlo : 32 ≤ returndata.size) :
    config.externalABI.decode? "balanceOf" returndata =
      some [uniswapUint256Value
        (UInt256.ofNat (fromByteArrayBigEndian (returndata.extract 0 32)))] := by
  let n := fromByteArrayBigEndian (returndata.extract 0 32)
  have hword :
      (UInt256.ofNat n).toNat = n := by
    exact UInt256.toNat_ofNat_of_lt (fromByteArrayBigEndian_extract0_32_lt hlo)
  have hret :
      some [uniswapUint256Value (UInt256.ofNat n)] =
        some [Value.int (Int.ofNat n)] := by
    change some [Value.int (Int.ofNat (UInt256.ofNat n).toNat)] =
      some [Value.int (Int.ofNat n)]
    rw [hword]
  have hdecode :
      ABI.decodeReturnValueWithMode? DecodeMode.legacySolc05 uint256 returndata =
        some (Value.int (Int.ofNat n)) := by
    change
      ABI.decodeReturnValueWithMode? DecodeMode.legacySolc05 abiUInt256 returndata =
        some (Value.int (Int.ofNat n))
    exact decodeReturnValueWithMode_legacy_uint256_ok (returndata := returndata) hlo
  change uniswapExternalABI.decode? "balanceOf" returndata =
    some [uniswapUint256Value (UInt256.ofNat n)]
  rw [hret]
  change
    (if "balanceOf" = "balanceOf" then
        (ABI.decodeReturnValueWithMode? DecodeMode.legacySolc05 uint256 returndata).map
          (fun v => [v])
      else if "balanceOf" = "transfer" then
        decodeOptionalBoolOrEmpty? returndata
      else if "balanceOf" = "feeTo" then
        (ABI.decodeReturnValueWithMode? DecodeMode.legacySolc05 addr returndata).map (fun v => [v])
      else if "balanceOf" = "uniswapV2Call" then
        some []
      else if "balanceOf" = "ecrecover" then
        (ABI.decodeReturnValueWithMode? DecodeMode.legacySolc05 addr returndata).map (fun v => [v])
      else
        none) = some [Value.int (Int.ofNat n)]
  rw [if_pos rfl, hdecode]
  rfl

theorem uniswapBalanceTypedCallFromState_source
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
          (AccountAddress.ofUInt256 (UInt256.ofNat evmE.executionEnv.codeOwner.val))
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

theorem uniswapFirstBalanceTypedCall_source
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
    exact (balanceCallAddress_self (uniswapAddressAtSlot evmSL ⟨6⟩)).symm
  have hcd :
      config.externalABI.encode? "balanceOf" [.address I.codeOwner] =
        some ((balanceOfThisCalldataMem (UInt256.ofNat I.codeOwner.val))
          |>.readWithPadding 128 36) := by
    exact balanceOfThisCalldataMem_encode I.codeOwner
  have hLockStateAccounts : accountMapEquiv σLockE evmSL.accountMap := by
    simpa [evmSL, evmS, σLockS, uniswapLockEnteredState, uniswapUnlockedState, initState,
      storageStore_accountMap] using hLockAccounts
  obtain ⟨evm0S, hcallSolm, hPostAccounts, hcreated0, hσ0, hgenesis0, hblocks0, henv0⟩ :=
    uniswapBalanceTypedCallFromState_source
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
        balanceCallStorageStore_sigma0])
      (by simp [evmSL, evmS, uniswapLockEnteredState, uniswapUnlockedState, initState,
        balanceCallStorageStore_genesisBlockHeader])
      (by simp [evmSL, evmS, uniswapLockEnteredState, uniswapUnlockedState, initState,
        balanceCallStorageStore_blocks])
      (by simp [evmSL, evmS, uniswapLockEnteredState, uniswapUnlockedState, initState,
        storageStore_executionEnv])
      hdepth hcd hΘ
  have htargetSource' :
      AccountAddress.ofUInt256 token0CleanE =
        EVM.address (uniswapAddressAtSlot evmSL ⟨6⟩) := by
    simpa [target] using htargetSource
  refine ⟨evm0S, ?_, hPostAccounts, hcreated0, hσ0, hgenesis0, hblocks0, ?_⟩
  · simpa [evmSL, evmS, htargetSource'] using hcallSolm
  · simpa [evmSL, evmS] using henv0

theorem uniswapSyncSecondBalanceTypedCall_source
    {cA1 gh bl σ1 σ₀ I} {evm0S : EVM.State}
    {cA2 : Batteries.RBSet AccountAddress compare} {σ2 : AccountMap}
    {z2 : Bool} {out2 : ByteArray} {A_in2 : Substate} {callGas2 : UInt256}
    {o : ByteArray}
    (hPost : accountMapEquiv σ1 evm0S.accountMap)
    (hcreated : evm0S.createdAccounts = cA1)
    (hσ0 : evm0S.σ₀ = σ₀)
    (hgenesis : evm0S.genesisBlockHeader = gh)
    (hblocks : evm0S.blocks = bl)
    (henv : evm0S.executionEnv = I)
    (hdepth : I.depth.val < 1024)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hΘ :
      ∃ (g'' : UInt256) (A'_evm : Substate),
        (cA2, σ2, g'', A'_evm, z2, out2) = Ethereum.EVM.Θ I.blobVersionedHashes cA1
          gh bl σ1 σ₀ A_in2
          (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner.val)) I.sender
          (AccountAddress.ofUInt256
            (UInt256.land solcAddrMask (uniswapSlotWord ⟨7⟩ σ1 I)))
          (toExecute σ1
            (AccountAddress.ofUInt256
              (UInt256.land solcAddrMask (uniswapSlotWord ⟨7⟩ σ1 I))))
          callGas2 (UInt256.ofNat I.gasPrice) ⟨0⟩ ⟨0⟩
          ((balanceOfThisRebuiltCalldataMem (UInt256.ofNat I.codeOwner.val) o)
            |>.readWithPadding 128 36)
          (I.depth + 1) I.header false) :
    ∃ evm1S : EVM.State,
      typedCallViaEVM config evm0S
        (EVM.address (uniswapAddressAtSlot evm0S ⟨7⟩))
        "balanceOf" 0 [.address evm0S.executionEnv.codeOwner]
        (z2, evm1S, out2) false ∧
      accountMapEquiv σ2 evm1S.accountMap ∧
      evm1S.createdAccounts = cA2 ∧
      evm1S.σ₀ = σ₀ ∧
      evm1S.genesisBlockHeader = gh ∧
      evm1S.blocks = bl ∧
      evm1S.executionEnv = evm0S.executionEnv := by
  let token1WordE := uniswapSlotWord ⟨7⟩ σ1 I
  let token1CleanE := UInt256.land solcAddrMask token1WordE
  have hslot :
      token1WordE =
        Solm.EVM.storageLoad evm0S evm0S.executionEnv.codeOwner ⟨7⟩ := by
    simpa [token1WordE, uniswapSlotWord, Solm.EVM.storageLoad, State.lookupAccount,
      Account.lookupStorage, henv] using
      accountMapEquiv_storage_findD hPost I.codeOwner ⟨7⟩ ⟨0⟩
  have htargetSource :
      AccountAddress.ofUInt256 token1CleanE =
        EVM.address (uniswapAddressAtSlot evm0S ⟨7⟩) := by
    have haddr :
        AccountAddress.ofUInt256 token1CleanE =
          uniswapAddressAtSlot evm0S ⟨7⟩ := by
      simpa [token1CleanE, token1WordE, uniswapAddressAtSlot, hslot,
        accountAddress_ofUInt256_eq_ofNat_toNat, u256_land_comm]
    rw [haddr]
    exact (balanceCallAddress_self (uniswapAddressAtSlot evm0S ⟨7⟩)).symm
  have hcd :
      config.externalABI.encode? "balanceOf" [.address I.codeOwner] =
        some ((balanceOfThisRebuiltCalldataMem (UInt256.ofNat I.codeOwner.val) o)
          |>.readWithPadding 128 36) := by
    exact balanceOfThisRebuiltCalldataMem_encode I.codeOwner o ho32 hoSize
  obtain ⟨evm1S, hcallSolm, hPost1, hcreated1, hσ01, hgenesis1, hblocks1, henv1⟩ :=
    uniswapBalanceTypedCallFromState_source
      (cA1 := cA1) (gh := gh) (bl := bl) (σ1 := σ1) (σ₀ := σ₀)
      (I := I) (evm1S := evm0S) (cA2 := cA2) (σ2 := σ2)
      (z2 := z2) (out2 := out2) (A_in2 := A_in2) (callGas2 := callGas2)
      (targetWord := token1CleanE)
      (calldataMem := balanceOfThisRebuiltCalldataMem (UInt256.ofNat I.codeOwner.val) o)
      (inOff := ⟨128⟩)
      hPost hcreated hσ0 hgenesis hblocks henv hdepth hcd hΘ
  refine ⟨evm1S, ?_, hPost1, hcreated1, hσ01, hgenesis1, hblocks1, ?_⟩
  · simpa [token1CleanE, token1WordE, htargetSource] using hcallSolm
  · simpa [henv] using henv1

end UniswapV2Pair
