import Examples.UniswapV2Pair.SkimSafeTransferDynamicRuntime
import Examples.UniswapV2Pair.SkimDynamicSecondRuntime
import Examples.UniswapV2Pair.SkimSecondSafeTransferDynamicRuntime
import Examples.UniswapV2Pair.SkimSecondSafeTransferDynamicOffsetRuntime
import Examples.UniswapV2Pair.SkimSecondSafeTransferDynamicOffsetReturnRuntime
import Examples.UniswapV2Pair.SkimSecondSafeTransferDynamicCalldataRuntime
import Examples.UniswapV2Pair.SkimSource
import Reasoning.ExternalCall

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

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

theorem uniswapAddress_self (a : AccountAddress) : EVM.address a.val = a := by
  apply Fin.ext
  show a.val % EVM.addressModulus = a.val
  rw [show EVM.addressModulus = AccountAddress.size from by decide]
  exact Nat.mod_eq_of_lt a.isLt

theorem uniswapSkimBalanceOfDecode_ok {returndata : ByteArray} (hlo : 32 ≤ returndata.size) :
    config.externalABI.decode? "balanceOf" returndata =
      some (skimBalanceValue
        (UInt256.ofNat (fromByteArrayBigEndian (returndata.extract 0 32)))) := by
  have hword :
      (UInt256.ofNat (fromByteArrayBigEndian (returndata.extract 0 32))).toNat =
        fromByteArrayBigEndian (returndata.extract 0 32) := by
    exact UInt256.toNat_ofNat_of_lt (fromByteArrayBigEndian_extract0_32_lt hlo)
  change uniswapExternalABI.decode? "balanceOf" returndata = _
  rw [show
    some (skimBalanceValue
        (UInt256.ofNat (fromByteArrayBigEndian (returndata.extract 0 32)))) =
      some (.int (Int.ofNat (fromByteArrayBigEndian (returndata.extract 0 32)))) by
      simp only [skimBalanceValue, uniswapUint256Value, hword]]
  simpa [uniswapExternalABI, uint256, uint256Int, abiUInt256] using
    (decodeReturnValueWithMode_legacy_uint256_ok (returndata := returndata) hlo)

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
  obtain ⟨g'', A'_evm, hΘeq⟩ := hΘ
  let evmE := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I
  let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmEL := uniswapLockEnteredState evmE
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
  have hdepthEL : evmEL.executionEnv.depth.val < 1024 := by
    simpa [evmEL, evmE, uniswapLockEnteredState, uniswapUnlockedState, initState,
      storageStore_executionEnv] using hdepth
  have hdepthNe : evmEL.executionEnv.depth ≠ 1024 := by
    intro hEq
    rw [hEq] at hdepthEL
    exact absurd hdepthEL (by decide)
  have hcd :
      config.externalABI.encode? "balanceOf"
        [.address evmEL.executionEnv.codeOwner] =
        some ((balanceOfThisCalldataMem (UInt256.ofNat I.codeOwner.val))
          |>.readWithPadding 128 36) := by
    simpa [evmEL, evmE, uniswapLockEnteredState, uniswapUnlockedState, initState,
      storageStore_executionEnv] using
      (balanceOfThisCalldataMem_encode I.codeOwner)
  have hΘE :
      (cA', σ', g'', A'_evm, z, o) =
        Ethereum.EVM.Θ evmEL.executionEnv.blobVersionedHashes
          evmEL.createdAccounts evmEL.genesisBlockHeader evmEL.blocks
          evmEL.accountMap evmEL.σ₀ A_in
          (AccountAddress.ofUInt256 (UInt256.ofNat evmEL.executionEnv.codeOwner))
          evmEL.executionEnv.sender
          (AccountAddress.ofUInt256 token0CleanE)
          (toExecute evmEL.accountMap (AccountAddress.ofUInt256 token0CleanE))
          callGas (UInt256.ofNat evmEL.executionEnv.gasPrice) ⟨0⟩ ⟨0⟩
          ((balanceOfThisCalldataMem (UInt256.ofNat I.codeOwner.val))
            |>.readWithPadding 128 36)
          (evmEL.executionEnv.depth + 1) evmEL.executionEnv.header false := by
    simpa [evmEL, evmE, σLockE, token0WordE, token0CleanE,
      uniswapLockEnteredState, uniswapUnlockedState, initState, storageStore_createdAccounts,
      storageStore_accountMap, storageStore_executionEnv, uniswapStorageStore_sigma0,
      uniswapStorageStore_genesisBlockHeader, uniswapStorageStore_blocks] using hΘeq
  have htarget : target = AccountAddress.ofUInt256 token0CleanE := by
    rfl
  have hcallE : typedCallViaEVM config evmEL target "balanceOf" 0
      [.address evmEL.executionEnv.codeOwner]
      (z,
        { evmEL with
            accountMap := σ'
            substate := A'_evm
            createdAccounts := cA' },
        o) false := by
    exact callCoincides
      (cfg := config) (evm := evmEL) (name := "balanceOf")
      (args := [.address evmEL.executionEnv.codeOwner]) (tgt := target)
      (targetWord := token0CleanE) (cA' := cA') (σ' := σ')
      (A' := A'_evm) (A_in := A_in) (z := z) (o := o)
      (g'' := g'') (callGas := callGas)
      (mem := balanceOfThisCalldataMem (UInt256.ofNat I.codeOwner.val))
      (inOff := ⟨128⟩) (inSize := ⟨36⟩) (callPerm := false)
      hdepthNe htarget hcd hΘE
  have hLockStateAccounts : accountMapEquiv evmEL.accountMap evmSL.accountMap := by
    simpa [evmEL, evmSL, evmE, evmS, σLockE, σLockS,
      uniswapLockEnteredState, uniswapUnlockedState, initState,
      storageStore_accountMap] using hLockAccounts
  obtain ⟨σ'_solm, A'_solm, hcallSolm, hPostAccounts⟩ :=
    typedCallViaEVM_accountMapEquiv
      (evm_solm := evmSL) hcallE hLockStateAccounts
      (by simp [evmEL, evmSL, evmE, evmS, uniswapLockEnteredState,
        uniswapUnlockedState, initState, uniswapStorageStore_sigma0])
      (by simp [evmEL, evmSL, evmE, evmS, uniswapLockEnteredState,
        uniswapUnlockedState, initState, storageStore_createdAccounts])
      (by simp [evmEL, evmSL, evmE, evmS, uniswapLockEnteredState,
        uniswapUnlockedState, initState, uniswapStorageStore_genesisBlockHeader])
      (by simp [evmEL, evmSL, evmE, evmS, uniswapLockEnteredState,
        uniswapUnlockedState, initState, uniswapStorageStore_blocks])
      (by simp [evmEL, evmSL, evmE, evmS, uniswapLockEnteredState,
        uniswapUnlockedState, initState, uniswapStorageStore_substate])
      (by simp [evmEL, evmSL, evmE, evmS, uniswapLockEnteredState,
        uniswapUnlockedState, initState, storageStore_executionEnv])
  let evm0S :=
    { evmSL with
        accountMap := σ'_solm
        substate := A'_solm
        createdAccounts := cA' }
  refine ⟨evm0S, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [evm0S, htargetSource, evmEL, evmSL, evmE, evmS,
      uniswapLockEnteredState, uniswapUnlockedState, initState,
      storageStore_executionEnv] using hcallSolm
  · simpa [evm0S] using hPostAccounts
  · simp [evm0S]
  · simp [evm0S, evmSL, evmS, uniswapLockEnteredState, uniswapUnlockedState, initState,
      uniswapStorageStore_sigma0]
  · simp [evm0S, evmSL, evmS, uniswapLockEnteredState, uniswapUnlockedState, initState,
      uniswapStorageStore_genesisBlockHeader]
  · simp [evm0S, evmSL, evmS, uniswapLockEnteredState, uniswapUnlockedState, initState,
      uniswapStorageStore_blocks]
  · simp [evm0S, evmSL, evmS]

theorem typedCallViaEVM_executionEnv_eq {cfg : Config} {evm evm' : EVM.State}
    {target : EVM.Address} {name : Ident} {value : ℤ} {args : List Value}
    {z : Bool} {out : ByteArray} {perm : Bool}
    (hcall : typedCallViaEVM cfg evm target name value args (z, evm', out) perm) :
    evm'.executionEnv = evm.executionEnv := by
  obtain ⟨_calldata, _hencode, hraw⟩ := hcall
  cases hraw with
  | callMade _hvalue _hTheta hevm' _hvalue' _hdepth =>
      subst hevm'
      rfl
  | callNotMade _hsubstate hevm' _hvalue =>
      subst hevm'
      rfl

-- TEMPORARY AXIOM: semantic bridge for raw EVM static calls.
-- `perm = false` is `STATICCALL`; it may change call metadata/substate, but not persistent
-- account storage. This should be replaced by a proof from `Ethereum.EVM.Θ`/`Ξ`.
axiom callViaEVM_static_accountMap_eq {evm evm' : EVM.State}
    {target : EVM.Address} {value : ℤ} {calldata : ByteArray}
    {z : Bool} {out : ByteArray}
    (hcall : callViaEVM evm target value calldata (z, evm', out) false) :
    evm'.accountMap = evm.accountMap

theorem callViaEVM_static_accountMapEquiv {evm evm' : EVM.State}
    {target : EVM.Address} {value : ℤ} {calldata : ByteArray}
    {z : Bool} {out : ByteArray}
    (hcall : callViaEVM evm target value calldata (z, evm', out) false) :
    accountMapEquiv evm'.accountMap evm.accountMap :=
  accountMapEquiv.of_eq (callViaEVM_static_accountMap_eq hcall)

theorem typedCallViaEVM_static_accountMapEquiv {cfg : Config} {evm evm' : EVM.State}
    {target : EVM.Address} {name : Ident} {args : List Value}
    {z : Bool} {out : ByteArray}
    (hcall : typedCallViaEVM cfg evm target name 0 args (z, evm', out) false) :
    accountMapEquiv evm'.accountMap evm.accountMap := by
  obtain ⟨calldata, _hencode, hraw⟩ := hcall
  exact callViaEVM_static_accountMapEquiv hraw

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
      config.externalABI.decode? "balanceOf" o = some (skimBalanceValue balance0) ∧
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
      config.externalABI.decode? "balanceOf" o = some (skimBalanceValue balance0) := by
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
  have hStaticAccounts : accountMapEquiv evm0S.accountMap evmL.accountMap :=
    typedCallViaEVM_static_accountMapEquiv hcall0
  have hLockAccounts : accountMapEquiv σLockE σLockS :=
    accountMapEquiv_sstoreAccountMap I.codeOwner ⟨12⟩ ⟨0⟩ hAccounts
  have howner : evm0S.executionEnv.codeOwner = I.codeOwner := by
    have henv := typedCallViaEVM_executionEnv_eq hcall0
    simpa [evmL, evmS, uniswapLockEnteredState, uniswapUnlockedState, initState,
      storageStore_executionEnv] using congrArg ExecutionEnv.codeOwner henv
  have hstaticSlot := accountMapEquiv_storage_findD hStaticAccounts I.codeOwner ⟨8⟩ ⟨0⟩
  have hlockSlot := accountMapEquiv_storage_findD hLockAccounts I.codeOwner ⟨8⟩ ⟨0⟩
  have hslot :
      ((evm0S.accountMap.find? I.codeOwner).option ⟨0⟩
          (fun acc => acc.storage.findD ⟨8⟩ ⟨0⟩)) =
        ((σLockE.find? I.codeOwner).option ⟨0⟩
          (fun acc => acc.storage.findD ⟨8⟩ ⟨0⟩)) := by
    rw [hstaticSlot]
    simpa [evmL, evmS, σLockE, σLockS, uniswapLockEnteredState,
      uniswapUnlockedState, initState, storageStore_accountMap] using hlockSlot.symm
  simpa [uniswapReserve0Word, Solm.EVM.storageLoad, State.lookupAccount,
    Account.lookupStorage, uniswapSlotWord, σLockE, howner] using
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
  obtain ⟨g'', A'_evm, hΘeq⟩ := hΘ
  let evmE : EVM.State :=
    { evm1S with
      accountMap := σ1
      createdAccounts := cA1
      σ₀ := σ₀
      genesisBlockHeader := gh
      blocks := bl
      executionEnv := I }
  let target : EVM.Address := AccountAddress.ofUInt256 (UInt256.land token1 solcAddrMask)
  have hdepthE : evmE.executionEnv.depth.val < 1024 := by
    simpa [evmE] using hdepth
  have hdepthNe : evmE.executionEnv.depth ≠ 1024 := by
    intro hEq
    rw [hEq] at hdepthE
    exact absurd hdepthE (by decide)
  have hcd :
      config.externalABI.encode? "balanceOf" [.address evmE.executionEnv.codeOwner] =
        some ((skimSecondBalanceCalldataMem (UInt256.ofNat I.codeOwner.val) o toWord value)
          |>.readWithPadding 292 36) := by
    simpa [evmE] using
      (skimSecondBalanceCalldataMem_encode I.codeOwner toWord value ho32 hoSize)
  have hΘE :
      (cA2, σ2, g'', A'_evm, z2, out2) =
        Ethereum.EVM.Θ evmE.executionEnv.blobVersionedHashes
          evmE.createdAccounts evmE.genesisBlockHeader evmE.blocks evmE.accountMap evmE.σ₀ A_in2
          (AccountAddress.ofUInt256 (UInt256.ofNat evmE.executionEnv.codeOwner))
          evmE.executionEnv.sender target
          (toExecute evmE.accountMap target)
          callGas2 (UInt256.ofNat evmE.executionEnv.gasPrice) ⟨0⟩ ⟨0⟩
          ((skimSecondBalanceCalldataMem (UInt256.ofNat I.codeOwner.val) o toWord value)
            |>.readWithPadding 292 36)
          (evmE.executionEnv.depth + 1) evmE.executionEnv.header false := by
    simpa [evmE, target] using hΘeq
  have hcallE : typedCallViaEVM config evmE target "balanceOf" 0
      [.address evmE.executionEnv.codeOwner]
      (z2,
        { evmE with
            accountMap := σ2
            substate := A'_evm
            createdAccounts := cA2 },
        out2) false := by
    exact callCoincides
      (cfg := config) (evm := evmE) (name := "balanceOf")
      (args := [.address evmE.executionEnv.codeOwner]) (tgt := target)
      (targetWord := UInt256.land token1 solcAddrMask) (cA' := cA2) (σ' := σ2)
      (A' := A'_evm) (A_in := A_in2) (z := z2) (o := out2)
      (g'' := g'') (callGas := callGas2)
      (mem := skimSecondBalanceCalldataMem (UInt256.ofNat I.codeOwner.val) o toWord value)
      (inOff := ⟨292⟩) (inSize := ⟨36⟩) (callPerm := false)
      hdepthNe rfl hcd hΘE
  obtain ⟨σ2S, A2S, hcallSolm, hPost2⟩ :=
    typedCallViaEVM_accountMapEquiv
      (evm_solm := evm1S) hcallE
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
  obtain ⟨g'', A'_evm, hΘeq⟩ := hΘ
  let evmE : EVM.State :=
    { evm1S with
      accountMap := σ1
      createdAccounts := cA1
      σ₀ := σ₀
      genesisBlockHeader := gh
      blocks := bl
      executionEnv := I }
  let target : EVM.Address := AccountAddress.ofUInt256 (UInt256.land token1 solcAddrMask)
  have hdepthE : evmE.executionEnv.depth.val < 1024 := by
    simpa [evmE] using hdepth
  have hdepthNe : evmE.executionEnv.depth ≠ 1024 := by
    intro hEq
    rw [hEq] at hdepthE
    exact absurd hdepthE (by decide)
  have hcd :
      config.externalABI.encode? "balanceOf" [.address evmE.executionEnv.codeOwner] =
        some ((skimSecondBalanceDynamicCalldataMem (UInt256.ofNat I.codeOwner.val) o
            toWord value out1)
          |>.readWithPadding (skimSafeTransferReturnDataPtr out1).toNat 36) := by
    simpa [evmE] using
      (skimSecondBalanceDynamicCalldataMem_encode I.codeOwner toWord value
        ho32 hoSize hout1Ne hout1Size)
  have hΘE :
      (cA2, σ2, g'', A'_evm, z2, out2) =
        Ethereum.EVM.Θ evmE.executionEnv.blobVersionedHashes
          evmE.createdAccounts evmE.genesisBlockHeader evmE.blocks evmE.accountMap evmE.σ₀ A_in2
          (AccountAddress.ofUInt256 (UInt256.ofNat evmE.executionEnv.codeOwner))
          evmE.executionEnv.sender target
          (toExecute evmE.accountMap target)
          callGas2 (UInt256.ofNat evmE.executionEnv.gasPrice) ⟨0⟩ ⟨0⟩
          ((skimSecondBalanceDynamicCalldataMem (UInt256.ofNat I.codeOwner.val) o
              toWord value out1)
            |>.readWithPadding (skimSafeTransferReturnDataPtr out1).toNat 36)
          (evmE.executionEnv.depth + 1) evmE.executionEnv.header false := by
    simpa [evmE, target] using hΘeq
  have hcallE : typedCallViaEVM config evmE target "balanceOf" 0
      [.address evmE.executionEnv.codeOwner]
      (z2,
        { evmE with
            accountMap := σ2
            substate := A'_evm
            createdAccounts := cA2 },
        out2) false := by
    exact callCoincides
      (cfg := config) (evm := evmE) (name := "balanceOf")
      (args := [.address evmE.executionEnv.codeOwner]) (tgt := target)
      (targetWord := UInt256.land token1 solcAddrMask) (cA' := cA2) (σ' := σ2)
      (A' := A'_evm) (A_in := A_in2) (z := z2) (o := out2)
      (g'' := g'') (callGas := callGas2)
      (mem := skimSecondBalanceDynamicCalldataMem (UInt256.ofNat I.codeOwner.val) o
        toWord value out1)
      (inOff := skimSafeTransferReturnDataPtr out1) (inSize := ⟨36⟩) (callPerm := false)
      hdepthNe rfl hcd hΘE
  obtain ⟨σ2S, A2S, hcallSolm, hPost2⟩ :=
    typedCallViaEVM_accountMapEquiv
      (evm_solm := evm1S) hcallE
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
  have hStaticAccounts : accountMapEquiv evm2S.accountMap evm1S.accountMap :=
    typedCallViaEVM_static_accountMapEquiv hcall1
  have howner : evm2S.executionEnv.codeOwner = I.codeOwner := by
    have henvCall := typedCallViaEVM_executionEnv_eq hcall1
    simpa [henv] using congrArg ExecutionEnv.codeOwner henvCall
  have hstaticSlot := accountMapEquiv_storage_findD hStaticAccounts I.codeOwner ⟨8⟩ ⟨0⟩
  have hpostSlot := accountMapEquiv_storage_findD hPost I.codeOwner ⟨8⟩ ⟨0⟩
  have hslot :
      ((evm2S.accountMap.find? I.codeOwner).option ⟨0⟩
          (fun acc => acc.storage.findD ⟨8⟩ ⟨0⟩)) =
        ((σ1.find? I.codeOwner).option ⟨0⟩
          (fun acc => acc.storage.findD ⟨8⟩ ⟨0⟩)) := by
    rw [hstaticSlot]
    exact hpostSlot.symm
  simpa [uniswapReserve1Word, Solm.EVM.storageLoad, State.lookupAccount,
    Account.lookupStorage, uniswapSlotWord, howner] using
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
  apply u256_inj
  rw [skimExcess0Word, hreserve]
  rw [UInt256.toNat_ofNat_of_lt]
  · exact (usub_toNat (a := balance0) (b := reserve0) hle).symm
  · exact lt_of_le_of_lt (Nat.sub_le _ _) balance0.val.isLt

theorem skimExcess1Word_eq_sub_of_reserve {evm : EVM.State} {balance1 reserve1 : UInt256}
    (hreserve : uniswapReserve1Word evm = reserve1)
    (hle : reserve1.toNat ≤ balance1.toNat) :
    skimExcess1Word evm balance1 = UInt256.sub balance1 reserve1 := by
  apply u256_inj
  rw [skimExcess1Word, hreserve]
  rw [UInt256.toNat_ofNat_of_lt]
  · exact (usub_toNat (a := balance1) (b := reserve1) hle).symm
  · exact lt_of_le_of_lt (Nat.sub_le _ _) balance1.val.isLt

theorem skimFirstSafeTransferCalldata_canonical {evm0S : EVM.State}
    {I : ExecutionEnv} {balance0 reserve0 : UInt256}
    (hreserve : uniswapReserve0Word evm0S = reserve0)
    (hle : reserve0.toNat ≤ balance0.toNat) :
    transferCalldata? (skimToAddress I) (skimExcess0Word evm0S balance0) =
      some ((transferCalldataMem (UInt256.land solcAddrMask (skimToWord I))
        (UInt256.sub balance0 reserve0)).readWithPadding 128 68) := by
  have hexcess : skimExcess0Word evm0S balance0 = UInt256.sub balance0 reserve0 :=
    skimExcess0Word_eq_sub_of_reserve hreserve hle
  simpa [transferCalldata?, transferCallArgs, hexcess, skimToAddress_word_eq_mask I] using
    transferCalldataMem_encode (skimToAddress I) (skimExcess0Word evm0S balance0)

theorem skimFirstSafeTransferCalldata_masked {evm0S : EVM.State}
    {I : ExecutionEnv} {balance0 reserve0 : UInt256}
    (hreserve : uniswapReserve0Word evm0S = reserve0)
    (hle : reserve0.toNat ≤ balance0.toNat) :
    transferCalldata? (skimToAddress I) (skimExcess0Word evm0S balance0) =
      some ((transferCalldataMem (UInt256.land solcAddrMask (skimToMaskedWord I))
        (UInt256.sub balance0 reserve0)).readWithPadding 128 68) := by
  have hexcess : skimExcess0Word evm0S balance0 = UInt256.sub balance0 reserve0 :=
    skimExcess0Word_eq_sub_of_reserve hreserve hle
  simpa [transferCalldata?, transferCallArgs, hexcess, skimToAddress_word_eq_masked I] using
    transferCalldataMem_encode (skimToAddress I) (skimExcess0Word evm0S balance0)

theorem skimSecondSafeTransferCalldata_canonical {evm2S : EVM.State}
    {I : ExecutionEnv} {o out2 : ByteArray} {balance1 reserve1 prevValue : UInt256}
    (hreserve : uniswapReserve1Word evm2S = reserve1)
    (hle : reserve1.toNat ≤ balance1.toNat)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hout32 : 32 ≤ out2.size) (houtSize : out2.size < UInt256.size) :
    transferCalldata? (skimToAddress I) (skimExcess1Word evm2S balance1) =
      some ((skimSecondSafeTransferCallMem2 (UInt256.ofNat I.codeOwner.val) o (skimToWord I)
        prevValue out2 (UInt256.sub balance1 reserve1)).readWithPadding 456 68) := by
  have hexcess : skimExcess1Word evm2S balance1 = UInt256.sub balance1 reserve1 :=
    skimExcess1Word_eq_sub_of_reserve hreserve hle
  rw [skimSecondSafeTransferCallMem2_read456_68
    (UInt256.ofNat I.codeOwner.val) (skimToWord I) prevValue (UInt256.sub balance1 reserve1)
    ho32 hoSize hout32 houtSize]
  simpa [transferCalldata?, transferCallArgs, hexcess, skimToAddress_word_eq_mask I] using
    transferCalldataMem_encode (skimToAddress I) (skimExcess1Word evm2S balance1)

theorem skimSecondSafeTransferCalldata_masked {evm2S : EVM.State}
    {I : ExecutionEnv} {o out2 : ByteArray} {balance1 reserve1 prevValue : UInt256}
    (hreserve : uniswapReserve1Word evm2S = reserve1)
    (hle : reserve1.toNat ≤ balance1.toNat)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hout32 : 32 ≤ out2.size) (houtSize : out2.size < UInt256.size) :
    transferCalldata? (skimToAddress I) (skimExcess1Word evm2S balance1) =
      some ((skimSecondSafeTransferCallMem2 (UInt256.ofNat I.codeOwner.val) o
        (skimToMaskedWord I) prevValue out2 (UInt256.sub balance1 reserve1)).readWithPadding
        456 68) := by
  have hexcess : skimExcess1Word evm2S balance1 = UInt256.sub balance1 reserve1 :=
    skimExcess1Word_eq_sub_of_reserve hreserve hle
  rw [skimSecondSafeTransferCallMem2_read456_68
    (UInt256.ofNat I.codeOwner.val) (skimToMaskedWord I) prevValue
    (UInt256.sub balance1 reserve1) ho32 hoSize hout32 houtSize]
  simpa [transferCalldata?, transferCallArgs, hexcess, skimToAddress_word_eq_masked I] using
    transferCalldataMem_encode (skimToAddress I) (skimExcess1Word evm2S balance1)

theorem skimSecondSafeTransferCalldata_canonical_dynamic {evm2S : EVM.State}
    {I : ExecutionEnv} {o out1 out2 : ByteArray} {balance1 reserve1 prevValue : UInt256}
    (hreserve : uniswapReserve1Word evm2S = reserve1)
    (hle : reserve1.toNat ≤ balance1.toNat)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hout1Ne : out1.size ≠ 0) (hout1Size : out1.size < 2 ^ 255)
    (hout32 : 32 ≤ out2.size) (houtSize : out2.size < UInt256.size) :
    transferCalldata? (skimToAddress I) (skimExcess1Word evm2S balance1) =
      some ((skimSecondSafeTransferDynamicCallMem2 (UInt256.ofNat I.codeOwner.val) o
        (skimToWord I) prevValue out1 out2 (UInt256.sub balance1 reserve1)).readWithPadding
        (skimSecondSafeTransferDynamicCallPtr out1).toNat 68) := by
  have hexcess : skimExcess1Word evm2S balance1 = UInt256.sub balance1 reserve1 :=
    skimExcess1Word_eq_sub_of_reserve hreserve hle
  rw [skimSecondSafeTransferDynamicCallMem2_read_callPtr_68
    (UInt256.ofNat I.codeOwner.val) (skimToWord I) prevValue
    (UInt256.sub balance1 reserve1) ho32 hoSize hout1Ne hout1Size hout32 houtSize]
  simpa [transferCalldata?, transferCallArgs, hexcess, skimToAddress_word_eq_mask I] using
    transferCalldataMem_encode (skimToAddress I) (skimExcess1Word evm2S balance1)

theorem skimSecondSafeTransferCalldata_masked_dynamic {evm2S : EVM.State}
    {I : ExecutionEnv} {o out1 out2 : ByteArray} {balance1 reserve1 prevValue : UInt256}
    (hreserve : uniswapReserve1Word evm2S = reserve1)
    (hle : reserve1.toNat ≤ balance1.toNat)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hout1Ne : out1.size ≠ 0) (hout1Size : out1.size < 2 ^ 255)
    (hout32 : 32 ≤ out2.size) (houtSize : out2.size < UInt256.size) :
    transferCalldata? (skimToAddress I) (skimExcess1Word evm2S balance1) =
      some ((skimSecondSafeTransferDynamicCallMem2 (UInt256.ofNat I.codeOwner.val) o
        (skimToMaskedWord I) prevValue out1 out2 (UInt256.sub balance1 reserve1)).readWithPadding
        (skimSecondSafeTransferDynamicCallPtr out1).toNat 68) := by
  have hexcess : skimExcess1Word evm2S balance1 = UInt256.sub balance1 reserve1 :=
    skimExcess1Word_eq_sub_of_reserve hreserve hle
  rw [skimSecondSafeTransferDynamicCallMem2_read_callPtr_68
    (UInt256.ofNat I.codeOwner.val) (skimToMaskedWord I) prevValue
    (UInt256.sub balance1 reserve1) ho32 hoSize hout1Ne hout1Size hout32 houtSize]
  simpa [transferCalldata?, transferCallArgs, hexcess, skimToAddress_word_eq_masked I] using
    transferCalldataMem_encode (skimToAddress I) (skimExcess1Word evm2S balance1)

theorem skimToken1GuardAfterFirstTransfer_false {σ : AccountMap}
    {evm evm0 evm1 : EVM.State} {I : ExecutionEnv} {balance0 token1 : UInt256}
    (hPost : accountMapEquiv σ evm1.accountMap)
    (htarget :
      AccountAddress.ofUInt256 (UInt256.land token1 solcAddrMask) =
        uniswapAddressAtSlot (uniswapLockEnteredState evm) ⟨7⟩)
    (hnoCode : uniswapExtCodeSizeWord σ (UInt256.land token1 solcAddrMask) = ⟨0⟩) :
    evalExpr? config
      { contract := contract, locals := skimFirstSafeTransferStore evm evm0 I balance0 } evm1
      (.binary .gt (.extCodeSize (.var "_token1")) (.intLit 0)) = .ok (.bool false) := by
  let target := UInt256.land token1 solcAddrMask
  let addr := uniswapAddressAtSlot (uniswapLockEnteredState evm) ⟨7⟩
  have hsame := uniswapExtCodeSizeWord_accountMapEquiv hPost target
  have hnoEvm : uniswapExtCodeSizeWord evm1.accountMap target = ⟨0⟩ := by
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
          simpa [target, addr, htarget, uniswapExtCodeSizeWord, hacc] using hnoEvm
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
    (hcode : uniswapExtCodeSizeWord σ (UInt256.land token1 solcAddrMask) ≠ ⟨0⟩) :
    evalExpr? config
      { contract := contract, locals := skimFirstSafeTransferStore evm evm0 I balance0 } evm1
      (.binary .gt (.extCodeSize (.var "_token1")) (.intLit 0)) = .ok (.bool true) := by
  let target := UInt256.land token1 solcAddrMask
  let addr := uniswapAddressAtSlot (uniswapLockEnteredState evm) ⟨7⟩
  have hsame := uniswapExtCodeSizeWord_accountMapEquiv hPost target
  have hcodeEvm : uniswapExtCodeSizeWord evm1.accountMap target ≠ ⟨0⟩ := by
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
        unfold uniswapExtCodeSizeWord
        rw [show AccountAddress.ofUInt256 target = addr by simpa [target, addr] using htarget,
          hacc]
        rfl
    | some acc =>
        have hzeroAcc : UInt256.ofNat acc.code.size = ⟨0⟩ := by
          simpa [hacc] using hzero
        simpa [target, addr, htarget, uniswapExtCodeSizeWord, hacc] using hzeroAcc
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
      uniswapExtCodeSizeWord (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩)
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
      uniswapExtCodeSizeWord σLockS (UInt256.land solcAddrMask token0WordS) = ⟨0⟩ := by
    have hsame :=
      uniswapExtCodeSizeWord_accountMapEquiv hLockAccounts
        (UInt256.land solcAddrMask token0WordE)
    have hnoE :
        uniswapExtCodeSizeWord σLockE (UInt256.land solcAddrMask token0WordE) = ⟨0⟩ := by
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
        uniswapExtCodeSizeWord σLockS (UInt256.land token0WordS solcAddrMask) = ⟨0⟩ := by
      simpa [u256_land_comm] using hnoSolm
    simpa [evmL, evmS, uniswapLockEnteredState, uniswapUnlockedState, initState,
      storageStore_accountMap, storageStore_executionEnv, State.lookupAccount, Solm.EVM.storageLoad,
      Account.lookupStorage, uniswapAddressAtSlot, uniswapExtCodeSizeWord, uniswapSlotWord, σLockS,
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
      uniswapExtCodeSizeWord (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩)
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
      uniswapExtCodeSizeWord σLockS (UInt256.land solcAddrMask token0WordS) ≠ ⟨0⟩ := by
    have hsame :=
      uniswapExtCodeSizeWord_accountMapEquiv hLockAccounts
        (UInt256.land solcAddrMask token0WordE)
    have hcodeE :
        uniswapExtCodeSizeWord σLockE (UInt256.land solcAddrMask token0WordE) ≠ ⟨0⟩ := by
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
        uniswapExtCodeSizeWord σLockS (UInt256.land token0WordS solcAddrMask) ≠ ⟨0⟩ := by
      simpa [u256_land_comm] using hcodeSolm
    simpa [evmL, evmS, uniswapLockEnteredState, uniswapUnlockedState, initState,
      storageStore_accountMap, storageStore_executionEnv, State.lookupAccount, Solm.EVM.storageLoad,
      Account.lookupStorage, uniswapAddressAtSlot, uniswapExtCodeSizeWord, uniswapSlotWord, σLockS,
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
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size)
    (hcanonTo : (skimToWord I).toNat < EVM.addressModulus)
    (hlocked :
      (σ_evm.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨12⟩ ⟨0⟩)) ≠
        ⟨1⟩)
    (hdispatch : dispatchMsg contract I.calldata = some skimTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (skimTransition.params.map Param.name)
        (transitionSignature skimTransition).paramTypes I.calldata = some (skimStore I))
    (hreach : ∃ k C, RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1286⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
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
  exact (uniswapSkimX_locked (g := Sat256.ofUInt256 g)
      hsz36 hsize hcanonTo hlocked hreach)
    |>.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem uniswapSkimBodyCoreRevert_locked_masked
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size)
    (hlocked :
      (σ_evm.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨12⟩ ⟨0⟩)) ≠
        ⟨1⟩)
    (hdispatch : dispatchMsg contract I.calldata = some skimTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (skimTransition.params.map Param.name)
        (transitionSignature skimTransition).paramTypes I.calldata = some (skimStore I))
    (hreach : ∃ k C, RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1286⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
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
  exact (uniswapSkimX_locked_masked (g := Sat256.ofUInt256 g)
      hsz36 hsize hlocked hreach)
    |>.reEquivExecutionRevert hcode hdispatch hdecode hbody

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
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xbc, 0x25, 0xcf, 0x77]⟩)
    (hsz36 : 36 ≤ I.calldata.size)
    (hcanonTo : (skimToWord I).toNat < EVM.addressModulus)
    (hunlocked :
      (σ_evm.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD ⟨12⟩ ⟨0⟩)) = ⟨1⟩)
    (htoken0NoCode :
      uniswapExtCodeSizeWord (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩)
        (UInt256.land solcAddrMask
          (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I)) =
        ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some skimTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (skimTransition.params.map Param.name)
        (transitionSignature skimTransition).paramTypes I.calldata = some (skimStore I))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
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
  exact (uniswapSkimRuntimeFirstBalanceOfMissingCodeReverts
      (g := g) hcode hsize hwv hsel hsz36 hcanonTo hperm
      hunlocked htoken0NoCode)
    |>.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem uniswapSkimBodyCoreRevert_firstNoCode_masked
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xbc, 0x25, 0xcf, 0x77]⟩)
    (hsz36 : 36 ≤ I.calldata.size)
    (hunlocked :
      (σ_evm.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD ⟨12⟩ ⟨0⟩)) = ⟨1⟩)
    (htoken0NoCode :
      uniswapExtCodeSizeWord (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩)
        (UInt256.land solcAddrMask
          (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I)) =
        ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some skimTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (skimTransition.params.map Param.name)
        (transitionSignature skimTransition).paramTypes I.calldata = some (skimStore I))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
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
  exact (uniswapSkimRuntimeFirstBalanceOfMissingCodeReverts_masked
      (g := g) hcode hsize hwv hsel hsz36 hperm hunlocked htoken0NoCode)
    |>.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem uniswapSkimBodyCoreRevert_firstCallDepth
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xbc, 0x25, 0xcf, 0x77]⟩)
    (hsz36 : 36 ≤ I.calldata.size)
    (hcanonTo : (skimToWord I).toNat < EVM.addressModulus)
    (hdepth : I.depth = 1024)
    (hunlocked :
      (σ_evm.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD ⟨12⟩ ⟨0⟩)) = ⟨1⟩)
    (htoken0Code :
      uniswapExtCodeSizeWord (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩)
        (UInt256.land solcAddrMask
          (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I)) ≠
        ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some skimTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (skimTransition.params.map Param.name)
        (transitionSignature skimTransition).paramTypes I.calldata = some (skimStore I))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmL := uniswapLockEnteredState evmS
  let target := EVM.address (uniswapAddressAtSlot evmL ⟨6⟩)
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
  exact (uniswapSkimRuntimeFirstBalanceOfStaticcallDepthReverts
      (g := g) hcode hsize hwv hsel hsz36 hcanonTo hperm hdepth
      hunlocked htoken0Code)
    |>.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem uniswapSkimBodyCoreRevert_firstCallDepth_masked
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xbc, 0x25, 0xcf, 0x77]⟩)
    (hsz36 : 36 ≤ I.calldata.size)
    (hdepth : I.depth = 1024)
    (hunlocked :
      (σ_evm.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD ⟨12⟩ ⟨0⟩)) = ⟨1⟩)
    (htoken0Code :
      uniswapExtCodeSizeWord (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩)
        (UInt256.land solcAddrMask
          (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I)) ≠
        ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some skimTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (skimTransition.params.map Param.name)
        (transitionSignature skimTransition).paramTypes I.calldata = some (skimStore I))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmL := uniswapLockEnteredState evmS
  let target := EVM.address (uniswapAddressAtSlot evmL ⟨6⟩)
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
  exact (uniswapSkimRuntimeFirstBalanceOfStaticcallDepthReverts_masked
      (g := g) hcode hsize hwv hsel hsz36 hperm hdepth hunlocked htoken0Code)
    |>.reEquivExecutionRevert hcode hdispatch hdecode hbody

/-- Locked-revert `skim(address)` refinement slice, packaged from selector dispatch through the
body core. -/
theorem uniswapSkimBodyRevert_locked
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩) (hsel : selIs I ⟨#[0xbc, 0x25, 0xcf, 0x77]⟩)
    (hsz36 : 36 ≤ I.calldata.size)
    (hcanonTo : (skimToWord I).toNat < EVM.addressModulus)
    (hlocked :
      (σ_evm.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨12⟩ ⟨0⟩)) ≠
        ⟨1⟩)
    (hdispatch : dispatchMsg contract I.calldata = some skimTransition)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I ⟨#[0xbc, 0x25, 0xcf, 0x77]⟩ rfl hsel
  exact uniswapSkimBodyCoreRevert_locked hcode hsize hwv hsz36 hcanonTo hlocked hdispatch
    (uniswapDecode_skim_ok hsz36 hcanonTo)
    (uniswapReachSkimBody (g := Sat256.ofUInt256 g) hcode hwv hsz4 hsize hsel)
    hAccounts

theorem uniswapSkimBodyRevert_locked_masked
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩) (hsel : selIs I ⟨#[0xbc, 0x25, 0xcf, 0x77]⟩)
    (hsz36 : 36 ≤ I.calldata.size)
    (hnoncanon : ¬ (skimToWord I).toNat < EVM.addressModulus)
    (hlocked :
      (σ_evm.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨12⟩ ⟨0⟩)) ≠
        ⟨1⟩)
    (hdispatch : dispatchMsg contract I.calldata = some skimTransition)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I ⟨#[0xbc, 0x25, 0xcf, 0x77]⟩ rfl hsel
  exact uniswapSkimBodyCoreRevert_locked_masked hcode hsize hwv hsz36 hlocked hdispatch
    (uniswapDecode_skim_ok_noncanon hsz36 hnoncanon)
    (uniswapReachSkimBody (g := Sat256.ofUInt256 g) hcode hwv hsz4 hsize hsel)
    hAccounts

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
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xbc, 0x25, 0xcf, 0x77]⟩)
    (hsz36 : 36 ≤ I.calldata.size)
    (hcanonTo : (skimToWord I).toNat < EVM.addressModulus)
    (hunlocked :
      (σ_evm.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD ⟨12⟩ ⟨0⟩)) = ⟨1⟩)
    (htoken0NoCode :
      uniswapExtCodeSizeWord (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩)
        (UInt256.land solcAddrMask
          (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I)) =
        ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some skimTransition)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  exact uniswapSkimBodyCoreRevert_firstNoCode hcode hsize hperm hwv hsel hsz36 hcanonTo
    hunlocked htoken0NoCode hdispatch (uniswapDecode_skim_ok hsz36 hcanonTo) hAccounts

theorem uniswapSkimBodyRevert_firstNoCode_masked
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xbc, 0x25, 0xcf, 0x77]⟩)
    (hsz36 : 36 ≤ I.calldata.size)
    (hnoncanon : ¬ (skimToWord I).toNat < EVM.addressModulus)
    (hunlocked :
      (σ_evm.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD ⟨12⟩ ⟨0⟩)) = ⟨1⟩)
    (htoken0NoCode :
      uniswapExtCodeSizeWord (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩)
        (UInt256.land solcAddrMask
          (uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I)) =
        ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some skimTransition)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  exact uniswapSkimBodyCoreRevert_firstNoCode_masked hcode hsize hperm hwv hsel hsz36
    hunlocked htoken0NoCode hdispatch (uniswapDecode_skim_ok_noncanon hsz36 hnoncanon)
    hAccounts

theorem uniswapSkimBody
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xbc, 0x25, 0xcf, 0x77]⟩)
    (hdispatch : dispatchMsg contract I.calldata = some skimTransition)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  by_cases hsz36 : 36 ≤ I.calldata.size
  · by_cases hcanonTo : (skimToWord I).toNat < EVM.addressModulus
    · by_cases hlocked :
        (σ_evm.find? I.codeOwner |>.option ⟨0⟩
          (fun acc => acc.storage.findD ⟨12⟩ ⟨0⟩)) ≠ ⟨1⟩
      · exact uniswapSkimBodyRevert_locked hcode hsize hwv hsel hsz36 hcanonTo
          hlocked hdispatch hAccounts
      · have hunlocked :
          (σ_evm.find? I.codeOwner |>.option ⟨0⟩
            (fun acc => acc.storage.findD ⟨12⟩ ⟨0⟩)) = ⟨1⟩ := by
          exact not_not.mp hlocked
        by_cases htoken0NoCode :
          uniswapExtCodeSizeWord (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩)
            (UInt256.land solcAddrMask
              (uniswapSlotWord ⟨6⟩
                (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I)) =
            ⟨0⟩
        · exact uniswapSkimBodyRevert_firstNoCode hcode hsize hperm hwv hsel hsz36
            hcanonTo hunlocked htoken0NoCode hdispatch hAccounts
        · by_cases hdepth : I.depth.val < 1024
          · obtain ⟨cA', σ', z, o, A_in, callGas, hΘ, hrev, hrevShort, hrevLong,
                hoSize⟩ :=
                uniswapSkimRuntimeFirstBalanceOfStaticcallFailureGuard
                  (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
                  (A := A) (I := I) (g := g)
                hcode hsize hwv hsel hsz36 hcanonTo hperm hdepth
                hunlocked htoken0NoCode
            by_cases hz : z = false
            · obtain ⟨g'', A'_evm, hΘeq⟩ := hΘ
              let evmE := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I
              let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
              let evmEL := uniswapLockEnteredState evmE
              let evmSL := uniswapLockEnteredState evmS
              let σLockE := sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩
              let σLockS := sstoreAccountMap I.codeOwner σ_solm ⟨12⟩ ⟨0⟩
              let token0WordE := uniswapSlotWord ⟨6⟩ σLockE I
              let token0WordS := uniswapSlotWord ⟨6⟩ σLockS I
              let token0CleanE := UInt256.land solcAddrMask token0WordE
              let target : EVM.Address := AccountAddress.ofUInt256 token0CleanE
              have hunlockedSolm :
                  Solm.EVM.storageLoad evmS evmS.executionEnv.codeOwner ⟨12⟩ = ⟨1⟩ := by
                have hword := accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨12⟩ ⟨0⟩
                simpa [evmS, initState, Solm.EVM.storageLoad, State.lookupAccount,
                  Account.lookupStorage] using (hword ▸ hunlocked)
              have hguard0 : skimToken0GuardTrue evmS I :=
                skimToken0GuardTrue_initState_of_code hAccounts htoken0NoCode
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
                    uniswapLockEnteredState, uniswapUnlockedState, initState,
                    storageStore_accountMap, storageStore_executionEnv, State.lookupAccount,
                    Account.lookupStorage, Solm.EVM.storageLoad, uniswapAddressAtSlot,
                    uniswapSlotWord, hslot, accountAddress_ofUInt256_eq_ofNat_toNat,
                    u256_land_comm]
                change AccountAddress.ofUInt256 token0CleanE =
                  EVM.address (uniswapAddressAtSlot evmSL ⟨6⟩)
                rw [haddr]
                exact (uniswapAddress_self (uniswapAddressAtSlot evmSL ⟨6⟩)).symm
              have hdepthEL : evmEL.executionEnv.depth.val < 1024 := by
                simpa [evmEL, evmE, uniswapLockEnteredState, uniswapUnlockedState, initState,
                  storageStore_executionEnv] using hdepth
              have hdepthNe : evmEL.executionEnv.depth ≠ 1024 := by
                intro hEq
                rw [hEq] at hdepthEL
                exact absurd hdepthEL (by decide)
              have hcd :
                  config.externalABI.encode? "balanceOf"
                    [.address evmEL.executionEnv.codeOwner] =
                    some ((balanceOfThisCalldataMem (UInt256.ofNat I.codeOwner.val))
                      |>.readWithPadding 128 36) := by
                simpa [evmEL, evmE, uniswapLockEnteredState, uniswapUnlockedState, initState,
                  storageStore_executionEnv] using
                  (balanceOfThisCalldataMem_encode I.codeOwner)
              have hΘE :
                  (cA', σ', g'', A'_evm, z, o) =
                    Ethereum.EVM.Θ evmEL.executionEnv.blobVersionedHashes
                      evmEL.createdAccounts evmEL.genesisBlockHeader evmEL.blocks
                      evmEL.accountMap evmEL.σ₀ A_in
                      (AccountAddress.ofUInt256 (UInt256.ofNat evmEL.executionEnv.codeOwner))
                      evmEL.executionEnv.sender
                      (AccountAddress.ofUInt256 token0CleanE)
                      (toExecute evmEL.accountMap (AccountAddress.ofUInt256 token0CleanE))
                      callGas (UInt256.ofNat evmEL.executionEnv.gasPrice) ⟨0⟩ ⟨0⟩
                      ((balanceOfThisCalldataMem (UInt256.ofNat I.codeOwner.val))
                        |>.readWithPadding 128 36)
                      (evmEL.executionEnv.depth + 1) evmEL.executionEnv.header false := by
                simpa [evmEL, evmE, σLockE, token0WordE, token0CleanE,
                  uniswapLockEnteredState, uniswapUnlockedState, initState,
                  storageStore_createdAccounts, storageStore_accountMap,
                  storageStore_executionEnv, uniswapStorageStore_sigma0,
                  uniswapStorageStore_genesisBlockHeader, uniswapStorageStore_blocks] using hΘeq
              have htarget : target = AccountAddress.ofUInt256 token0CleanE := by
                rfl
              have hcallE : typedCallViaEVM config evmEL target "balanceOf" 0
                  [.address evmEL.executionEnv.codeOwner]
                  (z,
                    { evmEL with
                        accountMap := σ'
                        substate := A'_evm
                        createdAccounts := cA' },
                    o) false := by
                exact callCoincides
                  (cfg := config) (evm := evmEL) (name := "balanceOf")
                  (args := [.address evmEL.executionEnv.codeOwner]) (tgt := target)
                  (targetWord := token0CleanE) (cA' := cA') (σ' := σ')
                  (A' := A'_evm) (A_in := A_in) (z := z) (o := o)
                  (g'' := g'') (callGas := callGas)
                  (mem := balanceOfThisCalldataMem (UInt256.ofNat I.codeOwner.val))
                  (inOff := ⟨128⟩) (inSize := ⟨36⟩) (callPerm := false)
                  hdepthNe htarget hcd hΘE
              have hLockStateAccounts : accountMapEquiv evmEL.accountMap evmSL.accountMap := by
                simpa [evmEL, evmSL, evmE, evmS, σLockE, σLockS,
                  uniswapLockEnteredState, uniswapUnlockedState, initState,
                  storageStore_accountMap] using hLockAccounts
              obtain ⟨σ'_solm, A'_solm, hcallSolm, _hPostAccounts⟩ :=
                typedCallViaEVM_accountMapEquiv
                  (evm_solm := evmSL) hcallE hLockStateAccounts
                  (by simp [evmEL, evmSL, evmE, evmS, uniswapLockEnteredState,
                    uniswapUnlockedState, initState, uniswapStorageStore_sigma0])
                  (by simp [evmEL, evmSL, evmE, evmS, uniswapLockEnteredState,
                    uniswapUnlockedState, initState, storageStore_createdAccounts])
                  (by simp [evmEL, evmSL, evmE, evmS, uniswapLockEnteredState,
                    uniswapUnlockedState, initState, uniswapStorageStore_genesisBlockHeader])
                  (by simp [evmEL, evmSL, evmE, evmS, uniswapLockEnteredState,
                    uniswapUnlockedState, initState, uniswapStorageStore_blocks])
                  (by simp [evmEL, evmSL, evmE, evmS, uniswapLockEnteredState,
                    uniswapUnlockedState, initState, uniswapStorageStore_substate])
                  (by simp [evmEL, evmSL, evmE, evmS, uniswapLockEnteredState,
                    uniswapUnlockedState, initState, storageStore_executionEnv])
              let evm0S :=
                { evmSL with
                    accountMap := σ'_solm
                    substate := A'_solm
                    createdAccounts := cA' }
              exact (hrev hz).reEquivExecutionRevert hcode hdispatch
                (uniswapDecode_skim_ok hsz36 hcanonTo) (by
                  have hcall0 : typedCallViaEVM config evmSL
                      (EVM.address (uniswapAddressAtSlot evmSL ⟨6⟩)) "balanceOf" 0
                      [.address evmSL.executionEnv.codeOwner] (false, evm0S, o) false := by
                    simpa [evm0S, hz, htargetSource, evmEL, evmSL, evmE, evmS,
                      uniswapLockEnteredState, uniswapUnlockedState, initState,
                      storageStore_executionEnv] using hcallSolm
                  exact uniswapSkimBodyReverts_firstCallFailure evmS evm0S I
                    (by simp only [evmS, initState]; exact hwv)
                    hunlockedSolm hguard0 hcall0)
            · by_cases hshort : o.size < 32
              · obtain ⟨evm0S, hcallAll, _hPostAccounts, _hcreated0, _hσ0, _hgenesis0,
                    _hblocks0, _henv0⟩ :=
                  uniswapSkimFirstBalanceTypedCall_source
                    (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
                    (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                    (cA' := cA') (σ' := σ') (z := z) (o := o)
                    (A_in := A_in) (callGas := callGas) hAccounts hdepth hΘ
                let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
                have hunlockedSolm :
                    Solm.EVM.storageLoad evmS evmS.executionEnv.codeOwner ⟨12⟩ = ⟨1⟩ := by
                  have hword := accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨12⟩ ⟨0⟩
                  simpa [evmS, initState, Solm.EVM.storageLoad, State.lookupAccount,
                    Account.lookupStorage] using (hword ▸ hunlocked)
                have hguard0 : skimToken0GuardTrue evmS I :=
                  skimToken0GuardTrue_initState_of_code hAccounts htoken0NoCode
                have hzTrue : z = true := Bool.eq_true_of_not_eq_false hz
                have hcall0 : typedCallViaEVM config (uniswapLockEnteredState evmS)
                    (EVM.address (uniswapAddressAtSlot (uniswapLockEnteredState evmS) ⟨6⟩))
                    "balanceOf" 0 [.address (uniswapLockEnteredState evmS).executionEnv.codeOwner]
                    (true, evm0S, o) false := by
                  simpa [evmS, hzTrue] using hcallAll
                have hdec0 : config.externalABI.decode? "balanceOf" o = none := by
                  change uniswapExternalABI.decode? "balanceOf" o = none
                  simpa [uniswapExternalABI, uint256, uint256Int, abiUInt256] using
                    (decodeReturnValueWithMode_legacy_uint256_none_short (returndata := o)
                      hshort)
                have hbody :
                    ExecTransitionBody config contract evmS (skimStore I) skimTransition.body
                      .reverted := by
                  exact uniswapSkimBodyReverts_firstCallDecode evmS evm0S I
                    (by simp only [evmS, initState]; exact hwv)
                    hunlockedSolm hguard0 hcall0 hdec0
                exact (hrevShort hzTrue hshort).reEquivExecutionRevert hcode hdispatch
                  (uniswapDecode_skim_ok hsz36 hcanonTo) hbody
              · have hzTrue : z = true := Bool.eq_true_of_not_eq_false hz
                have ho32 : 32 ≤ o.size := not_lt.mp hshort
                obtain ⟨evm0S, balance0, hcall0, hdec0, hPostAccounts0, hcreated0, hσ0,
                    hgenesis0, hblocks0, henv0, _hpostReserve, hbalance0⟩ :=
                  uniswapSkimFirstBalanceReturn_source
                    (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
                    (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                    (cA' := cA') (σ' := σ') (z := z) (o := o)
                    (A_in := A_in) (callGas := callGas) hAccounts hdepth hΘ hzTrue ho32
                let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
                have hunlockedSolm :
                    Solm.EVM.storageLoad evmS evmS.executionEnv.codeOwner ⟨12⟩ = ⟨1⟩ := by
                  have hword := accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨12⟩ ⟨0⟩
                  simpa [evmS, initState, Solm.EVM.storageLoad, State.lookupAccount,
                    Account.lookupStorage] using (hword ▸ hunlocked)
                have hguard0 : skimToken0GuardTrue evmS I :=
                  skimToken0GuardTrue_initState_of_code hAccounts htoken0NoCode
                let reserve0E := UInt256.land
                  (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨112⟩) ⟨1⟩)
                  (uniswapSlotWord ⟨8⟩
                    (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I)
                have hsourceReserve : uniswapReserve0Word evm0S = reserve0E := by
                  have h := uniswapSkimFirstBalanceStaticReserve0 hAccounts hcall0
                  simpa [reserve0E, reserve112Mask, u256_land_comm] using h
                by_cases hlt0 : balance0.toNat < reserve0E.toNat
                · obtain ⟨k5314, C5314, rd5314⟩ := hrevLong hzTrue ho32
                  have rd5314' : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
                      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨5314⟩
                      (balance0 :: reserve0E :: ⟨5325⟩ :: skimToWord I ::
                        UInt256.land solcAddrMask
                          (uniswapSlotWord ⟨6⟩
                            (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I) ::
                        ⟨5330⟩ ::
                        UInt256.land
                          (uniswapSlotWord ⟨7⟩
                            (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I)
                          solcAddrMask ::
                        UInt256.land solcAddrMask
                          (uniswapSlotWord ⟨6⟩
                            (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I) ::
                        skimToWord I :: ⟨570⟩ :: uniswapSelWord I :: [])
                      (balanceOfThisStaticcallMem (UInt256.ofNat I.codeOwner.val) o)
                      balanceOfThisStaticcallActiveWords o (cA', σ') k5314 C5314 := by
                    simpa [hbalance0, reserve0E, reserve112Mask, u256_land_comm] using rd5314
                  obtain ⟨k6879, C6879, rd6879⟩ :=
                    RD.uniswapSkimFirstExcessToSub rd5314'
                      (by simp only [List.length_cons, List.length_nil]; omega)
                  have rd6879' : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
                      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨6879⟩
                      (reserve0E :: balance0 :: ⟨5325⟩ :: skimToWord I ::
                        UInt256.land solcAddrMask
                          (uniswapSlotWord ⟨6⟩
                            (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I) ::
                        ⟨5330⟩ ::
                        UInt256.land
                          (uniswapSlotWord ⟨7⟩
                            (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I)
                          solcAddrMask ::
                        UInt256.land solcAddrMask
                          (uniswapSlotWord ⟨6⟩
                            (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I) ::
                        skimToWord I :: ⟨570⟩ :: uniswapSelWord I :: [])
                      (balanceOfThisStaticcallMem (UInt256.ofNat I.codeOwner.val) o)
                      balanceOfThisStaticcallActiveWords o (cA', σ') k6879 C6879 := by
                    simpa [balanceOfThisStaticcallActiveWords] using rd6879
                  have hmem :
                      (balanceOfThisStaticcallMem (UInt256.ofNat I.codeOwner.val) o).size =
                        164 :=
                    balanceOfThisStaticcallMem_size_of_size_ge
                      (UInt256.ofNat I.codeOwner.val) o ho32 hoSize
                  have hread64 :
                      (balanceOfThisStaticcallMem (UInt256.ofNat I.codeOwner.val) o).readWithPadding
                          64 32 =
                        UInt256.toByteArray ⟨128⟩ :=
                    balanceOfThisStaticcallMem_read64_of_size_ge
                      (UInt256.ofNat I.codeOwner.val) o ho32 hoSize
                  have rdRev :=
                    RD.uniswapSafeMathSubUnderflow_aw6_size164 rd6879' hlt0 hmem hread64
                      (by simp only [List.length_cons, List.length_nil]; omega)
                  have hltSource : balance0.toNat < (uniswapReserve0Word evm0S).toNat := by
                    rw [hsourceReserve]
                    exact hlt0
                  have hbody :
                      ExecTransitionBody config contract evmS (skimStore I) skimTransition.body
                        .reverted := by
                    exact uniswapSkimBodyReverts_firstExcessUnderflow evmS evm0S I
                      (by simp only [evmS, initState]; exact hwv)
                      hunlockedSolm hguard0 hcall0 hdec0 hltSource
                  exact rdRev.reEquivExecutionRevert hcode hdispatch
                    (uniswapDecode_skim_ok hsz36 hcanonTo) hbody
                · have hle0 : reserve0E.toNat ≤ balance0.toNat := not_lt.mp hlt0
                  obtain ⟨k5314, C5314, rd5314⟩ := hrevLong hzTrue ho32
                  have rd5314' : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
                      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨5314⟩
                      (balance0 :: reserve0E :: ⟨5325⟩ :: skimToWord I ::
                        UInt256.land solcAddrMask
                          (uniswapSlotWord ⟨6⟩
                            (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I) ::
                        ⟨5330⟩ ::
                        UInt256.land
                          (uniswapSlotWord ⟨7⟩
                            (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I)
                          solcAddrMask ::
                        UInt256.land solcAddrMask
                          (uniswapSlotWord ⟨6⟩
                            (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I) ::
                        skimToWord I :: ⟨570⟩ :: uniswapSelWord I :: [])
                      (balanceOfThisStaticcallMem (UInt256.ofNat I.codeOwner.val) o)
                      balanceOfThisStaticcallActiveWords o (cA', σ') k5314 C5314 := by
                    simpa [hbalance0, reserve0E, reserve112Mask, u256_land_comm] using rd5314
                  obtain ⟨k6879, C6879, rd6879⟩ :=
                    RD.uniswapSkimFirstExcessToSub rd5314'
                      (by simp only [List.length_cons, List.length_nil]; omega)
                  have rd6879' : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
                      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨6879⟩
                      (reserve0E :: balance0 :: ⟨5325⟩ :: skimToWord I ::
                        UInt256.land solcAddrMask
                          (uniswapSlotWord ⟨6⟩
                            (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I) ::
                        ⟨5330⟩ ::
                        UInt256.land
                          (uniswapSlotWord ⟨7⟩
                            (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I)
                          solcAddrMask ::
                        UInt256.land solcAddrMask
                          (uniswapSlotWord ⟨6⟩
                            (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I) ::
                        skimToWord I :: ⟨570⟩ :: uniswapSelWord I :: [])
                      (balanceOfThisStaticcallMem (UInt256.ofNat I.codeOwner.val) o)
                      balanceOfThisStaticcallActiveWords o (cA', σ') k6879 C6879 := by
                    simpa [balanceOfThisStaticcallActiveWords] using rd6879
                  obtain ⟨k6370, C6370, rd6370⟩ :=
                    RD.uniswapSkimFirstExcessSuccessToSafeTransferEntry rd6879' hle0
                  obtain ⟨cA1, σ1, z1, out1, A_in1, callGas1, _gasArg1,
                      k6595, C6595, hΘsafe0, rd6595, hout1Size⟩ :=
                    UniswapV2Pair.RD.uniswapSkimSafeTransferEntryToCallMade
                      rd6370 ho32 hoSize hdepth
                  let token0WordE :=
                    uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I
                  let token0CleanE := UInt256.land solcAddrMask token0WordE
                  let safeValue0 := UInt256.sub balance0 reserve0E
                  let safeData0 :=
                    (skimSafeTransferCallMem2 (UInt256.ofNat I.codeOwner.val) o
                      (skimToWord I) safeValue0).readWithPadding 292 68
                  have hdata0 :
                      transferCalldata? (skimToAddress I) (skimExcess0Word evm0S balance0) =
                        some safeData0 := by
                    have hencoded :=
                      skimFirstSafeTransferCalldata_canonical (evm0S := evm0S) (I := I)
                        (balance0 := balance0) (reserve0 := reserve0E) hsourceReserve hle0
                    have hread :=
                      skimSafeTransferCallMem2_read292_68
                        (UInt256.ofNat I.codeOwner.val) (o := o) (skimToWord I) safeValue0
                        ho32 hoSize
                    simpa [safeData0, safeValue0, hread] using hencoded
                  let evm0E : EVM.State :=
                    { evm0S with
                      accountMap := σ'
                      createdAccounts := cA'
                      σ₀ := σ₀
                      genesisBlockHeader := gh
                      blocks := bl
                      executionEnv := I }
                  obtain ⟨g1Ret, A1E, hΘsafeEq⟩ := hΘsafe0
                  have hcallE : callViaEVM evm0E
                      (AccountAddress.ofUInt256 (UInt256.land token0CleanE solcAddrMask))
                      0 safeData0
                      (z1,
                        { evm0E with
                          accountMap := σ1
                          substate := A1E
                          createdAccounts := cA1 },
                        out1) := by
                    refine callViaEVM.callMade (perm := true) (g' := g1Ret)
                      wordOfInt_zero.symm ?_ rfl ?_ ?_
                    · refine ⟨callGas1, A_in1, ?_⟩
                      simpa [evm0E, token0CleanE, token0WordE, safeData0, safeValue0, hperm,
                        accountAddress_roundtrip] using hΘsafeEq
                    · show (⟨0⟩ : UInt256) ≤ _
                      exact Fin.zero_le _
                    · intro hdepthEq
                      have hdepthLt : I.depth.val < 1024 := hdepth
                      rw [show evm0E.executionEnv.depth = I.depth by simp [evm0E]] at hdepthEq
                      rw [hdepthEq] at hdepthLt
                      exact absurd hdepthLt (by decide)
                  obtain ⟨σ1S, A1S, htransfer0Raw, hPostTransferAccounts0⟩ :=
                    callViaEVM_accountMapEquiv (storage := config.storage)
                      (evm_evm := evm0E) (evm_solm := evm0S) hcallE hPostAccounts0
                      (by simp [evm0E, hσ0])
                      (by simp [evm0E, hcreated0])
                      (by simp [evm0E, hgenesis0])
                      (by simp [evm0E, hblocks0])
                      (by simp [evm0E])
                      (by
                        simp [evm0E, henv0, uniswapLockEnteredState,
                          uniswapUnlockedState, initState, storageStore_executionEnv])
                  let evm1S : EVM.State :=
                    { evm0S with
                      accountMap := σ1S
                      substate := A1S
                      createdAccounts := cA1 }
                  have htransfer0Raw' : callViaEVM evm0S
                      (AccountAddress.ofUInt256 (UInt256.land token0CleanE solcAddrMask))
                      0 safeData0 (z1, evm1S, out1) := by
                    simpa [evm1S] using htransfer0Raw
                  have htarget0 :
                      AccountAddress.ofUInt256 (UInt256.land token0CleanE solcAddrMask) =
                        EVM.address (uniswapAddressAtSlot (uniswapLockEnteredState evmS) ⟨6⟩) := by
                    let σLockE := sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩
                    let σLockS := sstoreAccountMap I.codeOwner σ_solm ⟨12⟩ ⟨0⟩
                    let token0WordS := uniswapSlotWord ⟨6⟩ σLockS I
                    have hLockAccounts : accountMapEquiv σLockE σLockS := by
                      exact accountMapEquiv_sstoreAccountMap I.codeOwner ⟨12⟩ ⟨0⟩ hAccounts
                    have hslot : token0WordE = token0WordS := by
                      simpa [σLockE, σLockS, token0WordE, token0WordS] using
                        accountMapEquiv_storage_findD hLockAccounts I.codeOwner ⟨6⟩ ⟨0⟩
                    have hcanonClean : token0CleanE.toNat < EVM.addressModulus := by
                      simpa [token0CleanE, token0WordE, u256_land_comm] using
                        solcAddrMask_result_canonical token0WordE
                    have hclean : UInt256.land token0CleanE solcAddrMask = token0CleanE :=
                      solcAddrMask_clean hcanonClean
                    have haddr :
                        AccountAddress.ofUInt256 token0CleanE =
                          uniswapAddressAtSlot (uniswapLockEnteredState evmS) ⟨6⟩ := by
                      simpa [token0CleanE, token0WordE, token0WordS, σLockS, evmS,
                        uniswapLockEnteredState, uniswapUnlockedState, initState,
                        storageStore_accountMap, storageStore_executionEnv, State.lookupAccount,
                        Account.lookupStorage, Solm.EVM.storageLoad, uniswapAddressAtSlot,
                        uniswapSlotWord, hslot, accountAddress_ofUInt256_eq_ofNat_toNat,
                        u256_land_comm]
                    rw [hclean, haddr]
                    exact (uniswapAddress_self (uniswapAddressAtSlot
                      (uniswapLockEnteredState evmS) ⟨6⟩)).symm
                  have htransfer0 : callViaEVM evm0S
                      (EVM.address (uniswapAddressAtSlot (uniswapLockEnteredState evmS) ⟨6⟩))
                      0 safeData0 (z1, evm1S, out1) := by
                    simpa [htarget0] using htransfer0Raw'
                  by_cases hz1False : z1 = false
                  · have htransferFalse : callViaEVM evm0S
                        (EVM.address
                          (uniswapAddressAtSlot (uniswapLockEnteredState evmS) ⟨6⟩))
                        0 safeData0 (false, evm1S, out1) := by
                      simpa [hz1False] using htransfer0
                    have henoughSource :
                        (uniswapReserve0Word evm0S).toNat ≤ balance0.toNat := by
                      rw [hsourceReserve]
                      exact hle0
                    have hbody :
                        ExecTransitionBody config contract evmS (skimStore I) skimTransition.body
                          .reverted := by
                      exact uniswapSkimBodyReverts_firstSafeTransferFailure
                        evmS evm0S evm1S I
                        (by simp only [evmS, initState]; exact hwv)
                        hunlockedSolm hguard0 hcall0 hdec0 henoughSource hdata0
                        htransferFalse
                    have rd6595False : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
                        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨6595⟩
                        (⟨0⟩ :: ⟨360⟩ :: UInt256.land token0CleanE solcAddrMask ::
                          ⟨96⟩ :: ⟨0⟩ :: safeValue0 :: skimToWord I :: token0CleanE ::
                          ⟨5330⟩ ::
                          UInt256.land
                            (uniswapSlotWord ⟨7⟩
                              (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I)
                            solcAddrMask ::
                          token0CleanE :: skimToWord I :: ⟨570⟩ :: uniswapSelWord I :: [])
                        (skimSafeTransferCallMem2 (UInt256.ofNat I.codeOwner.val) o
                          (skimToWord I) safeValue0)
                        (UInt256.ofNat 13) out1 (cA1, σ1) k6595 C6595 := by
                      simpa [hz1False, token0CleanE, token0WordE, safeValue0] using rd6595
                    by_cases hout1Empty : out1.size = 0
                    · have rdRev :=
                        RD.uniswapSkimSafeTransferEmptyFailureReverts
                          rd6595False hout1Empty ho32 hoSize
                      exact rdRev.reEquivExecutionRevert hcode hdispatch
                        (uniswapDecode_skim_ok hsz36 hcanonTo) hbody
                    · by_cases hout1Sign : out1.size < 2 ^ 255
                      · have rdRev :=
                          RD.uniswapSkimSafeTransferNonemptyFailureReverts
                            rd6595False hout1Empty hout1Sign ho32 hoSize
                        exact rdRev.reEquivExecutionRevert hcode hdispatch
                          (uniswapDecode_skim_ok hsz36 hcanonTo) hbody
                      · have hhi : 2 ^ 255 ≤ out1.size := le_of_not_gt hout1Sign
                        have rdRev :=
                          RD.uniswapSkimSafeTransferNonemptyHugeReverts
                            rd6595False hout1Empty hhi hout1Size ho32 hoSize
                        exact rdRev.reEquivExecutionRevert hcode hdispatch
                          (uniswapDecode_skim_ok hsz36 hcanonTo) hbody
                  · have hz1True : z1 = true := Bool.eq_true_of_not_eq_false hz1False
                    have htransferTrue : callViaEVM evm0S
                        (EVM.address
                          (uniswapAddressAtSlot (uniswapLockEnteredState evmS) ⟨6⟩))
                        0 safeData0 (true, evm1S, out1) := by
                      simpa [hz1True] using htransfer0
                    have henoughSource :
                        (uniswapReserve0Word evm0S).toNat ≤ balance0.toNat := by
                      rw [hsourceReserve]
                      exact hle0
                    let token1WordE :=
                      uniswapSlotWord ⟨7⟩
                        (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I
                    let token1CleanE := UInt256.land token1WordE solcAddrMask
                    have htarget1 :
                        AccountAddress.ofUInt256 (UInt256.land token1CleanE solcAddrMask) =
                          uniswapAddressAtSlot (uniswapLockEnteredState evmS) ⟨7⟩ := by
                      let σLockE := sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩
                      let σLockS := sstoreAccountMap I.codeOwner σ_solm ⟨12⟩ ⟨0⟩
                      let token1WordS := uniswapSlotWord ⟨7⟩ σLockS I
                      have hLockAccounts : accountMapEquiv σLockE σLockS := by
                        exact accountMapEquiv_sstoreAccountMap I.codeOwner ⟨12⟩ ⟨0⟩ hAccounts
                      have hslot : token1WordE = token1WordS := by
                        simpa [σLockE, σLockS, token1WordE, token1WordS] using
                          accountMapEquiv_storage_findD hLockAccounts I.codeOwner ⟨7⟩ ⟨0⟩
                      have hcanonClean : token1CleanE.toNat < EVM.addressModulus := by
                        simpa [token1CleanE, token1WordE, u256_land_comm] using
                          solcAddrMask_result_canonical token1WordE
                      have hclean : UInt256.land token1CleanE solcAddrMask = token1CleanE :=
                        solcAddrMask_clean hcanonClean
                      have haddr :
                          AccountAddress.ofUInt256 token1CleanE =
                            uniswapAddressAtSlot (uniswapLockEnteredState evmS) ⟨7⟩ := by
                        simpa [token1CleanE, token1WordE, token1WordS, σLockS, evmS,
                          uniswapLockEnteredState, uniswapUnlockedState, initState,
                          storageStore_accountMap, storageStore_executionEnv, State.lookupAccount,
                          Account.lookupStorage, Solm.EVM.storageLoad, uniswapAddressAtSlot,
                          uniswapSlotWord, hslot, accountAddress_ofUInt256_eq_ofNat_toNat,
                          u256_land_comm]
                      rw [hclean, haddr]
                    have rd6595True : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
                        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨6595⟩
                        (⟨1⟩ :: ⟨360⟩ :: UInt256.land token0CleanE solcAddrMask ::
                          ⟨96⟩ :: ⟨0⟩ :: safeValue0 :: skimToWord I :: token0CleanE ::
                          ⟨5330⟩ :: token1CleanE :: token0CleanE :: skimToWord I ::
                          ⟨570⟩ :: uniswapSelWord I :: [])
                        (skimSafeTransferCallMem2 (UInt256.ofNat I.codeOwner.val) o
                          (skimToWord I) safeValue0)
                        (UInt256.ofNat 13) out1 (cA1, σ1) k6595 C6595 := by
                      simpa [hz1True, token0CleanE, token0WordE, token1CleanE, token1WordE,
                        safeValue0] using rd6595
                    by_cases hout1Empty : out1.size = 0
                    · have hsafe0 :
                          ExecStmt config
                            { contract := contract,
                              locals := skimFirstExcessStore evmS evm0S I balance0 } evm0S
                            (.internalCall "_safeTransfer"
                              [.var "_token0", .var "to", .var "excess0"] "ok0")
                            (.ok
                              { contract := contract,
                                locals := skimFirstSafeTransferStore evmS evm0S I balance0 }
                              evm1S) := by
                        have hs := safeTransferInternalCallReturns_empty
                          (caller :=
                            { contract := contract,
                              locals := skimFirstExcessStore evmS evm0S I balance0 })
                          (evm := evm0S) (evm' := evm1S)
                          (tokenExpr := .var "_token0") (toExpr := .var "to")
                          (valueExpr := .var "excess0") (retVar := "ok0")
                          (token := uniswapAddressAtSlot (uniswapLockEnteredState evmS) ⟨6⟩)
                          (recipient := skimToAddress I)
                          (value := skimExcess0Word evm0S balance0)
                          (calldata := safeData0) (out := out1)
                          rfl
                          (evalExprs_skim_safeTransfer0_args evmS evm0S I balance0)
                          hdata0 htransferTrue hout1Empty
                        simpa [resumeAfterInternalCall, skimFirstSafeTransferStore] using hs
                      obtain ⟨k5330, C5330, rd5330⟩ :=
                        RD.uniswapSkimSafeTransferEmptyReturnTo5330
                          rd6595True hout1Empty ho32 hoSize
                      have hPostTransferAccounts1 : accountMapEquiv σ1 evm1S.accountMap := by
                        simpa [evm1S] using hPostTransferAccounts0
                      by_cases htoken1NoCode :
                          uniswapExtCodeSizeWord σ1
                            (UInt256.land token1CleanE solcAddrMask) = ⟨0⟩
                      · have hguard1 :=
                          skimToken1GuardAfterFirstTransfer_false
                            (σ := σ1) (evm := evmS) (evm0 := evm0S) (evm1 := evm1S)
                            (I := I) (balance0 := balance0) (token1 := token1CleanE)
                            hPostTransferAccounts1 htarget1 htoken1NoCode
                        have hbody :
                            ExecTransitionBody config contract evmS (skimStore I)
                              skimTransition.body .reverted := by
                          exact uniswapSkimBodyReverts_secondNoCode
                            evmS evm0S evm1S I
                            (by simp only [evmS, initState]; exact hwv)
                            hunlockedSolm hguard0 hcall0 hdec0 henoughSource hsafe0 hguard1
                        have rdRev :=
                          RD.uniswapSkimSecondBalanceOfNoCodeReverts
                            (value := safeValue0) (toWord := skimToWord I)
                            (token0 := token0CleanE) (token1 := token1CleanE)
                            (sel := uniswapSelWord I) rd5330 ho32 hoSize htoken1NoCode
                        exact rdRev.reEquivExecutionRevert hcode hdispatch
                          (uniswapDecode_skim_ok hsz36 hcanonTo) hbody
                      · have htoken1Code :
                            uniswapExtCodeSizeWord σ1
                              (UInt256.land token1CleanE solcAddrMask) ≠ ⟨0⟩ :=
                          htoken1NoCode
                        have hguard1 :=
                          skimToken1GuardAfterFirstTransfer_true
                            (σ := σ1) (evm := evmS) (evm0 := evm0S) (evm1 := evm1S)
                            (I := I) (balance0 := balance0) (token1 := token1CleanE)
                            hPostTransferAccounts1 htarget1 htoken1Code
                        obtain ⟨cA2, σ2, z2, out2, A_in2, callGas2, k5273, C5273,
                            hΘ2, rd5273, hout2Size⟩ :=
                          RD.uniswapSkimSecondBalanceOfStaticcallMade
                            (value := safeValue0) (toWord := skimToWord I)
                            (token0 := token0CleanE) (token1 := token1CleanE)
                            (sel := uniswapSelWord I) rd5330 ho32 hoSize hdepth htoken1Code
                        have henv1 : evm1S.executionEnv = I := by
                          simpa [evm1S, evmS, uniswapLockEnteredState, uniswapUnlockedState,
                            initState, storageStore_executionEnv] using henv0
                        obtain ⟨evm2S, hcall1Raw, hPost2, hcreated2, hσ2, hgenesis2,
                            hblocks2, henv2⟩ :=
                          uniswapSkimSecondBalanceTypedCall_source
                            (cA1 := cA1) (gh := gh) (bl := bl) (σ1 := σ1) (σ₀ := σ₀)
                            (I := I) (evm1S := evm1S)
                            (cA2 := cA2) (σ2 := σ2) (z2 := z2) (out2 := out2)
                            (A_in2 := A_in2) (callGas2 := callGas2)
                            (o := o) (toWord := skimToWord I) (value := safeValue0)
                            (token1 := token1CleanE)
                            hPostTransferAccounts1
                            (by simp [evm1S])
                            (by simp [evm1S, hσ0])
                            (by simp [evm1S, hgenesis0])
                            (by simp [evm1S, hblocks0])
                            henv1 hdepth ho32 hoSize hΘ2
                        have htarget1E :
                            AccountAddress.ofUInt256 (UInt256.land token1CleanE solcAddrMask) =
                              EVM.address
                                (uniswapAddressAtSlot (uniswapLockEnteredState evmS) ⟨7⟩) := by
                          change
                            AccountAddress.ofUInt256 (UInt256.land token1CleanE solcAddrMask) =
                              EVM.address
                                (uniswapAddressAtSlot (uniswapLockEnteredState evmS) ⟨7⟩)
                          rw [htarget1]
                          exact
                            (uniswapAddress_self
                              (uniswapAddressAtSlot (uniswapLockEnteredState evmS) ⟨7⟩)).symm
                        have hcall1 : typedCallViaEVM config evm1S
                            (EVM.address
                              (uniswapAddressAtSlot (uniswapLockEnteredState evmS) ⟨7⟩))
                            "balanceOf" 0 [.address evm1S.executionEnv.codeOwner]
                            (z2, evm2S, out2) false := by
                          simpa [htarget1E] using hcall1Raw
                        by_cases hz2False : z2 = false
                        · have hcall1False : typedCallViaEVM config evm1S
                              (EVM.address
                                (uniswapAddressAtSlot (uniswapLockEnteredState evmS) ⟨7⟩))
                              "balanceOf" 0 [.address evm1S.executionEnv.codeOwner]
                              (false, evm2S, out2) false := by
                            simpa [hz2False] using hcall1
                          have hbody :
                              ExecTransitionBody config contract evmS (skimStore I)
                                skimTransition.body .reverted := by
                            exact uniswapSkimBodyReverts_secondCallFailure
                              evmS evm0S evm1S evm2S I
                              (by simp only [evmS, initState]; exact hwv)
                              hunlockedSolm hguard0 hcall0 hdec0 henoughSource hsafe0
                              hguard1 hcall1False
                          have hstatus :
                              (if z2 then (⟨1⟩ : UInt256) else ⟨0⟩) = ⟨0⟩ := by
                            simp [hz2False]
                          have rdRev :=
                            RD.uniswapSkimSecondBalanceCallFailureReverts
                              rd5273 hstatus hout2Size
                              (by simp only [List.length_cons, List.length_nil]; omega)
                          exact rdRev.reEquivExecutionRevert hcode hdispatch
                            (uniswapDecode_skim_ok hsz36 hcanonTo) hbody
                        · have hz2True : z2 = true := Bool.eq_true_of_not_eq_false hz2False
                          have hcall1True : typedCallViaEVM config evm1S
                              (EVM.address
                                (uniswapAddressAtSlot (uniswapLockEnteredState evmS) ⟨7⟩))
                              "balanceOf" 0 [.address evm1S.executionEnv.codeOwner]
                              (true, evm2S, out2) false := by
                            simpa [hz2True] using hcall1
                          have hstatus :
                              (if z2 then (⟨1⟩ : UInt256) else ⟨0⟩) ≠ ⟨0⟩ := by
                            rw [hz2True]
                            decide
                          obtain ⟨k5291, C5291, rd5291⟩ :=
                            RD.uniswapSkimSecondBalanceCallSuccessToDecode
                              rd5273 hstatus
                              (by simp only [List.length_cons, List.length_nil]; omega)
                          by_cases hshort2 : out2.size < 32
                          · have hdec1 : config.externalABI.decode? "balanceOf" out2 = none := by
                              change uniswapExternalABI.decode? "balanceOf" out2 = none
                              simpa [uniswapExternalABI, uint256, uint256Int, abiUInt256] using
                                (decodeReturnValueWithMode_legacy_uint256_none_short
                                  (returndata := out2) hshort2)
                            have hbody :
                                ExecTransitionBody config contract evmS (skimStore I)
                                  skimTransition.body .reverted := by
                              exact uniswapSkimBodyReverts_secondCallDecode
                                evmS evm0S evm1S evm2S I
                                (by simp only [evmS, initState]; exact hwv)
                                hunlockedSolm hguard0 hcall0 hdec0 henoughSource hsafe0
                                hguard1 hcall1True hdec1
                            have rdRev :=
                              RD.uniswapSkimSecondBalanceReturnWordDecodeShortReverts
                                rd5291 ho32 hoSize hshort2 hout2Size
                                (by simp only [List.length_cons, List.length_nil]; omega)
                            exact rdRev.reEquivExecutionRevert hcode hdispatch
                              (uniswapDecode_skim_ok hsz36 hcanonTo) hbody
                          · have ho32_2 : 32 ≤ out2.size := not_lt.mp hshort2
                            let balance1 :=
                              UInt256.ofNat (fromByteArrayBigEndian (out2.extract 0 32))
                            have hdec1 :
                                config.externalABI.decode? "balanceOf" out2 =
                                  some (skimBalanceValue balance1) := by
                              simpa [balance1] using
                                uniswapSkimBalanceOfDecode_ok (returndata := out2) ho32_2
                            let reserve1E :=
                              UInt256.land reserve112Mask
                                (UInt256.div (uniswapSlotWord ⟨8⟩ σ1 I) reserve112Shift)
                            have hsourceReserve1 : uniswapReserve1Word evm2S = reserve1E := by
                              have h :=
                                uniswapSkimSecondBalanceStaticReserve1
                                  hPostTransferAccounts1 henv1 hcall1True
                              simpa [reserve1E, u256_land_comm] using h
                            obtain ⟨k5314, C5314, rd5314⟩ :=
                              RD.uniswapSkimSecondBalanceReturnWordDecodeOk
                                rd5291 ho32 hoSize ho32_2 hout2Size
                                (by simp only [List.length_cons, List.length_nil]; omega)
                            have rd5314' : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
                                (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                                ⟨5314⟩
                                (balance1 :: reserve1E :: ⟨5325⟩ :: skimToWord I ::
                                  token1CleanE :: ⟨5433⟩ ::
                                  token1CleanE :: token0CleanE :: skimToWord I ::
                                  ⟨570⟩ :: uniswapSelWord I :: [])
                                (skimSecondBalanceStaticcallMem
                                  (UInt256.ofNat I.codeOwner.val) o (skimToWord I)
                                  safeValue0 out2)
                                (UInt256.ofNat 13) out2 (cA2, σ2) k5314 C5314 := by
                              simpa [balance1, reserve1E, u256_land_comm] using rd5314
                            by_cases hlt1 : balance1.toNat < reserve1E.toNat
                            · obtain ⟨k6879, C6879, rd6879⟩ :=
                                RD.uniswapSkimFirstExcessToSub rd5314'
                                  (by simp only [List.length_cons, List.length_nil]; omega)
                              have rd6879' : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
                                  (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                                  ⟨6879⟩
                                  (reserve1E :: balance1 :: ⟨5325⟩ :: skimToWord I ::
                                    token1CleanE :: ⟨5433⟩ ::
                                    token1CleanE :: token0CleanE :: skimToWord I ::
                                    ⟨570⟩ :: uniswapSelWord I :: [])
                                  (skimSecondBalanceStaticcallMem
                                    (UInt256.ofNat I.codeOwner.val) o (skimToWord I)
                                    safeValue0 out2)
                                  (UInt256.ofNat 13) out2 (cA2, σ2) k6879 C6879 := by
                                simpa using rd6879
                              have hmem :
                                  (skimSecondBalanceStaticcallMem
                                    (UInt256.ofNat I.codeOwner.val) o (skimToWord I)
                                    safeValue0 out2).size = 388 :=
                                skimSecondBalanceStaticcallMem_size_of_size_ge
                                  (UInt256.ofNat I.codeOwner.val) (skimToWord I) safeValue0
                                  out2 ho32 hoSize ho32_2 hout2Size
                              have hread64 :
                                  (skimSecondBalanceStaticcallMem
                                    (UInt256.ofNat I.codeOwner.val) o (skimToWord I)
                                    safeValue0 out2).readWithPadding 64 32 =
                                    UInt256.toByteArray ⟨292⟩ :=
                                skimSecondBalanceStaticcallMem_read64_of_size_ge
                                  (UInt256.ofNat I.codeOwner.val) (skimToWord I) safeValue0
                                  out2 ho32 hoSize ho32_2 hout2Size
                              have rdRev :=
                                RD.uniswapSafeMathSubUnderflow_aw13_free292
                                  rd6879' hlt1 hmem hread64
                                  (by simp only [List.length_cons, List.length_nil]; omega)
                              have hltSource :
                                  balance1.toNat < (uniswapReserve1Word evm2S).toNat := by
                                rw [hsourceReserve1]
                                exact hlt1
                              have hbody :
                                  ExecTransitionBody config contract evmS (skimStore I)
                                    skimTransition.body .reverted := by
                                exact uniswapSkimBodyReverts_secondExcessUnderflow
                                  evmS evm0S evm1S evm2S I
                                  (by simp only [evmS, initState]; exact hwv)
                                  hunlockedSolm hguard0 hcall0 hdec0 henoughSource hsafe0
                                  hguard1 hcall1True hdec1 hltSource
                              exact rdRev.reEquivExecutionRevert hcode hdispatch
                                (uniswapDecode_skim_ok hsz36 hcanonTo) hbody
                            · have hle1 : reserve1E.toNat ≤ balance1.toNat := not_lt.mp hlt1
                              obtain ⟨k6879, C6879, rd6879⟩ :=
                                RD.uniswapSkimFirstExcessToSub rd5314'
                                  (by simp only [List.length_cons, List.length_nil]; omega)
                              have rd6879' : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
                                  (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                                  ⟨6879⟩
                                  (reserve1E :: balance1 :: ⟨5325⟩ :: skimToWord I ::
                                    token1CleanE :: ⟨5433⟩ ::
                                    token1CleanE :: token0CleanE :: skimToWord I ::
                                    ⟨570⟩ :: uniswapSelWord I :: [])
                                  (skimSecondBalanceStaticcallMem
                                    (UInt256.ofNat I.codeOwner.val) o (skimToWord I)
                                    safeValue0 out2)
                                  (UInt256.ofNat 13) out2 (cA2, σ2) k6879 C6879 := by
                                simpa using rd6879
                              obtain ⟨k6370, C6370, rd6370⟩ :=
                                RD.uniswapSkimExcessSuccessToSafeTransferEntry rd6879' hle1
                                  (by simp only [List.length_cons, List.length_nil]; omega)
                              let safeValue1 := UInt256.sub balance1 reserve1E
                              let safeData1 :=
                                (skimSecondSafeTransferCallMem2
                                  (UInt256.ofNat I.codeOwner.val) o (skimToWord I)
                                  safeValue0 out2 safeValue1).readWithPadding 456 68
                              have hdata1 :
                                  transferCalldata? (skimToAddress I)
                                      (skimExcess1Word evm2S balance1) =
                                    some safeData1 := by
                                have hencoded :=
                                  skimSecondSafeTransferCalldata_canonical
                                    (evm2S := evm2S) (I := I) (o := o) (out2 := out2)
                                    (balance1 := balance1) (reserve1 := reserve1E)
                                    (prevValue := safeValue0) hsourceReserve1 hle1
                                    ho32 hoSize ho32_2 hout2Size
                                simpa [safeData1, safeValue1] using hencoded
                              have rd6370' : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
                                  (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                                  ⟨6370⟩
                                  (safeValue1 :: skimToWord I :: token1CleanE :: ⟨5433⟩ ::
                                    token1CleanE :: token0CleanE :: skimToWord I ::
                                    ⟨570⟩ :: uniswapSelWord I :: [])
                                  (skimSecondBalanceStaticcallMem
                                    (UInt256.ofNat I.codeOwner.val) o (skimToWord I)
                                    safeValue0 out2)
                                  (UInt256.ofNat 13) out2 (cA2, σ2) k6370 C6370 := by
                                simpa [safeValue1] using rd6370
                              obtain ⟨cA3, σ3, z3, out3, A_in3, callGas3, _gasArg3,
                                  k6595b, C6595b, hΘsafe1, rd6595b, hout3Size⟩ :=
                                RD.uniswapSkimSecondSafeTransferEntryToCallMade
                                  rd6370' ho32 hoSize ho32_2 hout2Size hdepth
                              let evm2E : EVM.State :=
                                { evm2S with
                                  accountMap := σ2
                                  createdAccounts := cA2
                                  σ₀ := σ₀
                                  genesisBlockHeader := gh
                                  blocks := bl
                                  executionEnv := I }
                              obtain ⟨g3Ret, A3E, hΘsafeEq1⟩ := hΘsafe1
                              have hcallE1 : callViaEVM evm2E
                                  (AccountAddress.ofUInt256
                                    (UInt256.land token1CleanE solcAddrMask))
                                  0 safeData1
                                  (z3,
                                    { evm2E with
                                      accountMap := σ3
                                      substate := A3E
                                      createdAccounts := cA3 },
                                    out3) := by
                                refine callViaEVM.callMade (perm := true) (g' := g3Ret)
                                  wordOfInt_zero.symm ?_ rfl ?_ ?_
                                · refine ⟨callGas3, A_in3, ?_⟩
                                  simpa [evm2E, safeData1, safeValue1, hperm,
                                    accountAddress_roundtrip] using hΘsafeEq1
                                · show (⟨0⟩ : UInt256) ≤ _
                                  exact Fin.zero_le _
                                · intro hdepthEq
                                  have hdepthLt : I.depth.val < 1024 := hdepth
                                  rw [show evm2E.executionEnv.depth = I.depth by simp [evm2E]]
                                    at hdepthEq
                                  rw [hdepthEq] at hdepthLt
                                  exact absurd hdepthLt (by decide)
                              obtain ⟨σ3S, A3S, htransfer1Raw, hPostTransferAccounts2⟩ :=
                                callViaEVM_accountMapEquiv (storage := config.storage)
                                  (evm_evm := evm2E) (evm_solm := evm2S)
                                  hcallE1 hPost2
                                  (by simp [evm2E, hσ2])
                                  (by simp [evm2E, hcreated2])
                                  (by simp [evm2E, hgenesis2])
                                  (by simp [evm2E, hblocks2])
                                  (by simp [evm2E])
                                  (by simp [evm2E, henv2, henv1])
                              let evm3S : EVM.State :=
                                { evm2S with
                                  accountMap := σ3S
                                  substate := A3S
                                  createdAccounts := cA3 }
                              have htransfer1Raw' : callViaEVM evm2S
                                  (AccountAddress.ofUInt256
                                    (UInt256.land token1CleanE solcAddrMask))
                                  0 safeData1 (z3, evm3S, out3) := by
                                simpa [evm3S] using htransfer1Raw
                              have htransfer1Target :
                                  AccountAddress.ofUInt256
                                      (UInt256.land token1CleanE solcAddrMask) =
                                    EVM.address
                                      (uniswapAddressAtSlot
                                        (uniswapLockEnteredState evmS) ⟨7⟩) := by
                                rw [htarget1]
                                exact (uniswapAddress_self
                                  (uniswapAddressAtSlot (uniswapLockEnteredState evmS) ⟨7⟩)).symm
                              have htransfer1 : callViaEVM evm2S
                                  (EVM.address
                                    (uniswapAddressAtSlot (uniswapLockEnteredState evmS) ⟨7⟩))
                                  0 safeData1 (z3, evm3S, out3) := by
                                simpa [htransfer1Target] using htransfer1Raw'
                              have hPostTransferAccounts3 :
                                  accountMapEquiv σ3 evm3S.accountMap := by
                                simpa [evm3S] using hPostTransferAccounts2
                              have henv3 : evm3S.executionEnv = I := by
                                simpa [evm3S] using henv2.trans henv1
                              have henough1Source :
                                  (uniswapReserve1Word evm2S).toNat ≤ balance1.toNat := by
                                rw [hsourceReserve1]
                                exact hle1
                              have hfinish :
                                  ∀ {mem outRet : ByteArray} {aw : UInt256} {kR CR : ℕ},
                                    RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
                                      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                                      ⟨5433⟩
                                      (token1CleanE :: token0CleanE :: skimToWord I ::
                                        ⟨570⟩ :: uniswapSelWord I :: [])
                                      mem aw outRet (cA3, σ3) kR CR →
                                    ExecStmt config
                                      { contract := contract,
                                        locals :=
                                          skimSecondExcessStore evmS evm0S evm2S I
                                            balance0 balance1 } evm2S
                                      (.internalCall "_safeTransfer"
                                        [.var "_token1", .var "to", .var "excess1"] "ok1")
                                      (.ok
                                        { contract := contract,
                                          locals :=
                                            skimSecondSafeTransferStore evmS evm0S evm2S I
                                              balance0 balance1 }
                                        evm3S) →
                                    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀
                                      g A I := by
                                intro mem outRet aw kR CR rd5433 hsafe1
                                have rdRet :=
                                  RD.uniswapSkimAfterSecondSafeTransferToReturn rd5433 hperm
                                have hbody :
                                    ExecTransitionBody config contract evmS (skimStore I)
                                      skimTransition.body
                                      (.returned
                                        { contract := contract,
                                          locals :=
                                            skimSecondSafeTransferStore evmS evm0S evm2S I
                                              balance0 balance1 }
                                        (uniswapLockExitedState evm3S) none) := by
                                  exact uniswapSkimBodyReturns
                                    evmS evm0S evm1S evm2S evm3S I
                                    (by simp only [evmS, initState]; exact hwv)
                                    hunlockedSolm hguard0 hcall0 hdec0 henoughSource hsafe0
                                    hguard1 hcall1True hdec1 henough1Source hsafe1
                                have hCreatedRet :
                                    cA3 = (uniswapLockExitedState evm3S).createdAccounts := by
                                  simp [uniswapLockExitedState, uniswapUnlockedState, evm3S,
                                    storageStore_createdAccounts]
                                have hAccountsRet :
                                    accountMapEquiv
                                      (sstoreAccountMap I.codeOwner σ3 ⟨12⟩ ⟨1⟩)
                                      (uniswapLockExitedState evm3S).accountMap := by
                                  have hs :=
                                    accountMapEquiv_sstoreAccountMap I.codeOwner ⟨12⟩ ⟨1⟩
                                      hPostTransferAccounts3
                                  simpa [uniswapLockExitedState, uniswapUnlockedState,
                                    storageStore_accountMap, henv3] using hs
                                exact rdRet.reEquivExecutionGenAccountMapEquiv hcode hdispatch
                                  (uniswapDecode_skim_ok hsz36 hcanonTo) hbody hCreatedRet
                                  hAccountsRet (returnEquiv.void rfl rfl rfl)
                              by_cases hz3False : z3 = false
                              · have htransfer1False : callViaEVM evm2S
                                    (EVM.address
                                      (uniswapAddressAtSlot
                                        (uniswapLockEnteredState evmS) ⟨7⟩))
                                    0 safeData1 (false, evm3S, out3) := by
                                  simpa [hz3False] using htransfer1
                                have hbody :
                                    ExecTransitionBody config contract evmS (skimStore I)
                                      skimTransition.body .reverted := by
                                  exact uniswapSkimBodyReverts_secondSafeTransferFailure
                                    evmS evm0S evm1S evm2S evm3S I
                                    (by simp only [evmS, initState]; exact hwv)
                                    hunlockedSolm hguard0 hcall0 hdec0 henoughSource hsafe0
                                    hguard1 hcall1True hdec1 henough1Source hdata1
                                    htransfer1False
                                have rd6595False : RD uniswapV2PairBytecode I
                                    (Sat256.ofUInt256 g)
                                    (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                                    ⟨6595⟩
                                    (⟨0⟩ :: ⟨524⟩ ::
                                      UInt256.land token1CleanE solcAddrMask :: ⟨96⟩ :: ⟨0⟩ ::
                                      safeValue1 :: skimToWord I :: token1CleanE :: ⟨5433⟩ ::
                                      token1CleanE :: token0CleanE :: skimToWord I ::
                                      ⟨570⟩ :: uniswapSelWord I :: [])
                                    (skimSecondSafeTransferCallMem2
                                      (UInt256.ofNat I.codeOwner.val) o (skimToWord I)
                                      safeValue0 out2 safeValue1)
                                    (UInt256.ofNat 18) out3 (cA3, σ3) k6595b C6595b := by
                                  simpa [hz3False, safeValue1] using rd6595b
                                by_cases hout3Empty : out3.size = 0
                                · have rdRev :=
                                    RD.uniswapSkimSecondSafeTransferEmptyFailureReverts
                                      rd6595False hout3Empty ho32 hoSize ho32_2 hout2Size
                                  exact rdRev.reEquivExecutionRevert hcode hdispatch
                                    (uniswapDecode_skim_ok hsz36 hcanonTo) hbody
                                · by_cases hout3Sign : out3.size < 2 ^ 255
                                  · have rdRev :=
                                      RD.uniswapSkimSecondSafeTransferNonemptyFailureReverts
                                        rd6595False hout3Empty hout3Sign ho32 hoSize
                                        ho32_2 hout2Size
                                    exact rdRev.reEquivExecutionRevert hcode hdispatch
                                      (uniswapDecode_skim_ok hsz36 hcanonTo) hbody
                                  · have hhi : 2 ^ 255 ≤ out3.size := le_of_not_gt hout3Sign
                                    have rdRev :=
                                      RD.uniswapSkimSecondSafeTransferNonemptyHugeReverts
                                        rd6595False hout3Empty hhi hout3Size ho32 hoSize
                                        ho32_2 hout2Size
                                    exact rdRev.reEquivExecutionRevert hcode hdispatch
                                      (uniswapDecode_skim_ok hsz36 hcanonTo) hbody
                              · have hz3True : z3 = true := Bool.eq_true_of_not_eq_false hz3False
                                have htransfer1True : callViaEVM evm2S
                                    (EVM.address
                                      (uniswapAddressAtSlot
                                        (uniswapLockEnteredState evmS) ⟨7⟩))
                                    0 safeData1 (true, evm3S, out3) := by
                                  simpa [hz3True] using htransfer1
                                have rd6595True : RD uniswapV2PairBytecode I
                                    (Sat256.ofUInt256 g)
                                    (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                                    ⟨6595⟩
                                    (⟨1⟩ :: ⟨524⟩ ::
                                      UInt256.land token1CleanE solcAddrMask :: ⟨96⟩ :: ⟨0⟩ ::
                                      safeValue1 :: skimToWord I :: token1CleanE :: ⟨5433⟩ ::
                                      token1CleanE :: token0CleanE :: skimToWord I ::
                                      ⟨570⟩ :: uniswapSelWord I :: [])
                                    (skimSecondSafeTransferCallMem2
                                      (UInt256.ofNat I.codeOwner.val) o (skimToWord I)
                                      safeValue0 out2 safeValue1)
                                    (UInt256.ofNat 18) out3 (cA3, σ3) k6595b C6595b := by
                                  simpa [hz3True, safeValue1] using rd6595b
                                by_cases hout3Empty : out3.size = 0
                                · have hsafe1 :
                                      ExecStmt config
                                        { contract := contract,
                                          locals :=
                                            skimSecondExcessStore evmS evm0S evm2S I
                                              balance0 balance1 } evm2S
                                        (.internalCall "_safeTransfer"
                                          [.var "_token1", .var "to", .var "excess1"] "ok1")
                                        (.ok
                                          { contract := contract,
                                            locals :=
                                              skimSecondSafeTransferStore evmS evm0S evm2S I
                                                balance0 balance1 }
                                          evm3S) := by
                                    have hs := safeTransferInternalCallReturns_empty
                                      (caller :=
                                        { contract := contract,
                                          locals :=
                                            skimSecondExcessStore evmS evm0S evm2S I
                                              balance0 balance1 })
                                      (evm := evm2S) (evm' := evm3S)
                                      (tokenExpr := .var "_token1") (toExpr := .var "to")
                                      (valueExpr := .var "excess1") (retVar := "ok1")
                                      (token :=
                                        uniswapAddressAtSlot (uniswapLockEnteredState evmS) ⟨7⟩)
                                      (recipient := skimToAddress I)
                                      (value := skimExcess1Word evm2S balance1)
                                      (calldata := safeData1) (out := out3)
                                      rfl
                                      (evalExprs_skim_safeTransfer1_args
                                        evmS evm0S evm2S I balance0 balance1)
                                      hdata1 htransfer1True hout3Empty
                                    simpa [resumeAfterInternalCall, skimSecondSafeTransferStore]
                                      using hs
                                  obtain ⟨k5433, C5433, rd5433⟩ :=
                                    RD.uniswapSkimSecondSafeTransferEmptyReturnTo5433
                                      rd6595True hout3Empty ho32 hoSize ho32_2 hout2Size
                                  exact hfinish rd5433 hsafe1
                                · by_cases hout3Sign : out3.size < 2 ^ 255
                                  · by_cases hshort3 : out3.size < 32
                                    · have hdecSafe1 :
                                          ABI.decodeReturnValueWithMode?
                                              config.abiDecodeMode boolTy out3 =
                                            none := by
                                        change
                                          ABI.decodeReturnValueWithMode?
                                              DecodeMode.legacySolc05 boolTy out3 =
                                            none
                                        exact decodeReturnValueWithMode_legacy_bool_none_short
                                          (returndata := out3) hshort3
                                      have hbody :
                                          ExecTransitionBody config contract evmS (skimStore I)
                                            skimTransition.body .reverted := by
                                        exact uniswapSkimBodyReverts_secondSafeTransferDecode
                                          evmS evm0S evm1S evm2S evm3S I
                                          (by simp only [evmS, initState]; exact hwv)
                                          hunlockedSolm hguard0 hcall0 hdec0 henoughSource hsafe0
                                          hguard1 hcall1True hdec1 henough1Source hdata1
                                          htransfer1True hout3Empty hdecSafe1
                                      have rdRev :=
                                        RD.uniswapSkimSecondSafeTransferNonemptyShortReverts
                                          rd6595True hout3Empty hshort3 hout3Sign ho32 hoSize
                                          ho32_2 hout2Size
                                      exact rdRev.reEquivExecutionRevert hcode hdispatch
                                        (uniswapDecode_skim_ok hsz36 hcanonTo) hbody
                                    · have hout332 : 32 ≤ out3.size := not_lt.mp hshort3
                                      let safeWord1 :=
                                        UInt256.ofNat
                                          (fromByteArrayBigEndian (out3.extract 0 32))
                                      by_cases hword1 : safeWord1 = ⟨0⟩
                                      · have hdecSafe1 :
                                            ABI.decodeReturnValueWithMode?
                                                config.abiDecodeMode boolTy out3 =
                                              some (.bool false) := by
                                          change
                                            ABI.decodeReturnValueWithMode?
                                                DecodeMode.legacySolc05 boolTy out3 =
                                              some (.bool false)
                                          exact decodeReturnValueWithMode_legacy_bool_false
                                            (returndata := out3) hout332 hout3Sign hword1
                                        have hbody :
                                            ExecTransitionBody config contract evmS (skimStore I)
                                              skimTransition.body .reverted := by
                                          exact uniswapSkimBodyReverts_secondSafeTransferDecodeFalse
                                            evmS evm0S evm1S evm2S evm3S I
                                            (by simp only [evmS, initState]; exact hwv)
                                            hunlockedSolm hguard0 hcall0 hdec0 henoughSource hsafe0
                                            hguard1 hcall1True hdec1 henough1Source hdata1
                                            htransfer1True hout3Empty hdecSafe1
                                        have rdRev :=
                                          RD.uniswapSkimSecondSafeTransferNonemptyFalseReverts
                                            rd6595True hout3Empty hout332 hout3Sign hword1 ho32
                                            hoSize ho32_2 hout2Size
                                        exact rdRev.reEquivExecutionRevert hcode hdispatch
                                          (uniswapDecode_skim_ok hsz36 hcanonTo) hbody
                                      · have hdecSafe1 :
                                            ABI.decodeReturnValueWithMode?
                                                config.abiDecodeMode boolTy out3 =
                                              some (.bool true) := by
                                          change
                                            ABI.decodeReturnValueWithMode?
                                                DecodeMode.legacySolc05 boolTy out3 =
                                              some (.bool true)
                                          exact decodeReturnValueWithMode_legacy_bool_true
                                            (returndata := out3) hout332 hout3Sign hword1
                                        have hsafe1 :
                                            ExecStmt config
                                              { contract := contract,
                                                locals :=
                                                  skimSecondExcessStore evmS evm0S evm2S I
                                                    balance0 balance1 } evm2S
                                              (.internalCall "_safeTransfer"
                                                [.var "_token1", .var "to", .var "excess1"]
                                                "ok1")
                                              (.ok
                                                { contract := contract,
                                                  locals :=
                                                    skimSecondSafeTransferStore evmS evm0S evm2S I
                                                      balance0 balance1 }
                                                evm3S) := by
                                          have hs := safeTransferInternalCallReturns_decodeTrue
                                            (caller :=
                                              { contract := contract,
                                                locals :=
                                                  skimSecondExcessStore evmS evm0S evm2S I
                                                    balance0 balance1 })
                                            (evm := evm2S) (evm' := evm3S)
                                            (tokenExpr := .var "_token1") (toExpr := .var "to")
                                            (valueExpr := .var "excess1") (retVar := "ok1")
                                            (token :=
                                              uniswapAddressAtSlot
                                                (uniswapLockEnteredState evmS) ⟨7⟩)
                                            (recipient := skimToAddress I)
                                            (value := skimExcess1Word evm2S balance1)
                                            (calldata := safeData1) (out := out3)
                                            rfl
                                            (evalExprs_skim_safeTransfer1_args
                                              evmS evm0S evm2S I balance0 balance1)
                                            hdata1 htransfer1True hout3Empty hdecSafe1
                                          simpa [resumeAfterInternalCall, skimSecondSafeTransferStore]
                                            using hs
                                        obtain ⟨k5433, C5433, rd5433⟩ :=
                                          RD.uniswapSkimSecondSafeTransferNonemptyTrueToRet
                                            rd6595True hout3Empty hout332 hout3Sign hword1 ho32
                                            hoSize ho32_2 hout2Size (by jump_dest)
                                        exact hfinish rd5433 hsafe1
                                  · have hhi : 2 ^ 255 ≤ out3.size := le_of_not_gt hout3Sign
                                    have hdecSafe1 :
                                        ABI.decodeReturnValueWithMode?
                                            config.abiDecodeMode boolTy out3 =
                                          none := by
                                      change
                                        ABI.decodeReturnValueWithMode?
                                            DecodeMode.legacySolc05 boolTy out3 =
                                          none
                                      exact decodeReturnValueWithMode_legacy_bool_none_huge
                                        (returndata := out3) hhi
                                    have hbody :
                                        ExecTransitionBody config contract evmS (skimStore I)
                                          skimTransition.body .reverted := by
                                      exact uniswapSkimBodyReverts_secondSafeTransferDecode
                                        evmS evm0S evm1S evm2S evm3S I
                                        (by simp only [evmS, initState]; exact hwv)
                                        hunlockedSolm hguard0 hcall0 hdec0 henoughSource hsafe0
                                        hguard1 hcall1True hdec1 henough1Source hdata1
                                        htransfer1True hout3Empty hdecSafe1
                                    have rdRev :=
                                      RD.uniswapSkimSecondSafeTransferNonemptyHugeReverts
                                        rd6595True hout3Empty hhi hout3Size ho32 hoSize
                                        ho32_2 hout2Size
                                    exact rdRev.reEquivExecutionRevert hcode hdispatch
                                      (uniswapDecode_skim_ok hsz36 hcanonTo) hbody
                    · by_cases hout1Sign : out1.size < 2 ^ 255
                      · by_cases hshort1 : out1.size < 32
                        · have hdecSafe0 :
                              ABI.decodeReturnValueWithMode? config.abiDecodeMode boolTy out1 =
                                none := by
                            change
                              ABI.decodeReturnValueWithMode? DecodeMode.legacySolc05 boolTy out1 =
                                none
                            exact decodeReturnValueWithMode_legacy_bool_none_short
                              (returndata := out1) hshort1
                          have hbody :
                              ExecTransitionBody config contract evmS (skimStore I)
                                skimTransition.body .reverted := by
                            exact uniswapSkimBodyReverts_firstSafeTransferDecode
                              evmS evm0S evm1S I
                              (by simp only [evmS, initState]; exact hwv)
                              hunlockedSolm hguard0 hcall0 hdec0 henoughSource hdata0
                              htransferTrue hout1Empty hdecSafe0
                          have rdRev :=
                            RD.uniswapSkimSafeTransferNonemptyShortReverts
                              rd6595True hout1Empty hshort1 hout1Sign ho32 hoSize
                          exact rdRev.reEquivExecutionRevert hcode hdispatch
                            (uniswapDecode_skim_ok hsz36 hcanonTo) hbody
                        · have hout132 : 32 ≤ out1.size := not_lt.mp hshort1
                          let safeWord0 :=
                            UInt256.ofNat (fromByteArrayBigEndian (out1.extract 0 32))
                          by_cases hword0 : safeWord0 = ⟨0⟩
                          · have hdecSafe0 :
                                ABI.decodeReturnValueWithMode? config.abiDecodeMode boolTy out1 =
                                  some (.bool false) := by
                              change
                                ABI.decodeReturnValueWithMode? DecodeMode.legacySolc05 boolTy out1 =
                                  some (.bool false)
                              exact decodeReturnValueWithMode_legacy_bool_false
                                (returndata := out1) hout132 hout1Sign hword0
                            have hbody :
                                ExecTransitionBody config contract evmS (skimStore I)
                                  skimTransition.body .reverted := by
                              exact uniswapSkimBodyReverts_firstSafeTransferDecodeFalse
                                evmS evm0S evm1S I
                                (by simp only [evmS, initState]; exact hwv)
                                hunlockedSolm hguard0 hcall0 hdec0 henoughSource hdata0
                                htransferTrue hout1Empty hdecSafe0
                            have rdRev :=
                              RD.uniswapSkimSafeTransferNonemptyFalseReverts
                                rd6595True hout1Empty hout132 hout1Sign hword0 ho32 hoSize
                            exact rdRev.reEquivExecutionRevert hcode hdispatch
                              (uniswapDecode_skim_ok hsz36 hcanonTo) hbody
                          · have hdecSafe0 :
                                ABI.decodeReturnValueWithMode? config.abiDecodeMode boolTy out1 =
                                  some (.bool true) := by
                              change
                                ABI.decodeReturnValueWithMode? DecodeMode.legacySolc05 boolTy out1 =
                                  some (.bool true)
                              exact decodeReturnValueWithMode_legacy_bool_true
                                (returndata := out1) hout132 hout1Sign hword0
                            have hsafe0 :
                                ExecStmt config
                                  { contract := contract,
                                    locals := skimFirstExcessStore evmS evm0S I balance0 } evm0S
                                  (.internalCall "_safeTransfer"
                                    [.var "_token0", .var "to", .var "excess0"] "ok0")
                                  (.ok
                                    { contract := contract,
                                      locals := skimFirstSafeTransferStore evmS evm0S I balance0 }
                                    evm1S) := by
                              have hs := safeTransferInternalCallReturns_decodeTrue
                                (caller :=
                                  { contract := contract,
                                    locals := skimFirstExcessStore evmS evm0S I balance0 })
                                (evm := evm0S) (evm' := evm1S)
                                (tokenExpr := .var "_token0") (toExpr := .var "to")
                                (valueExpr := .var "excess0") (retVar := "ok0")
                                (token := uniswapAddressAtSlot (uniswapLockEnteredState evmS) ⟨6⟩)
                                (recipient := skimToAddress I)
                                (value := skimExcess0Word evm0S balance0)
                                (calldata := safeData0) (out := out1)
                                rfl
                                (evalExprs_skim_safeTransfer0_args evmS evm0S I balance0)
                                hdata0 htransferTrue hout1Empty hdecSafe0
                              simpa [resumeAfterInternalCall, skimFirstSafeTransferStore] using hs
                            obtain ⟨k5330, C5330, rd5330⟩ :=
                              RD.uniswapSkimSafeTransferNonemptyTrueToRet
                                rd6595True hout1Empty hout132 hout1Sign hword0 ho32 hoSize
                                (by jump_dest)
                            have hPostTransferAccounts1 :
                                accountMapEquiv σ1 evm1S.accountMap := by
                              simpa [evm1S] using hPostTransferAccounts0
                            have hout1Small : out1.size < 2 ^ 138 := by
                              have htheta :=
                                Theta_returnData_size_lt_2pow138 I.blobVersionedHashes cA'
                                  ((initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I).genesisBlockHeader)
                                  (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I).blocks
                                  σ'
                                  (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I).σ₀
                                  A_in1
                                  (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner.val))
                                  I.sender
                                  (AccountAddress.ofUInt256
                                    (UInt256.land token0CleanE solcAddrMask))
                                  (toExecute σ'
                                    (AccountAddress.ofUInt256
                                      (UInt256.land token0CleanE solcAddrMask)))
                                  callGas1 (UInt256.ofNat I.gasPrice) ⟨0⟩ ⟨0⟩
                                  ((skimSafeTransferCallMem2 (UInt256.ofNat I.codeOwner.val) o
                                    (skimToWord I) (balance0.sub reserve0E)).readWithPadding
                                    292 68)
                                  (I.depth + 1) I.header I.perm
                                  (by
                                    exact
                                      Ethereum.EVM.ByteArray.readWithPadding_size_lt_uint256
                                        _ _ _)
                              rw [← hΘsafeEq] at htheta
                              simpa using htheta
                            by_cases htoken1NoCode :
                                uniswapExtCodeSizeWord σ1
                                  (UInt256.land token1CleanE solcAddrMask) = ⟨0⟩
                            · have hguard1 :=
                                skimToken1GuardAfterFirstTransfer_false
                                  (σ := σ1) (evm := evmS) (evm0 := evm0S) (evm1 := evm1S)
                                  (I := I) (balance0 := balance0) (token1 := token1CleanE)
                                  hPostTransferAccounts1 htarget1 htoken1NoCode
                              have hbody :
                                  ExecTransitionBody config contract evmS (skimStore I)
                                    skimTransition.body .reverted := by
                                exact uniswapSkimBodyReverts_secondNoCode
                                  evmS evm0S evm1S I
                                  (by simp only [evmS, initState]; exact hwv)
                                  hunlockedSolm hguard0 hcall0 hdec0 henoughSource hsafe0 hguard1
                              have rdRev :=
                                RD.uniswapSkimSecondBalanceOfNoCodeReverts_dynamic
                                  (value := safeValue0) (toWord := skimToWord I)
                                  (token0 := token0CleanE) (token1 := token1CleanE)
                                  (sel := uniswapSelWord I) rd5330 ho32 hoSize
                                  hout1Empty hout1Sign htoken1NoCode
                              exact rdRev.reEquivExecutionRevert hcode hdispatch
                                (uniswapDecode_skim_ok hsz36 hcanonTo) hbody
                            · have htoken1Code :
                                  uniswapExtCodeSizeWord σ1
                                    (UInt256.land token1CleanE solcAddrMask) ≠ ⟨0⟩ :=
                                htoken1NoCode
                              have hguard1 :=
                                skimToken1GuardAfterFirstTransfer_true
                                  (σ := σ1) (evm := evmS) (evm0 := evm0S) (evm1 := evm1S)
                                  (I := I) (balance0 := balance0) (token1 := token1CleanE)
                                  hPostTransferAccounts1 htarget1 htoken1Code
                              obtain ⟨cA2, σ2, z2, out2, A_in2, callGas2, k5273, C5273,
                                  hΘ2, rd5273, hout2Size⟩ :=
                                RD.uniswapSkimSecondBalanceOfStaticcallMade_dynamic
                                  (value := safeValue0) (toWord := skimToWord I)
                                  (token0 := token0CleanE) (token1 := token1CleanE)
                                  (sel := uniswapSelWord I) rd5330 ho32 hoSize
                                  hout1Empty hout1Sign hdepth htoken1Code
                              have henv1 : evm1S.executionEnv = I := by
                                simpa [evm1S, evmS, uniswapLockEnteredState,
                                  uniswapUnlockedState, initState, storageStore_executionEnv]
                                  using henv0
                              obtain ⟨evm2S, hcall1Raw, hPost2, hcreated2, hσ2, hgenesis2,
                                  hblocks2, henv2⟩ :=
                                uniswapSkimSecondBalanceTypedCall_source_dynamic
                                  (cA1 := cA1) (gh := gh) (bl := bl) (σ1 := σ1) (σ₀ := σ₀)
                                  (I := I) (evm1S := evm1S)
                                  (cA2 := cA2) (σ2 := σ2) (z2 := z2) (out2 := out2)
                                  (A_in2 := A_in2) (callGas2 := callGas2)
                                  (o := o) (out1 := out1) (toWord := skimToWord I)
                                  (value := safeValue0) (token1 := token1CleanE)
                                  hPostTransferAccounts1
                                  (by simp [evm1S])
                                  (by simp [evm1S, hσ0])
                                  (by simp [evm1S, hgenesis0])
                                  (by simp [evm1S, hblocks0])
                                  henv1 hdepth ho32 hoSize hout1Empty hout1Sign hΘ2
                              have htarget1E :
                                  AccountAddress.ofUInt256
                                      (UInt256.land token1CleanE solcAddrMask) =
                                    EVM.address
                                      (uniswapAddressAtSlot
                                        (uniswapLockEnteredState evmS) ⟨7⟩) := by
                                change
                                  AccountAddress.ofUInt256
                                      (UInt256.land token1CleanE solcAddrMask) =
                                    EVM.address
                                      (uniswapAddressAtSlot
                                        (uniswapLockEnteredState evmS) ⟨7⟩)
                                rw [htarget1]
                                exact
                                  (uniswapAddress_self
                                    (uniswapAddressAtSlot
                                      (uniswapLockEnteredState evmS) ⟨7⟩)).symm
                              have hcall1 : typedCallViaEVM config evm1S
                                  (EVM.address
                                    (uniswapAddressAtSlot
                                      (uniswapLockEnteredState evmS) ⟨7⟩))
                                  "balanceOf" 0 [.address evm1S.executionEnv.codeOwner]
                                  (z2, evm2S, out2) false := by
                                simpa [htarget1E] using hcall1Raw
                              by_cases hz2False : z2 = false
                              · have hcall1False : typedCallViaEVM config evm1S
                                    (EVM.address
                                      (uniswapAddressAtSlot
                                        (uniswapLockEnteredState evmS) ⟨7⟩))
                                    "balanceOf" 0 [.address evm1S.executionEnv.codeOwner]
                                    (false, evm2S, out2) false := by
                                  simpa [hz2False] using hcall1
                                have hbody :
                                    ExecTransitionBody config contract evmS (skimStore I)
                                      skimTransition.body .reverted := by
                                  exact uniswapSkimBodyReverts_secondCallFailure
                                    evmS evm0S evm1S evm2S I
                                    (by simp only [evmS, initState]; exact hwv)
                                    hunlockedSolm hguard0 hcall0 hdec0 henoughSource hsafe0
                                    hguard1 hcall1False
                                have hstatus :
                                    (if z2 then (⟨1⟩ : UInt256) else ⟨0⟩) = ⟨0⟩ := by
                                  simp [hz2False]
                                have rdRev :=
                                  RD.uniswapSkimSecondBalanceCallFailureReverts_dynamic
                                    rd5273 hstatus hout2Size
                                    (by simp only [List.length_cons, List.length_nil]; omega)
                                exact rdRev.reEquivExecutionRevert hcode hdispatch
                                  (uniswapDecode_skim_ok hsz36 hcanonTo) hbody
                              · have hz2True : z2 = true := Bool.eq_true_of_not_eq_false hz2False
                                have hcall1True : typedCallViaEVM config evm1S
                                    (EVM.address
                                      (uniswapAddressAtSlot
                                        (uniswapLockEnteredState evmS) ⟨7⟩))
                                    "balanceOf" 0 [.address evm1S.executionEnv.codeOwner]
                                    (true, evm2S, out2) false := by
                                  simpa [hz2True] using hcall1
                                have hstatus :
                                    (if z2 then (⟨1⟩ : UInt256) else ⟨0⟩) ≠ ⟨0⟩ := by
                                  rw [hz2True]
                                  decide
                                obtain ⟨k5291, C5291, rd5291⟩ :=
                                  RD.uniswapSkimSecondBalanceCallSuccessToDecode_dynamic
                                    rd5273 hstatus
                                    (by simp only [List.length_cons, List.length_nil]; omega)
                                by_cases hshort2 : out2.size < 32
                                · have hdec1 : config.externalABI.decode? "balanceOf" out2 = none := by
                                    change uniswapExternalABI.decode? "balanceOf" out2 = none
                                    simpa [uniswapExternalABI, uint256, uint256Int, abiUInt256] using
                                      (decodeReturnValueWithMode_legacy_uint256_none_short
                                        (returndata := out2) hshort2)
                                  have hbody :
                                      ExecTransitionBody config contract evmS (skimStore I)
                                        skimTransition.body .reverted := by
                                    exact uniswapSkimBodyReverts_secondCallDecode
                                      evmS evm0S evm1S evm2S I
                                      (by simp only [evmS, initState]; exact hwv)
                                      hunlockedSolm hguard0 hcall0 hdec0 henoughSource hsafe0
                                      hguard1 hcall1True hdec1
                                  have rdRev :=
                                    RD.uniswapSkimSecondBalanceReturnWordDecodeShortReverts_dynamic
                                      rd5291 ho32 hoSize hout1Empty hout1Sign hshort2 hout2Size
                                      (by simp only [List.length_cons, List.length_nil]; omega)
                                  exact rdRev.reEquivExecutionRevert hcode hdispatch
                                    (uniswapDecode_skim_ok hsz36 hcanonTo) hbody
                                · have ho32_2 : 32 ≤ out2.size := not_lt.mp hshort2
                                  let balance1 :=
                                    UInt256.ofNat (fromByteArrayBigEndian (out2.extract 0 32))
                                  have hdec1 :
                                      config.externalABI.decode? "balanceOf" out2 =
                                        some (skimBalanceValue balance1) := by
                                    simpa [balance1] using
                                      uniswapSkimBalanceOfDecode_ok (returndata := out2) ho32_2
                                  let reserve1E :=
                                    UInt256.land reserve112Mask
                                      (UInt256.div (uniswapSlotWord ⟨8⟩ σ1 I) reserve112Shift)
                                  have hsourceReserve1 : uniswapReserve1Word evm2S = reserve1E := by
                                    have h :=
                                      uniswapSkimSecondBalanceStaticReserve1
                                        hPostTransferAccounts1 henv1 hcall1True
                                    simpa [reserve1E, u256_land_comm] using h
                                  obtain ⟨k5314, C5314, rd5314⟩ :=
                                    RD.uniswapSkimSecondBalanceReturnWordDecodeOk_dynamic
                                      rd5291 ho32 hoSize hout1Empty hout1Sign ho32_2 hout2Size
                                      (by simp only [List.length_cons, List.length_nil]; omega)
                                  have hawBalance :=
                                    skimSecondBalanceDynamicStaticcallWords_mload64_ptr_same
                                      out1 hout1Sign
                                  have rd5314' : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
                                      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                                      ⟨5314⟩
                                      (balance1 :: reserve1E :: ⟨5325⟩ :: skimToWord I ::
                                        token1CleanE :: ⟨5433⟩ ::
                                        token1CleanE :: token0CleanE :: skimToWord I ::
                                        ⟨570⟩ :: uniswapSelWord I :: [])
                                      (skimSecondBalanceDynamicStaticcallMem
                                        (UInt256.ofNat I.codeOwner.val) o (skimToWord I)
                                        safeValue0 out1 out2)
                                      (skimSecondBalanceDynamicStaticcallWords out1)
                                      out2 (cA2, σ2) k5314 C5314 := by
                                    simpa [balance1, reserve1E, u256_land_comm, hawBalance] using
                                      rd5314
                                  by_cases hlt1 : balance1.toNat < reserve1E.toNat
                                  · obtain ⟨k6879, C6879, rd6879⟩ :=
                                      RD.uniswapSkimFirstExcessToSub rd5314'
                                        (by simp only [List.length_cons, List.length_nil]; omega)
                                    have rd6879' := by
                                      simpa using rd6879
                                    have rdRev :=
                                      RD.uniswapSafeMathSubUnderflow_dynamic rd6879'
                                        (by simpa [balance1, reserve1E, u256_land_comm] using hlt1)
                                        (by simp only [List.length_cons, List.length_nil]; omega)
                                    have hltSource :
                                        balance1.toNat < (uniswapReserve1Word evm2S).toNat := by
                                      rw [hsourceReserve1]
                                      exact hlt1
                                    have hbody :
                                        ExecTransitionBody config contract evmS (skimStore I)
                                          skimTransition.body .reverted := by
                                      exact uniswapSkimBodyReverts_secondExcessUnderflow
                                        evmS evm0S evm1S evm2S I
                                        (by simp only [evmS, initState]; exact hwv)
                                        hunlockedSolm hguard0 hcall0 hdec0 henoughSource hsafe0
                                        hguard1 hcall1True hdec1 hltSource
                                    exact rdRev.reEquivExecutionRevert hcode hdispatch
                                      (uniswapDecode_skim_ok hsz36 hcanonTo) hbody
                                  · have hle1 : reserve1E.toNat ≤ balance1.toNat := not_lt.mp hlt1
                                    obtain ⟨k6879, C6879, rd6879⟩ :=
                                      RD.uniswapSkimFirstExcessToSub rd5314'
                                        (by simp only [List.length_cons, List.length_nil]; omega)
                                    have rd6879' : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
                                        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                                        ⟨6879⟩
                                        (reserve1E :: balance1 :: ⟨5325⟩ :: skimToWord I ::
                                          token1CleanE :: ⟨5433⟩ ::
                                          token1CleanE :: token0CleanE :: skimToWord I ::
                                          ⟨570⟩ :: uniswapSelWord I :: [])
                                        (skimSecondBalanceDynamicStaticcallMem
                                          (UInt256.ofNat I.codeOwner.val) o (skimToWord I)
                                          safeValue0 out1 out2)
                                        (skimSecondBalanceDynamicStaticcallWords out1)
                                        out2 (cA2, σ2) k6879 C6879 := by
                                      simpa using rd6879
                                    obtain ⟨k6370, C6370, rd6370⟩ :=
                                      RD.uniswapSkimExcessSuccessToSafeTransferEntry rd6879' hle1
                                        (by simp only [List.length_cons, List.length_nil]; omega)
                                    let safeValue1 := UInt256.sub balance1 reserve1E
                                    let safeData1 :=
                                      (skimSecondSafeTransferDynamicCallMem2
                                        (UInt256.ofNat I.codeOwner.val) o (skimToWord I)
                                        safeValue0 out1 out2 safeValue1).readWithPadding
                                        (skimSecondSafeTransferDynamicCallPtr out1).toNat 68
                                    have hdata1 :
                                        transferCalldata? (skimToAddress I)
                                            (skimExcess1Word evm2S balance1) =
                                          some safeData1 := by
                                      have hencoded :=
                                        skimSecondSafeTransferCalldata_canonical_dynamic
                                          (evm2S := evm2S) (I := I) (o := o) (out1 := out1)
                                          (out2 := out2) (balance1 := balance1)
                                          (reserve1 := reserve1E) (prevValue := safeValue0)
                                          hsourceReserve1 hle1 ho32 hoSize hout1Empty
                                          hout1Sign ho32_2 hout2Size
                                      simpa [safeData1, safeValue1] using hencoded
                                    have rd6370' : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
                                        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                                        ⟨6370⟩
                                        (safeValue1 :: skimToWord I :: token1CleanE :: ⟨5433⟩ ::
                                          token1CleanE :: token0CleanE :: skimToWord I ::
                                          ⟨570⟩ :: uniswapSelWord I :: [])
                                        (skimSecondBalanceDynamicStaticcallMem
                                          (UInt256.ofNat I.codeOwner.val) o (skimToWord I)
                                          safeValue0 out1 out2)
                                        (skimSecondBalanceDynamicStaticcallWords out1)
                                        out2 (cA2, σ2) k6370 C6370 := by
                                      simpa [safeValue1] using rd6370
                                    obtain ⟨cA3, σ3, z3, out3, A_in3, callGas3, _gasArg3,
                                        k6595b, C6595b, hΘsafe1, rd6595b, hout3Size⟩ :=
                                      RD.uniswapSkimSecondSafeTransferEntryToCallMade_dynamic_offset
                                        rd6370' ho32 hoSize hout1Empty hout1Sign ho32_2
                                        hout2Size hdepth
                                    let evm2E : EVM.State :=
                                      { evm2S with
                                        accountMap := σ2
                                        createdAccounts := cA2
                                        σ₀ := σ₀
                                        genesisBlockHeader := gh
                                        blocks := bl
                                        executionEnv := I }
                                    obtain ⟨g3Ret, A3E, hΘsafeEq1⟩ := hΘsafe1
                                    have hout3Small : out3.size < 2 ^ 138 := by
                                      have htheta :=
                                        Theta_returnData_size_lt_2pow138 I.blobVersionedHashes cA2
                                          ((initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I).genesisBlockHeader)
                                          ((initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I).blocks)
                                          σ2
                                          (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I).σ₀
                                          A_in3
                                          (AccountAddress.ofUInt256
                                            (UInt256.ofNat I.codeOwner.val))
                                          I.sender
                                          (AccountAddress.ofUInt256
                                            (UInt256.land token1CleanE solcAddrMask))
                                          (toExecute σ2
                                            (AccountAddress.ofUInt256
                                              (UInt256.land token1CleanE solcAddrMask)))
                                          callGas3 (UInt256.ofNat I.gasPrice) ⟨0⟩ ⟨0⟩
                                          ((skimSecondSafeTransferDynamicCallMem2
                                            (UInt256.ofNat I.codeOwner.val) o (skimToWord I)
                                            safeValue0 out1 out2 safeValue1).readWithPadding
                                            (skimSecondSafeTransferDynamicCallPtr out1).toNat 68)
                                          (I.depth + 1) I.header I.perm
                                          (by
                                            exact
                                              Ethereum.EVM.ByteArray.readWithPadding_size_lt_uint256
                                                _ _ _)
                                      rw [← hΘsafeEq1] at htheta
                                      simpa [safeValue1] using htheta
                                    have hcallE1 : callViaEVM evm2E
                                        (AccountAddress.ofUInt256
                                          (UInt256.land token1CleanE solcAddrMask))
                                        0 safeData1
                                        (z3,
                                          { evm2E with
                                            accountMap := σ3
                                            substate := A3E
                                            createdAccounts := cA3 },
                                          out3) := by
                                      refine callViaEVM.callMade (perm := true) (g' := g3Ret)
                                        wordOfInt_zero.symm ?_ rfl ?_ ?_
                                      · refine ⟨callGas3, A_in3, ?_⟩
                                        simpa [evm2E, safeData1, safeValue1, hperm,
                                          accountAddress_roundtrip] using hΘsafeEq1
                                      · show (⟨0⟩ : UInt256) ≤ _
                                        exact Fin.zero_le _
                                      · intro hdepthEq
                                        have hdepthLt : I.depth.val < 1024 := hdepth
                                        rw [show evm2E.executionEnv.depth = I.depth by simp [evm2E]]
                                          at hdepthEq
                                        rw [hdepthEq] at hdepthLt
                                        exact absurd hdepthLt (by decide)
                                    obtain ⟨σ3S, A3S, htransfer1Raw, hPostTransferAccounts2⟩ :=
                                      callViaEVM_accountMapEquiv (storage := config.storage)
                                        (evm_evm := evm2E) (evm_solm := evm2S)
                                        hcallE1 hPost2
                                        (by simp [evm2E, hσ2])
                                        (by simp [evm2E, hcreated2])
                                        (by simp [evm2E, hgenesis2])
                                        (by simp [evm2E, hblocks2])
                                        (by simp [evm2E])
                                        (by simp [evm2E, henv2, henv1])
                                    let evm3S : EVM.State :=
                                      { evm2S with
                                        accountMap := σ3S
                                        substate := A3S
                                        createdAccounts := cA3 }
                                    have htransfer1Raw' : callViaEVM evm2S
                                        (AccountAddress.ofUInt256
                                          (UInt256.land token1CleanE solcAddrMask))
                                        0 safeData1 (z3, evm3S, out3) := by
                                      simpa [evm3S] using htransfer1Raw
                                    have htransfer1Target :
                                        AccountAddress.ofUInt256
                                            (UInt256.land token1CleanE solcAddrMask) =
                                          EVM.address
                                            (uniswapAddressAtSlot
                                              (uniswapLockEnteredState evmS) ⟨7⟩) := by
                                      rw [htarget1]
                                      exact (uniswapAddress_self
                                        (uniswapAddressAtSlot
                                          (uniswapLockEnteredState evmS) ⟨7⟩)).symm
                                    have htransfer1 : callViaEVM evm2S
                                        (EVM.address
                                          (uniswapAddressAtSlot
                                            (uniswapLockEnteredState evmS) ⟨7⟩))
                                        0 safeData1 (z3, evm3S, out3) := by
                                      simpa [htransfer1Target] using htransfer1Raw'
                                    have hPostTransferAccounts3 :
                                        accountMapEquiv σ3 evm3S.accountMap := by
                                      simpa [evm3S] using hPostTransferAccounts2
                                    have henv3 : evm3S.executionEnv = I := by
                                      simpa [evm3S] using henv2.trans henv1
                                    have henough1Source :
                                        (uniswapReserve1Word evm2S).toNat ≤ balance1.toNat := by
                                      rw [hsourceReserve1]
                                      exact hle1
                                    have hfinish :
                                        ∀ {mem outRet : ByteArray} {aw : UInt256} {kR CR : ℕ},
                                          RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
                                            (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                                            ⟨5433⟩
                                            (token1CleanE :: token0CleanE :: skimToWord I ::
                                              ⟨570⟩ :: uniswapSelWord I :: [])
                                            mem aw outRet (cA3, σ3) kR CR →
                                          ExecStmt config
                                            { contract := contract,
                                              locals :=
                                                skimSecondExcessStore evmS evm0S evm2S I
                                                  balance0 balance1 } evm2S
                                            (.internalCall "_safeTransfer"
                                              [.var "_token1", .var "to", .var "excess1"] "ok1")
                                            (.ok
                                              { contract := contract,
                                                locals :=
                                                  skimSecondSafeTransferStore evmS evm0S evm2S I
                                                    balance0 balance1 }
                                              evm3S) →
                                          runtimeEquivalenceFor config contract cA gh bl σ_evm
                                            σ_solm σ₀ g A I := by
                                      intro mem outRet aw kR CR rd5433 hsafe1
                                      have rdRet :=
                                        RD.uniswapSkimAfterSecondSafeTransferToReturn rd5433 hperm
                                      have hbody :
                                          ExecTransitionBody config contract evmS (skimStore I)
                                            skimTransition.body
                                            (.returned
                                              { contract := contract,
                                                locals :=
                                                  skimSecondSafeTransferStore evmS evm0S evm2S I
                                                    balance0 balance1 }
                                              (uniswapLockExitedState evm3S) none) := by
                                        exact uniswapSkimBodyReturns
                                          evmS evm0S evm1S evm2S evm3S I
                                          (by simp only [evmS, initState]; exact hwv)
                                          hunlockedSolm hguard0 hcall0 hdec0 henoughSource hsafe0
                                          hguard1 hcall1True hdec1 henough1Source hsafe1
                                      have hCreatedRet :
                                          cA3 = (uniswapLockExitedState evm3S).createdAccounts := by
                                        simp [uniswapLockExitedState, uniswapUnlockedState, evm3S,
                                          storageStore_createdAccounts]
                                      have hAccountsRet :
                                          accountMapEquiv
                                            (sstoreAccountMap I.codeOwner σ3 ⟨12⟩ ⟨1⟩)
                                            (uniswapLockExitedState evm3S).accountMap := by
                                        have hs :=
                                          accountMapEquiv_sstoreAccountMap I.codeOwner ⟨12⟩ ⟨1⟩
                                            hPostTransferAccounts3
                                        simpa [uniswapLockExitedState, uniswapUnlockedState,
                                          storageStore_accountMap, henv3] using hs
                                      exact rdRet.reEquivExecutionGenAccountMapEquiv hcode hdispatch
                                        (uniswapDecode_skim_ok hsz36 hcanonTo) hbody hCreatedRet
                                        hAccountsRet (returnEquiv.void rfl rfl rfl)
                                    by_cases hz3False : z3 = false
                                    · have htransfer1False : callViaEVM evm2S
                                          (EVM.address
                                            (uniswapAddressAtSlot
                                              (uniswapLockEnteredState evmS) ⟨7⟩))
                                          0 safeData1 (false, evm3S, out3) := by
                                        simpa [hz3False] using htransfer1
                                      have hbody :
                                          ExecTransitionBody config contract evmS (skimStore I)
                                            skimTransition.body .reverted := by
                                        exact uniswapSkimBodyReverts_secondSafeTransferFailure
                                          evmS evm0S evm1S evm2S evm3S I
                                          (by simp only [evmS, initState]; exact hwv)
                                          hunlockedSolm hguard0 hcall0 hdec0 henoughSource hsafe0
                                          hguard1 hcall1True hdec1 henough1Source hdata1
                                          htransfer1False
                                      have rd6595False : RD uniswapV2PairBytecode I
                                          (Sat256.ofUInt256 g)
                                          (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                                          ⟨6595⟩
                                          (⟨0⟩ :: skimSecondSafeTransferDynamicRetEnd out1 ::
                                            UInt256.land token1CleanE solcAddrMask :: ⟨96⟩ :: ⟨0⟩ ::
                                            safeValue1 :: skimToWord I :: token1CleanE :: ⟨5433⟩ ::
                                            token1CleanE :: token0CleanE :: skimToWord I ::
                                            ⟨570⟩ :: uniswapSelWord I :: [])
                                          (skimSecondSafeTransferDynamicCallMem2
                                            (UInt256.ofNat I.codeOwner.val) o (skimToWord I)
                                            safeValue0 out1 out2 safeValue1)
                                          (skimSecondSafeTransferDynamicWordsCall2 out1) out3
                                          (cA3, σ3) k6595b C6595b := by
                                        simpa [hz3False, safeValue1] using rd6595b
                                      by_cases hout3Empty : out3.size = 0
                                      · have rdRev :=
                                          RD.uniswapSkimSecondSafeTransferEmptyFailureReverts_dynamic_offset
                                            rd6595False hout3Empty
                                        exact rdRev.reEquivExecutionRevert hcode hdispatch
                                          (uniswapDecode_skim_ok hsz36 hcanonTo) hbody
                                      · by_cases hout3Sign : out3.size < 2 ^ 255
                                        · have rdRev :=
                                            RD.uniswapSkimSecondSafeTransferNonemptyFailureReverts_dynamic_offset
                                              rd6595False hout3Empty hout3Sign ho32 hoSize
                                              hout1Empty hout1Sign ho32_2 hout2Size
                                          exact rdRev.reEquivExecutionRevert hcode hdispatch
                                            (uniswapDecode_skim_ok hsz36 hcanonTo) hbody
                                        · have : out3.size < 2 ^ 255 := by
                                            exact lt_trans hout3Small (by norm_num)
                                          exact False.elim (hout3Sign this)
                                    · have hz3True : z3 = true := Bool.eq_true_of_not_eq_false hz3False
                                      have htransfer1True : callViaEVM evm2S
                                          (EVM.address
                                            (uniswapAddressAtSlot
                                              (uniswapLockEnteredState evmS) ⟨7⟩))
                                          0 safeData1 (true, evm3S, out3) := by
                                        simpa [hz3True] using htransfer1
                                      have rd6595True : RD uniswapV2PairBytecode I
                                          (Sat256.ofUInt256 g)
                                          (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                                          ⟨6595⟩
                                          (⟨1⟩ :: skimSecondSafeTransferDynamicRetEnd out1 ::
                                            UInt256.land token1CleanE solcAddrMask :: ⟨96⟩ :: ⟨0⟩ ::
                                            safeValue1 :: skimToWord I :: token1CleanE :: ⟨5433⟩ ::
                                            token1CleanE :: token0CleanE :: skimToWord I ::
                                            ⟨570⟩ :: uniswapSelWord I :: [])
                                          (skimSecondSafeTransferDynamicCallMem2
                                            (UInt256.ofNat I.codeOwner.val) o (skimToWord I)
                                            safeValue0 out1 out2 safeValue1)
                                          (skimSecondSafeTransferDynamicWordsCall2 out1) out3
                                          (cA3, σ3) k6595b C6595b := by
                                        simpa [hz3True, safeValue1] using rd6595b
                                      by_cases hout3Empty : out3.size = 0
                                      · have hsafe1 :
                                            ExecStmt config
                                              { contract := contract,
                                                locals :=
                                                  skimSecondExcessStore evmS evm0S evm2S I
                                                    balance0 balance1 } evm2S
                                              (.internalCall "_safeTransfer"
                                                [.var "_token1", .var "to", .var "excess1"] "ok1")
                                              (.ok
                                                { contract := contract,
                                                  locals :=
                                                    skimSecondSafeTransferStore evmS evm0S evm2S I
                                                      balance0 balance1 }
                                                evm3S) := by
                                          have hs := safeTransferInternalCallReturns_empty
                                            (caller :=
                                              { contract := contract,
                                                locals :=
                                                  skimSecondExcessStore evmS evm0S evm2S I
                                                    balance0 balance1 })
                                            (evm := evm2S) (evm' := evm3S)
                                            (tokenExpr := .var "_token1") (toExpr := .var "to")
                                            (valueExpr := .var "excess1") (retVar := "ok1")
                                            (token :=
                                              uniswapAddressAtSlot
                                                (uniswapLockEnteredState evmS) ⟨7⟩)
                                            (recipient := skimToAddress I)
                                            (value := skimExcess1Word evm2S balance1)
                                            (calldata := safeData1) (out := out3)
                                            rfl
                                            (evalExprs_skim_safeTransfer1_args
                                              evmS evm0S evm2S I balance0 balance1)
                                            hdata1 htransfer1True hout3Empty
                                          simpa [resumeAfterInternalCall, skimSecondSafeTransferStore]
                                            using hs
                                        obtain ⟨k5433, C5433, rd5433⟩ :=
                                          RD.uniswapSkimSecondSafeTransferEmptyReturnTo5433_dynamic_offset
                                            rd6595True hout3Empty ho32 hoSize hout1Empty
                                            hout1Sign ho32_2 hout2Size
                                        exact hfinish rd5433 hsafe1
                                      · by_cases hout3Sign : out3.size < 2 ^ 255
                                        · by_cases hshort3 : out3.size < 32
                                          · have hdecSafe1 :
                                                ABI.decodeReturnValueWithMode?
                                                    config.abiDecodeMode boolTy out3 =
                                                  none := by
                                              change
                                                ABI.decodeReturnValueWithMode?
                                                    DecodeMode.legacySolc05 boolTy out3 =
                                                  none
                                              exact decodeReturnValueWithMode_legacy_bool_none_short
                                                (returndata := out3) hshort3
                                            have hbody :
                                                ExecTransitionBody config contract evmS (skimStore I)
                                                  skimTransition.body .reverted := by
                                              exact uniswapSkimBodyReverts_secondSafeTransferDecode
                                                evmS evm0S evm1S evm2S evm3S I
                                                (by simp only [evmS, initState]; exact hwv)
                                                hunlockedSolm hguard0 hcall0 hdec0 henoughSource hsafe0
                                                hguard1 hcall1True hdec1 henough1Source hdata1
                                                htransfer1True hout3Empty hdecSafe1
                                            have rdRev :=
                                              RD.uniswapSkimSecondSafeTransferNonemptyShortReverts_dynamic_offset
                                                rd6595True hout3Empty hshort3 hout3Sign hout3Small
                                                ho32 hoSize hout1Empty hout1Sign hout1Small
                                                ho32_2 hout2Size
                                            exact rdRev.reEquivExecutionRevert hcode hdispatch
                                              (uniswapDecode_skim_ok hsz36 hcanonTo) hbody
                                          · have hout332 : 32 ≤ out3.size := not_lt.mp hshort3
                                            let safeWord1 :=
                                              UInt256.ofNat
                                                (fromByteArrayBigEndian (out3.extract 0 32))
                                            by_cases hword1 : safeWord1 = ⟨0⟩
                                            · have hdecSafe1 :
                                                  ABI.decodeReturnValueWithMode?
                                                      config.abiDecodeMode boolTy out3 =
                                                    some (.bool false) := by
                                                change
                                                  ABI.decodeReturnValueWithMode?
                                                      DecodeMode.legacySolc05 boolTy out3 =
                                                    some (.bool false)
                                                exact decodeReturnValueWithMode_legacy_bool_false
                                                  (returndata := out3) hout332 hout3Sign hword1
                                              have hbody :
                                                  ExecTransitionBody config contract evmS (skimStore I)
                                                    skimTransition.body .reverted := by
                                                exact uniswapSkimBodyReverts_secondSafeTransferDecodeFalse
                                                  evmS evm0S evm1S evm2S evm3S I
                                                  (by simp only [evmS, initState]; exact hwv)
                                                  hunlockedSolm hguard0 hcall0 hdec0 henoughSource hsafe0
                                                  hguard1 hcall1True hdec1 henough1Source hdata1
                                                  htransfer1True hout3Empty hdecSafe1
                                              have rdRev :=
                                                RD.uniswapSkimSecondSafeTransferNonemptyFalseReverts_dynamic_offset
                                                  rd6595True hout3Empty hout332 hout3Sign hout3Small
                                                  hword1 ho32 hoSize hout1Empty hout1Sign
                                                  hout1Small ho32_2 hout2Size
                                              exact rdRev.reEquivExecutionRevert hcode hdispatch
                                                (uniswapDecode_skim_ok hsz36 hcanonTo) hbody
                                            · have hdecSafe1 :
                                                  ABI.decodeReturnValueWithMode?
                                                      config.abiDecodeMode boolTy out3 =
                                                    some (.bool true) := by
                                                change
                                                  ABI.decodeReturnValueWithMode?
                                                      DecodeMode.legacySolc05 boolTy out3 =
                                                    some (.bool true)
                                                exact decodeReturnValueWithMode_legacy_bool_true
                                                  (returndata := out3) hout332 hout3Sign hword1
                                              have hsafe1 :
                                                  ExecStmt config
                                                    { contract := contract,
                                                      locals :=
                                                        skimSecondExcessStore evmS evm0S evm2S I
                                                          balance0 balance1 } evm2S
                                                    (.internalCall "_safeTransfer"
                                                      [.var "_token1", .var "to", .var "excess1"]
                                                      "ok1")
                                                    (.ok
                                                      { contract := contract,
                                                        locals :=
                                                          skimSecondSafeTransferStore evmS evm0S evm2S I
                                                            balance0 balance1 }
                                                      evm3S) := by
                                                have hs := safeTransferInternalCallReturns_decodeTrue
                                                  (caller :=
                                                    { contract := contract,
                                                      locals :=
                                                        skimSecondExcessStore evmS evm0S evm2S I
                                                          balance0 balance1 })
                                                  (evm := evm2S) (evm' := evm3S)
                                                  (tokenExpr := .var "_token1") (toExpr := .var "to")
                                                  (valueExpr := .var "excess1") (retVar := "ok1")
                                                  (token :=
                                                    uniswapAddressAtSlot
                                                      (uniswapLockEnteredState evmS) ⟨7⟩)
                                                  (recipient := skimToAddress I)
                                                  (value := skimExcess1Word evm2S balance1)
                                                  (calldata := safeData1) (out := out3)
                                                  rfl
                                                  (evalExprs_skim_safeTransfer1_args
                                                    evmS evm0S evm2S I balance0 balance1)
                                                  hdata1 htransfer1True hout3Empty hdecSafe1
                                                simpa [resumeAfterInternalCall,
                                                  skimSecondSafeTransferStore] using hs
                                              obtain ⟨k5433, C5433, rd5433⟩ :=
                                                RD.uniswapSkimSecondSafeTransferNonemptyTrueToRet_dynamic_offset
                                                  rd6595True hout3Empty hout332 hout3Sign
                                                  hout3Small hword1 ho32 hoSize hout1Empty
                                                  hout1Sign hout1Small ho32_2 hout2Size
                                                  (by jump_dest)
                                              exact hfinish rd5433 hsafe1
                                        · have : out3.size < 2 ^ 255 := by
                                            exact lt_trans hout3Small (by norm_num)
                                          exact False.elim (hout3Sign this)
                      · have hhi : 2 ^ 255 ≤ out1.size := le_of_not_gt hout1Sign
                        have hdecSafe0 :
                            ABI.decodeReturnValueWithMode? config.abiDecodeMode boolTy out1 =
                              none := by
                          change
                            ABI.decodeReturnValueWithMode? DecodeMode.legacySolc05 boolTy out1 =
                              none
                          exact decodeReturnValueWithMode_legacy_bool_none_huge
                            (returndata := out1) hhi
                        have hbody :
                            ExecTransitionBody config contract evmS (skimStore I)
                              skimTransition.body .reverted := by
                          exact uniswapSkimBodyReverts_firstSafeTransferDecode
                            evmS evm0S evm1S I
                            (by simp only [evmS, initState]; exact hwv)
                            hunlockedSolm hguard0 hcall0 hdec0 henoughSource hdata0
                            htransferTrue hout1Empty hdecSafe0
                        have rdRev :=
                          RD.uniswapSkimSafeTransferNonemptyHugeReverts
                            rd6595True hout1Empty hhi hout1Size ho32 hoSize
                        exact rdRev.reEquivExecutionRevert hcode hdispatch
                          (uniswapDecode_skim_ok hsz36 hcanonTo) hbody
          · rw [not_lt] at hdepth
            have hdepth1024 : I.depth = 1024 := Fin.ext (by have := I.depth.isLt; omega)
            exact uniswapSkimBodyCoreRevert_firstCallDepth hcode hsize hperm hwv hsel hsz36
              hcanonTo hdepth1024 hunlocked htoken0NoCode hdispatch
              (uniswapDecode_skim_ok hsz36 hcanonTo) hAccounts
    · by_cases hlocked :
        (σ_evm.find? I.codeOwner |>.option ⟨0⟩
          (fun acc => acc.storage.findD ⟨12⟩ ⟨0⟩)) ≠ ⟨1⟩
      · exact uniswapSkimBodyRevert_locked_masked hcode hsize hwv hsel hsz36 hcanonTo
          hlocked hdispatch hAccounts
      · have hunlocked :
          (σ_evm.find? I.codeOwner |>.option ⟨0⟩
            (fun acc => acc.storage.findD ⟨12⟩ ⟨0⟩)) = ⟨1⟩ := by
          exact not_not.mp hlocked
        by_cases htoken0NoCode :
          uniswapExtCodeSizeWord (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩)
            (UInt256.land solcAddrMask
              (uniswapSlotWord ⟨6⟩
                (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I)) =
            ⟨0⟩
        · exact uniswapSkimBodyRevert_firstNoCode_masked hcode hsize hperm hwv hsel hsz36
            hcanonTo hunlocked htoken0NoCode hdispatch hAccounts
        · by_cases hdepth : I.depth.val < 1024
          · obtain ⟨cA', σ', z, o, A_in, callGas, hΘ, hrev, hrevShort, hrevLong,
                hoSize⟩ :=
                uniswapSkimRuntimeFirstBalanceOfStaticcallFailureGuard_masked
                  (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
                  (A := A) (I := I) (g := g)
                hcode hsize hwv hsel hsz36 hperm hdepth hunlocked htoken0NoCode
            obtain ⟨evm0S, hcallAll, hPostAccounts0, hcreated0, hσ0, hgenesis0,
                hblocks0, henv0⟩ :=
              uniswapSkimFirstBalanceTypedCall_source
                (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
                (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                (cA' := cA') (σ' := σ') (z := z) (o := o)
                (A_in := A_in) (callGas := callGas) hAccounts hdepth hΘ
            let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
            have hunlockedSolm :
                Solm.EVM.storageLoad evmS evmS.executionEnv.codeOwner ⟨12⟩ = ⟨1⟩ := by
              have hword := accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨12⟩ ⟨0⟩
              simpa [evmS, initState, Solm.EVM.storageLoad, State.lookupAccount,
                Account.lookupStorage] using (hword ▸ hunlocked)
            have hguard0 : skimToken0GuardTrue evmS I :=
              skimToken0GuardTrue_initState_of_code hAccounts htoken0NoCode
            by_cases hz : z = false
            · exact (hrev hz).reEquivExecutionRevert hcode hdispatch
                (uniswapDecode_skim_ok_noncanon hsz36 hcanonTo) (by
                  have hcall0 : typedCallViaEVM config (uniswapLockEnteredState evmS)
                      (EVM.address (uniswapAddressAtSlot (uniswapLockEnteredState evmS) ⟨6⟩))
                      "balanceOf" 0
                      [.address (uniswapLockEnteredState evmS).executionEnv.codeOwner]
                      (false, evm0S, o) false := by
                    simpa [evmS, hz] using hcallAll
                  exact uniswapSkimBodyReverts_firstCallFailure evmS evm0S I
                    (by simp only [evmS, initState]; exact hwv)
                    hunlockedSolm hguard0 hcall0)
            · by_cases hshort : o.size < 32
              · have hzTrue : z = true := Bool.eq_true_of_not_eq_false hz
                have hcall0 : typedCallViaEVM config (uniswapLockEnteredState evmS)
                    (EVM.address (uniswapAddressAtSlot (uniswapLockEnteredState evmS) ⟨6⟩))
                    "balanceOf" 0 [.address (uniswapLockEnteredState evmS).executionEnv.codeOwner]
                    (true, evm0S, o) false := by
                  simpa [evmS, hzTrue] using hcallAll
                have hdec0 : config.externalABI.decode? "balanceOf" o = none := by
                  change uniswapExternalABI.decode? "balanceOf" o = none
                  simpa [uniswapExternalABI, uint256, uint256Int, abiUInt256] using
                    (decodeReturnValueWithMode_legacy_uint256_none_short (returndata := o)
                      hshort)
                have hbody :
                    ExecTransitionBody config contract evmS (skimStore I) skimTransition.body
                      .reverted := by
                  exact uniswapSkimBodyReverts_firstCallDecode evmS evm0S I
                    (by simp only [evmS, initState]; exact hwv)
                    hunlockedSolm hguard0 hcall0 hdec0
                exact (hrevShort hzTrue hshort).reEquivExecutionRevert hcode hdispatch
                  (uniswapDecode_skim_ok_noncanon hsz36 hcanonTo) hbody
              · have hzTrue : z = true := Bool.eq_true_of_not_eq_false hz
                have ho32 : 32 ≤ o.size := not_lt.mp hshort
                let balance0 := UInt256.ofNat (fromByteArrayBigEndian (o.extract 0 32))
                have hcall0 : typedCallViaEVM config (uniswapLockEnteredState evmS)
                    (EVM.address (uniswapAddressAtSlot (uniswapLockEnteredState evmS) ⟨6⟩))
                    "balanceOf" 0
                    [.address (uniswapLockEnteredState evmS).executionEnv.codeOwner]
                    (true, evm0S, o) false := by
                  simpa [evmS, hzTrue] using hcallAll
                have hdec0 :
                    config.externalABI.decode? "balanceOf" o =
                      some (skimBalanceValue balance0) := by
                  simpa [balance0] using uniswapSkimBalanceOfDecode_ok (returndata := o) ho32
                let reserve0E := UInt256.land
                  (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨112⟩) ⟨1⟩)
                  (uniswapSlotWord ⟨8⟩
                    (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I)
                have hsourceReserve : uniswapReserve0Word evm0S = reserve0E := by
                  have h := uniswapSkimFirstBalanceStaticReserve0 hAccounts hcall0
                  simpa [reserve0E, reserve112Mask, u256_land_comm] using h
                by_cases hlt0 : balance0.toNat < reserve0E.toNat
                · obtain ⟨k5314, C5314, rd5314⟩ := hrevLong hzTrue ho32
                  have rd5314' : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
                      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨5314⟩
                      (balance0 :: reserve0E :: ⟨5325⟩ :: skimToMaskedWord I ::
                        UInt256.land solcAddrMask
                          (uniswapSlotWord ⟨6⟩
                            (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I) ::
                        ⟨5330⟩ ::
                        UInt256.land
                          (uniswapSlotWord ⟨7⟩
                            (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I)
                          solcAddrMask ::
                        UInt256.land solcAddrMask
                          (uniswapSlotWord ⟨6⟩
                            (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I) ::
                        skimToMaskedWord I :: ⟨570⟩ :: uniswapSelWord I :: [])
                      (balanceOfThisStaticcallMem (UInt256.ofNat I.codeOwner.val) o)
                      balanceOfThisStaticcallActiveWords o (cA', σ') k5314 C5314 := by
                    simpa [balance0, reserve0E, reserve112Mask, u256_land_comm] using rd5314
                  obtain ⟨k6879, C6879, rd6879⟩ :=
                    RD.uniswapSkimFirstExcessToSub rd5314'
                      (by simp only [List.length_cons, List.length_nil]; omega)
                  have rd6879' : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
                      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨6879⟩
                      (reserve0E :: balance0 :: ⟨5325⟩ :: skimToMaskedWord I ::
                        UInt256.land solcAddrMask
                          (uniswapSlotWord ⟨6⟩
                            (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I) ::
                        ⟨5330⟩ ::
                        UInt256.land
                          (uniswapSlotWord ⟨7⟩
                            (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I)
                          solcAddrMask ::
                        UInt256.land solcAddrMask
                          (uniswapSlotWord ⟨6⟩
                            (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I) ::
                        skimToMaskedWord I :: ⟨570⟩ :: uniswapSelWord I :: [])
                      (balanceOfThisStaticcallMem (UInt256.ofNat I.codeOwner.val) o)
                      balanceOfThisStaticcallActiveWords o (cA', σ') k6879 C6879 := by
                    simpa [balanceOfThisStaticcallActiveWords] using rd6879
                  have hmem :
                      (balanceOfThisStaticcallMem (UInt256.ofNat I.codeOwner.val) o).size =
                        164 :=
                    balanceOfThisStaticcallMem_size_of_size_ge
                      (UInt256.ofNat I.codeOwner.val) o ho32 hoSize
                  have hread64 :
                      (balanceOfThisStaticcallMem (UInt256.ofNat I.codeOwner.val) o).readWithPadding
                          64 32 =
                        UInt256.toByteArray ⟨128⟩ :=
                    balanceOfThisStaticcallMem_read64_of_size_ge
                      (UInt256.ofNat I.codeOwner.val) o ho32 hoSize
                  have rdRev :=
                    RD.uniswapSafeMathSubUnderflow_aw6_size164 rd6879' hlt0 hmem hread64
                      (by simp only [List.length_cons, List.length_nil]; omega)
                  have hltSource : balance0.toNat < (uniswapReserve0Word evm0S).toNat := by
                    rw [hsourceReserve]
                    exact hlt0
                  have hbody :
                      ExecTransitionBody config contract evmS (skimStore I) skimTransition.body
                        .reverted := by
                    exact uniswapSkimBodyReverts_firstExcessUnderflow evmS evm0S I
                      (by simp only [evmS, initState]; exact hwv)
                      hunlockedSolm hguard0 hcall0 hdec0 hltSource
                  exact rdRev.reEquivExecutionRevert hcode hdispatch
                    (uniswapDecode_skim_ok_noncanon hsz36 hcanonTo) hbody
                · have hle0 : reserve0E.toNat ≤ balance0.toNat := not_lt.mp hlt0
                  obtain ⟨k5314, C5314, rd5314⟩ := hrevLong hzTrue ho32
                  have rd5314' : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
                      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨5314⟩
                      (balance0 :: reserve0E :: ⟨5325⟩ :: skimToMaskedWord I ::
                        UInt256.land solcAddrMask
                          (uniswapSlotWord ⟨6⟩
                            (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I) ::
                        ⟨5330⟩ ::
                        UInt256.land
                          (uniswapSlotWord ⟨7⟩
                            (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I)
                          solcAddrMask ::
                        UInt256.land solcAddrMask
                          (uniswapSlotWord ⟨6⟩
                            (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I) ::
                        skimToMaskedWord I :: ⟨570⟩ :: uniswapSelWord I :: [])
                      (balanceOfThisStaticcallMem (UInt256.ofNat I.codeOwner.val) o)
                      balanceOfThisStaticcallActiveWords o (cA', σ') k5314 C5314 := by
                    simpa [balance0, reserve0E, reserve112Mask, u256_land_comm] using rd5314
                  obtain ⟨k6879, C6879, rd6879⟩ :=
                    RD.uniswapSkimFirstExcessToSub rd5314'
                      (by simp only [List.length_cons, List.length_nil]; omega)
                  have rd6879' : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
                      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨6879⟩
                      (reserve0E :: balance0 :: ⟨5325⟩ :: skimToMaskedWord I ::
                        UInt256.land solcAddrMask
                          (uniswapSlotWord ⟨6⟩
                            (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I) ::
                        ⟨5330⟩ ::
                        UInt256.land
                          (uniswapSlotWord ⟨7⟩
                            (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I)
                          solcAddrMask ::
                        UInt256.land solcAddrMask
                          (uniswapSlotWord ⟨6⟩
                            (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I) ::
                        skimToMaskedWord I :: ⟨570⟩ :: uniswapSelWord I :: [])
                      (balanceOfThisStaticcallMem (UInt256.ofNat I.codeOwner.val) o)
                      balanceOfThisStaticcallActiveWords o (cA', σ') k6879 C6879 := by
                    simpa [balanceOfThisStaticcallActiveWords] using rd6879
                  obtain ⟨k6370, C6370, rd6370⟩ :=
                    RD.uniswapSkimFirstExcessSuccessToSafeTransferEntry rd6879' hle0
                  obtain ⟨cA1, σ1, z1, out1, A_in1, callGas1, _gasArg1,
                      k6595, C6595, hΘsafe0, rd6595, hout1Size⟩ :=
                    UniswapV2Pair.RD.uniswapSkimSafeTransferEntryToCallMade
                      rd6370 ho32 hoSize hdepth
                  let token0WordE :=
                    uniswapSlotWord ⟨6⟩ (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I
                  let token0CleanE := UInt256.land solcAddrMask token0WordE
                  let safeValue0 := UInt256.sub balance0 reserve0E
                  let safeData0 :=
                    (skimSafeTransferCallMem2 (UInt256.ofNat I.codeOwner.val) o
                      (skimToMaskedWord I) safeValue0).readWithPadding 292 68
                  have hdata0 :
                      transferCalldata? (skimToAddress I) (skimExcess0Word evm0S balance0) =
                        some safeData0 := by
                    have hencoded :=
                      skimFirstSafeTransferCalldata_masked (evm0S := evm0S) (I := I)
                        (balance0 := balance0) (reserve0 := reserve0E) hsourceReserve hle0
                    have hread :=
                      skimSafeTransferCallMem2_read292_68
                        (UInt256.ofNat I.codeOwner.val) (o := o) (skimToMaskedWord I) safeValue0
                        ho32 hoSize
                    simpa [safeData0, safeValue0, hread] using hencoded
                  let evm0E : EVM.State :=
                    { evm0S with
                      accountMap := σ'
                      createdAccounts := cA'
                      σ₀ := σ₀
                      genesisBlockHeader := gh
                      blocks := bl
                      executionEnv := I }
                  obtain ⟨g1Ret, A1E, hΘsafeEq⟩ := hΘsafe0
                  have hcallE : callViaEVM evm0E
                      (AccountAddress.ofUInt256 (UInt256.land token0CleanE solcAddrMask))
                      0 safeData0
                      (z1,
                        { evm0E with
                          accountMap := σ1
                          substate := A1E
                          createdAccounts := cA1 },
                        out1) := by
                    refine callViaEVM.callMade (perm := true) (g' := g1Ret)
                      wordOfInt_zero.symm ?_ rfl ?_ ?_
                    · refine ⟨callGas1, A_in1, ?_⟩
                      simpa [evm0E, token0CleanE, token0WordE, safeData0, safeValue0, hperm,
                        accountAddress_roundtrip] using hΘsafeEq
                    · show (⟨0⟩ : UInt256) ≤ _
                      exact Fin.zero_le _
                    · intro hdepthEq
                      have hdepthLt : I.depth.val < 1024 := hdepth
                      rw [show evm0E.executionEnv.depth = I.depth by simp [evm0E]] at hdepthEq
                      rw [hdepthEq] at hdepthLt
                      exact absurd hdepthLt (by decide)
                  obtain ⟨σ1S, A1S, htransfer0Raw, hPostTransferAccounts0⟩ :=
                    callViaEVM_accountMapEquiv (storage := config.storage)
                      (evm_evm := evm0E) (evm_solm := evm0S) hcallE hPostAccounts0
                      (by simp [evm0E, hσ0])
                      (by simp [evm0E, hcreated0])
                      (by simp [evm0E, hgenesis0])
                      (by simp [evm0E, hblocks0])
                      (by simp [evm0E])
                      (by
                        simp [evm0E, henv0, uniswapLockEnteredState,
                          uniswapUnlockedState, initState, storageStore_executionEnv])
                  let evm1S : EVM.State :=
                    { evm0S with
                      accountMap := σ1S
                      substate := A1S
                      createdAccounts := cA1 }
                  have htransfer0Raw' : callViaEVM evm0S
                      (AccountAddress.ofUInt256 (UInt256.land token0CleanE solcAddrMask))
                      0 safeData0 (z1, evm1S, out1) := by
                    simpa [evm1S] using htransfer0Raw
                  have htarget0 :
                      AccountAddress.ofUInt256 (UInt256.land token0CleanE solcAddrMask) =
                        EVM.address (uniswapAddressAtSlot (uniswapLockEnteredState evmS) ⟨6⟩) := by
                    let σLockE := sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩
                    let σLockS := sstoreAccountMap I.codeOwner σ_solm ⟨12⟩ ⟨0⟩
                    let token0WordS := uniswapSlotWord ⟨6⟩ σLockS I
                    have hLockAccounts : accountMapEquiv σLockE σLockS := by
                      exact accountMapEquiv_sstoreAccountMap I.codeOwner ⟨12⟩ ⟨0⟩ hAccounts
                    have hslot : token0WordE = token0WordS := by
                      simpa [σLockE, σLockS, token0WordE, token0WordS] using
                        accountMapEquiv_storage_findD hLockAccounts I.codeOwner ⟨6⟩ ⟨0⟩
                    have hcanonClean : token0CleanE.toNat < EVM.addressModulus := by
                      simpa [token0CleanE, token0WordE, u256_land_comm] using
                        solcAddrMask_result_canonical token0WordE
                    have hclean : UInt256.land token0CleanE solcAddrMask = token0CleanE :=
                      solcAddrMask_clean hcanonClean
                    have haddr :
                        AccountAddress.ofUInt256 token0CleanE =
                          uniswapAddressAtSlot (uniswapLockEnteredState evmS) ⟨6⟩ := by
                      simpa [token0CleanE, token0WordE, token0WordS, σLockS, evmS,
                        uniswapLockEnteredState, uniswapUnlockedState, initState,
                        storageStore_accountMap, storageStore_executionEnv, State.lookupAccount,
                        Account.lookupStorage, Solm.EVM.storageLoad, uniswapAddressAtSlot,
                        uniswapSlotWord, hslot, accountAddress_ofUInt256_eq_ofNat_toNat,
                        u256_land_comm]
                    rw [hclean, haddr]
                    exact (uniswapAddress_self (uniswapAddressAtSlot
                      (uniswapLockEnteredState evmS) ⟨6⟩)).symm
                  have htransfer0 : callViaEVM evm0S
                      (EVM.address (uniswapAddressAtSlot (uniswapLockEnteredState evmS) ⟨6⟩))
                      0 safeData0 (z1, evm1S, out1) := by
                    simpa [htarget0] using htransfer0Raw'
                  by_cases hz1False : z1 = false
                  · have htransferFalse : callViaEVM evm0S
                        (EVM.address
                          (uniswapAddressAtSlot (uniswapLockEnteredState evmS) ⟨6⟩))
                        0 safeData0 (false, evm1S, out1) := by
                      simpa [hz1False] using htransfer0
                    have henoughSource :
                        (uniswapReserve0Word evm0S).toNat ≤ balance0.toNat := by
                      rw [hsourceReserve]
                      exact hle0
                    have hbody :
                        ExecTransitionBody config contract evmS (skimStore I) skimTransition.body
                          .reverted := by
                      exact uniswapSkimBodyReverts_firstSafeTransferFailure
                        evmS evm0S evm1S I
                        (by simp only [evmS, initState]; exact hwv)
                        hunlockedSolm hguard0 hcall0 hdec0 henoughSource hdata0
                        htransferFalse
                    have rd6595False : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
                        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨6595⟩
                        (⟨0⟩ :: ⟨360⟩ :: UInt256.land token0CleanE solcAddrMask ::
                          ⟨96⟩ :: ⟨0⟩ :: safeValue0 :: skimToMaskedWord I :: token0CleanE ::
                          ⟨5330⟩ ::
                          UInt256.land
                            (uniswapSlotWord ⟨7⟩
                              (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I)
                            solcAddrMask ::
                          token0CleanE :: skimToMaskedWord I :: ⟨570⟩ :: uniswapSelWord I :: [])
                        (skimSafeTransferCallMem2 (UInt256.ofNat I.codeOwner.val) o
                          (skimToMaskedWord I) safeValue0)
                        (UInt256.ofNat 13) out1 (cA1, σ1) k6595 C6595 := by
                      simpa [hz1False, token0CleanE, token0WordE, safeValue0] using rd6595
                    by_cases hout1Empty : out1.size = 0
                    · have rdRev :=
                        RD.uniswapSkimSafeTransferEmptyFailureReverts
                          rd6595False hout1Empty ho32 hoSize
                      exact rdRev.reEquivExecutionRevert hcode hdispatch
                        (uniswapDecode_skim_ok_noncanon hsz36 hcanonTo) hbody
                    · by_cases hout1Sign : out1.size < 2 ^ 255
                      · have rdRev :=
                          RD.uniswapSkimSafeTransferNonemptyFailureReverts
                            rd6595False hout1Empty hout1Sign ho32 hoSize
                        exact rdRev.reEquivExecutionRevert hcode hdispatch
                          (uniswapDecode_skim_ok_noncanon hsz36 hcanonTo) hbody
                      · have hhi : 2 ^ 255 ≤ out1.size := le_of_not_gt hout1Sign
                        have rdRev :=
                          RD.uniswapSkimSafeTransferNonemptyHugeReverts
                            rd6595False hout1Empty hhi hout1Size ho32 hoSize
                        exact rdRev.reEquivExecutionRevert hcode hdispatch
                          (uniswapDecode_skim_ok_noncanon hsz36 hcanonTo) hbody
                  · have hz1True : z1 = true := Bool.eq_true_of_not_eq_false hz1False
                    have htransferTrue : callViaEVM evm0S
                        (EVM.address
                          (uniswapAddressAtSlot (uniswapLockEnteredState evmS) ⟨6⟩))
                        0 safeData0 (true, evm1S, out1) := by
                      simpa [hz1True] using htransfer0
                    have henoughSource :
                        (uniswapReserve0Word evm0S).toNat ≤ balance0.toNat := by
                      rw [hsourceReserve]
                      exact hle0
                    let token1WordE :=
                      uniswapSlotWord ⟨7⟩
                        (sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩) I
                    let token1CleanE := UInt256.land token1WordE solcAddrMask
                    have htarget1 :
                        AccountAddress.ofUInt256 (UInt256.land token1CleanE solcAddrMask) =
                          uniswapAddressAtSlot (uniswapLockEnteredState evmS) ⟨7⟩ := by
                      let σLockE := sstoreAccountMap I.codeOwner σ_evm ⟨12⟩ ⟨0⟩
                      let σLockS := sstoreAccountMap I.codeOwner σ_solm ⟨12⟩ ⟨0⟩
                      let token1WordS := uniswapSlotWord ⟨7⟩ σLockS I
                      have hLockAccounts : accountMapEquiv σLockE σLockS := by
                        exact accountMapEquiv_sstoreAccountMap I.codeOwner ⟨12⟩ ⟨0⟩ hAccounts
                      have hslot : token1WordE = token1WordS := by
                        simpa [σLockE, σLockS, token1WordE, token1WordS] using
                          accountMapEquiv_storage_findD hLockAccounts I.codeOwner ⟨7⟩ ⟨0⟩
                      have hcanonClean : token1CleanE.toNat < EVM.addressModulus := by
                        simpa [token1CleanE, token1WordE, u256_land_comm] using
                          solcAddrMask_result_canonical token1WordE
                      have hclean : UInt256.land token1CleanE solcAddrMask = token1CleanE :=
                        solcAddrMask_clean hcanonClean
                      have haddr :
                          AccountAddress.ofUInt256 token1CleanE =
                            uniswapAddressAtSlot (uniswapLockEnteredState evmS) ⟨7⟩ := by
                        simpa [token1CleanE, token1WordE, token1WordS, σLockS, evmS,
                          uniswapLockEnteredState, uniswapUnlockedState, initState,
                          storageStore_accountMap, storageStore_executionEnv, State.lookupAccount,
                          Account.lookupStorage, Solm.EVM.storageLoad, uniswapAddressAtSlot,
                          uniswapSlotWord, hslot, accountAddress_ofUInt256_eq_ofNat_toNat,
                          u256_land_comm]
                      rw [hclean, haddr]
                    have rd6595True : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
                        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨6595⟩
                        (⟨1⟩ :: ⟨360⟩ :: UInt256.land token0CleanE solcAddrMask ::
                          ⟨96⟩ :: ⟨0⟩ :: safeValue0 :: skimToMaskedWord I :: token0CleanE ::
                          ⟨5330⟩ :: token1CleanE :: token0CleanE :: skimToMaskedWord I ::
                          ⟨570⟩ :: uniswapSelWord I :: [])
                        (skimSafeTransferCallMem2 (UInt256.ofNat I.codeOwner.val) o
                          (skimToMaskedWord I) safeValue0)
                        (UInt256.ofNat 13) out1 (cA1, σ1) k6595 C6595 := by
                      simpa [hz1True, token0CleanE, token0WordE, token1CleanE, token1WordE,
                        safeValue0] using rd6595
                    by_cases hout1Empty : out1.size = 0
                    · have hsafe0 :
                          ExecStmt config
                            { contract := contract,
                              locals := skimFirstExcessStore evmS evm0S I balance0 } evm0S
                            (.internalCall "_safeTransfer"
                              [.var "_token0", .var "to", .var "excess0"] "ok0")
                            (.ok
                              { contract := contract,
                                locals := skimFirstSafeTransferStore evmS evm0S I balance0 }
                              evm1S) := by
                        have hs := safeTransferInternalCallReturns_empty
                          (caller :=
                            { contract := contract,
                              locals := skimFirstExcessStore evmS evm0S I balance0 })
                          (evm := evm0S) (evm' := evm1S)
                          (tokenExpr := .var "_token0") (toExpr := .var "to")
                          (valueExpr := .var "excess0") (retVar := "ok0")
                          (token := uniswapAddressAtSlot (uniswapLockEnteredState evmS) ⟨6⟩)
                          (recipient := skimToAddress I)
                          (value := skimExcess0Word evm0S balance0)
                          (calldata := safeData0) (out := out1)
                          rfl
                          (evalExprs_skim_safeTransfer0_args evmS evm0S I balance0)
                          hdata0 htransferTrue hout1Empty
                        simpa [resumeAfterInternalCall, skimFirstSafeTransferStore] using hs
                      obtain ⟨k5330, C5330, rd5330⟩ :=
                        RD.uniswapSkimSafeTransferEmptyReturnTo5330
                          rd6595True hout1Empty ho32 hoSize
                      have hPostTransferAccounts1 : accountMapEquiv σ1 evm1S.accountMap := by
                        simpa [evm1S] using hPostTransferAccounts0
                      by_cases htoken1NoCode :
                          uniswapExtCodeSizeWord σ1
                            (UInt256.land token1CleanE solcAddrMask) = ⟨0⟩
                      · have hguard1 :=
                          skimToken1GuardAfterFirstTransfer_false
                            (σ := σ1) (evm := evmS) (evm0 := evm0S) (evm1 := evm1S)
                            (I := I) (balance0 := balance0) (token1 := token1CleanE)
                            hPostTransferAccounts1 htarget1 htoken1NoCode
                        have hbody :
                            ExecTransitionBody config contract evmS (skimStore I)
                              skimTransition.body .reverted := by
                          exact uniswapSkimBodyReverts_secondNoCode
                            evmS evm0S evm1S I
                            (by simp only [evmS, initState]; exact hwv)
                            hunlockedSolm hguard0 hcall0 hdec0 henoughSource hsafe0 hguard1
                        have rdRev :=
                          RD.uniswapSkimSecondBalanceOfNoCodeReverts
                            (value := safeValue0) (toWord := skimToMaskedWord I)
                            (token0 := token0CleanE) (token1 := token1CleanE)
                            (sel := uniswapSelWord I) rd5330 ho32 hoSize htoken1NoCode
                        exact rdRev.reEquivExecutionRevert hcode hdispatch
                          (uniswapDecode_skim_ok_noncanon hsz36 hcanonTo) hbody
                      · have htoken1Code :
                            uniswapExtCodeSizeWord σ1
                              (UInt256.land token1CleanE solcAddrMask) ≠ ⟨0⟩ :=
                          htoken1NoCode
                        have hguard1 :=
                          skimToken1GuardAfterFirstTransfer_true
                            (σ := σ1) (evm := evmS) (evm0 := evm0S) (evm1 := evm1S)
                            (I := I) (balance0 := balance0) (token1 := token1CleanE)
                            hPostTransferAccounts1 htarget1 htoken1Code
                        obtain ⟨cA2, σ2, z2, out2, A_in2, callGas2, k5273, C5273,
                            hΘ2, rd5273, hout2Size⟩ :=
                          RD.uniswapSkimSecondBalanceOfStaticcallMade
                            (value := safeValue0) (toWord := skimToMaskedWord I)
                            (token0 := token0CleanE) (token1 := token1CleanE)
                            (sel := uniswapSelWord I) rd5330 ho32 hoSize hdepth htoken1Code
                        have henv1 : evm1S.executionEnv = I := by
                          simpa [evm1S, evmS, uniswapLockEnteredState, uniswapUnlockedState,
                            initState, storageStore_executionEnv] using henv0
                        obtain ⟨evm2S, hcall1Raw, hPost2, hcreated2, hσ2, hgenesis2,
                            hblocks2, henv2⟩ :=
                          uniswapSkimSecondBalanceTypedCall_source
                            (cA1 := cA1) (gh := gh) (bl := bl) (σ1 := σ1) (σ₀ := σ₀)
                            (I := I) (evm1S := evm1S)
                            (cA2 := cA2) (σ2 := σ2) (z2 := z2) (out2 := out2)
                            (A_in2 := A_in2) (callGas2 := callGas2)
                            (o := o) (toWord := skimToMaskedWord I) (value := safeValue0)
                            (token1 := token1CleanE)
                            hPostTransferAccounts1
                            (by simp [evm1S])
                            (by simp [evm1S, hσ0])
                            (by simp [evm1S, hgenesis0])
                            (by simp [evm1S, hblocks0])
                            henv1 hdepth ho32 hoSize hΘ2
                        have htarget1E :
                            AccountAddress.ofUInt256 (UInt256.land token1CleanE solcAddrMask) =
                              EVM.address
                                (uniswapAddressAtSlot (uniswapLockEnteredState evmS) ⟨7⟩) := by
                          change
                            AccountAddress.ofUInt256 (UInt256.land token1CleanE solcAddrMask) =
                              EVM.address
                                (uniswapAddressAtSlot (uniswapLockEnteredState evmS) ⟨7⟩)
                          rw [htarget1]
                          exact
                            (uniswapAddress_self
                              (uniswapAddressAtSlot (uniswapLockEnteredState evmS) ⟨7⟩)).symm
                        have hcall1 : typedCallViaEVM config evm1S
                            (EVM.address
                              (uniswapAddressAtSlot (uniswapLockEnteredState evmS) ⟨7⟩))
                            "balanceOf" 0 [.address evm1S.executionEnv.codeOwner]
                            (z2, evm2S, out2) false := by
                          simpa [htarget1E] using hcall1Raw
                        by_cases hz2False : z2 = false
                        · have hcall1False : typedCallViaEVM config evm1S
                              (EVM.address
                                (uniswapAddressAtSlot (uniswapLockEnteredState evmS) ⟨7⟩))
                              "balanceOf" 0 [.address evm1S.executionEnv.codeOwner]
                              (false, evm2S, out2) false := by
                            simpa [hz2False] using hcall1
                          have hbody :
                              ExecTransitionBody config contract evmS (skimStore I)
                                skimTransition.body .reverted := by
                            exact uniswapSkimBodyReverts_secondCallFailure
                              evmS evm0S evm1S evm2S I
                              (by simp only [evmS, initState]; exact hwv)
                              hunlockedSolm hguard0 hcall0 hdec0 henoughSource hsafe0
                              hguard1 hcall1False
                          have hstatus :
                              (if z2 then (⟨1⟩ : UInt256) else ⟨0⟩) = ⟨0⟩ := by
                            simp [hz2False]
                          have rdRev :=
                            RD.uniswapSkimSecondBalanceCallFailureReverts
                              rd5273 hstatus hout2Size
                              (by simp only [List.length_cons, List.length_nil]; omega)
                          exact rdRev.reEquivExecutionRevert hcode hdispatch
                            (uniswapDecode_skim_ok_noncanon hsz36 hcanonTo) hbody
                        · have hz2True : z2 = true := Bool.eq_true_of_not_eq_false hz2False
                          have hcall1True : typedCallViaEVM config evm1S
                              (EVM.address
                                (uniswapAddressAtSlot (uniswapLockEnteredState evmS) ⟨7⟩))
                              "balanceOf" 0 [.address evm1S.executionEnv.codeOwner]
                              (true, evm2S, out2) false := by
                            simpa [hz2True] using hcall1
                          have hstatus :
                              (if z2 then (⟨1⟩ : UInt256) else ⟨0⟩) ≠ ⟨0⟩ := by
                            rw [hz2True]
                            decide
                          obtain ⟨k5291, C5291, rd5291⟩ :=
                            RD.uniswapSkimSecondBalanceCallSuccessToDecode
                              rd5273 hstatus
                              (by simp only [List.length_cons, List.length_nil]; omega)
                          by_cases hshort2 : out2.size < 32
                          · have hdec1 : config.externalABI.decode? "balanceOf" out2 = none := by
                              change uniswapExternalABI.decode? "balanceOf" out2 = none
                              simpa [uniswapExternalABI, uint256, uint256Int, abiUInt256] using
                                (decodeReturnValueWithMode_legacy_uint256_none_short
                                  (returndata := out2) hshort2)
                            have hbody :
                                ExecTransitionBody config contract evmS (skimStore I)
                                  skimTransition.body .reverted := by
                              exact uniswapSkimBodyReverts_secondCallDecode
                                evmS evm0S evm1S evm2S I
                                (by simp only [evmS, initState]; exact hwv)
                                hunlockedSolm hguard0 hcall0 hdec0 henoughSource hsafe0
                                hguard1 hcall1True hdec1
                            have rdRev :=
                              RD.uniswapSkimSecondBalanceReturnWordDecodeShortReverts
                                rd5291 ho32 hoSize hshort2 hout2Size
                                (by simp only [List.length_cons, List.length_nil]; omega)
                            exact rdRev.reEquivExecutionRevert hcode hdispatch
                              (uniswapDecode_skim_ok_noncanon hsz36 hcanonTo) hbody
                          · have ho32_2 : 32 ≤ out2.size := not_lt.mp hshort2
                            let balance1 :=
                              UInt256.ofNat (fromByteArrayBigEndian (out2.extract 0 32))
                            have hdec1 :
                                config.externalABI.decode? "balanceOf" out2 =
                                  some (skimBalanceValue balance1) := by
                              simpa [balance1] using
                                uniswapSkimBalanceOfDecode_ok (returndata := out2) ho32_2
                            let reserve1E :=
                              UInt256.land reserve112Mask
                                (UInt256.div (uniswapSlotWord ⟨8⟩ σ1 I) reserve112Shift)
                            have hsourceReserve1 : uniswapReserve1Word evm2S = reserve1E := by
                              have h :=
                                uniswapSkimSecondBalanceStaticReserve1
                                  hPostTransferAccounts1 henv1 hcall1True
                              simpa [reserve1E, u256_land_comm] using h
                            obtain ⟨k5314, C5314, rd5314⟩ :=
                              RD.uniswapSkimSecondBalanceReturnWordDecodeOk
                                rd5291 ho32 hoSize ho32_2 hout2Size
                                (by simp only [List.length_cons, List.length_nil]; omega)
                            have rd5314' : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
                                (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                                ⟨5314⟩
                                (balance1 :: reserve1E :: ⟨5325⟩ :: skimToMaskedWord I ::
                                  token1CleanE :: ⟨5433⟩ ::
                                  token1CleanE :: token0CleanE :: skimToMaskedWord I ::
                                  ⟨570⟩ :: uniswapSelWord I :: [])
                                (skimSecondBalanceStaticcallMem
                                  (UInt256.ofNat I.codeOwner.val) o (skimToMaskedWord I)
                                  safeValue0 out2)
                                (UInt256.ofNat 13) out2 (cA2, σ2) k5314 C5314 := by
                              simpa [balance1, reserve1E, u256_land_comm] using rd5314
                            by_cases hlt1 : balance1.toNat < reserve1E.toNat
                            · obtain ⟨k6879, C6879, rd6879⟩ :=
                                RD.uniswapSkimFirstExcessToSub rd5314'
                                  (by simp only [List.length_cons, List.length_nil]; omega)
                              have rd6879' : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
                                  (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                                  ⟨6879⟩
                                  (reserve1E :: balance1 :: ⟨5325⟩ :: skimToMaskedWord I ::
                                    token1CleanE :: ⟨5433⟩ ::
                                    token1CleanE :: token0CleanE :: skimToMaskedWord I ::
                                    ⟨570⟩ :: uniswapSelWord I :: [])
                                  (skimSecondBalanceStaticcallMem
                                    (UInt256.ofNat I.codeOwner.val) o (skimToMaskedWord I)
                                    safeValue0 out2)
                                  (UInt256.ofNat 13) out2 (cA2, σ2) k6879 C6879 := by
                                simpa using rd6879
                              have hmem :
                                  (skimSecondBalanceStaticcallMem
                                    (UInt256.ofNat I.codeOwner.val) o (skimToMaskedWord I)
                                    safeValue0 out2).size = 388 :=
                                skimSecondBalanceStaticcallMem_size_of_size_ge
                                  (UInt256.ofNat I.codeOwner.val) (skimToMaskedWord I) safeValue0
                                  out2 ho32 hoSize ho32_2 hout2Size
                              have hread64 :
                                  (skimSecondBalanceStaticcallMem
                                    (UInt256.ofNat I.codeOwner.val) o (skimToMaskedWord I)
                                    safeValue0 out2).readWithPadding 64 32 =
                                    UInt256.toByteArray ⟨292⟩ :=
                                skimSecondBalanceStaticcallMem_read64_of_size_ge
                                  (UInt256.ofNat I.codeOwner.val) (skimToMaskedWord I) safeValue0
                                  out2 ho32 hoSize ho32_2 hout2Size
                              have rdRev :=
                                RD.uniswapSafeMathSubUnderflow_aw13_free292
                                  rd6879' hlt1 hmem hread64
                                  (by simp only [List.length_cons, List.length_nil]; omega)
                              have hltSource :
                                  balance1.toNat < (uniswapReserve1Word evm2S).toNat := by
                                rw [hsourceReserve1]
                                exact hlt1
                              have hbody :
                                  ExecTransitionBody config contract evmS (skimStore I)
                                    skimTransition.body .reverted := by
                                exact uniswapSkimBodyReverts_secondExcessUnderflow
                                  evmS evm0S evm1S evm2S I
                                  (by simp only [evmS, initState]; exact hwv)
                                  hunlockedSolm hguard0 hcall0 hdec0 henoughSource hsafe0
                                  hguard1 hcall1True hdec1 hltSource
                              exact rdRev.reEquivExecutionRevert hcode hdispatch
                                (uniswapDecode_skim_ok_noncanon hsz36 hcanonTo) hbody
                            · have hle1 : reserve1E.toNat ≤ balance1.toNat := not_lt.mp hlt1
                              obtain ⟨k6879, C6879, rd6879⟩ :=
                                RD.uniswapSkimFirstExcessToSub rd5314'
                                  (by simp only [List.length_cons, List.length_nil]; omega)
                              have rd6879' : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
                                  (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                                  ⟨6879⟩
                                  (reserve1E :: balance1 :: ⟨5325⟩ :: skimToMaskedWord I ::
                                    token1CleanE :: ⟨5433⟩ ::
                                    token1CleanE :: token0CleanE :: skimToMaskedWord I ::
                                    ⟨570⟩ :: uniswapSelWord I :: [])
                                  (skimSecondBalanceStaticcallMem
                                    (UInt256.ofNat I.codeOwner.val) o (skimToMaskedWord I)
                                    safeValue0 out2)
                                  (UInt256.ofNat 13) out2 (cA2, σ2) k6879 C6879 := by
                                simpa using rd6879
                              obtain ⟨k6370, C6370, rd6370⟩ :=
                                RD.uniswapSkimExcessSuccessToSafeTransferEntry rd6879' hle1
                                  (by simp only [List.length_cons, List.length_nil]; omega)
                              let safeValue1 := UInt256.sub balance1 reserve1E
                              let safeData1 :=
                                (skimSecondSafeTransferCallMem2
                                  (UInt256.ofNat I.codeOwner.val) o (skimToMaskedWord I)
                                  safeValue0 out2 safeValue1).readWithPadding 456 68
                              have hdata1 :
                                  transferCalldata? (skimToAddress I)
                                      (skimExcess1Word evm2S balance1) =
                                    some safeData1 := by
                                have hencoded :=
                                  skimSecondSafeTransferCalldata_masked
                                    (evm2S := evm2S) (I := I) (o := o) (out2 := out2)
                                    (balance1 := balance1) (reserve1 := reserve1E)
                                    (prevValue := safeValue0) hsourceReserve1 hle1
                                    ho32 hoSize ho32_2 hout2Size
                                simpa [safeData1, safeValue1] using hencoded
                              have rd6370' : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
                                  (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                                  ⟨6370⟩
                                  (safeValue1 :: skimToMaskedWord I :: token1CleanE :: ⟨5433⟩ ::
                                    token1CleanE :: token0CleanE :: skimToMaskedWord I ::
                                    ⟨570⟩ :: uniswapSelWord I :: [])
                                  (skimSecondBalanceStaticcallMem
                                    (UInt256.ofNat I.codeOwner.val) o (skimToMaskedWord I)
                                    safeValue0 out2)
                                  (UInt256.ofNat 13) out2 (cA2, σ2) k6370 C6370 := by
                                simpa [safeValue1] using rd6370
                              obtain ⟨cA3, σ3, z3, out3, A_in3, callGas3, _gasArg3,
                                  k6595b, C6595b, hΘsafe1, rd6595b, hout3Size⟩ :=
                                RD.uniswapSkimSecondSafeTransferEntryToCallMade
                                  rd6370' ho32 hoSize ho32_2 hout2Size hdepth
                              let evm2E : EVM.State :=
                                { evm2S with
                                  accountMap := σ2
                                  createdAccounts := cA2
                                  σ₀ := σ₀
                                  genesisBlockHeader := gh
                                  blocks := bl
                                  executionEnv := I }
                              obtain ⟨g3Ret, A3E, hΘsafeEq1⟩ := hΘsafe1
                              have hcallE1 : callViaEVM evm2E
                                  (AccountAddress.ofUInt256
                                    (UInt256.land token1CleanE solcAddrMask))
                                  0 safeData1
                                  (z3,
                                    { evm2E with
                                      accountMap := σ3
                                      substate := A3E
                                      createdAccounts := cA3 },
                                    out3) := by
                                refine callViaEVM.callMade (perm := true) (g' := g3Ret)
                                  wordOfInt_zero.symm ?_ rfl ?_ ?_
                                · refine ⟨callGas3, A_in3, ?_⟩
                                  simpa [evm2E, safeData1, safeValue1, hperm,
                                    accountAddress_roundtrip] using hΘsafeEq1
                                · show (⟨0⟩ : UInt256) ≤ _
                                  exact Fin.zero_le _
                                · intro hdepthEq
                                  have hdepthLt : I.depth.val < 1024 := hdepth
                                  rw [show evm2E.executionEnv.depth = I.depth by simp [evm2E]]
                                    at hdepthEq
                                  rw [hdepthEq] at hdepthLt
                                  exact absurd hdepthLt (by decide)
                              obtain ⟨σ3S, A3S, htransfer1Raw, hPostTransferAccounts2⟩ :=
                                callViaEVM_accountMapEquiv (storage := config.storage)
                                  (evm_evm := evm2E) (evm_solm := evm2S)
                                  hcallE1 hPost2
                                  (by simp [evm2E, hσ2])
                                  (by simp [evm2E, hcreated2])
                                  (by simp [evm2E, hgenesis2])
                                  (by simp [evm2E, hblocks2])
                                  (by simp [evm2E])
                                  (by simp [evm2E, henv2, henv1])
                              let evm3S : EVM.State :=
                                { evm2S with
                                  accountMap := σ3S
                                  substate := A3S
                                  createdAccounts := cA3 }
                              have htransfer1Raw' : callViaEVM evm2S
                                  (AccountAddress.ofUInt256
                                    (UInt256.land token1CleanE solcAddrMask))
                                  0 safeData1 (z3, evm3S, out3) := by
                                simpa [evm3S] using htransfer1Raw
                              have htransfer1Target :
                                  AccountAddress.ofUInt256
                                      (UInt256.land token1CleanE solcAddrMask) =
                                    EVM.address
                                      (uniswapAddressAtSlot
                                        (uniswapLockEnteredState evmS) ⟨7⟩) := by
                                rw [htarget1]
                                exact (uniswapAddress_self
                                  (uniswapAddressAtSlot (uniswapLockEnteredState evmS) ⟨7⟩)).symm
                              have htransfer1 : callViaEVM evm2S
                                  (EVM.address
                                    (uniswapAddressAtSlot (uniswapLockEnteredState evmS) ⟨7⟩))
                                  0 safeData1 (z3, evm3S, out3) := by
                                simpa [htransfer1Target] using htransfer1Raw'
                              have hPostTransferAccounts3 :
                                  accountMapEquiv σ3 evm3S.accountMap := by
                                simpa [evm3S] using hPostTransferAccounts2
                              have henv3 : evm3S.executionEnv = I := by
                                simpa [evm3S] using henv2.trans henv1
                              have henough1Source :
                                  (uniswapReserve1Word evm2S).toNat ≤ balance1.toNat := by
                                rw [hsourceReserve1]
                                exact hle1
                              have hfinish :
                                  ∀ {mem outRet : ByteArray} {aw : UInt256} {kR CR : ℕ},
                                    RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
                                      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                                      ⟨5433⟩
                                      (token1CleanE :: token0CleanE :: skimToMaskedWord I ::
                                        ⟨570⟩ :: uniswapSelWord I :: [])
                                      mem aw outRet (cA3, σ3) kR CR →
                                    ExecStmt config
                                      { contract := contract,
                                        locals :=
                                          skimSecondExcessStore evmS evm0S evm2S I
                                            balance0 balance1 } evm2S
                                      (.internalCall "_safeTransfer"
                                        [.var "_token1", .var "to", .var "excess1"] "ok1")
                                      (.ok
                                        { contract := contract,
                                          locals :=
                                            skimSecondSafeTransferStore evmS evm0S evm2S I
                                              balance0 balance1 }
                                        evm3S) →
                                    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀
                                      g A I := by
                                intro mem outRet aw kR CR rd5433 hsafe1
                                have rdRet :=
                                  RD.uniswapSkimAfterSecondSafeTransferToReturn rd5433 hperm
                                have hbody :
                                    ExecTransitionBody config contract evmS (skimStore I)
                                      skimTransition.body
                                      (.returned
                                        { contract := contract,
                                          locals :=
                                            skimSecondSafeTransferStore evmS evm0S evm2S I
                                              balance0 balance1 }
                                        (uniswapLockExitedState evm3S) none) := by
                                  exact uniswapSkimBodyReturns
                                    evmS evm0S evm1S evm2S evm3S I
                                    (by simp only [evmS, initState]; exact hwv)
                                    hunlockedSolm hguard0 hcall0 hdec0 henoughSource hsafe0
                                    hguard1 hcall1True hdec1 henough1Source hsafe1
                                have hCreatedRet :
                                    cA3 = (uniswapLockExitedState evm3S).createdAccounts := by
                                  simp [uniswapLockExitedState, uniswapUnlockedState, evm3S,
                                    storageStore_createdAccounts]
                                have hAccountsRet :
                                    accountMapEquiv
                                      (sstoreAccountMap I.codeOwner σ3 ⟨12⟩ ⟨1⟩)
                                      (uniswapLockExitedState evm3S).accountMap := by
                                  have hs :=
                                    accountMapEquiv_sstoreAccountMap I.codeOwner ⟨12⟩ ⟨1⟩
                                      hPostTransferAccounts3
                                  simpa [uniswapLockExitedState, uniswapUnlockedState,
                                    storageStore_accountMap, henv3] using hs
                                exact rdRet.reEquivExecutionGenAccountMapEquiv hcode hdispatch
                                  (uniswapDecode_skim_ok_noncanon hsz36 hcanonTo) hbody hCreatedRet
                                  hAccountsRet (returnEquiv.void rfl rfl rfl)
                              by_cases hz3False : z3 = false
                              · have htransfer1False : callViaEVM evm2S
                                    (EVM.address
                                      (uniswapAddressAtSlot
                                        (uniswapLockEnteredState evmS) ⟨7⟩))
                                    0 safeData1 (false, evm3S, out3) := by
                                  simpa [hz3False] using htransfer1
                                have hbody :
                                    ExecTransitionBody config contract evmS (skimStore I)
                                      skimTransition.body .reverted := by
                                  exact uniswapSkimBodyReverts_secondSafeTransferFailure
                                    evmS evm0S evm1S evm2S evm3S I
                                    (by simp only [evmS, initState]; exact hwv)
                                    hunlockedSolm hguard0 hcall0 hdec0 henoughSource hsafe0
                                    hguard1 hcall1True hdec1 henough1Source hdata1
                                    htransfer1False
                                have rd6595False : RD uniswapV2PairBytecode I
                                    (Sat256.ofUInt256 g)
                                    (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                                    ⟨6595⟩
                                    (⟨0⟩ :: ⟨524⟩ ::
                                      UInt256.land token1CleanE solcAddrMask :: ⟨96⟩ :: ⟨0⟩ ::
                                      safeValue1 :: skimToMaskedWord I :: token1CleanE :: ⟨5433⟩ ::
                                      token1CleanE :: token0CleanE :: skimToMaskedWord I ::
                                      ⟨570⟩ :: uniswapSelWord I :: [])
                                    (skimSecondSafeTransferCallMem2
                                      (UInt256.ofNat I.codeOwner.val) o (skimToMaskedWord I)
                                      safeValue0 out2 safeValue1)
                                    (UInt256.ofNat 18) out3 (cA3, σ3) k6595b C6595b := by
                                  simpa [hz3False, safeValue1] using rd6595b
                                by_cases hout3Empty : out3.size = 0
                                · have rdRev :=
                                    RD.uniswapSkimSecondSafeTransferEmptyFailureReverts
                                      rd6595False hout3Empty ho32 hoSize ho32_2 hout2Size
                                  exact rdRev.reEquivExecutionRevert hcode hdispatch
                                    (uniswapDecode_skim_ok_noncanon hsz36 hcanonTo) hbody
                                · by_cases hout3Sign : out3.size < 2 ^ 255
                                  · have rdRev :=
                                      RD.uniswapSkimSecondSafeTransferNonemptyFailureReverts
                                        rd6595False hout3Empty hout3Sign ho32 hoSize
                                        ho32_2 hout2Size
                                    exact rdRev.reEquivExecutionRevert hcode hdispatch
                                      (uniswapDecode_skim_ok_noncanon hsz36 hcanonTo) hbody
                                  · have hhi : 2 ^ 255 ≤ out3.size := le_of_not_gt hout3Sign
                                    have rdRev :=
                                      RD.uniswapSkimSecondSafeTransferNonemptyHugeReverts
                                        rd6595False hout3Empty hhi hout3Size ho32 hoSize
                                        ho32_2 hout2Size
                                    exact rdRev.reEquivExecutionRevert hcode hdispatch
                                      (uniswapDecode_skim_ok_noncanon hsz36 hcanonTo) hbody
                              · have hz3True : z3 = true := Bool.eq_true_of_not_eq_false hz3False
                                have htransfer1True : callViaEVM evm2S
                                    (EVM.address
                                      (uniswapAddressAtSlot
                                        (uniswapLockEnteredState evmS) ⟨7⟩))
                                    0 safeData1 (true, evm3S, out3) := by
                                  simpa [hz3True] using htransfer1
                                have rd6595True : RD uniswapV2PairBytecode I
                                    (Sat256.ofUInt256 g)
                                    (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                                    ⟨6595⟩
                                    (⟨1⟩ :: ⟨524⟩ ::
                                      UInt256.land token1CleanE solcAddrMask :: ⟨96⟩ :: ⟨0⟩ ::
                                      safeValue1 :: skimToMaskedWord I :: token1CleanE :: ⟨5433⟩ ::
                                      token1CleanE :: token0CleanE :: skimToMaskedWord I ::
                                      ⟨570⟩ :: uniswapSelWord I :: [])
                                    (skimSecondSafeTransferCallMem2
                                      (UInt256.ofNat I.codeOwner.val) o (skimToMaskedWord I)
                                      safeValue0 out2 safeValue1)
                                    (UInt256.ofNat 18) out3 (cA3, σ3) k6595b C6595b := by
                                  simpa [hz3True, safeValue1] using rd6595b
                                by_cases hout3Empty : out3.size = 0
                                · have hsafe1 :
                                      ExecStmt config
                                        { contract := contract,
                                          locals :=
                                            skimSecondExcessStore evmS evm0S evm2S I
                                              balance0 balance1 } evm2S
                                        (.internalCall "_safeTransfer"
                                          [.var "_token1", .var "to", .var "excess1"] "ok1")
                                        (.ok
                                          { contract := contract,
                                            locals :=
                                              skimSecondSafeTransferStore evmS evm0S evm2S I
                                                balance0 balance1 }
                                          evm3S) := by
                                    have hs := safeTransferInternalCallReturns_empty
                                      (caller :=
                                        { contract := contract,
                                          locals :=
                                            skimSecondExcessStore evmS evm0S evm2S I
                                              balance0 balance1 })
                                      (evm := evm2S) (evm' := evm3S)
                                      (tokenExpr := .var "_token1") (toExpr := .var "to")
                                      (valueExpr := .var "excess1") (retVar := "ok1")
                                      (token :=
                                        uniswapAddressAtSlot (uniswapLockEnteredState evmS) ⟨7⟩)
                                      (recipient := skimToAddress I)
                                      (value := skimExcess1Word evm2S balance1)
                                      (calldata := safeData1) (out := out3)
                                      rfl
                                      (evalExprs_skim_safeTransfer1_args
                                        evmS evm0S evm2S I balance0 balance1)
                                      hdata1 htransfer1True hout3Empty
                                    simpa [resumeAfterInternalCall, skimSecondSafeTransferStore]
                                      using hs
                                  obtain ⟨k5433, C5433, rd5433⟩ :=
                                    RD.uniswapSkimSecondSafeTransferEmptyReturnTo5433
                                      rd6595True hout3Empty ho32 hoSize ho32_2 hout2Size
                                  exact hfinish rd5433 hsafe1
                                · by_cases hout3Sign : out3.size < 2 ^ 255
                                  · by_cases hshort3 : out3.size < 32
                                    · have hdecSafe1 :
                                          ABI.decodeReturnValueWithMode?
                                              config.abiDecodeMode boolTy out3 =
                                            none := by
                                        change
                                          ABI.decodeReturnValueWithMode?
                                              DecodeMode.legacySolc05 boolTy out3 =
                                            none
                                        exact decodeReturnValueWithMode_legacy_bool_none_short
                                          (returndata := out3) hshort3
                                      have hbody :
                                          ExecTransitionBody config contract evmS (skimStore I)
                                            skimTransition.body .reverted := by
                                        exact uniswapSkimBodyReverts_secondSafeTransferDecode
                                          evmS evm0S evm1S evm2S evm3S I
                                          (by simp only [evmS, initState]; exact hwv)
                                          hunlockedSolm hguard0 hcall0 hdec0 henoughSource hsafe0
                                          hguard1 hcall1True hdec1 henough1Source hdata1
                                          htransfer1True hout3Empty hdecSafe1
                                      have rdRev :=
                                        RD.uniswapSkimSecondSafeTransferNonemptyShortReverts
                                          rd6595True hout3Empty hshort3 hout3Sign ho32 hoSize
                                          ho32_2 hout2Size
                                      exact rdRev.reEquivExecutionRevert hcode hdispatch
                                        (uniswapDecode_skim_ok_noncanon hsz36 hcanonTo) hbody
                                    · have hout332 : 32 ≤ out3.size := not_lt.mp hshort3
                                      let safeWord1 :=
                                        UInt256.ofNat
                                          (fromByteArrayBigEndian (out3.extract 0 32))
                                      by_cases hword1 : safeWord1 = ⟨0⟩
                                      · have hdecSafe1 :
                                            ABI.decodeReturnValueWithMode?
                                                config.abiDecodeMode boolTy out3 =
                                              some (.bool false) := by
                                          change
                                            ABI.decodeReturnValueWithMode?
                                                DecodeMode.legacySolc05 boolTy out3 =
                                              some (.bool false)
                                          exact decodeReturnValueWithMode_legacy_bool_false
                                            (returndata := out3) hout332 hout3Sign hword1
                                        have hbody :
                                            ExecTransitionBody config contract evmS (skimStore I)
                                              skimTransition.body .reverted := by
                                          exact uniswapSkimBodyReverts_secondSafeTransferDecodeFalse
                                            evmS evm0S evm1S evm2S evm3S I
                                            (by simp only [evmS, initState]; exact hwv)
                                            hunlockedSolm hguard0 hcall0 hdec0 henoughSource hsafe0
                                            hguard1 hcall1True hdec1 henough1Source hdata1
                                            htransfer1True hout3Empty hdecSafe1
                                        have rdRev :=
                                          RD.uniswapSkimSecondSafeTransferNonemptyFalseReverts
                                            rd6595True hout3Empty hout332 hout3Sign hword1 ho32
                                            hoSize ho32_2 hout2Size
                                        exact rdRev.reEquivExecutionRevert hcode hdispatch
                                          (uniswapDecode_skim_ok_noncanon hsz36 hcanonTo) hbody
                                      · have hdecSafe1 :
                                            ABI.decodeReturnValueWithMode?
                                                config.abiDecodeMode boolTy out3 =
                                              some (.bool true) := by
                                          change
                                            ABI.decodeReturnValueWithMode?
                                                DecodeMode.legacySolc05 boolTy out3 =
                                              some (.bool true)
                                          exact decodeReturnValueWithMode_legacy_bool_true
                                            (returndata := out3) hout332 hout3Sign hword1
                                        have hsafe1 :
                                            ExecStmt config
                                              { contract := contract,
                                                locals :=
                                                  skimSecondExcessStore evmS evm0S evm2S I
                                                    balance0 balance1 } evm2S
                                              (.internalCall "_safeTransfer"
                                                [.var "_token1", .var "to", .var "excess1"]
                                                "ok1")
                                              (.ok
                                                { contract := contract,
                                                  locals :=
                                                    skimSecondSafeTransferStore evmS evm0S evm2S I
                                                      balance0 balance1 }
                                                evm3S) := by
                                          have hs := safeTransferInternalCallReturns_decodeTrue
                                            (caller :=
                                              { contract := contract,
                                                locals :=
                                                  skimSecondExcessStore evmS evm0S evm2S I
                                                    balance0 balance1 })
                                            (evm := evm2S) (evm' := evm3S)
                                            (tokenExpr := .var "_token1") (toExpr := .var "to")
                                            (valueExpr := .var "excess1") (retVar := "ok1")
                                            (token :=
                                              uniswapAddressAtSlot
                                                (uniswapLockEnteredState evmS) ⟨7⟩)
                                            (recipient := skimToAddress I)
                                            (value := skimExcess1Word evm2S balance1)
                                            (calldata := safeData1) (out := out3)
                                            rfl
                                            (evalExprs_skim_safeTransfer1_args
                                              evmS evm0S evm2S I balance0 balance1)
                                            hdata1 htransfer1True hout3Empty hdecSafe1
                                          simpa [resumeAfterInternalCall, skimSecondSafeTransferStore]
                                            using hs
                                        obtain ⟨k5433, C5433, rd5433⟩ :=
                                          RD.uniswapSkimSecondSafeTransferNonemptyTrueToRet
                                            rd6595True hout3Empty hout332 hout3Sign hword1 ho32
                                            hoSize ho32_2 hout2Size (by jump_dest)
                                        exact hfinish rd5433 hsafe1
                                  · have hhi : 2 ^ 255 ≤ out3.size := le_of_not_gt hout3Sign
                                    have hdecSafe1 :
                                        ABI.decodeReturnValueWithMode?
                                            config.abiDecodeMode boolTy out3 =
                                          none := by
                                      change
                                        ABI.decodeReturnValueWithMode?
                                            DecodeMode.legacySolc05 boolTy out3 =
                                          none
                                      exact decodeReturnValueWithMode_legacy_bool_none_huge
                                        (returndata := out3) hhi
                                    have hbody :
                                        ExecTransitionBody config contract evmS (skimStore I)
                                          skimTransition.body .reverted := by
                                      exact uniswapSkimBodyReverts_secondSafeTransferDecode
                                        evmS evm0S evm1S evm2S evm3S I
                                        (by simp only [evmS, initState]; exact hwv)
                                        hunlockedSolm hguard0 hcall0 hdec0 henoughSource hsafe0
                                        hguard1 hcall1True hdec1 henough1Source hdata1
                                        htransfer1True hout3Empty hdecSafe1
                                    have rdRev :=
                                      RD.uniswapSkimSecondSafeTransferNonemptyHugeReverts
                                        rd6595True hout3Empty hhi hout3Size ho32 hoSize
                                        ho32_2 hout2Size
                                    exact rdRev.reEquivExecutionRevert hcode hdispatch
                                      (uniswapDecode_skim_ok_noncanon hsz36 hcanonTo) hbody
                    · by_cases hout1Sign : out1.size < 2 ^ 255
                      · by_cases hshort1 : out1.size < 32
                        · have hdecSafe0 :
                              ABI.decodeReturnValueWithMode? config.abiDecodeMode boolTy out1 =
                                none := by
                            change
                              ABI.decodeReturnValueWithMode? DecodeMode.legacySolc05 boolTy out1 =
                                none
                            exact decodeReturnValueWithMode_legacy_bool_none_short
                              (returndata := out1) hshort1
                          have hbody :
                              ExecTransitionBody config contract evmS (skimStore I)
                                skimTransition.body .reverted := by
                            exact uniswapSkimBodyReverts_firstSafeTransferDecode
                              evmS evm0S evm1S I
                              (by simp only [evmS, initState]; exact hwv)
                              hunlockedSolm hguard0 hcall0 hdec0 henoughSource hdata0
                              htransferTrue hout1Empty hdecSafe0
                          have rdRev :=
                            RD.uniswapSkimSafeTransferNonemptyShortReverts
                              rd6595True hout1Empty hshort1 hout1Sign ho32 hoSize
                          exact rdRev.reEquivExecutionRevert hcode hdispatch
                            (uniswapDecode_skim_ok_noncanon hsz36 hcanonTo) hbody
                        · have hout132 : 32 ≤ out1.size := not_lt.mp hshort1
                          let safeWord0 :=
                            UInt256.ofNat (fromByteArrayBigEndian (out1.extract 0 32))
                          by_cases hword0 : safeWord0 = ⟨0⟩
                          · have hdecSafe0 :
                                ABI.decodeReturnValueWithMode? config.abiDecodeMode boolTy out1 =
                                  some (.bool false) := by
                              change
                                ABI.decodeReturnValueWithMode? DecodeMode.legacySolc05 boolTy out1 =
                                  some (.bool false)
                              exact decodeReturnValueWithMode_legacy_bool_false
                                (returndata := out1) hout132 hout1Sign hword0
                            have hbody :
                                ExecTransitionBody config contract evmS (skimStore I)
                                  skimTransition.body .reverted := by
                              exact uniswapSkimBodyReverts_firstSafeTransferDecodeFalse
                                evmS evm0S evm1S I
                                (by simp only [evmS, initState]; exact hwv)
                                hunlockedSolm hguard0 hcall0 hdec0 henoughSource hdata0
                                htransferTrue hout1Empty hdecSafe0
                            have rdRev :=
                              RD.uniswapSkimSafeTransferNonemptyFalseReverts
                                rd6595True hout1Empty hout132 hout1Sign hword0 ho32 hoSize
                            exact rdRev.reEquivExecutionRevert hcode hdispatch
                              (uniswapDecode_skim_ok_noncanon hsz36 hcanonTo) hbody
                          · have hdecSafe0 :
                                ABI.decodeReturnValueWithMode? config.abiDecodeMode boolTy out1 =
                                  some (.bool true) := by
                              change
                                ABI.decodeReturnValueWithMode? DecodeMode.legacySolc05 boolTy out1 =
                                  some (.bool true)
                              exact decodeReturnValueWithMode_legacy_bool_true
                                (returndata := out1) hout132 hout1Sign hword0
                            have hsafe0 :
                                ExecStmt config
                                  { contract := contract,
                                    locals := skimFirstExcessStore evmS evm0S I balance0 } evm0S
                                  (.internalCall "_safeTransfer"
                                    [.var "_token0", .var "to", .var "excess0"] "ok0")
                                  (.ok
                                    { contract := contract,
                                      locals := skimFirstSafeTransferStore evmS evm0S I balance0 }
                                    evm1S) := by
                              have hs := safeTransferInternalCallReturns_decodeTrue
                                (caller :=
                                  { contract := contract,
                                    locals := skimFirstExcessStore evmS evm0S I balance0 })
                                (evm := evm0S) (evm' := evm1S)
                                (tokenExpr := .var "_token0") (toExpr := .var "to")
                                (valueExpr := .var "excess0") (retVar := "ok0")
                                (token := uniswapAddressAtSlot (uniswapLockEnteredState evmS) ⟨6⟩)
                                (recipient := skimToAddress I)
                                (value := skimExcess0Word evm0S balance0)
                                (calldata := safeData0) (out := out1)
                                rfl
                                (evalExprs_skim_safeTransfer0_args evmS evm0S I balance0)
                                hdata0 htransferTrue hout1Empty hdecSafe0
                              simpa [resumeAfterInternalCall, skimFirstSafeTransferStore] using hs
                            obtain ⟨k5330, C5330, rd5330⟩ :=
                              RD.uniswapSkimSafeTransferNonemptyTrueToRet
                                rd6595True hout1Empty hout132 hout1Sign hword0 ho32 hoSize
                                (by jump_dest)
                            have hPostTransferAccounts1 :
                                accountMapEquiv σ1 evm1S.accountMap := by
                              simpa [evm1S] using hPostTransferAccounts0
                            have hout1Small : out1.size < 2 ^ 138 := by
                              have htheta :=
                                Theta_returnData_size_lt_2pow138 I.blobVersionedHashes cA'
                                  ((initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I).genesisBlockHeader)
                                  (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I).blocks
                                  σ'
                                  (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I).σ₀
                                  A_in1
                                  (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner.val))
                                  I.sender
                                  (AccountAddress.ofUInt256
                                    (UInt256.land token0CleanE solcAddrMask))
                                  (toExecute σ'
                                    (AccountAddress.ofUInt256
                                      (UInt256.land token0CleanE solcAddrMask)))
                                  callGas1 (UInt256.ofNat I.gasPrice) ⟨0⟩ ⟨0⟩
                                  ((skimSafeTransferCallMem2 (UInt256.ofNat I.codeOwner.val) o
                                    (skimToMaskedWord I) (balance0.sub reserve0E)).readWithPadding
                                    292 68)
                                  (I.depth + 1) I.header I.perm
                                  (by
                                    exact
                                      Ethereum.EVM.ByteArray.readWithPadding_size_lt_uint256
                                        _ _ _)
                              rw [← hΘsafeEq] at htheta
                              simpa using htheta
                            by_cases htoken1NoCode :
                                uniswapExtCodeSizeWord σ1
                                  (UInt256.land token1CleanE solcAddrMask) = ⟨0⟩
                            · have hguard1 :=
                                skimToken1GuardAfterFirstTransfer_false
                                  (σ := σ1) (evm := evmS) (evm0 := evm0S) (evm1 := evm1S)
                                  (I := I) (balance0 := balance0) (token1 := token1CleanE)
                                  hPostTransferAccounts1 htarget1 htoken1NoCode
                              have hbody :
                                  ExecTransitionBody config contract evmS (skimStore I)
                                    skimTransition.body .reverted := by
                                exact uniswapSkimBodyReverts_secondNoCode
                                  evmS evm0S evm1S I
                                  (by simp only [evmS, initState]; exact hwv)
                                  hunlockedSolm hguard0 hcall0 hdec0 henoughSource hsafe0 hguard1
                              have rdRev :=
                                RD.uniswapSkimSecondBalanceOfNoCodeReverts_dynamic
                                  (value := safeValue0) (toWord := skimToMaskedWord I)
                                  (token0 := token0CleanE) (token1 := token1CleanE)
                                  (sel := uniswapSelWord I) rd5330 ho32 hoSize
                                  hout1Empty hout1Sign htoken1NoCode
                              exact rdRev.reEquivExecutionRevert hcode hdispatch
                                (uniswapDecode_skim_ok_noncanon hsz36 hcanonTo) hbody
                            · have htoken1Code :
                                  uniswapExtCodeSizeWord σ1
                                    (UInt256.land token1CleanE solcAddrMask) ≠ ⟨0⟩ :=
                                htoken1NoCode
                              have hguard1 :=
                                skimToken1GuardAfterFirstTransfer_true
                                  (σ := σ1) (evm := evmS) (evm0 := evm0S) (evm1 := evm1S)
                                  (I := I) (balance0 := balance0) (token1 := token1CleanE)
                                  hPostTransferAccounts1 htarget1 htoken1Code
                              obtain ⟨cA2, σ2, z2, out2, A_in2, callGas2, k5273, C5273,
                                  hΘ2, rd5273, hout2Size⟩ :=
                                RD.uniswapSkimSecondBalanceOfStaticcallMade_dynamic
                                  (value := safeValue0) (toWord := skimToMaskedWord I)
                                  (token0 := token0CleanE) (token1 := token1CleanE)
                                  (sel := uniswapSelWord I) rd5330 ho32 hoSize
                                  hout1Empty hout1Sign hdepth htoken1Code
                              have henv1 : evm1S.executionEnv = I := by
                                simpa [evm1S, evmS, uniswapLockEnteredState,
                                  uniswapUnlockedState, initState, storageStore_executionEnv]
                                  using henv0
                              obtain ⟨evm2S, hcall1Raw, hPost2, hcreated2, hσ2, hgenesis2,
                                  hblocks2, henv2⟩ :=
                                uniswapSkimSecondBalanceTypedCall_source_dynamic
                                  (cA1 := cA1) (gh := gh) (bl := bl) (σ1 := σ1) (σ₀ := σ₀)
                                  (I := I) (evm1S := evm1S)
                                  (cA2 := cA2) (σ2 := σ2) (z2 := z2) (out2 := out2)
                                  (A_in2 := A_in2) (callGas2 := callGas2)
                                  (o := o) (out1 := out1) (toWord := skimToMaskedWord I)
                                  (value := safeValue0) (token1 := token1CleanE)
                                  hPostTransferAccounts1
                                  (by simp [evm1S])
                                  (by simp [evm1S, hσ0])
                                  (by simp [evm1S, hgenesis0])
                                  (by simp [evm1S, hblocks0])
                                  henv1 hdepth ho32 hoSize hout1Empty hout1Sign hΘ2
                              have htarget1E :
                                  AccountAddress.ofUInt256
                                      (UInt256.land token1CleanE solcAddrMask) =
                                    EVM.address
                                      (uniswapAddressAtSlot
                                        (uniswapLockEnteredState evmS) ⟨7⟩) := by
                                change
                                  AccountAddress.ofUInt256
                                      (UInt256.land token1CleanE solcAddrMask) =
                                    EVM.address
                                      (uniswapAddressAtSlot
                                        (uniswapLockEnteredState evmS) ⟨7⟩)
                                rw [htarget1]
                                exact
                                  (uniswapAddress_self
                                    (uniswapAddressAtSlot
                                      (uniswapLockEnteredState evmS) ⟨7⟩)).symm
                              have hcall1 : typedCallViaEVM config evm1S
                                  (EVM.address
                                    (uniswapAddressAtSlot
                                      (uniswapLockEnteredState evmS) ⟨7⟩))
                                  "balanceOf" 0 [.address evm1S.executionEnv.codeOwner]
                                  (z2, evm2S, out2) false := by
                                simpa [htarget1E] using hcall1Raw
                              by_cases hz2False : z2 = false
                              · have hcall1False : typedCallViaEVM config evm1S
                                    (EVM.address
                                      (uniswapAddressAtSlot
                                        (uniswapLockEnteredState evmS) ⟨7⟩))
                                    "balanceOf" 0 [.address evm1S.executionEnv.codeOwner]
                                    (false, evm2S, out2) false := by
                                  simpa [hz2False] using hcall1
                                have hbody :
                                    ExecTransitionBody config contract evmS (skimStore I)
                                      skimTransition.body .reverted := by
                                  exact uniswapSkimBodyReverts_secondCallFailure
                                    evmS evm0S evm1S evm2S I
                                    (by simp only [evmS, initState]; exact hwv)
                                    hunlockedSolm hguard0 hcall0 hdec0 henoughSource hsafe0
                                    hguard1 hcall1False
                                have hstatus :
                                    (if z2 then (⟨1⟩ : UInt256) else ⟨0⟩) = ⟨0⟩ := by
                                  simp [hz2False]
                                have rdRev :=
                                  RD.uniswapSkimSecondBalanceCallFailureReverts_dynamic
                                    rd5273 hstatus hout2Size
                                    (by simp only [List.length_cons, List.length_nil]; omega)
                                exact rdRev.reEquivExecutionRevert hcode hdispatch
                                  (uniswapDecode_skim_ok_noncanon hsz36 hcanonTo) hbody
                              · have hz2True : z2 = true := Bool.eq_true_of_not_eq_false hz2False
                                have hcall1True : typedCallViaEVM config evm1S
                                    (EVM.address
                                      (uniswapAddressAtSlot
                                        (uniswapLockEnteredState evmS) ⟨7⟩))
                                    "balanceOf" 0 [.address evm1S.executionEnv.codeOwner]
                                    (true, evm2S, out2) false := by
                                  simpa [hz2True] using hcall1
                                have hstatus :
                                    (if z2 then (⟨1⟩ : UInt256) else ⟨0⟩) ≠ ⟨0⟩ := by
                                  rw [hz2True]
                                  decide
                                obtain ⟨k5291, C5291, rd5291⟩ :=
                                  RD.uniswapSkimSecondBalanceCallSuccessToDecode_dynamic
                                    rd5273 hstatus
                                    (by simp only [List.length_cons, List.length_nil]; omega)
                                by_cases hshort2 : out2.size < 32
                                · have hdec1 : config.externalABI.decode? "balanceOf" out2 = none := by
                                    change uniswapExternalABI.decode? "balanceOf" out2 = none
                                    simpa [uniswapExternalABI, uint256, uint256Int, abiUInt256] using
                                      (decodeReturnValueWithMode_legacy_uint256_none_short
                                        (returndata := out2) hshort2)
                                  have hbody :
                                      ExecTransitionBody config contract evmS (skimStore I)
                                        skimTransition.body .reverted := by
                                    exact uniswapSkimBodyReverts_secondCallDecode
                                      evmS evm0S evm1S evm2S I
                                      (by simp only [evmS, initState]; exact hwv)
                                      hunlockedSolm hguard0 hcall0 hdec0 henoughSource hsafe0
                                      hguard1 hcall1True hdec1
                                  have rdRev :=
                                    RD.uniswapSkimSecondBalanceReturnWordDecodeShortReverts_dynamic
                                      rd5291 ho32 hoSize hout1Empty hout1Sign hshort2 hout2Size
                                      (by simp only [List.length_cons, List.length_nil]; omega)
                                  exact rdRev.reEquivExecutionRevert hcode hdispatch
                                    (uniswapDecode_skim_ok_noncanon hsz36 hcanonTo) hbody
                                · have ho32_2 : 32 ≤ out2.size := not_lt.mp hshort2
                                  let balance1 :=
                                    UInt256.ofNat (fromByteArrayBigEndian (out2.extract 0 32))
                                  have hdec1 :
                                      config.externalABI.decode? "balanceOf" out2 =
                                        some (skimBalanceValue balance1) := by
                                    simpa [balance1] using
                                      uniswapSkimBalanceOfDecode_ok (returndata := out2) ho32_2
                                  let reserve1E :=
                                    UInt256.land reserve112Mask
                                      (UInt256.div (uniswapSlotWord ⟨8⟩ σ1 I) reserve112Shift)
                                  have hsourceReserve1 : uniswapReserve1Word evm2S = reserve1E := by
                                    have h :=
                                      uniswapSkimSecondBalanceStaticReserve1
                                        hPostTransferAccounts1 henv1 hcall1True
                                    simpa [reserve1E, u256_land_comm] using h
                                  obtain ⟨k5314, C5314, rd5314⟩ :=
                                    RD.uniswapSkimSecondBalanceReturnWordDecodeOk_dynamic
                                      rd5291 ho32 hoSize hout1Empty hout1Sign ho32_2 hout2Size
                                      (by simp only [List.length_cons, List.length_nil]; omega)
                                  have hawBalance :=
                                    skimSecondBalanceDynamicStaticcallWords_mload64_ptr_same
                                      out1 hout1Sign
                                  have rd5314' : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
                                      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                                      ⟨5314⟩
                                      (balance1 :: reserve1E :: ⟨5325⟩ :: skimToMaskedWord I ::
                                        token1CleanE :: ⟨5433⟩ ::
                                        token1CleanE :: token0CleanE :: skimToMaskedWord I ::
                                        ⟨570⟩ :: uniswapSelWord I :: [])
                                      (skimSecondBalanceDynamicStaticcallMem
                                        (UInt256.ofNat I.codeOwner.val) o (skimToMaskedWord I)
                                        safeValue0 out1 out2)
                                      (skimSecondBalanceDynamicStaticcallWords out1)
                                      out2 (cA2, σ2) k5314 C5314 := by
                                    simpa [balance1, reserve1E, u256_land_comm, hawBalance] using
                                      rd5314
                                  by_cases hlt1 : balance1.toNat < reserve1E.toNat
                                  · obtain ⟨k6879, C6879, rd6879⟩ :=
                                      RD.uniswapSkimFirstExcessToSub rd5314'
                                        (by simp only [List.length_cons, List.length_nil]; omega)
                                    have rd6879' := by
                                      simpa using rd6879
                                    have rdRev :=
                                      RD.uniswapSafeMathSubUnderflow_dynamic rd6879'
                                        (by simpa [balance1, reserve1E, u256_land_comm] using hlt1)
                                        (by simp only [List.length_cons, List.length_nil]; omega)
                                    have hltSource :
                                        balance1.toNat < (uniswapReserve1Word evm2S).toNat := by
                                      rw [hsourceReserve1]
                                      exact hlt1
                                    have hbody :
                                        ExecTransitionBody config contract evmS (skimStore I)
                                          skimTransition.body .reverted := by
                                      exact uniswapSkimBodyReverts_secondExcessUnderflow
                                        evmS evm0S evm1S evm2S I
                                        (by simp only [evmS, initState]; exact hwv)
                                        hunlockedSolm hguard0 hcall0 hdec0 henoughSource hsafe0
                                        hguard1 hcall1True hdec1 hltSource
                                    exact rdRev.reEquivExecutionRevert hcode hdispatch
                                      (uniswapDecode_skim_ok_noncanon hsz36 hcanonTo) hbody
                                  · have hle1 : reserve1E.toNat ≤ balance1.toNat := not_lt.mp hlt1
                                    obtain ⟨k6879, C6879, rd6879⟩ :=
                                      RD.uniswapSkimFirstExcessToSub rd5314'
                                        (by simp only [List.length_cons, List.length_nil]; omega)
                                    have rd6879' : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
                                        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                                        ⟨6879⟩
                                        (reserve1E :: balance1 :: ⟨5325⟩ :: skimToMaskedWord I ::
                                          token1CleanE :: ⟨5433⟩ ::
                                          token1CleanE :: token0CleanE :: skimToMaskedWord I ::
                                          ⟨570⟩ :: uniswapSelWord I :: [])
                                        (skimSecondBalanceDynamicStaticcallMem
                                          (UInt256.ofNat I.codeOwner.val) o (skimToMaskedWord I)
                                          safeValue0 out1 out2)
                                        (skimSecondBalanceDynamicStaticcallWords out1)
                                        out2 (cA2, σ2) k6879 C6879 := by
                                      simpa using rd6879
                                    obtain ⟨k6370, C6370, rd6370⟩ :=
                                      RD.uniswapSkimExcessSuccessToSafeTransferEntry rd6879' hle1
                                        (by simp only [List.length_cons, List.length_nil]; omega)
                                    let safeValue1 := UInt256.sub balance1 reserve1E
                                    let safeData1 :=
                                      (skimSecondSafeTransferDynamicCallMem2
                                        (UInt256.ofNat I.codeOwner.val) o (skimToMaskedWord I)
                                        safeValue0 out1 out2 safeValue1).readWithPadding
                                        (skimSecondSafeTransferDynamicCallPtr out1).toNat 68
                                    have hdata1 :
                                        transferCalldata? (skimToAddress I)
                                            (skimExcess1Word evm2S balance1) =
                                          some safeData1 := by
                                      have hencoded :=
                                        skimSecondSafeTransferCalldata_masked_dynamic
                                          (evm2S := evm2S) (I := I) (o := o) (out1 := out1)
                                          (out2 := out2) (balance1 := balance1)
                                          (reserve1 := reserve1E) (prevValue := safeValue0)
                                          hsourceReserve1 hle1 ho32 hoSize hout1Empty
                                          hout1Sign ho32_2 hout2Size
                                      simpa [safeData1, safeValue1] using hencoded
                                    have rd6370' : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
                                        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                                        ⟨6370⟩
                                        (safeValue1 :: skimToMaskedWord I :: token1CleanE :: ⟨5433⟩ ::
                                          token1CleanE :: token0CleanE :: skimToMaskedWord I ::
                                          ⟨570⟩ :: uniswapSelWord I :: [])
                                        (skimSecondBalanceDynamicStaticcallMem
                                          (UInt256.ofNat I.codeOwner.val) o (skimToMaskedWord I)
                                          safeValue0 out1 out2)
                                        (skimSecondBalanceDynamicStaticcallWords out1)
                                        out2 (cA2, σ2) k6370 C6370 := by
                                      simpa [safeValue1] using rd6370
                                    obtain ⟨cA3, σ3, z3, out3, A_in3, callGas3, _gasArg3,
                                        k6595b, C6595b, hΘsafe1, rd6595b, hout3Size⟩ :=
                                      RD.uniswapSkimSecondSafeTransferEntryToCallMade_dynamic_offset
                                        rd6370' ho32 hoSize hout1Empty hout1Sign ho32_2
                                        hout2Size hdepth
                                    let evm2E : EVM.State :=
                                      { evm2S with
                                        accountMap := σ2
                                        createdAccounts := cA2
                                        σ₀ := σ₀
                                        genesisBlockHeader := gh
                                        blocks := bl
                                        executionEnv := I }
                                    obtain ⟨g3Ret, A3E, hΘsafeEq1⟩ := hΘsafe1
                                    have hout3Small : out3.size < 2 ^ 138 := by
                                      have htheta :=
                                        Theta_returnData_size_lt_2pow138 I.blobVersionedHashes cA2
                                          ((initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I).genesisBlockHeader)
                                          ((initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I).blocks)
                                          σ2
                                          (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I).σ₀
                                          A_in3
                                          (AccountAddress.ofUInt256
                                            (UInt256.ofNat I.codeOwner.val))
                                          I.sender
                                          (AccountAddress.ofUInt256
                                            (UInt256.land token1CleanE solcAddrMask))
                                          (toExecute σ2
                                            (AccountAddress.ofUInt256
                                              (UInt256.land token1CleanE solcAddrMask)))
                                          callGas3 (UInt256.ofNat I.gasPrice) ⟨0⟩ ⟨0⟩
                                          ((skimSecondSafeTransferDynamicCallMem2
                                            (UInt256.ofNat I.codeOwner.val) o (skimToMaskedWord I)
                                            safeValue0 out1 out2 safeValue1).readWithPadding
                                            (skimSecondSafeTransferDynamicCallPtr out1).toNat 68)
                                          (I.depth + 1) I.header I.perm
                                          (by
                                            exact
                                              Ethereum.EVM.ByteArray.readWithPadding_size_lt_uint256
                                                _ _ _)
                                      rw [← hΘsafeEq1] at htheta
                                      simpa [safeValue1] using htheta
                                    have hcallE1 : callViaEVM evm2E
                                        (AccountAddress.ofUInt256
                                          (UInt256.land token1CleanE solcAddrMask))
                                        0 safeData1
                                        (z3,
                                          { evm2E with
                                            accountMap := σ3
                                            substate := A3E
                                            createdAccounts := cA3 },
                                          out3) := by
                                      refine callViaEVM.callMade (perm := true) (g' := g3Ret)
                                        wordOfInt_zero.symm ?_ rfl ?_ ?_
                                      · refine ⟨callGas3, A_in3, ?_⟩
                                        simpa [evm2E, safeData1, safeValue1, hperm,
                                          accountAddress_roundtrip] using hΘsafeEq1
                                      · show (⟨0⟩ : UInt256) ≤ _
                                        exact Fin.zero_le _
                                      · intro hdepthEq
                                        have hdepthLt : I.depth.val < 1024 := hdepth
                                        rw [show evm2E.executionEnv.depth = I.depth by simp [evm2E]]
                                          at hdepthEq
                                        rw [hdepthEq] at hdepthLt
                                        exact absurd hdepthLt (by decide)
                                    obtain ⟨σ3S, A3S, htransfer1Raw, hPostTransferAccounts2⟩ :=
                                      callViaEVM_accountMapEquiv (storage := config.storage)
                                        (evm_evm := evm2E) (evm_solm := evm2S)
                                        hcallE1 hPost2
                                        (by simp [evm2E, hσ2])
                                        (by simp [evm2E, hcreated2])
                                        (by simp [evm2E, hgenesis2])
                                        (by simp [evm2E, hblocks2])
                                        (by simp [evm2E])
                                        (by simp [evm2E, henv2, henv1])
                                    let evm3S : EVM.State :=
                                      { evm2S with
                                        accountMap := σ3S
                                        substate := A3S
                                        createdAccounts := cA3 }
                                    have htransfer1Raw' : callViaEVM evm2S
                                        (AccountAddress.ofUInt256
                                          (UInt256.land token1CleanE solcAddrMask))
                                        0 safeData1 (z3, evm3S, out3) := by
                                      simpa [evm3S] using htransfer1Raw
                                    have htransfer1Target :
                                        AccountAddress.ofUInt256
                                            (UInt256.land token1CleanE solcAddrMask) =
                                          EVM.address
                                            (uniswapAddressAtSlot
                                              (uniswapLockEnteredState evmS) ⟨7⟩) := by
                                      rw [htarget1]
                                      exact (uniswapAddress_self
                                        (uniswapAddressAtSlot
                                          (uniswapLockEnteredState evmS) ⟨7⟩)).symm
                                    have htransfer1 : callViaEVM evm2S
                                        (EVM.address
                                          (uniswapAddressAtSlot
                                            (uniswapLockEnteredState evmS) ⟨7⟩))
                                        0 safeData1 (z3, evm3S, out3) := by
                                      simpa [htransfer1Target] using htransfer1Raw'
                                    have hPostTransferAccounts3 :
                                        accountMapEquiv σ3 evm3S.accountMap := by
                                      simpa [evm3S] using hPostTransferAccounts2
                                    have henv3 : evm3S.executionEnv = I := by
                                      simpa [evm3S] using henv2.trans henv1
                                    have henough1Source :
                                        (uniswapReserve1Word evm2S).toNat ≤ balance1.toNat := by
                                      rw [hsourceReserve1]
                                      exact hle1
                                    have hfinish :
                                        ∀ {mem outRet : ByteArray} {aw : UInt256} {kR CR : ℕ},
                                          RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
                                            (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                                            ⟨5433⟩
                                            (token1CleanE :: token0CleanE :: skimToMaskedWord I ::
                                              ⟨570⟩ :: uniswapSelWord I :: [])
                                            mem aw outRet (cA3, σ3) kR CR →
                                          ExecStmt config
                                            { contract := contract,
                                              locals :=
                                                skimSecondExcessStore evmS evm0S evm2S I
                                                  balance0 balance1 } evm2S
                                            (.internalCall "_safeTransfer"
                                              [.var "_token1", .var "to", .var "excess1"] "ok1")
                                            (.ok
                                              { contract := contract,
                                                locals :=
                                                  skimSecondSafeTransferStore evmS evm0S evm2S I
                                                    balance0 balance1 }
                                              evm3S) →
                                          runtimeEquivalenceFor config contract cA gh bl σ_evm
                                            σ_solm σ₀ g A I := by
                                      intro mem outRet aw kR CR rd5433 hsafe1
                                      have rdRet :=
                                        RD.uniswapSkimAfterSecondSafeTransferToReturn rd5433 hperm
                                      have hbody :
                                          ExecTransitionBody config contract evmS (skimStore I)
                                            skimTransition.body
                                            (.returned
                                              { contract := contract,
                                                locals :=
                                                  skimSecondSafeTransferStore evmS evm0S evm2S I
                                                    balance0 balance1 }
                                              (uniswapLockExitedState evm3S) none) := by
                                        exact uniswapSkimBodyReturns
                                          evmS evm0S evm1S evm2S evm3S I
                                          (by simp only [evmS, initState]; exact hwv)
                                          hunlockedSolm hguard0 hcall0 hdec0 henoughSource hsafe0
                                          hguard1 hcall1True hdec1 henough1Source hsafe1
                                      have hCreatedRet :
                                          cA3 = (uniswapLockExitedState evm3S).createdAccounts := by
                                        simp [uniswapLockExitedState, uniswapUnlockedState, evm3S,
                                          storageStore_createdAccounts]
                                      have hAccountsRet :
                                          accountMapEquiv
                                            (sstoreAccountMap I.codeOwner σ3 ⟨12⟩ ⟨1⟩)
                                            (uniswapLockExitedState evm3S).accountMap := by
                                        have hs :=
                                          accountMapEquiv_sstoreAccountMap I.codeOwner ⟨12⟩ ⟨1⟩
                                            hPostTransferAccounts3
                                        simpa [uniswapLockExitedState, uniswapUnlockedState,
                                          storageStore_accountMap, henv3] using hs
                                      exact rdRet.reEquivExecutionGenAccountMapEquiv hcode hdispatch
                                        (uniswapDecode_skim_ok_noncanon hsz36 hcanonTo) hbody hCreatedRet
                                        hAccountsRet (returnEquiv.void rfl rfl rfl)
                                    by_cases hz3False : z3 = false
                                    · have htransfer1False : callViaEVM evm2S
                                          (EVM.address
                                            (uniswapAddressAtSlot
                                              (uniswapLockEnteredState evmS) ⟨7⟩))
                                          0 safeData1 (false, evm3S, out3) := by
                                        simpa [hz3False] using htransfer1
                                      have hbody :
                                          ExecTransitionBody config contract evmS (skimStore I)
                                            skimTransition.body .reverted := by
                                        exact uniswapSkimBodyReverts_secondSafeTransferFailure
                                          evmS evm0S evm1S evm2S evm3S I
                                          (by simp only [evmS, initState]; exact hwv)
                                          hunlockedSolm hguard0 hcall0 hdec0 henoughSource hsafe0
                                          hguard1 hcall1True hdec1 henough1Source hdata1
                                          htransfer1False
                                      have rd6595False : RD uniswapV2PairBytecode I
                                          (Sat256.ofUInt256 g)
                                          (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                                          ⟨6595⟩
                                          (⟨0⟩ :: skimSecondSafeTransferDynamicRetEnd out1 ::
                                            UInt256.land token1CleanE solcAddrMask :: ⟨96⟩ :: ⟨0⟩ ::
                                            safeValue1 :: skimToMaskedWord I :: token1CleanE :: ⟨5433⟩ ::
                                            token1CleanE :: token0CleanE :: skimToMaskedWord I ::
                                            ⟨570⟩ :: uniswapSelWord I :: [])
                                          (skimSecondSafeTransferDynamicCallMem2
                                            (UInt256.ofNat I.codeOwner.val) o (skimToMaskedWord I)
                                            safeValue0 out1 out2 safeValue1)
                                          (skimSecondSafeTransferDynamicWordsCall2 out1) out3
                                          (cA3, σ3) k6595b C6595b := by
                                        simpa [hz3False, safeValue1] using rd6595b
                                      by_cases hout3Empty : out3.size = 0
                                      · have rdRev :=
                                          RD.uniswapSkimSecondSafeTransferEmptyFailureReverts_dynamic_offset
                                            rd6595False hout3Empty
                                        exact rdRev.reEquivExecutionRevert hcode hdispatch
                                          (uniswapDecode_skim_ok_noncanon hsz36 hcanonTo) hbody
                                      · by_cases hout3Sign : out3.size < 2 ^ 255
                                        · have rdRev :=
                                            RD.uniswapSkimSecondSafeTransferNonemptyFailureReverts_dynamic_offset
                                              rd6595False hout3Empty hout3Sign ho32 hoSize
                                              hout1Empty hout1Sign ho32_2 hout2Size
                                          exact rdRev.reEquivExecutionRevert hcode hdispatch
                                            (uniswapDecode_skim_ok_noncanon hsz36 hcanonTo) hbody
                                        · have : out3.size < 2 ^ 255 := by
                                            exact lt_trans hout3Small (by norm_num)
                                          exact False.elim (hout3Sign this)
                                    · have hz3True : z3 = true := Bool.eq_true_of_not_eq_false hz3False
                                      have htransfer1True : callViaEVM evm2S
                                          (EVM.address
                                            (uniswapAddressAtSlot
                                              (uniswapLockEnteredState evmS) ⟨7⟩))
                                          0 safeData1 (true, evm3S, out3) := by
                                        simpa [hz3True] using htransfer1
                                      have rd6595True : RD uniswapV2PairBytecode I
                                          (Sat256.ofUInt256 g)
                                          (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
                                          ⟨6595⟩
                                          (⟨1⟩ :: skimSecondSafeTransferDynamicRetEnd out1 ::
                                            UInt256.land token1CleanE solcAddrMask :: ⟨96⟩ :: ⟨0⟩ ::
                                            safeValue1 :: skimToMaskedWord I :: token1CleanE :: ⟨5433⟩ ::
                                            token1CleanE :: token0CleanE :: skimToMaskedWord I ::
                                            ⟨570⟩ :: uniswapSelWord I :: [])
                                          (skimSecondSafeTransferDynamicCallMem2
                                            (UInt256.ofNat I.codeOwner.val) o (skimToMaskedWord I)
                                            safeValue0 out1 out2 safeValue1)
                                          (skimSecondSafeTransferDynamicWordsCall2 out1) out3
                                          (cA3, σ3) k6595b C6595b := by
                                        simpa [hz3True, safeValue1] using rd6595b
                                      by_cases hout3Empty : out3.size = 0
                                      · have hsafe1 :
                                            ExecStmt config
                                              { contract := contract,
                                                locals :=
                                                  skimSecondExcessStore evmS evm0S evm2S I
                                                    balance0 balance1 } evm2S
                                              (.internalCall "_safeTransfer"
                                                [.var "_token1", .var "to", .var "excess1"] "ok1")
                                              (.ok
                                                { contract := contract,
                                                  locals :=
                                                    skimSecondSafeTransferStore evmS evm0S evm2S I
                                                      balance0 balance1 }
                                                evm3S) := by
                                          have hs := safeTransferInternalCallReturns_empty
                                            (caller :=
                                              { contract := contract,
                                                locals :=
                                                  skimSecondExcessStore evmS evm0S evm2S I
                                                    balance0 balance1 })
                                            (evm := evm2S) (evm' := evm3S)
                                            (tokenExpr := .var "_token1") (toExpr := .var "to")
                                            (valueExpr := .var "excess1") (retVar := "ok1")
                                            (token :=
                                              uniswapAddressAtSlot
                                                (uniswapLockEnteredState evmS) ⟨7⟩)
                                            (recipient := skimToAddress I)
                                            (value := skimExcess1Word evm2S balance1)
                                            (calldata := safeData1) (out := out3)
                                            rfl
                                            (evalExprs_skim_safeTransfer1_args
                                              evmS evm0S evm2S I balance0 balance1)
                                            hdata1 htransfer1True hout3Empty
                                          simpa [resumeAfterInternalCall, skimSecondSafeTransferStore]
                                            using hs
                                        obtain ⟨k5433, C5433, rd5433⟩ :=
                                          RD.uniswapSkimSecondSafeTransferEmptyReturnTo5433_dynamic_offset
                                            rd6595True hout3Empty ho32 hoSize hout1Empty
                                            hout1Sign ho32_2 hout2Size
                                        exact hfinish rd5433 hsafe1
                                      · by_cases hout3Sign : out3.size < 2 ^ 255
                                        · by_cases hshort3 : out3.size < 32
                                          · have hdecSafe1 :
                                                ABI.decodeReturnValueWithMode?
                                                    config.abiDecodeMode boolTy out3 =
                                                  none := by
                                              change
                                                ABI.decodeReturnValueWithMode?
                                                    DecodeMode.legacySolc05 boolTy out3 =
                                                  none
                                              exact decodeReturnValueWithMode_legacy_bool_none_short
                                                (returndata := out3) hshort3
                                            have hbody :
                                                ExecTransitionBody config contract evmS (skimStore I)
                                                  skimTransition.body .reverted := by
                                              exact uniswapSkimBodyReverts_secondSafeTransferDecode
                                                evmS evm0S evm1S evm2S evm3S I
                                                (by simp only [evmS, initState]; exact hwv)
                                                hunlockedSolm hguard0 hcall0 hdec0 henoughSource hsafe0
                                                hguard1 hcall1True hdec1 henough1Source hdata1
                                                htransfer1True hout3Empty hdecSafe1
                                            have rdRev :=
                                              RD.uniswapSkimSecondSafeTransferNonemptyShortReverts_dynamic_offset
                                                rd6595True hout3Empty hshort3 hout3Sign hout3Small
                                                ho32 hoSize hout1Empty hout1Sign hout1Small
                                                ho32_2 hout2Size
                                            exact rdRev.reEquivExecutionRevert hcode hdispatch
                                              (uniswapDecode_skim_ok_noncanon hsz36 hcanonTo) hbody
                                          · have hout332 : 32 ≤ out3.size := not_lt.mp hshort3
                                            let safeWord1 :=
                                              UInt256.ofNat
                                                (fromByteArrayBigEndian (out3.extract 0 32))
                                            by_cases hword1 : safeWord1 = ⟨0⟩
                                            · have hdecSafe1 :
                                                  ABI.decodeReturnValueWithMode?
                                                      config.abiDecodeMode boolTy out3 =
                                                    some (.bool false) := by
                                                change
                                                  ABI.decodeReturnValueWithMode?
                                                      DecodeMode.legacySolc05 boolTy out3 =
                                                    some (.bool false)
                                                exact decodeReturnValueWithMode_legacy_bool_false
                                                  (returndata := out3) hout332 hout3Sign hword1
                                              have hbody :
                                                  ExecTransitionBody config contract evmS (skimStore I)
                                                    skimTransition.body .reverted := by
                                                exact uniswapSkimBodyReverts_secondSafeTransferDecodeFalse
                                                  evmS evm0S evm1S evm2S evm3S I
                                                  (by simp only [evmS, initState]; exact hwv)
                                                  hunlockedSolm hguard0 hcall0 hdec0 henoughSource hsafe0
                                                  hguard1 hcall1True hdec1 henough1Source hdata1
                                                  htransfer1True hout3Empty hdecSafe1
                                              have rdRev :=
                                                RD.uniswapSkimSecondSafeTransferNonemptyFalseReverts_dynamic_offset
                                                  rd6595True hout3Empty hout332 hout3Sign hout3Small
                                                  hword1 ho32 hoSize hout1Empty hout1Sign
                                                  hout1Small ho32_2 hout2Size
                                              exact rdRev.reEquivExecutionRevert hcode hdispatch
                                                (uniswapDecode_skim_ok_noncanon hsz36 hcanonTo) hbody
                                            · have hdecSafe1 :
                                                  ABI.decodeReturnValueWithMode?
                                                      config.abiDecodeMode boolTy out3 =
                                                    some (.bool true) := by
                                                change
                                                  ABI.decodeReturnValueWithMode?
                                                      DecodeMode.legacySolc05 boolTy out3 =
                                                    some (.bool true)
                                                exact decodeReturnValueWithMode_legacy_bool_true
                                                  (returndata := out3) hout332 hout3Sign hword1
                                              have hsafe1 :
                                                  ExecStmt config
                                                    { contract := contract,
                                                      locals :=
                                                        skimSecondExcessStore evmS evm0S evm2S I
                                                          balance0 balance1 } evm2S
                                                    (.internalCall "_safeTransfer"
                                                      [.var "_token1", .var "to", .var "excess1"]
                                                      "ok1")
                                                    (.ok
                                                      { contract := contract,
                                                        locals :=
                                                          skimSecondSafeTransferStore evmS evm0S evm2S I
                                                            balance0 balance1 }
                                                      evm3S) := by
                                                have hs := safeTransferInternalCallReturns_decodeTrue
                                                  (caller :=
                                                    { contract := contract,
                                                      locals :=
                                                        skimSecondExcessStore evmS evm0S evm2S I
                                                          balance0 balance1 })
                                                  (evm := evm2S) (evm' := evm3S)
                                                  (tokenExpr := .var "_token1") (toExpr := .var "to")
                                                  (valueExpr := .var "excess1") (retVar := "ok1")
                                                  (token :=
                                                    uniswapAddressAtSlot
                                                      (uniswapLockEnteredState evmS) ⟨7⟩)
                                                  (recipient := skimToAddress I)
                                                  (value := skimExcess1Word evm2S balance1)
                                                  (calldata := safeData1) (out := out3)
                                                  rfl
                                                  (evalExprs_skim_safeTransfer1_args
                                                    evmS evm0S evm2S I balance0 balance1)
                                                  hdata1 htransfer1True hout3Empty hdecSafe1
                                                simpa [resumeAfterInternalCall,
                                                  skimSecondSafeTransferStore] using hs
                                              obtain ⟨k5433, C5433, rd5433⟩ :=
                                                RD.uniswapSkimSecondSafeTransferNonemptyTrueToRet_dynamic_offset
                                                  rd6595True hout3Empty hout332 hout3Sign
                                                  hout3Small hword1 ho32 hoSize hout1Empty
                                                  hout1Sign hout1Small ho32_2 hout2Size
                                                  (by jump_dest)
                                              exact hfinish rd5433 hsafe1
                                        · have : out3.size < 2 ^ 255 := by
                                            exact lt_trans hout3Small (by norm_num)
                                          exact False.elim (hout3Sign this)
                      · have hhi : 2 ^ 255 ≤ out1.size := le_of_not_gt hout1Sign
                        have hdecSafe0 :
                            ABI.decodeReturnValueWithMode? config.abiDecodeMode boolTy out1 =
                              none := by
                          change
                            ABI.decodeReturnValueWithMode? DecodeMode.legacySolc05 boolTy out1 =
                              none
                          exact decodeReturnValueWithMode_legacy_bool_none_huge
                            (returndata := out1) hhi
                        have hbody :
                            ExecTransitionBody config contract evmS (skimStore I)
                              skimTransition.body .reverted := by
                          exact uniswapSkimBodyReverts_firstSafeTransferDecode
                            evmS evm0S evm1S I
                            (by simp only [evmS, initState]; exact hwv)
                            hunlockedSolm hguard0 hcall0 hdec0 henoughSource hdata0
                            htransferTrue hout1Empty hdecSafe0
                        have rdRev :=
                          RD.uniswapSkimSafeTransferNonemptyHugeReverts
                            rd6595True hout1Empty hhi hout1Size ho32 hoSize
                        exact rdRev.reEquivExecutionRevert hcode hdispatch
                          (uniswapDecode_skim_ok_noncanon hsz36 hcanonTo) hbody

          · rw [not_lt] at hdepth
            have hdepth1024 : I.depth = 1024 := Fin.ext (by have := I.depth.isLt; omega)
            exact uniswapSkimBodyCoreRevert_firstCallDepth_masked hcode hsize hperm hwv hsel
              hsz36 hdepth1024 hunlocked htoken0NoCode hdispatch
              (uniswapDecode_skim_ok_noncanon hsz36 hcanonTo) hAccounts
  · exact uniswapSkimBodyDecodeFailed_short hcode hsize hwv hsel (by omega) hdispatch
end UniswapV2Pair
