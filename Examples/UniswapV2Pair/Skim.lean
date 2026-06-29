import Examples.UniswapV2Pair.SkimRuntime
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
        (z, evm0S, o) false := by
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
  refine ⟨evm0S, ?_⟩
  simpa [evm0S, htargetSource, evmEL, evmSL, evmE, evmS,
    uniswapLockEnteredState, uniswapUnlockedState, initState,
    storageStore_executionEnv] using hcallSolm

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
          · obtain ⟨cA', σ', z, o, A_in, callGas, hΘ, hrev, hrevShort, _hoSize⟩ :=
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
              · obtain ⟨evm0S, hcallAll⟩ :=
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
                have hzTrue : z = true := by
                  cases z <;> simp at hz ⊢
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
              · sorry
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
          · obtain ⟨cA', σ', z, o, A_in, callGas, hΘ, hrev, hrevShort, _hoSize⟩ :=
                uniswapSkimRuntimeFirstBalanceOfStaticcallFailureGuard_masked
                  (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
                  (A := A) (I := I) (g := g)
                hcode hsize hwv hsel hsz36 hperm hdepth hunlocked htoken0NoCode
            obtain ⟨evm0S, hcallAll⟩ :=
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
              · have hzTrue : z = true := by
                  cases z <;> simp at hz ⊢
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
              · sorry
          · rw [not_lt] at hdepth
            have hdepth1024 : I.depth = 1024 := Fin.ext (by have := I.depth.isLt; omega)
            exact uniswapSkimBodyCoreRevert_firstCallDepth_masked hcode hsize hperm hwv hsel
              hsz36 hdepth1024 hunlocked htoken0NoCode hdispatch
              (uniswapDecode_skim_ok_noncanon hsz36 hcanonTo) hAccounts
  · exact uniswapSkimBodyDecodeFailed_short hcode hsize hwv hsel (by omega) hdispatch
end UniswapV2Pair
