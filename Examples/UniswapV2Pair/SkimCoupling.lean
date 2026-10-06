import Reasoning.StateFacts
import Reasoning.WordArithmetic
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
    {σ1 σ₀ I} {evm1S : EVM.State}
    {σ2 : AccountMap} {z2 : Bool} {out2 calldataMem : ByteArray} {A_in2 : Substate}
    {callGas2 targetWord inOff : UInt256}
    (hPost : σ1 = evm1S.accountMap)
    (hσ0 : evm1S.σ₀ = σ₀)
    (henv : evm1S.executionEnv = I)
    (hdepth : I.depth.val < 1024)
    (hcd : config.externalABI.encode? "balanceOf" [.address I.codeOwner] =
      some (calldataMem.readWithPadding inOff.toNat 36))
    (hΘ : ∃ (g'' : UInt256) (A'_evm : Substate),
      (σ2, g'', A'_evm, z2, out2) =
        Ethereum.EVM.Θ σ1 σ₀ A_in2
          (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner.val)) I.sender
          (AccountAddress.ofUInt256 targetWord)
          (toExecute σ1 (AccountAddress.ofUInt256 targetWord))
          callGas2 (UInt256.ofNat I.gasPrice) ⟨0⟩ ⟨0⟩
          (calldataMem.readWithPadding inOff.toNat 36)
          (I.depth + 1) I.header I.blobVersionedHashes I.blocks false) :
    ∃ evm2S : EVM.State,
      typedCallViaEVM config evm1S (AccountAddress.ofUInt256 targetWord)
        "balanceOf" 0 [.address evm1S.executionEnv.codeOwner] (z2, evm2S, out2) false ∧
      σ2 = evm2S.accountMap ∧ evm2S.σ₀ = σ₀ ∧ evm2S.executionEnv = I := by
  obtain ⟨g'', A'_evm, hΘeq⟩ := hΘ
  let evmE : EVM.State := { evm1S with accountMap := σ1, σ₀ := σ₀, executionEnv := I }
  let target : EVM.Address := AccountAddress.ofUInt256 targetWord
  have hdepthNe : evmE.executionEnv.depth ≠ ⟨1024, by decide⟩ := by
    intro hEq
    have hlt : evmE.executionEnv.depth.val < 1024 := by simpa [evmE] using hdepth
    have hval : evmE.executionEnv.depth.val = 1024 := by
      exact congrArg Fin.val hEq
    omega
  have hcdE : config.externalABI.encode? "balanceOf" [.address evmE.executionEnv.codeOwner] =
      some (calldataMem.readWithPadding inOff.toNat 36) := by
    simpa [evmE] using hcd
  have hΘE : (σ2, g'', A'_evm, z2, out2) =
      Ethereum.EVM.Θ evmE.accountMap evmE.σ₀ A_in2
        (AccountAddress.ofUInt256 (UInt256.ofNat evmE.executionEnv.codeOwner.val))
        evmE.executionEnv.sender target (toExecute evmE.accountMap target)
        callGas2 (UInt256.ofNat evmE.executionEnv.gasPrice) ⟨0⟩ ⟨0⟩
        (calldataMem.readWithPadding inOff.toNat 36)
        (evmE.executionEnv.depth + 1) evmE.executionEnv.header
        evmE.executionEnv.blobVersionedHashes evmE.executionEnv.blocks false := by
    simpa [evmE, target] using hΘeq
  obtain ⟨σ2S, A2S, hcallSolm, hPost2⟩ :=
    typedCallViaEVM_callMade_sameInputs
      (cfg := config) (evm_evm := evmE) (evm_solm := evm1S)
      (tgt := target) (targetWord := targetWord) (name := "balanceOf")
      (args := [.address evmE.executionEnv.codeOwner])
      (σ' := σ2) (A' := A'_evm) (A_in := A_in2) (z := z2) (out := out2)
      (g'' := g'') (callGas := callGas2) (mem := calldataMem) (inOff := inOff)
      (inSize := ⟨36⟩) (callPerm := false)
      hdepthNe rfl hcdE hΘE (by simpa [evmE] using hPost)
      (by simp [evmE, hσ0]) (by simp [evmE, henv])
  let evm2S : EVM.State := { evm1S with accountMap := σ2S, substate := A2S }
  refine ⟨evm2S, ?_, ?_, ?_, ?_⟩
  · simpa [evm2S, target, evmE, henv] using hcallSolm
  · simpa [evm2S] using hPost2
  · simp [evm2S, hσ0]
  · simp [evm2S, henv]

theorem uniswapSkimFirstBalanceTypedCall_source
    {σ σ₀ A I} {g : UInt256} {σ' : AccountMap}
    {z : Bool} {o : ByteArray} {A_in : Substate} {callGas : UInt256}
    (hdepth : I.depth.val < 1024)
    (hΘ : ∃ (g'' : UInt256) (A'_evm : Substate),
      (σ', g'', A'_evm, z, o) = Ethereum.EVM.Θ
        (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) σ₀ A_in
        (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner.val)) I.sender
        (AccountAddress.ofUInt256 (UInt256.land solcAddrMask
          (solcSlotWordAt ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I)))
        (toExecute (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩)
          (AccountAddress.ofUInt256 (UInt256.land solcAddrMask
            (solcSlotWordAt ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I))))
        callGas (UInt256.ofNat I.gasPrice) ⟨0⟩ ⟨0⟩
        ((balanceOfThisCalldataMem (UInt256.ofNat I.codeOwner.val)).readWithPadding 128 36)
        (I.depth + 1) I.header I.blobVersionedHashes I.blocks false) :
    ∃ evm0S : EVM.State,
      typedCallViaEVM config
        (uniswapLockEnteredState (initState σ σ₀ (Sat256.ofUInt256 g) A I))
        (EVM.address (uniswapAddressAtSlot
          (uniswapLockEnteredState (initState σ σ₀ (Sat256.ofUInt256 g) A I)) ⟨6⟩))
        "balanceOf" 0
        [.address (uniswapLockEnteredState
          (initState σ σ₀ (Sat256.ofUInt256 g) A I)).executionEnv.codeOwner]
        (z, evm0S, o) false ∧
      σ' = evm0S.accountMap ∧ evm0S.σ₀ = σ₀ ∧
      evm0S.executionEnv =
        (uniswapLockEnteredState (initState σ σ₀ (Sat256.ofUInt256 g) A I)).executionEnv := by
  let evmS := initState σ σ₀ (Sat256.ofUInt256 g) A I
  let evmSL := uniswapLockEnteredState evmS
  let σLock := sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩
  let token0Word := solcSlotWordAt ⟨6⟩ σLock I
  let token0Clean := UInt256.land solcAddrMask token0Word
  let target : EVM.Address := AccountAddress.ofUInt256 token0Clean
  have hLockState : σLock = evmSL.accountMap := by
    simp [σLock, evmSL, evmS, uniswapLockEnteredState, uniswapUnlockedState,
      initState, storageStore_accountMap]
  have htargetSource : target = EVM.address (uniswapAddressAtSlot evmSL ⟨6⟩) := by
    have haddr : AccountAddress.ofUInt256 token0Clean = uniswapAddressAtSlot evmSL ⟨6⟩ := by
      simpa [target, token0Clean, token0Word, σLock, evmSL, evmS,
        uniswapLockEnteredState, uniswapUnlockedState, initState, storageStore_accountMap,
        storageStore_executionEnv, State.lookupAccount, Account.lookupStorage,
        Solm.EVM.storageLoad, uniswapAddressAtSlot, solcSlotWordAt, solcSlotWord,
        accountAddress_ofUInt256_eq_ofNat_toNat, u256_land_comm]
    change AccountAddress.ofUInt256 token0Clean =
      EVM.address (uniswapAddressAtSlot evmSL ⟨6⟩)
    rw [haddr]
    exact (address_of_val (uniswapAddressAtSlot evmSL ⟨6⟩)).symm
  have hcd : config.externalABI.encode? "balanceOf" [.address I.codeOwner] =
      some ((balanceOfThisCalldataMem (UInt256.ofNat I.codeOwner.val)).readWithPadding 128 36) :=
    balanceOfThisCalldataMem_encode I.codeOwner
  obtain ⟨evm0S, hcall, hMap, hσ0, henv⟩ :=
    uniswapSkimBalanceTypedCallFromState_source
      (σ1 := σLock) (σ₀ := σ₀) (I := I) (evm1S := evmSL) (σ2 := σ')
      (z2 := z) (out2 := o) (A_in2 := A_in) (callGas2 := callGas)
      (targetWord := token0Clean)
      (calldataMem := balanceOfThisCalldataMem (UInt256.ofNat I.codeOwner.val))
      (inOff := ⟨128⟩) (hPost := hLockState)
      (hσ0 := by simpa [evmSL, evmS, uniswapLockEnteredState,
        uniswapUnlockedState, initState] using
        (storageStore_σ0 evmS I.codeOwner ⟨12⟩ ⟨0⟩))
      (henv := by simp [evmSL, evmS, uniswapLockEnteredState,
        uniswapUnlockedState, initState, storageStore_executionEnv])
      (hdepth := hdepth) (hcd := hcd) (hΘ := hΘ)
  refine ⟨evm0S, ?_, hMap, hσ0, ?_⟩
  · rw [← htargetSource]
    exact hcall
  · simpa [evmSL, evmS, uniswapLockEnteredState, uniswapUnlockedState, initState,
      storageStore_executionEnv] using henv

theorem uniswapSkimFirstBalanceReturn_source
    {σ σ₀ A I} {g : UInt256} {σ' : AccountMap}
    {z : Bool} {o : ByteArray} {A_in : Substate} {callGas : UInt256}
    (hdepth : I.depth.val < 1024)
    (hΘ : ∃ (g'' : UInt256) (A'_evm : Substate),
      (σ', g'', A'_evm, z, o) = Ethereum.EVM.Θ
        (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) σ₀ A_in
        (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner.val)) I.sender
        (AccountAddress.ofUInt256 (UInt256.land solcAddrMask
          (solcSlotWordAt ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I)))
        (toExecute (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩)
          (AccountAddress.ofUInt256 (UInt256.land solcAddrMask
            (solcSlotWordAt ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I))))
        callGas (UInt256.ofNat I.gasPrice) ⟨0⟩ ⟨0⟩
        ((balanceOfThisCalldataMem (UInt256.ofNat I.codeOwner.val)).readWithPadding 128 36)
        (I.depth + 1) I.header I.blobVersionedHashes I.blocks false)
    (hz : z = true) (ho32 : 32 ≤ o.size) :
    ∃ (evm0S : EVM.State) (balance0 : UInt256),
      typedCallViaEVM config
        (uniswapLockEnteredState (initState σ σ₀ (Sat256.ofUInt256 g) A I))
        (EVM.address (uniswapAddressAtSlot
          (uniswapLockEnteredState (initState σ σ₀ (Sat256.ofUInt256 g) A I)) ⟨6⟩))
        "balanceOf" 0 [.address (uniswapLockEnteredState
          (initState σ σ₀ (Sat256.ofUInt256 g) A I)).executionEnv.codeOwner]
        (true, evm0S, o) false ∧
      config.externalABI.decode? "balanceOf" o = some [skimBalanceValue balance0] ∧
      σ' = evm0S.accountMap ∧ evm0S.σ₀ = σ₀ ∧
      evm0S.executionEnv =
        (uniswapLockEnteredState (initState σ σ₀ (Sat256.ofUInt256 g) A I)).executionEnv ∧
      uniswapReserve0Word evm0S = UInt256.land (solcSlotWordAt ⟨8⟩ σ' I) reserve112Mask ∧
      balance0 = UInt256.ofNat (fromByteArrayBigEndian (o.extract 0 32)) := by
  obtain ⟨evm0S, hcallAll, hMap, hσ0, henv⟩ :=
    uniswapSkimFirstBalanceTypedCall_source hdepth hΘ
  let evmS := initState σ σ₀ (Sat256.ofUInt256 g) A I
  let balance0 := UInt256.ofNat (fromByteArrayBigEndian (o.extract 0 32))
  have hcall0 : typedCallViaEVM config (uniswapLockEnteredState evmS)
      (EVM.address (uniswapAddressAtSlot (uniswapLockEnteredState evmS) ⟨6⟩))
      "balanceOf" 0 [.address (uniswapLockEnteredState evmS).executionEnv.codeOwner]
      (true, evm0S, o) false := by
    simpa [evmS, hz] using hcallAll
  have hdecode : config.externalABI.decode? "balanceOf" o = some [skimBalanceValue balance0] := by
    simpa [balance0] using uniswapSkimBalanceOfDecode_ok (returndata := o) ho32
  have howner : evm0S.executionEnv.codeOwner = I.codeOwner := by
    have henvCall := typedCallViaEVM_executionEnv_eq hcall0
    have henvInit : (uniswapLockEnteredState evmS).executionEnv = I := by
      simp [evmS, uniswapLockEnteredState, uniswapUnlockedState, initState,
        storageStore_executionEnv]
    exact congrArg ExecutionEnv.codeOwner (henvCall.trans henvInit)
  have hreserve : uniswapReserve0Word evm0S =
      UInt256.land (solcSlotWordAt ⟨8⟩ σ' I) reserve112Mask := by
    rw [hMap]
    simp [uniswapReserve0Word, Solm.EVM.storageLoad, State.lookupAccount,
      Account.lookupStorage, solcSlotWordAt, solcSlotWord, howner, uniswapLockEnteredState,
      uniswapUnlockedState, initState, storageStore_executionEnv]
  exact ⟨evm0S, balance0, hcall0, hdecode, hMap, hσ0, by simpa [evmS] using henv,
    hreserve, rfl⟩

theorem uniswapSkimFirstBalanceStaticReserve0
    {σ σ₀ A I} {g : UInt256}
    {evm0S : EVM.State} {target : EVM.Address} {name : Ident}
    {args : List Value} {out0 : ByteArray} {z : Bool}
    (hcall0 : typedCallViaEVM config
      (uniswapLockEnteredState
        (initState σ σ₀ (Sat256.ofUInt256 g) A I))
      target name 0 args (z, evm0S, out0) false) :
    uniswapReserve0Word evm0S =
      UInt256.land
        (solcSlotWordAt ⟨8⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I)
        reserve112Mask := by
  let evmS := initState σ σ₀ (Sat256.ofUInt256 g) A I
  let evmL := uniswapLockEnteredState evmS
  let σLockE := sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩
  have hLockStateAccounts : σLockE = evmL.accountMap := by
    simpa [evmL, evmS, σLockE, uniswapLockEnteredState, uniswapUnlockedState, initState,
      storageStore_accountMap]
  have hslot :=
    typedCallViaEVM_static_storage_getD_of_accounts_eq
      (cfg := config) (σ := σLockE) (evm := evmL) (evm' := evm0S)
      (slot := ⟨8⟩) (default := ⟨0⟩) hLockStateAccounts hcall0
  simpa [uniswapReserve0Word, Solm.EVM.storageLoad, State.lookupAccount,
      Account.lookupStorage, solcSlotWordAt, solcSlotWord, σLockE, evmL, evmS,
    uniswapLockEnteredState, uniswapUnlockedState, initState, storageStore_executionEnv] using
    congrArg (fun w => UInt256.land w reserve112Mask) hslot

theorem uniswapSkimSecondBalanceTypedCall_source
    {σ1 σ₀ I} {evm1S : EVM.State} {σ2 : AccountMap}
    {z2 : Bool} {out2 : ByteArray} {A_in2 : Substate} {callGas2 : UInt256}
    {o : ByteArray} {toWord value token1 : UInt256}
    (hPost : σ1 = evm1S.accountMap) (hσ0 : evm1S.σ₀ = σ₀)
    (henv : evm1S.executionEnv = I) (hdepth : I.depth.val < 1024)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hΘ : ∃ (g'' : UInt256) (A'_evm : Substate),
      (σ2, g'', A'_evm, z2, out2) = Ethereum.EVM.Θ σ1 σ₀ A_in2
        (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner.val)) I.sender
        (AccountAddress.ofUInt256 (UInt256.land token1 solcAddrMask))
        (toExecute σ1 (AccountAddress.ofUInt256 (UInt256.land token1 solcAddrMask)))
        callGas2 (UInt256.ofNat I.gasPrice) ⟨0⟩ ⟨0⟩
        ((skimSecondBalanceCalldataMem (UInt256.ofNat I.codeOwner.val) o toWord value)
          |>.readWithPadding 292 36)
        (I.depth + 1) I.header I.blobVersionedHashes I.blocks false) :
    ∃ evm2S : EVM.State,
      typedCallViaEVM config evm1S
        (AccountAddress.ofUInt256 (UInt256.land token1 solcAddrMask))
        "balanceOf" 0 [.address evm1S.executionEnv.codeOwner] (z2, evm2S, out2) false ∧
      σ2 = evm2S.accountMap ∧ evm2S.σ₀ = σ₀ ∧ evm2S.executionEnv = I := by
  have hcd : config.externalABI.encode? "balanceOf" [.address I.codeOwner] =
      some ((skimSecondBalanceCalldataMem (UInt256.ofNat I.codeOwner.val) o toWord value)
        |>.readWithPadding 292 36) :=
    skimSecondBalanceCalldataMem_encode I.codeOwner toWord value ho32 hoSize
  exact uniswapSkimBalanceTypedCallFromState_source
    (targetWord := UInt256.land token1 solcAddrMask)
    (calldataMem := skimSecondBalanceCalldataMem (UInt256.ofNat I.codeOwner.val) o toWord value)
    (inOff := ⟨292⟩) hPost hσ0 henv hdepth hcd hΘ

theorem uniswapSkimSecondBalanceTypedCall_source_dynamic
    {σ1 σ₀ I} {evm1S : EVM.State} {σ2 : AccountMap}
    {z2 : Bool} {out2 : ByteArray} {A_in2 : Substate} {callGas2 : UInt256}
    {o out1 : ByteArray} {toWord value token1 : UInt256}
    (hPost : σ1 = evm1S.accountMap) (hσ0 : evm1S.σ₀ = σ₀)
    (henv : evm1S.executionEnv = I) (hdepth : I.depth.val < 1024)
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hout1Ne : out1.size ≠ 0) (hout1Size : out1.size < 2 ^ 255)
    (hΘ : ∃ (g'' : UInt256) (A'_evm : Substate),
      (σ2, g'', A'_evm, z2, out2) = Ethereum.EVM.Θ σ1 σ₀ A_in2
        (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner.val)) I.sender
        (AccountAddress.ofUInt256 (UInt256.land token1 solcAddrMask))
        (toExecute σ1 (AccountAddress.ofUInt256 (UInt256.land token1 solcAddrMask)))
        callGas2 (UInt256.ofNat I.gasPrice) ⟨0⟩ ⟨0⟩
        ((skimSecondBalanceDynamicCalldataMem (UInt256.ofNat I.codeOwner.val) o
          toWord value out1)
          |>.readWithPadding (skimSafeTransferReturnDataPtr out1).toNat 36)
        (I.depth + 1) I.header I.blobVersionedHashes I.blocks false) :
    ∃ evm2S : EVM.State,
      typedCallViaEVM config evm1S
        (AccountAddress.ofUInt256 (UInt256.land token1 solcAddrMask))
        "balanceOf" 0 [.address evm1S.executionEnv.codeOwner] (z2, evm2S, out2) false ∧
      σ2 = evm2S.accountMap ∧ evm2S.σ₀ = σ₀ ∧ evm2S.executionEnv = I := by
  have hcd : config.externalABI.encode? "balanceOf" [.address I.codeOwner] =
      some ((skimSecondBalanceDynamicCalldataMem (UInt256.ofNat I.codeOwner.val) o
        toWord value out1)
        |>.readWithPadding (skimSafeTransferReturnDataPtr out1).toNat 36) :=
    skimSecondBalanceDynamicCalldataMem_encode I.codeOwner toWord value
      ho32 hoSize hout1Ne hout1Size
  exact uniswapSkimBalanceTypedCallFromState_source
    (targetWord := UInt256.land token1 solcAddrMask)
    (calldataMem := skimSecondBalanceDynamicCalldataMem (UInt256.ofNat I.codeOwner.val)
      o toWord value out1)
    (inOff := skimSafeTransferReturnDataPtr out1) hPost hσ0 henv hdepth hcd hΘ

theorem uniswapSkimSecondBalanceStaticReserve1 {σ1 : AccountMap}
    {evm1S evm2S : EVM.State} {I : ExecutionEnv}
    {target : EVM.Address} {args : List Value} {z2 : Bool} {out2 : ByteArray}
    (hPost : σ1 = evm1S.accountMap)
    (henv : evm1S.executionEnv = I)
    (hcall1 : typedCallViaEVM config evm1S target "balanceOf" 0 args
      (z2, evm2S, out2) false) :
    uniswapReserve1Word evm2S =
      UInt256.land
        (UInt256.div (solcSlotWordAt ⟨8⟩ σ1 I) reserve112Shift)
        reserve112Mask := by
  have hslot :=
    typedCallViaEVM_static_storage_getD_of_accounts_eq
      (cfg := config) (σ := σ1) (evm := evm1S) (evm' := evm2S)
      (slot := ⟨8⟩) (default := ⟨0⟩) hPost hcall1
  simpa [uniswapReserve1Word, Solm.EVM.storageLoad, State.lookupAccount,
    Account.lookupStorage, solcSlotWordAt, solcSlotWord, henv] using
    congrArg (fun w => UInt256.land (UInt256.div w reserve112Shift) reserve112Mask) hslot


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
    (hPost : σ = evm1.accountMap)
    (htarget :
      AccountAddress.ofUInt256 (UInt256.land token1 solcAddrMask) =
        uniswapAddressAtSlot (uniswapLockEnteredState evm) ⟨7⟩)
    (hnoCode : extCodeSizeWord σ (UInt256.land token1 solcAddrMask) = ⟨0⟩) :
    evalExpr? config
      { contract := contract, locals := skimFirstSafeTransferStore evm evm0 I balance0 } evm1
      (.binary .gt (.extCodeSize (.var "_token1")) (.intLit 0)) = .ok (.bool false) := by
  let target := UInt256.land token1 solcAddrMask
  let addr := uniswapAddressAtSlot (uniswapLockEnteredState evm) ⟨7⟩
  have hnoEvm : extCodeSizeWord evm1.accountMap target = ⟨0⟩ := by
    simpa only [← hPost] using hnoCode
  have hcodeWord :
      EVM.Word.ofNat ((evm1.lookupAccount addr).option 0 (fun acc => acc.code.size)) = ⟨0⟩ := by
    change EVM.Word.ofNat
      ((evm1.accountMap.get? addr).option 0 (fun acc => acc.code.size)) = ⟨0⟩
    cases hacc : evm1.accountMap.get? addr with
    | none =>
        rfl
    | some acc =>
        have hnoAcc : UInt256.ofNat acc.code.size = ⟨0⟩ := by
          simpa [-Std.ExtTreeMap.get?_eq_getElem?, target, addr, htarget,
            extCodeSizeWord, hacc] using hnoEvm
        simpa [-Std.ExtTreeMap.get?_eq_getElem?, hacc] using hnoAcc
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
    (hPost : σ = evm1.accountMap)
    (htarget :
      AccountAddress.ofUInt256 (UInt256.land token1 solcAddrMask) =
        uniswapAddressAtSlot (uniswapLockEnteredState evm) ⟨7⟩)
    (hcode : extCodeSizeWord σ (UInt256.land token1 solcAddrMask) ≠ ⟨0⟩) :
    evalExpr? config
      { contract := contract, locals := skimFirstSafeTransferStore evm evm0 I balance0 } evm1
      (.binary .gt (.extCodeSize (.var "_token1")) (.intLit 0)) = .ok (.bool true) := by
  let target := UInt256.land token1 solcAddrMask
  let addr := uniswapAddressAtSlot (uniswapLockEnteredState evm) ⟨7⟩
  have hcodeEvm : extCodeSizeWord evm1.accountMap target ≠ ⟨0⟩ := by
    simpa only [← hPost] using hcode
  have hcodeWord :
      EVM.Word.ofNat ((evm1.lookupAccount addr).option 0 (fun acc => acc.code.size)) ≠ ⟨0⟩ := by
    change EVM.Word.ofNat
      ((evm1.accountMap.get? addr).option 0 (fun acc => acc.code.size)) ≠ ⟨0⟩
    intro hzero
    apply hcodeEvm
    cases hacc : evm1.accountMap.get? addr with
    | none =>
        unfold extCodeSizeWord
        rw [show AccountAddress.ofUInt256 target = addr by simpa [target, addr] using htarget,
          hacc]
        rfl
    | some acc =>
        have hzeroAcc : UInt256.ofNat acc.code.size = ⟨0⟩ := by
          simpa [-Std.ExtTreeMap.get?_eq_getElem?, hacc] using hzero
        simpa [-Std.ExtTreeMap.get?_eq_getElem?, target, addr, htarget,
          extCodeSizeWord, hacc] using hzeroAcc
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
    {σ σ₀ A I} {g : Sat256}
    (htoken0NoCode :
      extCodeSizeWord (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩)
        (UInt256.land solcAddrMask
          (solcSlotWordAt ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I)) =
        ⟨0⟩) :
    skimToken0GuardFalse (initState σ σ₀ g A I) I := by
  let σLockS := sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩
  let token0WordS := solcSlotWordAt ⟨6⟩ σLockS I
  have hnoSolm :
      extCodeSizeWord σLockS (UInt256.land solcAddrMask token0WordS) = ⟨0⟩ := by
    simpa [σLockS, token0WordS] using htoken0NoCode
  unfold skimToken0GuardFalse
  let evmS := initState σ σ₀ g A I
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
      Account.lookupStorage, uniswapAddressAtSlot, extCodeSizeWord, solcSlotWordAt, solcSlotWord,
        σLockS,
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
    {σ σ₀ A I} {g : Sat256}
    (htoken0Code :
      extCodeSizeWord (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩)
        (UInt256.land solcAddrMask
          (solcSlotWordAt ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I)) ≠
        ⟨0⟩) :
    skimToken0GuardTrue (initState σ σ₀ g A I) I := by
  let σLockS := sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩
  let token0WordS := solcSlotWordAt ⟨6⟩ σLockS I
  have hcodeSolm :
      extCodeSizeWord σLockS (UInt256.land solcAddrMask token0WordS) ≠ ⟨0⟩ := by
    simpa [σLockS, token0WordS] using htoken0Code
  unfold skimToken0GuardTrue
  let evmS := initState σ σ₀ g A I
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
      Account.lookupStorage, uniswapAddressAtSlot, extCodeSizeWord, solcSlotWordAt, solcSlotWord,
        σLockS,
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
    {σ σ₀ A I} {g : UInt256}
    (maskFn : UInt256 → UInt256)
    (hcode : I.code = uniswapV2PairBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hlocked :
      (σ.get? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.getD ⟨12⟩ ⟨0⟩)) ≠
        ⟨1⟩)
    (hdispatch : dispatchMsg contract I.calldata = some skimTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (skimTransition.params.map Param.name)
        (transitionSignature skimTransition).paramTypes I.calldata = some (skimStore I))
    (hRuntime :
      RDrev uniswapV2PairBytecode (Sat256.ofUInt256 g)
        (initState σ σ₀ (Sat256.ofUInt256 g) A I)) :
    runtimeEquivalenceFor config contract σ σ₀ g A I := by
  let evmS := initState σ σ₀ (Sat256.ofUInt256 g) A I
  let _toWord := maskFn (skimToWord I)
  have hlockedSolm :
      Solm.EVM.storageLoad evmS evmS.executionEnv.codeOwner ⟨12⟩ ≠ ⟨1⟩ := by
    simpa [evmS, initState, Solm.EVM.storageLoad, State.lookupAccount,
      Account.lookupStorage] using hlocked
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
    {σ σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36)
    (hdispatch : dispatchMsg contract I.calldata = some skimTransition)
    (hreach : ∃ k C, RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1286⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C) :
    runtimeEquivalenceFor config contract σ σ₀ g A I := by
  have hdec := uniswapDecode_skim_none_short (I := I) hsz4 hshort
  exact (uniswapSkimX_shortarg (g := Sat256.ofUInt256 g)
      hsz4 hsize hshort hreach)
    |>.reEquivDecodingFailed hcode hdispatch hdec

theorem uniswapSkimBodyCoreRevert_firstNoCode
    {σ σ₀ A I} {g : UInt256}
    (maskFn : UInt256 → UInt256)
    (hcode : I.code = uniswapV2PairBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hunlocked :
      (σ.get? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.getD ⟨12⟩ ⟨0⟩)) = ⟨1⟩)
    (htoken0NoCode :
      extCodeSizeWord (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩)
        (UInt256.land solcAddrMask
          (solcSlotWordAt ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I)) =
        ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some skimTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (skimTransition.params.map Param.name)
        (transitionSignature skimTransition).paramTypes I.calldata = some (skimStore I))
    (hRuntime :
      RDrev uniswapV2PairBytecode (Sat256.ofUInt256 g)
        (initState σ σ₀ (Sat256.ofUInt256 g) A I)) :
    runtimeEquivalenceFor config contract σ σ₀ g A I := by
  let evmS := initState σ σ₀ (Sat256.ofUInt256 g) A I
  let _toWord := maskFn (skimToWord I)
  have hunlockedSolm :
      Solm.EVM.storageLoad evmS evmS.executionEnv.codeOwner ⟨12⟩ = ⟨1⟩ := by
    simpa [evmS, initState, Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage]
      using hunlocked
  have hguard0 : skimToken0GuardFalse evmS I :=
    skimToken0GuardFalse_initState_of_noCode htoken0NoCode
  have hbody :
      ExecTransitionBody config contract evmS (skimStore I) skimTransition.body .reverted := by
    exact uniswapSkimBodyReverts_firstNoCode evmS I
      (by simp only [evmS, initState]; exact hwv)
      hunlockedSolm hguard0
  exact hRuntime.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem uniswapSkimBodyCoreRevert_firstCallDepth
    {σ σ₀ A I} {g : UInt256}
    (maskFn : UInt256 → UInt256)
    (hcode : I.code = uniswapV2PairBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hdepth : I.depth = 1024)
    (hunlocked :
      (σ.get? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.getD ⟨12⟩ ⟨0⟩)) = ⟨1⟩)
    (htoken0Code :
      extCodeSizeWord (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩)
        (UInt256.land solcAddrMask
          (solcSlotWordAt ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I)) ≠
        ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some skimTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (skimTransition.params.map Param.name)
        (transitionSignature skimTransition).paramTypes I.calldata = some (skimStore I))
    (hRuntime :
      RDrev uniswapV2PairBytecode (Sat256.ofUInt256 g)
        (initState σ σ₀ (Sat256.ofUInt256 g) A I)) :
    runtimeEquivalenceFor config contract σ σ₀ g A I := by
  let evmS := initState σ σ₀ (Sat256.ofUInt256 g) A I
  let evmL := uniswapLockEnteredState evmS
  let target := EVM.address (uniswapAddressAtSlot evmL ⟨6⟩)
  let _toWord := maskFn (skimToWord I)
  have hunlockedSolm :
      Solm.EVM.storageLoad evmS evmS.executionEnv.codeOwner ⟨12⟩ = ⟨1⟩ := by
    simpa [evmS, initState, Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage]
      using hunlocked
  have hguard0 : skimToken0GuardTrue evmS I :=
    skimToken0GuardTrue_initState_of_code htoken0Code
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
    {σ σ₀ A I} {g : UInt256}
    (maskFn : UInt256 → UInt256)
    (hcode : I.code = uniswapV2PairBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hlocked :
      (σ.get? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.getD ⟨12⟩ ⟨0⟩)) ≠
        ⟨1⟩)
    (hdispatch : dispatchMsg contract I.calldata = some skimTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (skimTransition.params.map Param.name)
        (transitionSignature skimTransition).paramTypes I.calldata = some (skimStore I))
    (hRuntime :
      RDrev uniswapV2PairBytecode (Sat256.ofUInt256 g)
        (initState σ σ₀ (Sat256.ofUInt256 g) A I)) :
    runtimeEquivalenceFor config contract σ σ₀ g A I := by
  exact uniswapSkimBodyCoreRevert_locked maskFn hcode hwv hlocked hdispatch hdecode
    hRuntime

/-- Short-calldata decode-failure `skim(address)` refinement slice, packaged from selector
dispatch through the body core. -/
theorem uniswapSkimBodyDecodeFailed_short
    {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = uniswapV2PairBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩) (hsel : selIs I ⟨#[0xbc, 0x25, 0xcf, 0x77]⟩)
    (hshort : I.calldata.size < 36)
    (hdispatch : dispatchMsg contract I.calldata = some skimTransition) :
    runtimeEquivalenceFor config contract σ σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I ⟨#[0xbc, 0x25, 0xcf, 0x77]⟩ rfl hsel
  exact uniswapSkimBodyCoreDecodeFailed_short hcode hsize hsz4 hshort hdispatch
    (uniswapReachSkimBody (g := Sat256.ofUInt256 g) hcode hwv hsz4 hsize hsel)

theorem uniswapSkimBodyRevert_firstNoCode
    {σ σ₀ A I} {g : UInt256}
    (maskFn : UInt256 → UInt256)
    (hcode : I.code = uniswapV2PairBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hunlocked :
      (σ.get? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.getD ⟨12⟩ ⟨0⟩)) = ⟨1⟩)
    (htoken0NoCode :
      extCodeSizeWord (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩)
        (UInt256.land solcAddrMask
          (solcSlotWordAt ⟨6⟩ (sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩) I)) =
        ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some skimTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (skimTransition.params.map Param.name)
        (transitionSignature skimTransition).paramTypes I.calldata = some (skimStore I))
    (hRuntime :
      RDrev uniswapV2PairBytecode (Sat256.ofUInt256 g)
        (initState σ σ₀ (Sat256.ofUInt256 g) A I)) :
    runtimeEquivalenceFor config contract σ σ₀ g A I := by
  exact uniswapSkimBodyCoreRevert_firstNoCode maskFn hcode hwv hunlocked htoken0NoCode
    hdispatch hdecode hRuntime

end UniswapV2Pair
