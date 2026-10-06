import Reasoning.StateFacts
import Reasoning.EVMWord
import Examples.UniswapV2Pair.Sync
import Reasoning.ExternalCall

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace UniswapV2Pair


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
    {σ1 σ₀ I} {evm1S : EVM.State} {σ2 : AccountMap}
    {z2 : Bool} {out2 calldataMem : ByteArray} {A_in2 : Substate}
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
      evm2S.accountMap = σ2 ∧ evm2S.executionEnv = evm1S.executionEnv ∧
      evm2S.σ₀ = evm1S.σ₀ := by
  obtain ⟨g'', A'_evm, hΘeq⟩ := hΘ
  let target : EVM.Address := AccountAddress.ofUInt256 targetWord
  let evmE : EVM.State := { evm1S with accountMap := σ1, σ₀ := σ₀, executionEnv := I }
  have hdepthNe : evmE.executionEnv.depth ≠ 1024 := by
    intro hEq
    have hlt : evmE.executionEnv.depth.val < 1024 := by simpa [evmE] using hdepth
    rw [hEq] at hlt
    exact absurd hlt (by decide)
  have hΘE : (σ2, g'', A'_evm, z2, out2) =
      Ethereum.EVM.Θ evmE.accountMap evmE.σ₀ A_in2
        (AccountAddress.ofUInt256 (UInt256.ofNat evmE.executionEnv.codeOwner.val))
        evmE.executionEnv.sender target (toExecute evmE.accountMap target)
        callGas2 (UInt256.ofNat evmE.executionEnv.gasPrice) ⟨0⟩ ⟨0⟩
        (calldataMem.readWithPadding inOff.toNat 36)
        (evmE.executionEnv.depth + 1) evmE.executionEnv.header
        evmE.executionEnv.blobVersionedHashes evmE.executionEnv.blocks false := by
    simpa [evmE, target] using hΘeq
  have hcdE : config.externalABI.encode? "balanceOf" [.address evmE.executionEnv.codeOwner] =
      some (calldataMem.readWithPadding inOff.toNat 36) := by
    simpa [evmE] using hcd
  have hevmE : evmE = evm1S := by
    cases evm1S
    simp_all [evmE]
  have hcallE :
      typedCallViaEVM config evmE target "balanceOf" 0
        [.address evmE.executionEnv.codeOwner]
        (z2, { evmE with accountMap := σ2, substate := A'_evm }, out2) false :=
    callCoincides
      (cfg := config) (evm := evmE) (tgt := target) (targetWord := targetWord)
      (name := "balanceOf") (args := [.address evmE.executionEnv.codeOwner])
      (σ' := σ2) (A' := A'_evm) (A_in := A_in2) (z := z2) (o := out2)
      (g'' := g'') (callGas := callGas2) (mem := calldataMem) (inOff := inOff)
      (inSize := ⟨36⟩) (callPerm := false) hdepthNe rfl hcdE hΘE
  refine ⟨{ evm1S with accountMap := σ2, substate := A'_evm }, ?_, rfl, rfl, rfl⟩
  simpa [hevmE] using hcallE

theorem uniswapFirstBalanceTypedCall_source
    {σ σ₀ A I} {g : UInt256} {σ' : AccountMap}
    {z : Bool} {o : ByteArray} {A_in : Substate} {callGas : UInt256}
    (hdepth : I.depth.val < 1024)
    (hΘ : ∃ (g'' : UInt256) (A'_evm : Substate),
      (σ', g'', A'_evm, z, o) =
        Ethereum.EVM.Θ
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
        "balanceOf" 0 [.address I.codeOwner] (z, evm0S, o) false ∧
      evm0S.accountMap = σ' ∧ evm0S.executionEnv = I ∧ evm0S.σ₀ = σ₀ := by
  let evmS := initState σ σ₀ (Sat256.ofUInt256 g) A I
  let evmSL := uniswapLockEnteredState evmS
  let σLock := sstoreAccountMap I.codeOwner σ ⟨12⟩ ⟨0⟩
  let token0Word := solcSlotWordAt ⟨6⟩ σLock I
  let token0Clean := UInt256.land solcAddrMask token0Word
  have hPost : σLock = evmSL.accountMap := by
    simp [evmSL, evmS, σLock, uniswapLockEnteredState, uniswapUnlockedState,
      initState, storageStore_accountMap]
  have henv : evmSL.executionEnv = I := by
    simp [evmSL, evmS, uniswapLockEnteredState, uniswapUnlockedState, initState,
      storageStore_executionEnv]
  let target : EVM.Address := AccountAddress.ofUInt256 token0Clean
  have htarget : target = EVM.address (uniswapAddressAtSlot evmSL ⟨6⟩) := by
    have haddr : AccountAddress.ofUInt256 token0Clean = uniswapAddressAtSlot evmSL ⟨6⟩ := by
      simp [token0Clean, token0Word, uniswapAddressAtSlot, solcSlotWordAt, solcSlotWord,
        Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage, hPost, henv,
        accountAddress_ofUInt256_eq_ofNat_toNat, u256_land_comm]
    change AccountAddress.ofUInt256 token0Clean =
      EVM.address (uniswapAddressAtSlot evmSL ⟨6⟩)
    rw [haddr]
    exact (address_of_val (uniswapAddressAtSlot evmSL ⟨6⟩)).symm
  have hσ0 : evmSL.σ₀ = σ₀ := by
    simp [evmSL, evmS, uniswapLockEnteredState, uniswapUnlockedState, initState,
      storageStore_σ0]
  have hcd : config.externalABI.encode? "balanceOf" [.address I.codeOwner] =
      some ((balanceOfThisCalldataMem (UInt256.ofNat I.codeOwner.val)).readWithPadding 128 36) :=
    balanceOfThisCalldataMem_encode I.codeOwner
  obtain ⟨evm0S, hcall, hMap, hEnv, hOrig⟩ := uniswapBalanceTypedCallFromState_source
    (σ1 := σLock) (σ₀ := σ₀) (I := I) (evm1S := evmSL) (σ2 := σ')
    (z2 := z) (out2 := o) (A_in2 := A_in) (callGas2 := callGas)
    (targetWord := token0Clean) (calldataMem := balanceOfThisCalldataMem
      (UInt256.ofNat I.codeOwner.val)) (inOff := ⟨128⟩)
    hPost hσ0 henv hdepth hcd hΘ
  refine ⟨evm0S, ?_, hMap, hEnv.trans henv, ?_⟩
  have htargets : AccountAddress.ofUInt256 token0Clean =
      EVM.address (uniswapAddressAtSlot evmSL ⟨6⟩) := by
    simpa [target] using htarget
  rw [← htargets]
  simpa [evmSL, evmS, henv] using hcall
  · exact hOrig.trans hσ0

theorem uniswapSyncSecondBalanceTypedCall_source
    {σ1 σ₀ I} {evm0S : EVM.State} {σ2 : AccountMap}
    {z2 : Bool} {out2 : ByteArray} {A_in2 : Substate} {callGas2 : UInt256}
    {o : ByteArray} (hPost : σ1 = evm0S.accountMap)
    (hσ0 : evm0S.σ₀ = σ₀) (henv : evm0S.executionEnv = I)
    (hdepth : I.depth.val < 1024) (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size)
    (hΘ : ∃ (g'' : UInt256) (A'_evm : Substate),
      (σ2, g'', A'_evm, z2, out2) = Ethereum.EVM.Θ σ1 σ₀ A_in2
        (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner.val)) I.sender
        (AccountAddress.ofUInt256 (UInt256.land solcAddrMask (solcSlotWordAt ⟨7⟩ σ1 I)))
        (toExecute σ1 (AccountAddress.ofUInt256
          (UInt256.land solcAddrMask (solcSlotWordAt ⟨7⟩ σ1 I))))
        callGas2 (UInt256.ofNat I.gasPrice) ⟨0⟩ ⟨0⟩
        ((balanceOfThisRebuiltCalldataMem (UInt256.ofNat I.codeOwner.val) o).readWithPadding 128 36)
        (I.depth + 1) I.header I.blobVersionedHashes I.blocks false) :
    ∃ evm1S : EVM.State,
      typedCallViaEVM config evm0S (EVM.address (uniswapAddressAtSlot evm0S ⟨7⟩))
        "balanceOf" 0 [.address evm0S.executionEnv.codeOwner] (z2, evm1S, out2) false ∧
      evm1S.accountMap = σ2 ∧ evm1S.executionEnv = evm0S.executionEnv ∧
      evm1S.σ₀ = evm0S.σ₀ := by
  let token1WordE := solcSlotWordAt ⟨7⟩ σ1 I
  let token1CleanE := UInt256.land solcAddrMask token1WordE
  have hslot : token1WordE = Solm.EVM.storageLoad evm0S evm0S.executionEnv.codeOwner ⟨7⟩ := by
    simpa [token1WordE, solcSlotWordAt, solcSlotWord, Solm.EVM.storageLoad, State.lookupAccount,
      Account.lookupStorage, henv, hPost]
  have htarget : AccountAddress.ofUInt256 token1CleanE =
      EVM.address (uniswapAddressAtSlot evm0S ⟨7⟩) := by
    have haddr : AccountAddress.ofUInt256 token1CleanE = uniswapAddressAtSlot evm0S ⟨7⟩ := by
      simpa [token1CleanE, token1WordE, uniswapAddressAtSlot, hslot,
        accountAddress_ofUInt256_eq_ofNat_toNat, u256_land_comm]
    rw [haddr]
    exact (address_of_val (uniswapAddressAtSlot evm0S ⟨7⟩)).symm
  have hcd : config.externalABI.encode? "balanceOf" [.address I.codeOwner] =
      some ((balanceOfThisRebuiltCalldataMem (UInt256.ofNat I.codeOwner.val) o).readWithPadding 128 36) :=
    balanceOfThisRebuiltCalldataMem_encode I.codeOwner o ho32 hoSize
  obtain ⟨evm1S, hcall, hMap, hEnv, hOrig⟩ := uniswapBalanceTypedCallFromState_source
    (σ1 := σ1) (σ₀ := σ₀) (I := I) (evm1S := evm0S) (σ2 := σ2)
    (z2 := z2) (out2 := out2) (A_in2 := A_in2) (callGas2 := callGas2)
    (targetWord := token1CleanE) (calldataMem := balanceOfThisRebuiltCalldataMem
      (UInt256.ofNat I.codeOwner.val) o) (inOff := ⟨128⟩)
    hPost hσ0 henv hdepth hcd hΘ
  refine ⟨evm1S, ?_, hMap, ?_, hOrig⟩
  · simpa [token1CleanE, token1WordE, htarget] using hcall
  · simpa [henv] using hEnv

end UniswapV2Pair
