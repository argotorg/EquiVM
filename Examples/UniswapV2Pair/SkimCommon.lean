import Examples.UniswapV2Pair.Common
import Examples.UniswapV2Pair.SafeTransfer
import Examples.UniswapV2Pair.ExternalWrappers
import Examples.UniswapV2Pair.ExternalCalls
import Examples.UniswapV2Pair.Dispatch
import Reasoning.SolmBody

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace UniswapV2Pair

/-! ## `skim(address)` source/ABI prefix -/

/-- The raw ABI word for `skim`'s `to` argument. -/
abbrev skimToWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

abbrev skimToMaskedWord (I : ExecutionEnv) : UInt256 :=
  UInt256.land solcAddrMask (skimToWord I)

abbrev skimToAddress (I : ExecutionEnv) : AccountAddress :=
  AccountAddress.ofNat (skimToWord I).toNat

abbrev skimToValue (I : ExecutionEnv) : Value :=
  .address (skimToAddress I)

abbrev skimStore (I : ExecutionEnv) : Store :=
  (∅ : Store).insert "to" (skimToValue I)

abbrev skimBalanceValue (balance : UInt256) : Value :=
  uniswapUint256Value balance

def skimTokenSlot (i : Fin 2) : UInt256 :=
  match i.val with
  | 0 => ⟨6⟩
  | _ => ⟨7⟩

def skimTokenVar (i : Fin 2) : Ident :=
  match i.val with
  | 0 => "_token0"
  | _ => "_token1"

def skimBalanceVar (i : Fin 2) : Ident :=
  match i.val with
  | 0 => "balance0"
  | _ => "balance1"

def skimExcessVar (i : Fin 2) : Ident :=
  match i.val with
  | 0 => "excess0"
  | _ => "excess1"

def skimReserveWord (i : Fin 2) (evm : EVM.State) : UInt256 :=
  match i.val with
  | 0 => uniswapReserve0Word evm
  | _ => uniswapReserve1Word evm

def skimBalanceWord (i : Fin 2) (balance0 balance1 : UInt256) : UInt256 :=
  match i.val with
  | 0 => balance0
  | _ => balance1

abbrev skimBalanceValueAt (i : Fin 2) (balance0 balance1 : UInt256) : Value :=
  skimBalanceValue (skimBalanceWord i balance0 balance1)

abbrev skimBalanceStore (I : ExecutionEnv) (balance0 balance1 : UInt256) : Store :=
  uniswapBalanceOfStore (skimStore I) (skimBalanceValue balance0) (skimBalanceValue balance1)

def skimExcessWord (reserve balance : UInt256) : UInt256 :=
  UInt256.ofNat (balance.toNat - reserve.toNat)

theorem skimExcessWord_eq_sub {reserve balance : UInt256}
    (hle : reserve.toNat ≤ balance.toNat) :
    skimExcessWord reserve balance = UInt256.sub balance reserve := by
  apply u256_inj
  rw [skimExcessWord, UInt256.toNat_ofNat_of_lt]
  · exact (usub_toNat (a := balance) (b := reserve) hle).symm
  · exact lt_of_le_of_lt (Nat.sub_le _ _) balance.val.isLt

def skimExcessWordAt (i : Fin 2) (evm : EVM.State) (balance0 balance1 : UInt256) : UInt256 :=
  skimExcessWord (skimReserveWord i evm) (skimBalanceWord i balance0 balance1)

abbrev skimExcessValueOf (reserve balance : UInt256) : Value :=
  uint256Value (skimExcessWord reserve balance)

abbrev skimExcessValueAt (i : Fin 2) (evm : EVM.State)
    (balance0 balance1 : UInt256) : Value :=
  uint256Value (skimExcessWordAt i evm balance0 balance1)

abbrev skimSequentialExcessValueAt (i : Fin 2) (firstCallEvm secondCallEvm : EVM.State)
    (balance0 balance1 : UInt256) : Value :=
  match i.val with
  | 0 => skimExcessValueAt 0 firstCallEvm balance0 balance1
  | _ => skimExcessValueAt 1 secondCallEvm balance0 balance1

def skimExcess0Word (evm : EVM.State) (balance0 : UInt256) : UInt256 :=
  skimExcessWord (uniswapReserve0Word evm) balance0

def skimExcess1Word (evm : EVM.State) (balance1 : UInt256) : UInt256 :=
  skimExcessWord (uniswapReserve1Word evm) balance1

abbrev skimExcess0Value (evm : EVM.State) (balance0 : UInt256) : Value :=
  skimExcessValueOf (uniswapReserve0Word evm) balance0

abbrev skimExcess1Value (evm : EVM.State) (balance1 : UInt256) : Value :=
  skimExcessValueOf (uniswapReserve1Word evm) balance1

theorem skimExcessValueAt_zero (evm : EVM.State) (balance0 balance1 : UInt256) :
    skimExcessValueAt 0 evm balance0 balance1 = skimExcess0Value evm balance0 := by
  rfl

theorem skimExcessValueAt_one (evm : EVM.State) (balance0 balance1 : UInt256) :
    skimExcessValueAt 1 evm balance0 balance1 = skimExcess1Value evm balance1 := by
  rfl

abbrev skimExcess0Store (evm : EVM.State) (I : ExecutionEnv)
    (balance0 balance1 : UInt256) : Store :=
  (skimBalanceStore I balance0 balance1).insert "excess0" (skimExcess0Value evm balance0)

abbrev skimExcessStore (evm : EVM.State) (I : ExecutionEnv)
    (balance0 balance1 : UInt256) : Store :=
  (skimExcess0Store evm I balance0 balance1).insert "excess1"
    (skimExcess1Value evm balance1)

abbrev skimSafeTransfer0Store (evm : EVM.State) (I : ExecutionEnv)
    (balance0 balance1 : UInt256) (success : Bool) (out : ByteArray) : Store :=
  ((skimExcessStore evm I balance0 balance1).insert "ok0" (.bool success)).insert "_ret0"
    (.bytes out)

abbrev skimSafeTransfer1Store (evm : EVM.State) (I : ExecutionEnv)
    (balance0 balance1 : UInt256) (out0 : ByteArray) (success : Bool) (out1 : ByteArray) :
    Store :=
  uniswapLowLevelCallRequireStore
    (skimSafeTransfer0Store evm I balance0 balance1 true out0) "ok1" "_ret1" success out1

abbrev skimTokenStore (evm : EVM.State) (I : ExecutionEnv) : Store :=
  ((skimStore I).insert "_token0"
    (.address (uniswapAddressAtSlot (uniswapLockEnteredState evm) ⟨6⟩))).insert "_token1"
    (.address (uniswapAddressAtSlot (uniswapLockEnteredState evm) ⟨7⟩))

abbrev skimFirstBalanceStore (evm : EVM.State) (I : ExecutionEnv)
    (balance0 : UInt256) : Store :=
  (skimTokenStore evm I).insert "balance0" (skimBalanceValue balance0)

abbrev skimFirstExcessStore (startEvm callEvm : EVM.State) (I : ExecutionEnv)
    (balance0 : UInt256) : Store :=
  (skimFirstBalanceStore startEvm I balance0).insert "excess0"
    (skimExcess0Value callEvm balance0)

abbrev skimFirstSafeTransferStore (startEvm callEvm : EVM.State) (I : ExecutionEnv)
    (balance0 : UInt256) : Store :=
  (skimFirstExcessStore startEvm callEvm I balance0).insert "ok0" .unit

abbrev skimSecondBalanceStore (startEvm firstCallEvm : EVM.State) (I : ExecutionEnv)
    (balance0 balance1 : UInt256) : Store :=
  (skimFirstSafeTransferStore startEvm firstCallEvm I balance0).insert "balance1"
    (skimBalanceValue balance1)

abbrev skimSecondExcessStore (startEvm firstCallEvm secondCallEvm : EVM.State)
    (I : ExecutionEnv) (balance0 balance1 : UInt256) : Store :=
  (skimSecondBalanceStore startEvm firstCallEvm I balance0 balance1).insert "excess1"
    (skimExcess1Value secondCallEvm balance1)

abbrev skimSecondSafeTransferStore (startEvm firstCallEvm secondCallEvm : EVM.State)
    (I : ExecutionEnv) (balance0 balance1 : UInt256) : Store :=
  (skimSecondExcessStore startEvm firstCallEvm secondCallEvm I balance0 balance1).insert "ok1" .unit

theorem skimBalanceStore_balance (I : ExecutionEnv) (balance0 balance1 : UInt256)
    (i : Fin 2) :
    (skimBalanceStore I balance0 balance1).get? (skimBalanceVar i) =
      some (skimBalanceValueAt i balance0 balance1) := by
  fin_cases i
  · exact uniswapBalanceOfStore_balance0 (skimStore I) (skimBalanceValue balance0)
      (skimBalanceValue balance1)
  · exact uniswapBalanceOfStore_balance1 (skimStore I) (skimBalanceValue balance0)
      (skimBalanceValue balance1)

theorem skimBalanceStore_balance0 (I : ExecutionEnv) (balance0 balance1 : UInt256) :
    (skimBalanceStore I balance0 balance1).get? "balance0" =
      some (skimBalanceValue balance0) := by
  show (skimBalanceStore I balance0 balance1).get? (skimBalanceVar 0) =
    some (skimBalanceValueAt 0 balance0 balance1)
  exact skimBalanceStore_balance I balance0 balance1 0

theorem skimBalanceStore_balance1 (I : ExecutionEnv) (balance0 balance1 : UInt256) :
    (skimBalanceStore I balance0 balance1).get? "balance1" =
      some (skimBalanceValue balance1) := by
  show (skimBalanceStore I balance0 balance1).get? (skimBalanceVar 1) =
    some (skimBalanceValueAt 1 balance0 balance1)
  exact skimBalanceStore_balance I balance0 balance1 1

theorem skimExcess0Store_balance1 (evm : EVM.State) (I : ExecutionEnv)
    (balance0 balance1 : UInt256) :
    (skimExcess0Store evm I balance0 balance1).get? "balance1" =
      some (skimBalanceValue balance1) := by
  rw [skimExcess0Store, store_get_ne _ _ (by decide), skimBalanceStore_balance1]

theorem skimExcessStore_excess (evm : EVM.State) (I : ExecutionEnv)
    (balance0 balance1 : UInt256) (i : Fin 2) :
    (skimExcessStore evm I balance0 balance1).get? (skimExcessVar i) =
      some (skimExcessValueAt i evm balance0 balance1) := by
  fin_cases i
  · simp only [skimExcessVar, skimExcessValueAt, skimExcessWordAt, skimReserveWord,
      skimBalanceWord]
    rw [skimExcessStore, store_get_ne _ _ (by decide), skimExcess0Store, store_get_self]
  · simp only [skimExcessVar, skimExcessValueAt, skimExcessWordAt, skimReserveWord,
      skimBalanceWord]
    rw [skimExcessStore, store_get_self]

theorem skimSafeTransfer0Store_ok0 (evm : EVM.State) (I : ExecutionEnv)
    (balance0 balance1 : UInt256) (success : Bool) (out : ByteArray) :
    (skimSafeTransfer0Store evm I balance0 balance1 success out).get? "ok0" =
      some (.bool success) := by
  rw [skimSafeTransfer0Store, store_get_ne _ _ (by decide), store_get_self]

theorem evalExpr_skim_safeTransfer0_ok (storeEvm evalEvm : EVM.State) (I : ExecutionEnv)
    (balance0 balance1 : UInt256) (success : Bool) (out : ByteArray) :
    evalExpr? config
      { contract := contract, locals := skimSafeTransfer0Store storeEvm I balance0 balance1 success out }
      evalEvm (.var "ok0") = .ok (.bool success) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [skimSafeTransfer0Store_ok0]

theorem skimTokenStore_token (evm : EVM.State) (I : ExecutionEnv) (i : Fin 2) :
    (skimTokenStore evm I).get? (skimTokenVar i) =
      some (.address (uniswapAddressAtSlot (uniswapLockEnteredState evm) (skimTokenSlot i))) := by
  fin_cases i
  · simp only [skimTokenVar, skimTokenSlot]
    rw [skimTokenStore, store_get_ne _ _ (by decide), store_get_self]
  · simp only [skimTokenVar, skimTokenSlot]
    rw [skimTokenStore, store_get_self]

theorem skimTokenStore_token0 (evm : EVM.State) (I : ExecutionEnv) :
    (skimTokenStore evm I).get? "_token0" =
      some (.address (uniswapAddressAtSlot (uniswapLockEnteredState evm) ⟨6⟩)) := by
  show (skimTokenStore evm I).get? (skimTokenVar 0) =
    some (.address (uniswapAddressAtSlot (uniswapLockEnteredState evm) (skimTokenSlot 0)))
  exact skimTokenStore_token evm I 0

theorem skimTokenStore_token1 (evm : EVM.State) (I : ExecutionEnv) :
    (skimTokenStore evm I).get? "_token1" =
      some (.address (uniswapAddressAtSlot (uniswapLockEnteredState evm) ⟨7⟩)) := by
  show (skimTokenStore evm I).get? (skimTokenVar 1) =
    some (.address (uniswapAddressAtSlot (uniswapLockEnteredState evm) (skimTokenSlot 1)))
  exact skimTokenStore_token evm I 1

theorem skimTokenStore_to (evm : EVM.State) (I : ExecutionEnv) :
    (skimTokenStore evm I).get? "to" = some (skimToValue I) := by
  rw [skimTokenStore, store_get_ne _ _ (by decide), store_get_ne _ _ (by decide)]
  rw [skimStore, store_get_self]

theorem skimFirstBalanceStore_balance0 (evm : EVM.State) (I : ExecutionEnv)
    (balance0 : UInt256) :
    (skimFirstBalanceStore evm I balance0).get? "balance0" =
      some (skimBalanceValue balance0) := by
  rw [skimFirstBalanceStore, store_get_self]

theorem skimFirstBalanceStore_token (evm : EVM.State) (I : ExecutionEnv)
    (balance0 : UInt256) (i : Fin 2) :
    (skimFirstBalanceStore evm I balance0).get? (skimTokenVar i) =
      some (.address (uniswapAddressAtSlot (uniswapLockEnteredState evm) (skimTokenSlot i))) := by
  have hne : ("balance0" == skimTokenVar i) = false := by
    fin_cases i <;> simp [skimTokenVar]
  rw [skimFirstBalanceStore, store_get_ne _ _ hne, skimTokenStore_token]

theorem skimFirstBalanceStore_token0 (evm : EVM.State) (I : ExecutionEnv)
    (balance0 : UInt256) :
    (skimFirstBalanceStore evm I balance0).get? "_token0" =
      some (.address (uniswapAddressAtSlot (uniswapLockEnteredState evm) ⟨6⟩)) := by
  simpa [skimTokenVar, skimTokenSlot] using skimFirstBalanceStore_token evm I balance0 0

theorem skimFirstBalanceStore_to (evm : EVM.State) (I : ExecutionEnv)
    (balance0 : UInt256) :
    (skimFirstBalanceStore evm I balance0).get? "to" = some (skimToValue I) := by
  rw [skimFirstBalanceStore, store_get_ne _ _ (by decide), skimTokenStore_to]

theorem skimFirstExcessStore_token (startEvm callEvm : EVM.State) (I : ExecutionEnv)
    (balance0 : UInt256) (i : Fin 2) :
    (skimFirstExcessStore startEvm callEvm I balance0).get? (skimTokenVar i) =
      some (.address
        (uniswapAddressAtSlot (uniswapLockEnteredState startEvm) (skimTokenSlot i))) := by
  have hne : ("excess0" == skimTokenVar i) = false := by
    fin_cases i <;> simp [skimTokenVar]
  rw [skimFirstExcessStore, store_get_ne _ _ hne, skimFirstBalanceStore_token]

theorem skimFirstExcessStore_token0 (startEvm callEvm : EVM.State) (I : ExecutionEnv)
    (balance0 : UInt256) :
    (skimFirstExcessStore startEvm callEvm I balance0).get? "_token0" =
      some (.address (uniswapAddressAtSlot (uniswapLockEnteredState startEvm) ⟨6⟩)) := by
  simpa [skimTokenVar, skimTokenSlot] using
    skimFirstExcessStore_token startEvm callEvm I balance0 0

theorem skimFirstExcessStore_to (startEvm callEvm : EVM.State) (I : ExecutionEnv)
    (balance0 : UInt256) :
    (skimFirstExcessStore startEvm callEvm I balance0).get? "to" = some (skimToValue I) := by
  rw [skimFirstExcessStore, store_get_ne _ _ (by decide), skimFirstBalanceStore_to]

theorem skimFirstExcessStore_excess0 (startEvm callEvm : EVM.State) (I : ExecutionEnv)
    (balance0 : UInt256) :
    (skimFirstExcessStore startEvm callEvm I balance0).get? "excess0" =
      some (skimExcess0Value callEvm balance0) := by
  rw [skimFirstExcessStore, store_get_self]

theorem skimFirstSafeTransferStore_token (startEvm callEvm : EVM.State)
    (I : ExecutionEnv) (balance0 : UInt256) (i : Fin 2) :
    (skimFirstSafeTransferStore startEvm callEvm I balance0).get? (skimTokenVar i) =
      some (.address
        (uniswapAddressAtSlot (uniswapLockEnteredState startEvm) (skimTokenSlot i))) := by
  have hne : ("ok0" == skimTokenVar i) = false := by
    fin_cases i <;> simp [skimTokenVar]
  rw [skimFirstSafeTransferStore, store_get_ne _ _ hne, skimFirstExcessStore_token]

theorem skimFirstSafeTransferStore_token1 (startEvm callEvm : EVM.State)
    (I : ExecutionEnv) (balance0 : UInt256) :
    (skimFirstSafeTransferStore startEvm callEvm I balance0).get? "_token1" =
      some (.address (uniswapAddressAtSlot (uniswapLockEnteredState startEvm) ⟨7⟩)) := by
  simpa [skimTokenVar, skimTokenSlot] using
    skimFirstSafeTransferStore_token startEvm callEvm I balance0 1

theorem skimFirstSafeTransferStore_to (startEvm callEvm : EVM.State)
    (I : ExecutionEnv) (balance0 : UInt256) :
    (skimFirstSafeTransferStore startEvm callEvm I balance0).get? "to" =
      some (skimToValue I) := by
  rw [skimFirstSafeTransferStore, store_get_ne _ _ (by decide), skimFirstExcessStore_to]

theorem skimSecondBalanceStore_balance1 (startEvm firstCallEvm : EVM.State)
    (I : ExecutionEnv) (balance0 balance1 : UInt256) :
    (skimSecondBalanceStore startEvm firstCallEvm I balance0 balance1).get? "balance1" =
      some (skimBalanceValue balance1) := by
  rw [skimSecondBalanceStore, store_get_self]

theorem skimSecondBalanceStore_token (startEvm firstCallEvm : EVM.State)
    (I : ExecutionEnv) (balance0 balance1 : UInt256) (i : Fin 2) :
    (skimSecondBalanceStore startEvm firstCallEvm I balance0 balance1).get?
        (skimTokenVar i) =
      some (.address
        (uniswapAddressAtSlot (uniswapLockEnteredState startEvm) (skimTokenSlot i))) := by
  have hne : ("balance1" == skimTokenVar i) = false := by
    fin_cases i <;> simp [skimTokenVar]
  rw [skimSecondBalanceStore, store_get_ne _ _ hne, skimFirstSafeTransferStore_token]

theorem skimSecondBalanceStore_token1 (startEvm firstCallEvm : EVM.State)
    (I : ExecutionEnv) (balance0 balance1 : UInt256) :
    (skimSecondBalanceStore startEvm firstCallEvm I balance0 balance1).get? "_token1" =
      some (.address (uniswapAddressAtSlot (uniswapLockEnteredState startEvm) ⟨7⟩)) := by
  simpa [skimTokenVar, skimTokenSlot] using
    skimSecondBalanceStore_token startEvm firstCallEvm I balance0 balance1 1

theorem skimSecondBalanceStore_to (startEvm firstCallEvm : EVM.State)
    (I : ExecutionEnv) (balance0 balance1 : UInt256) :
    (skimSecondBalanceStore startEvm firstCallEvm I balance0 balance1).get? "to" =
      some (skimToValue I) := by
  rw [skimSecondBalanceStore, store_get_ne _ _ (by decide), skimFirstSafeTransferStore_to]

theorem skimSecondExcessStore_token
    (startEvm firstCallEvm secondCallEvm : EVM.State)
    (I : ExecutionEnv) (balance0 balance1 : UInt256) (i : Fin 2) :
    (skimSecondExcessStore startEvm firstCallEvm secondCallEvm I balance0 balance1).get?
        (skimTokenVar i) =
      some (.address
        (uniswapAddressAtSlot (uniswapLockEnteredState startEvm) (skimTokenSlot i))) := by
  have hne : ("excess1" == skimTokenVar i) = false := by
    fin_cases i <;> simp [skimTokenVar]
  rw [skimSecondExcessStore, store_get_ne _ _ hne, skimSecondBalanceStore_token]

theorem skimSecondExcessStore_token1
    (startEvm firstCallEvm secondCallEvm : EVM.State)
    (I : ExecutionEnv) (balance0 balance1 : UInt256) :
    (skimSecondExcessStore startEvm firstCallEvm secondCallEvm I balance0 balance1).get?
        "_token1" =
      some (.address (uniswapAddressAtSlot (uniswapLockEnteredState startEvm) ⟨7⟩)) := by
  simpa [skimTokenVar, skimTokenSlot] using
    skimSecondExcessStore_token startEvm firstCallEvm secondCallEvm I balance0 balance1 1

theorem skimSecondExcessStore_to
    (startEvm firstCallEvm secondCallEvm : EVM.State)
    (I : ExecutionEnv) (balance0 balance1 : UInt256) :
    (skimSecondExcessStore startEvm firstCallEvm secondCallEvm I balance0 balance1).get?
        "to" =
      some (skimToValue I) := by
  rw [skimSecondExcessStore, store_get_ne _ _ (by decide), skimSecondBalanceStore_to]

theorem skimSecondExcessStore_excess
    (startEvm firstCallEvm secondCallEvm : EVM.State)
    (I : ExecutionEnv) (balance0 balance1 : UInt256) (i : Fin 2) :
    (skimSecondExcessStore startEvm firstCallEvm secondCallEvm I balance0 balance1).get?
        (skimExcessVar i) =
      some (skimSequentialExcessValueAt i firstCallEvm secondCallEvm balance0 balance1) := by
  fin_cases i
  · simp only [skimExcessVar, skimSequentialExcessValueAt]
    rw [skimSecondExcessStore, store_get_ne _ _ (by decide)]
    rw [skimSecondBalanceStore, store_get_ne _ _ (by decide)]
    rw [skimFirstSafeTransferStore, store_get_ne _ _ (by decide), skimFirstExcessStore_excess0]
    rfl
  · simp only [skimExcessVar, skimSequentialExcessValueAt]
    rw [skimSecondExcessStore, store_get_self]
    rfl

theorem skimSecondExcessStore_excess1
    (startEvm firstCallEvm secondCallEvm : EVM.State)
    (I : ExecutionEnv) (balance0 balance1 : UInt256) :
    (skimSecondExcessStore startEvm firstCallEvm secondCallEvm I balance0 balance1).get?
        "excess1" =
      some (skimExcess1Value secondCallEvm balance1) := by
  show (skimSecondExcessStore startEvm firstCallEvm secondCallEvm I balance0 balance1).get?
      (skimExcessVar 1) =
    some (skimSequentialExcessValueAt 1 firstCallEvm secondCallEvm balance0 balance1)
  exact skimSecondExcessStore_excess startEvm firstCallEvm secondCallEvm I balance0 balance1 1

theorem uniswapDecode_skim_ok {I : ExecutionEnv}
    (hsz36 : 36 ≤ I.calldata.size)
    (_hcanon : (skimToWord I).toNat < EVM.addressModulus) :
    decodeCalldataWithMode config.abiDecodeMode (skimTransition.params.map Param.name)
      (transitionSignature skimTransition).paramTypes I.calldata = some (skimStore I) := by
  show decodeCalldataWithMode config.abiDecodeMode ["to"] [legacyAddr] I.calldata = _
  simpa [skimStore, skimToValue, skimToWord, calldataWord]
    using decodeCalldata_legacyAddress_ok (cd := I.calldata) (x := "to") hsz36

theorem uniswapDecode_skim_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36) :
    decodeCalldataWithMode config.abiDecodeMode (skimTransition.params.map Param.name)
      (transitionSignature skimTransition).paramTypes I.calldata = none := by
  show decodeCalldataWithMode config.abiDecodeMode ["to"] [legacyAddr] I.calldata = none
  simpa using decodeCalldata_legacyAddress_none_short (cd := I.calldata) (x := "to")
    hsz4 hshort

theorem uniswapDecode_skim_ok_noncanon {I : ExecutionEnv}
    (hsz36 : 36 ≤ I.calldata.size)
    (_hnc : ¬ (skimToWord I).toNat < EVM.addressModulus) :
    decodeCalldataWithMode config.abiDecodeMode (skimTransition.params.map Param.name)
      (transitionSignature skimTransition).paramTypes I.calldata = some (skimStore I) := by
  show decodeCalldataWithMode config.abiDecodeMode ["to"] [legacyAddr] I.calldata = _
  simpa [skimStore, skimToValue, skimToWord, calldataWord]
    using decodeCalldata_legacyAddress_ok (cd := I.calldata) (x := "to") hsz36

end UniswapV2Pair
