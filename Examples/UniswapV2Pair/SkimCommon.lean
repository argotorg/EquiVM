import Examples.UniswapV2Pair.Common
import Examples.UniswapV2Pair.SafeTransfer
import Examples.UniswapV2Pair.ExternalWrappers
import Examples.UniswapV2Pair.ExternalCalls
import Examples.UniswapV2Pair.Dispatch
import Reasoning.Refinement
import Reasoning.SolmBody

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

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

abbrev skimBalanceStore (I : ExecutionEnv) (balance0 balance1 : UInt256) : Store :=
  uniswapBalanceOfStore (skimStore I) (skimBalanceValue balance0) (skimBalanceValue balance1)

def skimExcess0Word (evm : EVM.State) (balance0 : UInt256) : UInt256 :=
  UInt256.ofNat (balance0.toNat - (uniswapReserve0Word evm).toNat)

def skimExcess1Word (evm : EVM.State) (balance1 : UInt256) : UInt256 :=
  UInt256.ofNat (balance1.toNat - (uniswapReserve1Word evm).toNat)

abbrev skimExcess0Value (evm : EVM.State) (balance0 : UInt256) : Value :=
  .int (Int.ofNat (skimExcess0Word evm balance0).toNat)

abbrev skimExcess1Value (evm : EVM.State) (balance1 : UInt256) : Value :=
  .int (Int.ofNat (skimExcess1Word evm balance1).toNat)

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

theorem skimBalanceStore_balance0 (I : ExecutionEnv) (balance0 balance1 : UInt256) :
    (skimBalanceStore I balance0 balance1).get? "balance0" =
      some (skimBalanceValue balance0) := by
  exact uniswapBalanceOfStore_balance0 (skimStore I) (skimBalanceValue balance0)
    (skimBalanceValue balance1)

theorem skimBalanceStore_balance1 (I : ExecutionEnv) (balance0 balance1 : UInt256) :
    (skimBalanceStore I balance0 balance1).get? "balance1" =
      some (skimBalanceValue balance1) := by
  exact uniswapBalanceOfStore_balance1 (skimStore I) (skimBalanceValue balance0)
    (skimBalanceValue balance1)

theorem skimExcess0Store_balance1 (evm : EVM.State) (I : ExecutionEnv)
    (balance0 balance1 : UInt256) :
    (skimExcess0Store evm I balance0 balance1).get? "balance1" =
      some (skimBalanceValue balance1) := by
  rw [skimExcess0Store, store_get_ne _ _ (by decide), skimBalanceStore_balance1]

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

theorem skimTokenStore_token0 (evm : EVM.State) (I : ExecutionEnv) :
    (skimTokenStore evm I).get? "_token0" =
      some (.address (uniswapAddressAtSlot (uniswapLockEnteredState evm) ⟨6⟩)) := by
  rw [skimTokenStore, store_get_ne _ _ (by decide), store_get_self]

theorem skimTokenStore_token1 (evm : EVM.State) (I : ExecutionEnv) :
    (skimTokenStore evm I).get? "_token1" =
      some (.address (uniswapAddressAtSlot (uniswapLockEnteredState evm) ⟨7⟩)) := by
  rw [skimTokenStore, store_get_self]

theorem skimTokenStore_to (evm : EVM.State) (I : ExecutionEnv) :
    (skimTokenStore evm I).get? "to" = some (skimToValue I) := by
  rw [skimTokenStore, store_get_ne _ _ (by decide), store_get_ne _ _ (by decide)]
  rw [skimStore, store_get_self]

theorem skimFirstBalanceStore_balance0 (evm : EVM.State) (I : ExecutionEnv)
    (balance0 : UInt256) :
    (skimFirstBalanceStore evm I balance0).get? "balance0" =
      some (skimBalanceValue balance0) := by
  rw [skimFirstBalanceStore, store_get_self]

theorem skimFirstBalanceStore_token0 (evm : EVM.State) (I : ExecutionEnv)
    (balance0 : UInt256) :
    (skimFirstBalanceStore evm I balance0).get? "_token0" =
      some (.address (uniswapAddressAtSlot (uniswapLockEnteredState evm) ⟨6⟩)) := by
  rw [skimFirstBalanceStore, store_get_ne _ _ (by decide), skimTokenStore_token0]

theorem skimFirstBalanceStore_to (evm : EVM.State) (I : ExecutionEnv)
    (balance0 : UInt256) :
    (skimFirstBalanceStore evm I balance0).get? "to" = some (skimToValue I) := by
  rw [skimFirstBalanceStore, store_get_ne _ _ (by decide), skimTokenStore_to]

theorem skimFirstExcessStore_token0 (startEvm callEvm : EVM.State) (I : ExecutionEnv)
    (balance0 : UInt256) :
    (skimFirstExcessStore startEvm callEvm I balance0).get? "_token0" =
      some (.address (uniswapAddressAtSlot (uniswapLockEnteredState startEvm) ⟨6⟩)) := by
  rw [skimFirstExcessStore, store_get_ne _ _ (by decide),
    skimFirstBalanceStore_token0]

theorem skimFirstExcessStore_to (startEvm callEvm : EVM.State) (I : ExecutionEnv)
    (balance0 : UInt256) :
    (skimFirstExcessStore startEvm callEvm I balance0).get? "to" = some (skimToValue I) := by
  rw [skimFirstExcessStore, store_get_ne _ _ (by decide), skimFirstBalanceStore_to]

theorem skimFirstExcessStore_excess0 (startEvm callEvm : EVM.State) (I : ExecutionEnv)
    (balance0 : UInt256) :
    (skimFirstExcessStore startEvm callEvm I balance0).get? "excess0" =
      some (skimExcess0Value callEvm balance0) := by
  rw [skimFirstExcessStore, store_get_self]

theorem skimFirstSafeTransferStore_token1 (startEvm callEvm : EVM.State)
    (I : ExecutionEnv) (balance0 : UInt256) :
    (skimFirstSafeTransferStore startEvm callEvm I balance0).get? "_token1" =
      some (.address (uniswapAddressAtSlot (uniswapLockEnteredState startEvm) ⟨7⟩)) := by
  rw [skimFirstSafeTransferStore, store_get_ne _ _ (by decide),
    skimFirstExcessStore, store_get_ne _ _ (by decide),
    skimFirstBalanceStore, store_get_ne _ _ (by decide), skimTokenStore_token1]

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

theorem skimSecondBalanceStore_token1 (startEvm firstCallEvm : EVM.State)
    (I : ExecutionEnv) (balance0 balance1 : UInt256) :
    (skimSecondBalanceStore startEvm firstCallEvm I balance0 balance1).get? "_token1" =
      some (.address (uniswapAddressAtSlot (uniswapLockEnteredState startEvm) ⟨7⟩)) := by
  rw [skimSecondBalanceStore, store_get_ne _ _ (by decide),
    skimFirstSafeTransferStore_token1]

theorem skimSecondBalanceStore_to (startEvm firstCallEvm : EVM.State)
    (I : ExecutionEnv) (balance0 balance1 : UInt256) :
    (skimSecondBalanceStore startEvm firstCallEvm I balance0 balance1).get? "to" =
      some (skimToValue I) := by
  rw [skimSecondBalanceStore, store_get_ne _ _ (by decide), skimFirstSafeTransferStore_to]

theorem skimSecondExcessStore_token1
    (startEvm firstCallEvm secondCallEvm : EVM.State)
    (I : ExecutionEnv) (balance0 balance1 : UInt256) :
    (skimSecondExcessStore startEvm firstCallEvm secondCallEvm I balance0 balance1).get?
        "_token1" =
      some (.address (uniswapAddressAtSlot (uniswapLockEnteredState startEvm) ⟨7⟩)) := by
  rw [skimSecondExcessStore, store_get_ne _ _ (by decide), skimSecondBalanceStore_token1]

theorem skimSecondExcessStore_to
    (startEvm firstCallEvm secondCallEvm : EVM.State)
    (I : ExecutionEnv) (balance0 balance1 : UInt256) :
    (skimSecondExcessStore startEvm firstCallEvm secondCallEvm I balance0 balance1).get?
        "to" =
      some (skimToValue I) := by
  rw [skimSecondExcessStore, store_get_ne _ _ (by decide), skimSecondBalanceStore_to]

theorem skimSecondExcessStore_excess1
    (startEvm firstCallEvm secondCallEvm : EVM.State)
    (I : ExecutionEnv) (balance0 balance1 : UInt256) :
    (skimSecondExcessStore startEvm firstCallEvm secondCallEvm I balance0 balance1).get?
        "excess1" =
      some (skimExcess1Value secondCallEvm balance1) := by
  rw [skimSecondExcessStore, store_get_self]

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
