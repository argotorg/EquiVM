import Benchmarks.Midnight.CollateralData

/-! Typed market tuples used to relate ABI values and the runtime's word layouts. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

structure MarketData where
  chainId : UInt256
  midnight : AccountAddress
  loanToken : AccountAddress
  collaterals : List CollateralData
  maturity : UInt256
  rcfThreshold : UInt256
  enterGate : AccountAddress
  liquidatorGate : AccountAddress

def MarketData.value (m : MarketData) : Value :=
  .tuple [.int (Int.ofNat m.chainId.toNat), .address m.midnight, .address m.loanToken,
    .array (m.collaterals.map CollateralData.value), .int (Int.ofNat m.maturity.toNat),
    .int (Int.ofNat m.rcfThreshold.toNat), .address m.enterGate, .address m.liquidatorGate]

def MarketData.words (m : MarketData) (collateralPtr : UInt256) : List UInt256 :=
  [m.chainId, UInt256.ofNat m.midnight.val, UInt256.ofNat m.loanToken.val, collateralPtr,
    m.maturity, m.rcfThreshold, UInt256.ofNat m.enterGate.val, UInt256.ofNat m.liquidatorGate.val]

def MarketData.at (bytes : ByteArray) (start : Nat) (collaterals : List CollateralData) : MarketData :=
  ⟨calldataWord bytes start, AccountAddress.ofNat (calldataWord bytes (start + 32)).toNat,
    AccountAddress.ofNat (calldataWord bytes (start + 64)).toNat, collaterals,
    calldataWord bytes (start + 128), calldataWord bytes (start + 160),
    AccountAddress.ofNat (calldataWord bytes (start + 192)).toNat,
    AccountAddress.ofNat (calldataWord bytes (start + 224)).toNat⟩

def MarketData.canonicalAt (bytes : ByteArray) (start : Nat) : Prop :=
  (calldataWord bytes (start + 32)).toNat < EVM.addressModulus ∧
  (calldataWord bytes (start + 64)).toNat < EVM.addressModulus ∧
  (calldataWord bytes (start + 192)).toNat < EVM.addressModulus ∧
  (calldataWord bytes (start + 224)).toNat < EVM.addressModulus

instance (bytes : ByteArray) (start : Nat) : Decidable (MarketData.canonicalAt bytes start) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

theorem MarketData.abiValue (m : MarketData) : Model.abiValue m.value = m.value := by
  have hc : Model.abiValues (m.collaterals.map CollateralData.value) =
      m.collaterals.map CollateralData.value := by
    induction m.collaterals with
    | nil => rfl
    | cons c cs ih => simp only [List.map_cons, Model.abiValues, CollateralData.abiValue, ih]
  simp only [MarketData.value, Model.abiValue, Model.abiValues, hc]

theorem MarketData.collaterals_get (m : MarketData) :
    tupleGetValue? m.value 3 = .ok (.array (m.collaterals.map CollateralData.value)) := rfl

end Benchmarks.Midnight
