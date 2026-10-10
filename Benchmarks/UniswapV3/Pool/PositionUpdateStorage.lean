import Benchmarks.UniswapV3.Pool.PositionUpdateStoreModel
import Benchmarks.UniswapV3.Pool.PositionSnapshotMemory
import Benchmarks.UniswapV3.Pool.StorageWordUpdate

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool

theorem uint128Word_add_mask (a b : UInt256) :
    uint128Word (a + uint128Word b) = uint128Word (a + b) := by
  apply u256_inj
  simp only [uint128Word_toNat, uadd_toNat,
    Nat.mod_mod_of_dvd _ (by decide : 2 ^ 128 ∣ UInt256.size)]
  exact Nat.add_mod_mod _ _ _

def positionOwedPart (second : Bool) (word : UInt256) : UInt256 :=
  uint128Word (if second then UInt256.div word (UInt256.ofNat (2 ^ 128)) else word)

theorem positionOwedWord_eq (key : UInt256) (second : Bool) (σ : AccountMap) (ee : ExecutionEnv) :
    positionOwedWord key second σ ee =
      positionOwedPart second (solcSlotWordAt (solcMappingSlot ⟨7⟩ key + UInt256.ofNat 3) σ ee) := by
  cases second
  · exact positionLowWord key 3 σ ee
  · change UInt256.land (UInt256.div _ (UInt256.ofNat (256 ^ 16)))
      (UInt256.ofNat (256 ^ 16 - 1)) = _
    rw [show UInt256.ofNat (256 ^ 16) = UInt256.ofNat (2 ^ 128) from by decide,
      show UInt256.ofNat (256 ^ 16 - 1) = UInt256.ofNat (2 ^ 128 - 1) from by decide,
      u256_land_comm]
    rfl

def positionOwedAddWord (second : Bool) (feeWord old : UInt256) : UInt256 :=
  if second then
    UInt256.lor (UInt256.mul (uint128Word (feeWord + positionOwedPart true old)) (UInt256.ofNat (2 ^ 128)))
      (uint128Word old)
  else UInt256.lor (uint128Word (feeWord + positionOwedPart false old))
    (UInt256.land old (UInt256.lnot (UInt256.ofNat (2 ^ 128 - 1))))

theorem positionOwedAddWord_eq (second : Bool) (feeWord old : UInt256) :
    protocolFeeUpdateWord second old (positionOwedPart second old + uint128Word feeWord) =
      positionOwedAddWord second feeWord old := by
  cases second
  · simp only [protocolFeeUpdateWord, positionOwedAddWord, Bool.false_eq_true, if_false]
    rw [uint128Word_add_mask, u256_add_comm (positionOwedPart false old)]
  · simp only [protocolFeeUpdateWord, positionOwedAddWord, if_true]
    rw [uint128Word_add_mask, u256_add_comm (positionOwedPart true old)]
    exact u256_lor_comm _ _

theorem positionUpdateOwedState_eq (a : PositionUpdateArgs) (original current : EVM.State)
    (second : Bool) :
    positionUpdateOwedState a original current second =
      modifyStorageWord current (solcMappingSlot ⟨7⟩ a.key + UInt256.ofNat 3)
        (positionOwedAddWord second (positionUpdateFeeRaw a original second)) := by
  unfold positionUpdateOwedState storePositionOwed modifyStorageWord
  rw [positionOwedWord_eq, storageLoad_codeOwner_eq_solcSlotWordAt current current.executionEnv _ rfl]
  congr 1
  exact positionOwedAddWord_eq second _ _

def positionUpdateOwedPairWord (a : PositionUpdateArgs) (evm : EVM.State) (old : UInt256) : UInt256 :=
  positionOwedAddWord true (positionUpdateFeeRaw a evm true)
    (positionOwedAddWord false (positionUpdateFeeRaw a evm false) old)

theorem positionUpdateOwedPair_eq (a : PositionUpdateArgs) (original current : EVM.State) :
    positionUpdateOwedState a original (positionUpdateOwedState a original current false) true =
      modifyStorageWord current (solcMappingSlot ⟨7⟩ a.key + UInt256.ofNat 3)
        (positionUpdateOwedPairWord a original) := by
  simp only [positionUpdateOwedState_eq, modifyStorageWord_comp]
  rfl

def positionLiquidityMap (σ : AccountMap) (ee : ExecutionEnv) (key word : UInt256) : AccountMap :=
  sstoreAccountMap ee.codeOwner σ (solcMappingSlot ⟨7⟩ key)
    (protocolFeeUpdateWord false (solcSlotWordAt (solcMappingSlot ⟨7⟩ key) σ ee) word)

theorem SourceState.positionLiquidity {s0 : EVM.State} {ee : ExecutionEnv} {σ : AccountMap}
    {evm : EVM.State} (hs : SourceState s0 ee σ evm) (key word : UInt256) :
    SourceState s0 ee (positionLiquidityMap σ ee key word) (positionLiquidityState evm key word) :=
  hs.readModifyWrite (solcMappingSlot ⟨7⟩ key) (fun old ↦ protocolFeeUpdateWord false old word)

theorem SourceState.positionLast {s0 : EVM.State} {ee : ExecutionEnv} {σ : AccountMap}
    {evm : EVM.State} (hs : SourceState s0 ee σ evm) (key : UInt256) (second : Bool) (word : UInt256) :
    SourceState s0 ee
      (sstoreAccountMap ee.codeOwner σ
        (solcMappingSlot ⟨7⟩ key + UInt256.ofNat (if second then 2 else 1)) word)
      (positionLastState evm key second word) := by
  simpa only [positionLastState, hs.env] using
    hs.storageWrite (solcMappingSlot ⟨7⟩ key + UInt256.ofNat (if second then 2 else 1)) word

def positionUpdateGrowthMap (a : PositionUpdateArgs) (σ : AccountMap) (ee : ExecutionEnv) : AccountMap :=
  sstoreAccountMap ee.codeOwner
    (sstoreAccountMap ee.codeOwner σ (solcMappingSlot ⟨7⟩ a.key + UInt256.ofNat 1) a.growth0)
    (solcMappingSlot ⟨7⟩ a.key + UInt256.ofNat 2) a.growth1

theorem SourceState.positionUpdateGrowth {s0 : EVM.State} {ee : ExecutionEnv} {σ : AccountMap}
    {evm : EVM.State} (a : PositionUpdateArgs) (hs : SourceState s0 ee σ (positionUpdateLiquidityState a evm)) :
    SourceState s0 ee (positionUpdateGrowthMap a σ ee) (positionUpdateGrowthState a evm) :=
  SourceState.positionLast (SourceState.positionLast hs a.key false a.growth0) a.key true a.growth1

def positionUpdateOwedMap (a : PositionUpdateArgs) (evm : EVM.State)
    (σ : AccountMap) (ee : ExecutionEnv) : AccountMap :=
  sstoreAccountMap ee.codeOwner σ (solcMappingSlot ⟨7⟩ a.key + UInt256.ofNat 3)
    (positionUpdateOwedPairWord a evm
      (solcSlotWordAt (solcMappingSlot ⟨7⟩ a.key + UInt256.ofNat 3) σ ee))

theorem SourceState.positionUpdateOwedPair {s0 : EVM.State} {ee : ExecutionEnv} {σ : AccountMap}
    {current : EVM.State} (hs : SourceState s0 ee σ current) (a : PositionUpdateArgs) (evm : EVM.State) :
    SourceState s0 ee (positionUpdateOwedMap a evm σ ee)
      (positionUpdateOwedState a evm (positionUpdateOwedState a evm current false) true) := by
  rw [positionUpdateOwedPair_eq]
  exact hs.readModifyWrite (solcMappingSlot ⟨7⟩ a.key + UInt256.ofNat 3) (positionUpdateOwedPairWord a evm)

end Benchmarks.UniswapV3.Pool
