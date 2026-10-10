import Benchmarks.UniswapV3.Pool.PackedPrefixStore
import Benchmarks.UniswapV3.Pool.Slot0Struct
import Benchmarks.UniswapV3.Pool.Calls

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool

def initializeTickLow (price : UInt256) (tick : Int) : UInt256 :=
  packedAppend price (EVM.wordOfInt tick) 160 24

def initializeCardinalityLow (price : UInt256) (tick : Int) : UInt256 :=
  packedAppend (initializeTickLow price tick) ⟨1⟩ 200 16

def initializeNextLow (price : UInt256) (tick : Int) : UInt256 :=
  packedAppend (initializeCardinalityLow price tick) ⟨1⟩ 216 16

def initializeUnlockedLow (price : UInt256) (tick : Int) : UInt256 :=
  packedAppend (initializeNextLow price tick) ⟨1⟩ 240 8

def initializeSlot0Word (old price : UInt256) (tick : Int) : UInt256 :=
  packedPrefixWord old (initializeUnlockedLow price tick) 248

def initializeSlot0State (evm : EVM.State) (price : UInt256) (tick : Int) : EVM.State :=
  EVM.storageStore evm evm.executionEnv.codeOwner ⟨0⟩
    (initializeSlot0Word (EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩) price tick)

def initializeSlot0Value (price : UInt256) (tick : Int) : Value :=
  .struct "Slot0" [("sqrtPriceX96", .int (Int.ofNat price.toNat)), ("tick", .int tick),
    ("observationIndex", .int 0), ("observationCardinality", .int 1),
    ("observationCardinalityNext", .int 1), ("feeProtocol", .int 0), ("unlocked", .bool true)]

theorem initializeTickLow_lt (price : UInt256) (tick : Int) (hp : price.toNat < 2 ^ 160) :
    (initializeTickLow price tick).toNat < 2 ^ 184 :=
  packedAppend_lt price (EVM.wordOfInt tick) 160 24 (by decide) hp

theorem initializeCardinalityLow_lt (price : UInt256) (tick : Int) (hp : price.toNat < 2 ^ 160) :
    (initializeCardinalityLow price tick).toNat < 2 ^ 216 :=
  packedAppend_lt (initializeTickLow price tick) ⟨1⟩ 200 16 (by decide)
    (lt_of_lt_of_le (initializeTickLow_lt price tick hp) (by decide))

theorem initializeNextLow_lt (price : UInt256) (tick : Int) (hp : price.toNat < 2 ^ 160) :
    (initializeNextLow price tick).toNat < 2 ^ 232 :=
  packedAppend_lt (initializeCardinalityLow price tick) ⟨1⟩ 216 16 (by decide)
    (initializeCardinalityLow_lt price tick hp)

theorem initializeUnlockedLow_lt (price : UInt256) (tick : Int) (hp : price.toNat < 2 ^ 160) :
    (initializeUnlockedLow price tick).toNat < 2 ^ 248 :=
  packedAppend_lt (initializeNextLow price tick) ⟨1⟩ 240 8 (by decide)
    (lt_of_lt_of_le (initializeNextLow_lt price tick hp) (by decide))

theorem initializeSlot0Word_toNat (old price : UInt256) (tick : Int) (hp : price.toNat < 2 ^ 160) :
    (initializeSlot0Word old price tick).toNat =
      price.toNat + 2 ^ 160 * ((EVM.wordOfInt tick).toNat % 2 ^ 24) + 2 ^ 200 + 2 ^ 216 +
        2 ^ 240 + 2 ^ 248 * (old.toNat / 2 ^ 248) := by
  rw [initializeSlot0Word, packedPrefixWord_toNat _ _ _ (by decide)
    (initializeUnlockedLow_lt price tick hp), initializeUnlockedLow,
    packedAppend_toNat _ _ _ _ (by decide)
      (lt_of_lt_of_le (initializeNextLow_lt price tick hp) (by decide)),
    initializeNextLow, packedAppend_toNat _ _ _ _ (by decide)
      (initializeCardinalityLow_lt price tick hp),
    initializeCardinalityLow, packedAppend_toNat _ _ _ _ (by decide)
      (lt_of_lt_of_le (initializeTickLow_lt price tick hp) (by decide)),
    initializeTickLow, packedAppend_toNat _ _ _ _ (by decide) hp]
  norm_num [show (⟨1⟩ : UInt256).toNat = 1 from rfl]

theorem SourceState.initializeSlot0 {s0 ee σ evm} (hs : SourceState s0 ee σ evm)
    (price : UInt256) (tick : Int) :
    SourceState s0 ee
      (sstoreAccountMap ee.codeOwner σ ⟨0⟩ (initializeSlot0Word (solcSlotWordAt ⟨0⟩ σ ee) price tick))
      (initializeSlot0State evm price tick) := by
  simpa only [initializeSlot0State, hs.env, solcSlotWordAt] using
    hs.readModifyWrite ⟨0⟩ (fun old ↦ initializeSlot0Word old price tick)

end Benchmarks.UniswapV3.Pool
