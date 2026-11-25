import Benchmarks.Midnight.LiquidateCallbackHead
import Benchmarks.Midnight.LiquidateCallbackArrayHead
import Benchmarks.Midnight.LiquidateCallbackCollateralLoop

variable {fork : Ethereum.Fork}

/-! The callback header and complete collateral array, with the remaining scalar fields pending. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

def liquidateCallbackMarketPrefixMemory (mem : ByteArray) (root : Nat) (sender : AccountAddress)
    (id : UInt256) (m : MarketData) : ByteArray :=
  writeWordArray (liquidateCallbackArrayHeadMemory mem root sender id m) (root + 612)
    (m.collaterals.flatMap CollateralData.words)

theorem liquidateCallbackMarketPrefixMemory_prefix (mem : ByteArray) (root : Nat)
    (sender : AccountAddress) (id : UInt256) (m : MarketData) :
    MemoryPrefix mem (liquidateCallbackMarketPrefixMemory mem root sender id m) root :=
  (liquidateCallbackArrayHeadMemory_prefix _ _ _ _ _).trans
    (memoryPrefix_writeWordArray _ _ _ _ (by omega))

theorem midnightLiquidateCallbackMarketPrefix {credit : Nat} {I : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem rdata : ByteArray} {aw root id dp dl borrower receiver badDebt : UInt256}
    {m : MarketData} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 24 ≤ 1024) (hd : decodeCalldataMarket I.calldata 4 = some m)
    (hroot : root.toNat < 2^128) (hlo : 832 ≤ root.toNat) (hsize : 832 ≤ mem.size)
    (hfree : memLoad (UInt256.ofNat 64) mem = root)
    (hid : memLoad (UInt256.ofNat 768) mem = id)
    (hz : memLoad (UInt256.ofNat 800) mem = ⟨0⟩) (ha : MemoryFunding credit mem aw C)
    (rd : RD fork midnightBytecode I g s0 ⟨5824⟩
      ([dp, dl, borrower, badDebt, receiver] ++ R) mem aw rdata σ k C) :
    ∃ aw' k' C',
      MemoryFunding (credit + 4)
        (liquidateCallbackMarketPrefixMemory mem root.toNat I.source id m) aw' C' ∧
      RD fork midnightBytecode I g s0 ⟨6050⟩
        ([UInt256.ofNat m.collaterals.length, liquidateCallbackArrayBase I.calldata,
          UInt256.ofNat (marketCollateralDataStart I.calldata) + UInt256.ofNat (128 * m.collaterals.length),
          borrower, receiver, dp, dl, root + UInt256.ofNat (612 + 128 * m.collaterals.length),
          root, badDebt, root] ++ R)
        (liquidateCallbackMarketPrefixMemory mem root.toNat I.source id m) aw' rdata σ k' C' := by
  obtain ⟨aw1, k1, C1, ha1, rd1⟩ := midnightLiquidateCallbackHead (by omega) hd hroot hlo hsize
    hfree hid ha rd
  have hp1 := liquidateCallbackHeadMemory_prefix mem root.toNat I.source id m
  have hz1 : memLoad (UInt256.ofNat 800)
      (liquidateCallbackHeadMemory mem root.toNat I.source id m) = ⟨0⟩ :=
    (hp1.load ⟨800⟩ (by decide) hlo hsize).trans hz
  obtain ⟨aw2, k2, C2, ha2, rd2⟩ := midnightLiquidateCallbackArrayHead (by omega) hd hroot hlo
    (hsize.trans hp1.size) hz1 ha1 rd1
  have hm : liquidateCallbackArraySetupMemory
      (liquidateCallbackHeadMemory mem root.toNat I.source id m) root.toNat m =
      liquidateCallbackArrayHeadMemory mem root.toNat I.source id m := by
    simp only [liquidateCallbackArraySetupMemory, liquidateCallbackArrayHeadMemory,
      writeWordArray, Nat.add_assoc, Nat.reduceAdd]
  rw [hm] at ha2 rd2
  obtain ⟨hstart, hdecode⟩ := decodeCalldataMarket_collateralsAt hd
  obtain ⟨_, hn, _, hl, _⟩ := decodeCalldataMarket_collateralArray hd
  have hlen : m.collaterals.length < 2^64 := by rw [hl]; exact hn
  have hc : (UInt256.ofNat m.collaterals.length).toNat = m.collaterals.length :=
    UInt256.toNat_ofNat_of_lt (by change _ < 2^256; omega)
  have hs : (UInt256.ofNat (marketCollateralDataStart I.calldata)).toNat =
      marketCollateralDataStart I.calldata := UInt256.toNat_ofNat_of_lt (by change _ < 2^256; omega)
  have ho : (root + UInt256.ofNat 612).toNat = root.toNat + 612 :=
    uadd_word_ofNat_toNat _ _ (by change _ < 2^256; omega)
  have hcount := (liquidateCallbackArrayFacts hd).2.2.2.2
  obtain ⟨aw3, k3, C3, _, ha3, rd3⟩ := midnightLiquidateCallbackCollateralLoop m.collaterals
    hstack (by rw [hcount, hc]; change _ = 0 + _; omega) (by rw [hs]; change _ < 2^256; omega)
    (by rw [ho]; change _ < 2^256; omega) (by rw [hs]; exact hdecode) ha2 rd2
  have hzadd (w : UInt256) : (⟨0⟩ : UInt256) + w = w := u256_zero_add w
  have hf := And.intro ha3 rd3
  simp only [ho, wordAddNat_add, hzadd] at hf
  exact ⟨_, _, _, hf⟩

end Benchmarks.Midnight
