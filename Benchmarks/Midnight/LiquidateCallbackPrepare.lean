import Benchmarks.Midnight.LiquidateCallbackMarketPrefix
import Benchmarks.Midnight.LiquidateCallbackFields
import Benchmarks.Midnight.CalldataBytesEncodeMemory

/-! Complete construction of liquidation's callback input buffer, up to CALL. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

def liquidateCallbackSize (m : MarketData) (dl : Nat) : Nat :=
  612 + 128 * m.collaterals.length + returnDataAllocation dl

def liquidateCallbackMemory (mem bytes : ByteArray) (root : Nat) (sender : AccountAddress)
    (m : MarketData) (id index seized repaid borrower receiver : UInt256) (dp dl : Nat)
    (badDebt : UInt256) : ByteArray :=
  writeWord (calldataBytesEncodeMemory
    (liquidateCallbackFieldsMemory (liquidateCallbackMarketPrefixMemory mem root sender id m)
      root m index seized repaid borrower receiver) bytes (root + 612 + 128 * m.collaterals.length)
      dp dl) (root + 292) badDebt

theorem liquidateCallbackMemory_prefix (mem bytes : ByteArray) (root : Nat) (sender : AccountAddress)
    (m : MarketData) (id index seized repaid borrower receiver : UInt256) (dp dl : Nat)
    (badDebt : UInt256) (hd : dp + dl ≤ bytes.size) :
    MemoryPrefix mem
      (liquidateCallbackMemory mem bytes root sender m id index seized repaid borrower receiver
        dp dl badDebt) root :=
  (((liquidateCallbackMarketPrefixMemory_prefix _ _ _ _ _).trans
    (liquidateCallbackFieldsMemory_prefix _ _ _ _ _ _ _ _)).trans
    (calldataBytesEncodeMemory_prefix _ _ _ _ _ _ hd (by omega))).trans
    (memoryPrefix_writeWord _ _ _ _ (Or.inl (by omega)))

theorem midnightLiquidateCallbackPrepare {credit : Nat} {I : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem rdata : ByteArray} {aw root id index seized repaid dp dl borrower badDebt : UInt256}
    {receiver callback : AccountAddress} {m : MarketData} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 24 ≤ 1024) (hd : decodeCalldataMarket I.calldata 4 = some m)
    (hi : calldataWord I.calldata 36 = index)
    (hroot : root.toNat < 2^128) (hlo : 832 ≤ root.toNat) (hsize : 832 ≤ mem.size)
    (hfree : memLoad (UInt256.ofNat 64) mem = root)
    (hid : memLoad (UInt256.ofNat 768) mem = id)
    (hz : memLoad (UInt256.ofNat 800) mem = ⟨0⟩)
    (hcallback : memLoad (UInt256.ofNat 736) mem = UInt256.ofNat callback.val)
    (hcanon : borrower.toNat < EVM.addressModulus)
    (hseized : memLoad (UInt256.ofNat 640) mem = seized)
    (hpaid : memLoad (UInt256.ofNat 608) mem = repaid)
    (hdl : dl.toNat < 2^64) (hdata : dp.toNat + dl.toNat ≤ I.calldata.size)
    (ha : MemoryFunding credit mem aw C)
    (rd : RD midnightBytecode I g s0 ⟨5824⟩
      ([dp, dl, borrower, badDebt, UInt256.ofNat receiver.val] ++ R) mem aw rdata σ k C) :
    ∃ gasArg aw' k' C',
      MemoryFunding (credit + 4)
        (liquidateCallbackMemory mem I.calldata root.toNat I.source m id index seized repaid borrower
          (UInt256.ofNat receiver.val) dp.toNat dl.toNat badDebt) aw' C' ∧
      RD midnightBytecode I g s0 ⟨6227⟩
        ([gasArg, UInt256.ofNat callback.val, ⟨0⟩, root,
          UInt256.ofNat (liquidateCallbackSize m dl.toNat), root, ⟨32⟩, root] ++ R)
        (liquidateCallbackMemory mem I.calldata root.toNat I.source m id index seized repaid borrower
          (UInt256.ofNat receiver.val) dp.toNat dl.toNat badDebt) aw' rdata σ k' C' := by
  obtain ⟨aw1, k1, C1, ha1, rd1⟩ := midnightLiquidateCallbackMarketPrefix hstack hd hroot hlo hsize
    hfree hid hz ha rd
  have hp1 := liquidateCallbackMarketPrefixMemory_prefix mem root.toNat I.source id m
  obtain ⟨aw2, k2, C2, ha2, rd2⟩ := midnightLiquidateCallbackFields hstack hd hi hroot hlo
    (hsize.trans hp1.size) hcanon
    ((hp1.load ⟨640⟩ (by decide) (by change 672 ≤ root.toNat; omega)
      (by change 672 ≤ mem.size; omega)).trans hseized)
    ((hp1.load ⟨608⟩ (by decide) (by change 640 ≤ root.toNat; omega)
      (by change 640 ≤ mem.size; omega)).trans hpaid) ha1 rd1
  have hlen : m.collaterals.length < 2^64 := by
    obtain ⟨_, hn, _, hl, _⟩ := decodeCalldataMarket_collateralArray hd
    rw [hl]; exact hn
  have ho : (root + UInt256.ofNat (612 + 128 * m.collaterals.length)).toNat =
      root.toNat + 612 + 128 * m.collaterals.length := by
    rw [uadd_word_ofNat_toNat _ _ (by change _ < 2^256; omega)]
    omega
  obtain ⟨aw3, k3, C3, _, ha3, rd3⟩ := midnightCalldataBytesEncoderFunded
    (R := [badDebt, root, root, ⟨32⟩, root] ++ R)
    (by simp only [List.length_append, List.length_cons, List.length_nil]; omega) hdl
    (by rw [ho]; change _ < 2^256; omega) (by jump_dest) ha2 rd2
  simp only [ho, wordAddNat_add] at ha3 rd3
  have rd4 := midnightBlocks.midnight_block_6199 (R := [⟨32⟩, root] ++ R)
    (by simp only [List.length_append, List.length_cons, List.length_nil]; omega) rd3
  have ha4 := memoryFundingAt (credit := credit + 4) rd4 (by
    unfold midnightBlocks.midnight_block_6199_memory
    memory_fund ha3)
  have h292 : (root + UInt256.ofNat 292).toNat = root.toNat + 292 :=
    uadd_word_ofNat_toNat _ _ (by change _ < 2^256; omega)
  let input := liquidateCallbackMemory mem I.calldata root.toNat I.source m id index seized repaid
    borrower (UInt256.ofNat receiver.val) dp.toNat dl.toNat badDebt
  have hp4 := liquidateCallbackMemory_prefix mem I.calldata root.toNat I.source m id index seized
    repaid borrower (UInt256.ofNat receiver.val) dp.toNat dl.toNat badDebt hdata
  have hz4 : memLoad (UInt256.ofNat 800) input = ⟨0⟩ :=
    (hp4.load ⟨800⟩ (by decide) hlo hsize).trans hz
  have hcb4 : memLoad (UInt256.ofNat 736) input = UInt256.ofNat callback.val :=
    (hp4.load ⟨736⟩ (by decide) (by change 768 ≤ root.toNat; omega)
      (by change 768 ≤ mem.size; omega)).trans hcallback
  have hclean : UInt256.land (UInt256.ofNat callback.val) solcAddrMask =
      UInt256.ofNat callback.val := addressWord_val_clean callback
  have hf := And.intro ha4 rd4
  simp only [midnightBlocks.midnight_block_6199_stack, midnightBlocks.midnight_block_6199_memory,
    h292, word_add_sub_left, addressMask_computed] at hf
  change MemoryFunding (credit + 4) input _ _ ∧
    RD midnightBytecode I g s0 ⟨6227⟩
      (_ :: UInt256.land (memLoad (UInt256.ofNat 736) input) solcAddrMask ::
        memLoad (UInt256.ofNat 800) input :: root ::
        UInt256.ofNat (liquidateCallbackSize m dl.toNat) :: root :: ⟨32⟩ :: root :: R)
      input _ rdata σ _ _ at hf
  rw [hz4, hcb4, hclean] at hf
  exact ⟨_, _, _, _, hf⟩

end Benchmarks.Midnight
