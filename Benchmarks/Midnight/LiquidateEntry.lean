import Benchmarks.Midnight.LiquidateEntryChecks
import Benchmarks.Midnight.LiquidateEntryMemory
import Benchmarks.Midnight.MarketDecoderPreserved

variable {fork : Ethereum.Fork}

/-! The complete liquidation entry decoder, preserving its reserved memory words. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open ABI.Solc08Calldata

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

set_option maxHeartbeats 800000 in
-- GENERALIZES midnightLiquidateEntry by retaining the decoded market equation.
theorem midnightLiquidateEntry_decoded {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 32 ≤ 1024) (h4 : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hselector : ¬ 0xac9650d8 = (bytesToWord (I.calldata.toList.take 4)).toNat)
    (hmem : 832 ≤ mem.size) (hfree : memLoad (UInt256.ofNat 64) mem = ⟨832⟩)
    (ha : MemoryAccounting mem aw C)
    (rd : RD fork midnightBytecode I g s0 ⟨4983⟩ R mem aw rdata σ k C) :
    (config.externalABI.decodeCalldata? liquidateNames liquidateTypes I.calldata = none ∧
      RDrev fork midnightBytecode g s0) ∨
    (∃ m, config.externalABI.decodeCalldata? liquidateNames liquidateTypes I.calldata =
        some (liquidateArguments m (calldataWord I.calldata 36) (calldataWord I.calldata 68)
          (calldataWord I.calldata 100) (AccountAddress.ofNat (calldataWord I.calldata 132).toNat)
          (calldataWord I.calldata 164) (AccountAddress.ofNat (calldataWord I.calldata 196).toNat)
          (AccountAddress.ofNat (calldataWord I.calldata 228).toNat)
          (I.calldata.extract (calldataArgumentPointer I.calldata 260).toNat
            ((calldataArgumentPointer I.calldata 260).toNat +
              (calldataArgumentLength I.calldata 260).toNat))) ∧
      decodeCalldataMarket I.calldata 4 = some m ∧
      292 ≤ I.calldata.size ∧ I.calldata.size < 2^255 ∧ LiquidateScalarsValid I.calldata ∧
      CalldataArgumentValid true I.calldata 260 ∧
      ∃ mem' root aw' k' C', root.toNat = 1120 + 160 * m.collaterals.length ∧
        MarketStored mem' ⟨832⟩ ⟨1088⟩ root m ∧ memLoad (UInt256.ofNat 64) mem' = root ∧
        root.toNat ≤ mem'.size ∧
        MemoryWords mem' 96 (memoryWordSnapshot (liquidateEntryMemory mem I.calldata) 96 23) ∧
        MemoryAccounting mem' aw' C' ∧ RD fork midnightBytecode I g s0 ⟨4356⟩
          (⟨832⟩ :: ⟨5161⟩ :: calldataArgumentLength I.calldata 260 ::
            calldataWord I.calldata 132 :: calldataArgumentPointer I.calldata 260 ::
            calldataWord I.calldata 196 :: calldataWord I.calldata 164 :: R)
          mem' aw' rdata σ k' C') := by
  rcases midnightLiquidateEntryChecks (by omega) h4 hsize hselector ha rd with
    hfail | ⟨h292, ho, hv, hdata, hdecode, aw1, k1, C1, ha1, rd1⟩
  · exact Or.inl hfail
  have hsmall : I.calldata.size < 2^255 := hdata.2.1
  have hh : (UInt256.ofNat 4 + calldataWord I.calldata 4).toNat =
      4 + (calldataWord I.calldata 4).toNat := calldataArgumentHead_toNat ho
  have hcap : ¬ solcMaxU64 < (calldataWord I.calldata 4).toNat := by
    change ¬ (2^64 - 1 < _)
    omega
  have hd : decodeCalldataMarket I.calldata 4 =
      decodeMarketData I.calldata (UInt256.ofNat 4 + calldataWord I.calldata 4).toNat := by
    simp only [decodeCalldataMarket, hcap, false_or, not_le_of_gt hsmall, if_false, hh]
  have rd2 := midnightBlocks.midnight_block_5126
    (by change R.length + 2 + 8 ≤ 1024; omega) (by jump_dest) rd1
  have ha2 := memoryAccountingAt rd2 (by
    simp only [midnightBlocks.midnight_block_5126_memory]
    memory_account ha1)
  change RD fork midnightBytecode I g s0 ⟨18574⟩
    ((UInt256.ofNat 4 + calldataWord I.calldata 4) :: UInt256.ofNat I.calldata.size ::
      ⟨4356⟩ :: ⟨5161⟩ :: calldataArgumentLength I.calldata 260 ::
      calldataWord I.calldata 132 :: calldataArgumentPointer I.calldata 260 ::
      calldataWord I.calldata 196 :: calldataWord I.calldata 164 :: R)
    (liquidateEntryMemory mem I.calldata) _ rdata σ _ _ at rd2
  have hf : memLoad (UInt256.ofNat 64) (liquidateEntryMemory mem I.calldata) = ⟨832⟩ := by
    rw [liquidateEntryMemory_load hmem _ (by change 96 ≤ mem.size; omega)
      (Or.inl (by decide)), hfree]
  have hkeep := MemoryWords.snapshot (liquidateEntryMemory mem I.calldata) 96 23
    (by decide) (by rw [liquidateEntryMemory_size hmem]; exact hmem)
  rcases midnightMarketCalldataDecoder_preserved
      (by change R.length + 6 + 25 ≤ 1024; omega) hsmall (by rw [hh]; omega)
      (by decide) (by decide) hf (by jump_dest) hkeep (by decide)
      (by rw [memoryWordSnapshot_length]; decide) ha2 rd2 with
    ⟨hnone, hrev⟩ | ⟨m, hm, hfit, mem', root, aw3, k3, C3, hroot, hstored,
      hf3, hmem3, hk3, ha3, rd3⟩
  · refine Or.inl ⟨hdecode.trans ?_, hrev⟩
    unfold decodeLiquidateArguments
    rw [hd]
    cases hm : decodeMarketData I.calldata (UInt256.ofNat 4 + calldataWord I.calldata 4).toNat with
    | none => rfl
    | some m =>
      have hc := hnone m hm
      change ¬ 1120 + 160 * m.collaterals.length < 2^64 at hc
      dsimp only [bind, Option.bind]
      rw [if_neg (fun h ↦ hc h.2)]
  · refine Or.inr ⟨m, ?_, hd.trans hm, h292, hsmall, hv, hdata, mem', root, aw3, k3, C3,
      hroot, hstored, hf3, hmem3, hk3, ha3, rd3⟩
    rw [hdecode]
    unfold decodeLiquidateArguments
    rw [hd, hm]
    change 1120 + 160 * m.collaterals.length < 2^64 at hfit
    dsimp only [bind, Option.bind]
    rw [if_pos ⟨hv, hfit⟩, decodeCalldataBytes_valid hdata]

set_option maxHeartbeats 800000 in
theorem midnightLiquidateEntry {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 32 ≤ 1024) (h4 : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hselector : ¬ 0xac9650d8 = (bytesToWord (I.calldata.toList.take 4)).toNat)
    (hmem : 832 ≤ mem.size) (hfree : memLoad (UInt256.ofNat 64) mem = ⟨832⟩)
    (ha : MemoryAccounting mem aw C)
    (rd : RD fork midnightBytecode I g s0 ⟨4983⟩ R mem aw rdata σ k C) :
    (config.externalABI.decodeCalldata? liquidateNames liquidateTypes I.calldata = none ∧
      RDrev fork midnightBytecode g s0) ∨
    (∃ m, config.externalABI.decodeCalldata? liquidateNames liquidateTypes I.calldata =
        some (liquidateArguments m (calldataWord I.calldata 36) (calldataWord I.calldata 68)
          (calldataWord I.calldata 100) (AccountAddress.ofNat (calldataWord I.calldata 132).toNat)
          (calldataWord I.calldata 164) (AccountAddress.ofNat (calldataWord I.calldata 196).toNat)
          (AccountAddress.ofNat (calldataWord I.calldata 228).toNat)
          (I.calldata.extract (calldataArgumentPointer I.calldata 260).toNat
            ((calldataArgumentPointer I.calldata 260).toNat +
              (calldataArgumentLength I.calldata 260).toNat))) ∧
      292 ≤ I.calldata.size ∧ I.calldata.size < 2^255 ∧ LiquidateScalarsValid I.calldata ∧
      CalldataArgumentValid true I.calldata 260 ∧
      ∃ mem' root aw' k' C', root.toNat = 1120 + 160 * m.collaterals.length ∧
        MarketStored mem' ⟨832⟩ ⟨1088⟩ root m ∧ memLoad (UInt256.ofNat 64) mem' = root ∧
        root.toNat ≤ mem'.size ∧
        MemoryWords mem' 96 (memoryWordSnapshot (liquidateEntryMemory mem I.calldata) 96 23) ∧
        MemoryAccounting mem' aw' C' ∧ RD fork midnightBytecode I g s0 ⟨4356⟩
          (⟨832⟩ :: ⟨5161⟩ :: calldataArgumentLength I.calldata 260 ::
            calldataWord I.calldata 132 :: calldataArgumentPointer I.calldata 260 ::
            calldataWord I.calldata 196 :: calldataWord I.calldata 164 :: R)
          mem' aw' rdata σ k' C') := by
  rcases midnightLiquidateEntry_decoded hstack h4 hsize hselector hmem hfree ha rd with
    hbad | ⟨m, hdec, _, h292, hsmall, hv, hdata, rest⟩
  · exact Or.inl hbad
  · exact Or.inr ⟨m, hdec, h292, hsmall, hv, hdata, rest⟩

end Benchmarks.Midnight
