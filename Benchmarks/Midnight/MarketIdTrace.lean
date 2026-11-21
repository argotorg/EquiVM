import Benchmarks.Midnight.Sstore2Prefix
import Benchmarks.Midnight.MarketInitcodeTrace
import Benchmarks.Midnight.MarketIdPreimageTrace
import Benchmarks.Midnight.MemoryPrefixWindow

/-! The complete market-ID hashing path at the start of touchMarket. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

def marketIdEncodedPtr (root : UInt256) : UInt256 := root + UInt256.ofNat 64

def marketIdInitcodePtr (root : UInt256) (m : MarketData) : UInt256 :=
  marketIdEncodedPtr root + UInt256.ofNat (m.encodingSize + 32)

def marketIdPreimagePtr (root : UInt256) (m : MarketData) : UInt256 :=
  marketIdInitcodePtr root m + UInt256.ofNat (m.encodingSize + 64)

def marketIdWorkMemory (mem : ByteArray) (root : UInt256) (m : MarketData) : ByteArray :=
  let first := sstore2PrefixMemory mem root
  let encoded := marketBytesMemory first (marketIdEncodedPtr root) m
  let initcode := marketInitcodeMemory encoded (marketIdInitcodePtr root m) root
    (marketIdEncodedPtr root) m
  marketIdMemory initcode (marketIdPreimagePtr root m) m

set_option maxRecDepth 2000000 in
theorem midnightMarketIdTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw root ptr arrayPtr : UInt256} {σ : AccountMap} {k C : Nat}
    {R : List UInt256} (m : MarketData) (hstack : R.length + 25 ≤ 1024)
    (hm : MarketStored mem ptr arrayPtr root m)
    (hb : root.toNat + 2 * m.encodingSize + 288 < 2^64)
    (hfree : memLoad (UInt256.ofNat 64) mem = root)
    (rd : RD midnightBytecode I g s0 ⟨20557⟩ (ptr :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD midnightBytecode I g s0 ⟨20728⟩
      (marketIdPreimagePtr root m :: (marketIdPreimagePtr root m + UInt256.ofNat 32) ::
        ptr :: (ptr + UInt256.ofNat 32) :: R)
      (marketIdWorkMemory mem root m) aw' rdata σ k' C' := by
  let ep := marketIdEncodedPtr root
  let cp := marketIdInitcodePtr root m
  let hp := marketIdPreimagePtr root m
  let mem1 := sstore2PrefixMemory mem root
  let mem2 := marketBytesMemory mem1 ep m
  let mem3 := marketInitcodeMemory mem2 cp root ep m
  have hlo : 96 ≤ root.toNat := by
    have := hm.lower; have := hm.array; have := hm.extent; omega
  have he : ep.toNat = root.toNat + 64 :=
    uadd_word_ofNat_toNat _ _ (by change _ < 2^256; omega)
  have hc : cp.toNat = root.toNat + m.encodingSize + 96 := by
    rw [show cp = ep + UInt256.ofNat (m.encodingSize + 32) from rfl,
      uadd_word_ofNat_toNat _ _ (by rw [he]; change _ < 2^256; omega), he]
    omega
  have hh : hp.toNat = root.toNat + 2 * m.encodingSize + 160 := by
    rw [show hp = cp + UInt256.ofNat (m.encodingSize + 64) from rfl,
      uadd_word_ofNat_toNat _ _ (by rw [hc]; change _ < 2^256; omega), hc]
    omega
  have hmid : memLoad (ptr + UInt256.ofNat 32) mem = UInt256.ofNat m.midnight.val :=
    hm.words.load_offset ⟨1, by simp [MarketData.words]⟩ rfl
  have rd1 := midnightBlocks.midnight_block_20557 (by omega) (by jump_dest) rd
  simp only [midnightBlocks.midnight_block_20557_stack, hmid] at rd1
  obtain ⟨aw2, k2, C2, rd2⟩ := midnightSstore2Prefix
    (by simp only [List.length_cons]; omega) (by omega) hfree (by jump_dest) rd1
  change RD _ _ _ _ _ _ mem1 _ _ _ _ _ at rd2
  have hf1 : memLoad (UInt256.ofNat 64) mem1 = ep := sstore2PrefixMemory_free mem hlo
  have hm1 := hm.preserve (sstore2PrefixMemory_prefix mem root)
  have rd3 := midnightBlocks.midnight_block_20572 (by simp only [List.length_cons]; omega)
    (by jump_dest) rd2
  have he32 : (ep + UInt256.ofNat 32).toNat = ep.toNat + 32 :=
    uadd_word_ofNat_toNat _ _ (by rw [he]; change _ < 2^256; omega)
  simp only [midnightBlocks.midnight_block_20572_stack,
    midnightBlocks.midnight_block_20572_memory, hf1, he32] at rd3
  obtain ⟨aw4, k4, C4, rd4⟩ := midnightMarketBytesEncode m
    (by simp only [List.length_cons]; omega) hm1 (by rw [he]; omega)
    (by rw [he]; omega) (by jump_dest) rd3
  change RD _ _ _ _ _ _ mem2 _ _ _ _ _ at rd4
  have hp2 := marketBytesMemory_prefix mem1 ep m
  have hs1 : root.toNat + 64 ≤ mem1.size := sstore2PrefixMemory_size mem root
  have hpLen : memLoad root mem2 = UInt256.ofNat 11 := by
    rw [hp2.load root hlo (by rw [he]; omega) (by omega), sstore2PrefixMemory_length]
  have hpBytes : mem2.readWithPadding (root.toNat + 32) 11 = Model.sstore2Prefix := by
    rw [hp2.read_window (by omega) (by rw [he]) hs1 (by decide) (by decide),
      sstore2PrefixMemory_bytes]
  have hwords := marketBytesMemory_words mem1 m (root := ep) (by rw [he]; omega)
    (by rw [he]; change _ < 2^256; omega)
  have heSize : ep.toNat + 32 + m.encodingSize ≤ mem2.size := by
    simpa only [← m.encodingSize_eq] using hwords.size
  have heBytes : mem2.readWithPadding (ep.toNat + 32) m.encodingSize =
      wordArrayBytes m.encodedWords := by rw [m.encodingSize_eq]; exact hwords.read
  have hf2 : memLoad (UInt256.ofNat 64) mem2 = cp := marketBytesMemory_free mem1 ep m
  have heLen : memLoad ep mem2 = UInt256.ofNat m.encodingSize :=
    marketBytesMemory_length mem1 m (by rw [he]; omega)
  obtain ⟨aw5, k5, C5, rd5⟩ := midnightMarketInitcodeConcat m
    (by simp only [List.length_cons]; omega) (by rw [hc]; omega)
    (by have := hp2.size; omega) (by rw [hc]; omega) (by omega)
    (by rw [hc, he]; omega) hf2 hpLen heLen (by jump_dest) rd4
  change RD _ _ _ _ _ _ mem3 _ _ _ _ _ at rd5
  have hcBytes : mem3.readWithPadding (cp.toNat + 32) (11 + m.encodingSize) = m.initcode :=
    marketInitcodeMemory_bytes mem2 m (by rw [hc]; omega) (by omega)
      (by have := hp2.size; omega) heSize (by rw [hc, he]; omega) hpBytes heBytes
  have hf3 : memLoad (UInt256.ofNat 64) mem3 = hp := marketInitcodeMemory_free mem2 cp root ep m
  have hcLen : memLoad cp mem3 = UInt256.ofNat (11 + m.encodingSize) :=
    marketInitcodeMemory_length mem2 m (by rw [hc]; omega)
  obtain ⟨aw6, k6, C6, rd6⟩ := midnightMarketIdPreimage m
    (by simp only [List.length_cons]; omega) (by rw [hh]; omega)
    (by rw [hc]; change _ < 2^256; omega) (by change _ < 2^256; omega)
    hf3 hcLen hcBytes rd5
  exact ⟨aw6, k6, C6, rd6⟩

end Benchmarks.Midnight
