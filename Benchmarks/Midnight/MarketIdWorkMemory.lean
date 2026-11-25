import Benchmarks.Midnight.MarketIdTrace

/-! Heap preservation, free pointer, and hash result of the complete ID calculation. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

theorem marketIdPointers {root : UInt256} (m : MarketData)
    (hb : root.toNat + 2 * m.encodingSize + 288 < 2^64) :
    (marketIdEncodedPtr root).toNat = root.toNat + 64 ∧
    (marketIdInitcodePtr root m).toNat = root.toNat + m.encodingSize + 96 ∧
    (marketIdPreimagePtr root m).toNat = root.toNat + 2 * m.encodingSize + 160 := by
  have he : (marketIdEncodedPtr root).toNat = root.toNat + 64 :=
    uadd_word_ofNat_toNat _ _ (by change _ < 2^256; omega)
  have hc : (marketIdInitcodePtr root m).toNat = root.toNat + m.encodingSize + 96 := by
    rw [marketIdInitcodePtr, uadd_word_ofNat_toNat _ _ (by rw [he]; change _ < 2^256; omega), he]
    omega
  refine ⟨he, hc, ?_⟩
  rw [marketIdPreimagePtr, uadd_word_ofNat_toNat _ _ (by rw [hc]; change _ < 2^256; omega), hc]
  omega

theorem marketIdWorkMemory_prefix (mem : ByteArray) {root : UInt256} (m : MarketData)
    (hlo : 96 ≤ root.toNat) (hb : root.toNat + 2 * m.encodingSize + 288 < 2^64) :
    MemoryPrefix mem (marketIdWorkMemory mem root m) root.toNat := by
  rcases marketIdPointers m hb with ⟨he, hc, hh⟩
  let mem1 := sstore2PrefixMemory mem root
  let mem2 := marketBytesMemory mem1 (marketIdEncodedPtr root) m
  let mem3 := marketInitcodeMemory mem2 (marketIdInitcodePtr root m) root (marketIdEncodedPtr root) m
  have hp1 := sstore2PrefixMemory_prefix mem root
  have hp2 := marketBytesMemory_prefix mem1 (marketIdEncodedPtr root) m
  have hs1 := sstore2PrefixMemory_size mem root
  have he2 := marketBytesMemory_words mem1 m (root := marketIdEncodedPtr root)
    (by rw [he]; omega) (by rw [he]; change _ < 2^256; omega)
  have hs2 : (marketIdEncodedPtr root).toNat + 32 + m.encodingSize ≤ mem2.size := by
    simpa only [← m.encodingSize_eq] using he2.size
  have hp3 := marketInitcodeMemory_prefix mem2 (marketIdInitcodePtr root m) root
    (marketIdEncodedPtr root) m (by have := hp2.size; omega) hs2
  have hp4 := marketIdMemory_prefix mem3 (marketIdPreimagePtr root m) m
  exact ((hp1.trans (hp2.mono (by rw [he]; omega))).trans
    (hp3.mono (by rw [hc]; omega))).trans (hp4.mono (by rw [hh]; omega))

theorem marketIdWorkMemory_free (mem : ByteArray) (root : UInt256) (m : MarketData) :
    memLoad (UInt256.ofNat 64) (marketIdWorkMemory mem root m) =
      marketIdPreimagePtr root m + UInt256.ofNat 128 := marketIdMemory_free _ _ _

theorem marketIdWorkMemory_length (mem : ByteArray) {root : UInt256} (m : MarketData)
    (hlo : 96 ≤ root.toNat) (hb : root.toNat + 2 * m.encodingSize + 288 < 2^64) :
    memLoad (marketIdPreimagePtr root m) (marketIdWorkMemory mem root m) = UInt256.ofNat 85 := by
  apply marketIdMemory_length
  rw [(marketIdPointers m hb).2.2]
  omega

theorem marketIdWorkMemory_hash (mem : ByteArray) {root : UInt256} (m : MarketData)
    (hlo : 96 ≤ root.toNat) (hb : root.toNat + 2 * m.encodingSize + 288 < 2^64) :
    keccakWord (marketIdPreimagePtr root m + UInt256.ofNat 32) (UInt256.ofNat 85)
      (marketIdWorkMemory mem root m) = m.id := by
  apply marketIdMemory_hash
  · rw [(marketIdPointers m hb).2.2]; omega
  · rw [(marketIdPointers m hb).2.2]; change _ < 2^256; omega

end Benchmarks.Midnight
