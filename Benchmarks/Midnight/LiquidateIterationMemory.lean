import Benchmarks.Midnight.CollateralRecordMemory
import Benchmarks.Midnight.OracleMemory
import Benchmarks.Midnight.LiquidateLoopEntry

/-! The collateral record and oracle result allocated by one liquidation iteration. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

def liquidateIterationMemory (mem : ByteArray) (root : UInt256) (c : CollateralData)
    (out : ByteArray) : ByteArray :=
  oraclePriceMemory (collateralRecordMemory mem root c) (root + UInt256.ofNat 128) out

theorem liquidateIterationMemory_properties (mem : ByteArray) {root : UInt256}
    (c : CollateralData) {out : ByteArray} (hroot : root.toNat + 160 < 2^64)
    (hlower : 96 ≤ root.toNat) (h32 : 32 ≤ out.size) :
    MemoryPrefix mem (liquidateIterationMemory mem root c out) root.toNat ∧
    memLoad (UInt256.ofNat 64) (liquidateIterationMemory mem root c out) =
      root + UInt256.ofNat 160 ∧
    memLoad (root + UInt256.ofNat 128) (liquidateIterationMemory mem root c out) =
      calldataWord out 0 ∧
    MemoryWords (liquidateIterationMemory mem root c out) root.toNat c.words := by
  have hr : (root + UInt256.ofNat 128).toNat = root.toNat + 128 :=
    uadd_word_ofNat_toNat _ _ (by change _ < 2^256; omega)
  have hp := oraclePriceMemory_properties (collateralRecordMemory mem root c)
    (root + UInt256.ofNat 128) h32 (by omega)
  have hwords := collateralRecordMemory_words (ptr := root) mem c
    (by change _ < 2^256; omega)
  refine ⟨(collateralRecordMemory_prefix mem root c).trans (hp.2.2.2.mono (by omega)),
    ?_, hp.2.2.1, ?_⟩
  · simpa only [wordAddNat_add] using hp.2.1
  · apply hwords.preserve hp.2.2.2.size
    intro word hlo hhi
    exact hp.2.2.2.load word (hlower.trans hlo)
      (by change word.toNat + 32 ≤ root.toNat + 32 * 4 at hhi; omega)
      (hhi.trans hwords.size)

theorem liquidateIterationMemory_free_after_clear {mem : ByteArray} {root bitmap : UInt256}
    {c : CollateralData} {out : ByteArray} (hroot : root.toNat + 160 < 2^64)
    (hlower : 96 ≤ root.toNat) (hm : 96 ≤ mem.size) (h32 : 32 ≤ out.size) :
    memLoad (UInt256.ofNat 64)
        (liquidateBitmapMemory (liquidateIterationMemory mem root c out) bitmap) =
      root + UInt256.ofNat 160 := by
  have hp := liquidateIterationMemory_properties mem c hroot hlower h32
  rw [liquidateBitmapMemory_preserved bitmap (UInt256.ofNat 64)
    (hm.trans hp.1.size) (Or.inl (by decide)), hp.2.1]

end Benchmarks.Midnight
