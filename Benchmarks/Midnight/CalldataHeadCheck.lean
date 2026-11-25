import Benchmarks.Midnight.MarketEntryDecode
import Benchmarks.Midnight.MemoryDecodeBounds
import Benchmarks.Midnight.CalldataArgumentSlice

/-! The shifted signed guard used before decoding a dynamic calldata tuple. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open ABI.Solc08Calldata

namespace Benchmarks.Midnight

set_option maxRecDepth 2000

-- LIBRARY CANDIDATE: move the selector displacement into the subtracted pointer.
theorem lnot3_add_sub_word (finish relative : UInt256) :
    UInt256.lnot ⟨3⟩ + UInt256.sub finish relative =
      UInt256.sub finish (UInt256.ofNat 4 + relative) := by
  apply u256_inj
  change ((UInt256.lnot ⟨3⟩).val + (finish.val - relative.val)).val =
    (finish.val - ((UInt256.ofNat 4).val + relative.val)).val
  rw [show (UInt256.lnot ⟨3⟩).val = -(UInt256.ofNat 4).val from by decide +kernel]
  congr 1
  simp only [sub_eq_add_neg, neg_add_rev]
  rw [add_comm (-(UInt256.ofNat 4).val), add_assoc]

theorem decodeCalldataMarket_headerCheck {bytes : ByteArray} {m : MarketData}
    (hdec : decodeCalldataMarket bytes 4 = some m) :
    UInt256.slt (UInt256.lnot ⟨3⟩ + UInt256.sub (UInt256.ofNat bytes.size)
      (calldataWord bytes 4)) ⟨256⟩ = ⟨0⟩ := by
  dsimp only [decodeCalldataMarket] at hdec
  split at hdec
  · cases hdec
  rename_i hv
  have ho : (calldataWord bytes 4).toNat < 2^64 := by
    change ¬ (2^64 - 1 < _ ∨ 2^255 ≤ _) at hv
    omega
  have hs : bytes.size < 2^255 := by omega
  have hh : (UInt256.ofNat 4 + calldataWord bytes 4).toNat =
      4 + (calldataWord bytes 4).toNat :=
    calldataArgumentHead_toNat ho
  have hb := (decodeMarketData_success hdec).1
  rw [lnot3_add_sub_word]
  have hc := signedDecodeCheck (finish := UInt256.ofNat bytes.size)
    (start := UInt256.ofNat 4 + calldataWord bytes 4) (need := 256)
    (by rw [UInt256.toNat_ofNat_of_lt (by change _ < 2^256; omega)]; exact hs)
    (by rw [hh]; omega) (by decide)
  rw [UInt256.toNat_ofNat_of_lt (by change _ < 2^256; omega), hh,
    decide_eq_false (by omega)] at hc
  exact hc

end Benchmarks.Midnight
