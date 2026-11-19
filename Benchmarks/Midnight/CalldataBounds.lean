import Benchmarks.Midnight.MemoryDecodeBounds
import Benchmarks.Midnight.CalldataWordCopies

/-! Natural-number forms of Solidity's bounded calldata guards. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open ABI.Solc08Calldata

namespace Benchmarks.Midnight

-- LIBRARY CANDIDATE: signed ABI head checks for nonnegative lengths and addresses.
theorem solcSLT_sub_small {finish start need : Nat}
    (he : finish < 2^255) (hs : start < 2^255) (hn : need < 2^255) :
    solcSLT (solcSub finish start) need = decide (finish < start + need) := by
  have he' := ulit_toNat' finish (lt_size_of_lt_sign he)
  have hs' := ulit_toNat' start (lt_size_of_lt_sign hs)
  have hn' := ulit_toNat' need (lt_size_of_lt_sign hn)
  have hc := signedDecodeCheck (finish := UInt256.ofNat finish)
    (start := UInt256.ofNat start) (need := need)
    (by rw [he']; exact he) (by rw [hs']; exact hs) hn
  simpa only [solcSub, hn', he', hs'] using solcSLT_of_check hc

theorem solcSLT_small {a b : Nat} (ha : a < 2^255) (hb : b < 2^255) :
    solcSLT a b = decide (a < b) := by
  have ha' := ulit_toNat' a (lt_size_of_lt_sign ha)
  have hb' := ulit_toNat' b (lt_size_of_lt_sign hb)
  unfold solcSLT EVM.signed
  change decide ((if (UInt256.ofNat a).toNat < 2^255 then
      ((UInt256.ofNat a).toNat : Int) else ((UInt256.ofNat a).toNat : Int) - 2^256) <
    (if (UInt256.ofNat b).toNat < 2^255 then
      ((UInt256.ofNat b).toNat : Int) else ((UInt256.ofNat b).toNat : Int) - 2^256)) = _
  simp only [ha', hb', ha, hb, if_true, Int.ofNat_lt]

theorem solcReadNat_bounded {bytes : ByteArray} {start : Nat}
    (hbound : start + 32 ≤ bytes.size) (hsize : bytes.size < EVM.wordModulus) :
    solcReadNat bytes.toList start = (calldataWord bytes start).toNat := by
  have hl : bytes.toList.length = bytes.size := by
    simp only [byteArray_toList_eq, Array.length_toList]; rfl
  rw [solcReadNat, solcReadBytes_bounded (by rw [hl]; exact hbound)
    (by rw [hl]; exact hsize), decode_word_at_eq_any bytes start hbound]

theorem solcSLT_low_high {a b : Nat} (ha : a < 2^255)
    (hb : 2^255 ≤ b) (hbmod : b < UInt256.size) : solcSLT a b = false := by
  have ha' := ulit_toNat' a (lt_size_of_lt_sign ha)
  have hb' := ulit_toNat' b hbmod
  have hc := slt_zero_low_high (a := UInt256.ofNat a) (b := UInt256.ofNat b)
    (by rw [ha']; exact ha) (by rw [hb']; exact hb)
  simpa only [ha', hb'] using (solcSLT_of_check (bit := false) hc)

end Benchmarks.Midnight
