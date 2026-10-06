import Reasoning.ABI
import Benchmarks.Auction.UIntReturnDecoder
import Benchmarks.Auction.ErrorDecodeMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction


theorem errorReturnString_ok {out : ByteArray} (hv : ErrorDataValid out)
    (hb : out.size < 2 ^ 255) :
    ∃ value, ABI.decodeReturnValue? .string (out.extract 4 out.size) = some value := by
  have ht : out.toList.length = out.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have hx : (out.extract 4 out.size).toList = out.toList.drop 4 := by
    rw [extract_toList, ← ht, ← List.length_drop, List.take_length]
  have ho := readNat_drop4_zero_eq_calldataWord (cd := out) (by have h := hv.1; omega)
  have hl := readNat_drop4_dynamic_eq_calldataWord (cd := out)
    (by change 4 + (errorOffset out).toNat + 32 ≤ out.size; have h := hv.2.1.2; omega)
  have hpay := hv.2.2.2
  simp only [errorLength, errorOffset] at hpay
  have hp := readBytes_drop4_string_payload (cd := out) (by
    simp only [List.length_take, List.length_drop, ht]
    omega)
  refine ⟨_, decodeReturnString_of_reads (offset := (errorOffset out).toNat)
    (len := (errorLength out).toNat)
    (payload := ((out.toList.drop 4).drop ((errorOffset out).toNat + 32)).take
      (errorLength out).toNat) ?_ ?_ ?_ ?_ hv.2.1.1 hv.2.2.1⟩
  · rw [hx, List.length_drop, ht]
    omega
  · simpa only [hx, errorOffset] using ho
  · simpa only [hx, errorLength, errorOffset] using hl
  · simpa only [hx, errorLength, errorOffset] using hp

end Auction
