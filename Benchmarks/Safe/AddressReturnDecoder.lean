import Reasoning.ABI

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

namespace Benchmarks.Safe

-- LIBRARY CANDIDATE: modern ABI decoding of a canonical address return word.
theorem decodeReturnAddressLong {out : ByteArray} (hl : 32 ≤ out.size)
    (hb : out.size < 2 ^ 255) (hc : (calldataWord out 0).toNat < EVM.addressModulus) :
    ABI.decodeReturnValue? (.elem .address) out =
      some (.address (AccountAddress.ofNat (calldataWord out 0).toNat)) := by
  have hlen : out.toList.length = out.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have hword := decode_word_at_eq_any out 0 (by omega)
  have h32 : ((out.toList.drop 0).take 32).length = 32 := by
    simp only [List.drop_zero, List.length_take, hlen]
    omega
  unfold ABI.decodeReturnValue?
  rw [decodeReturnValues_scalarWords_eq (by decide)]
  rw [if_neg (by simp only [List.isEmpty_cons, hlen]; omega)]
  simp only [decodeScalarWords?, decodeScalarWord_address_ok h32 (by rw [hword]; exact hc),
    hword, bind, Option.bind]

end Benchmarks.Safe
