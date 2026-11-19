import Benchmarks.Midnight.ScalarDecode
import Benchmarks.Midnight.ABIWordDecode

/-! Bounded word copies used by Solidity's calldata value decoder. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open ABI.Solc08Calldata

namespace Benchmarks.Midnight

-- LIBRARY CANDIDATE: an in-bounds calldata copy needs no padding or address wrapping.
theorem solcReadBytes_bounded {bytes : List UInt8} {start len : Nat}
    (hbound : start + len ≤ bytes.length) (hsize : bytes.length < EVM.wordModulus) :
    solcReadBytes bytes start len = (bytes.drop start).take len := by
  have hs : start < EVM.wordModulus := by omega
  have hm : min len (bytes.length - start) = len := Nat.min_eq_left (by omega)
  simp only [solcReadBytes, Nat.mod_eq_of_lt hs, List.length_take, List.length_drop,
    hm, Nat.sub_self, List.replicate_zero, List.append_nil]

-- LIBRARY CANDIDATE: consecutive bounded word loads are one contiguous calldata slice.
theorem solcReadWords_bounded {bytes : List UInt8} {start count : Nat}
    (hbound : start + 32 * count ≤ bytes.length) (hsize : bytes.length < EVM.wordModulus) :
    solcReadWords bytes start count = (bytes.drop start).take (32 * count) := by
  induction count generalizing start with
  | zero => simp [solcReadWords]
  | succ n ih =>
    rw [solcReadWords, List.range_succ_eq_map]
    simp only [List.flatMap_cons, List.flatMap_map]
    have hstart : solcAdd start (32 * 0) = start := by
      have hs : start < EVM.wordModulus := by omega
      simp only [solcAdd, Nat.mul_zero, Nat.add_zero, Nat.mod_eq_of_lt hs]
    rw [hstart, solcReadBytes_bounded (by omega) hsize]
    have ht : (List.range n).flatMap (fun i ↦ solcReadBytes bytes (solcAdd start (32 * (i + 1))) 32) =
        solcReadWords bytes (start + 32) n := by
      unfold solcReadWords
      congr 1
      funext i
      apply congrArg (fun k ↦ solcReadBytes bytes k 32)
      unfold solcAdd
      congr 1
      omega
    rw [ht, ih (by omega)]
    rw [show 32 * (n + 1) = 32 + 32 * n by omega, List.take_add, List.drop_drop]

end Benchmarks.Midnight
