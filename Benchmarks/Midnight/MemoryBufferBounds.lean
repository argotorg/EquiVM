import Benchmarks.Midnight.MarketEncodeMemory
import Benchmarks.Midnight.CollateralHeapMemory
import Benchmarks.Midnight.MemoryAccounting

/-! The ends of constructed buffers are covered by actual memory writes. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

theorem collateralStepMemory_end (mem : ByteArray) (ptr writePtr : UInt256)
    (c : CollateralData) :
    ptr.toNat + 128 ≤ (collateralStepMemory mem ptr writePtr c).size := by
  simp only [collateralStepMemory, collateralCopyMemory, CollateralData.words,
    writeWordArray, writeWord_sparse_size]
  omega

theorem collateralLoopMemory_end {mem : ByteArray} {ptr writePtr : UInt256}
    (cs : List CollateralData) (hb : ptr.toNat + 128 * cs.length < UInt256.size)
    (hnil : cs = [] → ptr.toNat ≤ mem.size) :
    ptr.toNat + 128 * cs.length ≤ (collateralLoopMemory mem ptr writePtr cs).size := by
  induction cs generalizing mem ptr writePtr with
  | nil => simpa only [List.length_nil, Nat.mul_zero, Nat.add_zero] using hnil rfl
  | cons c cs ih =>
    have hp : (ptr + UInt256.ofNat 128).toNat = ptr.toNat + 128 :=
      uadd_word_ofNat_toNat _ _ (by simp only [List.length_cons] at hb; omega)
    have hs := collateralStepMemory_end mem ptr writePtr c
    have hr := ih (mem := collateralStepMemory mem ptr writePtr c)
      (ptr := ptr + UInt256.ofNat 128) (writePtr := writePtr + UInt256.ofNat 32)
      (by rw [hp]; simp only [List.length_cons] at hb; omega)
      (fun _ ↦ by rw [hp]; exact hs)
    simpa only [collateralLoopMemory, List.length_cons, hp, Nat.mul_add,
      Nat.mul_one, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hr

theorem marketEncodeMemory_end (mem : ByteArray) (output : Nat) (m : MarketData)
    (hb : output + 288 + 128 * m.collaterals.length < UInt256.size) :
    output + 288 + 128 * m.collaterals.length ≤ (marketEncodeMemory mem output m).size := by
  have hs := (marketEncodeMemory_words mem output m hb).size
  simp only [List.length_append, List.length_cons, collateralWords_length,
    show (m.words (UInt256.ofNat 256)).length = 8 from rfl] at hs
  omega

end Benchmarks.Midnight
