import Benchmarks.EAS.Attester.ReturnArrayAllocTrace
import Benchmarks.EAS.Attester.StructAllocMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Reasoning.Theory

theorem wordArrayDataMemory_load {mem : ByteArray} {off i n j : Nat}
    (values : Nat → UInt256) (hj : j < n) (hfit : off + 32 * n < UInt256.size) :
    memLoad (UInt256.ofNat (off + 32 * j))
      (wordSequenceMemory mem off (wordArrayWords values i n)) = values (i + j) := by
  induction n generalizing mem off i j with
  | zero => omega
  | succ n ih =>
      cases j with
      | zero =>
          simp only [wordArrayWords, wordSequenceMemory, Nat.mul_zero, Nat.add_zero]
          rw [wordSequenceMemory_load_below _ (by rw [writeWord_sparse_size]; omega)
            (le_refl _) (by omega)]
          exact memLoad_write_same _ _ _ _ (ulit_toNat' _ (by omega))
      | succ j =>
          simp only [wordArrayWords, wordSequenceMemory]
          rw [show off + 32 * (j + 1) = off + 32 + 32 * j by omega]
          simpa only [Nat.add_assoc, Nat.add_comm 1 j] using
            ih (mem := writeWord mem off (values i)) (off := off + 32) (i := i + 1)
              (j := j) (by omega) (by omega)

end Reasoning.Theory

namespace Benchmarks.EAS.Attester

def wordArrayMemory (mem : ByteArray) (free n : Nat) (values : Nat → UInt256) : ByteArray :=
  wordSequenceMemory (wordArrayHeaderMemory mem free n) (free + 32) (wordArrayWords values 0 n)

theorem wordArrayHeaderMemory_size (mem : ByteArray) (free n : Nat) (hlo : 96 ≤ free) :
    (wordArrayHeaderMemory mem free n).size = max mem.size (free + 32) := by
  simp only [wordArrayHeaderMemory, writeWord_sparse_size]; omega

theorem wordArrayHeaderMemory_prefix (mem : ByteArray) (free n : Nat) :
    MemoryPrefix mem (wordArrayHeaderMemory mem free n) free :=
  (memoryPrefix_sparse_writeWord _ 64 free _ (.inr (by decide))).trans
    (memoryPrefix_sparse_writeWord _ free free _ (.inl (le_refl _)))

theorem wordArrayHeaderMemory_freePtr (mem : ByteArray) (free n : Nat) (hlo : 96 ≤ free) :
    memLoad (UInt256.ofNat 64) (wordArrayHeaderMemory mem free n) =
      UInt256.ofNat (free + 32 * (n + 1)) := by
  simp only [wordArrayHeaderMemory, Reasoning.Theory.writeWord]
  rw [memLoad_write_disjoint _ _ _ _ (by rw [wordWrite_size]; change 96 ≤ _; omega)
    (.inl hlo)]
  exact memLoad_write_same _ _ _ _ rfl

theorem wordArrayHeaderMemory_length (mem : ByteArray) (free n : Nat)
    (hfit : free < UInt256.size) :
    memLoad (UInt256.ofNat free) (wordArrayHeaderMemory mem free n) = UInt256.ofNat n :=
  memLoad_write_same _ _ _ _ (ulit_toNat' _ hfit)

theorem wordArrayMemory_size (mem : ByteArray) (free n : Nat) (values : Nat → UInt256)
    (hlo : 96 ≤ free) :
    (wordArrayMemory mem free n values).size = max mem.size (free + 32 * (n + 1)) := by
  rw [wordArrayMemory, wordSequenceMemory_size _
    (by rw [wordArrayHeaderMemory_size _ _ _ hlo]; omega), wordArrayWords_length,
    wordArrayHeaderMemory_size _ _ _ hlo]
  omega

theorem wordArrayMemory_freePtr (mem : ByteArray) (free n : Nat) (values : Nat → UInt256)
    (hlo : 96 ≤ free) :
    memLoad (UInt256.ofNat 64) (wordArrayMemory mem free n values) =
      UInt256.ofNat (free + 32 * (n + 1)) := by
  rw [wordArrayMemory, wordSequenceMemory_load_below _
    (by rw [wordArrayHeaderMemory_size _ _ _ hlo]; omega) (by omega) (by decide),
    wordArrayHeaderMemory_freePtr _ _ _ hlo]

theorem wordArrayMemory_length (mem : ByteArray) (free n : Nat) (values : Nat → UInt256)
    (hlo : 96 ≤ free) (hfit : free < UInt256.size) :
    memLoad (UInt256.ofNat free) (wordArrayMemory mem free n values) = UInt256.ofNat n := by
  rw [wordArrayMemory, wordSequenceMemory_load_below _
    (by rw [wordArrayHeaderMemory_size _ _ _ hlo]; omega) (le_refl _) hfit,
    wordArrayHeaderMemory_length _ _ _ hfit]

theorem wordArrayMemory_data (mem : ByteArray) (free n : Nat) (values : Nat → UInt256)
    {i : Nat} (hi : i < n) (hfit : free + 32 * (n + 1) < UInt256.size) :
    memLoad (UInt256.ofNat (free + 32 + 32 * i)) (wordArrayMemory mem free n values) =
      values i := by
  simpa only [wordArrayMemory, Nat.zero_add] using
    wordArrayDataMemory_load (mem := wordArrayHeaderMemory mem free n)
      (off := free + 32) (i := 0) values hi (by omega)

def returnArrayWords (out : ByteArray) (i : Nat) : UInt256 :=
  calldataWord out (returnArrayOffset out + 32 + 32 * i)

def returnArrayDecodedMemory (mem : ByteArray) (base : Nat) (out : ByteArray) : ByteArray :=
  wordArrayMemory (returnArrayInputMemory mem base out) (returnArrayFree base out)
    (returnArrayCount out) (returnArrayWords out)

theorem returnArrayHeaderMemory_data {mem out : ByteArray} {base i : Nat}
    (hlo : 96 ≤ base) (hb : base ≤ mem.size) (hc : ReturnArrayChecks out)
    (hi : i < returnArrayCount out) (hfit : base + out.size < UInt256.size) :
    memLoad (UInt256.ofNat (base + returnArrayOffset out + 32 + 32 * i))
      (wordArrayHeaderMemory (returnArrayInputMemory mem base out)
        (returnArrayFree base out) (returnArrayCount out)) = returnArrayWords out i := by
  have hp := wordArrayHeaderMemory_prefix (returnArrayInputMemory mem base out)
    (returnArrayFree base out) (returnArrayCount out)
  have hdata := hc.data
  have hf := (returnArrayFree_bounds base out).1
  rw [hp.load_preserved (by omega) (by omega)
    (by rw [returnArrayInputMemory_size hlo hb]; omega) (by omega)]
  rw [show base + returnArrayOffset out + 32 + 32 * i =
    base + (returnArrayOffset out + 32 + 32 * i) by omega]
  exact returnArrayInputMemory_load hlo hb (by omega) (by omega)

end Benchmarks.EAS.Attester
