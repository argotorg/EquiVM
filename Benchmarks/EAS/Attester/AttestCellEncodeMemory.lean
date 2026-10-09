import Benchmarks.EAS.Attester.Common
import Benchmarks.EAS.Attester.AttestHeap
import Benchmarks.EAS.Attester.WordSequenceMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.EAS.Attester.Immutables attesterRuntimeBlocks

namespace Benchmarks.EAS.Attester

def attestCellEncodedHead (mem : ByteArray) (dst : Nat) : ByteArray :=
  writeCascade mem [(dst, ⟨0⟩), (dst + 32, ⟨0⟩), (dst + 64, ⟨1⟩),
    (dst + 96, ⟨0⟩), (dst + 128, ⟨192⟩), (dst + 192, ⟨32⟩)]

def attestCellEncodedPayload (mem : ByteArray) (dst : Nat) (input : UInt256) : ByteArray :=
  writeWord (attestCellEncodedHead mem dst) (dst + 224) input

def attestCellEncodedMemory (mem : ByteArray) (dst : Nat) (input : UInt256) : ByteArray :=
  writeCascade (attestCellEncodedPayload mem dst input) [(dst + 256, ⟨0⟩), (dst + 160, ⟨0⟩)]

theorem attestCellEncodedHead_prefix (mem : ByteArray) (dst : Nat) :
    MemoryPrefix mem (attestCellEncodedHead mem dst) dst := by
  apply memoryPrefix_sparse_cascade
  intro w hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl <;> exact .inl (by omega)

theorem attestCellEncodedMemory_prefix (mem : ByteArray) (dst : Nat) (input : UInt256) :
    MemoryPrefix mem (attestCellEncodedMemory mem dst input) dst :=
  ((attestCellEncodedHead_prefix mem dst).trans
    (memoryPrefix_sparse_writeWord _ _ _ input (.inl (by omega)))).trans
    (memoryPrefix_sparse_cascade _ _ _ (by
      intro w hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl <;> exact .inl (by omega)))

theorem attestCellEncodedMemory_size (mem : ByteArray) (dst : Nat) (input : UInt256) :
    (attestCellEncodedMemory mem dst input).size = max mem.size (dst + 288) := by
  simp only [attestCellEncodedMemory, attestCellEncodedPayload, attestCellEncodedHead,
    writeCascade, Reasoning.Theory.writeWord, wordWrite_size]
  omega

theorem attestCellEncodedHead_summary {mem : ByteArray} {limit ptr dst : Nat} {input : UInt256}
    (heap : AttestCellAt mem 96 limit ptr input) (hsize : limit ≤ mem.size)
    (hsep : limit ≤ dst) (hfit : dst + 288 < UInt256.size) :
    attesterRuntime_block_3109_memory (mem := mem) (x0 := UInt256.ofNat ptr)
      (x1 := UInt256.ofNat dst) = attestCellEncodedHead mem dst := by
  obtain ⟨hlo, hhi, data, hdlo, hdhi, h0, h32, h64, h96, h128, h160, hlen, hinput⟩ := heap
  simp only [attesterRuntime_block_3109_memory, ofNat_add_words]
  simp (disch :=
    (first | omega | (simp (disch := omega) only [wordWrite_size, ulit_toNat']; omega))) only
    [ulit_toNat', memLoad_write_disjoint, h0, h32, h64, h96, h128, hlen,
      u256_land_zero_left]
  rfl

theorem attestCellEncodedHead_stack {mem : ByteArray} {limit ptr dst : Nat} {input : UInt256}
    (heap : AttestCellAt mem 96 limit ptr input) (hsize : limit ≤ mem.size)
    (hsep : limit ≤ dst) (hfit : dst + 288 < UInt256.size) (R : List UInt256) :
    ∃ data, 96 ≤ data ∧ data + 64 ≤ limit ∧
      memLoad (UInt256.ofNat (data + 32)) mem = input ∧
      attesterRuntime_block_3109_stack (mem := mem) (x0 := UInt256.ofNat ptr)
        (x1 := UInt256.ofNat dst) (R := R) =
        [UInt256.ofNat 0, UInt256.ofNat 32, UInt256.ofNat data, UInt256.ofNat 0,
          UInt256.ofNat ptr, UInt256.ofNat dst] ++ R := by
  obtain ⟨hlo, hhi, data, hdlo, hdhi, h0, h32, h64, h96, h128, h160, hlen, hinput⟩ := heap
  refine ⟨data, hdlo, hdhi, hinput, ?_⟩
  simp only [attesterRuntime_block_3109_stack, ofNat_add_words]
  simp (disch :=
    (first | omega | (simp (disch := omega) only [wordWrite_size, ulit_toNat']; omega))) only
    [ulit_toNat', memLoad_write_disjoint, h0, h32, h64, h96, h128, hlen,
      u256_land_zero_left]
  rfl

end Benchmarks.EAS.Attester
