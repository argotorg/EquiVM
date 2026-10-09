import Benchmarks.Safe.Memory
import Benchmarks.Safe.PackedAddress
import Benchmarks.Safe.Blocks.Runtime_005

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open safeRuntimeBlocks

namespace Benchmarks.Safe

def fallbackCallData (cd : ByteArray) (caller : AccountAddress) : ByteArray :=
  cd ++ ((EVM.word caller.val).toBytesBE.drop 12).toByteArray

def fallbackMemory (I : ExecutionEnv) : ByteArray :=
  safeRuntime_block_588_memory (ee := I) (mem := solcFreePtrMem)

def fallbackMemoryPrefix : ByteArray := solcFreePtrMem ++ ByteArray.zeroes 32

theorem fallbackMemoryPrefix_size : fallbackMemoryPrefix.size = 128 := by
  rw [fallbackMemoryPrefix, ByteArray.size_append, solcFreePtrMem_size, ByteArray_zeroes_size]

theorem fallbackMemory_eq (I : ExecutionEnv) (hn : I.calldata.size ≠ 0)
    (hsmall : I.calldata.size < 2 ^ 138) :
    fallbackMemory I = (fallbackMemoryPrefix ++ I.calldata) ++
      (UInt256.shiftLeft (UInt256.ofNat I.source.val) ⟨96⟩).toByteArray := by
  have hsize : I.calldata.size < UInt256.size := by
    exact lt_trans hsmall (by decide)
  have hf : memLoad (UInt256.ofNat 64) solcFreePtrMem = ⟨128⟩ := solcFreePtrMem_mload64
  have hadd : (⟨128⟩ + UInt256.ofNat I.calldata.size).toNat = 128 + I.calldata.size := by
    simpa using uadd_ofNat_toNat (a := 128) (b := I.calldata.size) (by decide) hsize (by
      change 128 + I.calldata.size < 2 ^ 256
      omega)
  have hc : I.calldata.write 0 solcFreePtrMem 128 I.calldata.size =
      fallbackMemoryPrefix ++ I.calldata := by
    rw [write_from_gap_eq' _ _ 0 128 _ hn (by omega)
      (by rw [solcFreePtrMem_size]; decide)
      (by rw [solcFreePtrMem_size]; exact lt_usize _ (by decide)),
      solcFreePtrMem_size]
    change (solcFreePtrMem ++ ByteArray.zeroes 32) ++
      I.calldata.extract 0 (0 + I.calldata.size) = _
    rw [Nat.zero_add, byteArray_extract_self]
    rfl
  simp only [fallbackMemory, safeRuntime_block_588_memory, hf, hadd,
    ulit_toNat' _ hsize, show (⟨0⟩ : UInt256).toNat = 0 from rfl,
    show (⟨128⟩ : UInt256).toNat = 128 from rfl, hc]
  exact writeWordAtEnd _ _ (by rw [ByteArray.size_append, fallbackMemoryPrefix_size])

theorem fallbackMemory_size (I : ExecutionEnv) (hn : I.calldata.size ≠ 0)
    (hsmall : I.calldata.size < 2 ^ 138) :
    (fallbackMemory I).size = 160 + I.calldata.size := by
  rw [fallbackMemory_eq I hn hsmall, ByteArray.size_append, ByteArray.size_append,
    fallbackMemoryPrefix_size, toByteArray_size]
  omega

theorem fallbackMemory_read (I : ExecutionEnv) (hn : I.calldata.size ≠ 0)
    (hsmall : I.calldata.size < 2 ^ 138) :
    (fallbackMemory I).readWithPadding 128 (I.calldata.size + 20) =
      fallbackCallData I.calldata I.source := by
  rw [readWithPadding_eq_extract_unbounded _ _ _ (by omega)
    (by rw [fallbackMemory_size I hn hsmall]; omega), fallbackMemory_eq I hn hsmall,
    ByteArray.append_assoc, extract_append_right_window _ _ _ _
      (by rw [fallbackMemoryPrefix_size]), fallbackMemoryPrefix_size]
  simp only [Nat.sub_self, Nat.add_sub_cancel_left]
  rw [extract_append_span _ _ _ _ (by omega) (by omega),
    byteArray_extract_self, show I.calldata.size + 20 - I.calldata.size = 20 by omega]
  have hp := congrArg List.toByteArray (packedAddress_shifted_word I.source)
  rw [byteArray_toList_toByteArray] at hp
  exact congrArg (I.calldata ++ ·) hp

end Benchmarks.Safe
