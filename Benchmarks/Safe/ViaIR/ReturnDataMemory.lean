import Benchmarks.Safe.ViaIR.ByteCopy
import Benchmarks.Safe.ViaIR.MemoryBytesDecoded
import Benchmarks.Safe.ViaIR.Blocks.Runtime_047
import Benchmarks.Safe.ViaIR.Blocks.Runtime_046
import Benchmarks.Safe.ViaIR.IRMemoryAllocation

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.ViaIR.RuntimeBlocks

namespace Benchmarks.Safe.ViaIR

-- LIBRARY CANDIDATE: store a returned byte buffer and reserve its rounded allocation.
def returnDataMemory (mem : ByteArray) (ptr : Nat) (out : ByteArray) : ByteArray :=
  out.write 0
    (writeWord (writeWord mem 64 (UInt256.ofNat (ptr + 32 + ABI.paddedSize out.size))) ptr
      (UInt256.ofNat out.size)) (ptr + 32) out.size

theorem returnDataMemory_size (mem out : ByteArray) (ptr : Nat) (hp : 96 ≤ ptr) :
    (returnDataMemory mem ptr out).size = max mem.size (ptr + 32 + out.size) := by
  rw [returnDataMemory, byteArray_write_all_size _ _ _ (by
    simp only [writeWord_sparse_size]; omega)]
  simp only [writeWord_sparse_size]
  omega

theorem returnDataMemory_free (mem out : ByteArray) (ptr : Nat) (hp : 96 ≤ ptr) :
    memLoad ⟨64⟩ (returnDataMemory mem ptr out) =
      UInt256.ofNat (ptr + 32 + ABI.paddedSize out.size) := by
  apply memLoad_of_wordRead
  change (returnDataMemory mem ptr out).readWithPadding 64 32 = _
  rw [returnDataMemory, copyWindowReadBelow _ _ _ _ _ _ _ (by omega)
      (by simp only [writeWord_sparse_size]; omega) (by omega),
    writeWordReadBelow _ _ _ _ _ (by rw [writeWord_sparse_size]; omega) hp,
    writeWord_sparse_read_back]

theorem returnDataMemory_length (mem out : ByteArray) (ptr : Nat) :
    (returnDataMemory mem ptr out).readWithPadding ptr 32 =
      (UInt256.ofNat out.size).toByteArray := by
  rw [returnDataMemory, copyWindowReadBelow _ _ _ _ _ _ _ (by omega)
    (by simp only [writeWord_sparse_size]; omega) (by omega), writeWord_sparse_read_back]

theorem returnDataMemory_word (mem out : ByteArray) (ptr : Nat) (hl : 32 ≤ out.size) :
    (returnDataMemory mem ptr out).readWithPadding (ptr + 32) 32 =
      (calldataWord out 0).toByteArray := by
  rw [returnDataMemory, copyWindow_read_word out _ 0 (ptr + 32) out.size 0
    (by omega) (by omega) (by simp only [writeWord_sparse_size]; omega) (by omega)]
  rw [readWithPadding_eq_extract out 0 hl]
  exact (calldataWord_bytes hl).symm

theorem returnDataMemory_preserved (mem out : ByteArray) (ptr off count : Nat)
    (hin : off + count ≤ mem.size) (hl : 96 ≤ off) (hh : off + count ≤ ptr) :
    (returnDataMemory mem ptr out).readWithPadding off count =
      mem.readWithPadding off count := by
  rw [returnDataMemory, copyWindowReadBelow _ _ _ _ _ _ _ (by omega)
    (by simp only [writeWord_sparse_size]; omega) (by omega),
    writeWordReadBelow _ _ _ _ _ (by rw [writeWord_sparse_size]; omega) hh,
    writeWordReadAbove _ _ _ _ _ hin hl]

theorem safeReturnDataMemory {mem out : ByteArray} {ptr : Nat}
    (hb : ptr + out.size + 64 < UInt256.size) :
    safeRuntime_block_10413_memory
      (mem := writeWord mem 64 (UInt256.ofNat (ptr + 32 + ABI.paddedSize out.size)))
      (rdata := out) (x0 := UInt256.ofNat out.size) (x2 := UInt256.ofNat ptr) =
      returnDataMemory mem ptr out := by
  have h32 : (UInt256.ofNat ptr + UInt256.ofNat 32).toNat = ptr + 32 :=
    uadd_ofNat_toNat (by omega) (by decide) (by omega)
  simp only [safeRuntime_block_10413_memory, h32, ulit_toNat' ptr (by omega),
    ulit_toNat' out.size (by omega), returnDataMemory, Reasoning.Theory.writeWord]
  rfl

set_option maxRecDepth 2000 in
theorem safeIRReturnBufferTrace {I g s0 σ k C aw mem ptr}
    {out : ByteArray} {ret : UInt256} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨10382⟩ (ret :: R) mem aw out σ k C)
    (hf : memLoad ⟨64⟩ mem = UInt256.ofNat ptr)
    (hb : ptr + out.size + 64 < UInt256.size) (hov : R.length + 11 ≤ 1024)
    (hret : (D_J safeBytecode 0).contains ret = true) :
    RDrev fork safeBytecode g s0 ∨
      ∃ aw' k' C', RD fork safeBytecode I g s0 ret
        ((if out.size = 0 then ⟨96⟩ else UInt256.ofNat ptr) :: R)
        (if out.size = 0 then mem else returnDataMemory mem ptr out) aw' out σ k' C' ∧
        (ptr < 2 ^ 64 → (if out.size = 0 then ptr else
          ptr + 32 + ABI.paddedSize out.size) < 2 ^ 64) := by
  have hlarge : 2 ^ 64 + 128 < UInt256.size := by decide
  by_cases hz : out.size = 0
  · have h₁ := safeRuntime_block_10382_taken (by simp; omega)
      (by rw [hz]; decide) (by jump_dest) h
    have h₂ := safeRuntime_block_10424 (by simp; omega) hret h₁
    exact .inr ⟨_, _, _, by simpa only [safeRuntime_block_10424_stack,
      hz, if_true] using h₂,
      by simpa only [hz, if_true] using (id : ptr < 2 ^ 64 → ptr < 2 ^ 64)⟩
  have hne : UInt256.ofNat out.size ≠ ⟨0⟩ := by
    intro he
    have he' := congrArg UInt256.toNat he
    rw [ulit_toNat' out.size (by omega)] at he'
    exact hz he'
  have hc : UInt256.isZero (UInt256.ofNat out.size) = ⟨0⟩ := isZero_eq_zero_of_ne hne
  have h₁ := safeRuntime_block_10382_fallthrough (by simp; omega) hc h
  have h₂ := safeRuntime_block_10389 (by simp; omega) (by jump_dest) h₁
  have hmax : UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64))
      (UInt256.ofNat 1) = UInt256.ofNat (2 ^ 64 - 1) := by decide +kernel
  by_cases hsmall : out.size < 2 ^ 64
  swap
  · have hg : UInt256.gt (UInt256.ofNat out.size) (UInt256.ofNat (2 ^ 64 - 1)) =
        ⟨1⟩ := ugt_one (by
      rw [ulit_toNat' out.size (by omega), ulit_toNat' (2 ^ 64 - 1) (by decide)]; omega)
    have h₃ := safeRuntime_block_7181_taken (by simp; omega)
      (by rw [hmax, hg]; decide) (by jump_dest) h₂
    exact .inl (safeRuntime_block_7161 (by simp; omega) h₃)
  have hg : UInt256.gt (UInt256.ofNat out.size) (UInt256.ofNat (2 ^ 64 - 1)) =
      ⟨0⟩ := ugt_zero (by
    rw [ulit_toNat' out.size (by omega), ulit_toNat' (2 ^ 64 - 1) (by decide)]; omega)
  have h₃ := safeRuntime_block_7181_fallthrough (by simp; omega) (by rw [hmax]; exact hg) h₂
  have h₄ := safeRuntime_block_7196 (by simp; omega) (by jump_dest) h₃
  have hr : UInt256.ofNat 32 + UInt256.land (UInt256.lnot (UInt256.ofNat 31))
      (UInt256.ofNat 31 + UInt256.ofNat out.size) =
      UInt256.ofNat (32 + ABI.paddedSize out.size) := by
    rw [u256_land_comm, u256_add_comm (UInt256.ofNat 31),
      roundedCalldataLengthMask _ (by omega), wordOfNatAdd _ _ (by
        dsimp [ABI.paddedSize]; omega)]
  have h₅ := safeRuntime_block_10399 (by simp; omega) (by jump_dest) h₄
  change memLoad (UInt256.ofNat 64) mem = UInt256.ofNat ptr at hf
  simp only [safeRuntime_block_10399_stack, hf, hr] at h₅
  have hround : ptr + ABI.paddedSize (32 + ABI.paddedSize out.size) =
      ptr + 32 + ABI.paddedSize out.size := by
    dsimp [ABI.paddedSize]
    omega
  obtain hrev | ⟨_, _, _, hfit, h₆⟩ := safeIRAllocateTrace h₅
    (by dsimp [ABI.paddedSize]; omega) (by rw [hround]; dsimp [ABI.paddedSize]; omega)
    (by simp; omega) (by jump_dest)
  · exact .inl hrev
  rw [hround] at h₆
  obtain ⟨aw', k', C', h₇⟩ := safeRuntime_block_10413_packed (by simp; omega)
    (by rw [ulit_toNat' out.size (by omega)]; change 0 + out.size ≤ out.size; omega)
    hret h₆
  rw [safeReturnDataMemory hb] at h₇
  exact .inr ⟨aw', k', C', by simpa only [safeRuntime_block_10413_stack,
    hz, if_false] using h₇,
    fun _ ↦ by simpa only [hz, if_false, hround] using hfit⟩

end Benchmarks.Safe.ViaIR
