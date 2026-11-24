import Benchmarks.Safe.ViaIR.ContractSignatureMemory
import Benchmarks.Safe.ViaIR.Blocks.Runtime_034
import Benchmarks.Safe.ViaIR.Blocks.Runtime_037
import Benchmarks.Safe.ViaIR.IRMemoryAllocation

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.ViaIR.RuntimeBlocks

namespace Benchmarks.Safe.ViaIR

set_option maxRecDepth 2000

theorem contractSignatureArgs_free {mem : ByteArray} {ptr len : Nat} {hash : UInt256}
    {words : List UInt256} (hf : memLoad ⟨64⟩ mem = UInt256.ofNat ptr)
    (hm : 96 ≤ mem.size) (hp : 96 ≤ ptr) :
    memLoad ⟨64⟩ (wordBytesArgsMemory (writeWord mem (ptr + 32) signatureMagicWord)
      (ptr + 36) len hash words) = UInt256.ofNat ptr := by
  rw [memLoadReadWord, show (⟨64⟩ : UInt256).toNat = 64 from rfl,
    wordBytesArgsMemory_preserved _ _ _ _ _ _ _ (by rw [writeWord_sparse_size]; omega)
      (by omega), writeWordReadBelow _ _ _ _ _ hm (by omega),
    ← show (⟨64⟩ : UInt256).toNat = 64 from rfl, ← memLoadReadWord, hf]

theorem safeContractSignatureArgs (words : List UInt256)
    {I g s0 σ k C aw mem rdata ptr src len} {hash owner last sig : UInt256} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨7707⟩
      (UInt256.ofNat src :: last :: owner :: sig :: hash :: R) mem aw rdata σ k C)
    (hf : memLoad ⟨64⟩ mem = UInt256.ofNat ptr)
    (hl : memLoad (UInt256.ofNat src) mem = UInt256.ofNat len)
    (hw : WordArrayMemory mem (src + 32) words) (hn : words.length = (len + 31) / 32)
    (hin : src + 32 + 32 * words.length ≤ mem.size)
    (ha : src + 32 + 32 * words.length ≤ ptr + 32)
    (hb : ptr + 164 + 32 * words.length < UInt256.size) (hov : R.length + 23 ≤ 1024) :
    ∃ aw' k' C', RD fork safeBytecode I g s0 ⟨7757⟩
      (UInt256.ofNat (ptr + 132 + 32 * words.length) :: UInt256.ofNat ptr :: ⟨7771⟩ ::
        UInt256.ofNat ptr :: UInt256.ofNat (ptr + 32) :: ⟨0⟩ :: ⟨0⟩ ::
        last :: owner :: sig :: hash :: R)
      (wordBytesArgsMemory (writeWord mem (ptr + 32) signatureMagicWord)
        (ptr + 36) len hash words) aw' rdata σ k' C' := by
  have hadd (n : Nat) (hh : n ≤ 100) :
      UInt256.ofNat ptr + UInt256.ofNat n = UInt256.ofNat (ptr + n) := by
    apply u256_inj
    rw [ulit_toNat' _ (by omega)]
    exact uadd_ofNat_toNat (by omega) (by omega) (by omega)
  let head := writeWords (writeWord mem (ptr + 32) signatureMagicWord) (ptr + 36) [hash, ⟨64⟩]
  have hm : safeRuntime_block_7707_memory (mem := mem) (x4 := hash) = head := by
    change memLoad (UInt256.ofNat 64) mem = UInt256.ofNat ptr at hf
    have hmagic : UInt256.shiftLeft (UInt256.ofNat 185818431) (UInt256.ofNat 225) =
        signatureMagicWord := by decide +kernel
    simp only [safeRuntime_block_7707_memory, hf, hmagic, hadd 32 (by decide),
      hadd 36 (by decide), hadd 68 (by decide), ulit_toNat' (ptr + 32) (by omega),
      ulit_toNat' (ptr + 36) (by omega), ulit_toNat' (ptr + 68) (by omega)]
    simp only [head, writeWords, Reasoning.Theory.writeWord]
    rfl
  have hload : memLoad (UInt256.ofNat src) head = UInt256.ofNat len := by
    rw [memLoadReadWord, ulit_toNat' src (by omega),
      writeWords_readBelow _ _ src 32 _ (by rw [writeWord_sparse_size]; omega) (by omega),
      writeWordReadBelow _ _ _ _ _ (by omega) (by omega),
      ← ulit_toNat' src (by omega), ← memLoadReadWord]
    exact hl
  have hwords : WordArrayMemory head (src + 32) words := by
    intro i hi
    rw [writeWords_readBelow _ _ _ _ _ (by rw [writeWord_sparse_size]; omega) (by omega),
      writeWordReadBelow _ _ _ _ _ (by omega) (by omega)]
    exact hw i hi
  have h₁ := safeRuntime_block_7707 (by simp; omega) (by jump_dest) h
  rw [hm] at h₁
  change memLoad (UInt256.ofNat 64) mem = UInt256.ofNat ptr at hf
  simp only [safeRuntime_block_7707_stack, hf, hadd 100 (by decide), hadd 32 (by decide)] at h₁
  obtain ⟨aw', k', C', h₂⟩ := safeMemoryBytesEncodeInto words h₁ hload hwords hn (by omega)
    (by dsimp [head]; rw [writeWords_size_nonempty _ _ _ (by simp), writeWord_sparse_size];
        omega) (by omega) (by simp; omega) (by jump_dest)
  rw [show ptr + 100 + 32 + 32 * words.length = ptr + 132 + 32 * words.length by omega] at h₂
  exact ⟨aw', k', C', h₂⟩

theorem safeContractSignatureEncodedMemory {mem : ByteArray} {ptr len : Nat} {hash : UInt256}
    {words : List UInt256} (hn : words.length = (len + 31) / 32)
    (hb : contractSignatureCallEnd ptr len + 32 < UInt256.size) :
    safeRuntime_block_7757_memory
      (mem := wordBytesArgsMemory (writeWord mem (ptr + 32) signatureMagicWord)
        (ptr + 36) len hash words)
      (x0 := UInt256.ofNat (ptr + 132 + 32 * words.length)) (x1 := UInt256.ofNat ptr)
      (x3 := UInt256.ofNat ptr) =
      writeWord (wordBytesArgsMemory (writeWord mem (ptr + 32) signatureMagicWord)
        (ptr + 36) len hash words) ptr (UInt256.ofNat (contractSignatureCallLength len)) := by
  have he : UInt256.ofNat (ptr + 132 + 32 * words.length) =
      UInt256.ofNat ptr + UInt256.ofNat (132 + 32 * words.length) := by
    rw [wordOfNatAdd _ _ (by
      dsimp [contractSignatureCallEnd, ABI.paddedSize] at hb
      rw [hn]; omega)]
    congr 1
    omega
  have hlen : UInt256.ofNat (132 + 32 * words.length) + UInt256.lnot (UInt256.ofNat 31) =
      UInt256.ofNat (contractSignatureCallLength len) := by
    have hnot : (UInt256.lnot (UInt256.ofNat 31)).toNat = UInt256.size - 32 := by decide
    have hsize : 132 + 32 * words.length < UInt256.size := by
      dsimp [contractSignatureCallEnd, ABI.paddedSize] at hb
      rw [hn]; omega
    apply u256_inj
    rw [uadd_toNat, ulit_toNat' _ hsize, hnot,
      Nat.mod_eq_sub_mod (by
        have : 32 ≤ UInt256.size := by decide
        omega),
      Nat.mod_eq_of_lt (by omega),
      ulit_toNat' _ (by
        dsimp [contractSignatureCallLength, ABI.paddedSize]
        rw [hn] at hsize
        omega)]
    dsimp [contractSignatureCallLength, ABI.paddedSize]
    rw [hn]
    have : 0 < UInt256.size := by decide
    omega
  simp only [safeRuntime_block_7757_memory, he, word_add_sub_left, hlen,
    ulit_toNat' ptr (by dsimp [contractSignatureCallEnd] at hb; omega)]
  rfl

theorem safeContractSignatureEncode {I g s0 σ k C aw mem rdata ptr len}
    {hash owner last sig : UInt256} {words : List UInt256} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨7757⟩
      (UInt256.ofNat (ptr + 132 + 32 * words.length) :: UInt256.ofNat ptr :: ⟨7771⟩ ::
        UInt256.ofNat ptr :: UInt256.ofNat (ptr + 32) :: ⟨0⟩ :: ⟨0⟩ ::
        last :: owner :: sig :: hash :: R)
      (wordBytesArgsMemory (writeWord mem (ptr + 32) signatureMagicWord)
        (ptr + 36) len hash words) aw rdata σ k C)
    (hn : words.length = (len + 31) / 32)
    (hb : contractSignatureCallEnd ptr len + 32 < UInt256.size) (hov : R.length + 14 ≤ 1024) :
    RDrev fork safeBytecode g s0 ∨
      ∃ aw' k' C', contractSignatureCallEnd ptr len < 2 ^ 64 ∧
        RD fork safeBytecode I g s0 ⟨7771⟩
          (UInt256.ofNat ptr :: UInt256.ofNat (ptr + 32) :: ⟨0⟩ :: ⟨0⟩ ::
            last :: owner :: sig :: hash :: R)
          (contractSignatureEncodedMemory mem ptr len hash words) aw' rdata σ k' C' := by
  obtain ⟨aw₁, k₁, C₁, h₁⟩ := safeRuntime_block_7757_packed (by simp; omega)
    (by jump_dest) h
  rw [safeContractSignatureEncodedMemory hn hb] at h₁
  have he : UInt256.ofNat (ptr + 132 + 32 * words.length) =
      UInt256.ofNat ptr + UInt256.ofNat (132 + 32 * words.length) := by
    rw [wordOfNatAdd _ _ (by
      dsimp [contractSignatureCallEnd, ABI.paddedSize] at hb
      rw [hn]; omega)]
    congr 1
    omega
  simp only [safeRuntime_block_7757_stack, he, word_add_sub_left] at h₁
  have hround : ptr + ABI.paddedSize (132 + 32 * words.length) =
      contractSignatureCallEnd ptr len := by
    simp only [contractSignatureCallEnd, ABI.paddedSize, hn]
    omega
  obtain hrev | ⟨aw', k', C', ha, h₂⟩ := safeIRAllocateTrace h₁
    (by dsimp [contractSignatureCallEnd, ABI.paddedSize] at hb; rw [hn]; omega)
    (by rw [hround]; omega) (by simp; omega) (by jump_dest)
  · exact .inl hrev
  rw [hround] at ha h₂
  exact .inr ⟨aw', k', C', ha, h₂⟩

end Benchmarks.Safe.ViaIR
