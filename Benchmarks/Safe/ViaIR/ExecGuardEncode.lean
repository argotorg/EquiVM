import Benchmarks.Safe.ViaIR.CalldataLengthRounding
import Benchmarks.Safe.ViaIR.ExecGuardEncodingMemory
import Benchmarks.Safe.ViaIR.ExecGuardCallMemory
import Benchmarks.Safe.ViaIR.ExecTransactionCalldataFacts
import Benchmarks.Safe.ViaIR.IRLengthCheck
import Benchmarks.Safe.ViaIR.Blocks.Runtime_027
import Benchmarks.Safe.ViaIR.Blocks.Runtime_041

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.ViaIR.RuntimeBlocks

namespace Benchmarks.Safe.ViaIR

set_option maxRecDepth 2000
set_option maxHeartbeats 1000000

theorem safeExecGuardEncode (p : ExecTransactionInput)
    {I g s0 σ k C aw mem rdata ptr src sigPtr} {guard hash : UInt256} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨5462⟩
      ([UInt256.ofNat sigPtr, UInt256.ofNat p.tx.target.val, UInt256.ofNat src,
        UInt256.ofNat p.tx.refundReceiver.val, guard, UInt256.ofNat p.tx.gasToken.val,
        hash, UInt256.ofNat p.tx.payload.size] ++ R) mem aw rdata σ k C)
    (hc : ExecTransactionCalldataFields I.calldata p)
    (hf : memLoad ⟨64⟩ mem = UInt256.ofNat ptr) (hsig : BytesMemory mem sigPtr p.signatures)
    (ha : sigPtr + 32 + p.signatures.size ≤ ptr)
    (hin : src + p.tx.payload.size ≤ I.calldata.size) (hs : src < UInt256.size)
    (hb : ptr + 452 + ABI.paddedSize p.tx.payload.size + ABI.paddedSize p.signatures.size <
      UInt256.size)
    (ho : p.tx.operation.toNat < 2) (hov : R.length + 32 ≤ 1024) :
    ∃ words aw' k' C', words.length = (p.signatures.size + 31) / 32 ∧
      (wordBytes words).extract 0 p.signatures.size = p.signatures ∧
      RD fork safeBytecode I g s0 ⟨5637⟩
        ([UInt256.ofNat (ptr + 420 + ABI.paddedSize p.tx.payload.size +
            ABI.paddedSize p.signatures.size), UInt256.ofNat ptr, UInt256.ofNat ptr,
          ⟨0⟩, UInt256.ofNat ptr, UInt256.ofNat p.tx.target.val, UInt256.ofNat src,
          UInt256.ofNat p.tx.refundReceiver.val, guard, UInt256.ofNat p.tx.gasToken.val,
          hash, UInt256.ofNat p.tx.payload.size] ++ R)
        (memoryBytesEncodedInto
          (execGuardPrefixMemory I.calldata (writeWord mem ptr execGuardSelectorWord)
            (ptr + 4) src p.tx)
          (ptr + 388 + ABI.paddedSize p.tx.payload.size) p.signatures.size words)
        aw' rdata σ k' C' := by
  have hpad : p.tx.payload.size ≤ ABI.paddedSize p.tx.payload.size := by
    unfold ABI.paddedSize; omega
  have hpadSig : p.signatures.size ≤ ABI.paddedSize p.signatures.size := by
    unfold ABI.paddedSize; omega
  have hadd (a b : Nat) (hh : a + b < UInt256.size) :
      UInt256.ofNat a + UInt256.ofNat b = UInt256.ofNat (a + b) := wordOfNatAdd _ _ hh
  have ht (n : Nat) (hh : n < UInt256.size) : (UInt256.ofNat n).toNat = n :=
    ulit_toNat' _ hh
  change memLoad (UInt256.ofNat 64) mem = UInt256.ofNat ptr at hf
  have hselector : UInt256.shiftLeft (UInt256.ofNat 989355433) (UInt256.ofNat 225) =
      execGuardSelectorWord := by decide +kernel
  have hhead : safeRuntime_block_5462_memory (ee := I) (mem := mem)
      (x1 := UInt256.ofNat p.tx.target.val) (x2 := UInt256.ofNat src)
      (x7 := UInt256.ofNat p.tx.payload.size) =
      execGuardHeadMemory I.calldata (writeWord mem ptr execGuardSelectorWord)
        (ptr + 4) src p.tx := by
    simp only [safeRuntime_block_5462_memory, hf, safeAddressMask, hselector,
      show uInt256OfByteArray (I.calldata.readBytes (UInt256.ofNat 36).toNat 32) =
        p.tx.value from hc.value,
      hadd ptr 4 (by omega), hadd ptr 36 (by omega), hadd ptr 68 (by omega),
      hadd ptr 356 (by omega), hadd 388 ptr (by omega),
      hadd ptr p.tx.payload.size (by omega), hadd (ptr + p.tx.payload.size) 388 (by omega),
      ht ptr (by omega), ht src hs, ht p.tx.payload.size (by omega), ht (ptr + 4) (by omega),
      ht (ptr + 36) (by omega), ht (ptr + 68) (by omega), ht (ptr + 356) (by omega),
      ht (388 + ptr) (by omega), ht (ptr + p.tx.payload.size + 388) (by omega)]
    simp only [execGuardHeadMemory, execGuardHeadWords, calldataBytesEncodedInto, writeWords,
      Reasoning.Theory.writeWord, Nat.add_assoc, Nat.reduceAdd,
      Nat.add_right_comm ptr p.tx.payload.size 388, Nat.add_comm 388 ptr]
    rfl
  obtain ⟨aw₁, k₁, C₁, h₁⟩ := safeRuntime_block_5462_packed (by simp; omega) h
  rw [hhead] at h₁
  simp only [safeRuntime_block_5462_stack, hf] at h₁
  have h₂ := safeRuntime_block_5550 (by simp; omega) (by jump_dest) h₁
  have hmask := roundedCalldataLengthMask p.tx.payload.size (by omega)
  simp only [safeRuntime_block_5550_stack, u256_land_comm (UInt256.lnot (UInt256.ofNat 31)),
    hmask, hadd ptr 100 (by omega), hadd ptr (ABI.paddedSize p.tx.payload.size) (by omega)] at h₂
  have hop : uInt256OfByteArray (I.calldata.readBytes (UInt256.ofNat 100).toNat 32) =
      p.tx.operation := hc.operation
  rw [hop] at h₂
  have h₃ := safeRuntime_block_8837_fallthrough (by simp; omega)
    (by rw [ult_one (by exact ho)]; rfl) h₂
  obtain ⟨aw₄, k₄, C₄, h₄⟩ := safeRuntime_block_8848_packed (by simp; omega)
    (by jump_dest) h₃
  simp only [safeRuntime_block_8848_stack, safeRuntime_block_8848_memory,
    ht (ptr + 100) (by omega)] at h₄
  obtain ⟨aw₅, k₅, C₅, h₅⟩ := safeRuntime_block_5567_packed (by simp; omega)
    (by jump_dest) h₄
  have hsub : UInt256.sub (UInt256.ofNat (ptr + ABI.paddedSize p.tx.payload.size))
      (UInt256.ofNat ptr) = UInt256.ofNat (ABI.paddedSize p.tx.payload.size) := by
    rw [← hadd _ _ (by omega), word_add_sub_left]
  have hoff : UInt256.lnot (UInt256.ofNat 3) +
      (UInt256.ofNat 388 + UInt256.ofNat (ABI.paddedSize p.tx.payload.size)) =
      UInt256.ofNat (384 + ABI.paddedSize p.tx.payload.size) := by
    rw [hadd _ _ (by omega)]
    change UInt256.lnot ⟨3⟩ + UInt256.ofNat (388 + ABI.paddedSize p.tx.payload.size) = _
    rw [lnot3_add_returnSize (by omega) (by omega)]
    congr 1
    omega
  let m := execGuardPrefixMemory I.calldata (writeWord mem ptr execGuardSelectorWord)
    (ptr + 4) src p.tx
  have hmiddle : safeRuntime_block_5567_memory (ee := I)
      (mem := writeWord
        (execGuardHeadMemory I.calldata (writeWord mem ptr execGuardSelectorWord)
          (ptr + 4) src p.tx) (ptr + 100) p.tx.operation)
      (x0 := UInt256.ofNat (ptr + ABI.paddedSize p.tx.payload.size))
      (x1 := UInt256.ofNat 388) (x4 := UInt256.ofNat ptr)
      (x10 := UInt256.ofNat p.tx.refundReceiver.val)
      (x12 := UInt256.ofNat p.tx.gasToken.val) = m := by
    simp only [safeRuntime_block_5567_memory, safeAddressMask, hsub, hoff,
      show uInt256OfByteArray (I.calldata.readBytes (UInt256.ofNat 132).toNat 32) =
        p.tx.safeTxGas from hc.safeTxGas,
      show uInt256OfByteArray (I.calldata.readBytes (UInt256.ofNat 164).toNat 32) =
        p.tx.baseGas from hc.baseGas,
      show uInt256OfByteArray (I.calldata.readBytes (UInt256.ofNat 196).toNat 32) =
        p.tx.gasPrice from hc.gasPrice,
      hadd ptr 132 (by omega), hadd ptr 164 (by omega), hadd ptr 196 (by omega),
      hadd ptr 228 (by omega), hadd ptr 260 (by omega), hadd ptr 292 (by omega),
      ht (ptr + 132) (by omega), ht (ptr + 164) (by omega), ht (ptr + 196) (by omega),
      ht (ptr + 228) (by omega), ht (ptr + 260) (by omega), ht (ptr + 292) (by omega),
      m, execGuardPrefixMemory, execGuardMiddleWords, writeWords, Reasoning.Theory.writeWord,
      Nat.add_assoc, Nat.reduceAdd]
  simp only [safeRuntime_block_5567_memory, Reasoning.Theory.writeWord] at hmiddle h₅
  rw [hmiddle] at h₅
  simp only [safeRuntime_block_5567_stack,
    hadd (ptr + ABI.paddedSize p.tx.payload.size) 388 (by omega)] at h₅
  rw [show ptr + ABI.paddedSize p.tx.payload.size + 388 =
    ptr + 388 + ABI.paddedSize p.tx.payload.size by omega] at h₅
  have hp := execGuardPrefixMemory_preserves I.calldata
    (writeWord mem ptr execGuardSelectorWord) (ptr + 4) src p.tx hin
  have hsig' : BytesMemory m sigPtr p.signatures := by
    apply hsig.preserved (by omega)
      (Nat.le_trans (by rw [writeWord_sparse_size]; omega) hp.size)
    intro off count hlo hhi
    rw [hp.read off count (by omega) (by omega)
      (by rw [writeWord_sparse_size]; have := hsig.available; omega),
      writeWordReadBelow _ _ _ _ _ (by have := hsig.available; omega) (by omega)]
  let words := memoryWords m (sigPtr + 32) ((p.signatures.size + 31) / 32)
  have hn : words.length = (p.signatures.size + 31) / 32 := memoryWords_length _ _ _
  have hm := execGuardPrefixMemory_size I.calldata
    (writeWord mem ptr execGuardSelectorWord) (ptr + 4) src p.tx hin
  have hi : sigPtr + 32 + 32 * words.length ≤ m.size := by
    rw [hn]
    change sigPtr + 32 + 32 * ((p.signatures.size + 31) / 32) ≤
      (execGuardPrefixMemory _ _ _ _ _).size
    rw [hm]
    omega
  have hbytes : (wordBytes words).extract 0 p.signatures.size = p.signatures := by
    rw [memoryWords_prefix _ _ _ _ (by rw [hn] at hi; exact hi) (by omega), hsig'.payload]
  obtain ⟨aw₆, k₆, C₆, h₆⟩ := safeMemoryBytesEncodeInto words h₅ hsig'.length
    (memoryWords_view _ _ _) hn (by rw [hn]; unfold ABI.paddedSize; omega) hi
    (by rw [hn]; unfold ABI.paddedSize at hb ⊢; omega) (by simp; omega) (by jump_dest)
  have he : ptr + 388 + ABI.paddedSize p.tx.payload.size + 32 + 32 * words.length =
      ptr + 420 + ABI.paddedSize p.tx.payload.size + ABI.paddedSize p.signatures.size := by
    rw [hn]; unfold ABI.paddedSize; omega
  rw [he] at h₆
  exact ⟨words, aw₆, k₆, C₆, hn, hbytes, h₆⟩

end Benchmarks.Safe.ViaIR
