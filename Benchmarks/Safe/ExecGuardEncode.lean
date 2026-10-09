import Benchmarks.Safe.CalldataLengthRounding
import Benchmarks.Safe.ExecGuardEncodingMemory
import Benchmarks.Safe.Blocks.Runtime_049
import Benchmarks.Safe.Blocks.Runtime_050

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open safeRuntimeBlocks

namespace Benchmarks.Safe

set_option maxRecDepth 100000 in
theorem safeExecGuardEncode (tx : SafeTransaction) (signatures : ByteArray)
    {I g s0 σ k C aw mem rdata base src sigPtr} {sender ret : UInt256} {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨11256⟩
      (UInt256.ofNat base :: sender :: UInt256.ofNat sigPtr ::
        UInt256.ofNat tx.refundReceiver.val :: UInt256.ofNat tx.gasToken.val ::
        tx.gasPrice :: tx.baseGas :: tx.safeTxGas :: tx.operation ::
        UInt256.ofNat tx.payload.size :: UInt256.ofNat src :: tx.value ::
        UInt256.ofNat tx.target.val :: ret :: R) mem aw rdata σ k C)
    (hsig : BytesMemory mem sigPtr signatures)
    (ha : sigPtr + 32 + signatures.size ≤ base)
    (hin : src + tx.payload.size ≤ I.calldata.size) (hs : src < UInt256.size)
    (hb : base + 448 + ABI.paddedSize tx.payload.size + ABI.paddedSize signatures.size <
      UInt256.size)
    (ho : tx.operation.toNat < 2) (hov : R.length + 32 ≤ 1024)
    (hret : (D_J safeBytecode 0).contains ret = true) :
    ∃ words aw' k' C', words.length = (signatures.size + 31) / 32 ∧
      (wordBytes words).extract 0 signatures.size = signatures ∧
      RD safeBytecode I g s0 ret
        (UInt256.ofNat (base + 416 + ABI.paddedSize tx.payload.size +
          ABI.paddedSize signatures.size) :: R)
        (execGuardArgsMemory I.calldata mem base src tx sender signatures.size words)
        aw' rdata σ k' C' := by
  have hpad : tx.payload.size ≤ ABI.paddedSize tx.payload.size := by
    unfold ABI.paddedSize; omega
  have hpadSig : signatures.size ≤ ABI.paddedSize signatures.size := by
    unfold ABI.paddedSize; omega
  have hadd (a b : Nat) (hh : a + b < UInt256.size) :
      UInt256.ofNat a + UInt256.ofNat b = UInt256.ofNat (a + b) := by
    apply u256_inj
    rw [ulit_toNat' _ hh]
    exact uadd_ofNat_toNat (by omega) (by omega) hh
  have ht (n : Nat) (hh : n < UInt256.size) : (UInt256.ofNat n).toNat = n :=
    ulit_toNat' _ hh
  have hmask := roundedCalldataLengthMask tx.payload.size (by omega)
  have hhead : safeRuntime_block_11256_memory (ee := I) (mem := mem)
      (x0 := UInt256.ofNat base) (x9 := UInt256.ofNat tx.payload.size)
      (x10 := UInt256.ofNat src) (x11 := tx.value) (x12 := UInt256.ofNat tx.target.val) =
      execGuardHeadMemory I.calldata mem base src tx := by
    simp only [safeRuntime_block_11256_memory, safeAddressMask,
      hadd base 32 (by omega), hadd base 64 (by omega), hadd base 352 (by omega),
      hadd base 384 (by omega), hadd base tx.payload.size (by omega),
      hadd (base + tx.payload.size) 384 (by omega), ht base (by omega), ht src hs,
      ht tx.payload.size (by omega), ht (base + 32) (by omega), ht (base + 64) (by omega),
      ht (base + 352) (by omega), ht (base + 384) (by omega),
      ht (base + tx.payload.size + 384) (by omega)]
    simp only [execGuardHeadMemory, execGuardHeadWords, calldataBytesEncodedInto, writeWords,
      Reasoning.Theory.writeWord, Nat.add_assoc, Nat.reduceAdd,
      Nat.add_right_comm base tx.payload.size 384]
    rfl
  obtain ⟨_, _, _, h₁⟩ := safeRuntime_block_11256_packed (by simp; omega) (by jump_dest) h
  rw [hhead] at h₁
  simp only [safeRuntime_block_11256_stack, hmask, hadd base 96 (by omega),
    hadd base (ABI.paddedSize tx.payload.size) (by omega)] at h₁
  have hc : UInt256.lt tx.operation (UInt256.ofNat 2) ≠ UInt256.ofNat 0 := by
    simp [UInt256.lt, UInt256.fromBool, show tx.operation < UInt256.ofNat 2 from ho]
    decide
  have h₂ := safeRuntime_block_11224_taken (by simp; omega) hc (by jump_dest) h₁
  obtain ⟨_, _, _, h₃⟩ := safeRuntime_block_11252_packed (by simp; omega) (by jump_dest) h₂
  simp only [safeRuntime_block_11252_stack, safeRuntime_block_11252_memory,
    ht (base + 96) (by omega)] at h₃
  obtain ⟨_, _, _, h₄⟩ := safeRuntime_block_11331_packed (by simp; omega) (by jump_dest) h₃
  obtain ⟨_, _, _, h₅⟩ := safeRuntime_block_11370_packed (by simp; omega) (by jump_dest) h₄
  have hsub : UInt256.sub (UInt256.ofNat (base + ABI.paddedSize tx.payload.size))
      (UInt256.ofNat base) = UInt256.ofNat (ABI.paddedSize tx.payload.size) := by
    rw [← hadd _ _ (by omega), word_add_sub_left]
  have hm : execGuardPrefixMemory I.calldata mem base src tx =
      safeRuntime_block_11370_memory
        (mem := safeRuntime_block_11331_memory
          (mem := tx.operation.toByteArray.write 0
            (execGuardHeadMemory I.calldata mem base src tx) (base + 96) 32)
          (x2 := UInt256.ofNat base) (x6 := UInt256.ofNat tx.gasToken.val)
          (x7 := tx.gasPrice) (x8 := tx.baseGas) (x9 := tx.safeTxGas))
        (x0 := UInt256.ofNat (base + ABI.paddedSize tx.payload.size))
        (x2 := UInt256.ofNat base) (x5 := UInt256.ofNat tx.refundReceiver.val) := by
    simp only [safeRuntime_block_11370_memory, safeRuntime_block_11331_memory,
      safeAddressMask, hsub,
      hadd base 128 (by omega), hadd base 160 (by omega), hadd base 192 (by omega),
      hadd base 224 (by omega), hadd base 256 (by omega), hadd base 288 (by omega),
      hadd (ABI.paddedSize tx.payload.size) 384 (by omega),
      ht (base + 128) (by omega), ht (base + 160) (by omega), ht (base + 192) (by omega),
      ht (base + 224) (by omega), ht (base + 256) (by omega), ht (base + 288) (by omega),
      execGuardPrefixMemory, execGuardMiddleWords, writeWords, Reasoning.Theory.writeWord,
      Nat.add_assoc, Nat.reduceAdd, Nat.add_comm (ABI.paddedSize tx.payload.size) 384]
  rw [← hm] at h₅
  simp only [safeRuntime_block_11370_stack,
    hadd (base + ABI.paddedSize tx.payload.size) 384 (by omega)] at h₅
  rw [show base + ABI.paddedSize tx.payload.size + 384 =
    base + 384 + ABI.paddedSize tx.payload.size by omega] at h₅
  let m := execGuardPrefixMemory I.calldata mem base src tx
  have hp := execGuardPrefixMemory_preserves I.calldata mem base src tx hin
  have hsig' : BytesMemory m sigPtr signatures := by
    apply hsig.preserved (by omega) hp.size
    intro off count hlo hhi
    exact hp.read off count (by omega) (by omega) (by have := hsig.available; omega)
  let words := memoryWords m (sigPtr + 32) ((signatures.size + 31) / 32)
  have hn : words.length = (signatures.size + 31) / 32 := memoryWords_length _ _ _
  have hi : sigPtr + 32 + 32 * words.length ≤ m.size := by
    rw [hn]; have := hsig'.available; omega
  have hbytes : (wordBytes words).extract 0 signatures.size = signatures := by
    rw [memoryWords_prefix _ _ _ _ (by rw [hn] at hi; exact hi) (by omega), hsig'.payload]
  obtain ⟨_, _, _, h₆⟩ := safeMemoryBytesEncodeInto words h₅ hsig'.length
    (memoryWords_view _ _ _) hn (by rw [hn]; unfold ABI.paddedSize; omega) hi
    (by rw [hn]; unfold ABI.paddedSize at hb ⊢; omega) (by simp; omega) (by jump_dest)
  obtain ⟨_, _, _, h₇⟩ := safeRuntime_block_11413_packed (by simp; omega) (by jump_dest) h₆
  simp only [safeRuntime_block_11413_stack, safeRuntime_block_11413_memory, safeAddressMask,
    hadd base 320 (by omega), ht (base + 320) (by omega)] at h₇
  obtain ⟨_, _, _, h₈⟩ := safeRuntime_block_11438_packed (by simp; omega) hret h₇
  simp only [safeRuntime_block_11438_stack] at h₈
  have he : base + 384 + ABI.paddedSize tx.payload.size + 32 + 32 * words.length =
      base + 416 + ABI.paddedSize tx.payload.size + ABI.paddedSize signatures.size := by
    rw [hn]; unfold ABI.paddedSize; omega
  rw [he] at h₈
  exact ⟨words, _, _, _, hn, hbytes, h₈⟩

end Benchmarks.Safe
