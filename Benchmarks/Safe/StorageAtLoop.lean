import Benchmarks.Safe.StorageAtSource
import Benchmarks.Safe.StorageAtAllocation

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open safeRuntimeBlocks

namespace Benchmarks.Safe

set_option maxRecDepth 2000

theorem safeStorageAtIndexAddress (i : Nat) (hi : i ≤ 2 ^ 64 - 1) :
    ((UInt256.ofNat 128 + UInt256.mul (UInt256.ofNat i) (UInt256.ofNat 32)) +
      UInt256.ofNat 32).toNat = 160 + 32 * i := by
  rw [u256_add_comm _ (UInt256.ofNat 32), u256_add_comm (UInt256.ofNat 128),
    u256_mul_comm]
  exact safeAddressArrayIndexAddress i hi

set_option maxHeartbeats 800000 in
theorem safeStorageAtLoopNext (evm : EVM.State) {g s0 k C aw mem rdata i n offset}
    {R : List UInt256}
    (h : RD safeBytecode evm.executionEnv g s0 ⟨3131⟩
      (UInt256.ofNat i :: ⟨128⟩ :: ⟨96⟩ :: UInt256.ofNat n :: offset :: R)
      mem aw rdata evm.accountMap k C)
    (hov : R.length + 9 ≤ 1024) (hn : n ≤ 2 ^ 64 - 1) (hi : i < n) :
    ∃ aw' k' C', RD safeBytecode evm.executionEnv g s0 ⟨3131⟩
      (UInt256.ofNat (i + 1) :: ⟨128⟩ :: ⟨96⟩ :: UInt256.ofNat n :: offset :: R)
      (writeWord mem (160 + 32 * i) (storageAtWord evm offset i))
      aw' rdata evm.accountMap k' C' := by
  have hiw := ulit_toNat' i (by change i < 2 ^ 256; omega)
  have hnw := ulit_toNat' n (by change n < 2 ^ 256; omega)
  have h₁ := safeRuntime_block_3131_fallthrough (by simp; omega)
    (by rw [ult_one (by rw [hiw, hnw]; exact hi)]; decide) h
  obtain ⟨aw', k', C', h'⟩ := safeRuntime_block_3140_packed hov (by jump_dest) h₁
  have hp := safeStorageAtIndexAddress i (by omega)
  change (((⟨128⟩ : UInt256) + UInt256.mul (UInt256.ofNat i) (UInt256.ofNat 32)) +
    UInt256.ofNat 32).toNat = 160 + 32 * i at hp
  have hslot : (evm.accountMap.get? evm.executionEnv.codeOwner |>.option (⟨0⟩ : UInt256)
      (fun ac ↦ ac.storage.getD (UInt256.ofNat i + offset) ⟨0⟩)) =
      storageAtWord evm offset i := by
    rw [u256_add_comm (UInt256.ofNat i) offset]
    rfl
  simp only [safeRuntime_block_3140_stack, safeRuntime_block_3140_memory,
    hp, hslot, show UInt256.ofNat 1 + UInt256.ofNat i = UInt256.ofNat (i + 1) from
      u256_one_add_ofNat i] at h'
  exact ⟨_, _, _, h'⟩

theorem safeStorageAtLoopExit {I g s0 σ k C aw mem rdata n offset ret}
    {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨3131⟩
      (UInt256.ofNat n :: ⟨128⟩ :: ⟨96⟩ :: UInt256.ofNat n :: offset :: ret :: R)
      mem aw rdata σ k C)
    (hov : R.length + 8 ≤ 1024) (hret : (D_J safeBytecode 0).contains ret = true) :
    ∃ k' C', RD safeBytecode I g s0 ret (⟨128⟩ :: R) mem aw rdata σ k' C' := by
  have h₁ := safeRuntime_block_3131_taken (by simp; omega)
    (by rw [ult_zero (by omega)]; decide) (by jump_dest) h
  have h₂ := safeRuntime_block_3160 (by omega) hret h₁
  exact ⟨_, _, h₂⟩

theorem safeStorageAtLoop (evm : EVM.State) {g s0 k C aw mem rdata n offset locals}
    {doneWords : List UInt256} {fuel : Nat} {ret : UInt256} {R : List UInt256}
    (h : RD safeBytecode evm.executionEnv g s0 ⟨3131⟩
      (UInt256.ofNat doneWords.length :: ⟨128⟩ :: ⟨96⟩ :: UInt256.ofNat n :: offset :: ret :: R)
      mem aw rdata evm.accountMap k C)
    (hov : R.length + 10 ≤ 1024)
    (hm : AddressArrayMemory mem n (doneWords ++ List.replicate fuel ⟨0⟩)
      (UInt256.ofNat (32 * n)))
    (hl : StorageAtLocals locals offset (UInt256.ofNat n) doneWords)
    (hn : n ≤ 2 ^ 64 - 1) (hf : doneWords.length + fuel = n)
    (hret : (D_J safeBytecode 0).contains ret = true) :
    ∃ words' locals' mem' aw' k' C',
      ExecStmt config { contract := contract, locals := locals } evm storageAtLoop
        (.ok { contract := contract, locals := locals' } evm) ∧
      StorageAtLocals locals' offset (UInt256.ofNat n) words' ∧
      AddressArrayMemory mem' n words' (UInt256.ofNat (32 * n)) ∧
      RD safeBytecode evm.executionEnv g s0 ret (⟨128⟩ :: R)
        mem' aw' rdata evm.accountMap k' C' := by
  induction fuel generalizing doneWords locals mem aw k C with
  | zero =>
      have he : doneWords.length = n := by omega
      obtain ⟨k', C', h'⟩ := safeStorageAtLoopExit (by simpa only [he] using h) (by omega) hret
      have hcond := safeStorageAtCondition evm hl
      rw [ulit_toNat' n (by change n < 2 ^ 256; omega)] at hcond
      refine ⟨doneWords, locals, mem, aw, k', C', .whileFalse ?_, hl, ?_, h'⟩
      · simpa only [he, lt_self_iff_false, decide_false] using hcond
      · simpa using hm
  | succ fuel ih =>
      have hi : doneWords.length < n := by omega
      have hcond := safeStorageAtCondition evm hl
      rw [ulit_toNat' n (by change n < 2 ^ 256; omega)] at hcond
      have hsrc := safeStorageAtStep evm hl (by change doneWords.length + 1 < 2 ^ 256; omega)
      obtain ⟨aw₁, k₁, C₁, h₁⟩ := safeStorageAtLoopNext evm h (by simp; omega) hn hi
      have hm₁ := hm.write doneWords.length (storageAtWord evm offset doneWords.length) hi
      have hset : (doneWords ++ List.replicate (fuel + 1) (⟨0⟩ : UInt256)).set
          doneWords.length (storageAtWord evm offset doneWords.length) =
          (doneWords ++ [storageAtWord evm offset doneWords.length]) ++
            List.replicate fuel ⟨0⟩ := by
        simp [List.set_append_right, List.replicate_succ, List.append_assoc]
      rw [hset] at hm₁
      obtain ⟨ws, ls, ms, a, k', C', hs, hls, hms, hr⟩ := ih
        (by simpa only [List.length_append, List.length_singleton] using h₁) hm₁
        (safeStorageAtNextLocals hl) (by
          simp only [List.length_append, List.length_singleton]
          omega)
      exact ⟨ws, ls, ms, a, k', C',
        .whileTrue (by simpa only [hi, decide_true] using hcond) hsrc hs,
        hls, hms, hr⟩

end Benchmarks.Safe
