import Benchmarks.Safe.ViaIR.StorageAtSource
import Benchmarks.Safe.ViaIR.StorageAtAllocation

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.ViaIR.RuntimeBlocks

namespace Benchmarks.Safe.ViaIR

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
    (h : RD fork safeBytecode evm.executionEnv g s0 ⟨6165⟩
      (UInt256.ofNat i :: offset :: UInt256.ofNat n :: ⟨128⟩ :: R)
      mem aw rdata evm.accountMap k C)
    (hov : R.length + 9 ≤ 1024) (hn : n ≤ 2 ^ 64 - 1) (hi : i < n) :
    ∃ aw' k' C', RD fork safeBytecode evm.executionEnv g s0 ⟨6165⟩
      (UInt256.ofNat (i + 1) :: offset :: UInt256.ofNat n :: ⟨128⟩ :: R)
      (writeWord mem (160 + 32 * i) (storageAtWord evm offset i))
      aw' rdata evm.accountMap k' C' := by
  have hiw := ulit_toNat' i (by change i < 2 ^ 256; omega)
  have hnw := ulit_toNat' n (by change n < 2 ^ 256; omega)
  have h₁ := safeRuntime_block_6165_taken (by simp; omega)
    (by rw [ult_one (by rw [hiw, hnw]; exact hi)]; decide) (by jump_dest) h
  obtain ⟨aw', k', C', h'⟩ := safeRuntime_block_6194_packed hov (by jump_dest) h₁
  have hshift : UInt256.shiftLeft (UInt256.ofNat i) (UInt256.ofNat 5) =
      UInt256.mul (UInt256.ofNat i) (UInt256.ofNat 32) := by
    apply u256_inj
    have hs : (UInt256.shiftLeft (UInt256.ofNat i) (UInt256.ofNat 5)).toNat = 32 * i :=
      ushl5_ofNat_toNat i (by omega)
    rw [hs]
    change 32 * i = ((UInt256.ofNat i).toNat * 32) % UInt256.size
    rw [hiw, Nat.mod_eq_of_lt (by change i * 32 < 2 ^ 256; omega)]
    omega
  have hp := safeStorageAtIndexAddress i (by omega)
  have hslot : (evm.accountMap.get? evm.executionEnv.codeOwner |>.option (⟨0⟩ : UInt256)
      (fun ac ↦ ac.storage.getD (offset + UInt256.ofNat i) ⟨0⟩)) =
      storageAtWord evm offset i := by rfl
  have hinc : UInt256.ofNat i + UInt256.ofNat 1 = UInt256.ofNat (i + 1) := by
    rw [u256_add_comm]
    exact u256_one_add_ofNat i
  simp only [safeRuntime_block_6194_stack, safeRuntime_block_6194_memory,
    hshift, hslot, hinc] at h'
  change (((⟨128⟩ : UInt256) + UInt256.mul (UInt256.ofNat i) (UInt256.ofNat 32)) +
    UInt256.ofNat 32).toNat = 160 + 32 * i at hp
  rw [hp] at h'
  exact ⟨_, _, _, h'⟩

theorem safeStorageAtLoopExit {I g s0 σ k C aw mem rdata n offset}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨6165⟩
      (UInt256.ofNat n :: offset :: UInt256.ofNat n :: ⟨128⟩ :: R) mem aw rdata σ k C)
    (hov : R.length + 6 ≤ 1024) :
    ∃ k' C', RD fork safeBytecode I g s0 ⟨6173⟩
      (UInt256.ofNat n :: offset :: UInt256.ofNat n :: ⟨128⟩ :: R) mem aw rdata σ k' C' := by
  have h' := safeRuntime_block_6165_fallthrough (by simp; omega)
    (ult_zero (by omega)) h
  exact ⟨_, _, h'⟩

theorem safeStorageAtLoop (evm : EVM.State) {g s0 k C aw mem rdata n offset locals}
    {doneWords : List UInt256} {fuel : Nat} {R : List UInt256}
    (h : RD fork safeBytecode evm.executionEnv g s0 ⟨6165⟩
      (UInt256.ofNat doneWords.length :: offset :: UInt256.ofNat n :: ⟨128⟩ :: R)
      mem aw rdata evm.accountMap k C)
    (hov : R.length + 10 ≤ 1024)
    (hm : AddressArrayMemory mem n (doneWords ++ List.replicate fuel ⟨0⟩)
      (UInt256.ofNat (32 * n)))
    (hl : StorageAtLocals locals offset (UInt256.ofNat n) doneWords)
    (hn : n ≤ 2 ^ 64 - 1) (hf : doneWords.length + fuel = n) :
    ∃ words' locals' mem' aw' k' C',
      ExecStmt fork config { contract := contract, locals := locals } evm storageAtLoop
        (.ok { contract := contract, locals := locals' } evm) ∧
      StorageAtLocals locals' offset (UInt256.ofNat n) words' ∧
      AddressArrayMemory mem' n words' (UInt256.ofNat (32 * n)) ∧
      RD fork safeBytecode evm.executionEnv g s0 ⟨6173⟩
        (UInt256.ofNat n :: offset :: UInt256.ofNat n :: ⟨128⟩ :: R)
        mem' aw' rdata evm.accountMap k' C' := by
  induction fuel generalizing doneWords locals mem aw k C with
  | zero =>
      have he : doneWords.length = n := by omega
      obtain ⟨k', C', h'⟩ := safeStorageAtLoopExit (by simpa only [he] using h) (by omega)
      have hcond := safeStorageAtCondition evm hl
      rw [ulit_toNat' n (by change n < 2 ^ 256; omega)] at hcond
      refine ⟨doneWords, locals, mem, aw, k', C', .whileFalse ?_, hl, ?_, h'⟩
      · simpa only [he, lt_self_iff_false, decide_false] using hcond
      · simpa using hm
  | succ fuel ih =>
      have hi : doneWords.length < n := by omega
      have hcond := safeStorageAtCondition evm hl
      rw [ulit_toNat' n (by change n < 2 ^ 256; omega)] at hcond
      have hsrc := safeStorageAtStep (fork := fork) evm hl (by change doneWords.length + 1 < 2 ^ 256; omega)
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

end Benchmarks.Safe.ViaIR
