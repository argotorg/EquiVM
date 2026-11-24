import Benchmarks.EAS.EAS.BytesLength
import Benchmarks.EAS.EAS.WordSequence

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

-- LIBRARY CANDIDATE: a finite sequence of consecutive storage words, with modular slots.
def storedWords (σ : AccountMap) (ee : ExecutionEnv) (slot : UInt256) : Nat → List UInt256
  | 0 => []
  | n + 1 => solcSlotWord σ ee slot :: storedWords σ ee (slot + ⟨1⟩) n

theorem storedWords_length (σ : AccountMap) (ee : ExecutionEnv) (slot : UInt256) (n : Nat) :
    (storedWords σ ee slot n).length = n := by
  induction n generalizing slot with
  | zero => rfl
  | succ n ih => simp only [storedWords, List.length_cons, ih]

-- LIBRARY CANDIDATE: advancing a long-byte storage slot uses modular addition.
theorem solidityBytesDataSlot_succ (slot : UInt256) (idx : Nat) :
    solidityBytesDataSlot slot idx + ⟨1⟩ = solidityBytesDataSlot slot (idx + 1) := by
  unfold solidityBytesDataSlot
  rw [u256_add_assoc, u256_add_comm (UInt256.ofNat idx) ⟨1⟩, u256_one_add_ofNat]

theorem storedWords_solidityBytes (evm : EVM.State) (slot : UInt256) (idx n : Nat) :
    wordBytes (storedWords evm.accountMap evm.executionEnv (solidityBytesDataSlot slot idx) n) =
      readSolidityBytesDataWordsFrom evm slot idx n := by
  induction n generalizing idx with
  | zero => rfl
  | succ n ih =>
    simp only [storedWords, wordBytes, readSolidityBytesDataWordsFrom,
      solidityBytesDataSlot_succ, ih, storageLoad_eq_solcSlotWord]

-- LIBRARY CANDIDATE: the one-word hash used for dynamic storage data.
theorem storedBytesDataHash (slot : UInt256) (mem : ByteArray) :
    keccakWord (UInt256.ofNat 0) (UInt256.ofNat 32) (Reasoning.Theory.writeWord mem 0 slot) =
      solidityBytesDataSlot slot 0 := by
  simp only [keccakWord, solidityBytesDataSlot, solidityBytesDataBaseSlot]
  change UInt256.ofNat (fromByteArrayBigEndian (KEC ((wordAt0Mem slot mem).readWithPadding 0 32))) =
    uInt256OfByteArray (KEC slot.toByteArray) + ⟨0⟩
  rw [wordAt0Mem_read0, uint256_add_zero_right, uInt256OfByteArray_eq]

theorem easStoredWords_loop {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {slot len bytesPtr ptr : UInt256} {R : List UInt256} (v : EASImmutables)
    (i n : Nat) (hstack : R.length + 11 ≤ 1024)
    (hbound : bytesPtr.toNat + i + 32 * n + 32 < UInt256.size)
    (hbefore : n > 0 → i + 32 * (n - 1) < len.toNat)
    (hafter : len.toNat ≤ i + 32 * n)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨6744⟩
      (slot :: len :: UInt256.ofNat i :: bytesPtr :: ptr :: bytesPtr :: R) mem aw rdata σ k C) :
    ∃ last aw' k' C', RD fork (deployedRuntime v) ee g s0 ⟨6752⟩
      (last :: len :: UInt256.ofNat (i + 32 * n) :: bytesPtr :: ptr :: bytesPtr :: R)
      (writeWordSequence mem (bytesPtr.toNat + i + 32) (storedWords σ ee slot n)) aw' rdata σ k' C' := by
  induction n generalizing mem aw k C slot i with
  | zero =>
    have hi : i < UInt256.size := by omega
    obtain ⟨aw', k', C', rd1⟩ := easBlocks.eas_block_6744_fallthrough_packed (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega)
      (ult_zero (by rw [ulit_toNat' _ hi]; simpa only [Nat.mul_zero, Nat.add_zero] using hafter)) rd
    exact ⟨slot, aw', k', C', rd1⟩
  | succ n ih =>
    have hi : i < UInt256.size := by omega
    have hlt : i < len.toNat := by have := hbefore (by omega); omega
    have rd1 := easBlocks.eas_block_6744_taken (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega)
      (by rw [ult_one (by rw [ulit_toNat' _ hi]; exact hlt)]; decide)
      (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
    obtain ⟨aw1, k1, C1, rd2⟩ := easBlocks.eas_block_6767_packed (immWords := wordsOf (immStore v)) hstack
      (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd1
    have hn : ((bytesPtr + UInt256.ofNat i) + UInt256.ofNat 32).toNat = bytesPtr.toNat + i + 32 := by
      have hb := uadd_word_ofNat_toNat bytesPtr i (by omega)
      rw [uadd_word_ofNat_toNat _ 32 (by rw [hb]; omega), hb]
    have hstep : UInt256.ofNat i + UInt256.ofNat 32 = UInt256.ofNat (i + 32) := by
      exact (u256_add_comm _ _).trans (u256_32_add_ofNat i)
    simp only [easBlocks.eas_block_6767_stack, hstep] at rd2
    change RD fork (deployedRuntime v) ee g s0 ⟨6744⟩
      ((slot + ⟨1⟩) :: len :: UInt256.ofNat (i + 32) :: bytesPtr :: ptr :: bytesPtr :: R)
      (Reasoning.Theory.writeWord mem ((bytesPtr + UInt256.ofNat i) + UInt256.ofNat 32).toNat
        (solcSlotWord σ ee slot)) aw1 rdata σ k1 C1 at rd2
    rw [hn] at rd2
    obtain ⟨last, aw2, k2, C2, rd3⟩ := ih (i + 32) (by omega)
      (by intro hn; have := hbefore (by omega); omega) (by omega) rd2
    refine ⟨last, aw2, k2, C2, ?_⟩
    simpa only [storedWords, writeWordSequence, show i + 32 * (n + 1) = i + 32 + 32 * n by omega,
      show bytesPtr.toNat + i + 32 + 32 = bytesPtr.toNat + (i + 32) + 32 by omega] using rd3

end Benchmarks.EAS.EAS
