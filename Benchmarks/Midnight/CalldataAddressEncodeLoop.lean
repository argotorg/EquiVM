import Benchmarks.Midnight.MemoryFunding
import Benchmarks.Midnight.CalldataAddressEncodeStep
import Benchmarks.Midnight.CalldataArrayWords
import Benchmarks.Midnight.CollateralLoopMemory

/-! The address-array encoder loop, including its element-validation failures. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

theorem midnightCalldataAddressEncodeLoopFunded {credit : Nat} {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw index count ptr output ret : UInt256} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} (n : Nat) (hstack : R.length + 15 ≤ 1024)
    (hcount : count.toNat = index.toNat + n)
    (hptr : ptr.toNat + 32 * n < UInt256.size)
    (hout : output.toNat + 32 * n < UInt256.size)
    (hret : (D_J midnightBytecode 0).contains ret = true)
    (ha : MemoryFunding credit mem aw C)
    (rd : RD midnightBytecode I g s0 ⟨19561⟩
      (index :: count :: ptr :: output :: ret :: R) mem aw rdata σ k C) :
    (¬ CanonicalAddressWords (calldataArrayWords I.calldata n ptr.toNat) ∧
      RDrev midnightBytecode g s0) ∨
    (CanonicalAddressWords (calldataArrayWords I.calldata n ptr.toNat) ∧
      ∃ aw' k' C', C ≤ C' ∧
      MemoryFunding credit
        (writeWordArray mem output.toNat (calldataArrayWords I.calldata n ptr.toNat)) aw' C' ∧
      RD midnightBytecode I g s0 ret ((output + UInt256.ofNat (32 * n)) :: R)
        (writeWordArray mem output.toNat (calldataArrayWords I.calldata n ptr.toNat))
        aw' rdata σ k' C') := by
  induction n generalizing mem aw index ptr output k C with
  | zero =>
    have hc : UInt256.lt index count = ⟨0⟩ := ult_zero (by omega)
    have rd1 := midnightBlocks.midnight_block_19561_fallthrough
      (by simp only [List.length_cons]; omega) hc rd
    have rd2 := midnightBlocks.midnight_block_19569 (by omega) hret rd1
    have ha2 := memoryFundingAt (credit := credit) rd2 (by memory_fund ha)
    right
    refine ⟨by simp [CanonicalAddressWords, calldataArrayWords], aw,
      k + 6 + 5, C + 23 + 17, by omega, ?_⟩
    simpa only [calldataArrayWords, writeWordArray, Nat.mul_zero, wordAddNat_zero,
      midnightBlocks.midnight_block_19569_stack] using And.intro ha2 rd2
  | succ n ih =>
    have hc : UInt256.lt index count = ⟨1⟩ := ult_one (by omega)
    have rd1 := midnightBlocks.midnight_block_19561_taken
      (by simp only [List.length_cons]; omega) (by rw [hc]; decide) (by jump_dest) rd
    have ha1 := memoryFundingAt (credit := credit) rd1 (by memory_fund ha)
    rcases midnightCalldataAddressEncodeStepFunded hstack ha1 rd1 with
      ⟨hn, hr⟩ | ⟨hc, aw2, k2, C2, hC2, ha2, rd2⟩
    · exact Or.inl ⟨fun h ↦ hn (h _ List.mem_cons_self), hr⟩
    have hi : (index + UInt256.ofNat 1).toNat = index.toNat + 1 :=
      uadd_word_ofNat_toNat _ _ (by
        have hh : count.toNat < UInt256.size := count.val.isLt
        omega)
    have hp : (ptr + UInt256.ofNat 32).toNat = ptr.toNat + 32 :=
      uadd_word_ofNat_toNat _ _ (by omega)
    have ho : (output + UInt256.ofNat 32).toNat = output.toNat + 32 :=
      uadd_word_ofNat_toNat _ _ (by omega)
    rcases ih (by rw [hi]; omega) (by rw [hp]; omega) (by rw [ho]; omega) ha2 rd2 with
      ⟨hn, hr⟩ | ⟨ht, aw3, k3, C3, hC3, ha3, rd3⟩
    · left
      refine ⟨?_, hr⟩
      intro h
      apply hn
      rw [hp]
      exact fun w hw ↦ h w (List.mem_cons_of_mem _ hw)
    · right
      have hall : CanonicalAddressWords (calldataArrayWords I.calldata (n + 1) ptr.toNat) := by
        rw [hp] at ht
        simpa only [calldataArrayWords, CanonicalAddressWords, List.forall_mem_cons] using
          And.intro hc ht
      have hm : writeWordArray (writeWord mem output.toNat (calldataWord I.calldata ptr.toNat))
          (output + UInt256.ofNat 32).toNat
          (calldataArrayWords I.calldata n (ptr + UInt256.ofNat 32).toNat) =
          writeWordArray mem output.toNat (calldataArrayWords I.calldata (n + 1) ptr.toNat) := by
        rw [hp, ho]
        rfl
      rw [hm] at ha3 rd3
      refine ⟨hall, aw3, k3, C3, by omega, ha3, ?_⟩
      simpa only [wordAddNat_add, show 32 + 32 * n = 32 * (n + 1) by omega] using rd3

theorem midnightCalldataAddressEncodeLoop {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw index count ptr output ret : UInt256} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} (n : Nat) (hstack : R.length + 15 ≤ 1024)
    (hcount : count.toNat = index.toNat + n)
    (hptr : ptr.toNat + 32 * n < UInt256.size)
    (hout : output.toNat + 32 * n < UInt256.size)
    (hret : (D_J midnightBytecode 0).contains ret = true)
    (ha : MemoryAccounting mem aw C)
    (rd : RD midnightBytecode I g s0 ⟨19561⟩
      (index :: count :: ptr :: output :: ret :: R) mem aw rdata σ k C) :
    (¬ CanonicalAddressWords (calldataArrayWords I.calldata n ptr.toNat) ∧
      RDrev midnightBytecode g s0) ∨
    (CanonicalAddressWords (calldataArrayWords I.calldata n ptr.toNat) ∧
      ∃ aw' k' C', C ≤ C' ∧
      MemoryAccounting
        (writeWordArray mem output.toNat (calldataArrayWords I.calldata n ptr.toNat)) aw' C' ∧
      RD midnightBytecode I g s0 ret ((output + UInt256.ofNat (32 * n)) :: R)
        (writeWordArray mem output.toNat (calldataArrayWords I.calldata n ptr.toNat))
        aw' rdata σ k' C') := by
  rcases midnightCalldataAddressEncodeLoopFunded n hstack hcount hptr hout hret (MemoryFunding.of_accounting ha) rd with
    hrev | ⟨hc, aw', k', C', hC, ha', rd'⟩
  · exact Or.inl hrev
  · exact Or.inr ⟨hc, aw', k', C', hC, ha'.accounting, rd'⟩

end Benchmarks.Midnight
