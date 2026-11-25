import Benchmarks.Midnight.CollateralCalldata
import Benchmarks.Midnight.TransferBudget

variable {fork : Ethereum.Fork}

/-! Collateral calldata decoding retains the budget for later external calls. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

theorem midnightCalldataAddress_ok_budget {root : UInt256} {credit : Nat} {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw head ret : UInt256} {σ : AccountMap} {k C : Nat}
    {R : List UInt256} (hstack : R.length + 5 ≤ 1024)
    (hcanon : (calldataWord I.calldata head.toNat).toNat < EVM.addressModulus)
    (hvalid : (D_J midnightBytecode 0).contains ret = true)
    (ha : TransferBudget root credit mem aw C)
    (rd : RD fork midnightBytecode I g s0 ⟨18342⟩ (head :: ret :: R) mem aw rdata σ k C) :
    ∃ k' C', TransferBudget root credit mem aw C' ∧ RD fork midnightBytecode I g s0 ret (calldataWord I.calldata head.toNat :: R)
      mem aw rdata σ k' C' := by
  have rd1 := midnightBlocks.midnight_block_18342_fallthrough hstack
    (addressCheck_zero hcanon) rd
  have rd2 := midnightBlocks.midnight_block_18361 (by
    simp only [List.length_cons]; omega) hvalid rd1
  have ha2 := transferBudgetAt (root := root) (credit := credit) rd2 (by transfer_budget ha)
  exact ⟨_, _, ha2, rd2⟩

theorem midnightAllocate128_budget {root : UInt256} {credit : Nat} {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {ptr ret : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024)
    (hc : allocationCheck ptr (ptr + UInt256.ofNat 128) = ⟨0⟩)
    (hret : (D_J midnightBytecode 0).contains ret = true)
    (ha : TransferBudget root credit mem aw C)
    (rd : RD fork midnightBytecode I g s0 ⟨18417⟩ (ptr :: ret :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', TransferBudget root credit (writeWord mem 64 (ptr + UInt256.ofNat 128)) aw' C' ∧
      RD fork midnightBytecode I g s0 ret R
        (writeWord mem 64 (ptr + UInt256.ofNat 128)) aw' rdata σ k' C' := by
  have rd1 := midnightBlocks.midnight_block_18417_fallthrough (by simpa using hstack) hc rd
  simp only [midnightBlocks.midnight_block_18417_fallthrough_stack] at rd1
  have rd2 := midnightBlocks.midnight_block_18440 (by omega) hret rd1
  have ha2 := transferBudgetAt (root := root) (credit := credit) rd2 (by
    unfold midnightBlocks.midnight_block_18440_memory
    transfer_budget ha)
  exact ⟨_, _, _, ha2, rd2⟩


theorem midnightCollateralCalldataCopy_budget {root : UInt256} {credit : Nat} {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw ptr head ret : UInt256} {σ : AccountMap} {k C : Nat}
    {R : List UInt256} (hstack : R.length + 12 ≤ 1024)
    (hhead : head.toNat + 128 < UInt256.size) (hptr : ptr.toNat + 128 < UInt256.size)
    (hvalid : (D_J midnightBytecode 0).contains ret = true)
    (ha : TransferBudget root credit mem aw C)
    (rd : RD fork midnightBytecode I g s0 ⟨18524⟩ (ptr :: ret :: head :: R)
      mem aw rdata σ k C) :
    (¬ CollateralData.canonicalAt I.calldata head.toNat ∧ RDrev fork midnightBytecode g s0) ∨
    (CollateralData.canonicalAt I.calldata head.toNat ∧ ∃ aw' k' C',
      TransferBudget root credit
        (writeWordArray mem ptr.toNat (CollateralData.at I.calldata head.toNat).words) aw' C' ∧
      RD fork midnightBytecode I g s0 ret (ptr :: R)
        (writeWordArray mem ptr.toNat (CollateralData.at I.calldata head.toNat).words)
        aw' rdata σ k' C') := by
  have hh32 := uadd_word_ofNat_toNat head 32 (by omega)
  have hh64 := uadd_word_ofNat_toNat head 64 (by omega)
  have hh96 := uadd_word_ofNat_toNat head 96 (by omega)
  have hp32 := uadd_word_ofNat_toNat ptr 32 (by omega)
  have hp64 := uadd_word_ofNat_toNat ptr 64 (by omega)
  have hp96 := uadd_word_ofNat_toNat ptr 96 (by omega)
  have rd1 := midnightBlocks.midnight_block_18524 (by omega) (by jump_dest) rd
  simp only [midnightBlocks.midnight_block_18524_stack] at rd1
  have ha1 := transferBudgetAt (root := root) (credit := credit) rd1 (by transfer_budget ha)
  by_cases ht : (calldataWord I.calldata head.toNat).toNat < EVM.addressModulus
  · obtain ⟨k2, C2, ha2, rd2⟩ := midnightCalldataAddress_ok_budget
      (by simp only [List.length_cons]; omega) ht (by jump_dest) ha1 rd1
    have rd3 := midnightBlocks.midnight_block_18541 (by
      simp only [List.length_cons]; omega) (by jump_dest) rd2
    have ha3 := transferBudgetAt (root := root) (credit := credit) rd3 (by
      unfold midnightBlocks.midnight_block_18541_memory
      transfer_budget ha2)
    simp only [midnightBlocks.midnight_block_18541_stack] at rd3
    by_cases ho : (calldataWord I.calldata (head.toNat + 96)).toNat < EVM.addressModulus
    · have hc : CollateralData.canonicalAt I.calldata head.toNat := ⟨ht, ho⟩
      right
      refine ⟨hc, ?_⟩
      obtain ⟨k4, C4, ha4, rd4⟩ := midnightCalldataAddress_ok_budget
        (by simp only [List.length_cons]; omega) (by rw [hh96]; exact ho)
        (by jump_dest) ha3 rd3
      have rd5 := midnightBlocks.midnight_block_18569 (by
        simp only [List.length_cons]; omega) hvalid rd4
      have ha5 := transferBudgetAt (root := root) (credit := credit) rd5 (by
        unfold midnightBlocks.midnight_block_18569_memory
        transfer_budget ha4)
      have hm : midnightBlocks.midnight_block_18569_memory
          (mem := midnightBlocks.midnight_block_18541_memory (ee := I) (mem := mem)
            (x0 := calldataWord I.calldata head.toNat) (x1 := head) (x5 := ptr))
          (x0 := calldataWord I.calldata (head + UInt256.ofNat 96).toNat)
          (x1 := UInt256.ofNat 96) (x2 := ptr) =
          writeWordArray mem ptr.toNat (CollateralData.at I.calldata head.toNat).words := by
        change writeWord (writeWord (writeWord (writeWord mem ptr.toNat
          (calldataWord I.calldata head.toNat)) (ptr + UInt256.ofNat 32).toNat
          (calldataWord I.calldata (head + UInt256.ofNat 32).toNat))
          (ptr + UInt256.ofNat 64).toNat
          (calldataWord I.calldata (head + UInt256.ofNat 64).toNat))
          (ptr + UInt256.ofNat 96).toNat
          (calldataWord I.calldata (head + UInt256.ofNat 96).toNat) = _
        simp only [CollateralData.at_words hc, writeWordArray,
          hh32, hh64, hh96, hp32, hp64, hp96, Nat.add_assoc, Nat.reduceAdd]
      have hr := And.intro ha5 rd5
      simp only [midnightBlocks.midnight_block_18569_stack, hm] at hr
      exact ⟨_, _, _, hr⟩
    · left
      refine ⟨by simp [CollateralData.canonicalAt, ho], ?_⟩
      exact midnightCalldataAddress_bad (by simp only [List.length_cons]; omega)
        (by rw [hh96]; exact ho) rd3
  · left
    refine ⟨by simp [CollateralData.canonicalAt, ht], ?_⟩
    exact midnightCalldataAddress_bad (by simp only [List.length_cons]; omega) ht rd1


theorem midnightCollateralCalldata_budget {root : UInt256} {credit : Nat} {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw ptr head ret : UInt256} {σ : AccountMap} {k C : Nat}
    {R : List UInt256} (hstack : R.length + 12 ≤ 1024)
    (hhead : head.toNat + 128 ≤ I.calldata.size) (hsize : I.calldata.size < 2^255)
    (hfree : memLoad (UInt256.ofNat 64) mem = ptr) (hptr : ptr.toNat < 2^64)
    (hvalid : (D_J midnightBytecode 0).contains ret = true)
    (ha : TransferBudget root credit mem aw C)
    (rd : RD fork midnightBytecode I g s0 ⟨18500⟩
      (head :: UInt256.ofNat I.calldata.size :: ret :: R) mem aw rdata σ k C) :
    (¬ ptr.toNat + 128 < 2^64 ∧ RDrev fork midnightBytecode g s0) ∨
    (¬ CollateralData.canonicalAt I.calldata head.toNat ∧ RDrev fork midnightBytecode g s0) ∨
    (ptr.toNat + 128 < 2^64 ∧ CollateralData.canonicalAt I.calldata head.toNat ∧ ∃ aw' k' C',
      TransferBudget root credit
        (writeWordArray (writeWord mem 64 (ptr + UInt256.ofNat 128)) ptr.toNat
          (CollateralData.at I.calldata head.toNat).words) aw' C' ∧
      RD fork midnightBytecode I g s0 ret (ptr :: R)
        (writeWordArray (writeWord mem 64 (ptr + UInt256.ofNat 128)) ptr.toNat
          (CollateralData.at I.calldata head.toNat).words) aw' rdata σ k' C') := by
  have rd1 := midnightBlocks.midnight_block_18500_fallthrough (by omega)
    (solcDecodeLenCheckOk (head := head) (need := UInt256.ofNat 128)
      hhead (by omega) (lt_size_of_lt_sign hsize) (by decide)) rd
  have rd2 := midnightBlocks.midnight_block_18513 (by
    simp only [midnightBlocks.midnight_block_18500_fallthrough_stack, List.length_cons]; omega)
    (by jump_dest) rd1
  simp only [midnightBlocks.midnight_block_18513_stack, hfree,
    midnightBlocks.midnight_block_18500_fallthrough_stack] at rd2
  have ha2 := transferBudgetAt (root := root) (credit := credit) rd2 (by transfer_budget ha)
  have hp : (ptr + UInt256.ofNat 128).toNat = ptr.toNat + 128 :=
    uadd_word_ofNat_toNat _ _ (by change _ < 2^256; omega)
  by_cases hfit : ptr.toNat + 128 < 2^64
  · obtain ⟨aw3, k3, C3, ha3, rd3⟩ := midnightAllocate128_budget
      (by simp only [List.length_cons]; omega)
      (allocationCheck_ok (by rw [hp]; exact hfit) (by rw [hp]; omega)) (by jump_dest) ha2 rd2
    rcases midnightCollateralCalldataCopy_budget hstack (by change _ < 2^256; omega)
      (by change _ < 2^256; omega) hvalid ha3 rd3 with ⟨hbad, hr⟩ | ⟨hc, hret⟩
    · exact Or.inr (Or.inl ⟨hbad, hr⟩)
    · exact Or.inr (Or.inr ⟨hfit, hc, hret⟩)
  · left
    refine ⟨hfit, ?_⟩
    exact midnightAllocate128Revert (by simp only [List.length_cons]; omega)
      (allocationCheck_large (by rw [hp]; omega) (by rw [hp]; omega)) rd2

end Benchmarks.Midnight
