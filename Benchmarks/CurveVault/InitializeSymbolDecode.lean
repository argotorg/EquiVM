import Benchmarks.CurveVault.SymbolReturnChecks
import Benchmarks.CurveVault.MemoryActive
import Benchmarks.CurveVault.RuntimeBlocks_002
import Benchmarks.CurveVault.RuntimeBlocks_003
import Benchmarks.CurveVault.RuntimeBlocks_031

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.CurveVault

theorem vaultInitializeSymbolDecode {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {target : UInt256} {R : List UInt256}
    (hmem : mem.size = 320) (h32 : 32 ≤ out.size) (haw : aw.toNat ≤ 12)
    (hstack : R.length + 7 ≤ 1024)
    (h : RD fork vaultBytecode I g s0 (UInt256.ofNat 425)
      (UInt256.ofNat (min out.size 96) :: target :: R) (vaultSymbolCallMemory mem out) aw out σ k C) :
    (∃ (size ptr : UInt256) (aw' : UInt256) (k' C' : Nat),
      size.toNat ≤ 32 ∧ ptr.toNat ≤ 352 ∧
      ptr.toNat + 32 ≤ (vaultSymbolCallMemory mem out).size ∧
      decodeTokenSymbol out = some [vaultBorrowedSymbol size.toNat
        ((vaultSymbolCallMemory mem out).readWithPadding (ptr.toNat + 32) 32)] ∧
      memLoad ptr (vaultSymbolCallMemory mem out) = size ∧
      RD fork vaultBytecode I g s0 (UInt256.ofNat 476)
        (size :: ptr :: UInt256.ofNat (min out.size 96) :: target :: R)
        (vaultSymbolCallMemory mem out) aw' out σ k' C') ∨
    (decodeTokenSymbol out = none ∧ RDrev fork vaultBytecode g s0) := by
  let m := vaultSymbolCallMemory mem out
  let offset := memLoad (UInt256.ofNat 288) m
  let ptr := UInt256.ofNat 288 + offset
  let size := memLoad ptr m
  have hchecks := vaultSymbolValidChecks mem out hmem h32
  have hc : (out.extract 0 96).size = min out.size 96 := by rw [ByteArray.size_extract]; omega
  have hhead : offset = memLoad (UInt256.ofNat 0) (out.extract 0 96) :=
    vaultSymbolCallMemory_load mem out 0 hmem h32 (by decide +kernel)
  by_cases h425 : UInt256.lt ptr (UInt256.ofNat 288) = ⟨0⟩
  swap
  · have rdFail := vaultBlocks.vault_block_425_taken
      (by simp only [List.length_cons]; omega) h425 (by native_decide) h
    refine Or.inr ⟨?_, vaultBlocks.vault_block_8284 (by simp only [List.length_cons]; omega) rdFail⟩
    by_contra hvalid
    exact h425 (hchecks hvalid).1
  have rd441 := vaultBlocks.vault_block_425_fallthrough
    (by simp only [List.length_cons]; omega) h425 h
  have hpfit := symbolOffset_noOverflow offset h425
  have hp : ptr.toNat = 288 + offset.toNat := addWord_toNat _ _ hpfit
  by_cases h441 : UInt256.gt (ptr + (UInt256.ofNat 32 + size))
      (UInt256.ofNat 288 + UInt256.ofNat (min out.size 96)) = ⟨0⟩
  swap
  · have rdFail := vaultBlocks.vault_block_441_taken
      (by simp only [List.length_cons]; omega) h441 (by native_decide) rd441
    refine Or.inr ⟨?_, vaultBlocks.vault_block_8284
      (by simp only [vaultBlocks.vault_block_441_taken_stack, List.length_cons]; omega) rdFail⟩
    by_contra hvalid
    exact h441 (hchecks hvalid).2.1
  have rd468 := vaultBlocks.vault_block_441_fallthrough
    (by simp only [List.length_cons]; omega) h441 rd441
  by_cases hlarge : 2 ^ 160 ≤ ptr.toNat
  · have haw1 : (M aw (UInt256.ofNat 288) ⟨32⟩).toNat ≤ 12 := memoryActive_le haw (by decide +kernel)
    have haw2 : (M (M aw (UInt256.ofNat 288) ⟨32⟩) (UInt256.ofNat 288) ⟨32⟩).toNat ≤ 12 :=
      memoryActive_le haw1 (by decide +kernel)
    have hcost := memoryExpansionCost_large haw2 hlarge
    refine Or.inr ⟨decodeTokenSymbol_offset out h32 ?_, Or.inl (rd468.oog_of_cost_gt ?_)⟩
    · rw [← hhead, hc]
      omega
    · have hg : g.toNat < UInt256.size := g.isLt
      dsimp only [ptr, offset] at hcost
      omega
  have hsmall : ptr.toNat < 2 ^ 160 := by omega
  by_cases h468 : UInt256.gt size (UInt256.ofNat 32) = ⟨0⟩
  swap
  · have rdFail := vaultBlocks.vault_block_468_taken
      (by simp only [vaultBlocks.vault_block_441_fallthrough_stack, List.length_cons]; omega)
      h468 (by native_decide) rd468
    refine Or.inr ⟨?_, vaultBlocks.vault_block_8284
      (by simp only [vaultBlocks.vault_block_441_fallthrough_stack, List.length_cons]; omega) rdFail⟩
    by_contra hvalid
    exact h468 (hchecks hvalid).2.2
  obtain ⟨hn, he⟩ := symbolChecks_bounds offset size (min out.size 96) (by omega) h425 hsmall h441 h468
  have rd476 := vaultBlocks.vault_block_468_fallthrough
    (by simp only [vaultBlocks.vault_block_441_fallthrough_stack, List.length_cons]; omega) h468 rd468
  have hptr : ptr = UInt256.ofNat (288 + offset.toNat) := by
    apply u256_inj
    rw [hp, ulit_toNat' _ hpfit]
  have hsize : size = memLoad (UInt256.ofNat offset.toNat) (out.extract 0 96) := by
    dsimp only [size]
    rw [hptr]
    exact vaultSymbolCallMemory_load mem out offset.toNat hmem h32 hpfit
  refine Or.inl ⟨size, ptr, _, _, _, hn, by omega, ?_, ?_, rfl, rd476⟩
  · rw [vaultSymbolCallMemory_size mem out hmem, hp]
    omega
  · have hfull : (memLoad (UInt256.ofNat 0) (out.extract 0 96)).toNat + 32 ≤ (out.extract 0 96).size := by
      rw [← hhead, hc]
      omega
    have hdec := decodeTokenSymbol_eq out h32 hfull
    dsimp only at hdec
    rw [← hhead, ← hsize, hc, if_neg (by omega)] at hdec
    have hword : (vaultSymbolCallMemory mem out).readWithPadding (ptr.toNat + 32) 32 =
        (out.extract 0 96).readWithPadding (offset.toNat + 32) 32 := by
      rw [hp, Nat.add_assoc, vaultSymbolCallMemory_read mem out (offset.toNat + 32) hmem h32]
    rw [hword]
    exact hdec

end Benchmarks.CurveVault
