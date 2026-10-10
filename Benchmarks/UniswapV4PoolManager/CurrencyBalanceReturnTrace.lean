import Benchmarks.UniswapV4PoolManager.CurrencyBalanceABI
import Benchmarks.UniswapV4PoolManager.AllocationTrace
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_042
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_026

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem balanceReturnAllocateTrace {I : ExecutionEnv} {g : Sat256} {s0 : State} {mem out : ByteArray}
    {aw ptr len ret : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+10 ≤ 1024)
    (hf : ptr.toNat+len.toNat+31 ≤ solcMaxU64)
    (h : RD (deployedRuntime v) I g s0 ⟨15112⟩ (ptr :: len :: ptr :: ret :: R) mem aw out σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨15125⟩ (len :: ptr :: ⟨32⟩ :: ptr :: ret :: R)
      (writeWord mem 64 (allocationEnd ptr len)) aw' out σ k' C' := by
  have hr := poolManagerBlocks.poolManager_block_15112 (by simp; omega)
    (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
  exact allocateTrace v (by change R.length+5+5 ≤ 1024; omega) hf
    (by rw [deployedRuntime_jumps]; jump_dest) hr

theorem currencyBalanceReturnTrace {I : ExecutionEnv} {g : Sat256} {s0 : State} {mem out : ByteArray}
    {aw ptr ret : UInt256} {z : Bool} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+10 ≤ 1024)
    (hptr : 96 ≤ ptr.toNat) (hfit : ptr.toNat+63 ≤ solcMaxU64)
    (hmem : ptr.toNat+32 ≤ mem.size) (ho : out.size < UInt256.size)
    (hread : 32 ≤ out.size → mem.readWithPadding ptr.toNat 32 = (returnedBalanceWord out).toByteArray)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) I g s0 ⟨15082⟩ ((if z then ⟨1⟩ else ⟨0⟩) :: ptr :: ret :: R) mem aw out σ k C) :
    (¬(z = true ∧ 32 ≤ out.size) ∧ RDrev (deployedRuntime v) g s0) ∨
    (z = true ∧ 32 ≤ out.size ∧ ∃ mem' aw' k' C',
      96 ≤ mem'.size ∧ (memLoad ⟨64⟩ mem').toNat ≤ mem'.size ∧
      RD (deployedRuntime v) I g s0 ret (returnedBalanceWord out :: R) mem' aw' out σ k' C') := by
  have hsize : (UInt256.ofNat out.size).toNat = out.size := UInt256.toNat_ofNat_of_lt ho
  cases z with
  | false =>
    have hr := poolManagerBlocks.poolManager_block_15082_taken (by simp; omega) (by decide)
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
    refine .inl ⟨by simp, poolManagerBlocks.poolManager_block_9410 (by change R.length+3+4 ≤ 1024; omega) ?_ hr⟩
    change 0+(UInt256.ofNat out.size).toNat ≤ out.size
    rw [hsize]; omega
  | true =>
    have rd1 := poolManagerBlocks.poolManager_block_15082_fallthrough (by simp; omega) (by decide) h
    have rd2 := poolManagerBlocks.poolManager_block_15089_taken (by change R.length+1+4 ≤ 1024; omega) (by decide)
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd1
    by_cases hlo : 32 ≤ out.size
    · have rd3 := poolManagerBlocks.poolManager_block_15098_fallthrough (by change R.length+1+5 ≤ 1024; omega)
        (ugt_zero (by rw [hsize]; exact hlo)) rd2
      obtain ⟨aw4, k4, C4, rd4⟩ := balanceReturnAllocateTrace v hstack (by simpa using hfit) rd3
      have rd5 := poolManagerBlocks.poolManager_block_15125_fallthrough (by change R.length+2+4 ≤ 1024; omega)
        (by rw [word_add_sub_left]; decide) rd4
      have rd6 := poolManagerBlocks.poolManager_block_15134 (by simp; omega) hret rd5
      have hgap : 64-mem.size < USize.size := by
        rw [Nat.sub_eq_zero_of_le (by omega : 64 ≤ mem.size)]
        exact USize.size_pos
      have hs : (writeWord mem 64 (allocationEnd ptr ⟨32⟩)).size = mem.size := by
        rw [writeWord_size _ _ _ hgap]
        omega
      have hr := writeWord_read_preserved mem 64 ptr.toNat (allocationEnd ptr ⟨32⟩)
        hgap
        (.inr ⟨by omega, hmem⟩)
      have hm : memLoad ptr (writeWord mem 64 (allocationEnd ptr ⟨32⟩)) = returnedBalanceWord out :=
        mloadWordValue_of_readWithPadding (by rw [hs]; omega) (hr.trans (hread hlo))
      change RD _ _ _ _ ret (memLoad ptr (writeWord mem 64 (allocationEnd ptr ⟨32⟩)) :: R) _ _ _ _ _ _ at rd6
      rw [hm] at rd6
      have hmfree : memLoad ⟨64⟩ (writeWord mem 64 (allocationEnd ptr ⟨32⟩)) = allocationEnd ptr ⟨32⟩ :=
        mloadWordValue_of_readWithPadding (by change 64 < _; rw [hs]; omega) (writeWord_read_back mem 64 _ hgap)
      have hbound : (allocationEnd ptr ⟨32⟩).toNat ≤ mem.size := by
        change (ptr+⟨32⟩).toNat ≤ mem.size
        rw [uadd_toNat]
        exact le_trans (Nat.mod_le _ _) hmem
      exact .inr ⟨rfl, hlo, writeWord mem 64 (allocationEnd ptr ⟨32⟩), _, _, _,
        by rw [hs]; omega, by rw [hmfree, hs]; exact hbound, rd6⟩
    · have hshort := Nat.lt_of_not_ge hlo
      have rd3 := poolManagerBlocks.poolManager_block_15098_taken (by change R.length+1+5 ≤ 1024; omega)
        (by rw [ugt_one (by rw [hsize]; exact hshort)]; decide)
        (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd2
      have rd4 := poolManagerBlocks.poolManager_block_15137 (by change R.length+2+3 ≤ 1024; omega)
        (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd3
      obtain ⟨aw5, k5, C5, rd5⟩ := balanceReturnAllocateTrace v hstack (by rw [hsize]; omega) rd4
      have hlt : UInt256.slt (UInt256.ofNat out.size) ⟨32⟩ = ⟨1⟩ :=
        slt_ofNat_lit_one_low (by decide) hshort
      have rd6 := poolManagerBlocks.poolManager_block_15125_taken (by change R.length+2+4 ≤ 1024; omega)
        (by rw [word_add_sub_left, hlt]; decide)
        (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd5
      exact .inl ⟨fun h => hlo h.2, emptyRevert v (by change R.length+2+2 ≤ 1024; omega) rd6⟩

end Benchmarks.UniswapV4PoolManager
