import Benchmarks.UniswapV3.Pool.SafeTransferCall
import Benchmarks.UniswapV3.Pool.BalanceSource
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_051

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

-- LIBRARY CANDIDATE: bound the output of a source call with either permission bit.
theorem callViaEVM_output_size {evm evm' : EVM.State} {target : AccountAddress} {value : Int}
    {calldata out : ByteArray} {ok perm : Bool}
    (hc : callViaEVM evm target value calldata (ok, evm', out) perm)
    (hsmall : calldata.size ≤ Ethereum.EVM.maxReturnDataSizeByGas) : out.size < 2 ^ 138 := by
  cases hc with
  | callMade _ hex _ _ _ =>
      obtain ⟨gas, A, hΘ⟩ := hex
      exact Theta_returnData_size_lt_2pow138_of_eq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hΘ hsmall
  | callNotMade _ _ _ => decide

theorem balanceReturndataGrowingX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw ptr status junk1 junk2 : UInt256} {mem out : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨15775⟩ (status :: junk1 :: junk2 :: R) mem aw out σ k C)
    (hm : HeapMemory mem aw ptr) (hptr : ptr.toNat + 32 ≤ mem.size)
    (hzero : memLoad (UInt256.ofNat 96) mem = ⟨0⟩)
    (hbound : ptr.toNat + out.size + 95 ≤ 2 ^ 200)
    (hout : out.size < UInt256.size) (hov : R.length + 7 ≤ 1024) :
    ∃ dataPtr next mem' aw' k' C',
      RD (deployedRuntime v) ee g s0 ⟨15826⟩
        (UInt256.ofNat out.size :: dataPtr :: status :: R) mem' aw' out σ k' C' ∧
      HeapMemory mem' aw' next ∧ MemoryPrefix mem mem' ptr.toNat ∧
      ptr.toNat ≤ next.toNat ∧
      next.toNat ≤ ptr.toNat + out.size + 63 ∧ dataPtr.toNat + 64 ≤ 2 ^ 200 ∧
      memLoad dataPtr mem' = UInt256.ofNat out.size ∧
      (32 ≤ out.size → memLoad ((UInt256.ofNat 32) + dataPtr) mem' = balanceValue out) := by
  have hload : memLoad (UInt256.ofNat 64) mem = ptr := hm.load64
  by_cases hempty : out.size = 0
  · have rdEmpty := uniswapV3Pool_block_15775_taken (immWords := wordsOf (immStore v))
      (by omega) (by rw [hempty, uInt256_eq_self]; decide)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
    simp only [uniswapV3Pool_block_15775_taken_stack] at rdEmpty
    have rdDone := uniswapV3Pool_block_15821 (immWords := wordsOf (immStore v)) (by evm_ov) rdEmpty
    refine ⟨UInt256.ofNat 96, ptr, mem, aw, _, _, rdDone, hm, MemoryPrefix.refl _ _,
      by omega, by omega, by decide, ?_, ?_⟩
    · rw [hempty]; exact hzero
    · intro hlong; omega
  · have hlenNe : UInt256.ofNat out.size ≠ UInt256.ofNat 0 := by
      intro heq
      have hn := congrArg UInt256.toNat heq
      rw [ulit_toNat' _ hout] at hn
      exact hempty hn
    have rdAlloc := uniswapV3Pool_block_15775_fallthrough (immWords := wordsOf (immStore v))
      (by omega) (u256_eq_of_ne hlenNe) rd
    simp only [uniswapV3Pool_block_15775_fallthrough_stack] at rdAlloc
    have rdDone := uniswapV3Pool_block_15788 (immWords := wordsOf (immStore v))
      (by evm_ov) (by
        simpa only [show (UInt256.ofNat 0).toNat = 0 from rfl, Nat.zero_add] using
          Nat.le_of_eq (ulit_toNat' _ hout))
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rdAlloc
    have h64 : M aw (UInt256.ofNat 64) ⟨32⟩ = aw := activeWordsMload64_eq_self hm.active.1
    simp only [uniswapV3Pool_block_15788_stack, uniswapV3Pool_block_15788_memory,
      hload, h64] at rdDone
    have hfit : ptr.toNat + 32 < UInt256.size := by change _ < 2 ^ 256; omega
    have hmem :
      out.write (UInt256.ofNat 0).toNat
        ((UInt256.ofNat out.size).toByteArray.write 0
          ((ptr + UInt256.land (UInt256.ofNat out.size + UInt256.ofNat 63)
            (UInt256.lnot (UInt256.ofNat 31))).toByteArray.write 0 mem (UInt256.ofNat 64).toNat 32)
          ptr.toNat 32) (ptr + UInt256.ofNat 32).toNat (UInt256.ofNat out.size).toNat =
      solcReturnDataMem mem ptr out := by
        rw [ulit_toNat' _ hout]
        rfl
    rw [hmem] at rdDone
    change RD (deployedRuntime v) ee g s0 ⟨15826⟩
      (UInt256.ofNat out.size :: ptr :: status :: R) (solcReturnDataMem mem ptr out)
      (bytesAllocWords aw ptr out.size) out σ _ _ at rdDone
    have hmemEq := solcReturnDataMem_eq_bytesAllocMem mem ptr out hfit
    have hheap := bytesAlloc_heap hm out hempty (by omega)
    have hpref := bytesAlloc_prefix hm out hempty
    rw [← hmemEq] at hheap hpref
    refine ⟨ptr, bytesAllocPtr ptr out.size, solcReturnDataMem mem ptr out,
      bytesAllocWords aw ptr out.size, _, _, rdDone, hheap, hpref, ?_, ?_, by omega, ?_, ?_⟩
    · rw [bytesAllocPtr_toNat (by omega)]; omega
    · rw [bytesAllocPtr_toNat (by omega)]
      have hround := Nat.div_mul_le_self (out.size + 63) 32
      omega
    · exact mloadWordValue_of_readWithPadding
        (by rw [solcReturnDataMem_size ptr out hm.size hptr hfit]; omega)
        (solcReturnDataMem_read_size ptr out hm.size hptr hfit)
    · intro hlong
      rw [u256_add_comm (UInt256.ofNat 32)]
      unfold memLoad
      rw [if_neg (by rw [solcReturnDataMem_size ptr out hm.size hptr hfit,
        uadd_word_ofNat_toNat ptr 32 hfit]; omega)]
      exact congrArg (fun bytes ↦ UInt256.ofNat (fromByteArrayBigEndian bytes))
        (solcReturnDataMem_read_word ptr out hm.size hptr hfit hlong)

theorem balanceReturndataX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw ptr status junk1 junk2 : UInt256} {mem out : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨15775⟩ (status :: junk1 :: junk2 :: R) mem aw out σ k C)
    (hm : HeapMemory mem aw ptr) (hptr : ptr.toNat + 32 ≤ mem.size)
    (hzero : memLoad (UInt256.ofNat 96) mem = ⟨0⟩)
    (hbound : ptr.toNat + out.size + 95 ≤ 2 ^ 200)
    (hout : out.size < UInt256.size) (hov : R.length + 7 ≤ 1024) :
    ∃ dataPtr next mem' aw' k' C',
      RD (deployedRuntime v) ee g s0 ⟨15826⟩
        (UInt256.ofNat out.size :: dataPtr :: status :: R) mem' aw' out σ k' C' ∧
      HeapMemory mem' aw' next ∧ MemoryPrefix mem mem' ptr.toNat ∧
      next.toNat ≤ ptr.toNat + out.size + 63 ∧ dataPtr.toNat + 64 ≤ 2 ^ 200 ∧
      memLoad dataPtr mem' = UInt256.ofNat out.size ∧
      (32 ≤ out.size → memLoad ((UInt256.ofNat 32) + dataPtr) mem' = balanceValue out) := by
  obtain ⟨dataPtr, next, mem', aw', k', C', rr, hm', hpref, _, hnext, hdata, hlen, hword⟩ :=
    balanceReturndataGrowingX (v := v) rd hm hptr hzero hbound hout hov
  exact ⟨dataPtr, next, mem', aw', k', C', rr, hm', hpref, hnext, hdata, hlen, hword⟩

theorem balanceFinishX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw dataPtr junk0 junk1 junk2 ret : UInt256}
    {mem out : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables} (ok : Bool)
    (rd : RD (deployedRuntime v) ee g s0 ⟨15826⟩
      (UInt256.ofNat out.size :: dataPtr :: ok.toUInt256 :: junk0 :: junk1 :: junk2 :: ret :: R)
      mem aw out σ k C)
    (hlen : memLoad dataPtr mem = UInt256.ofNat out.size)
    (hword : 32 ≤ out.size → memLoad (UInt256.ofNat 32 + dataPtr) mem = balanceValue out)
    (hout : out.size < UInt256.size) (ha : ActiveWords aw)
    (hp : dataPtr.toNat + 64 ≤ 2 ^ 200)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hov : R.length + 9 ≤ 1024) :
    ((ok && decide (32 ≤ out.size)) = false ∧ RDrev (deployedRuntime v) g s0) ∨
    (ok = true ∧ 32 ≤ out.size ∧ ∃ aw' k' C',
      RD (deployedRuntime v) ee g s0 ret (balanceValue out :: R) mem aw' out σ k' C' ∧
      ActiveWords aw') := by
  cases ok with
  | false =>
      have rdGuard := uniswapV3Pool_block_15826_taken (immWords := wordsOf (immStore v))
        (by evm_ov) (by decide +kernel)
        (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
      simp only [uniswapV3Pool_block_15826_taken_stack] at rdGuard
      have rdFail := uniswapV3Pool_block_15846_fallthrough (immWords := wordsOf (immStore v))
        (by evm_ov) rfl rdGuard
      simp only [uniswapV3Pool_block_15846_fallthrough_stack] at rdFail
      exact Or.inl ⟨rfl, uniswapV3Pool_block_15851 (immWords := wordsOf (immStore v))
        (by evm_ov) rdFail⟩
  | true =>
      have rdLength := uniswapV3Pool_block_15826_fallthrough (immWords := wordsOf (immStore v))
        (by evm_ov) (by decide +kernel) rd
      simp only [uniswapV3Pool_block_15826_fallthrough_stack] at rdLength
      have rdGuard := uniswapV3Pool_block_15839 (immWords := wordsOf (immStore v))
        (by evm_ov) rdLength
      simp only [uniswapV3Pool_block_15839_stack, hlen] at rdGuard
      by_cases hlong : 32 ≤ out.size
      · have hcond : UInt256.isZero (UInt256.lt (UInt256.ofNat out.size) (UInt256.ofNat 32)) ≠
            UInt256.ofNat 0 := by
          rw [ult_zero (by rw [ulit_toNat' _ hout]; exact hlong)]
          decide +kernel
        have rdDecode := uniswapV3Pool_block_15846_taken (immWords := wordsOf (immStore v))
          (by evm_ov) hcond (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rdGuard
        simp only [uniswapV3Pool_block_15846_taken_stack] at rdDecode
        have rdWord := uniswapV3Pool_block_15855_taken (immWords := wordsOf (immStore v))
          (by evm_ov) (by rw [hlen]; exact hcond)
          (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rdDecode
        simp only [uniswapV3Pool_block_15855_taken_stack] at rdWord
        have rdDone := uniswapV3Pool_block_15876 (immWords := wordsOf (immStore v))
          (by evm_ov) hret rdWord
        simp only [uniswapV3Pool_block_15876_stack, hword hlong] at rdDone
        refine Or.inr ⟨rfl, hlong, _, _, _, rdDone, ?_⟩
        apply activeWords_expand32 (activeWords_expand32 (activeWords_expand32 ha (by omega))
          (by omega))
        rw [u256_add_comm, uadd_word_ofNat_toNat dataPtr 32 (by change _ < 2 ^ 256; omega)]
        omega
      · have hcond : UInt256.isZero (UInt256.lt (UInt256.ofNat out.size) (UInt256.ofNat 32)) =
            UInt256.ofNat 0 := by
          rw [ult_one (by rw [ulit_toNat' _ hout]; change out.size < 32; omega)]
          decide +kernel
        have rdFail := uniswapV3Pool_block_15846_fallthrough (immWords := wordsOf (immStore v))
          (by evm_ov) hcond rdGuard
        simp only [uniswapV3Pool_block_15846_fallthrough_stack] at rdFail
        exact Or.inl ⟨by simp only [hlong, decide_false, Bool.and_false],
          uniswapV3Pool_block_15851 (immWords := wordsOf (immStore v)) (by evm_ov) rdFail⟩

end Benchmarks.UniswapV3.Pool
