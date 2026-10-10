import Benchmarks.UniswapV3.Pool.SafeTransferTrace
import Benchmarks.UniswapV3.Pool.Dispatch

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

-- LIBRARY CANDIDATE: identify the solc return-data write sequence with heap allocation.
theorem solcReturnDataMem_eq_bytesAllocMem (mem : ByteArray) (ptr : UInt256) (out : ByteArray)
    (hfit : ptr.toNat + 32 < UInt256.size) :
    solcReturnDataMem mem ptr out = bytesAllocMem mem out ptr := by
  have hptr : ptr + UInt256.land (UInt256.ofNat out.size + ⟨63⟩) (UInt256.lnot ⟨31⟩) =
      bytesAllocPtr ptr out.size := by
    unfold bytesAllocPtr bytesAllocSize
    rw [u256_land_comm]
    rfl
  unfold solcReturnDataMem solcReturnDataSizeMem solcReturnDataPtrMem bytesAllocMem
  rw [hptr, show (ptr + (⟨32⟩ : UInt256)).toNat = ptr.toNat + 32 from
    uadd_word_ofNat_toNat ptr 32 hfit]
  rfl

-- LIBRARY CANDIDATE: preserve a loaded word under an unchanged memory prefix.
theorem MemoryPrefix.memLoad {before after : ByteArray} {limit : Nat}
    (h : MemoryPrefix before after limit) (off : UInt256)
    (hlo : 96 ≤ off.toNat) (hhi : off.toNat + 32 ≤ limit)
    (hin : off.toNat + 32 ≤ before.size) : memLoad off after = memLoad off before := by
  have hsize := h.size
  simp only [Reasoning.Reach.memLoad, if_neg (by omega : ¬ off.toNat ≥ after.size),
    if_neg (by omega : ¬ off.toNat ≥ before.size), h.read off.toNat hlo hhi hin]

theorem safeTransferReturndataGrowingX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw ptr status junk1 junk2 : UInt256} {mem out : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨15414⟩ (status :: junk1 :: junk2 :: R) mem aw out σ k C)
    (hm : HeapMemory mem aw ptr) (hptr : ptr.toNat + 32 ≤ mem.size)
    (hzero : memLoad (UInt256.ofNat 96) mem = ⟨0⟩)
    (hbound : ptr.toNat + out.size + 95 ≤ 2 ^ 200)
    (hout : out.size < UInt256.size) (hov : R.length + 7 ≤ 1024) :
    ∃ dataPtr next mem' aw' k' C',
      RD (deployedRuntime v) ee g s0 ⟨15465⟩
        (UInt256.ofNat out.size :: dataPtr :: status :: R) mem' aw' out σ k' C' ∧
      HeapMemory mem' aw' next ∧ MemoryPrefix mem mem' ptr.toNat ∧
      ptr.toNat ≤ next.toNat ∧
      next.toNat ≤ ptr.toNat + out.size + 63 ∧ dataPtr.toNat + 64 ≤ 2 ^ 200 ∧
      memLoad dataPtr mem' = UInt256.ofNat out.size ∧
      (32 ≤ out.size → memLoad ((UInt256.ofNat 32) + dataPtr) mem' =
        UInt256.ofNat (fromByteArrayBigEndian (out.extract 0 32))) := by
  have hload : memLoad (UInt256.ofNat 64) mem = ptr := hm.load64
  by_cases hempty : out.size = 0
  · have rdEmpty := uniswapV3Pool_block_15414_taken (immWords := wordsOf (immStore v))
      (by omega) (by rw [hempty, uInt256_eq_self]; decide)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
    simp only [uniswapV3Pool_block_15414_taken_stack] at rdEmpty
    have rdDone := uniswapV3Pool_block_15460 (immWords := wordsOf (immStore v)) (by evm_ov) rdEmpty
    refine ⟨UInt256.ofNat 96, ptr, mem, aw, _, _, rdDone, hm,
      MemoryPrefix.refl _ _, by omega, by omega, by decide, ?_, ?_⟩
    · rw [hempty]; exact hzero
    · intro hlong; omega
  · have hlenNe : UInt256.ofNat out.size ≠ UInt256.ofNat 0 := by
      intro heq
      have hn := congrArg UInt256.toNat heq
      rw [ulit_toNat' _ hout] at hn
      exact hempty hn
    have rdAlloc := uniswapV3Pool_block_15414_fallthrough (immWords := wordsOf (immStore v))
      (by omega) (u256_eq_of_ne hlenNe) rd
    simp only [uniswapV3Pool_block_15414_fallthrough_stack] at rdAlloc
    have rdDone := uniswapV3Pool_block_15427 (immWords := wordsOf (immStore v))
      (by evm_ov) (by
        simpa only [show (UInt256.ofNat 0).toNat = 0 from rfl, Nat.zero_add] using
          Nat.le_of_eq (ulit_toNat' _ hout))
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rdAlloc
    have h64 : M aw (UInt256.ofNat 64) ⟨32⟩ = aw := activeWordsMload64_eq_self hm.active.1
    simp only [uniswapV3Pool_block_15427_stack, uniswapV3Pool_block_15427_memory,
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
    change RD (deployedRuntime v) ee g s0 ⟨15465⟩
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
      exact congrArg (fun bytes => UInt256.ofNat (fromByteArrayBigEndian bytes))
        (solcReturnDataMem_read_word ptr out hm.size hptr hfit hlong)

theorem safeTransferReturndataX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw ptr status junk1 junk2 : UInt256} {mem out : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨15414⟩ (status :: junk1 :: junk2 :: R) mem aw out σ k C)
    (hm : HeapMemory mem aw ptr) (hptr : ptr.toNat + 32 ≤ mem.size)
    (hzero : memLoad (UInt256.ofNat 96) mem = ⟨0⟩)
    (hbound : ptr.toNat + out.size + 95 ≤ 2 ^ 200)
    (hout : out.size < UInt256.size) (hov : R.length + 7 ≤ 1024) :
    ∃ dataPtr next mem' aw' k' C',
      RD (deployedRuntime v) ee g s0 ⟨15465⟩
        (UInt256.ofNat out.size :: dataPtr :: status :: R) mem' aw' out σ k' C' ∧
      HeapMemory mem' aw' next ∧ MemoryPrefix mem mem' ptr.toNat ∧
      next.toNat ≤ ptr.toNat + out.size + 63 ∧ dataPtr.toNat + 64 ≤ 2 ^ 200 ∧
      memLoad dataPtr mem' = UInt256.ofNat out.size ∧
      (32 ≤ out.size → memLoad ((UInt256.ofNat 32) + dataPtr) mem' =
        UInt256.ofNat (fromByteArrayBigEndian (out.extract 0 32))) := by
  obtain ⟨dataPtr, next, mem', aw', k', C', rr, hm', hpref, _, hnext, hdata, hlen, hword⟩ :=
    safeTransferReturndataGrowingX (v := v) rd hm hptr hzero hbound hout hov
  exact ⟨dataPtr, next, mem', aw', k', C', rr, hm', hpref, hnext, hdata, hlen, hword⟩

theorem safeTransferCalldata_size (recipient : AccountAddress) (value : UInt256) :
    (safeTransferCalldata recipient value).size = 68 := by
  simp only [safeTransferCalldata, ByteArray.size_append, toByteArray_size]
  rfl

theorem safeTransferCallGrowingX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 evm : EVM.State} {k C : Nat}
    {aw ptr inOff gasArg junk1 junk2 junk3 junk4 arg0 arg1 arg2 ret : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (imms : Store) (token recipient : AccountAddress) (value : UInt256)
    (rd : RD (deployedRuntime v) ee g s0 ⟨15413⟩
      (gasArg :: EVM.word token.val :: ⟨0⟩ :: inOff :: ⟨68⟩ :: inOff :: ⟨0⟩ ::
        junk1 :: junk2 :: junk3 :: junk4 :: arg0 :: arg1 :: arg2 :: ret :: R) mem aw rdata σ k C)
    (hs : SourceState s0 ee σ evm) (hperm : ee.perm = true)
    (hcd : mem.readWithPadding inOff.toNat 68 = safeTransferCalldata recipient value)
    (hm : HeapMemory mem aw ptr) (hptr : ptr.toNat + 32 ≤ mem.size)
    (hzero : memLoad (UInt256.ofNat 96) mem = ⟨0⟩)
    (hbound : ptr.toNat + 2 ^ 138 + 95 ≤ 2 ^ 200)
    (hinOff : inOff.toNat + 68 ≤ 2 ^ 200)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hov : R.length + 13 ≤ 1024) :
    (RDrev (deployedRuntime v) g s0 ∧
      ExecFuncBody config (safeTransferFrame imms token recipient value) evm
        safeTransferFunction.body .reverted) ∨
    ∃ evm' σ' out mem' aw' next k' C', SourceState s0 ee σ' evm' ∧
      ExecFuncBody config (safeTransferFrame imms token recipient value) evm
        safeTransferFunction.body
        (.returned (safeTransferCallFrame imms token recipient value true out) evm' none) ∧
      RD (deployedRuntime v) ee g s0 ret R mem' aw' out σ' k' C' ∧
      HeapMemory mem' aw' next ∧ MemoryPrefix mem mem' ptr.toNat ∧
      ptr.toNat ≤ next.toNat ∧
      next.toNat ≤ ptr.toNat + 2 ^ 138 + 63 := by
  obtain ⟨evm', σ', ok, out, kCall, CCall, hcall, hs', rdAfter, hout⟩ :=
    callBridge rd hs hperm
      (by immutable_decode(immutableLayout, uniswapV3PoolBytecode, wordsOf (immStore v),
        (⟨15413⟩ : UInt256), (UInt8.ofNat 241), .CALL, none,
        immutableLayout_inBounds, immutableTemplate_size64))
      hcd (by rw [safeTransferCalldata_size]; decide) (by evm_ov)
  change callViaEVM evm (AccountAddress.ofUInt256 (EVM.word token.val)) 0
    (safeTransferCalldata recipient value) (ok, evm', out) true at hcall
  rw [show AccountAddress.ofUInt256 (EVM.word token.val) = token from accountAddress_roundtrip
    token] at hcall
  rw [callOutputMem_zero] at rdAfter
  have hflag : (if ok then (⟨1⟩ : UInt256) else ⟨0⟩) = ok.toUInt256 := by cases ok <;> rfl
  rw [hflag] at rdAfter
  have hmCall : HeapMemory mem (callActiveWords aw inOff ⟨68⟩ inOff ⟨0⟩) ptr :=
    ⟨hm.size, hm.free, hm.lower, hm.gap,
      callActiveWords_active hm.active hinOff (by change inOff.toNat + 0 ≤ _; omega)⟩
  obtain ⟨dataPtr, next, mem', aw', kData, CData, rdReady, hm', hpref, hmono, hnext, hdataPtr, hlen,
    hword⟩ :=
    safeTransferReturndataGrowingX (v := v) rdAfter hmCall hptr hzero (by omega)
      (by change out.size < 2 ^ 256; omega) (by evm_ov)
  rcases safeTransferFinishX (v := v) imms token recipient value ok rdReady hcall
      hlen hword (by omega) hm'.active hdataPtr hret hov with
    hbad | ⟨aw'', kFinal, CFinal, rdFinal, hbody, haFinal⟩
  · exact Or.inl hbad
  · have hmFinal : HeapMemory mem' aw'' next := by
      exact { hm' with active := haFinal }
    exact Or.inr ⟨evm', σ', out, mem', aw'', next, kFinal, CFinal, hs', hbody, rdFinal,
      hmFinal, hpref, hmono, by omega⟩

theorem safeTransferCallX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 evm : EVM.State} {k C : Nat}
    {aw ptr inOff gasArg junk1 junk2 junk3 junk4 arg0 arg1 arg2 ret : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (imms : Store) (token recipient : AccountAddress) (value : UInt256)
    (rd : RD (deployedRuntime v) ee g s0 ⟨15413⟩
      (gasArg :: EVM.word token.val :: ⟨0⟩ :: inOff :: ⟨68⟩ :: inOff :: ⟨0⟩ ::
        junk1 :: junk2 :: junk3 :: junk4 :: arg0 :: arg1 :: arg2 :: ret :: R) mem aw rdata σ k C)
    (hs : SourceState s0 ee σ evm) (hperm : ee.perm = true)
    (hcd : mem.readWithPadding inOff.toNat 68 = safeTransferCalldata recipient value)
    (hm : HeapMemory mem aw ptr) (hptr : ptr.toNat + 32 ≤ mem.size)
    (hzero : memLoad (UInt256.ofNat 96) mem = ⟨0⟩)
    (hbound : ptr.toNat + 2 ^ 138 + 95 ≤ 2 ^ 200)
    (hinOff : inOff.toNat + 68 ≤ 2 ^ 200)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hov : R.length + 13 ≤ 1024) :
    (RDrev (deployedRuntime v) g s0 ∧
      ExecFuncBody config (safeTransferFrame imms token recipient value) evm
        safeTransferFunction.body .reverted) ∨
    ∃ evm' σ' out mem' aw' next k' C', SourceState s0 ee σ' evm' ∧
      ExecFuncBody config (safeTransferFrame imms token recipient value) evm
        safeTransferFunction.body
        (.returned (safeTransferCallFrame imms token recipient value true out) evm' none) ∧
      RD (deployedRuntime v) ee g s0 ret R mem' aw' out σ' k' C' ∧
      HeapMemory mem' aw' next ∧ MemoryPrefix mem mem' ptr.toNat ∧
      next.toNat ≤ ptr.toNat + 2 ^ 138 + 63 := by
  rcases safeTransferCallGrowingX (v := v) imms token recipient value rd hs hperm hcd
      hm hptr hzero hbound hinOff hret hov with
    hbad | ⟨evm', σ', out, mem', aw', next, k', C', hs', hbody, rr, hm', hpref, _, hnext⟩
  · exact Or.inl hbad
  · exact Or.inr ⟨evm', σ', out, mem', aw', next, k', C', hs', hbody, rr, hm', hpref, hnext⟩

end Benchmarks.UniswapV3.Pool
