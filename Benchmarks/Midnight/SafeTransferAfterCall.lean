import Benchmarks.Midnight.SafeTransferPostResult
import Benchmarks.Midnight.ReturnDataMemory
import Benchmarks.Midnight.SafeTransferSource

/-! Compose raw return-data extraction, decoding, and source execution after a token call. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

def safeTransferOutputMem (mem out : ByteArray) (ptr : UInt256) : ByteArray :=
  if out.size = 0 then mem else returnDataMem mem out ptr

def safeTransferOutputPtr (ptr : UInt256) (out : ByteArray) : UInt256 :=
  if out.size = 0 then ptr else returnDataPtr ptr out.size

theorem safeTransferReturnDataStepCharge (isFrom : Bool) {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (rd : RD midnightBytecode I g s0 (safeTransferCallPC isFrom + ⟨1⟩)
      R mem aw out σ k C) :
    ∃ k' C', MemoryCharge 0 aw aw C C' ∧ RD midnightBytecode I g s0 ⟨22728⟩ (safeTransferCheckPC isFrom :: R)
      mem aw out σ k' C' := by
  have h0 := MemoryCharge.refl aw C
  cases isFrom with
  | false => 
    have rd1 := midnightBlocks.midnight_block_23312 hstack (by jump_dest) rd
    have hc1 := memoryChargeAt (work := 0) (aw₀ := aw) (C₀ := C) rd1 (by memory_charge h0)
    exact ⟨_, _, hc1, rd1⟩
  | true => 
    have rd1 := midnightBlocks.midnight_block_23523 hstack (by jump_dest) rd
    have hc1 := memoryChargeAt (work := 0) (aw₀ := aw) (C₀ := C) rd1 (by memory_charge h0)
    exact ⟨_, _, hc1, rd1⟩

theorem safeTransferReturnDataStep (isFrom : Bool) {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (rd : RD midnightBytecode I g s0 (safeTransferCallPC isFrom + ⟨1⟩)
      R mem aw out σ k C) :
    ∃ k' C', RD midnightBytecode I g s0 ⟨22728⟩ (safeTransferCheckPC isFrom :: R)
      mem aw out σ k' C' := by
  obtain ⟨k', C', _, rd'⟩ := safeTransferReturnDataStepCharge isFrom hstack rd
  exact ⟨k', C', rd'⟩

theorem safeTransferAfterCallCharge (isFrom : Bool) (imms : Store)
    {I : ExecutionEnv} {g : Sat256} {s0 evm evm' : State}
    {mem out : ByteArray} {aw ptr ret : UInt256} {σ : AccountMap} {k C : Nat}
    {token sender recipient : AccountAddress} {value : UInt256} {success : Bool}
    {R : List UInt256}
    (hstack : R.length + 11 ≤ 1024) (hm : 96 ≤ mem.size) (hl : 96 ≤ ptr.toNat)
    (hfree : memLoad (UInt256.ofNat 64) mem = ptr)
    (hzero : memLoad (UInt256.ofNat 96) mem = ⟨0⟩)
    (hptr : ptr.toNat < 2 ^ 64) (hout : out.size < UInt256.size)
    (hspace : out.size < 2 ^ 64 → out.size ≠ 0 →
      ptr.toNat + returnDataAllocation out.size < 2 ^ 64)
    (hcode : 0 < (extCodeSizeWord evm.accountMap (UInt256.ofNat token.val)).toNat)
    (hcall : callViaEVM evm token 0 (safeTransferCalldata isFrom sender recipient value)
      (success, evm', out) true)
    (hret : (D_J midnightBytecode 0).contains ret = true)
    (rd : RD midnightBytecode I g s0 (safeTransferCallPC isFrom + ⟨1⟩)
      ((if success then ⟨1⟩ else ⟨0⟩) :: ret :: R) mem aw out σ k C) :
    (ExecFuncBody config (safeTransferFrame isFrom imms token sender recipient value) evm
      (safeTransferFunctionFor isFrom).body .reverted ∧ RDrev midnightBytecode g s0) ∨
    (success = true ∧
      ExecFuncBody config (safeTransferFrame isFrom imms token sender recipient value) evm
        (safeTransferFunctionFor isFrom).body
        (.returned (safeTransferCallFrame isFrom imms token sender recipient value true out) evm'
          none) ∧
      MemoryPrefix mem (safeTransferOutputMem mem out ptr) ptr.toNat ∧
      memLoad (UInt256.ofNat 64) (safeTransferOutputMem mem out ptr) = safeTransferOutputPtr ptr out ∧
      ptr.toNat ≤ (safeTransferOutputPtr ptr out).toNat ∧
      (safeTransferOutputPtr ptr out).toNat < 2 ^ 64 ∧
      ∃ aw' k' C', MemoryCharge (3 * ((out.size + 31) / 32)) aw aw' C C' ∧
        (MemoryCovered mem aw → MemoryCovered (safeTransferOutputMem mem out ptr) aw') ∧
        RD midnightBytecode I g s0 ret R
        (safeTransferOutputMem mem out ptr) aw' out σ k' C') := by
  obtain ⟨k1, C1, hc1, rd1⟩ := safeTransferReturnDataStepCharge isFrom
    (by simp only [List.length_cons]; omega) rd
  have hcheck : (D_J midnightBytecode 0).contains (safeTransferCheckPC isFrom) = true :=
    by cases isFrom <;> jump_dest
  by_cases hb : out.size < 2 ^ 64
  · by_cases hempty : out.size = 0
    · obtain ⟨k2, C2, hc2, rd2⟩ := midnightReturnDataEmptyCharge hempty
        (by simp only [List.length_cons]; omega) hcheck rd1
      cases success with
      | false =>
        exact Or.inl ⟨safeTransferRevertsCall isFrom imms evm evm' token sender recipient value out
          hcode hcall, safeTransferPostFailure isFrom (by simp only [List.length_cons]; omega) rd2⟩
      | true =>
        obtain ⟨k3, C3, hc3, rd3⟩ := safeTransferPostSuccessCharge isFrom
          (by simp only [List.length_cons]; omega) rd2
        obtain ⟨aw4, k4, C4, hc4, rd4⟩ := safeTransferPostEmptyCharge isFrom (by omega) hzero hret rd3
        refine Or.inr ⟨rfl, safeTransferReturns isFrom imms evm evm' token sender recipient value out
          hcode hcall hb (Or.inl hempty), ?_, ?_, ?_, ?_, ?_⟩
        · simpa only [safeTransferOutputMem, if_pos hempty] using MemoryPrefix.refl mem ptr.toNat
        · simpa only [safeTransferOutputMem, safeTransferOutputPtr, if_pos hempty] using hfree
        · simp only [safeTransferOutputPtr, if_pos hempty, le_refl]
        · simpa only [safeTransferOutputPtr, if_pos hempty] using hptr
        · refine ⟨aw4, k4, C4, ?_, ?_, ?_⟩
          · simpa only [hempty, Nat.reduceAdd, Nat.reduceDiv, Nat.mul_zero, Nat.add_zero] using
              ((hc1.trans hc2).trans hc3).trans hc4
          · intro ha
            simpa only [safeTransferOutputMem, if_pos hempty] using
              ha.mono (((hc1.trans hc2).trans hc3).trans hc4).active_le
          · simpa only [safeTransferOutputMem, if_pos hempty] using rd4
    · have hfit := hspace hb hempty
      obtain ⟨aw2, k2, C2, hc2, hcover2, rd2⟩ := midnightReturnDataCopyCharge hb hempty hfree
        (by simp only [List.length_cons]; omega) hcheck hfit rd1
      cases success with
      | false =>
        exact Or.inl ⟨safeTransferRevertsCall isFrom imms evm evm' token sender recipient value out
          hcode hcall, safeTransferPostFailure isFrom (by simp only [List.length_cons]; omega) rd2⟩
      | true =>
        obtain ⟨k3, C3, hc3, rd3⟩ := safeTransferPostSuccessCharge isFrom
          (by simp only [List.length_cons]; omega) rd2
        have hp := returnDataMem_properties hm hl hempty (by change _ < 2 ^ 256; omega)
        rcases safeTransferPostResultCharge isFrom (by omega) hb hp.2.2.1 hp.2.2.2 hret rd3 with
          ⟨hgood, aw4, k4, C4, hc4, rd4⟩ | ⟨hn, hbad, hrev⟩
        · refine Or.inr ⟨rfl, safeTransferReturns isFrom imms evm evm' token sender recipient value out
            hcode hcall hb hgood, ?_, ?_, ?_, ?_, ?_⟩
          · simpa only [safeTransferOutputMem, if_neg hempty] using returnDataMem_prefix hempty
          · simpa only [safeTransferOutputMem, safeTransferOutputPtr, if_neg hempty] using hp.2.1
          · simp only [safeTransferOutputPtr, if_neg hempty, returnDataPtr,
              uadd_word_ofNat_toNat ptr (returnDataAllocation out.size)
                (by change _ < 2 ^ 256; omega)]
            omega
          · simpa only [safeTransferOutputPtr, if_neg hempty, returnDataPtr,
              uadd_word_ofNat_toNat ptr (returnDataAllocation out.size)
                (by change _ < 2 ^ 256; omega)] using hfit
          · refine ⟨aw4, k4, C4, ?_, ?_, ?_⟩
            · simpa only [Nat.zero_add, Nat.add_zero] using
                ((hc1.trans hc2).trans hc3).trans hc4
            · intro ha
              simpa only [safeTransferOutputMem, if_neg hempty] using
                (hcover2 hm (ha.mono hc1.active_le)).mono (hc3.trans hc4).active_le
            · simpa only [safeTransferOutputMem, if_neg hempty] using rd4
        · exact Or.inl ⟨safeTransferRevertsDecode isFrom imms evm evm' token sender recipient value out
            hcode hcall hn hbad, hrev⟩
  · exact Or.inl ⟨safeTransferRevertsSize isFrom imms evm evm' token sender recipient value success out
      hcode hcall (by omega), midnightReturnDataOversize hout (by omega)
        (by simp only [List.length_cons]; omega) rd1⟩

theorem safeTransferAfterCall (isFrom : Bool) (imms : Store)
    {I : ExecutionEnv} {g : Sat256} {s0 evm evm' : State}
    {mem out : ByteArray} {aw ptr ret : UInt256} {σ : AccountMap} {k C : Nat}
    {token sender recipient : AccountAddress} {value : UInt256} {success : Bool}
    {R : List UInt256}
    (hstack : R.length + 11 ≤ 1024) (hm : 96 ≤ mem.size) (hl : 96 ≤ ptr.toNat)
    (hfree : memLoad (UInt256.ofNat 64) mem = ptr)
    (hzero : memLoad (UInt256.ofNat 96) mem = ⟨0⟩)
    (hptr : ptr.toNat < 2 ^ 64) (hout : out.size < UInt256.size)
    (hspace : out.size < 2 ^ 64 → out.size ≠ 0 →
      ptr.toNat + returnDataAllocation out.size < 2 ^ 64)
    (hcode : 0 < (extCodeSizeWord evm.accountMap (UInt256.ofNat token.val)).toNat)
    (hcall : callViaEVM evm token 0 (safeTransferCalldata isFrom sender recipient value)
      (success, evm', out) true)
    (hret : (D_J midnightBytecode 0).contains ret = true)
    (rd : RD midnightBytecode I g s0 (safeTransferCallPC isFrom + ⟨1⟩)
      ((if success then ⟨1⟩ else ⟨0⟩) :: ret :: R) mem aw out σ k C) :
    (ExecFuncBody config (safeTransferFrame isFrom imms token sender recipient value) evm
      (safeTransferFunctionFor isFrom).body .reverted ∧ RDrev midnightBytecode g s0) ∨
    (success = true ∧
      ExecFuncBody config (safeTransferFrame isFrom imms token sender recipient value) evm
        (safeTransferFunctionFor isFrom).body
        (.returned (safeTransferCallFrame isFrom imms token sender recipient value true out) evm'
          none) ∧
      MemoryPrefix mem (safeTransferOutputMem mem out ptr) ptr.toNat ∧
      memLoad (UInt256.ofNat 64) (safeTransferOutputMem mem out ptr) = safeTransferOutputPtr ptr out ∧
      ptr.toNat ≤ (safeTransferOutputPtr ptr out).toNat ∧
      (safeTransferOutputPtr ptr out).toNat < 2 ^ 64 ∧
      ∃ aw' k' C', RD midnightBytecode I g s0 ret R
        (safeTransferOutputMem mem out ptr) aw' out σ k' C') := by
  rcases safeTransferAfterCallCharge isFrom imms hstack hm hl hfree hzero hptr hout hspace
      hcode hcall hret rd with hrev | ⟨hs, hb, hp, hf, hl, hlt, aw', k', C', _, _, rd'⟩
  · exact Or.inl hrev
  · exact Or.inr ⟨hs, hb, hp, hf, hl, hlt, aw', k', C', rd'⟩

end Benchmarks.Midnight
