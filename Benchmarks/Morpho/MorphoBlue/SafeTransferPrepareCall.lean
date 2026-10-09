import Benchmarks.Morpho.MorphoBlue.SafeTransferEntry

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

theorem morphoTransferPrepareCall {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem out : ByteArray} {aw ptr value ret : UInt256} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} (isFrom : Bool) (token sender recipient : AccountAddress)
    (hstack : R.length + 21 ≤ 1024) (hm : MorphoHeap mem ptr 0)
    (hsize : 128 ≤ mem.size) (hlower : 128 ≤ ptr.toNat)
    (hzero : memLoad (UInt256.ofNat 96) mem = UInt256.ofNat 0)
    (hc : extCodeSizeWord σ (UInt256.ofNat token.val) ≠ UInt256.ofNat 0)
    (hfit : ptr.toNat + safeTransferInputAllocation isFrom < 2 ^ 64)
    (h : RD (deployedRuntime v) ee g s0 (safeTransferEntryPC isFrom)
      (safeTransferEVMArgs isFrom token sender recipient value ++ ret :: R) mem aw out σ k C) :
    ∃ ptr' inOffset mem' gasArg a k C,
      RD (deployedRuntime v) ee g s0 (safeTransferCallPC isFrom)
        ([gasArg, UInt256.ofNat token.val, UInt256.ofNat 0, inOffset,
          UInt256.ofNat (safeTransferCallSize isFrom), UInt256.ofNat 0, UInt256.ofNat 0,
          UInt256.ofNat 15005, ret] ++ R) mem' a out σ k C ∧
      mem'.readWithPadding inOffset.toNat (safeTransferCallSize isFrom) =
        safeTransferCalldata isFrom sender recipient value ∧
      MorphoHeap mem' ptr' 0 ∧
      ptr'.toNat = ptr.toNat + safeTransferInputAllocation isFrom ∧
      MemoryPrefix mem mem' ptr.toNat ∧ 128 ≤ mem'.size ∧ 128 ≤ ptr'.toNat ∧
      memLoad (UInt256.ofNat 96) mem' = UInt256.ofNat 0 := by
  have hcost : 64 ≤ safeTransferInputAllocation isFrom := by cases isFrom <;> decide
  have hf0 : ptr.toNat + 64 < 2 ^ 64 := by omega
  obtain ⟨a0, k0, C0, rd0⟩ := morphoTransferEntry isFrom token sender recipient (by omega) h
  obtain ⟨a1, k1, C1, rd1⟩ := morphoTransferCodeOk
    (by rw [safeTransferEncodeStack_length]; omega) hm.free hf0 (safeTransferCodeCond_ne hc)
    (by cases isFrom <;> rw [morphoPatchedValidJumps v] <;> jump_dest) rd0
  let mem1 := safeTransferNoCodeMem mem
  let ptr1 := ptr + UInt256.ofNat 64
  have hm1 : MorphoHeap mem1 ptr1 0 := hm.errorMessage _ _ hf0
  have hp1 : ptr1.toNat = ptr.toNat + 64 :=
    uadd_word_ofNat_toNat ptr 64 (by change _ < 2 ^ 256; omega)
  have hsz1 : mem1.size = max mem.size (ptr.toNat + 64) :=
    (morphoErrorMem_properties_general _ _ ptr mem hm.lower hm.free hm.size
      (by have hg := hm.gap; omega) (by change _ < 2 ^ 256; omega)).1
  have hfit1 : ptr1.toNat + safeTransferCallAllocation isFrom < 2 ^ 64 := by
    rw [safeTransferInputAllocation_eq] at hfit
    rw [hp1]
    omega
  have hlo1 : 128 ≤ ptr1.toNat := by rw [hp1]; omega
  have hin1 : ptr1.toNat ≤ mem1.size := by rw [hp1, hsz1]; omega
  obtain ⟨a2, k2, C2, rd2⟩ := morphoTransferEncode isFrom token sender recipient (by omega)
    hm1.free (by have hh := hm1.space; change _ < 2 ^ 256; omega) rd1
  rw [List.append_assoc] at rd2
  obtain ⟨a3, k3, C3, rd3⟩ := morphoTransferAllocate
    (ptr := ptr1) (ret := safeTransferBeforeCallPC isFrom)
    (R := [ptr1, UInt256.ofNat 0, ptr1 + UInt256.ofNat 32, UInt256.ofNat token.val,
      UInt256.ofNat 0, UInt256.ofNat 0, UInt256.ofNat 15005, ret] ++ R)
    isFrom (by change R.length + 8 + 5 ≤ 1024; omega)
    (by cases isFrom <;> rw [morphoPatchedValidJumps v] <;> jump_dest) hfit1 rd2
  let mem2 := safeTransferCallMem isFrom sender recipient value mem1 ptr1
  let ptr2 := ptr1 + UInt256.ofNat (safeTransferCallAllocation isFrom)
  have hs2 := safeTransferCallMem_properties isFrom sender recipient value mem1 ptr1 hlo1 hin1
  have hm2 := safeTransferCallMem_heap isFrom sender recipient value mem1 ptr1 hlo1 hin1 hfit1
  obtain ⟨gasArg, a4, k4, C4, rd4⟩ := morphoTransferCallReady isFrom token (by omega) hs2.2.2.1 rd3
  have hp32 : (ptr1 + UInt256.ofNat 32).toNat = ptr1.toNat + 32 :=
    uadd_word_ofNat_toNat ptr1 32 (by have hh := hm1.space; change _ < 2 ^ 256; omega)
  have hp2 : ptr2.toNat = ptr.toNat + safeTransferInputAllocation isFrom := by
    rw [uadd_word_ofNat_toNat _ _ (by change _ < 2 ^ 256; omega), hp1, safeTransferInputAllocation_eq]
    omega
  have hpref1 : MemoryPrefix mem mem1 ptr.toNat := morphoErrorMem_prefix _ _ hm.size hm.free
    (by have hg := hm.gap; omega) (by change _ < 2 ^ 256; omega)
  have hpref := hpref1.trans ((safeTransferCallMem_prefix isFrom sender recipient value mem1 ptr1).mono
    (by rw [hp1]; omega))
  refine ⟨ptr2, ptr1 + UInt256.ofNat 32, mem2, gasArg, a4, k4, C4, rd4, ?_, hm2, hp2, hpref,
    le_trans hsize hpref.size, by rw [hp2]; omega, ?_⟩
  · rw [hp32]
    exact hs2.2.2.2
  · rw [memoryPrefix_memLoad hpref (UInt256.ofNat 96) (by decide) hlower hsize]
    exact hzero

end Benchmarks.Morpho.MorphoBlue
