import Benchmarks.EAS.EAS.ResolveOneAmountRun

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

theorem resolveOnePaymentRun {locals imms : Store} {ee : ExecutionEnv} {g : Sat256} {s0 evm : EVM.State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {src dataPtr available value ptr ret : UInt256} {R : List UInt256} {a : AttestationRecord} {target : AccountAddress}
    {rev last : Bool} (v : EASImmutables)
    (hf : ResolveOneLocals locals a target value available rev last ptr.toNat)
    (hstack : R.length+26 ≤ 1024) (hperm : ee.perm = true) (hs : SourceState s0 ee σ evm)
    (hview : AttestationMemoryView mem src dataPtr a)
    (hsrc : src.toNat+320 ≤ ptr.toNat) (hdata : dataPtr.toNat+32+32*((a.data.size+31)/32) ≤ ptr.toNat)
    (hheap : ptr.toNat ≤ 2^64-1) (hh : memLoad (UInt256.ofNat 64) mem = ptr)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨15764⟩
      (src::rev.toUInt256::UInt256.ofNat target.val::last.toUInt256::available::value::ret::R) mem aw rdata σ k C) :
    HeapReturnPost fork (value.toNat ≤ available.toNat) config (deployedRuntime v) ee g s0 {contract := contract, locals := locals, immutables := imms}
      evm resolveOneSuffix (.int (Int.ofNat value.toNat)) ret (value::R) mem ptr.toNat := by
  have he : evalExpr? config {contract := contract, locals := locals, immutables := imms} evm resolveOneValueNonzero =
      .ok (.bool (decide (value ≠ ⟨0⟩))) := by
    exact evalWordNeZero (by simp only [evalExpr?, hf.value, EvalResult.ofOption])
  by_cases hz : value = ⟨0⟩
  · subst value
    obtain ⟨aw1,k1,C1,rd1⟩ := resolveOneNoPayment v (by simp only [List.length_cons]; omega) rd
    have hnext := resolveOneAmountRun (imms := imms) v hf hstack hperm hs hview hsrc hdata hheap hh hret rd1
    have hpay : ExecStmt fork config {contract := contract, locals := locals, immutables := imms} evm resolveOnePayment
        (.ok {contract := contract, locals := locals, immutables := imms} evm) :=
      ExecStmt.iteFalse (by simpa only [ne_self_iff_false, decide_false] using he) ExecBlock.nil
    exact hnext.prepend (ExecBlock.consNormal hpay ExecBlock.nil) (MemoryPrefix.refl _ _) (le_refl _)
  · have hlo : 96 ≤ ptr.toNat := by have h := hview.sourceLow; omega
    obtain ⟨aw1,k1,C1,rd1⟩ := resolveOnePaymentEntry v (by simp only [List.length_cons]; omega) hz rd
    obtain ⟨evm',σ',success,out,hcall,hs',hout,hr⟩ := payableCheckEVM
      (a := src) (b := rev.toUInt256) (c := ⟨0⟩) (d := ⟨0⟩) (e := ⟨0⟩)
      (R := last.toUInt256::available::value::ret::R) v .single
      (by simp only [List.length_cons]; omega) hs hheap hlo hh rd1
    simp only [accountAddress_roundtrip] at hcall
    have hsource := payableCheckSource (imms := imms) hf.resolver hf.heap hcall (by omega)
    by_cases hv : callBoolAccepted ptr.toNat success out
    · rw [if_pos hv] at hr hsource
      obtain ⟨aw2,k2,C2,rd2⟩ := hr
      have hmin : min out.size 32 = 32 := Nat.min_eq_right hv.1.2.2.1
      have halloc : allocateNext ptr.toNat 32 ≤ 2^64-1 ∧ ptr.toNat ≤ allocateNext ptr.toNat 32 := by
        simpa only [hmin] using hv.1.2.1
      let nextPtr := UInt256.ofNat (allocateNext ptr.toNat 32)
      have hnext : nextPtr.toNat = allocateNext ptr.toNat 32 := ulit_toNat' _ (by change _ < 2^256; omega)
      have hp := payableOutputMemory_prefix mem ptr out (by change out.size < 2^256; omega)
      have hview' := hview.preserve hp hsrc hdata (by change ptr.toNat < 2^256; omega)
      have hf' : ResolveOneLocals (payableProbeLocals locals out ptr.toNat) a target value available rev last nextPtr.toNat := by
        simpa only [hnext] using hf.payment out
      have hhh : memLoad (UInt256.ofNat 64) (payableOutputMemory mem ptr out) = nextPtr := by
        simpa only [hmin] using payableOutputMemory_heap mem ptr out
      have hfinish := resolveOneAmountRun (imms := imms) v hf' hstack hperm hs' hview'
        (by rw [hnext]; omega) (by rw [hnext]; omega) (by rw [hnext]; exact halloc.1) hhh hret rd2
      simp only [hnext] at hfinish
      have hpay : ExecStmt fork config {contract := contract, locals := locals, immutables := imms} evm resolveOnePayment
          (.ok {contract := contract, locals := payableProbeLocals locals out ptr.toNat, immutables := imms} evm') :=
        ExecStmt.iteTrue (by simpa only [decide_eq_true hz] using he) hsource
      exact hfinish.prepend (ExecBlock.consNormal hpay ExecBlock.nil) hp halloc.2
    · rw [if_neg hv] at hr hsource
      exact HeapReturnPost.of_revert_prefix (front := [resolveOnePayment])
        (ExecBlock.consRevert (ExecStmt.iteTrue (by simpa only [decide_eq_true hz] using he) hsource)) hr

end Benchmarks.EAS.EAS
