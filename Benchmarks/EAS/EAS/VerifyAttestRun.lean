import Benchmarks.EAS.EAS.VerifyAttestEVM

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

theorem verifyAttestRun {L : Store} {ee : ExecutionEnv} {g : Sat256} {s0 evm : EVM.State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {heap ptr dataPtr bytesPtr sigPtr ret : UInt256} {R : List UInt256} {r : DelegatedAttestationRecord} (v : EASImmutables)
    (hreq : L.get? "request" = some r.struct) (hn : L.get? "_nonces" = none)
    (hf : L.get? "$EAS.freeMemory" = some (.int (Int.ofNat heap.toNat)))
    (hstack : R.length+20 ≤ 1024) (hs : SourceState s0 ee σ evm)
    (hv : DelegatedAttestMemoryView mem ptr dataPtr bytesPtr sigPtr r heap.toNat)
    (hh : memLoad (UInt256.ofNat 64) mem = heap) (hheap : heap.toNat ≤ 2^64-1)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨13494⟩ (ptr::ret::R) mem aw rdata σ k C) :
    HeapReturnOrStatic fork config (deployedRuntime v) ee g s0 {contract := contract,locals := L,immutables := immStore v}
      evm verifyAttestFunction.body (.tuple []) ret R mem heap.toNat := by
  let nonce := nonceWord evm r.attester
  let L1 := verifyAttestReadLocals L r nonce heap.toNat
  have hp1 := verifyAttestReadSource (fork := fork) (imms := immStore v) (evm := evm) hreq hn hf
  have hfacts := verifyAttestReadLocals_facts (nonce := nonce) (heap := heap.toNat) hreq hn
  have hreq1 : L1.get? "request" = some r.struct := hfacts.1
  have hd1 : L1.get? "data" = some r.data.struct := hfacts.2.1
  have hs1 : L1.get? "signature" = some r.signature.struct := hfacts.2.2.1
  have hn1 : L1.get? "nonce" = some (.int (Int.ofNat nonce.toNat)) := hfacts.2.2.2.1
  have hf1 : L1.get? "$EAS.freeMemory" = some (.int (Int.ofNat heap.toNat)) := hfacts.2.2.2.2.1
  have hnone1 : L1.get? "_nonces" = none := hfacts.2.2.2.2.2
  have he1 : evalExpr? config {contract := contract,locals := L1,immutables := immStore v} evm
      (.field (.var "request") "attester") = .ok (.address r.attester) := delegatedAttestField (cfg := config) (frame := {contract := contract,locals := L1,immutables := immStore v}) (evm := evm) (r := r) hreq1 "attester" _ rfl
  rw [verifyAttest_body]
  simp only [List.append_assoc]
  refine HeapReturnOrStatic.prepend ?_ hp1 (MemoryPrefix.refl _ _) (le_refl _)
  by_cases hp : ee.perm = true
  · have hw := nonceWriteSource (fork := fork) (hperm := by simpa only [hs.env] using hp) (L := L1) (imms := immStore v) (evm := evm) (a := r.attester) hnone1 hn1 he1
    have hwb : ExecBlock fork config {contract := contract,locals := L1,immutables := immStore v} evm
        [nonceWrite (.field (.var "request") "attester")]
        (.ok {contract := contract,locals := L1,immutables := immStore v} (nonceStore evm r.attester)) :=
      ExecBlock.consNormal hw ExecBlock.nil
    refine HeapReturnOrStatic.prepend ?_ hwb (MemoryPrefix.refl _ _) (le_refl _)
    have hs' := hs.readModifyWrite (nonceSlot r.attester) (fun w => w+UInt256.ofNat 1)
    have hnonce : solcSlotWord σ ee (nonceSlot r.attester) = nonce := (hs.storageRead _).symm
    have hr := verifyAttestHashEVM v hstack hp hv hh hheap rd
    rw [hnonce] at hr hs'
    have hb : heap.toNat < UInt256.size := heap.val.isLt
    by_cases hg : allocateNext heap.toNat 288 ≤ 2^64-1 ∧ heap.toNat ≤ allocateNext heap.toNat 288
    · rw [if_pos hg] at hr
      obtain ⟨aw1,k1,C1,rd1⟩ := hr
      let next := allocateNext heap.toNat 288
      let mem1 := verifyBuffer (verifyAttestScratch mem r) heap.toNat (verifyAttestWords r nonce)
      let L2 := allocateBlockLocals L1 next
      let L3 := verifyAttestHashLocals L2 r nonce
      have hnxt : (UInt256.ofNat next).toNat = next := ulit_toNat' _ (by change next < 2^256; dsimp only [next]; omega)
      have hpa : ExecBlock fork config {contract := contract,locals := L1,immutables := immStore v} (nonceStore evm r.attester)
          (allocateBlock (.intLit 288)) (.ok {contract := contract,locals := L2,immutables := immStore v} (nonceStore evm r.attester)) :=
        allocateBlock_ok (by simp only [evalExpr?,pure]; rfl) hf1 hg
      have hreq2 : L2.get? "request" = some r.struct := (allocateBlockLocals_get (by decide) (by decide) (by decide)).trans hreq1
      have hd2 : L2.get? "data" = some r.data.struct := (allocateBlockLocals_get (by decide) (by decide) (by decide)).trans hd1
      have hn2 : L2.get? "nonce" = some (.int (Int.ofNat nonce.toNat)) := (allocateBlockLocals_get (by decide) (by decide) (by decide)).trans hn1
      have hph := verifyAttestHashSource (fork := fork) (imms := immStore v) (evm := nonceStore evm r.attester) hreq2 hd2 hn2
      have hprefix : MemoryPrefix mem mem1 heap.toNat :=
        (verifyAttestScratch_prefix mem r heap.toNat).trans (verifyBuffer_prefix _ _ _)
      have hv1 := (hv.preserve hprefix hb).mono hg.2
      have hreq3 : L3.get? "request" = some r.struct := by
        simpa (disch := decide) only [L3,verifyAttestHashLocals,store_get_ne] using hreq2
      have hsig3 : L3.get? "signature" = some r.signature.struct := by
        simpa (disch := decide) only [L3,L2,verifyAttestHashLocals,allocateBlockLocals,unpackHeapLocals,store_get_ne] using hs1
      have hhash3 : L3.get? "structHash" = some (wordBytes32Value (verifyAttestHash r nonce)) := store_get_self _ _ _
      have hf3 : L3.get? "$EAS.freeMemory" = some (.int (Int.ofNat next)) := by
        simp (disch := decide) only [L3,L2,verifyAttestHashLocals,allocateBlockLocals,unpackHeapLocals,store_get_ne,store_get_self]
      have hfree : memLoad (UInt256.ofNat 64) mem1 = UInt256.ofNat next := verifyBuffer_free _ _ _
      have ho : (ptr+UInt256.ofNat 96).toNat = ptr.toNat+96 := uadd_word_ofNat_toNat _ _ (by have := hv.span; omega)
      have hrun := verifyDigestRun (L := L3) (field := "attester") (heap := UInt256.ofNat next) v hreq3 (by rfl) hsig3 hhash3
        (by simpa only [hnxt] using hf3) hv1.signature (by rw [hnxt]; exact hv1.sigEnd)
        hv1.attester (by rw [ho]; have := hv1.low; omega) (by rw [ho]; have := hv1.covered; omega)
        (by rw [ho,hnxt]; have := hv1.span; omega) (by omega) hs' hfree
        (by rw [hnxt]; have := hv.low; have := hv.span; dsimp only [next]; omega)
        (by rw [hnxt]; exact hg.1) hret rd1
      simp only [hnxt] at hrun
      exact Or.inl ((hrun.prepend hph (MemoryPrefix.refl _ _) (le_refl _)).prepend hpa hprefix hg.2)
    · rw [if_neg hg] at hr
      exact HeapReturnOrStatic.of_revert_prefix (allocateBlock_revert (imms := immStore v) (evm := nonceStore evm r.attester)
        (by simp only [evalExpr?,pure]; rfl) hf1 hg) hr
  · have hp' : evm.executionEnv.perm = false := by rw [hs.env]; exact Bool.eq_false_iff.mpr hp
    exact Or.inr ⟨ExecFuncBody.execBlockStatic (ExecBlock.consStatic (nonceWriteStatic (L := L1) (imms := immStore v) (evm := evm) (a := r.attester) hnone1 hn1 he1 hp')),
      easVerifyAttestStatic v (by simp only [List.length_cons]; omega) (by rw [← hs.env]; exact hp') rd⟩

def verifyAttestArgs (r : DelegatedAttestationRecord) (heap : Nat) : Store :=
  (∅ : Store).insert "$EAS.freeMemory" (.int (Int.ofNat heap)) |>.insert "request" r.struct
theorem verifyAttest_lookup : lookupCallable? contract "_verifyAttest" = some verifyAttestFunction.toCallable := rfl
theorem verifyAttest_bind (r : DelegatedAttestationRecord) (heap : Nat) :
    bindParams? verifyAttestFunction.params [r.struct,.int (Int.ofNat heap)] = some (verifyAttestArgs r heap) := rfl

theorem verifyAttestCallRun {L : Store} {args : List Expr} {retVar : Ident}
    {ee : ExecutionEnv} {g : Sat256} {s0 evm : EVM.State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {heap ptr dataPtr bytesPtr sigPtr ret : UInt256} {R : List UInt256} {r : DelegatedAttestationRecord} (v : EASImmutables)
    (he : evalExprs? config {contract := contract,locals := L,immutables := immStore v} evm args =
      .ok [r.struct,.int (Int.ofNat heap.toNat)])
    (hstack : R.length+20 ≤ 1024) (hs : SourceState s0 ee σ evm)
    (hv : DelegatedAttestMemoryView mem ptr dataPtr bytesPtr sigPtr r heap.toNat)
    (hh : memLoad (UInt256.ofNat 64) mem = heap) (hheap : heap.toNat ≤ 2^64-1)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨13494⟩ (ptr::ret::R) mem aw rdata σ k C) :
    HeapCallOrStatic fork config (deployedRuntime v) ee g s0 {contract := contract,locals := L,immutables := immStore v}
      evm "_verifyAttest" args retVar (.tuple []) ret R mem heap.toNat := by
  exact (verifyAttestRun (L := verifyAttestArgs r heap.toNat) v
    (by simp only [verifyAttestArgs,store_get_self])
    (by simp (disch := decide) only [verifyAttestArgs,store_get_ne,store_get_empty])
    (by simp (disch := decide) only [verifyAttestArgs,store_get_ne,store_get_self])
    hstack hs hv hh hheap hret rd).call he verifyAttest_lookup (verifyAttest_bind r heap.toNat)

end Benchmarks.EAS.EAS
