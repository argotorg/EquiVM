import Benchmarks.EAS.EAS.ResolveManyAmountRun

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

theorem resolveManyIterationRun {locals imms : Store} {ee : ExecutionEnv} {g : Sat256} {s0 evm : EVM.State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C i : Nat}
    {array values available total ptr : UInt256} {R : List UInt256}
    {ats : List AttestationRecord} {words : List UInt256} {target : AccountAddress} {rev last : Bool}
    (v : EASImmutables) (hf : ResolveManyLocals locals ats words target available total rev last ptr.toNat i)
    (hi : i < words.length) (hstack : R.length+21 ≤ 1024) (hs : SourceState s0 ee σ evm)
    (hv : WordArrayMemoryView mem values words ptr.toNat)
    (hheap : ptr.toNat ≤ 2^64-1) (hh : memLoad (UInt256.ofNat 64) mem = ptr)
    (rd : RD fork (deployedRuntime v) ee g s0 (resolveManyLoopPC rev)
      (resolveManyLoopStack rev i array (UInt256.ofNat target.val) values available last.toUInt256 total words.length R)
      mem aw rdata σ k C) :
    HeapBlockRun fork config (deployedRuntime v) ee g s0 {contract := contract, locals := locals, immutables := imms}
      evm resolveManyIteration
      (fun L heap => ResolveManyLocals L ats words target (UInt256.sub available words[i]) (total+words[i]) rev last heap (i+1) ∧ words[i].toNat ≤ available.toNat)
      (resolveManyLoopPC rev)
      (resolveManyLoopStack rev (i+1) array (UInt256.ofNat target.val) values (UInt256.sub available words[i])
        last.toUInt256 (total+words[i]) words.length R) mem ptr.toNat := by
  have hlen : words.length < UInt256.size := by change words.length < 2^256; have := hv.span; omega
  have hlo : 96 ≤ ptr.toNat := by have := hv.low; have := hv.span; omega
  let L1 := locals.insert "value" (.int (Int.ofNat words[i].toNat))
  have hf1 : ResolveManyLocals L1 ats words target available total rev last ptr.toNat i := hf.withValue words[i]
  have hvalue : L1.get? "value" = some (.int (Int.ofNat words[i].toNat)) := store_get_self _ _ _
  have hlet : ExecBlock fork config {contract := contract, locals := locals, immutables := imms} evm
      [.letDecl "value" (some abiUInt256) (.index (.var "values") (.var "i"))]
      (.ok {contract := contract, locals := L1, immutables := imms} evm) :=
    ExecBlock.consNormal (ExecStmt.letDecl (evalWordArrayIndex
      (by simp only [evalExpr?,hf.values,EvalResult.ofOption])
      (by simp only [evalExpr?,hf.index,EvalResult.ofOption]) hi)) ExecBlock.nil
  have he : evalExpr? config {contract := contract, locals := L1, immutables := imms} evm resolveOneValueNonzero =
      .ok (.bool (decide (words[i] ≠ ⟨0⟩))) :=
    evalWordNeZero (by simp only [evalExpr?,hvalue,EvalResult.ofOption])
  have hread := resolveManyRead v rev (by omega) hv hi ptr.val.isLt rd
  by_cases hz : words[i] = ⟨0⟩
  · rw [if_pos hz] at hread
    obtain ⟨a1,k1,C1,r1⟩ := hread
    have hnext := resolveManyAmountRun (imms := imms) v hf1 hvalue hi hlen (by omega) hs hheap hh r1
    have hpay : ExecStmt fork config {contract := contract, locals := L1, immutables := imms} evm resolveOnePayment
        (.ok {contract := contract, locals := L1, immutables := imms} evm) :=
      ExecStmt.iteFalse (by simpa only [hz,ne_self_iff_false,decide_false] using he) ExecBlock.nil
    exact (hnext.prepend (ExecBlock.consNormal hpay ExecBlock.nil) (MemoryPrefix.refl _ _) (le_refl _)).prepend (front := [.letDecl "value" (some abiUInt256) (.index (.var "values") (.var "i"))])
      hlet (MemoryPrefix.refl _ _) (le_refl _)
  · rw [if_neg hz] at hread
    obtain ⟨a1,k1,C1,r1⟩ := hread
    obtain ⟨evm',σ',success,out,hcall,hs',hout,hr⟩ := resolveManyPayableEVM v rev (by omega) hs hheap hlo hh r1
    simp only [accountAddress_roundtrip] at hcall
    have hsource := payableCheckSource (imms := imms) hf1.resolver hf1.heap hcall (by omega)
    by_cases hg : callBoolAccepted ptr.toNat success out
    · rw [if_pos hg] at hsource hr
      obtain ⟨a2,k2,C2,r2⟩ := hr
      have hmin : min out.size 32 = 32 := Nat.min_eq_right hg.1.2.2.1
      have ha : allocateNext ptr.toNat 32 ≤ 2^64-1 ∧ ptr.toNat ≤ allocateNext ptr.toNat 32 := by
        simpa only [hmin] using hg.1.2.1
      let nextPtr := UInt256.ofNat (allocateNext ptr.toNat 32)
      have hn : nextPtr.toNat = allocateNext ptr.toNat 32 := ulit_toNat' _ (by change _ < 2^256; omega)
      have hf2 : ResolveManyLocals (payableProbeLocals L1 out ptr.toNat) ats words target available total rev last nextPtr.toNat i := by
        simpa only [hn] using hf1.payment out
      have hv2 : (payableProbeLocals L1 out ptr.toNat).get? "value" = some (.int (Int.ofNat words[i].toNat)) := by
        simpa (disch := decide) only [payableProbeLocals,allocateBlockLocals,unpackHeapLocals,store_get_ne] using hvalue
      have hh2 : memLoad (UInt256.ofNat 64) (payableOutputMemory mem ptr out) = nextPtr := by
        simpa only [hmin] using payableOutputMemory_heap mem ptr out
      have hnext := resolveManyAmountRun (imms := imms) v hf2 hv2 hi hlen (by omega) hs'
        (by rw [hn]; exact ha.1) hh2 r2
      simp only [hn] at hnext
      have hp := payableOutputMemory_prefix mem ptr out (by change out.size < 2^256; omega)
      have hpay : ExecStmt fork config {contract := contract, locals := L1, immutables := imms} evm resolveOnePayment
          (.ok {contract := contract, locals := payableProbeLocals L1 out ptr.toNat, immutables := imms} evm') :=
        ExecStmt.iteTrue (by simpa only [decide_eq_true hz] using he) hsource
      exact (hnext.prepend (ExecBlock.consNormal hpay ExecBlock.nil) hp ha.2).prepend (front := [.letDecl "value" (some abiUInt256) (.index (.var "values") (.var "i"))])
        hlet (MemoryPrefix.refl _ _) (le_refl _)
    · rw [if_neg hg] at hsource hr
      have hpay : ExecBlock fork config {contract := contract, locals := L1, immutables := imms} evm [resolveOnePayment] .reverted :=
        ExecBlock.consRevert (ExecStmt.iteTrue (by simpa only [decide_eq_true hz] using he) hsource)
      exact (HeapBlockRun.of_revert_prefix (suffix := resolveOneAmountBlock ++ [resolveManyTotalUpdate,resolveManyIncrement]) hpay hr).prepend (front := [.letDecl "value" (some abiUInt256) (.index (.var "values") (.var "i"))])
        hlet (MemoryPrefix.refl _ _) (le_refl _)

end Benchmarks.EAS.EAS
