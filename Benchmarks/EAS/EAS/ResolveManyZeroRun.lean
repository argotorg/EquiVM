import Benchmarks.EAS.EAS.ResolveManyZeroControl
import Benchmarks.EAS.EAS.ResolveManySource
import Benchmarks.EAS.EAS.WhileInvariant

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

theorem resolveManyZeroRun {locals imms : Store} {ee : ExecutionEnv} {g : Sat256} {s0 evm : EVM.State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C heap : Nat}
    {values ret : UInt256} {words : List UInt256} {R : List UInt256} (v : EASImmutables) (rev : Bool)
    (hvalues : locals.get? "values" = some (.array (words.map fun w => .int (Int.ofNat w.toNat))))
    (hlength : locals.get? "length" = some (.int (Int.ofNat words.length)))
    (hcursor : locals.get? "$EAS.freeMemory" = some (.int (Int.ofNat heap)))
    (hstack : R.length+11 ≤ 1024) (hs : SourceState s0 ee σ evm)
    (hv : WordArrayMemoryView mem values words heap) (hheap : heap ≤ 2^64-1)
    (hh : memLoad (UInt256.ofNat 64) mem = UInt256.ofNat heap)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD fork (deployedRuntime v) ee g s0 (resolveManyZeroPC rev)
      (resolveManyZeroStack rev 0 values words.length (ret::R)) mem aw rdata σ k C) :
    HeapReturnRun fork config (deployedRuntime v) ee g s0 {contract := contract, locals := locals, immutables := imms}
      evm resolveManyZeroBody (.int 0) ret (⟨0⟩::R) mem heap := by
  have hlimit : heap < UInt256.size := by change heap < 2^256; omega
  have hlen : words.length < UInt256.size := by have := hv.span; omega
  let Inv := fun i L e => e=evm ∧ ResolveManyZeroLocals L words heap i ∧
    ∃ a j D, RD fork (deployedRuntime v) ee g s0 (resolveManyZeroPC rev)
      (resolveManyZeroStack rev i values words.length (ret::R)) mem a rdata σ j D
  let Post := fun L e => e=evm ∧ ResolveManyZeroLocals L words heap words.length ∧
    ∃ a j D, RD fork (deployedRuntime v) ee g s0 ret (⟨0⟩::R) mem a rdata σ j D
  have hguard : ∀ i L e, i ≤ words.length → Inv i L e →
      evalExpr? config {contract := contract, locals := L, immutables := imms} e timeArrayGuard =
        .ok (.bool (decide (i < words.length))) := by
    intro i L e _ h
    exact resolveManyZeroGuardSource h.2.1
  have hend : ∀ L e, Inv words.length L e → Post L e := by
    rintro L e ⟨he,hf,a,j,D,hr⟩
    exact ⟨he,hf,resolveManyZeroDone v rev (by omega) hret hr⟩
  have hstep : ∀ i L e, i < words.length → Inv i L e →
      (∃ L' e', ExecBlock fork config {contract := contract, locals := L, immutables := imms} e resolveManyZeroIteration
        (.ok {contract := contract, locals := L', immutables := imms} e') ∧ Inv (i+1) L' e') ∨
      (ExecBlock fork config {contract := contract, locals := L, immutables := imms} e resolveManyZeroIteration .reverted ∧
        RDrev fork (deployedRuntime v) g s0) ∨
      (ExecBlock fork config {contract := contract, locals := L, immutables := imms} e resolveManyZeroIteration .staticViolation ∧ False) := by
    rintro i L e hi ⟨he,hf,a,j,D,hr⟩
    subst e
    have hsrc := resolveManyZeroIterationSource (fork := fork) (cfg := config) (imms := imms) (evm := evm) hf hi hlen
    have hnext := resolveManyZeroStep v rev (by simp only [List.length_cons]; omega) hv hi hlimit hr
    by_cases hz : words[i] = ⟨0⟩
    · rw [if_pos hz] at hsrc hnext
      exact Or.inl ⟨L.insert "i" (.int (Int.ofNat (i+1))),evm,hsrc,rfl,hf.next,hnext⟩
    · rw [if_neg hz] at hsrc hnext
      exact Or.inr (Or.inl ⟨hsrc,hnext⟩)
  let L0 := locals.insert "i" (.int 0)
  have hf0 : ResolveManyZeroLocals L0 words heap 0 := by
    constructor <;> simp (disch := decide) only [L0,store_get_self,store_get_ne] <;> first | assumption | rfl
  have hloop := execWhile_invariant (cfg := config) (contract := contract) (imms := imms)
    (cond := timeArrayGuard) (body := resolveManyZeroIteration) (bound := words.length)
    Inv Post (RDrev fork (deployedRuntime v) g s0) False hguard hend hstep
    words.length 0 L0 evm (by omega) ⟨rfl,hf0,aw,k,C,rd⟩
  have hinit : ExecStmt fork config {contract := contract, locals := locals, immutables := imms} evm resolveManyIndexInit
      (.ok {contract := contract, locals := L0, immutables := imms} evm) :=
    ExecStmt.letDecl (by simp only [evalExpr?]; rfl)
  rcases hloop with ⟨L,e,hloop,he,hf,a,j,D,hr⟩ | ⟨hloop,hr⟩ | ⟨_,hfalse⟩
  · subst e
    refine Or.inl ⟨{contract := contract, locals := L, immutables := imms},evm,σ,mem,rdata,a,j,D,heap,
      hs,le_refl _,hheap,MemoryPrefix.refl _ _,hh,?_,hr⟩
    apply ExecFuncBody.execBlockRet (ExecBlock.consNormal hinit (ExecBlock.consNormal hloop (ExecBlock.consReturn (ExecStmt.return ?_))))
    simp only [evalExprs?,evalExpr?,hf.heap,EvalResult.ofOption,EvalResult.bind,bind,pure]
  · exact Or.inr ⟨ExecFuncBody.execBlockRevert (ExecBlock.consNormal hinit (ExecBlock.consRevert hloop)),hr⟩
  · exact hfalse.elim

end Benchmarks.EAS.EAS
