import Benchmarks.EAS.EAS.RefundEVM

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

-- Pair the modular source call with the EVM return or revert, including heap preservation.
theorem refundRun {cfg : Config} {locals imms : Store} {args : List Expr} {retVar : Ident}
    {ee : ExecutionEnv} {g : Sat256} {s0 evm : EVM.State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {value ptr ret : UInt256} {R : List UInt256} (v : EASImmutables)
    (hstack : R.length+12 ≤ 1024) (hperm : ee.perm = true) (hs : SourceState s0 ee σ evm)
    (hheap : ptr.toNat ≤ 2^64-1) (hlo : 96 ≤ ptr.toNat) (hh : memLoad (UInt256.ofNat 64) mem = ptr)
    (he : evalExprs? cfg {contract := contract, locals := locals, immutables := imms} evm args =
      .ok [.int (Int.ofNat value.toNat),.int (Int.ofNat ptr.toNat)])
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨16342⟩ (value::ret::R) mem aw rdata σ k C) :
    (∃ (evm' : EVM.State) (σ' : AccountMap) (mem' out : ByteArray) (aw' : UInt256) (k' C' heap' : Nat),
      SourceState s0 ee σ' evm' ∧ ptr.toNat ≤ heap' ∧ heap' ≤ 2^64-1 ∧
      MemoryPrefix mem mem' ptr.toNat ∧ memLoad (UInt256.ofNat 64) mem' = UInt256.ofNat heap' ∧
      ExecStmt fork cfg {contract := contract, locals := locals, immutables := imms} evm (.internalCall "_refund" args retVar)
        (.ok {contract := contract, locals := locals.insert retVar (.tuple [.tuple [],.int (Int.ofNat heap')]), immutables := imms} evm') ∧
      RD fork (deployedRuntime v) ee g s0 ret R mem' aw' out σ' k' C') ∨
    (ExecStmt fork cfg {contract := contract, locals := locals, immutables := imms} evm (.internalCall "_refund" args retVar) .reverted ∧
      RDrev fork (deployedRuntime v) g s0) := by
  by_cases hz : value = ⟨0⟩
  · subst value
    obtain ⟨aw1,k1,C1,rd1⟩ := refundEVM_zero v (by omega) hret rd
    exact Or.inl ⟨evm,σ,mem,rdata,aw1,k1,C1,ptr.toNat,hs,le_refl _,hheap,MemoryPrefix.refl _ _,
      by simpa only [u256_ofNat_toNat] using hh,refundCall_zero he,rd1⟩
  · by_cases hb : value.toNat ≤ (refundBalance evm).toNat
    · obtain ⟨evm',σ',success,out,hc,hs',hout,hr⟩ := refundEVM v hstack hperm hs hz hb hheap hh hret rd
      have hsrc := refundCall (hperm := (congrArg ExecutionEnv.perm hs.env).trans hperm) (retVar := retVar) he hz hb hc
      by_cases hv : refundResultValid ptr.toNat success out
      · rw [if_pos hv] at hr hsrc
        obtain ⟨aw1,k1,C1,rd1⟩ := hr
        have hnext : ptr.toNat ≤ refundNext ptr.toNat out.size ∧ refundNext ptr.toNat out.size ≤ 2^64-1 := by
          rcases hv.2 with hz' | ⟨_,hnext,hmono⟩
          · simp only [refundNext, hz', if_true]
            exact ⟨le_refl _,hheap⟩
          · unfold refundNext
            split
            · exact ⟨le_refl _,hheap⟩
            · exact ⟨hmono,hnext⟩
        exact Or.inl ⟨evm',σ',refundMemory mem ptr out,out,aw1,k1,C1,refundNext ptr.toNat out.size,hs',
          hnext.1,hnext.2,refundMemory_prefix mem ptr out,refundMemory_heap out hlo hh,hsrc,rd1⟩
      · rw [if_neg hv] at hr hsrc
        exact Or.inr ⟨hsrc,hr⟩
    · exact Or.inr ⟨refundCall_insufficient he hz hb,refundEVM_insufficient v (by omega) hs hz hb rd⟩

end Benchmarks.EAS.EAS
