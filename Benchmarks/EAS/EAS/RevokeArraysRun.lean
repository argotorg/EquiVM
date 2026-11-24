import Benchmarks.EAS.EAS.RevokeSetup
import Benchmarks.EAS.EAS.RevokeArraysEVM

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS

theorem revokeArraysRun {L : Store} {evm : EVM.State} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {rs : List RevocationRequestRecord} {s : SchemaRecord} {R : List UInt256}
    (v : EASImmutables) (site : RevokeSite) (hstack : R.length+22 ≤ 1024)
    (hf : RevokeSetupLocals L site rs s site.records.toNat) (hm : RevokeSetupMemory mem site rs s)
    (hlen : rs.length = site.length) (hh : site.records.toNat ≤ 2^64-1)
    (hheap : memLoad (UInt256.ofNat 64) mem = site.records) (hcd : ee.calldata.size < UInt256.size)
    (hv : site.values = UInt256.ofNat (allocateNext site.records.toNat (32+352*rs.length)))
    (rd : RD fork (deployedRuntime v) ee g s0 site.kind.arraysPC (revokeArraysStack site R) mem aw rdata σ k C) :
    let middle := allocateNext site.records.toNat (32+352*rs.length)
    let next := allocateNext middle (32+32*rs.length)
    let final := attestArraysMemory mem ee.calldata site.records rs.length
    let locals' := attestArraysLocals L rs.length middle next
    (site.records.toNat ≤ next ∧ next ≤ 2^64-1 ∧ MemoryPrefix mem final site.records.toNat ∧
      RevokeLoopMemory final site rs s (defaultArrayPointers site.records rs.length)
        (List.replicate rs.length ⟨0⟩) (List.replicate rs.length defaultAttestationRecord) next ∧
      RevokeLoopLocals locals' site rs s (List.replicate rs.length defaultAttestationRecord) (List.replicate rs.length ⟨0⟩) 0 next ∧
      ExecBlock fork config {contract := contract,locals := L,immutables := immStore v} evm attestArraysBody
        (.ok {contract := contract,locals := locals',immutables := immStore v} evm) ∧
      ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 site.kind.loopPC (revokeLoopStack site ee ⟨0⟩ R) final aw' rdata σ k' C') ∨
    (ExecBlock fork config {contract := contract,locals := L,immutables := immStore v} evm attestArraysBody .reverted ∧
      RDrev fork (deployedRuntime v) g s0) := by
  dsimp only
  have hspan := hm.requests.span
  have hsh := hm.schemaHigh
  have hsl := hm.schemaView.low
  have hl : rs.length ≤ 2^64-1 := by omega
  have hb : rs.length < UInt256.size := by change rs.length < 2^256; omega
  have hevm := easRevokeArrays v site hstack (by omega) hh (by omega)
    (by simpa only [← hlen] using hm.requests.length) hheap hcd (by simpa only [← hlen] using hv) rd
  dsimp only at hevm
  rw [← hlen,if_pos hl] at hevm
  have hsource := attestArraysSource (fork := fork) (imms := immStore v) (evm := evm) hf.length hf.heap
  dsimp only at hsource
  rw [if_pos hl] at hsource
  by_cases hg1 : allocateNext site.records.toNat (32+352*rs.length) ≤ 2^64-1 ∧
      site.records.toNat ≤ allocateNext site.records.toNat (32+352*rs.length)
  · rw [if_pos hg1] at hevm hsource
    by_cases hg2 : allocateNext (allocateNext site.records.toNat (32+352*rs.length)) (32+32*rs.length) ≤ 2^64-1 ∧
        allocateNext site.records.toNat (32+352*rs.length) ≤ allocateNext (allocateNext site.records.toNat (32+352*rs.length)) (32+32*rs.length)
    · rw [if_pos hg2] at hevm hsource
      have hm' := revokeArraysMemory_init (calldata := ee.calldata) hm hlen hv hh hl hg1.1
      exact Or.inl ⟨le_trans hg1.2 hg2.2,hg2.1,hm'.1,hm'.2,revokeArraysLocals_view hf _ _,hsource,hevm⟩
    · rw [if_neg hg2] at hevm hsource
      exact Or.inr ⟨hsource,hevm⟩
  · rw [if_neg hg1] at hevm hsource
    exact Or.inr ⟨hsource,hevm⟩

end Benchmarks.EAS.EAS
