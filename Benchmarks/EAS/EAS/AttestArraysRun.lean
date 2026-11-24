import Benchmarks.EAS.EAS.AttestArraysSource
import Benchmarks.EAS.EAS.AttestArraysControl

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

theorem attestArraysRun {L : Store} {evm : EVM.State} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {schema available heap t3 t4 uidPtr : UInt256} {attester : AccountAddress} {last : Bool}
    {rs : List AttestationRequestRecord} {s : SchemaRecord} {R : List UInt256}
    (v : EASImmutables) (site : UIDSite) (hstack : R.length+22 ≤ 1024)
    (hf : AttestSetupLocals L rs s schema attester available last heap.toNat)
    (hm : AttestSetupMemory mem site uidPtr rs s attester heap.toNat)
    (hlen : attestLoopLength site = UInt256.ofNat rs.length)
    (hh : heap.toNat ≤ 2^64-1) (hheap : memLoad (UInt256.ofNat 64) mem = heap)
    (hcd : ee.calldata.size < UInt256.size) (ha : recordArrayPtr site t3 t4 = heap)
    (hv : recordValuesPtr site t4 = UInt256.ofNat (allocateNext heap.toNat (32+352*rs.length)))
    (rd : RD fork (deployedRuntime v) ee g s0 (attestArraysStartPC site)
      (attestArraysStartStack site schema R) mem aw rdata σ k C) :
    let middle := allocateNext heap.toNat (32+352*rs.length)
    let next := allocateNext middle (32+32*rs.length)
    let final := attestArraysMemory mem ee.calldata heap rs.length
    let locals' := attestArraysLocals L rs.length middle next
    (heap.toNat ≤ next ∧ next ≤ 2^64-1 ∧ MemoryPrefix mem final heap.toNat ∧
      AttestLoopMemory final site t3 t4 uidPtr rs s attester
        (defaultArrayPointers heap rs.length) (List.replicate rs.length ⟨0⟩) (List.replicate rs.length ⟨0⟩)
        (List.replicate rs.length defaultAttestationRecord) next ∧
      AttestLoopLocals locals' rs s schema attester available last (List.replicate rs.length defaultAttestationRecord)
        (List.replicate rs.length ⟨0⟩) (List.replicate rs.length ⟨0⟩) ⟨0⟩ 0 next ∧
      ExecBlock fork config {contract := contract,locals := L,immutables := immStore v} evm attestArraysBody
        (.ok {contract := contract,locals := locals',immutables := immStore v} evm) ∧
      ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 (recordNextPC site)
        (recordNextStack site schema ⟨0⟩ t3 t4 R) final aw' rdata σ k' C') ∨
    (ExecBlock fork config {contract := contract,locals := L,immutables := immStore v} evm attestArraysBody .reverted ∧
      RDrev fork (deployedRuntime v) g s0) := by
  dsimp only
  have hspan := hm.uidArray.span
  have hul := hm.uidLow
  simp only [List.length_replicate] at hspan
  have hl : rs.length ≤ 2^64-1 := by omega
  have hn : (attestLoopLength site).toNat = rs.length := by
    rw [hlen,ulit_toNat' _ (by change rs.length < 2^256; omega)]
  have hevm := easAttestArrays v site hstack (by omega) hh hheap hcd ha (by simpa only [hn] using hv) rd
  dsimp only at hevm
  rw [hn,if_pos hl] at hevm
  have hsource := attestArraysSource (fork := fork) (imms := immStore v) (evm := evm) hf.length hf.heap
  dsimp only at hsource
  rw [if_pos hl] at hsource
  by_cases hg1 : allocateNext heap.toNat (32+352*rs.length) ≤ 2^64-1 ∧
      heap.toNat ≤ allocateNext heap.toNat (32+352*rs.length)
  · rw [if_pos hg1] at hevm hsource
    by_cases hg2 : allocateNext (allocateNext heap.toNat (32+352*rs.length)) (32+32*rs.length) ≤ 2^64-1 ∧
        allocateNext heap.toNat (32+352*rs.length) ≤ allocateNext (allocateNext heap.toNat (32+352*rs.length)) (32+32*rs.length)
    · rw [if_pos hg2] at hevm hsource
      have hm' := attestArraysMemory_init (calldata := ee.calldata) hm ha hv hh hl hg1.1
      exact Or.inl ⟨le_trans hg1.2 hg2.2,hg2.1,hm'.1,hm'.2,attestArraysLocals_view hf _ _,hsource,hevm⟩
    · rw [if_neg hg2] at hevm hsource
      exact Or.inr ⟨hsource,hevm⟩
  · rw [if_neg hg1] at hevm hsource
    exact Or.inr ⟨hsource,hevm⟩

end Benchmarks.EAS.EAS
