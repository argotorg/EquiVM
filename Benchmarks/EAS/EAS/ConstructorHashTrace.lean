import Benchmarks.EAS.EAS.ConstructorDomainMemory
import Benchmarks.EAS.EAS.ConstructorFrontTrace

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables easCreationBlocks
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

theorem easCtorBlock106_memory (registry : AccountAddress) :
    easCreation_block_106_memory (tail := (UInt256.ofNat registry.val).toByteArray) (mem := easCtorNameAllocated registry)
      (x0 := UInt256.ofNat 448) (x1 := UInt256.ofNat 416) (x2 := UInt256.ofNat 384) = easCtorDomainPrefix registry := by
  have hs : (UInt256.shiftLeft (UInt256.ofNat 4538707) (UInt256.ofNat 232)).toByteArray.write 0
    ((UInt256.ofNat 3).toByteArray.write 0 (easCtorNameAllocated registry) (UInt256.ofNat 448).toNat 32)
    (UInt256.ofNat 480).toNat 32 = easCtorStringsMemory registry := rfl
  simp only [easCreation_block_106_memory,hs,
    show UInt256.ofNat 448+UInt256.ofNat 32 = UInt256.ofNat 480 by native_decide,
    easCtorStrings_nameLength,easCtorStrings_versionLength,easCtorStrings_nameHash,easCtorStrings_versionHash]
  have hf : memLoad (UInt256.ofNat 64) ((UInt256.ofNat Ethereum.chainId).toByteArray.write 0
    (easCtorVersion.toByteArray.write 0 (easCtorName.toByteArray.write 0 (easCtorStringsMemory registry) (UInt256.ofNat 224).toNat 32)
      (UInt256.ofNat 256).toNat 32) (UInt256.ofNat 160).toNat 32) = UInt256.ofNat 512 := easCtorHashMemory_free registry
  rw [hf]
  change writeWord (writeWord (writeWord (writeWord
    (writeWord ((easCtorCode registry).write 17642 (easCtorHashMemory registry) 0 32) 0 (memLoad (UInt256.ofNat 0) (easCtorHashMemory registry)))
    544 (memLoad (UInt256.ofNat 0) ((easCtorCode registry).write 17642 (easCtorHashMemory registry) 0 32)))
    576 easCtorName) 608 easCtorVersion) 640 (UInt256.ofNat Ethereum.chainId) = _
  rw [easCtorCode_copyType registry _ (by rw [easCtorHashMemory_size]; decide),memLoad_write_at _ _ _ (by decide)]
  rfl

theorem easCtorBlock106_stack (registry : AccountAddress) (ee : ExecutionEnv) (R : List UInt256) :
    easCreation_block_106_stack (ee := ee) (mem := easCtorNameAllocated registry)
      (x0 := UInt256.ofNat 448) (x1 := UInt256.ofNat 416) (x2 := UInt256.ofNat 384) (R := R) =
        UInt256.ofNat 160::UInt256.ofNat ee.codeOwner.val::UInt256.ofNat 512::UInt256.ofNat 544::R := by
  have hs : (UInt256.shiftLeft (UInt256.ofNat 4538707) (UInt256.ofNat 232)).toByteArray.write 0
    ((UInt256.ofNat 3).toByteArray.write 0 (easCtorNameAllocated registry) (UInt256.ofNat 448).toNat 32)
    (UInt256.ofNat 480).toNat 32 = easCtorStringsMemory registry := rfl
  simp only [easCreation_block_106_stack,hs,
    show UInt256.ofNat 448+UInt256.ofNat 32 = UInt256.ofNat 480 by native_decide,
    easCtorStrings_nameLength,easCtorStrings_versionLength,easCtorStrings_nameHash,easCtorStrings_versionHash]
  change UInt256.ofNat 160::UInt256.ofNat ee.codeOwner.val::memLoad (UInt256.ofNat 64) (easCtorHashMemory registry)::
    (memLoad (UInt256.ofNat 64) (easCtorHashMemory registry)+UInt256.ofNat 32)::R = _
  rw [easCtorHashMemory_free]
  rfl

theorem easCtorReachDomain {σ σ₀ A I} {g : Sat256} (registry : AccountAddress)
    (hcode : I.code = easCtorCode registry) (hv : I.weiValue = UInt256.ofNat 0) :
    ∃ aw k C, RD fork (easCtorCode registry) I g (initState σ σ₀ g A I) (UInt256.ofNat 207)
      [UInt256.ofNat 512,UInt256.ofNat 544,UInt256.ofNat registry.val,UInt256.ofNat registry.val]
      (easCtorDomainAllocated registry I.codeOwner) aw ByteArray.empty σ k C := by
  obtain ⟨a,j,D,rd⟩ := easCtorReachStrings (fork := fork) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) registry hcode hv
  obtain ⟨a1,j1,D1,r1⟩ := easCreation_block_106_packed (by simp) rd
  rw [easCtorBlock106_memory,easCtorBlock106_stack] at r1
  obtain ⟨a2,j2,D2,r2⟩ := easCreation_block_190_packed (by simp) (by native_decide) r1
  change RD fork _ _ _ _ _ [UInt256.ofNat 512,UInt256.ofNat 192,UInt256.ofNat 207,UInt256.ofNat 512,
    UInt256.ofNat 544,UInt256.ofNat registry.val,UInt256.ofNat registry.val]
    (easCtorDomainMemory registry I.codeOwner) _ _ _ _ _ at r2
  obtain ⟨a3,j3,D3,r3⟩ := easCtorAllocate .domain (by simp) (by native_decide) r2
  exact ⟨a3,j3,D3,r3⟩

theorem easCtorBlock207_memory (registry : AccountAddress) (ee : ExecutionEnv) :
    easCreation_block_207_fallthrough_memory (tail := (UInt256.ofNat registry.val).toByteArray) (ee := ee)
      (mem := easCtorDomainAllocated registry ee.codeOwner) (x0 := UInt256.ofNat 512) (x1 := UInt256.ofNat 544) =
        easCtorFinalMemory registry ee.codeOwner := by
  simp only [easCreation_block_207_fallthrough_memory,easCtorDomainAllocated_length,easCtorDomainAllocated_hash]
  let pre := writeWord (writeWord (easCtorDomainAllocated registry ee.codeOwner) 128 (easCtorDomain ee.codeOwner)) 192 (UInt256.ofNat ee.codeOwner.val)
  change writeWord (writeWord ((easCtorCode registry).write 17642 pre 0 32) 0 (memLoad (UInt256.ofNat 0) pre)) 288
    (memLoad (UInt256.ofNat 0) ((easCtorCode registry).write 17642 pre 0 32)) = _
  rw [easCtorCode_copyType registry pre (by simp only [pre,writeWord_sparse_size,easCtorDomainAllocated_size]; decide),memLoad_write_at _ _ _ (by decide)]
  rfl

theorem easCtorZeroTrace {σ σ₀ A I} {g : Sat256} (registry : AccountAddress)
    (hcode : I.code = easCtorCode registry) (hv : I.weiValue = UInt256.ofNat 0) (hz : registry = ⟨0,by decide⟩) :
    RDrev fork (easCtorCode registry) g (initState σ σ₀ g A I) := by
  obtain ⟨a,j,D,rd⟩ := easCtorReachDomain (fork := fork) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) registry hcode hv
  obtain ⟨a1,j1,D1,r1⟩ := easCreation_block_207_taken_packed (by simp) (by rw [hz]; decide) (by native_decide) rd
  exact easCreation_block_354 (by simp [easCreation_block_207_taken_stack]) r1

end Benchmarks.EAS.EAS
