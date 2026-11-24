import Benchmarks.EAS.EAS.ConstructorMemoryBase
import Benchmarks.EAS.EAS.CreationBlocks_001
import Benchmarks.EAS.EAS.CreationBlocks_002

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables easCreationBlocks
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

inductive CtorAllocation where | arg | version | name | domain
def CtorAllocation.heap : CtorAllocation → Nat | .arg => 352 | .version => 384 | .name => 448 | .domain => 512
def CtorAllocation.size : CtorAllocation → Nat | .arg => 32 | .version => 64 | .name => 64 | .domain => 192
def CtorAllocation.next (site : CtorAllocation) : Nat := site.heap+site.size

theorem easCtorAllocate {ee : ExecutionEnv} {g : Sat256} {s0 : State} {tail mem : ByteArray}
    {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat} {ret : UInt256} {R : List UInt256}
    (site : CtorAllocation) (hs : R.length+6 ≤ 1024)
    (hret : (D_J easCreationBytecode 0).contains ret = true)
    (rd : RD fork (easCreationBytecode++tail) ee g s0 (UInt256.ofNat 376)
      (UInt256.ofNat site.heap::UInt256.ofNat site.size::ret::R) mem aw rdata σ k C) :
    ∃ a j D, RD fork (easCreationBytecode++tail) ee g s0 ret R (writeWord mem 64 (UInt256.ofNat site.next)) a rdata σ j D := by
  obtain ⟨a1,j1,D1,r1⟩ := easCreation_block_376_fallthrough_packed (by simp only [List.length_cons]; omega)
    (by cases site <;> native_decide) rd
  have he : UInt256.ofNat site.heap + UInt256.land (UInt256.lnot (UInt256.ofNat 31)) (UInt256.ofNat site.size+UInt256.ofNat 31) = UInt256.ofNat site.next := by
    cases site <;> native_decide
  simp only [easCreation_block_376_fallthrough_stack,he] at r1
  exact easCreation_block_407_packed (by omega) hret r1

theorem easCtorNonpayableTrace {σ σ₀ A I} {g : Sat256} {tail : ByteArray}
    (hcode : I.code = easCreationBytecode++tail) (hv : I.weiValue ≠ UInt256.ofNat 0) :
    RDrev fork (easCreationBytecode++tail) g (initState σ σ₀ g A I) := by
  have h0 := RD.initState (fork := fork) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) hcode
  obtain ⟨a1,j1,D1,h1⟩ := easCreation_block_0_taken_packed (by simp) hv (by native_decide) h0
  exact easCreation_block_371 (by simp [easCreation_block_0_taken_stack]) h1

theorem easCtorReachStrings {σ σ₀ A I} {g : Sat256} (registry : AccountAddress)
    (hcode : I.code = easCtorCode registry) (hv : I.weiValue = UInt256.ofNat 0) :
    ∃ aw k C, RD fork (easCtorCode registry) I g (initState σ σ₀ g A I) (UInt256.ofNat 106)
      [UInt256.ofNat 448,UInt256.ofNat 416,UInt256.ofNat 384,UInt256.ofNat registry.val,UInt256.ofNat registry.val]
      (easCtorNameAllocated registry) aw ByteArray.empty σ k C := by
  have h0 := RD.initState (fork := fork) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) hcode
  obtain ⟨a1,j1,D1,h1⟩ := easCreation_block_0_fallthrough_packed (by simp) hv h0
  change RD fork _ _ _ _ _ [UInt256.ofNat 352] easCtorFreeMemory _ _ _ _ _ at h1
  obtain ⟨a2,j2,D2,h2⟩ := easCreation_block_12_packed (by simp) (by native_decide) h1
  have hsz : (easCreationBytecode++(UInt256.ofNat registry.val).toByteArray).size = 17706 := easCtorCode_size registry
  simp only [easCreation_block_12_stack,hsz,
    show UInt256.sub (UInt256.ofNat 17706) (UInt256.ofNat 17674) = UInt256.ofNat 32 by native_decide] at h2
  obtain ⟨a3,j3,D3,h3⟩ := easCtorAllocate .arg (by simp) (by native_decide) h2
  change RD fork _ _ _ _ _ [UInt256.ofNat 17674,UInt256.ofNat 32,UInt256.ofNat 32,UInt256.ofNat 352,UInt256.ofNat 32,UInt256.ofNat 352]
    easCtorArgAllocated _ _ _ _ _ at h3
  obtain ⟨a4,j4,D4,h4⟩ := easCreation_block_32_fallthrough_packed (by simp) (by native_decide) h3
  change RD fork _ _ _ _ _ [UInt256.ofNat 352] ((easCtorCode registry).write 17674 easCtorArgAllocated 352 32) _ _ _ _ _ at h4
  rw [easCtorCode_copyArg] at h4
  have hmask : UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1) = solcAddrMask := by native_decide
  have hc : UInt256.land (UInt256.ofNat registry.val) solcAddrMask = UInt256.ofNat registry.val := by exact addressWord_val_clean registry
  obtain ⟨a5,j5,D5,h5⟩ := easCreation_block_43_fallthrough_packed (by simp)
    (by rw [easCtorABIMemory_load,hmask,hc,u256_sub_self]; rfl) h4
  simp only [easCreation_block_43_fallthrough_stack,easCtorABIMemory_load,hmask,hc] at h5
  obtain ⟨a6,j6,D6,h6⟩ := easCreation_block_61_packed (by simp) (by native_decide) h5
  simp only [easCreation_block_61_stack,easCtorABIMemory_free] at h6
  obtain ⟨a7,j7,D7,h7⟩ := easCtorAllocate .version (by simp) (by native_decide) h6
  change RD fork _ _ _ _ _ [UInt256.ofNat 384,UInt256.ofNat registry.val,UInt256.ofNat registry.val]
    (easCtorVersionAllocated registry) _ _ _ _ _ at h7
  obtain ⟨a8,j8,D8,h8⟩ := easCreation_block_74_packed (by simp) (by native_decide) h7
  have hm : easCreation_block_74_memory (mem := easCtorVersionAllocated registry) (x0 := UInt256.ofNat 384) = easCtorVersionMemory registry := rfl
  have hl : memLoad (UInt256.ofNat 64) (easCreation_block_74_memory (mem := easCtorVersionAllocated registry) (x0 := UInt256.ofNat 384)) = UInt256.ofNat 448 := by rw [hm,easCtorVersionMemory_free]
  change RD fork _ _ _ _ _ (memLoad (UInt256.ofNat 64) (easCtorVersionMemory registry)::UInt256.ofNat 64::UInt256.ofNat 106::
    memLoad (UInt256.ofNat 64) (easCtorVersionMemory registry)::UInt256.ofNat 416::UInt256.ofNat 384::
    UInt256.ofNat registry.val::UInt256.ofNat registry.val::[]) (easCtorVersionMemory registry) _ _ _ _ _ at h8
  rw [easCtorVersionMemory_free] at h8
  obtain ⟨a9,j9,D9,h9⟩ := easCtorAllocate .name (by simp) (by native_decide) h8
  exact ⟨a9,j9,D9,h9⟩

end Benchmarks.EAS.EAS
