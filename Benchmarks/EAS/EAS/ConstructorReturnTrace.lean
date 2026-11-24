import Benchmarks.EAS.EAS.ConstructorReturnMemory
import Benchmarks.EAS.EAS.ConstructorHashTrace

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables easCreationBlocks
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

-- LIBRARY CANDIDATE: expose the word-write abstraction in a generated trace.
theorem byteWord_writeWord (word : UInt256) (mem : ByteArray) (off : Nat) :
    word.toByteArray.write 0 mem off 32 = Reasoning.Theory.writeWord mem off word := rfl

theorem easCtorBlock242_memory (registry : AccountAddress) (ee : ExecutionEnv) :
    easCreation_block_242_memory (tail := (UInt256.ofNat registry.val).toByteArray) (mem := easCtorFinalMemory registry ee.codeOwner)
      (x0 := UInt256.ofNat registry.val) = easCtorReturnMemory9 registry ee.codeOwner := by
  have hp : (UInt256.ofNat registry.val).toByteArray.write 0 (easCtorFinalMemory registry ee.codeOwner) (UInt256.ofNat 320).toNat 32 =
      easCtorReturnPrefix registry ee.codeOwner := rfl
  simp only [easCreation_block_242_memory,hp,easCtorReturnPrefix_free]
  simp (disch := decide) only [ulit_toNat']
  have hcopy := easCtorCopyRuntime registry ee.codeOwner
  change (easCreationBytecode++(UInt256.ofNat registry.val).toByteArray).write 434
    (easCtorReturnPrefix registry ee.codeOwner) 704 17208 = _ at hcopy
  rw [hcopy]
  simp (disch := (first | decide | (simp (disch := decide) only [writeWord_sparse_size,ByteArray.size_append,easCtorReturnPrefix_size,easBytecode_size,ulit_toNat']; omega))) only
    [byteWord_writeWord,memLoad_write_below,memLoad_append_prefix,easCtorReturnPrefix_load,easCtorReturnPrefix_registry,
      easCtorFinalMemory_domain,easCtorFinalMemory_chain,easCtorFinalMemory_owner,easCtorFinalMemory_name,easCtorFinalMemory_version,easCtorFinalMemory_type]
  rfl

theorem easCtorBlock242_stack (registry : AccountAddress) (ee : ExecutionEnv) (R : List UInt256) :
    easCreation_block_242_stack (tail := (UInt256.ofNat registry.val).toByteArray) (mem := easCtorFinalMemory registry ee.codeOwner)
      (x0 := UInt256.ofNat registry.val) (R := R) = UInt256.ofNat 704::UInt256.ofNat registry.val::UInt256.ofNat 704::UInt256.ofNat 17208::R := by
  have hp : (UInt256.ofNat registry.val).toByteArray.write 0 (easCtorFinalMemory registry ee.codeOwner) (UInt256.ofNat 320).toNat 32 =
      easCtorReturnPrefix registry ee.codeOwner := rfl
  simp only [easCreation_block_242_stack,hp,easCtorReturnPrefix_free]
  simp (disch := decide) only [ulit_toNat']
  have hcopy := easCtorCopyRuntime registry ee.codeOwner
  change (easCreationBytecode++(UInt256.ofNat registry.val).toByteArray).write 434
    (easCtorReturnPrefix registry ee.codeOwner) 704 17208 = _ at hcopy
  rw [hcopy]
  simp (disch := (first | decide | (simp (disch := decide) only [writeWord_sparse_size,ByteArray.size_append,easCtorReturnPrefix_size,easBytecode_size,ulit_toNat']; omega))) only
    [byteWord_writeWord,memLoad_write_below,memLoad_append_prefix,easCtorReturnPrefix_load,easCtorReturnPrefix_registry,
      easCtorFinalMemory_domain,easCtorFinalMemory_chain,easCtorFinalMemory_owner,easCtorFinalMemory_name,easCtorFinalMemory_version,easCtorFinalMemory_type]

theorem easCtorSuccessTrace {σ σ₀ A I} {g : Sat256} (registry : AccountAddress)
    (hcode : I.code = easCtorCode registry) (hv : I.weiValue = UInt256.ofNat 0) (hz : registry ≠ ⟨0,by decide⟩) :
    RDret fork (easCtorCode registry) g (initState σ σ₀ g A I) σ
      (immutableLayout.deployed easBytecode (easCtorImms I.codeOwner registry)) := by
  obtain ⟨a,j,D,rd⟩ := easCtorReachDomain (fork := fork) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) registry hcode hv
  have hne : UInt256.ofNat registry.val ≠ ⟨0⟩ := by
    intro he
    have hn := congrArg UInt256.toNat he
    rw [ulit_toNat' registry.val (lt_of_lt_of_le registry.isLt (by decide))] at hn
    exact hz (Fin.ext hn)
  obtain ⟨a1,j1,D1,r1⟩ := easCreation_block_207_fallthrough_packed (by simp) (isZero_eq_zero_of_ne hne) rd
  simp only [easCreation_block_207_fallthrough_stack,easCtorBlock207_memory] at r1
  obtain ⟨a2,j2,D2,r2⟩ := easCreation_block_242_packed (by simp) r1
  rw [easCtorBlock242_memory,easCtorBlock242_stack] at r2
  have hr := easCreation_block_341 (by simp) r2
  change RDret fork _ _ _ _ ((easCtorReturnMemory registry I.codeOwner).readWithPadding 704 17208) at hr
  simpa only [easCtorReturnMemory_read] using hr

end Benchmarks.EAS.EAS
