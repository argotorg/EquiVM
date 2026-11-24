import Benchmarks.EAS.EAS.BuildDomain
import Benchmarks.EAS.EAS.WordSequence

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

def buildDomainMemory (mem : ByteArray) (heap : Nat) (t n v : UInt256) (owner : AccountAddress) : ByteArray :=
  Reasoning.Theory.writeWord
    (Reasoning.Theory.writeWord
      (writeWordSequence mem (heap + 32) [t, n, v, UInt256.ofNat Ethereum.chainId, UInt256.ofNat owner.val])
      heap (UInt256.ofNat 160))
    64 (UInt256.ofNat (allocateNext heap 192))

theorem domainPayload_wordBytes (t n v : UInt256) (owner : AccountAddress) :
    domainPayload t n v owner = wordBytes [t, n, v, UInt256.ofNat Ethereum.chainId, UInt256.ofNat owner.val] := by
  rw [wordBytes_eq_list]
  simp only [domainPayload, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc]
  exact mk_toArray_eq _

theorem buildDomainMemory_payload (mem : ByteArray) (heap : Nat) (t n v : UInt256) (owner : AccountAddress)
    (hlo : 96 ≤ heap) :
    (buildDomainMemory mem heap t n v owner).readWithPadding (heap + 32) 160 = domainPayload t n v owner := by
  let body := writeWordSequence mem (heap + 32) [t, n, v, UInt256.ofNat Ethereum.chainId, UInt256.ofNat owner.val]
  have hsize : heap + 192 ≤ body.size := by
    have h := writeWordSequence_covers mem (heap + 32)
      [t, n, v, UInt256.ofNat Ethereum.chainId, UInt256.ofNat owner.val] (by simp)
    simpa only [List.length_cons, List.length_nil] using h
  have hu := lt_usize 0 (by decide)
  change (Reasoning.Theory.writeWord (Reasoning.Theory.writeWord body heap ⟨160⟩) 64 _).readWithPadding _ _ = _
  rw [writeWord_read_preserved_len _ 64 (heap + 32) 160 _
    (by rw [writeWord_sparse_size]; omega)
    (Or.inr ⟨by omega, by rw [writeWord_sparse_size]; omega⟩) (by decide) (by decide)]
  rw [writeWord_read_preserved_len body heap (heap + 32) 160 _
    (by omega) (Or.inr ⟨by omega, by omega⟩) (by decide) (by decide)]
  rw [domainPayload_wordBytes]
  exact writeWordSequence_read _ _ _

theorem buildDomainMemory_size (mem : ByteArray) (heap : Nat) (t n v : UInt256) (owner : AccountAddress) :
    heap + 192 ≤ (buildDomainMemory mem heap t n v owner).size := by
  have h := writeWordSequence_covers mem (heap + 32)
    [t, n, v, UInt256.ofNat Ethereum.chainId, UInt256.ofNat owner.val] (by simp)
  simp only [List.length_cons, List.length_nil] at h
  simp only [buildDomainMemory, writeWord_sparse_size]
  omega

theorem buildDomainMemory_header (mem : ByteArray) (heap : Nat) (t n v : UInt256) (owner : AccountAddress)
    (hlo : 96 ≤ heap) :
    (buildDomainMemory mem heap t n v owner).readWithPadding heap 32 = (UInt256.ofNat 160).toByteArray := by
  unfold buildDomainMemory
  rw [writeWord_sparse_read_preserved _ 64 heap _
    (Or.inr ⟨hlo, by rw [writeWord_sparse_size]; omega⟩), writeWord_sparse_read_back]

theorem buildDomainMemory_free (mem : ByteArray) (heap : Nat) (t n v : UInt256) (owner : AccountAddress) :
    (buildDomainMemory mem heap t n v owner).readWithPadding 64 32 =
      (UInt256.ofNat (allocateNext heap 192)).toByteArray := writeWord_sparse_read_back _ _ _

theorem buildDomainMemory_keccak (mem : ByteArray) (heap : UInt256) (t n v : UInt256) (owner : AccountAddress)
    (hlo : 96 ≤ heap.toNat) (hfit : heap.toNat + 192 < UInt256.size) :
    keccakWord (heap + UInt256.ofNat 32)
      (memLoad heap (buildDomainMemory mem heap.toNat t n v owner))
      (buildDomainMemory mem heap.toNat t n v owner) = builtDomainWord t n v owner := by
  have hl : memLoad heap (buildDomainMemory mem heap.toNat t n v owner) = UInt256.ofNat 160 :=
    mloadWordValue_of_readWithPadding (by have h := buildDomainMemory_size mem heap.toNat t n v owner; omega)
      (buildDomainMemory_header mem heap.toNat t n v owner hlo)
  have hadd : (heap + UInt256.ofNat 32).toNat = heap.toNat + 32 :=
    addWord_toNat _ _ (by change heap.toNat + 32 < UInt256.size; omega)
  rw [hl, keccakWord, hadd]
  change UInt256.ofNat (fromByteArrayBigEndian (KEC
    ((buildDomainMemory mem heap.toNat t n v owner).readWithPadding (heap.toNat + 32) 160))) = _
  rw [buildDomainMemory_payload mem heap.toNat t n v owner hlo]
  exact (uInt256OfByteArray_eq _).symm

theorem allocate192_fits {heap : Nat}
    (hguard : allocateNext heap 192 ≤ 2^64-1 ∧ heap ≤ allocateNext heap 192) :
    allocateNext heap 192 = heap + 192 ∧ heap + 192 ≤ 2^64-1 := by
  have hb : heap ≤ 2^64-1 := le_trans hguard.2 hguard.1
  have hn : allocateNext heap 192 = heap + 192 := by
    change (heap + 192) % UInt256.size = heap + 192
    apply Nat.mod_eq_of_lt
    change heap + 192 < 2^256
    omega
  exact ⟨hn, by rw [hn] at hguard; exact hguard.1⟩


theorem easBuildDomain_ok {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {heap ret : UInt256} {R : List UInt256} (v : EASImmutables)
    (hstack : R.length + 8 ≤ 1024)
    (hfree : memLoad (UInt256.ofNat 64) mem = heap)
    (hlo : 96 ≤ heap.toNat)
    (hguard : allocateNext heap.toNat 192 ≤ 2^64-1 ∧ heap.toNat ≤ allocateNext heap.toNat 192)
    (hvalid : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨14063⟩ (ret :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 ret
      (builtDomainWord v._TYPE_HASH v._HASHED_NAME v._HASHED_VERSION ee.codeOwner :: R)
      (buildDomainMemory mem heap.toNat v._TYPE_HASH v._HASHED_NAME v._HASHED_VERSION ee.codeOwner)
      aw' rdata σ k' C' := by
  obtain ⟨aw1, k1, C1, rd1⟩ := easBlocks.eas_block_14063_packed (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
  simp only [easBlocks.eas_block_14063_stack, hfree] at rd1
  obtain ⟨aw2, k2, C2, rd2⟩ := easAllocate_ok (heap := heap) (size := UInt256.ofNat 192)
    (ret := UInt256.ofNat 14209) (R := heap :: (heap + UInt256.ofNat 32) :: ret :: R) v (by simp only [List.length_cons]; omega) hguard
    (by rw [easPatchedValidJumps v]; jump_dest) rd1
  have hfit : heap.toNat + 192 < UInt256.size := by
    have h := (allocate192_fits hguard).2
    change heap.toNat + 192 < 2^256
    omega
  have hoff (n : Nat) (hn : n ≤ 192) : (heap + UInt256.ofNat n).toNat = heap.toNat + n := by
    rw [uadd_toNat, ulit_toNat' n (by change n < 2^256; omega)]
    exact Nat.mod_eq_of_lt (by omega)
  have hm : Reasoning.Theory.writeWord
      (easBlocks.eas_block_14063_memory (immWords := wordsOf (immStore v)) (ee := ee) (mem := mem))
      64 (UInt256.ofNat (allocateNext heap.toNat 192)) =
      buildDomainMemory mem heap.toNat v._TYPE_HASH v._HASHED_NAME v._HASHED_VERSION ee.codeOwner := by
    simp only [easBlocks.eas_block_14063_memory, hfree, wordsOf_immStore__TYPE_HASH,
      wordsOf_immStore__HASHED_NAME, wordsOf_immStore__HASHED_VERSION, wordOfInt_ofNat_toNat,
      hoff 32 (by decide), hoff 64 (by decide), hoff 96 (by decide), hoff 128 (by decide), hoff 160 (by decide),
      buildDomainMemory, writeWordSequence, Reasoning.Theory.writeWord, Nat.add_assoc, Nat.reduceAdd]
  change RD fork _ _ _ _ ⟨14209⟩ (heap :: (heap + UInt256.ofNat 32) :: ret :: R)
    (Reasoning.Theory.writeWord _ 64 (UInt256.ofNat (allocateNext heap.toNat 192))) _ _ _ _ _ at rd2
  rw [hm] at rd2
  obtain ⟨aw3, k3, C3, rd3⟩ := easBlocks.eas_block_14209_packed (immWords := wordsOf (immStore v))
    (by omega) hvalid rd2
  refine ⟨aw3, k3, C3, ?_⟩
  simpa only [easBlocks.eas_block_14209_stack, buildDomainMemory_keccak mem heap _ _ _ _ hlo hfit] using rd3

theorem easBuildDomain_revert {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {heap : UInt256} {R : List UInt256} (v : EASImmutables)
    (hstack : R.length + 7 ≤ 1024)
    (hfree : memLoad (UInt256.ofNat 64) mem = heap)
    (hguard : ¬ (allocateNext heap.toNat 192 ≤ 2^64-1 ∧ heap.toNat ≤ allocateNext heap.toNat 192))
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨14063⟩ R mem aw rdata σ k C) :
    RDrev fork (deployedRuntime v) g s0 := by
  obtain ⟨aw1, k1, C1, rd1⟩ := easBlocks.eas_block_14063_packed (immWords := wordsOf (immStore v))
    (by omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
  simp only [easBlocks.eas_block_14063_stack, hfree] at rd1
  exact easAllocate_revert (heap := heap) (size := UInt256.ofNat 192)
    (R := UInt256.ofNat 14209 :: heap :: (heap + UInt256.ofNat 32) :: R) v (by simp only [List.length_cons]; omega) hguard rd1

end Benchmarks.EAS.EAS
