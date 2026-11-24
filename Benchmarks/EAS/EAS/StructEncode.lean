import Benchmarks.EAS.EAS.CopyViews

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

theorem writeWord_as_write (mem : ByteArray) (off : Nat) (word : UInt256) :
    Reasoning.Theory.writeWord mem off word = word.toByteArray.write 0 mem off 32 := rfl

-- LIBRARY CANDIDATE: initialized loads below a word write are unchanged.
theorem memLoad_write_below (mem : ByteArray) (off : Nat) (ptr word : UInt256)
    (hbelow : ptr.toNat+32 ≤ off) (hin : ptr.toNat+32 ≤ mem.size) :
    memLoad ptr (Reasoning.Theory.writeWord mem off word) = memLoad ptr mem := by
  change (if ptr.toNat ≥ (Reasoning.Theory.writeWord mem off word).size then (⟨0⟩ : UInt256)
    else UInt256.ofNat (fromByteArrayBigEndian ((Reasoning.Theory.writeWord mem off word).readWithPadding ptr.toNat 32))) =
    (if ptr.toNat ≥ mem.size then (⟨0⟩ : UInt256)
    else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding ptr.toNat 32)))
  rw [if_neg (by rw [writeWord_sparse_size]; omega), if_neg (by omega),
    writeWord_sparse_read_preserved _ _ _ _ (Or.inl ⟨hbelow, hin⟩)]

def attestationEncodeFirstWords (mem : ByteArray) (src : UInt256) : List UInt256 := [
  memLoad src mem, memLoad (src + UInt256.ofNat 32) mem,
  UInt256.land (memLoad (src + UInt256.ofNat 64) mem) (UInt256.ofNat (2^64-1)),
  UInt256.land (memLoad (src + UInt256.ofNat 96) mem) (UInt256.ofNat (2^64-1)),
  UInt256.land (memLoad (src + UInt256.ofNat 128) mem) (UInt256.ofNat (2^64-1)),
  memLoad (src + UInt256.ofNat 160) mem]

theorem attestationEncodeFirstMemory (mem : ByteArray) (src dst : UInt256)
    (hdisj : src.toNat+320 ≤ dst.toNat) (hin : src.toNat+320 ≤ mem.size)
    (hbound : dst.toNat+320 < UInt256.size) :
    easBlocks.eas_block_4502_memory (mem := mem) (x0 := src) (x1 := dst) =
      writeWordSequence mem dst.toNat (attestationEncodeFirstWords mem src) := by
  have hs (n : Nat) (hn : n ≤ 320) : (src + UInt256.ofNat n).toNat = src.toNat+n :=
    uadd_word_ofNat_toNat src n (by omega)
  have hd (n : Nat) (hn : n ≤ 320) : (dst + UInt256.ofNat n).toNat = dst.toNat+n :=
    uadd_word_ofNat_toNat dst n (by omega)
  simp only [easBlocks.eas_block_4502_memory, ← writeWord_as_write,
    hd 32 (by decide), hd 64 (by decide), hd 96 (by decide), hd 128 (by decide), hd 160 (by decide)]
  simp (disch := (simp only [hs 32 (by decide), hs 64 (by decide), hs 96 (by decide), hs 128 (by decide), hs 160 (by decide), writeWord_sparse_size]; omega)) only [memLoad_write_below]
  rfl


def attestationEncodeLastWords (mem : ByteArray) (src recipient : UInt256) : List UInt256 := [
  recipient, UInt256.land (memLoad (src + UInt256.ofNat 224) mem) (UInt256.ofNat (2^160-1)),
  UInt256.isZero (UInt256.isZero (memLoad (src + UInt256.ofNat 256) mem)), UInt256.ofNat 320]

theorem attestationEncodeLastMemory (mem : ByteArray) (src dst recipient : UInt256)
    (hdisj : src.toNat+320 ≤ dst.toNat) (hin : src.toNat+320 ≤ mem.size)
    (hbound : dst.toNat+320 < UInt256.size) :
    easBlocks.eas_block_4628_memory (mem := mem) (x0 := dst) (x1 := UInt256.ofNat 192)
      (x2 := recipient) (x3 := src) (x5 := UInt256.ofNat 320) (x6 := dst) =
      writeWordSequence mem (dst.toNat+192) (attestationEncodeLastWords mem src recipient) := by
  have hs (n : Nat) (hn : n ≤ 320) : (src + UInt256.ofNat n).toNat = src.toNat+n :=
    uadd_word_ofNat_toNat src n (by omega)
  have hd (n : Nat) (hn : n ≤ 320) : (dst + UInt256.ofNat n).toNat = dst.toNat+n :=
    uadd_word_ofNat_toNat dst n (by omega)
  simp only [easBlocks.eas_block_4628_memory, ← writeWord_as_write,
    hd 192 (by decide), hd 224 (by decide), hd 256 (by decide), hd 288 (by decide)]
  simp (disch := (simp only [hs 224 (by decide), hs 256 (by decide), writeWord_sparse_size]; omega)) only [memLoad_write_below]
  rfl

theorem attestationEncodeLastStack (mem : ByteArray) (src dst recipient : UInt256) (R : List UInt256)
    (hdisj : src.toNat+320 ≤ dst.toNat) (hin : src.toNat+320 ≤ mem.size)
    (hbound : dst.toNat+320 < UInt256.size) :
    easBlocks.eas_block_4628_stack (mem := mem) (x0 := dst) (x1 := UInt256.ofNat 192)
      (x2 := recipient) (x3 := src) (x4 := UInt256.ofNat 288) (x5 := UInt256.ofNat 320) (x6 := dst) (R := R) =
      memLoad (src + UInt256.ofNat 288) mem :: (dst + UInt256.ofNat 320) :: R := by
  have hs (n : Nat) (hn : n ≤ 320) : (src + UInt256.ofNat n).toNat = src.toNat+n :=
    uadd_word_ofNat_toNat src n (by omega)
  have hd (n : Nat) (hn : n ≤ 320) : (dst + UInt256.ofNat n).toNat = dst.toNat+n :=
    uadd_word_ofNat_toNat dst n (by omega)
  simp only [easBlocks.eas_block_4628_stack, ← writeWord_as_write,
    hd 192 (by decide), hd 224 (by decide), hd 256 (by decide)]
  simp (disch := (simp only [hs 224 (by decide), hs 256 (by decide), hs 288 (by decide), writeWord_sparse_size]; omega)) only [memLoad_write_below]


theorem attestationEncodeFirstStack (mem : ByteArray) (src dst : UInt256) (R : List UInt256)
    (hlo : 96 ≤ src.toNat) (hdisj : src.toNat+320 ≤ dst.toNat) (hin : src.toNat+320 ≤ mem.size)
    (hbound : dst.toNat+320 < UInt256.size) :
    easBlocks.eas_block_4502_stack (mem := mem) (x0 := src) (x1 := dst) (R := R) =
      dst :: UInt256.ofNat 192 :: UInt256.land (memLoad (src+UInt256.ofNat 192) mem) (UInt256.ofNat (2^160-1)) ::
      src :: UInt256.ofNat 288 :: UInt256.ofNat 320 :: dst :: UInt256.ofNat 4692 :: R := by
  have hm := attestationEncodeFirstMemory mem src dst hdisj hin hbound
  dsimp only [easBlocks.eas_block_4502_memory] at hm
  have hs : (src + UInt256.ofNat 192).toNat = src.toNat+192 := uadd_word_ofNat_toNat src 192 (by omega)
  have hp := writeWordSequence_prefix mem dst.toNat dst.toNat (attestationEncodeFirstWords mem src) (le_refl _)
  simp only [easBlocks.eas_block_4502_stack, hm, memLoad_of_prefix hp (src+UInt256.ofNat 192)
    (by rw [hs]; omega) (by rw [hs]; omega) (by rw [hs]; omega)] <;> rfl

theorem writeWordSequence_append (mem : ByteArray) (off : Nat) (xs ys : List UInt256) :
    writeWordSequence mem off (xs++ys) =
      writeWordSequence (writeWordSequence mem off xs) (off+32*xs.length) ys := by
  induction xs generalizing mem off with
  | nil => simp only [List.nil_append, writeWordSequence, List.length_nil, Nat.mul_zero, Nat.add_zero]
  | cons x xs ih =>
    simp only [List.cons_append, writeWordSequence, List.length_cons, ih]
    congr 1
    omega

def attestationEncodeHeadWords (mem : ByteArray) (src : UInt256) : List UInt256 :=
  attestationEncodeFirstWords mem src ++
    attestationEncodeLastWords mem src (UInt256.land (memLoad (src+UInt256.ofNat 192) mem) (UInt256.ofNat (2^160-1)))

def attestationEncodeHeadMemory (mem : ByteArray) (src dst : UInt256) : ByteArray :=
  writeWordSequence mem dst.toNat (attestationEncodeHeadWords mem src)

theorem easEncodeAttestationHead {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {src dst : UInt256} {R : List UInt256} (v : EASImmutables)
    (hstack : R.length+8 ≤ 1024) (hlo : 96 ≤ src.toNat)
    (hdisj : src.toNat+320 ≤ dst.toNat) (hin : src.toNat+320 ≤ mem.size)
    (hbound : dst.toNat+320 < UInt256.size)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨4502⟩ (src::dst::R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 ⟨4435⟩
      (memLoad (src+UInt256.ofNat 288) mem :: (dst+UInt256.ofNat 320) :: UInt256.ofNat 4692 :: R)
      (attestationEncodeHeadMemory mem src dst) aw' rdata σ k' C' := by
  obtain ⟨aw1,k1,C1,rd1⟩ := easBlocks.eas_block_4502_packed (immWords := wordsOf (immStore v)) hstack rd
  simp only [attestationEncodeFirstMemory mem src dst hdisj hin hbound,
    attestationEncodeFirstStack mem src dst R hlo hdisj hin hbound] at rd1
  let m := writeWordSequence mem dst.toNat (attestationEncodeFirstWords mem src)
  have hg : mem.size ≤ m.size := writeWordSequence_grows _ _ _
  have hp : MemoryPrefix mem m dst.toNat := writeWordSequence_prefix _ _ _ _ (le_refl _)
  have hload (n : Nat) (hn : n+32 ≤ 320) : memLoad (src+UInt256.ofNat n) m = memLoad (src+UInt256.ofNat n) mem := by
    have hs : (src+UInt256.ofNat n).toNat = src.toNat+n := uadd_word_ofNat_toNat src n (by omega)
    exact memLoad_of_prefix hp _ (by rw [hs]; omega) (by rw [hs]; omega) (by rw [hs]; omega)
  obtain ⟨aw2,k2,C2,rd2⟩ := easBlocks.eas_block_4628_packed (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd1
  change RD fork (deployedRuntime v) ee g s0 (UInt256.ofNat 4435)
    (easBlocks.eas_block_4628_stack (mem := m) (x0 := dst) (x1 := UInt256.ofNat 192)
      (x2 := UInt256.land (memLoad (src+UInt256.ofNat 192) mem) (UInt256.ofNat (2^160-1)))
      (x3 := src) (x4 := UInt256.ofNat 288) (x5 := UInt256.ofNat 320) (x6 := dst) (R := UInt256.ofNat 4692 :: R))
    (easBlocks.eas_block_4628_memory (mem := m) (x0 := dst) (x1 := UInt256.ofNat 192)
      (x2 := UInt256.land (memLoad (src+UInt256.ofNat 192) mem) (UInt256.ofNat (2^160-1)))
      (x3 := src) (x5 := UInt256.ofNat 320) (x6 := dst)) aw2 rdata σ k2 C2 at rd2
  simp only [attestationEncodeLastMemory m src dst _ hdisj (by omega) hbound,
    attestationEncodeLastStack m src dst _ _ hdisj (by omega) hbound, hload 288 (by decide),
    attestationEncodeLastWords, hload 224 (by decide), hload 256 (by decide)] at rd2
  have hm : attestationEncodeHeadMemory mem src dst = writeWordSequence m (dst.toNat+192)
      (attestationEncodeLastWords mem src (UInt256.land (memLoad (src+UInt256.ofNat 192) mem) (UInt256.ofNat (2^160-1)))) := by
    rw [attestationEncodeHeadMemory, attestationEncodeHeadWords, writeWordSequence_append]
    rfl
  rw [hm]
  exact ⟨aw2,k2,C2,rd2⟩

end Benchmarks.EAS.EAS
