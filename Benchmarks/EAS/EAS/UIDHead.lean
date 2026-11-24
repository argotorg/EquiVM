import Benchmarks.EAS.EAS.UIDSites

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

theorem uidMask96 (w : UInt256) :
    UInt256.land (UInt256.ofNat 115792089237316195423570985008687907853269984665561335876943319670319585689600)
      (UInt256.shiftLeft w (UInt256.ofNat 96)) = UInt256.shiftLeft w (UInt256.ofNat 96) := shiftLeft_highMask w 96 (by decide)
theorem uidMask192 (w : UInt256) :
    UInt256.land (UInt256.ofNat 115792089237316195417293883273301227089434195242432897623355228563449095127040)
      (UInt256.shiftLeft w (UInt256.ofNat 192)) = UInt256.shiftLeft w (UInt256.ofNat 192) := shiftLeft_highMask w 192 (by decide)
theorem uidMask224 (w : UInt256) :
    UInt256.land (UInt256.ofNat 115792089210356248756420345214020892766250353992003419616917011526809519390720)
      (UInt256.shiftLeft w (UInt256.ofNat 224)) = UInt256.shiftLeft w (UInt256.ofNat 224) := shiftLeft_highMask w 224 (by decide)

theorem uidFirstMemory_block {mem : ByteArray} {src heap dataPtr : UInt256} {a : AttestationRecord}
    (hview : AttestationMemoryView mem src dataPtr a) (hh : heap.toNat ≤ 2^64-1)
    (hheap : memLoad (UInt256.ofNat 64) mem = heap) :
    easBlocks.eas_block_8110_memory (mem := mem) (x9 := src) = uidFirstMemory mem (heap.toNat+32) a := by
  obtain ⟨hs,hr,_⟩ := hview.uidFields
  have hd (n : Nat) (hn : n ≤ 64) : (heap+UInt256.ofNat n).toNat = heap.toNat+n :=
    uadd_word_ofNat_toNat heap n (by change heap.toNat+n < 2^256; omega)
  simp only [easBlocks.eas_block_8110_memory,uidMask96,hs,hr,hheap,← writeWord_as_write,
    hd 32 (by decide),hd 64 (by decide),uidFirstMemory,Nat.add_assoc,Nat.reduceAdd]

theorem uidSecondMemory_block {mem : ByteArray} {src heap dataPtr : UInt256} {a : AttestationRecord}
    (hview : AttestationMemoryView mem src dataPtr a) (hh : heap.toNat ≤ 2^64-1) :
    easBlocks.eas_block_8254_memory (mem := uidFirstMemory mem (heap.toNat+32) a)
      (x0 := heap) (x1 := UInt256.ofNat 84)
      (x2 := UInt256.shiftLeft (UInt256.ofNat a.attester.val) (UInt256.ofNat 96))
      (x3 := memLoad (src+UInt256.ofNat 64) mem) (x4 := memLoad (src+UInt256.ofNat 96) mem)
      (x5 := a.revocable.toUInt256) (x6 := a.refUID) (x8 := heap) = uidHeadMemory mem (heap.toNat+32) a := by
  obtain ⟨_,_,_,ht,he,_⟩ := hview.uidFields
  have hd (n : Nat) (hn : n ≤ 121) : (heap+UInt256.ofNat n).toNat = heap.toNat+n :=
    uadd_word_ofNat_toNat heap n (by change heap.toNat+n < 2^256; omega)
  simp only [easBlocks.eas_block_8254_memory,uidMask192,ht,he,← writeWord_as_write,
    hd 84 (by decide),hd 104 (by decide),hd 112 (by decide),hd 120 (by decide),hd 121 (by decide),
    uidHeadMemory,Nat.add_assoc,Nat.reduceAdd]

theorem easUIDFirst {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {src heap dataPtr bump : UInt256} {a : AttestationRecord} {R : List UInt256} (v : EASImmutables) (site : UIDSite)
    (hstack : R.length+24 ≤ 1024) (hview : AttestationMemoryView mem src dataPtr a)
    (hh : heap.toNat ≤ 2^64-1) (hheap : memLoad (UInt256.ofNat 64) mem = heap)
    (rd : RD fork (deployedRuntime v) ee g s0 (uidStartPC site) (bump::uidSaved site src R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 (uidHeadPC site)
      (uidHeadStack mem src heap dataPtr a (heap::(heap+UInt256.ofNat 32)::bump::uidSaved site src R))
      (uidFirstMemory mem (heap.toNat+32) a) aw' rdata σ k' C' := by
  obtain ⟨_,_,ha,_,_,hb,href⟩ := hview.uidFields
  have hp : memLoad (UInt256.ofNat 288+src) mem = dataPtr := by rw [u256_add_comm]; exact hview.pointer
  cases site with
  | single s1 s2 s3 s4 s5 s6 s7 s8 =>
    obtain ⟨aw',k',C',rd'⟩ := easBlocks.eas_block_8110_packed (immWords := wordsOf (immStore v)) (by omega) rd
    refine ⟨aw',k',C',?_⟩
    simpa only [easBlocks.eas_block_8110_stack,uidFirstMemory_block hview hh hheap,hheap,uidMask96,ha,hb,href,hp,
      uidHeadPC,uidHeadStack,uidSaved] using rd'
  | many s1 s2 s3 s4 s5 s6 =>
    obtain ⟨aw',k',C',rd'⟩ := easBlocks.eas_block_10326_packed (immWords := wordsOf (immStore v)) (by omega) rd
    have hm : easBlocks.eas_block_10326_memory (mem := mem) (x7 := src) = uidFirstMemory mem (heap.toNat+32) a :=
      uidFirstMemory_block hview hh hheap
    refine ⟨aw',k',C',?_⟩
    simpa only [easBlocks.eas_block_10326_stack,hm,hheap,uidMask96,ha,hb,href,hp,uidHeadPC,uidHeadStack,uidSaved] using rd'

theorem easUIDSecond {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {src heap dataPtr : UInt256} {a : AttestationRecord} {R : List UInt256} (v : EASImmutables) (site : UIDSite)
    (hstack : R.length+14 ≤ 1024) (hview : AttestationMemoryView mem src dataPtr a)
    (hh : heap.toNat ≤ 2^64-1) (hdisj : dataPtr.toNat+32 ≤ heap.toNat)
    (rd : RD fork (deployedRuntime v) ee g s0 (uidHeadPC site) (uidHeadStack mem src heap dataPtr a R)
      (uidFirstMemory mem (heap.toNat+32) a) aw rdata σ k C) :
    ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 (UInt256.ofNat 4400)
      ((dataPtr+UInt256.ofNat 32)::(heap+UInt256.ofNat 153)::UInt256.ofNat a.data.size::uidCopyReturnPC site::
        UInt256.ofNat a.data.size::heap::R)
      (uidHeadMemory mem (heap.toNat+32) a) aw' rdata σ k' C' := by
  have hp := uidHeadMemory_prefix mem (heap.toNat+32) heap.toNat a (by omega)
  have hl : memLoad dataPtr (uidHeadMemory mem (heap.toNat+32) a) = UInt256.ofNat a.data.size :=
    (memLoad_of_prefix hp dataPtr hview.dataLow hdisj (by have hi := hview.dataCovered; omega)).trans hview.length
  let m2 := easBlocks.eas_block_8254_memory (mem := uidFirstMemory mem (heap.toNat+32) a)
    (x0 := heap) (x1 := UInt256.ofNat 84)
    (x2 := UInt256.shiftLeft (UInt256.ofNat a.attester.val) (UInt256.ofNat 96))
    (x3 := memLoad (src+UInt256.ofNat 64) mem) (x4 := memLoad (src+UInt256.ofNat 96) mem)
    (x5 := a.revocable.toUInt256) (x6 := a.refUID) (x8 := heap)
  have hm : m2 = uidHeadMemory mem (heap.toNat+32) a := uidSecondMemory_block hview hh
  cases site with
  | single s1 s2 s3 s4 s5 s6 s7 s8 =>
    obtain ⟨aw',k',C',rd'⟩ := easBlocks.eas_block_8254_packed (immWords := wordsOf (immStore v)) (by omega)
      (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
    refine ⟨aw',k',C',?_⟩
    change RD fork (deployedRuntime v) ee g s0 (UInt256.ofNat 4400)
      ((UInt256.ofNat 32+dataPtr)::(heap+UInt256.ofNat 153)::memLoad dataPtr m2::
        UInt256.ofNat 8374::memLoad dataPtr m2::heap::R) m2 aw' rdata σ k' C' at rd'
    simpa only [hm,u256_add_comm (UInt256.ofNat 32) dataPtr,hl,uidCopyReturnPC] using rd'
  | many s1 s2 s3 s4 s5 s6 =>
    obtain ⟨aw',k',C',rd'⟩ := easBlocks.eas_block_10470_packed (immWords := wordsOf (immStore v)) (by omega)
      (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
    refine ⟨aw',k',C',?_⟩
    change RD fork (deployedRuntime v) ee g s0 (UInt256.ofNat 4400)
      ((UInt256.ofNat 32+dataPtr)::(heap+UInt256.ofNat 153)::memLoad dataPtr m2::
        UInt256.ofNat 10590::memLoad dataPtr m2::heap::R) m2 aw' rdata σ k' C' at rd'
    simpa only [hm,u256_add_comm (UInt256.ofNat 32) dataPtr,hl,uidCopyReturnPC] using rd'

end Benchmarks.EAS.EAS
