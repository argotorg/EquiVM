import Benchmarks.Morpho.MorphoBlue.Routines
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

-- The compiler's shared 64-byte memory allocation routine.
theorem morphoAlloc64 {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {σ : AccountMap} {k C : Nat} {ptr ret : UInt256} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hvalid : (D_J (deployedRuntime v) 0).contains ret = true)
    (hfit : UInt256.lor (UInt256.gt (ptr + UInt256.ofNat 64)
      (UInt256.ofNat 18446744073709551615))
      (UInt256.lt (ptr + UInt256.ofNat 64) ptr) = UInt256.ofNat 0)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 11507)
      (ptr :: ret :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 ret R
      ((ptr + UInt256.ofNat 64).toByteArray.write 0 mem 64 32) aw' rdata σ k' C' := by
  have rd := morphoBlocks.morpho_block_11507_fallthrough
    (immWords := wordsOf (immStore v)) (by simpa using hstack) hfit h
  have rdRet := morphoBlocks.morpho_block_11531
    (immWords := wordsOf (immStore v)) (by omega) hvalid rd
  exact ⟨_, _, _, rdRet⟩

def morphoErrorMem (length payload : UInt256) (mem : ByteArray) : ByteArray :=
  let ptr := memLoad (UInt256.ofNat 64) mem
  payload.toByteArray.write 0 (length.toByteArray.write 0
    ((ptr + UInt256.ofNat 64).toByteArray.write 0 mem 64 32) ptr.toNat 32)
    (ptr + UInt256.ofNat 32).toNat 32

def morphoNotOwnerMem (mem : ByteArray) : ByteArray :=
  morphoErrorMem (UInt256.ofNat 9)
    (UInt256.ofNat 49951334845383019971626788737275015727498476547903358252245993671974541328384) mem

def morphoAlreadySetMem (mem : ByteArray) : ByteArray :=
  morphoErrorMem (UInt256.ofNat 11)
    (UInt256.ofNat 44065955327867677235277023697061832690950930944920221635870317986597549637632) mem

theorem morphoNotOwnerMessage {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {σ : AccountMap} {k C : Nat} {ret : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hvalid : (D_J (deployedRuntime v) 0).contains ret = true)
    (hfit : UInt256.lor (UInt256.gt (memLoad (UInt256.ofNat 64) mem + UInt256.ofNat 64)
      (UInt256.ofNat 18446744073709551615))
      (UInt256.lt (memLoad (UInt256.ofNat 64) mem + UInt256.ofNat 64)
        (memLoad (UInt256.ofNat 64) mem)) = UInt256.ofNat 0)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 12040)
      (ret :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 ret
      (memLoad (UInt256.ofNat 64) mem :: R) (morphoNotOwnerMem mem) aw' rdata σ k' C' := by
  have rd := morphoBlocks.morpho_block_12040
    (immWords := wordsOf (immStore v)) (by omega)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h
  obtain ⟨aw', k', C', rdAlloc⟩ := morphoAlloc64 (v := v) (by simp only [List.length_cons]; omega)
    (by rw [morphoPatchedValidJumps v]; jump_dest) hfit rd
  have rdRet := morphoBlocks.morpho_block_12053
    (immWords := wordsOf (immStore v)) (by omega) hvalid rdAlloc
  exact ⟨_, _, _, rdRet⟩

theorem morphoAlreadySetMessage {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {σ : AccountMap} {k C : Nat} {ret : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hvalid : (D_J (deployedRuntime v) 0).contains ret = true)
    (hfit : UInt256.lor (UInt256.gt (memLoad (UInt256.ofNat 64) mem + UInt256.ofNat 64)
      (UInt256.ofNat 18446744073709551615))
      (UInt256.lt (memLoad (UInt256.ofNat 64) mem + UInt256.ofNat 64)
        (memLoad (UInt256.ofNat 64) mem)) = UInt256.ofNat 0)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 12253)
      (ret :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 ret
      (memLoad (UInt256.ofNat 64) mem :: R) (morphoAlreadySetMem mem) aw' rdata σ k' C' := by
  have rd := morphoBlocks.morpho_block_12253
    (immWords := wordsOf (immStore v)) (by omega)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h
  obtain ⟨aw', k', C', rdAlloc⟩ := morphoAlloc64 (v := v) (by simp only [List.length_cons]; omega)
    (by rw [morphoPatchedValidJumps v]; jump_dest) hfit rd
  have rdRet := morphoBlocks.morpho_block_12266
    (immWords := wordsOf (immStore v)) (by omega) hvalid rdAlloc
  exact ⟨_, _, _, rdRet⟩

theorem morphoRequireTrue {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {σ : AccountMap} {k C : Nat} {cond msg ret : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J (deployedRuntime v) 0).contains ret = true)
    (hcond : UInt256.isZero cond = UInt256.ofNat 0)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 12097)
      (cond :: msg :: ret :: R) mem aw rdata σ k C) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 ret R mem aw rdata σ k' C' := by
  have rd := morphoBlocks.morpho_block_12097_fallthrough
    (immWords := wordsOf (immStore v)) (by simpa using hstack) hcond h
  exact ⟨_, _, morphoBlocks.morpho_block_12103
    (immWords := wordsOf (immStore v)) (by omega) hvalid rd⟩

def morphoErrorLength (mem : ByteArray) (msg : UInt256) : UInt256 :=
  memLoad msg ((UInt256.ofNat 32).toByteArray.write 0
    ((UInt256.ofNat 3963877391197344453575983046348115674221700746820753546331534351508065746944).toByteArray.write
      0 mem (memLoad (UInt256.ofNat 64) mem).toNat 32)
    (memLoad (UInt256.ofNat 64) mem + UInt256.ofNat 4).toNat 32)

theorem morphoRequireFalseShort {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {σ : AccountMap} {k C : Nat} {cond msg ret : UInt256} {R : List UInt256}
    (hstack : R.length + 11 ≤ 1024)
    (hcond : cond = UInt256.ofNat 0)
    (hlenPos : UInt256.lt (UInt256.ofNat 0) (morphoErrorLength mem msg) ≠ UInt256.ofNat 0)
    (hlenMax : UInt256.lt (UInt256.ofNat 32) (morphoErrorLength mem msg) = UInt256.ofNat 0)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 12097)
      (cond :: msg :: ret :: R) mem aw rdata σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  have rdBad := morphoBlocks.morpho_block_12097_taken
    (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega)
    (by rw [hcond]; decide) (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h
  have rdLoop := morphoBlocks.morpho_block_12105
    (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega) rdBad
  have rdCopy := morphoBlocks.morpho_block_12165_taken
    (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega)
    hlenPos (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rdLoop
  have rdLoopEnd := morphoBlocks.morpho_block_12230
    (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rdCopy
  have rdRevert := morphoBlocks.morpho_block_12165_fallthrough
    (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega)
    hlenMax rdLoopEnd
  exact morphoBlocks.morpho_block_12173
    (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega) rdRevert

-- GENERALIZES Reasoning.Theory.twoWordHashMem_read_above64 to word loads.
theorem twoWordHashMem_memLoad_above64 (key slot a : UInt256) {mem : ByteArray}
    (hlo : 64 ≤ a.toNat) (hin : a.toNat + 32 ≤ mem.size) :
    memLoad a (twoWordHashMem key slot mem) = memLoad a mem := by
  unfold memLoad
  rw [twoWordHashMem_size_of_ge_64' key slot (by omega),
    twoWordHashMem_read_above64 key slot a.toNat hlo hin]

theorem morphoErrorMem_asCascade (length payload ptr : UInt256) (mem : ByteArray)
    (hptr : memLoad (UInt256.ofNat 64) mem = ptr) :
    morphoErrorMem length payload mem = writeCascade mem
      [(64, ptr + UInt256.ofNat 64), (ptr.toNat, length),
       ((ptr + UInt256.ofNat 32).toNat, payload)] := by
  unfold morphoErrorMem
  rw [hptr]
  rfl

-- LIBRARY CANDIDATE: a two-word error string allocated at the end of memory.
theorem morphoErrorMem_properties_of_gap (length payload ptr : UInt256) (mem : ByteArray)
    (hsize : mem.size ≤ ptr.toNat) (hptr : memLoad (UInt256.ofNat 64) mem = ptr)
    (hlo : 96 ≤ mem.size) (hgap : ptr.toNat - mem.size < USize.size)
    (hhi : ptr.toNat + 100 < UInt256.size) :
    (morphoErrorMem length payload mem).size = ptr.toNat + 64 ∧
    memLoad (UInt256.ofNat 64) (morphoErrorMem length payload mem) = ptr + UInt256.ofNat 64 ∧
    morphoErrorLength (morphoErrorMem length payload mem) ptr = length := by
  have h32 := uadd_word_ofNat_toNat ptr 32 (by omega)
  have h64 := uadd_word_ofNat_toNat ptr 64 (by omega)
  have h68 : (ptr + UInt256.ofNat 64 + UInt256.ofNat 4).toNat = ptr.toNat + 68 := by
    rw [uadd_word_ofNat_toNat _ 4 (by omega), h64]
  have huz : 0 < USize.size := lt_usize _ (by decide)
  have hmem : morphoErrorMem length payload mem = writeCascade mem
      [(64, ptr + UInt256.ofNat 64), (ptr.toNat, length), (ptr.toNat + 32, payload)] := by
    rw [morphoErrorMem_asCascade _ _ _ _ hptr, h32]
  have hs : (morphoErrorMem length payload mem).size = ptr.toNat + 64 := by
    rw [hmem, writeCascade_size]
    · simp only [writeCascadeSize]
      omega
    · simp only [WriteGapsOk, and_true]
      omega
  have hp : memLoad (UInt256.ofNat 64) (morphoErrorMem length payload mem) = ptr + UInt256.ofNat 64 := by
    apply mloadWordValue_of_readWithPadding
    · change 64 < _
      rw [hs]
      omega
    · rw [hmem]
      apply writeCascade_read_word_of_head
      · omega
      · simp only [WindowDisjointFromWrites, and_true]
        omega
  refine ⟨hs, hp, ?_⟩
  unfold morphoErrorLength
  rw [hp, hmem, h64, h68]
  let mem0 := Reasoning.Theory.writeWord mem 64 (ptr + UInt256.ofNat 64)
  have hm0 : mem0.size = mem.size := by
    rw [Reasoning.Theory.writeWord_size mem 64 _ (by omega)]
    omega
  let rest := [(ptr.toNat + 32, payload),
    (ptr.toNat + 64, UInt256.ofNat 3963877391197344453575983046348115674221700746820753546331534351508065746944),
    (ptr.toNat + 68, UInt256.ofNat 32)]
  change memLoad ptr (writeCascade mem0 ((ptr.toNat, length) :: rest)) = length
  have hs' : (writeCascade mem0 ((ptr.toNat, length) :: rest)).size = ptr.toNat + 100 := by
    rw [writeCascade_size]
    · simp only [rest, writeCascadeSize, hm0]
      omega
    · simp only [rest, WriteGapsOk, hm0, and_true]
      omega
  apply mloadWordValue_of_readWithPadding
  · rw [hs']
    omega
  · apply writeCascade_read_word_of_head
    · rw [hm0]
      omega
    · simp only [rest, WindowDisjointFromWrites, hm0, and_true]
      omega

theorem morphoErrorMem_properties (length payload ptr : UInt256) (mem : ByteArray)
    (hsize : mem.size = ptr.toNat) (hptr : memLoad (UInt256.ofNat 64) mem = ptr)
    (hlo : 96 ≤ ptr.toNat) (hhi : ptr.toNat + 100 < UInt256.size) :
    (morphoErrorMem length payload mem).size = ptr.toNat + 64 ∧
    memLoad (UInt256.ofNat 64) (morphoErrorMem length payload mem) = ptr + UInt256.ofNat 64 ∧
    morphoErrorLength (morphoErrorMem length payload mem) ptr = length :=
  morphoErrorMem_properties_of_gap length payload ptr mem (by omega) hptr (by omega)
    (by rw [hsize, Nat.sub_self]; exact lt_usize _ (by decide)) hhi

-- Compatibility specializations for the second administrative guard.
theorem morphoErrorMem192_size (length payload : UInt256) (mem : ByteArray)
    (hsize : mem.size = 192) (hptr : memLoad (UInt256.ofNat 64) mem = UInt256.ofNat 192) :
    (morphoErrorMem length payload mem).size = 256 :=
  (morphoErrorMem_properties length payload (UInt256.ofNat 192) mem hsize hptr (by decide) (by decide)).1

theorem morphoErrorMem192_load64 (length payload : UInt256) (mem : ByteArray)
    (hsize : mem.size = 192) (hptr : memLoad (UInt256.ofNat 64) mem = UInt256.ofNat 192) :
    memLoad (UInt256.ofNat 64) (morphoErrorMem length payload mem) = UInt256.ofNat 256 :=
  (morphoErrorMem_properties length payload (UInt256.ofNat 192) mem hsize hptr (by decide) (by decide)).2.1

theorem morphoErrorMem192_length (length payload : UInt256) (mem : ByteArray)
    (hsize : mem.size = 192) (hptr : memLoad (UInt256.ofNat 64) mem = UInt256.ofNat 192) :
    morphoErrorLength (morphoErrorMem length payload mem) (UInt256.ofNat 192) = length :=
  (morphoErrorMem_properties length payload (UInt256.ofNat 192) mem hsize hptr (by decide) (by decide)).2.2

def booleanAdminCheckMem (slot key : UInt256) : ByteArray :=
  twoWordHashMem key slot (morphoNotOwnerMem solcFreePtrMem)

theorem booleanAdminCheckMem_size (slot key : UInt256) : (booleanAdminCheckMem slot key).size = 192 := by
  rw [booleanAdminCheckMem, twoWordHashMem_size_of_ge_64' _ _ (by native_decide)]
  native_decide

theorem booleanAdminCheckMem_load64 (slot key : UInt256) :
    memLoad (UInt256.ofNat 64) (booleanAdminCheckMem slot key) = UInt256.ofNat 192 := by
  rw [booleanAdminCheckMem, twoWordHashMem_memLoad_above64 _ _ _ (by decide) (by native_decide)]
  native_decide

-- LIBRARY CANDIDATE: the two consecutive hashes for a nested mapping access.
def nestedMappingMem (base key0 key1 : UInt256) (mem : ByteArray) : ByteArray :=
  let inner := twoWordHashMem key0 base mem
  twoWordHashMem key1 (keccakWord ⟨0⟩ (UInt256.ofNat 64) inner) inner

theorem nestedMappingMem_hash (base key0 key1 : UInt256) (mem : ByteArray) :
    keccakWord ⟨0⟩ (UInt256.ofNat 64) (nestedMappingMem base key0 key1 mem) =
      solcMappingSlot (solcMappingSlot base key0) key1 := by
  dsimp only [nestedMappingMem]
  rw [show keccakWord ⟨0⟩ (UInt256.ofNat 64) (twoWordHashMem key0 base mem) =
    solcMappingSlot base key0 from twoWordHashMem_solcMappingSlot_any _ _ _]
  exact twoWordHashMem_solcMappingSlot_any _ _ _

theorem nestedMappingMem_size (base key0 key1 : UInt256) (mem : ByteArray) (hmem : 64 ≤ mem.size) :
    (nestedMappingMem base key0 key1 mem).size = mem.size := by
  dsimp only [nestedMappingMem]
  rw [twoWordHashMem_size_of_ge_64' _ _ (by rw [twoWordHashMem_size_of_ge_64' _ _ hmem]; exact hmem),
    twoWordHashMem_size_of_ge_64' _ _ hmem]

theorem nestedMappingMem_load64 (base key0 key1 : UInt256) (mem : ByteArray) (hmem : 96 ≤ mem.size) :
    memLoad (UInt256.ofNat 64) (nestedMappingMem base key0 key1 mem) = memLoad (UInt256.ofNat 64) mem := by
  dsimp only [nestedMappingMem]
  rw [twoWordHashMem_memLoad_above64 _ _ _ (by decide)
    (by rw [twoWordHashMem_size_of_ge_64' _ _ (by omega)]; exact hmem),
    twoWordHashMem_memLoad_above64 key0 base (UInt256.ofNat 64) (by decide) hmem]

end Benchmarks.Morpho.MorphoBlue
