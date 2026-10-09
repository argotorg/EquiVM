import Benchmarks.Morpho.MorphoBlue.ConstructorMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

def constructorPreparedMem (owner : UInt256) (I : ExecutionEnv) : ByteArray :=
  writeWord (constructorDomainMem owner I) 64 (UInt256.ofNat 384)

theorem constructorPreparedMemory (owner : UInt256) (I : ExecutionEnv) :
    (constructorPreparedMem owner I).size = 384 ∧
    memLoad (UInt256.ofNat 256) (constructorPreparedMem owner I) = UInt256.ofNat 96 ∧
    keccakWord (UInt256.ofNat 288) (UInt256.ofNat 96) (constructorPreparedMem owner I) = morphoDomainSeparator I := by
  have hd := constructorDomainMemory owner I
  have hg : 64 - (constructorDomainMem owner I).size < USize.size := by
    rw [hd.1]; exact lt_usize _ (by decide)
  refine ⟨?_, ?_, ?_⟩
  · rw [constructorPreparedMem, writeWord_size _ _ _ hg, hd.1]; rfl
  · rw [constructorPreparedMem, memLoad_writeWord_disjoint _ _ _ _ hg
      (by rw [hd.1]; decide) (by right; decide)]
    exact hd.2.2.1
  · change UInt256.ofNat (fromByteArrayBigEndian (KEC ((writeWord _ 64 _).readWithPadding 288 96))) = _
    rw [writeWord_read_preserved_len_of_disjoint hg (by right; rw [hd.1]; decide) (by decide) (by decide)]
    exact hd.2.2.2

def constructorPatchMem (owner : UInt256) (I : ExecutionEnv) : ByteArray :=
  writeWord (constructorPreparedMem owner I) 128 (morphoDomainSeparator I)

theorem constructorPatchMemory (owner : UInt256) (I : ExecutionEnv) :
    (constructorPatchMem owner I).size = 384 ∧
    memLoad (UInt256.ofNat 128) (constructorPatchMem owner I) = morphoDomainSeparator I := by
  have hs := (constructorPreparedMemory owner I).1
  have hg : 128 - (constructorPreparedMem owner I).size < USize.size := by
    rw [hs]; exact lt_usize _ (by decide)
  exact ⟨by rw [constructorPatchMem, writeWord_size _ _ _ hg, hs]; rfl,
    memLoad_writeWord_self _ _ (UInt256.ofNat 128) hg⟩

-- LIBRARY CANDIDATE: two ordered word patches expose the untouched byte ranges.
theorem writeWord_twice (base : ByteArray) (p q : Nat) (x y : UInt256)
    (hpq : p + 32 ≤ q) (hq : q + 32 ≤ base.size) :
    writeWord (writeWord base p x) q y =
      base.extract 0 p ++ x.toByteArray ++ base.extract (p + 32) q ++ y.toByteArray ++
        base.extract (q + 32) base.size := by
  have hp : p ≤ base.size := by omega
  have hfirst : writeWord base p x = base.extract 0 p ++ x.toByteArray ++ base.extract (p + 32) base.size := by
    rw [Reasoning.Theory.writeWord, write32_eq _ _ _ (by rw [toByteArray_size]) hp, toByteArray_extract_all]
  let pref := base.extract 0 p ++ x.toByteArray
  have hs : pref.size = p + 32 := by simp only [pref, ByteArray.size_append, ByteArray.size_extract, toByteArray_size]; omega
  have ht : (base.extract (p + 32) base.size).size = base.size - (p + 32) := by
    rw [ByteArray.size_extract]; omega
  rw [hfirst]
  change writeWord (pref ++ base.extract (p + 32) base.size) q y = _
  rw [show q = pref.size + (q - (p + 32)) by omega,
    writeWord_append_right _ _ _ _ (by rw [ht]; omega)]
  rw [Reasoning.Theory.writeWord, write32_eq _ _ _ (by rw [toByteArray_size]) (by rw [ht]; omega),
    toByteArray_extract_all, ht, extract_extract_BA, extract_extract_BA]
  simp only [Nat.add_zero]
  rw [show p + 32 + (q - (p + 32)) = q by omega,
    show min q base.size = q by omega,
    show p + 32 + (q - (p + 32) + 32) = q + 32 by omega,
    show p + 32 + (base.size - (p + 32)) = base.size by omega, Nat.min_self]
  rw [show pref.size + (q - (p + 32)) = q by omega]
  simp only [pref, ByteArray.append_assoc]

def constructorRuntimeTemplate : ByteArray := morphoCreationBytecode.extract 432 16055

theorem constructorTemplatePatches (w : UInt256) :
    writeWord (writeWord constructorRuntimeTemplate 6282 w) 9401 w =
      immutableLayout.runtime morphoBytecode (fun _ => w) := by
  change writeWord (writeWord constructorRuntimeTemplate 6282 w) 9401 w =
    writeWord (writeWord morphoBytecode 6282 w) 9401 w
  rw [writeWord_twice _ _ _ _ _ (by decide) (by native_decide),
    writeWord_twice _ _ _ _ _ (by decide) (by native_decide)]
  have h0 : constructorRuntimeTemplate.extract 0 6282 = morphoBytecode.extract 0 6282 := by native_decide
  have h1 : constructorRuntimeTemplate.extract (6282 + 32) 9401 = morphoBytecode.extract (6282 + 32) 9401 := by native_decide
  have h2 : constructorRuntimeTemplate.extract (9401 + 32) constructorRuntimeTemplate.size =
      morphoBytecode.extract (9401 + 32) morphoBytecode.size := by native_decide
  rw [h0, h1, h2]

def constructorCopiedMem (mem tail : ByteArray) : ByteArray :=
  (morphoCreationBytecode ++ tail).write 432 mem 384 15623

theorem constructorCopiedMem_eq (mem tail : ByteArray) (hm : mem.size = 384) :
    constructorCopiedMem mem tail = mem ++ constructorRuntimeTemplate := by
  have hc : morphoCreationBytecode.size = 16055 := by native_decide
  rw [constructorCopiedMem, ← hm, write_at_end_eq_from _ _ _ _ (by decide)
    (by rw [ByteArray.size_append, hc]; omega), byteArray_extract_append_left _ _ _ _ (by rw [hc])]
  rfl

theorem constructorCopiedMem_load (mem tail : ByteArray) (hm : mem.size = 384) :
    memLoad (UInt256.ofNat 128) (constructorCopiedMem mem tail) = memLoad (UInt256.ofNat 128) mem := by
  have hc : morphoCreationBytecode.size = 16055 := by native_decide
  have hs := copyWindow_size (morphoCreationBytecode ++ tail) mem 432 384 15623 (by decide)
    (by rw [ByteArray.size_append, hc]; omega) (by rw [hm])
  have hr := copyWindow_read_preserved (morphoCreationBytecode ++ tail) mem 432 384 15623 128
    (by decide) (by rw [ByteArray.size_append, hc]; omega) (by rw [hm])
    (by rw [hm]; decide) (by left; decide)
  change memLoad (UInt256.ofNat 128) ((morphoCreationBytecode ++ tail).write 432 mem 384 15623) = _
  simp only [memLoad, show (UInt256.ofNat 128).toNat = 128 from rfl, hs, hm, hr]
  rfl

theorem constructorPatchedReturn (mem tail : ByteArray) (w : UInt256) (hm : mem.size = 384)
    (hw : memLoad (UInt256.ofNat 128) mem = w) :
    (writeWord (writeWord (constructorCopiedMem mem tail) 6666
      (memLoad (UInt256.ofNat 128) (constructorCopiedMem mem tail))) 9785
      (memLoad (UInt256.ofNat 128) (constructorCopiedMem mem tail))).readWithPadding 384 15623 =
      immutableLayout.runtime morphoBytecode (fun _ => w) := by
  rw [constructorCopiedMem_load mem tail hm, hw, constructorCopiedMem_eq mem tail hm]
  have ht : constructorRuntimeTemplate.size = 15623 := by native_decide
  have hs : (writeWord constructorRuntimeTemplate 6282 w).size = 15623 := by
    rw [writeWord_size _ _ _ (by rw [ht]; exact lt_usize _ (by decide)), ht]; rfl
  rw [show 6666 = mem.size + 6282 by omega, writeWord_append_right _ _ _ _ (by rw [ht]; decide)]
  rw [show 9785 = mem.size + 9401 by omega, writeWord_append_right _ _ _ _ (by rw [hs]; decide)]
  rw [constructorTemplatePatches]
  change (mem ++ immutableLayout.runtime morphoBytecode (fun _ => w)).readWithPadding 384 15623 = _
  have hs' : (immutableLayout.runtime morphoBytecode (fun _ => w)).size = 15623 :=
    (Layout.runtime_size_of_bounds (by native_decide)).trans (by native_decide)
  rw [readWithPadding_eq_extract' _ _ _ (by decide) (by decide) (by rw [ByteArray.size_append, hm, hs'])]
  exact extract_append_right' _ _ _ _ hm.symm (by rw [hm, hs'])

theorem constructorRuntimeFinal (a : AccountAddress) (I : ExecutionEnv) :
    immutableLayout.runtime morphoBytecode (fun _ => morphoDomainSeparator I) =
      immutableLayout.deployed morphoBytecode (morphoConstructorFinal a I).immutables := by
  apply Layout.runtime_congr
  intro site hsite
  have hkey : site.2.2 = "DOMAIN_SEPARATOR" := by
    simp only [immutableLayout, Immutables.immutableReferences, List.flatMap_cons, List.flatMap_nil,
      List.map_cons, List.map_nil, List.append_nil, List.mem_cons, List.not_mem_nil, or_false] at hsite
    rcases hsite with rfl | rfl <;> rfl
  rw [hkey, morphoConstructorFinal_word]

end Benchmarks.Morpho.MorphoBlue
