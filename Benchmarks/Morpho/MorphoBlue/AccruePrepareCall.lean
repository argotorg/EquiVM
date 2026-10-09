import Benchmarks.Morpho.MorphoBlue.BorrowRateEncode
import Benchmarks.Morpho.MorphoBlue.BorrowRateABI
import Benchmarks.Morpho.MorphoBlue.Dispatch

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

def accrueCallDataMem (p : MarketParamsWords) (σ : AccountMap) (I : ExecutionEnv)
    (mem : ByteArray) (fp : UInt256) : ByteArray :=
  staticWordCallMem borrowRateSelectorWord (p.toList ++ marketStateWords σ I p.id)
    (twoWordHashMem p.id (UInt256.ofNat 3) mem) fp.toNat

theorem morphoAccruePrepareCall {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {σ : AccountMap} {k C : Nat} {ptr fp elapsed ret : UInt256} {R : List UInt256}
    (p : MarketParamsWords) (hc : p.Canonical) (hr : p.InMemory ptr mem)
    (hstack : R.length + 32 ≤ 1024) (hfp : memLoad (UInt256.ofNat 64) mem = fp)
    (hplo : 96 ≤ ptr.toNat) (hpf : ptr.toNat + 160 < UInt256.size)
    (hin : ptr.toNat + 160 ≤ mem.size) (hsep : ptr.toNat + 160 ≤ fp.toNat)
    (hfit : fp.toNat + 356 < UInt256.size) (hgap : fp.toNat + 356 - mem.size < USize.size)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 13321)
      ([p.irm, elapsed, solcAddrMask, p.id, UInt256.ofNat 32, UInt256.ofNat 3,
        UInt256.ofNat 0, UInt256.ofNat 64, uint128Mask, ret, ptr] ++ R) mem aw rdata σ k C) :
    ∃ aw' gasArg k' C', RD (deployedRuntime v) ee g s0 (UInt256.ofNat 13393)
      ([gasArg, p.irm, UInt256.ofNat 0, fp, UInt256.ofNat 356, fp, UInt256.ofNat 32,
        elapsed, solcAddrMask, p.id, UInt256.ofNat 32, UInt256.ofNat 3, UInt256.ofNat 0,
        UInt256.ofNat 64, uint128Mask, ret, fp] ++ R)
      (accrueCallDataMem p σ ee mem fp) aw' rdata σ k' C' := by
  let hm := twoWordHashMem p.id (UInt256.ofNat 3) mem
  have hms : hm.size = mem.size := twoWordHashMem_size_of_ge_64' _ _ (by omega)
  have hmf : memLoad (UInt256.ofNat 64) hm = fp := by
    rw [twoWordHashMem_memLoad_above64 _ _ _ (by decide) (by change 64 + 32 ≤ mem.size; omega), hfp]
  have hmh : keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) hm = solcMappingSlot ⟨3⟩ p.id :=
    twoWordHashMem_solcMappingSlot_any _ _ _
  have hmr : p.InMemory ptr hm := hr.twoWordHashMem _ _ hpf hin (by omega)
  let cm := writeWord hm fp.toNat borrowRateSelectorWord
  have hcs : cm.size = max mem.size (fp.toNat + 32) := by
    rw [writeWord_size _ _ _ (by rw [hms]; omega), hms]
  have hcr : p.InMemory ptr cm := hmr.writeWord _ _ hpf (by rw [hms]; exact hin)
    (by rw [hms]; omega) (Or.inl hsep)
  obtain ⟨aw1, k1, C1, rd1⟩ := morphoBlocks.morpho_block_13321_packed
    (immWords := wordsOf (immStore v)) (by simp only [List.append]; omega)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h
  change RD _ _ _ _ _
    ([memLoad (UInt256.ofNat 64) hm + UInt256.ofNat 4, ptr,
      keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) hm, UInt256.ofNat 13389,
      memLoad (UInt256.ofNat 64) hm, UInt256.ofNat 0, memLoad (UInt256.ofNat 64) hm, p.irm,
      memLoad (UInt256.ofNat 64) hm, UInt256.ofNat 32, elapsed, solcAddrMask, p.id,
      UInt256.ofNat 32, UInt256.ofNat 3, UInt256.ofNat 0, UInt256.ofNat 64, uint128Mask,
      ret, memLoad (UInt256.ofNat 64) hm] ++ R)
    (borrowRateSelectorWord.toByteArray.write 0 hm (memLoad (UInt256.ofNat 64) hm).toNat 32)
    _ _ _ _ _ at rd1
  rw [hmf, hmh] at rd1
  have h4 : (fp + UInt256.ofNat 4).toNat = fp.toNat + 4 := uadd_word_ofNat_toNat fp 4 (by omega)
  obtain ⟨aw2, k2, C2, rd2⟩ := morphoBorrowRateArguments (v := v) p hc hcr hpf
    (by rw [h4]; omega) (by rw [hcs]; omega) (by rw [h4]; omega)
    (by rw [h4, hcs]; omega) (by simp only [List.append, List.length_cons]; omega)
    (by rw [morphoPatchedValidJumps v]; jump_dest) rd1
  obtain ⟨aw3, k3, C3, rd3⟩ := morphoBlocks.morpho_block_13389_packed
    (immWords := wordsOf (immStore v)) (by simp only [List.append, List.length_cons]; omega) rd2
  have hlen : UInt256.sub ((fp + UInt256.ofNat 4) + UInt256.ofNat 352) fp = UInt256.ofNat 356 := by
    rw [u256_add_assoc, word_add_sub_left]
    rfl
  simp only [morphoBlocks.morpho_block_13389_stack, hlen, h4] at rd3
  exact ⟨aw3, _, k3, C3, rd3⟩

-- LIBRARY CANDIDATE: size of a selector followed by at least one static argument word.
theorem staticWordCallMem_size (selector : UInt256) (ws : List UInt256) (mem : ByteArray) (off : Nat)
    (hne : ws ≠ []) (hgap : off - mem.size < USize.size) :
    (staticWordCallMem selector ws mem off).size = max mem.size (off + 4 + 32 * ws.length) := by
  have hs := writeWord_size mem off selector hgap
  have hw := List.length_pos_of_ne_nil hne
  unfold staticWordCallMem
  rw [writeReturnWords_size ws _ _ hne (by rw [hs]; have hp := USize.size_pos; omega), hs]
  omega

theorem accrueCallDataMem_size (p : MarketParamsWords) (σ : AccountMap) (I : ExecutionEnv)
    (mem : ByteArray) (fp : UInt256) (hs : 64 ≤ mem.size) (hg : fp.toNat - mem.size < USize.size) :
    (accrueCallDataMem p σ I mem fp).size = max mem.size (fp.toNat + 356) := by
  have hh := twoWordHashMem_size_of_ge_64' p.id (UInt256.ofNat 3) hs
  rw [accrueCallDataMem, staticWordCallMem_size _ _ _ _ (by simp [MarketParamsWords.toList])
    (by rw [hh]; exact hg), hh]
  simp only [List.length_append, MarketParamsWords.toList, marketStateWords,
    marketReturnEntries, List.length_map, List.length_cons, List.length_nil, Nat.add_assoc]

theorem accrueCallDataMem_read (p : MarketParamsWords) (σ : AccountMap) (I : ExecutionEnv)
    (mem : ByteArray) (fp : UInt256) (hs : 64 ≤ mem.size) (hg : fp.toNat - mem.size < USize.size) :
    (accrueCallDataMem p σ I mem fp).readWithPadding fp.toNat 356 = borrowRateCalldata p σ I p.id := by
  apply borrowRateCalldata_read
  rw [twoWordHashMem_size_of_ge_64' _ _ hs]
  exact hg

theorem accrueCallDataMem_freePtr (p : MarketParamsWords) (σ : AccountMap) (I : ExecutionEnv)
    (mem : ByteArray) (fp : UInt256) (hs : 96 ≤ mem.size) (hl : 96 ≤ fp.toNat)
    (hg : fp.toNat - mem.size < USize.size) :
    memLoad (UInt256.ofNat 64) (accrueCallDataMem p σ I mem fp) = memLoad (UInt256.ofNat 64) mem := by
  have hh := twoWordHashMem_size_of_ge_64' p.id (UInt256.ofNat 3) (by omega : 64 ≤ mem.size)
  have hw := writeWord_size (twoWordHashMem p.id (UInt256.ofNat 3) mem) fp.toNat borrowRateSelectorWord
    (by rw [hh]; exact hg)
  rw [accrueCallDataMem, staticWordCallMem,
    memLoad_writeReturnWords_below _ _ _ _ (by rw [hw]; have hu := USize.size_pos; omega)
      (by change 64 + 32 ≤ _; rw [hw, hh]; omega) (by change 64 + 32 ≤ _; omega),
    memLoad_writeWord_disjoint _ _ _ _ (by rw [hh]; exact hg)
      (by change 64 + 32 ≤ _; rw [hh]; omega) (Or.inl hl)]
  exact twoWordHashMem_memLoad_above64 _ _ _ (by decide) hs

end Benchmarks.Morpho.MorphoBlue
