import Benchmarks.Morpho.MorphoBlue.MarketParamsMemory
import Benchmarks.Morpho.MorphoBlue.MarketStateCommon
import Benchmarks.Morpho.MorphoBlue.RuntimeBlocks_033

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

theorem morphoMarketParamsCopyMemory (p : MarketParamsWords) (src dest : UInt256)
    (mem : ByteArray) (hc : p.Canonical) (hr : p.InMemory src mem)
    (hsfit : src.toNat + 160 < UInt256.size)
    (hdfit : dest.toNat + 160 < UInt256.size)
    (hsize : src.toNat + 160 ≤ mem.size) (hsep : src.toNat + 160 ≤ dest.toNat)
    (hgap : dest.toNat + 160 - mem.size < USize.size) :
    morphoBlocks.morpho_block_12367_memory (mem := mem) (x0 := dest) (x1 := src) =
      marketParamsMem p dest mem := by
  have hd (n : Nat) (hn : n ≤ 160) : (dest + UInt256.ofNat n).toNat = dest.toNat + n :=
    uadd_word_ofNat_toNat dest n (by omega)
  let m1 := writeWord mem dest.toNat p.loanToken
  let m2 := writeWord m1 (dest + UInt256.ofNat 32).toNat p.collateralToken
  let m3 := writeWord m2 (dest + UInt256.ofNat 64).toNat p.oracle
  let m4 := writeWord m3 (dest + UInt256.ofNat 96).toNat p.irm
  have hs1 : m1.size = max mem.size (dest.toNat + 32) :=
    writeWord_size _ _ _ (by omega)
  have hs2 : m2.size = max m1.size ((dest + UInt256.ofNat 32).toNat + 32) :=
    writeWord_size _ _ _ (by rw [hs1, hd 32 (by omega)]; omega)
  have hs3 : m3.size = max m2.size ((dest + UInt256.ofNat 64).toNat + 32) :=
    writeWord_size _ _ _ (by rw [hs2, hs1, hd 32 (by omega), hd 64 (by omega)]; omega)
  have hs4 : m4.size = max m3.size ((dest + UInt256.ofNat 96).toNat + 32) :=
    writeWord_size _ _ _ (by
      rw [hs3, hs2, hs1, hd 32 (by omega), hd 64 (by omega), hd 96 (by omega)]
      omega)
  have hd32 := hd 32 (by omega)
  have hd64 := hd 64 (by omega)
  have hd96 := hd 96 (by omega)
  have hr1 : p.InMemory src m1 := hr.writeWord _ _ hsfit hsize (by omega) (Or.inl hsep)
  have hr2 : p.InMemory src m2 :=
    hr1.writeWord _ _ hsfit (by omega) (by omega) (Or.inl (by omega))
  have hr3 : p.InMemory src m3 :=
    hr2.writeWord _ _ hsfit (by omega) (by omega) (Or.inl (by omega))
  have hr4 : p.InMemory src m4 :=
    hr3.writeWord _ _ hsfit (by omega) (by omega) (Or.inl (by omega))
  have h0 := hr ⟨0, by decide⟩
  have h1 := hr1 ⟨1, by decide⟩
  have h2 := hr2 ⟨2, by decide⟩
  have h3 := hr3 ⟨3, by decide⟩
  have h4 := hr4 ⟨4, by decide⟩
  simp only [MarketParamsWords.word, Nat.reduceMul,
    show UInt256.ofNat 0 = (⟨0⟩ : UInt256) from rfl, u256_add_zero] at h0 h1 h2 h3 h4
  dsimp only [m4, m3, m2, m1, Reasoning.Theory.writeWord] at h1 h2 h3 h4
  unfold morphoBlocks.morpho_block_12367_memory
  simp only [show UInt256.ofNat 1461501637330902918203684832716283019655932542975 =
    solcAddrMask from rfl]
  rw [h0, solcAddrMask_clean hc.1]
  rw [h1, solcAddrMask_clean hc.2.1]
  rw [h2, solcAddrMask_clean hc.2.2.1]
  rw [h3, solcAddrMask_clean hc.2.2.2, h4]
  rfl

theorem morphoBorrowRateArguments {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {σ : AccountMap} {k C : Nat} {src dest ret id : UInt256} {R : List UInt256}
    (p : MarketParamsWords) (hc : p.Canonical) (hr : p.InMemory src mem)
    (hsfit : src.toNat + 160 < UInt256.size)
    (hdfit : dest.toNat + 352 < UInt256.size)
    (hsize : src.toNat + 160 ≤ mem.size) (hsep : src.toNat + 160 ≤ dest.toNat)
    (hgap : dest.toNat + 160 - mem.size < USize.size)
    (hstack : R.length + 14 ≤ 1024)
    (hvalid : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 12367)
      (dest :: src :: solcMappingSlot ⟨3⟩ id :: ret :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 ret ((dest + UInt256.ofNat 352) :: R)
      (writeCascade mem (returnWordWrites dest.toNat (p.toList ++ marketStateWords σ ee id)))
      aw' rdata σ k' C' := by
  obtain ⟨aw1, k1, C1, rd1⟩ := morphoBlocks.morpho_block_12367_packed
    (immWords := wordsOf (immStore v)) hstack
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h
  rw [morphoMarketParamsCopyMemory p src dest mem hc hr hsfit (by omega) hsize hsep hgap] at rd1
  obtain ⟨aw2, k2, C2, rd2⟩ := morphoBlocks.morpho_block_12457_packed
    (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega) hvalid rd1
  have hadd (n : Nat) (hn : n ≤ 352) : (dest + UInt256.ofNat n).toNat = dest.toNat + n :=
    uadd_word_ofNat_toNat dest n (by omega)
  have hm : morphoBlocks.morpho_block_12457_memory (ee := ee)
      (mem := marketParamsMem p dest mem) (σ := σ) (x0 := solcMappingSlot ⟨3⟩ id)
      (x1 := UInt256.ofNat 320) (x2 := dest) =
      writeCascade mem (returnWordWrites dest.toNat (p.toList ++ marketStateWords σ ee id)) := by
    simp only [morphoBlocks.morpho_block_12457_memory, marketParamsMem,
      MarketParamsWords.toList, marketStateWords, marketReturnEntries, marketFieldWord,
      marketFieldSlot, halfWord, uint128Mask, solcSlotWordAt, solcSlotWord,
      List.map_cons, List.map_nil, List.cons_append, List.nil_append,
      returnWordWrites, writeCascade, Reasoning.Theory.writeWord,
      Nat.reduceDiv, Nat.reduceMod, Nat.reduceBEq, decide_true, decide_false, ↓reduceIte,
      show UInt256.ofNat 0 = (⟨0⟩ : UInt256) from rfl, u256_add_zero, Nat.add_assoc]
    simp (disch := omega) only [hadd]
    rfl
  rw [hm] at rd2
  exact ⟨aw2, k2, C2, rd2⟩

end Benchmarks.Morpho.MorphoBlue
