import Benchmarks.UniswapV3.Pool.Slot0Struct
import Benchmarks.UniswapV3.Pool.WordArrayMemory
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_032

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem slot0SqrtWord (σ : AccountMap) (I : ExecutionEnv) :
    slot0FieldWord 0 20 σ I = UInt256.land (solcSlotWordAt ⟨0⟩ σ I)
      (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) := by
  have hm : UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
      (UInt256.ofNat 1) = UInt256.ofNat (256 ^ 20 - 1) := by native_decide
  rw [hm]
  simp only [slot0FieldWord, Nat.pow_zero,
    show UInt256.ofNat 1 = (⟨1⟩ : UInt256) from rfl, word_div_one]

theorem slot0TickWord (σ : AccountMap) (I : ExecutionEnv) :
    EVM.wordOfInt (slot0TickValue σ I) = UInt256.signextend (UInt256.ofNat 2)
      (UInt256.div (solcSlotWordAt ⟨0⟩ σ I)
        (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))) := by
  have hs : UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160) =
      UInt256.ofNat (2 ^ 160) := by native_decide
  rw [hs, signextend_normalizeSint ⟨24, by decide⟩ _ _ (by decide) (by decide)]
  rfl

theorem slot0FieldShift (offset size : Nat) (shift mask : UInt256) (σ : AccountMap) (I : ExecutionEnv)
    (hs : shift = UInt256.ofNat (256 ^ offset))
    (hm : mask = UInt256.ofNat (256 ^ size - 1)) :
    slot0FieldWord offset size σ I = UInt256.land mask (UInt256.div (solcSlotWordAt ⟨0⟩ σ I) shift) := by
  rw [hs, hm, u256_land_comm]
  rfl

def slot0ReadHeadMem (mem : ByteArray) (p : UInt256) (σ : AccountMap) (I : ExecutionEnv) : ByteArray :=
  writeWordArray (writeWord mem 64 (p + ⟨224⟩)) p.toNat
    [slot0FieldWord 0 20 σ I, EVM.wordOfInt (slot0TickValue σ I), slot0FieldWord 23 2 σ I]

theorem slot0ReadHeadMem_eq {mem : ByteArray} {aw p : UInt256} (σ : AccountMap) (I : ExecutionEnv)
    (hm : HeapMemory mem aw p) (hb : p.toNat + 224 ≤ 2 ^ 200) :
    uniswapV3Pool_block_10148_memory (ee := I) (σ := σ) (mem := mem) =
      slot0ReadHeadMem mem p σ I := by
  have hload : memLoad (UInt256.ofNat 64) mem = p := hm.load64
  have hp32 : (p + UInt256.ofNat 32).toNat = p.toNat + 32 :=
    uadd_word_ofNat_toNat p 32 (by change _ < 2 ^ 256; omega)
  have hp64 : (p + UInt256.ofNat 64).toNat = p.toNat + 64 :=
    uadd_word_ofNat_toNat p 64 (by change _ < 2 ^ 256; omega)
  simp only [uniswapV3Pool_block_10148_memory, hload, hp32, hp64,
    signextend_idem ⟨24, by decide⟩ (UInt256.ofNat 2) _ (by decide) (by decide)]
  change writeWord (writeWord (writeWord (writeWord mem 64 (p + ⟨224⟩)) p.toNat
    (UInt256.land (solcSlotWordAt ⟨0⟩ σ I)
      (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))))
    (p.toNat + 32) (UInt256.signextend (UInt256.ofNat 2) (UInt256.div (solcSlotWordAt ⟨0⟩ σ I)
      (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)))))
    (p.toNat + 64) (UInt256.land (UInt256.ofNat 65535) (UInt256.div (solcSlotWordAt ⟨0⟩ σ I)
      (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 184)))) = _
  rw [← slot0SqrtWord, ← slot0TickWord,
    ← slot0FieldShift 23 2 _ _ σ I (by native_decide) (by native_decide)]
  rfl

theorem slot0ReadTailMem_eq (mem : ByteArray) (p : UInt256) (σ : AccountMap) (I : ExecutionEnv)
    (hb : p.toNat + 224 ≤ 2 ^ 200) :
    uniswapV3Pool_block_10229_taken_memory (mem := slot0ReadHeadMem mem p σ I)
      (x0 := UInt256.ofNat 96) (x1 := slot0FieldWord 25 2 σ I) (x4 := solcSlotWordAt ⟨0⟩ σ I)
      (x5 := p) (x6 := UInt256.ofNat 65535) =
      wordArrayAllocMem mem p (slot0StructWords σ I) := by
  have h96 := uadd_word_ofNat_toNat p 96 (show p.toNat + 96 < UInt256.size by change _ < 2 ^ 256; omega)
  have h128 := uadd_word_ofNat_toNat p 128 (show p.toNat + 128 < UInt256.size by change _ < 2 ^ 256; omega)
  have h160 := uadd_word_ofNat_toNat p 160 (show p.toNat + 160 < UInt256.size by change _ < 2 ^ 256; omega)
  have h192 := uadd_word_ofNat_toNat p 192 (show p.toNat + 192 < UInt256.size by change _ < 2 ^ 256; omega)
  simp only [uniswapV3Pool_block_10229_taken_memory, h96, h128, h160, h192]
  rw [← slot0FieldShift 27 2
      (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 216)) (UInt256.ofNat 65535)
      σ I (by native_decide) (by native_decide),
    ← slot0FieldShift 29 1
      (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 232)) (UInt256.ofNat 255)
      σ I (by native_decide) (by native_decide),
    ← slot0FieldShift 30 1
      (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 240)) (UInt256.ofNat 255)
      σ I (by native_decide) (by native_decide)]
  rfl

theorem slot0ReadX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p x0 x1 : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨10148⟩ (x0 :: x1 :: R) mem aw rdata σ k C)
    (hm : HeapMemory mem aw p) (hb : p.toNat + 224 ≤ 2 ^ 200) (hov : R.length + 8 ≤ 1024) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 ⟨10229⟩
      (UInt256.ofNat 96 :: slot0FieldWord 25 2 σ ee :: EVM.wordOfInt (slot0TickValue σ ee) ::
       UInt256.ofNat 2 :: solcSlotWordAt ⟨0⟩ σ ee :: p :: UInt256.ofNat 65535 :: R)
      (slot0ReadHeadMem mem p σ ee) aw' rdata σ k' C' ∧ ActiveWords aw' := by
  have hload : memLoad (UInt256.ofNat 64) mem = p := hm.load64
  have h64 : M aw (UInt256.ofNat 64) ⟨32⟩ = aw := expandedWords64_eq hm.active
  have hp32 := uadd_word_ofNat_toNat p 32 (show p.toNat + 32 < UInt256.size by change _ < 2 ^ 256; omega)
  have hp64 := uadd_word_ofNat_toNat p 64 (show p.toNat + 64 < UInt256.size by change _ < 2 ^ 256; omega)
  have ht := slot0TickWord σ ee
  have hc := slot0FieldShift 25 2 (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 200))
    (UInt256.ofNat 65535) σ ee (by native_decide) (by native_decide)
  obtain ⟨kr, Cr, rdRead⟩ := uniswapV3Pool_block_10148 (immWords := wordsOf (immStore v)) hov rd
  simp only [uniswapV3Pool_block_10148_stack, hload, h64,
    signextend_idem ⟨24, by decide⟩ (UInt256.ofNat 2) _ (by decide) (by decide),
    slot0ReadHeadMem_eq σ ee hm hb] at rdRead
  change RD (deployedRuntime v) ee g s0 ⟨10229⟩
    (UInt256.ofNat 96 :: UInt256.land (UInt256.ofNat 65535)
      (UInt256.div (solcSlotWordAt ⟨0⟩ σ ee)
        (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 200))) ::
      UInt256.signextend (UInt256.ofNat 2) (UInt256.div (solcSlotWordAt ⟨0⟩ σ ee)
        (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))) ::
      UInt256.ofNat 2 :: solcSlotWordAt ⟨0⟩ σ ee :: p :: UInt256.ofNat 65535 :: R)
    (slot0ReadHeadMem mem p σ ee) _ rdata σ _ _ at rdRead
  rw [← ht, ← hc] at rdRead
  have ha := activeWords_expand32
    (activeWords_expand32
      (activeWords_expand32 hm.active (show p.toNat + 32 ≤ 2 ^ 200 by omega))
      (show (p + UInt256.ofNat 32).toNat + 32 ≤ 2 ^ 200 by rw [hp32]; omega))
    (show (p + UInt256.ofNat 64).toNat + 32 ≤ 2 ^ 200 by rw [hp64]; omega)
  exact ⟨_, kr, Cr, rdRead, ha⟩

def Slot0Memory (mem : ByteArray) (p : UInt256) (σ : AccountMap) (I : ExecutionEnv) : Prop :=
  WordArrayMemory mem p (slot0StructWords σ I)

theorem slot0TickWord_idem (σ : AccountMap) (I : ExecutionEnv) :
    UInt256.signextend (UInt256.ofNat 2) (EVM.wordOfInt (slot0TickValue σ I)) =
      EVM.wordOfInt (slot0TickValue σ I) := by
  simp only [slot0TickWord,
    signextend_idem ⟨24, by decide⟩ (UInt256.ofNat 2) _ (by decide) (by decide)]

theorem Slot0Memory.load_tick {mem : ByteArray} {p : UInt256} {σ : AccountMap} {I : ExecutionEnv}
    (hm : Slot0Memory mem p σ I) (hb : p.toNat + 224 < UInt256.size) :
    memLoad (p + UInt256.ofNat 32) mem = EVM.wordOfInt (slot0TickValue σ I) :=
  by
    have h := WordArrayMemory.load hm 1 (by change 1 < 7; decide) hb
    simpa only [slot0StructWords, List.getElem_cons_succ, List.getElem_cons_zero, Nat.reduceMul] using h

theorem Slot0Memory.load_index {mem : ByteArray} {p : UInt256} {σ : AccountMap} {I : ExecutionEnv}
    (hm : Slot0Memory mem p σ I) (hb : p.toNat + 224 < UInt256.size) :
    memLoad (p + UInt256.ofNat 64) mem = slot0FieldWord 23 2 σ I :=
  by
    have h := WordArrayMemory.load hm 2 (by change 2 < 7; decide) hb
    simpa only [slot0StructWords, List.getElem_cons_succ, List.getElem_cons_zero, Nat.reduceMul] using h

theorem Slot0Memory.load_cardinality {mem : ByteArray} {p : UInt256} {σ : AccountMap} {I : ExecutionEnv}
    (hm : Slot0Memory mem p σ I) (hb : p.toNat + 224 < UInt256.size) :
    memLoad (p + UInt256.ofNat 96) mem = slot0FieldWord 25 2 σ I :=
  by
    have h := WordArrayMemory.load hm 3 (by change 3 < 7; decide) hb
    simpa only [slot0StructWords, List.getElem_cons_succ, List.getElem_cons_zero, Nat.reduceMul] using h

end Benchmarks.UniswapV3.Pool
