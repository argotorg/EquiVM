import Benchmarks.UniswapV3.Pool.TickOutsideWords
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_031
import Reasoning.HeapMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def snapshotMapMem (mem : ByteArray) (lower upper : Int) : ByteArray :=
  wordAt0Mem (EVM.wordOfInt upper) (twoWordHashMem (EVM.wordOfInt lower) ⟨5⟩ mem)

theorem snapshotMapMem_heap {mem : ByteArray} {aw : UInt256}
    (hm : HeapMemory mem aw ⟨128⟩) (hs : mem.size = 96) (lower upper : Int) :
    HeapMemory (snapshotMapMem mem lower upper) aw ⟨128⟩ := by
  have hs' := twoWordHashMem_size_96 (EVM.wordOfInt lower) ⟨5⟩ hs
  have hs'' := wordAt0Mem_size_96 (EVM.wordOfInt upper) hs'
  refine ⟨by rw [snapshotMapMem, hs''], ?_, hm.lower, ?_, hm.active⟩
  · exact wordAt0Mem_read64 _ hs' (twoWordHashMem_read64 _ _ hs hm.free)
  · change 128 ≤ (snapshotMapMem mem lower upper).size + 32
    rw [snapshotMapMem, hs'']

theorem snapshotMappingHashes (mem : ByteArray) (lower upper : Int) (hs : mem.size = 96) :
    keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
      (twoWordHashMem (EVM.wordOfInt lower) (UInt256.ofNat 5) mem) =
        solcMappingSlot ⟨5⟩ (EVM.wordOfInt lower) ∧
    keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) (snapshotMapMem mem lower upper) =
        solcMappingSlot ⟨5⟩ (EVM.wordOfInt upper) :=
  ⟨twoWordHashMem_solcMappingSlot_any _ _ mem,
    wordAt0Mem_twoWordHashMem_solcMappingSlot _ _ _ hs⟩

def snapshotLowerStack (lower upper : Int) (σ : AccountMap) (I : ExecutionEnv)
    (a b c lowerRaw upperRaw : UInt256) (R : List UInt256) : List UInt256 :=
  [UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 248), solcSlotWordAt (tickFieldSlot lower 3) σ I,
   solcMappingSlot ⟨5⟩ (EVM.wordOfInt upper), solcMappingSlot ⟨5⟩ (EVM.wordOfInt lower),
   ⟨0⟩, (tickOutside lower σ I).seconds, ⟨0⟩, (tickOutside lower σ I).secondsPerLiquidity,
   ⟨0⟩, EVM.wordOfInt (tickOutside lower σ I).cumulative, a, b, c, upperRaw, lowerRaw] ++ R

def snapshotRawLowerStack (σ : AccountMap) (I : ExecutionEnv)
    (a b c lowerRaw upperRaw : UInt256) (R : List UInt256) (lowerSlot upperSlot : UInt256) : List UInt256 :=
  let last := solcSlotWordAt (lowerSlot + UInt256.ofNat 3) σ I
  [UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 248), last, upperSlot, lowerSlot,
   UInt256.ofNat 0, UInt256.land (UInt256.ofNat 4294967295)
     (UInt256.div last (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 216))),
   UInt256.ofNat 0, UInt256.land
     (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))
     (UInt256.div last (UInt256.ofNat 72057594037927936)),
   UInt256.ofNat 0, UInt256.signextend (UInt256.ofNat 6) last,
   a, b, c, upperRaw, lowerRaw] ++ R

theorem snapshotMapStack_eq (lower upper : Int) (σ : AccountMap) (ee : ExecutionEnv)
    (mem : ByteArray) (a b c lowerRaw upperRaw : UInt256) (R : List UInt256)
    (hs : mem.size = 96)
    (hl : UInt256.signextend (UInt256.ofNat 2) lowerRaw = EVM.wordOfInt lower)
    (hu : UInt256.signextend (UInt256.ofNat 2) upperRaw = EVM.wordOfInt upper) :
    uniswapV3Pool_block_9975_stack (ee := ee) (mem := mem) (σ := σ)
      (x0 := a) (x1 := b) (x2 := c) (x3 := upperRaw) (x4 := lowerRaw) (R := R) =
      snapshotLowerStack lower upper σ ee a b c lowerRaw upperRaw R := by
  obtain ⟨hlo, hup⟩ := snapshotMappingHashes mem lower upper hs
  have hh := congrArg₂ (snapshotRawLowerStack σ ee a b c lowerRaw upperRaw R) hlo hup
  calc
    _ = snapshotRawLowerStack σ ee a b c lowerRaw upperRaw R
        (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64)
          (twoWordHashMem (EVM.wordOfInt lower) (UInt256.ofNat 5) mem))
        (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) (snapshotMapMem mem lower upper)) := by
      simp only [uniswapV3Pool_block_9975_stack,
        signextend_idem ⟨24, by decide⟩ (UInt256.ofNat 2) _ (by decide) (by decide)]
      simp only [hl, hu]
      rfl
    _ = snapshotRawLowerStack σ ee a b c lowerRaw upperRaw R
        (solcMappingSlot ⟨5⟩ (EVM.wordOfInt lower)) (solcMappingSlot ⟨5⟩ (EVM.wordOfInt upper)) := hh
    _ = _ := by
      simp only [snapshotRawLowerStack, snapshotLowerStack, tickOutsideSecondsWord,
        tickOutsideLiquidityWord, tickOutsideTickWord, tickFieldSlot]
      rfl

theorem snapshotMapMemory_eq (mem : ByteArray) (lower upper : Int) (lowerRaw upperRaw : UInt256)
    (hl : UInt256.signextend (UInt256.ofNat 2) lowerRaw = EVM.wordOfInt lower)
    (hu : UInt256.signextend (UInt256.ofNat 2) upperRaw = EVM.wordOfInt upper) :
    uniswapV3Pool_block_9975_memory (mem := mem) (x3 := upperRaw) (x4 := lowerRaw) =
      snapshotMapMem mem lower upper := by
  simp only [uniswapV3Pool_block_9975_memory,
    signextend_idem ⟨24, by decide⟩ (UInt256.ofNat 2) _ (by decide) (by decide)]
  simp only [hl, hu]
  rfl

theorem snapshotMapLowerX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw a b c lowerRaw upperRaw : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (lower upper : Int)
    (rd : RD (deployedRuntime v) ee g s0 ⟨9975⟩
      (a :: b :: c :: upperRaw :: lowerRaw :: R) mem aw rdata σ k C)
    (hs : mem.size = 96) (ha : ActiveWords aw)
    (hl : UInt256.signextend (UInt256.ofNat 2) lowerRaw = EVM.wordOfInt lower)
    (hu : UInt256.signextend (UInt256.ofNat 2) upperRaw = EVM.wordOfInt upper)
    (hov : R.length + 16 ≤ 1024) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 ⟨10065⟩
      (snapshotLowerStack lower upper σ ee a b c lowerRaw upperRaw R)
      (snapshotMapMem mem lower upper) aw rdata σ k' C' := by
  have h0 : M aw (UInt256.ofNat 0) ⟨32⟩ = aw :=
    UInt256_M_same_of_cover_len aw ⟨0⟩ 32 (by have := ha.1; change 0 + 32 ≤ _; omega)
  have h32 : M aw (UInt256.ofNat 32) ⟨32⟩ = aw :=
    UInt256_M_same_of_cover_len aw ⟨32⟩ 32 (by have := ha.1; change 32 + 32 ≤ _; omega)
  have h64 : M aw (UInt256.ofNat 0) (UInt256.ofNat 64) = aw :=
    UInt256_M_same_of_cover_len aw ⟨0⟩ 64 (by have := ha.1; change 0 + 64 ≤ _; omega)
  obtain ⟨kr, Cr, rdMap⟩ := uniswapV3Pool_block_9975 (immWords := wordsOf (immStore v)) hov rd
  rw [snapshotMapStack_eq lower upper σ ee mem a b c lowerRaw upperRaw R hs hl hu,
    snapshotMapMemory_eq mem lower upper lowerRaw upperRaw hl hu] at rdMap
  simp only [h0, h32, h64] at rdMap
  exact ⟨kr, Cr, rdMap⟩

end Benchmarks.UniswapV3.Pool
