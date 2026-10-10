import Benchmarks.UniswapV3.Pool.PositionStruct
import Benchmarks.UniswapV3.Pool.WordArrayMemory
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_072

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 1000

def positionSnapshotWords (key : UInt256) (σ : AccountMap) (I : ExecutionEnv) : List UInt256 :=
  [positionFieldWord key 0 0 16 σ I, positionFieldWord key 1 0 32 σ I,
    positionFieldWord key 2 0 32 σ I, positionOwedWord key false σ I, positionOwedWord key true σ I]

theorem positionFullWord (key : UInt256) (slotDelta : Nat) (σ : AccountMap) (I : ExecutionEnv) :
    positionFieldWord key slotDelta 0 32 σ I =
      solcSlotWordAt (solcMappingSlot ⟨7⟩ key + UInt256.ofNat slotDelta) σ I := by
  simp only [positionFieldWord, Nat.pow_zero,
    show UInt256.ofNat 1 = (⟨1⟩ : UInt256) from rfl, word_div_one]
  exact u256LandMaskCleanOfToNat (bits := 256) _ _ (by decide) (UInt256.val _).isLt

theorem positionLowWord (key : UInt256) (slotDelta : Nat) (σ : AccountMap) (I : ExecutionEnv) :
    positionFieldWord key slotDelta 0 16 σ I =
      uint128Word (solcSlotWordAt (solcMappingSlot ⟨7⟩ key + UInt256.ofNat slotDelta) σ I) := by
  simp only [positionFieldWord, Nat.pow_zero,
    show UInt256.ofNat 1 = (⟨1⟩ : UInt256) from rfl, word_div_one]
  rw [show UInt256.ofNat (256 ^ 16 - 1) = UInt256.ofNat (2 ^ 128 - 1) from by decide,
    u256_land_comm]
  rfl

theorem positionSnapshotMemory_eq {mem : ByteArray} {aw p : UInt256} (key : UInt256)
    (σ : AccountMap) (I : ExecutionEnv) (hm : HeapMemory mem aw p)
    (hb : p.toNat + 160 ≤ 2 ^ 200) :
    uniswapV3Pool_block_21559_memory (ee := I) (σ := σ) (mem := mem)
      (x3 := solcMappingSlot ⟨7⟩ key) = wordArrayAllocMem mem p (positionSnapshotWords key σ I) := by
  have hload : memLoad (UInt256.ofNat 64) mem = p := hm.load64
  have h32 := uadd_word_ofNat_toNat p 32
    (show p.toNat + 32 < UInt256.size by change _ < 2 ^ 256; omega)
  have h64 := uadd_word_ofNat_toNat p 64
    (show p.toNat + 64 < UInt256.size by change _ < 2 ^ 256; omega)
  have h96 := uadd_word_ofNat_toNat p 96
    (show p.toNat + 96 < UInt256.size by change _ < 2 ^ 256; omega)
  have h128 := uadd_word_ofNat_toNat p 128
    (show p.toNat + 128 < UInt256.size by change _ < 2 ^ 256; omega)
  have hmask : UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128))
      (UInt256.ofNat 1) = UInt256.ofNat (2 ^ 128 - 1) := by native_decide
  have hshift : UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128) =
      UInt256.ofNat (256 ^ 16) := by native_decide
  simp only [uniswapV3Pool_block_21559_memory, hload, h32, h64, h96, h128]
  rw [hmask, hshift]
  simp only [wordArrayAllocMem, positionSnapshotWords, positionOwedWord,
    Bool.false_eq_true, if_false, if_true, positionFullWord, positionLowWord]
  simp only [List.length_cons, List.length_nil, writeWordArray, positionFieldWord,
    Nat.pow_zero, show UInt256.ofNat 1 = (⟨1⟩ : UInt256) from rfl,
    show UInt256.ofNat 0 = (⟨0⟩ : UInt256) from rfl, u256_add_zero, word_div_one,
    uint128Word, show UInt256.ofNat (256 ^ 16 - 1) = UInt256.ofNat (2 ^ 128 - 1) from by decide,
    u256_land_comm (UInt256.ofNat (2 ^ 128 - 1)), Nat.add_assoc, Nat.reduceAdd]
  rfl

theorem positionSnapshotX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p key growth1 growth0 delta ret : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨21559⟩
      (growth1 :: growth0 :: delta :: solcMappingSlot ⟨7⟩ key :: ret :: R) mem aw rdata σ k C)
    (hm : HeapMemory mem aw p) (hb : p.toNat + 160 ≤ 2 ^ 200) (hov : R.length + 11 ≤ 1024) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 ⟨21637⟩
      (⟨0⟩ :: p :: growth1 :: growth0 :: delta :: solcMappingSlot ⟨7⟩ key :: ret :: R)
      (wordArrayAllocMem mem p (positionSnapshotWords key σ ee)) aw' rdata σ k' C' ∧
      HeapMemory (wordArrayAllocMem mem p (positionSnapshotWords key σ ee)) aw' (p + ⟨160⟩) ∧
      WordArrayMemory (wordArrayAllocMem mem p (positionSnapshotWords key σ ee)) p
        (positionSnapshotWords key σ ee) := by
  have hload : memLoad (UInt256.ofNat 64) mem = p := hm.load64
  have h64 : M aw (UInt256.ofNat 64) ⟨32⟩ = aw := expandedWords64_eq hm.active
  obtain ⟨kr, Cr, rr⟩ := uniswapV3Pool_block_21559 (immWords := wordsOf (immStore v))
    (by simpa using hov) rd
  simp only [uniswapV3Pool_block_21559_stack, hload, h64,
    positionSnapshotMemory_eq key σ ee hm hb] at rr
  have hb32 (n : Nat) (hn : n ≤ 128) : (p + UInt256.ofNat n).toNat + 32 ≤ 2 ^ 200 := by
    rw [uadd_word_ofNat_toNat p n (by change _ < 2 ^ 256; omega)]
    omega
  have ha := activeWords_expand32
    (activeWords_expand32
      (activeWords_expand32
        (activeWords_expand32
          (activeWords_expand32 hm.active (show p.toNat + 32 ≤ 2 ^ 200 by omega))
          (hb32 32 (by decide))) (hb32 64 (by decide))) (hb32 96 (by decide)))
    (hb32 128 (by decide))
  exact ⟨_, kr, Cr, rr,
    wordArrayAllocMem_heap mem p _ (positionSnapshotWords key σ ee) hm.lower
      (by intro h; cases h) hb ha,
    wordArrayAllocMem_region mem p (positionSnapshotWords key σ ee) hm.lower (by simp [positionSnapshotWords])⟩

end Benchmarks.UniswapV3.Pool
