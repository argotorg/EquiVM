import Benchmarks.UniswapV3.Pool.PositionGetMemory
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_054

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

set_option maxHeartbeats 1000000 in
theorem positionGetBuildX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p lower upper : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (owner : AccountAddress)
    (rd : RD (deployedRuntime v) ee g s0 ⟨16867⟩
      (upper :: lower :: EVM.word owner.val :: R) mem aw rdata σ k C)
    (hm : HeapMemory mem aw p) (hb : p.toNat + 87 ≤ 2 ^ 200) (hov : R.length + 9 ≤ 1024) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 ⟨16952⟩
      (⟨26⟩ :: ⟨64⟩ :: ⟨32⟩ :: (⟨32⟩ + p) :: R)
      (positionBuildMem mem p owner lower upper) aw' rdata σ k' C' ∧
      HeapMemory (positionBuildMem mem p owner lower upper) aw' (p + ⟨58⟩) := by
  have hload : memLoad (UInt256.ofNat 64) mem = p := hm.load64
  have haddr : UInt256.land (UInt256.lnot (UInt256.ofNat 79228162514264337593543950335))
      (UInt256.shiftLeft (EVM.word owner.val) (UInt256.ofNat 96)) =
      UInt256.shiftLeft (EVM.word owner.val) ⟨96⟩ := by
    rw [u256_land_comm]
    exact ctorAddressHighShift owner
  have hoff (n : Nat) (hn : n ≤ 87) : (p + UInt256.ofNat n).toNat = p.toNat + n :=
    uadd_word_ofNat_toNat p n (by change _ < 2 ^ 256; omega)
  have hdataEq :
      (UInt256.shiftLeft (UInt256.signextend (UInt256.ofNat 2) upper) (UInt256.ofNat 232)).toByteArray.write 0
      ((UInt256.shiftLeft (UInt256.signextend (UInt256.ofNat 2) lower) (UInt256.ofNat 232)).toByteArray.write 0
      ((UInt256.shiftLeft (EVM.word owner.val) ⟨96⟩).toByteArray.write 0 mem (p.toNat + 32) 32)
      (p.toNat + 52) 32) (p.toNat + 55) 32 =
      positionDataMem mem p owner lower upper := rfl
  have hbuildEq : (p + UInt256.ofNat 58).toByteArray.write 0
      ((UInt256.ofNat 26).toByteArray.write 0 (positionDataMem mem p owner lower upper) p.toNat 32)
      (UInt256.ofNat 64).toNat 32 = positionBuildMem mem p owner lower upper := rfl
  have rdBuild := uniswapV3Pool_block_16867 (immWords := wordsOf (immStore v)) hov rd
  simp only [uniswapV3Pool_block_16867_stack, uniswapV3Pool_block_16867_memory,
    hload, haddr, hoff 32 (by decide), hoff 52 (by decide), hoff 55 (by decide), hdataEq,
    positionDataMem_load64 hm owner lower upper, u256_sub_self, u256_add_zero, hbuildEq,
    positionBuildMem_length _ _ _ _ _ hm.lower] at rdBuild
  refine ⟨_, _, _, rdBuild, ?_⟩
  refine ⟨?_, positionBuildMem_free _ _ _ _ _, ?_, ?_, ?_⟩
  · rw [positionBuildMem_size _ _ _ _ _ hm.lower]; have hp := hm.lower; omega
  · rw [show (p + (⟨58⟩ : UInt256)).toNat = p.toNat + 58 from hoff 58 (by decide)]
    have hp := hm.lower
    omega
  · rw [show (p + (⟨58⟩ : UInt256)).toNat = p.toNat + 58 from hoff 58 (by decide),
      positionBuildMem_size _ _ _ _ _ hm.lower]
    omega
  · repeat' apply activeWords_expand32
    all_goals first | exact hm.active | (change 64 + 32 ≤ _; omega) |
      (change (p + UInt256.ofNat _).toNat + 32 ≤ _; rw [hoff _ (by omega)]; omega) | omega

set_option maxHeartbeats 1000000 in
theorem positionGetX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p lower upper slot ret : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (owner : AccountAddress)
    (rd : RD (deployedRuntime v) ee g s0 ⟨16867⟩
      (upper :: lower :: EVM.word owner.val :: slot :: ret :: R) mem aw rdata σ k C)
    (hm : HeapMemory mem aw p) (hb : p.toNat + 87 ≤ 2 ^ 200)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hov : R.length + 11 ≤ 1024) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 ret
      (solcMappingSlot slot (positionKey owner lower upper) :: R)
      (positionGetMem mem p owner lower upper slot) aw' rdata σ k' C' ∧
      HeapMemory (positionGetMem mem p owner lower upper slot) aw' (p + ⟨58⟩) := by
  obtain ⟨awBuild, kBuild, CBuild, rdBuild, hmBuild⟩ := positionGetBuildX (v := v) owner rd hm hb (by evm_ov)
  have rdHash := uniswapV3Pool_block_16952 (immWords := wordsOf (immStore v)) (by evm_ov) hret rdBuild
  have hhash : keccakWord (⟨32⟩ + p) ⟨26⟩ (positionBuildMem mem p owner lower upper) =
      positionKey owner lower upper :=
    positionBuildMem_hash _ _ _ _ _ hm.lower (by change _ < 2 ^ 256; omega)
  have hmem : slot.toByteArray.write 0
      ((positionKey owner lower upper).toByteArray.write 0 (positionBuildMem mem p owner lower upper)
        (UInt256.ofNat 0).toNat 32) (⟨32⟩ : UInt256).toNat 32 =
      positionGetMem mem p owner lower upper slot := rfl
  have hkey : keccakWord (UInt256.ofNat 0) ⟨64⟩ (positionGetMem mem p owner lower upper slot) =
      solcMappingSlot slot (positionKey owner lower upper) := positionGetMem_hash _ _ _ _ _ _
  simp only [uniswapV3Pool_block_16952_stack, uniswapV3Pool_block_16952_memory, hhash, hmem,
    hkey] at rdHash
  refine ⟨_, _, _, rdHash, ?_⟩
  refine ⟨?_, positionGetMem_free _ _ _ _ _ _ hm.lower, hmBuild.lower, ?_, ?_⟩
  · rw [positionGetMem_size _ _ _ _ _ _ hm.lower]; have hp := hm.lower; omega
  · rw [positionGetMem_size _ _ _ _ _ _ hm.lower]
    have hn : (p + (⟨58⟩ : UInt256)).toNat = p.toNat + 58 :=
      uadd_word_ofNat_toNat p 58 (by change _ < 2 ^ 256; omega)
    rw [hn]
    omega
  · have ho : (⟨32⟩ + p : UInt256).toNat = p.toNat + 32 := by
      rw [u256_add_comm]
      exact uadd_word_ofNat_toNat p 32 (by change _ < 2 ^ 256; omega)
    repeat' apply activeWords_expand
    all_goals first | exact hmBuild.active |
      (change (⟨32⟩ + p : UInt256).toNat + 26 ≤ _; rw [ho]; omega) | (change 32 + 32 ≤ _; decide) |
      (change 0 + 32 ≤ _; decide)

end Benchmarks.UniswapV3.Pool
