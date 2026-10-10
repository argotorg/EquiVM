import Benchmarks.UniswapV3.Pool.ConstructorMemory
import Benchmarks.UniswapV3.Pool.TickSpacingTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open uniswapV3PoolCreationBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 1000

theorem constructorFieldsSummaryMem (original : AccountAddress) (out : ByteArray)
    (hlen : 160 ≤ out.size) :
    uniswapV3PoolCreation_block_130_memory (mem := constructorOutputMem original out)
      (x1 := ⟨352⟩) = constructorFieldsMem original out := by
  have h0 : memLoad ⟨352⟩ (constructorOutputMem original out) = calldataWord out 0 :=
    constructorOutputMem_loadParameter _ _ 0 hlen (by decide)
  have h32 : memLoad (⟨352⟩ + UInt256.ofNat 32) (constructorOutputMem original out) =
      calldataWord out 32 := constructorOutputMem_loadParameter _ _ 32 hlen (by decide)
  have h64 : memLoad (⟨352⟩ + UInt256.ofNat 64) (constructorOutputMem original out) =
      calldataWord out 64 := constructorOutputMem_loadParameter _ _ 64 hlen (by decide)
  have h96 : memLoad (⟨352⟩ + UInt256.ofNat 96) (constructorOutputMem original out) =
      calldataWord out 96 := constructorOutputMem_loadParameter _ _ 96 hlen (by decide)
  unfold uniswapV3PoolCreation_block_130_memory
  rw [h0, h32, h64, h96]
  have hcomm (w : UInt256) :
      UInt256.land (UInt256.lnot (UInt256.sub
        (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 96)) (UInt256.ofNat 1)))
        (UInt256.shiftLeft w (UInt256.ofNat 96)) = constructorAddressStored w :=
    u256_land_comm _ _
  rw [hcomm, hcomm]
  rfl

theorem constructorFieldsX {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {σ : AccountMap} {aw : UInt256} {k C : Nat} {out : ByteArray}
    (rd : RD (uniswapV3PoolCreationBytecode ++ tail) ee g s0 ⟨130⟩
      [UInt256.ofNat out.size, ⟨352⟩, ⟨0⟩] (constructorOutputMem ee.codeOwner out)
      aw out σ k C) (hlen : 160 ≤ out.size) :
    ∃ k' C' aw', RD (uniswapV3PoolCreationBytecode ++ tail) ee g s0 ⟨271⟩
      [calldataWord out 128, ⟨247⟩, calldataWord out 128]
      (constructorTickMem ee.codeOwner out) aw' out σ k' C' := by
  have rf := uniswapV3PoolCreation_block_130 (by decide) rd
  simp only [uniswapV3PoolCreation_block_130_stack] at rf
  have hm : memLoad (⟨352⟩ + UInt256.ofNat 128) (constructorOutputMem ee.codeOwner out) =
      calldataWord out 128 := constructorOutputMem_loadParameter _ _ 128 hlen (by decide)
  rw [hm, constructorFieldsSummaryMem _ _ hlen] at rf
  have rt := uniswapV3PoolCreation_block_210 (by decide) (by native_decide) rf
  exact ⟨_, _, _, rt⟩

theorem constructorAfterSpacingX {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {σ : AccountMap} {aw : UInt256} {k C : Nat} {out : ByteArray}
    (rd : RD (uniswapV3PoolCreationBytecode ++ tail) ee g s0 ⟨247⟩
      [EVM.wordOfInt (spacingLiquidity (constructorSpacing out)), calldataWord out 128]
      (constructorTickMem ee.codeOwner out) aw out σ k C) :
    ∃ k' C' aw', RD (uniswapV3PoolCreationBytecode ++ tail) ee g s0 ⟨381⟩ []
      (constructorFinalMem ee.codeOwner out) aw' out σ k' C' := by
  have rn := uniswapV3PoolCreation_block_247 (by decide) (by native_decide) rd
  exact ⟨_, _, _, rn⟩

theorem constructorBeforeRuntimeX {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {σ : AccountMap} {aw : UInt256} {k C : Nat} {out : ByteArray}
    (rd : RD (uniswapV3PoolCreationBytecode ++ tail) ee g s0 ⟨130⟩
      [UInt256.ofNat out.size, ⟨352⟩, ⟨0⟩] (constructorOutputMem ee.codeOwner out)
      aw out σ k C) (hlen : 160 ≤ out.size) :
    (RDinvalid (uniswapV3PoolCreationBytecode ++ tail) g s0 ∧
      (constructorSpacing out = 0 ∨ spacingCount (constructorSpacing out) = 0)) ∨
    (constructorSpacing out ≠ 0 ∧ spacingCount (constructorSpacing out) ≠ 0 ∧
      ∃ k' C' aw', RD (uniswapV3PoolCreationBytecode ++ tail) ee g s0 ⟨381⟩ []
        (constructorFinalMem ee.codeOwner out) aw' out σ k' C') := by
  obtain ⟨_, _, _, rt⟩ := constructorFieldsX rd hlen
  have hb := constructorSpacing_bounds out
  rcases tickSpacingCreationX (constructorSpacing out) rt rfl hb.1 hb.2 (by native_decide)
    (by change 11 ≤ 1024; decide) with hbad | ⟨hn, hc, _, _, rn⟩
  · exact Or.inl hbad
  exact Or.inr ⟨hn, hc, constructorAfterSpacingX rn⟩

end Benchmarks.UniswapV3.Pool
