import Benchmarks.UniswapV3.Pool.ConstructorInputMemory
import Benchmarks.UniswapV3.Pool.CreationBlocks_001

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open uniswapV3PoolCreationBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 1000

theorem constructorInputSummaryMem (ee : ExecutionEnv) :
    uniswapV3PoolCreation_block_18_taken_memory (ee := ee) (mem := constructorFreeMem) =
      constructorInputMem ee.codeOwner := by
  unfold uniswapV3PoolCreation_block_18_taken_memory
  change writeWord (constructorOriginalMem ee.codeOwner)
    (memLoad ⟨64⟩ (constructorOriginalMem ee.codeOwner)).toNat constructorSelectorWord = _
  rw [constructorOriginalMem_load64]
  rfl

theorem constructorInputSummaryStack (ee : ExecutionEnv) (σ : AccountMap) :
    uniswapV3PoolCreation_block_18_taken_stack (ee := ee) (σ := σ)
      (mem := constructorFreeMem) (R := []) =
    [UInt256.isZero (extCodeSizeWord σ (UInt256.ofNat ee.source.val)),
      UInt256.ofNat ee.source.val, ⟨352⟩, ⟨4⟩, ⟨352⟩, ⟨160⟩, ⟨356⟩,
      ⟨2298697520⟩, UInt256.ofNat ee.source.val, ⟨0⟩] := by
  have ho : memLoad (UInt256.ofNat 64)
      ((UInt256.shiftLeft (UInt256.ofNat ee.codeOwner.val) (UInt256.ofNat 96)).toByteArray.write
        0 constructorFreeMem (UInt256.ofNat 128).toNat 32) = ⟨352⟩ :=
    constructorOriginalMem_load64 ee.codeOwner
  unfold uniswapV3PoolCreation_block_18_taken_stack
  rw [ho]
  change [UInt256.isZero (extCodeSizeWord σ (UInt256.ofNat ee.source.val)),
    UInt256.ofNat ee.source.val, memLoad ⟨64⟩ (constructorInputMem ee.codeOwner),
    UInt256.sub ⟨352⟩ (memLoad ⟨64⟩ (constructorInputMem ee.codeOwner)) + ⟨4⟩,
    memLoad ⟨64⟩ (constructorInputMem ee.codeOwner), ⟨160⟩, ⟨352⟩ + ⟨4⟩,
    ⟨2298697520⟩, UInt256.ofNat ee.source.val, ⟨0⟩] = _
  rw [constructorInputMem_load64]
  rfl

theorem constructorNonpayableX {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {σ : AccountMap} {aw : UInt256} {k C : Nat} {rdata : ByteArray}
    (rd : RD (uniswapV3PoolCreationBytecode ++ tail) ee g s0 ⟨0⟩ [] ByteArray.empty aw rdata σ k C)
    (hwv : ee.weiValue ≠ ⟨0⟩) : RDrev (uniswapV3PoolCreationBytecode ++ tail) g s0 := by
  have rb := uniswapV3PoolCreation_block_0_fallthrough (by decide)
    (isZero_eq_zero_of_ne hwv) rd
  exact uniswapV3PoolCreation_block_14 (by change 3 ≤ 1024; decide) rb

theorem constructorZeroValueX {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {σ : AccountMap} {aw : UInt256} {k C : Nat} {rdata : ByteArray}
    (rd : RD (uniswapV3PoolCreationBytecode ++ tail) ee g s0 ⟨0⟩ [] ByteArray.empty aw rdata σ k C)
    (hwv : ee.weiValue = ⟨0⟩) :
    ∃ k' C' aw', RD (uniswapV3PoolCreationBytecode ++ tail) ee g s0 ⟨18⟩ [⟨0⟩]
      constructorFreeMem aw' rdata σ k' C' := by
  have rn := uniswapV3PoolCreation_block_0_taken (by decide) (by rw [hwv]; decide)
    (by native_decide) rd
  simp only [uniswapV3PoolCreation_block_0_taken_stack, hwv] at rn
  exact ⟨_, _, _, rn⟩

theorem constructorNoCodeX {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {σ : AccountMap} {aw : UInt256} {k C : Nat} {rdata : ByteArray}
    (rd : RD (uniswapV3PoolCreationBytecode ++ tail) ee g s0 ⟨18⟩ [⟨0⟩]
      constructorFreeMem aw rdata σ k C)
    (hc : extCodeSizeWord σ (UInt256.ofNat ee.source.val) = ⟨0⟩) :
    RDrev (uniswapV3PoolCreationBytecode ++ tail) g s0 := by
  obtain ⟨_, _, rb⟩ := uniswapV3PoolCreation_block_18_fallthrough (by decide)
    (by rw [hc]; decide) rd
  exact uniswapV3PoolCreation_block_82 (by change 12 ≤ 1024; decide) rb

theorem constructorBeforeCallX {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {σ : AccountMap} {aw : UInt256} {k C : Nat} {rdata : ByteArray}
    (rd : RD (uniswapV3PoolCreationBytecode ++ tail) ee g s0 ⟨18⟩ [⟨0⟩]
      constructorFreeMem aw rdata σ k C)
    (hc : extCodeSizeWord σ (UInt256.ofNat ee.source.val) ≠ ⟨0⟩) :
    ∃ k' C' aw' gasArg, RD (uniswapV3PoolCreationBytecode ++ tail) ee g s0 ⟨89⟩
      [gasArg, UInt256.ofNat ee.source.val, ⟨352⟩, ⟨4⟩, ⟨352⟩, ⟨160⟩,
        ⟨356⟩, ⟨2298697520⟩, UInt256.ofNat ee.source.val, ⟨0⟩]
      (constructorInputMem ee.codeOwner) aw' rdata σ k' C' := by
  obtain ⟨_, _, rn⟩ := uniswapV3PoolCreation_block_18_taken (by decide)
    (by rw [isZero_eq_zero_of_ne hc]; decide) (by native_decide) rd
  rw [constructorInputSummaryMem, constructorInputSummaryStack] at rn
  have rout := uniswapV3PoolCreation_block_86 (by change 10 ≤ 1024; decide) rn
  exact ⟨_, _, _, _, rout⟩

end Benchmarks.UniswapV3.Pool
