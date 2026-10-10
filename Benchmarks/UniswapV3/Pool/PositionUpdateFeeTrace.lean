import Benchmarks.UniswapV3.Pool.PositionUpdateWords
import Benchmarks.UniswapV3.Pool.FullMathTrace
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_073

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem positionUpdateFeeX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p ret : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (a : PositionUpdateArgs) (evm : EVM.State)
    (rd : RD (deployedRuntime v) ee g s0 ⟨21733⟩
      (EVM.wordOfInt (positionUpdateLiquidityNext a evm) :: p :: a.growth1 :: a.growth0 ::
        EVM.wordOfInt a.delta :: solcMappingSlot ⟨7⟩ a.key :: ret :: R) mem aw rdata σ k C)
    (hm : WordArrayMemory mem p (positionSnapshotWords a.key evm.accountMap evm.executionEnv))
    (ha : ActiveWords aw) (hb : p.toNat + 160 ≤ 2 ^ 200) (hov : R.length + 25 ≤ 1024) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 ⟨21807⟩
      (positionUpdateFeeRaw a evm true :: ⟨0⟩ :: positionUpdateFeeRaw a evm false ::
        EVM.wordOfInt (positionUpdateLiquidityNext a evm) :: p :: a.growth1 :: a.growth0 ::
        EVM.wordOfInt a.delta :: solcMappingSlot ⟨7⟩ a.key :: ret :: R)
      mem aw' rdata σ k' C' ∧ ActiveWords aw' := by
  have hbword : p.toNat + 160 < UInt256.size := by change _ < 2 ^ 256; omega
  have hload := positionSnapshotLoadLiquidity a evm hm hbword
  have hlast0 : memLoad (p + UInt256.ofNat 32) mem =
      positionFieldWord a.key 1 0 32 evm.accountMap evm.executionEnv :=
    positionSnapshotLoadLast a evm false hm hbword
  have hlast1 : memLoad (p + UInt256.ofNat 64) mem =
      positionFieldWord a.key 2 0 32 evm.accountMap evm.executionEnv :=
    positionSnapshotLoadLast a evm true hm hbword
  have hclean : UInt256.land (UInt256.ofNat (2 ^ 128 - 1)) (positionUpdateLiquidityWord a evm) =
      positionUpdateLiquidityWord a evm := uint128Word_clean (positionUpdateLiquidityWord_lt a evm)
  have hshift : UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128) =
      UInt256.ofNat (2 ^ 128) := by native_decide
  have hb32 : (p + UInt256.ofNat 32).toNat + 32 ≤ 2 ^ 200 := by
    rw [uadd_word_ofNat_toNat p 32 (by change _ < 2 ^ 256; omega)]
    omega
  have hb64 : (p + UInt256.ofNat 64).toNat + 32 ≤ 2 ^ 200 := by
    rw [uadd_word_ofNat_toNat p 64 (by change _ < 2 ^ 256; omega)]
    omega
  have r1 := uniswapV3Pool_block_21733 (immWords := wordsOf (immStore v)) (by evm_ov)
    (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
  simp only [uniswapV3Pool_block_21733_stack] at r1
  rw [solcMask128, hshift] at r1
  simp only [
    show UInt256.ofNat 0 = (⟨0⟩ : UInt256) from rfl, u256_zero_add,
    u256_add_comm (UInt256.ofNat 32), hload, hlast0, hclean] at r1
  change RD (deployedRuntime v) ee g s0 ⟨13017⟩
    (UInt256.ofNat (2 ^ 128) :: positionUpdateLiquidityWord a evm ::
      positionUpdateFeeDelta a evm false :: ⟨21769⟩ :: ⟨0⟩ ::
      EVM.wordOfInt (positionUpdateLiquidityNext a evm) :: p :: a.growth1 :: a.growth0 ::
      EVM.wordOfInt a.delta :: solcMappingSlot ⟨7⟩ a.key :: ret :: R)
    mem _ rdata σ _ _ at r1
  rcases fullMathX (v := v) r1
    (by rw [uniswapV3PoolPatchedValidJumps v]; jump_dest) (by evm_ov) with
      ⟨hbad, _⟩ | ⟨_, k2, C2, _, r2⟩
  · exact False.elim (hbad (positionUpdateFeeValid a evm false))
  · have ha1 := activeWords_expand32 (activeWords_expand32 ha hb32)
      (show p.toNat + 32 ≤ 2 ^ 200 by omega)
    have r3 := uniswapV3Pool_block_21769 (immWords := wordsOf (immStore v)) (by evm_ov)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) r2
    simp only [uniswapV3Pool_block_21769_stack] at r3
    rw [solcMask128, hshift] at r3
    simp only [
      show UInt256.ofNat 0 = (⟨0⟩ : UInt256) from rfl, u256_zero_add,
      u256_add_comm (UInt256.ofNat 64), hload, hlast1, hclean] at r3
    change RD (deployedRuntime v) ee g s0 ⟨13017⟩
      (UInt256.ofNat (2 ^ 128) :: positionUpdateLiquidityWord a evm ::
        positionUpdateFeeDelta a evm true :: ⟨21807⟩ :: ⟨0⟩ :: positionUpdateFeeRaw a evm false ::
        EVM.wordOfInt (positionUpdateLiquidityNext a evm) :: p :: a.growth1 :: a.growth0 ::
        EVM.wordOfInt a.delta :: solcMappingSlot ⟨7⟩ a.key :: ret :: R)
      mem _ rdata σ _ _ at r3
    rcases fullMathX (v := v) r3
      (by rw [uniswapV3PoolPatchedValidJumps v]; jump_dest) (by evm_ov) with
        ⟨hbad, _⟩ | ⟨_, k4, C4, _, r4⟩
    · exact False.elim (hbad (positionUpdateFeeValid a evm true))
    · exact ⟨_, k4, C4, r4, activeWords_expand32 (activeWords_expand32 ha1 hb64)
        (show p.toNat + 32 ≤ 2 ^ 200 by omega)⟩

end Benchmarks.UniswapV3.Pool
