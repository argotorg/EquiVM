import Benchmarks.UniswapV3.Pool.ObserveCalldata
import Benchmarks.UniswapV3.Pool.Dispatch

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem observeDecodeX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256} {s0 : EVM.State}
    {mem rdata : ByteArray} {aw : UInt256} {k C : Nat} {R : List UInt256}
    {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨1587⟩ R mem aw rdata σ k C)
    (hsz : 4 ≤ ee.calldata.size) (hsize : ee.calldata.size < UInt256.size)
    (hov : R.length + 10 ≤ 1024) :
    (¬ ObserveCalldataValid ee.calldata ∧ RDrev (deployedRuntime v) g s0) ∨
    (ObserveCalldataValid ee.calldata ∧ ∃ k' C',
      RD (deployedRuntime v) ee g s0 ⟨9436⟩
        (UInt256.ofNat (observeCount ee.calldata) :: UInt256.ofNat (observeDataStart ee.calldata) ::
          ⟨1699⟩ :: R) mem aw rdata σ k' C') := by
  by_cases hhead : ee.calldata.size < 36
  · have r1 := uniswapV3Pool_block_1587_fallthrough (immWords := wordsOf (immStore v))
      (by omega) (by rw [solcDecodeLenCheckShortUnsigned hsz hhead hsize]; decide) rd
    have r2 := uniswapV3Pool_block_1605 (immWords := wordsOf (immStore v))
      (by dsimp only [uniswapV3Pool_block_1587_fallthrough_stack, List.length]; omega) r1
    exact Or.inl ⟨fun h ↦ by have := h.head; omega, r2⟩
  have r1 := uniswapV3Pool_block_1587_taken (immWords := wordsOf (immStore v)) (by omega)
    (by rw [solcDecodeLenCheckOkUnsigned (by change 4 + 32 ≤ ee.calldata.size; omega) hsize]; decide)
    (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
  simp only [uniswapV3Pool_block_1587_taken_stack] at r1
  by_cases hoff : 2 ^ 32 < observeOffset ee.calldata
  · have r2 := uniswapV3Pool_block_1609_fallthrough (immWords := wordsOf (immStore v))
      (by dsimp only [List.length]; omega)
      (by rw [ugt_one (by exact hoff)]; decide) r1
    have r3 := uniswapV3Pool_block_1632 (immWords := wordsOf (immStore v))
      (by dsimp only [uniswapV3Pool_block_1609_fallthrough_stack, List.length]; omega) r2
    exact Or.inl ⟨fun h ↦ by have := h.offset; omega, r3⟩
  have r2 := uniswapV3Pool_block_1609_taken (immWords := wordsOf (immStore v))
    (by dsimp only [List.length]; omega)
    (by rw [ugt_zero (by change observeOffset ee.calldata ≤ 2 ^ 32; omega)]; decide)
    (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) r1
  simp only [uniswapV3Pool_block_1609_taken_stack,
    uadd_lit_usub_ofNat_lit hsz hsize] at r2
  change RD (deployedRuntime v) ee g s0 ⟨1636⟩
    (calldataWord ee.calldata 4 :: UInt256.ofNat 36 :: UInt256.ofNat 4 ::
      UInt256.ofNat ee.calldata.size :: ⟨1699⟩ :: R) mem aw rdata σ _ _ at r2
  have haddr : (UInt256.ofNat 4 + calldataWord ee.calldata 4).toNat =
      4 + observeOffset ee.calldata := add4_word_toNat _
        (by change observeOffset ee.calldata ≤ 2 ^ 64 - 1; omega)
  have hend : ((UInt256.ofNat 4 + calldataWord ee.calldata 4) + UInt256.ofNat 32).toNat =
      observeDataStart ee.calldata := by
    rw [uadd_word_ofNat_toNat _ 32 (by rw [haddr]; change _ < 2 ^ 256; omega), haddr]
    rfl
  have hszword := ulit_toNat' ee.calldata.size hsize
  by_cases hlen : ee.calldata.size < observeDataStart ee.calldata
  · have r3 := uniswapV3Pool_block_1636_fallthrough (immWords := wordsOf (immStore v))
      (by dsimp only [List.length]; omega)
      (by rw [ugt_one (by rw [hend, hszword]; exact hlen)]; decide) r2
    have r4 := uniswapV3Pool_block_1650 (immWords := wordsOf (immStore v))
      (by dsimp only [uniswapV3Pool_block_1636_fallthrough_stack, List.length]; omega) r3
    exact Or.inl ⟨fun h ↦ by have := h.length_word; omega, r4⟩
  have r3 := uniswapV3Pool_block_1636_taken (immWords := wordsOf (immStore v))
    (by dsimp only [List.length]; omega)
    (by rw [ugt_zero (by rw [hend, hszword]; omega)]; decide)
    (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) r2
  simp only [uniswapV3Pool_block_1636_taken_stack] at r3
  have hread : uInt256OfByteArray
      (ee.calldata.readBytes (UInt256.ofNat 4 + calldataWord ee.calldata 4).toNat 32) =
      UInt256.ofNat (observeCount ee.calldata) := by
    rw [haddr]
    exact (u256_ofNat_toNat _).symm
  have hstart : UInt256.ofNat 32 + (UInt256.ofNat 4 + calldataWord ee.calldata 4) =
      UInt256.ofNat (observeDataStart ee.calldata) := by
    apply u256_inj
    rw [uadd_toNat, haddr, ulit_toNat' (observeDataStart ee.calldata) (by
      unfold observeDataStart; change _ < 2 ^ 256; omega)]
    change (32 + (4 + observeOffset ee.calldata)) % UInt256.size = _
    rw [Nat.mod_eq_of_lt (by change _ < 2 ^ 256; omega)]
    unfold observeDataStart
    omega
  have hcountword : (UInt256.ofNat (observeCount ee.calldata)).toNat =
      observeCount ee.calldata := ulit_toNat' _ (calldataWord _ _).val.isLt
  by_cases hcount : 2 ^ 32 < observeCount ee.calldata
  · have r4 := uniswapV3Pool_block_1654_fallthrough (immWords := wordsOf (immStore v))
      (by dsimp only [List.length]; omega)
      (by rw [hread, ugt_one (by rw [hcountword]; exact hcount)]
          exact isZero_eq_zero_of_ne (u256_lor_one_left_ne_zero _)) r3
    have r5 := uniswapV3Pool_block_1684 (immWords := wordsOf (immStore v))
      (by dsimp only [uniswapV3Pool_block_1654_fallthrough_stack, List.length]; omega) r4
    exact Or.inl ⟨fun h ↦ by have := h.count; omega, r5⟩
  have hmul : (UInt256.mul (UInt256.ofNat (observeCount ee.calldata))
      (UInt256.ofNat 32)).toNat = 32 * observeCount ee.calldata := by
    rw [u256_mul_toNat, hcountword]
    change (observeCount ee.calldata * 32) % UInt256.size = _
    rw [Nat.mod_eq_of_lt (by change _ < 2 ^ 256; omega)]
    omega
  have hpayloadEnd : (UInt256.ofNat (observeDataStart ee.calldata) +
      UInt256.mul (UInt256.ofNat (observeCount ee.calldata)) (UInt256.ofNat 32)).toNat =
      observeDataStart ee.calldata + 32 * observeCount ee.calldata := by
    rw [uadd_toNat, hmul, ulit_toNat' (observeDataStart ee.calldata) (by
      unfold observeDataStart; change _ < 2 ^ 256; omega)]
    exact Nat.mod_eq_of_lt (by unfold observeDataStart; change _ < 2 ^ 256; omega)
  have hc0 : UInt256.gt (UInt256.ofNat (observeCount ee.calldata))
      (UInt256.ofNat 4294967296) = ⟨0⟩ := ugt_zero (by rw [hcountword]; exact Nat.le_of_not_gt hcount)
  by_cases hpayload : ee.calldata.size < observeDataStart ee.calldata + 32 * observeCount ee.calldata
  · have r4 := uniswapV3Pool_block_1654_fallthrough (immWords := wordsOf (immStore v))
      (by dsimp only [List.length]; omega)
      (by rw [hread, hstart, hc0, ugt_one (by rw [hpayloadEnd, hszword]; exact hpayload)]; decide) r3
    have r5 := uniswapV3Pool_block_1684 (immWords := wordsOf (immStore v))
      (by dsimp only [uniswapV3Pool_block_1654_fallthrough_stack, List.length]; omega) r4
    exact Or.inl ⟨fun h ↦ by have := h.payload; omega, r5⟩
  have r4 := uniswapV3Pool_block_1654_taken (immWords := wordsOf (immStore v))
    (by dsimp only [List.length]; omega)
    (by rw [hread, hstart, hc0, ugt_zero (by rw [hpayloadEnd, hszword]; omega)]; decide)
    (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) r3
  simp only [uniswapV3Pool_block_1654_taken_stack, hread, hstart] at r4
  have r5 := uniswapV3Pool_block_1688 (immWords := wordsOf (immStore v))
    (by dsimp only [List.length]; omega)
    (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) r4
  exact Or.inr ⟨⟨by omega, by omega, by omega, by omega, by omega⟩, _, _, r5⟩

end Benchmarks.UniswapV3.Pool
