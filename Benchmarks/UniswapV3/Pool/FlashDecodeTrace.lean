import Benchmarks.UniswapV3.Pool.FlashCalldata
import Benchmarks.UniswapV3.Pool.Dispatch
import Benchmarks.UniswapV3.Pool.BytesWindowWords

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem flashDecodeX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256} {s0 : EVM.State}
    {mem rdata : ByteArray} {aw : UInt256} {k C : Nat} {R : List UInt256}
    {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨1136⟩ R mem aw rdata σ k C)
    (hsz : 4 ≤ ee.calldata.size) (hsize : ee.calldata.size < UInt256.size)
    (hov : R.length + 12 ≤ 1024) :
    (¬ FlashCalldataValid ee.calldata ∧ RDrev (deployedRuntime v) g s0) ∨
    (FlashCalldataValid ee.calldata ∧ ∃ k' C',
      RD (deployedRuntime v) ee g s0 ⟨6440⟩
        (UInt256.ofNat (flashDataLength ee.calldata) :: UInt256.ofNat (flashDataStart ee.calldata) ::
          (flashDecodedArgs ee.calldata).amount1 :: (flashDecodedArgs ee.calldata).amount0 ::
          EVM.word (flashDecodedArgs ee.calldata).recipient.val :: ⟨857⟩ :: R) mem aw rdata σ k' C') := by
  by_cases hhead : ee.calldata.size < 132
  · have r1 := uniswapV3Pool_block_1136_fallthrough (immWords := wordsOf (immStore v))
      (by omega) (by rw [solcDecodeLenCheckShortUnsigned hsz hhead hsize]; decide) rd
    have r2 := uniswapV3Pool_block_1154 (immWords := wordsOf (immStore v))
      (by dsimp only [uniswapV3Pool_block_1136_fallthrough_stack, List.length]; omega) r1
    exact Or.inl ⟨fun h ↦ by have := h.head; omega, r2⟩
  have r1 := uniswapV3Pool_block_1136_taken (immWords := wordsOf (immStore v)) (by omega)
    (by rw [solcDecodeLenCheckOkUnsigned (by change 4 + 128 ≤ ee.calldata.size; omega) hsize]; decide)
    (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
  simp only [uniswapV3Pool_block_1136_taken_stack] at r1
  by_cases hoff : 2 ^ 32 < flashOffset ee.calldata
  · have r2 := uniswapV3Pool_block_1158_fallthrough (immWords := wordsOf (immStore v))
      (by dsimp only [List.length]; omega)
      (by rw [ugt_one (by exact hoff)]; decide) r1
    have r3 := uniswapV3Pool_block_1209 (immWords := wordsOf (immStore v))
      (by dsimp only [uniswapV3Pool_block_1158_fallthrough_stack, List.length]; omega) r2
    exact Or.inl ⟨fun h ↦ by have := h.offset; omega, r3⟩
  have r2 := uniswapV3Pool_block_1158_taken (immWords := wordsOf (immStore v))
    (by dsimp only [List.length]; omega)
    (by rw [ugt_zero (by change flashOffset ee.calldata ≤ 2 ^ 32; omega)]; decide)
    (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) r1
  simp only [uniswapV3Pool_block_1158_taken_stack,
    uadd_lit_usub_ofNat_lit hsz hsize] at r2
  have hclean : UInt256.land (uInt256OfByteArray
      (ee.calldata.readBytes (UInt256.ofNat 4).toNat 32))
      (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) =
      EVM.word (flashDecodedArgs ee.calldata).recipient.val := by
    change UInt256.land (calldataWord ee.calldata 4) solcAddrMask = _
    exact (word_of_addressOfNat_eq_mask _).symm
  rw [hclean] at r2
  change RD (deployedRuntime v) ee g s0 ⟨1213⟩
    (calldataWord ee.calldata 100 :: UInt256.ofNat 132 :: UInt256.ofNat 4 ::
      UInt256.ofNat ee.calldata.size :: (flashDecodedArgs ee.calldata).amount1 ::
      (flashDecodedArgs ee.calldata).amount0 :: EVM.word (flashDecodedArgs ee.calldata).recipient.val ::
      ⟨857⟩ :: R) mem aw rdata σ _ _ at r2
  have ho64 : (calldataWord ee.calldata 100).toNat ≤ solcMaxU64 := by
    change flashOffset ee.calldata ≤ 2 ^ 64 - 1; omega
  have haddr : (UInt256.ofNat 4 + calldataWord ee.calldata 100).toNat =
      4 + flashOffset ee.calldata := add4_word_toNat _ ho64
  have hend : ((UInt256.ofNat 4 + calldataWord ee.calldata 100) + UInt256.ofNat 32).toNat =
      flashDataStart ee.calldata := bytesWindow_start_toNat ho64
  have hszword := ulit_toNat' ee.calldata.size hsize
  by_cases hlen : ee.calldata.size < flashDataStart ee.calldata
  · have r3 := uniswapV3Pool_block_1213_fallthrough (immWords := wordsOf (immStore v))
      (by dsimp only [List.length]; omega)
      (by rw [ugt_one (by rw [hend, hszword]; exact hlen)]; decide) r2
    have r4 := uniswapV3Pool_block_1227 (immWords := wordsOf (immStore v))
      (by dsimp only [uniswapV3Pool_block_1213_fallthrough_stack, List.length]; omega) r3
    exact Or.inl ⟨fun h ↦ by have := h.length_word; omega, r4⟩
  have r3 := uniswapV3Pool_block_1213_taken (immWords := wordsOf (immStore v))
    (by dsimp only [List.length]; omega)
    (by rw [ugt_zero (by rw [hend, hszword]; omega)]; decide)
    (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) r2
  simp only [uniswapV3Pool_block_1213_taken_stack] at r3
  have hread : uInt256OfByteArray
      (ee.calldata.readBytes (UInt256.ofNat 4 + calldataWord ee.calldata 100).toNat 32) =
      UInt256.ofNat (flashDataLength ee.calldata) := by
    rw [haddr]
    exact (u256_ofNat_toNat _).symm
  have hstart : UInt256.ofNat 32 + (UInt256.ofNat 4 + calldataWord ee.calldata 100) =
      UInt256.ofNat (flashDataStart ee.calldata) := bytesWindow_start_word ho64
  have hcountword : (UInt256.ofNat (flashDataLength ee.calldata)).toNat =
      flashDataLength ee.calldata := ulit_toNat' _ (calldataWord _ _).val.isLt
  by_cases hcount : 2 ^ 32 < flashDataLength ee.calldata
  · have r4 := uniswapV3Pool_block_1231_fallthrough (immWords := wordsOf (immStore v))
      (by dsimp only [List.length]; omega)
      (by rw [hread, ugt_one (by rw [hcountword]; exact hcount)]
          exact isZero_eq_zero_of_ne (u256_lor_one_left_ne_zero _)) r3
    have r5 := uniswapV3Pool_block_1261 (immWords := wordsOf (immStore v))
      (by dsimp only [uniswapV3Pool_block_1231_fallthrough_stack, List.length]; omega) r4
    exact Or.inl ⟨fun h ↦ by have := h.length; omega, r5⟩
  have hpayloadEnd : (UInt256.ofNat (flashDataStart ee.calldata) +
      UInt256.mul (UInt256.ofNat (flashDataLength ee.calldata)) (UInt256.ofNat 1)).toNat =
      flashDataStart ee.calldata + flashDataLength ee.calldata := by
    have h := bytesWindow_end_toNat ho64 (len := UInt256.ofNat (flashDataLength ee.calldata))
      (by rw [hcountword]; change flashDataLength ee.calldata ≤ 2 ^ 64 - 1; omega)
    rw [hstart, hcountword] at h
    exact h
  have hc0 : UInt256.gt (UInt256.ofNat (flashDataLength ee.calldata))
      (UInt256.ofNat 4294967296) = ⟨0⟩ := ugt_zero (by rw [hcountword]; exact Nat.le_of_not_gt hcount)
  by_cases hpayload : ee.calldata.size < flashDataStart ee.calldata + flashDataLength ee.calldata
  · have r4 := uniswapV3Pool_block_1231_fallthrough (immWords := wordsOf (immStore v))
      (by dsimp only [List.length]; omega)
      (by rw [hread, hstart, hc0, ugt_one (by rw [hpayloadEnd, hszword]; exact hpayload)]; decide) r3
    have r5 := uniswapV3Pool_block_1261 (immWords := wordsOf (immStore v))
      (by dsimp only [uniswapV3Pool_block_1231_fallthrough_stack, List.length]; omega) r4
    exact Or.inl ⟨fun h ↦ by have := h.payload; omega, r5⟩
  have r4 := uniswapV3Pool_block_1231_taken (immWords := wordsOf (immStore v))
    (by dsimp only [List.length]; omega)
    (by rw [hread, hstart, hc0, ugt_zero (by rw [hpayloadEnd, hszword]; omega)]; decide)
    (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) r3
  simp only [uniswapV3Pool_block_1231_taken_stack, hread, hstart] at r4
  have r5 := uniswapV3Pool_block_1265 (immWords := wordsOf (immStore v))
    (by dsimp only [List.length]; omega)
    (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) r4
  exact Or.inr ⟨⟨by omega, by omega, by omega, by omega, by omega⟩, _, _, r5⟩

end Benchmarks.UniswapV3.Pool
