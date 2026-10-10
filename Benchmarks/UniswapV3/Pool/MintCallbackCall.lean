import Benchmarks.UniswapV3.Pool.CallbackCallLayout
import Benchmarks.UniswapV3.Pool.MintCallbackBuild
import Benchmarks.UniswapV3.Pool.MintCallbackSource
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_022
import Benchmarks.UniswapV3.Pool.FlashCallbackCall

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

set_option maxHeartbeats 1000000 in
theorem mintCallbackCallX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 evm : EVM.State} {frame : Frame} {k C : Nat}
    {aw p amount0 amount1 len junk2 junk4 junk5 junk6 junk7 junk8 junk9 selector : UInt256}
    {target : AccountAddress} {mem rdata data : ByteArray} {R : List UInt256}
    {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨6050⟩
      (UInt256.lnot ⟨31⟩ :: len :: junk2 :: (p + ⟨132⟩) :: junk4 :: junk5 ::
        junk6 :: junk7 :: junk8 :: junk9 :: selector :: EVM.word target.val :: R)
      mem aw rdata σ k C)
    (hs : SourceState s0 ee σ evm) (hperm : ee.perm = true) (hm : HeapMemory mem aw p)
    (ht : frame.locals.get? "callback" = some (.address target))
    (hf0 : frame.locals.get? "amount0" = some (.int (Int.ofNat amount0.toNat)))
    (hf1 : frame.locals.get? "amount1" = some (.int (Int.ofNat amount1.toNat)))
    (hd : frame.locals.get? "data" = some (.bytes data)) (hdata : data.size = len.toNat)
    (hcd : mem.readWithPadding p.toNat (132 + paddedSize len.toNat) =
      mintCallbackCalldata amount0 amount1 data)
    (hl : len.toNat ≤ 2 ^ 32) (hb : p.toNat + len.toNat + 164 ≤ 2 ^ 200)
    (hov : R.length + 14 ≤ 1024) :
    (RDrev (deployedRuntime v) g s0 ∧ ExecBlock config frame evm mintCallbackStmts .reverted) ∨
    ∃ evm' σ' out aw' k' C', SourceState s0 ee σ' evm' ∧
      ExecBlock config frame evm mintCallbackStmts
        (.ok {frame with locals := frame.locals.insert "__c4" .unit} evm') ∧
      RD (deployedRuntime v) ee g s0 ⟨6116⟩
        (⟨0⟩ :: ((p + ⟨132⟩) + UInt256.ofNat (paddedSize len.toNat)) ::
          selector :: EVM.word target.val :: R) mem aw' out σ' k' C' ∧
      HeapMemory mem aw' p := by
  have hload : memLoad (UInt256.ofNat 64) mem = p := hm.load64
  have hround := callbackPaddedWord len hl
  have hpad : paddedSize len.toNat ≤ len.toNat + 31 := by unfold paddedSize; omega
  obtain ⟨hsize, hsub, hbound⟩ := callbackCallRange p len hb
  by_cases hc : extCodeSizeWord σ (EVM.word target.val) = ⟨0⟩
  · obtain ⟨kBad, CBad, rdBad⟩ := uniswapV3Pool_block_6050_fallthrough
      (immWords := wordsOf (immStore v)) hov (by rw [hc]; decide +kernel) rd
    exact Or.inl ⟨uniswapV3Pool_block_6092 (immWords := wordsOf (immStore v))
      (by simpa only [uniswapV3Pool_block_6050_fallthrough_stack, List.length_cons] using
        (show R.length + 12 ≤ 1024 by omega)) rdBad,
      mintCallbackNoCode hs.accounts ht hc⟩
  · obtain ⟨kGuard, CGuard, rdGuard⟩ := uniswapV3Pool_block_6050_taken
      (immWords := wordsOf (immStore v)) hov
      (by rw [isZero_eq_zero_of_ne hc]; decide +kernel)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
    simp only [uniswapV3Pool_block_6050_taken_stack, hload, hround, hsub] at rdGuard
    have rdCall := uniswapV3Pool_block_6096 (immWords := wordsOf (immStore v)) (by evm_ov) rdGuard
    simp only [uniswapV3Pool_block_6096_stack] at rdCall
    have hsmall : (mintCallbackCalldata amount0 amount1 data).size ≤ maxReturnDataSizeByGas := by
      rw [mintCallbackCalldata_size, hdata]
      have hbig : 2 ^ 32 + 163 ≤ maxReturnDataSizeByGas := by decide +kernel
      omega
    obtain ⟨evm', σ', ok, out, kCall, CCall, hcall, hs', rdAfter, hout⟩ :=
      callBridge rdCall hs hperm
        (by immutable_decode(immutableLayout, uniswapV3PoolBytecode, wordsOf (immStore v),
          (⟨6099⟩ : UInt256), (UInt8.ofNat 241), .CALL, none,
          immutableLayout_inBounds, immutableTemplate_size64))
        (by rw [hsize]; exact hcd) hsmall (by evm_ov)
    change callViaEVM evm (AccountAddress.ofUInt256 (EVM.word target.val)) 0
      (mintCallbackCalldata amount0 amount1 data) (ok, evm', out) at hcall
    rw [show AccountAddress.ofUInt256 (EVM.word target.val) = target from
      accountAddress_roundtrip target] at hcall
    rw [show callOutputMem mem out p (UInt256.ofNat 0) = mem from callOutputMem_zero mem out p] at rdAfter
    cases ok
    · have rdFail := uniswapV3Pool_block_6100_fallthrough (immWords := wordsOf (immStore v))
        (by evm_ov) (by decide +kernel) rdAfter
      exact Or.inl ⟨uniswapV3Pool_block_6107 (immWords := wordsOf (immStore v))
        (by simpa only [uniswapV3Pool_block_6100_fallthrough_stack, List.length_cons] using
          (show R.length + 7 ≤ 1024 by omega)) rdFail,
        mintCallbackReverts hs.accounts ht hf0 hf1 hd hc hcall⟩
    · have rdDone := uniswapV3Pool_block_6100_taken (immWords := wordsOf (immStore v))
        (by evm_ov) (by decide +kernel)
        (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rdAfter
      simp only [uniswapV3Pool_block_6100_taken_stack] at rdDone
      refine Or.inr ⟨evm', σ', out, _, _, _, hs',
        mintCallbackReturns hs.accounts ht hf0 hf1 hd hc hcall, rdDone, ?_⟩
      refine {hm with active := ?_}
      apply callActiveWords_active (activeWords_expand32 hm.active (by decide))
      · rw [hsize]; exact hbound
      · change p.toNat + 0 ≤ _; omega

end Benchmarks.UniswapV3.Pool
