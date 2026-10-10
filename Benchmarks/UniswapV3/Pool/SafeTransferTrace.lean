import Benchmarks.UniswapV3.Pool.SafeTransferSource
import Benchmarks.UniswapV3.Pool.Dispatch

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem safeTransferRequireFalseX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨15511⟩ (⟨0⟩ :: R) mem aw rdata σ k C)
    (hov : R.length + 7 ≤ 1024) : RDrev (deployedRuntime v) g s0 := by
  have rdRevert := uniswapV3Pool_block_15511_fallthrough (immWords := wordsOf (immStore v))
    (by omega) rfl rd
  simp only [uniswapV3Pool_block_15511_fallthrough_stack] at rdRevert
  exact uniswapV3Pool_block_15516 (immWords := wordsOf (immStore v)) (by evm_ov) rdRevert

theorem safeTransferRequireTrueX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw word : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨15511⟩ (word :: R) mem aw rdata σ k C)
    (hword : word ≠ ⟨0⟩) (hov : R.length + 2 ≤ 1024) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 ⟨15565⟩ R mem aw rdata σ k' C' := by
  have rdReturn := uniswapV3Pool_block_15511_taken (immWords := wordsOf (immStore v)) hov
    hword (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
  exact ⟨_, _, rdReturn⟩

theorem safeTransferDataX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw flag ptr : UInt256} {mem out : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨15478⟩ (flag :: ptr :: R) mem aw out σ k C)
    (hlen : memLoad ptr mem = UInt256.ofNat out.size)
    (hword : 32 ≤ out.size → memLoad ((UInt256.ofNat 32) + ptr) mem =
      UInt256.ofNat (fromByteArrayBigEndian (out.extract 0 32)))
    (hsize : out.size < 2 ^ 255) (ha : ActiveWords aw)
    (hptr : ptr.toNat + 64 ≤ 2 ^ 200) (hov : R.length + 8 ≤ 1024) :
    (RDrev (deployedRuntime v) g s0 ∧ out.size ≠ 0 ∧
      (decodeReturnValueWithMode? config.abiDecodeMode abiBool out = none ∨
       decodeReturnValueWithMode? config.abiDecodeMode abiBool out = some (.bool false))) ∨
    ((out.size = 0 ∨ decodeReturnValueWithMode? config.abiDecodeMode abiBool out = some (.bool true)) ∧
      ∃ aw' k' C', RD (deployedRuntime v) ee g s0 ⟨15565⟩ (ptr :: R) mem aw' out σ k' C' ∧
        ActiveWords aw') := by
  have hsz : out.size < UInt256.size := lt_size_of_lt_sign hsize
  have ha1 : ActiveWords (M aw ptr ⟨32⟩) := activeWords_expand32 ha (by omega)
  by_cases hempty : out.size = 0
  · have rdFlag := uniswapV3Pool_block_15478_taken (immWords := wordsOf (immStore v))
      (by evm_ov) (by rw [hlen, hempty]; decide)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
    simp only [uniswapV3Pool_block_15478_taken_stack, hlen, hempty] at rdFlag
    obtain ⟨k', C', rdReturn⟩ := safeTransferRequireTrueX (v := v) rdFlag (by decide) (by evm_ov)
    exact Or.inr ⟨Or.inl hempty, _, k', C', rdReturn, ha1⟩
  · have hlenNe : UInt256.ofNat out.size ≠ ⟨0⟩ := by
      intro heq
      have hn := congrArg UInt256.toNat heq
      rw [ulit_toNat' _ hsz] at hn
      exact hempty hn
    have rdSize := uniswapV3Pool_block_15478_fallthrough (immWords := wordsOf (immStore v))
      (by evm_ov) (by rw [hlen, isZero_eq_zero_of_ne hlenNe]; rfl) rd
    simp only [uniswapV3Pool_block_15478_fallthrough_stack] at rdSize
    by_cases hlong : 32 ≤ out.size
    · have rdLoad := uniswapV3Pool_block_15487_taken (immWords := wordsOf (immStore v))
        (by evm_ov) (by rw [hlen, ult_zero (by rw [ulit_toNat' _ hsz]; exact hlong)]; decide)
        (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rdSize
      simp only [uniswapV3Pool_block_15487_taken_stack] at rdLoad
      have rdFlag := uniswapV3Pool_block_15508 (immWords := wordsOf (immStore v)) (by evm_ov) rdLoad
      simp only [uniswapV3Pool_block_15508_stack, hword hlong] at rdFlag
      by_cases hzero : UInt256.ofNat (fromByteArrayBigEndian (out.extract 0 32)) = ⟨0⟩
      · rw [hzero] at rdFlag
        exact Or.inl ⟨safeTransferRequireFalseX (v := v) rdFlag (by evm_ov), hempty,
          Or.inr (decodeReturnValueWithMode_legacy_bool_false hlong hsize hzero)⟩
      · have ha2 : ActiveWords (M (M aw ptr ⟨32⟩) ptr ⟨32⟩) :=
          activeWords_expand32 ha1 (by omega)
        have ha3 : ActiveWords (M (M (M aw ptr ⟨32⟩) ptr ⟨32⟩)
            ((UInt256.ofNat 32) + ptr) ⟨32⟩) := by
          apply activeWords_expand32 ha2
          rw [u256_add_comm (UInt256.ofNat 32),
            uadd_word_ofNat_toNat ptr 32 (by change _ < 2 ^ 256; omega)]
          omega
        obtain ⟨k', C', rdReturn⟩ := safeTransferRequireTrueX (v := v) rdFlag hzero (by evm_ov)
        exact Or.inr ⟨Or.inr (decodeReturnValueWithMode_legacy_bool_true hlong hsize hzero),
          _, k', C', rdReturn, ha3⟩
    · have hshort : out.size < 32 := by omega
      have rdRevert := uniswapV3Pool_block_15487_fallthrough (immWords := wordsOf (immStore v))
        (by evm_ov) (by rw [hlen, ult_one (by rw [ulit_toNat' _ hsz]; exact hshort)]; decide) rdSize
      simp only [uniswapV3Pool_block_15487_fallthrough_stack] at rdRevert
      exact Or.inl ⟨uniswapV3Pool_block_15504 (immWords := wordsOf (immStore v))
        (by evm_ov) rdRevert, hempty, Or.inl (decodeReturnValueWithMode_legacy_bool_none_short hshort)⟩

theorem safeTransferFinishX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 evm evm' : EVM.State} {k C : Nat} {aw ptr junk0 junk1 junk2 arg0 arg1 arg2 ret : UInt256}
    {mem out : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (imms : Store) (token recipient : AccountAddress) (value : UInt256) (ok : Bool)
    (rd : RD (deployedRuntime v) ee g s0 ⟨15465⟩
      (junk0 :: ptr :: ok.toUInt256 :: junk1 :: junk2 :: arg0 :: arg1 :: arg2 :: ret :: R)
      mem aw out σ k C)
    (hcall : callViaEVM evm token 0 (safeTransferCalldata recipient value) (ok, evm', out) true)
    (hlen : memLoad ptr mem = UInt256.ofNat out.size)
    (hword : 32 ≤ out.size → memLoad ((UInt256.ofNat 32) + ptr) mem =
      UInt256.ofNat (fromByteArrayBigEndian (out.extract 0 32)))
    (hsize : out.size < 2 ^ 255) (ha : ActiveWords aw)
    (hptr : ptr.toNat + 64 ≤ 2 ^ 200)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hov : R.length + 13 ≤ 1024) :
    (RDrev (deployedRuntime v) g s0 ∧
      ExecFuncBody config (safeTransferFrame imms token recipient value) evm
        safeTransferFunction.body .reverted) ∨
    (∃ aw' k' C', RD (deployedRuntime v) ee g s0 ret R mem aw' out σ k' C' ∧
      ExecFuncBody config (safeTransferFrame imms token recipient value) evm safeTransferFunction.body
        (.returned (safeTransferCallFrame imms token recipient value true out) evm' none) ∧
      ActiveWords aw') := by
  cases ok with
  | false =>
      have rdFlag := uniswapV3Pool_block_15465_taken (immWords := wordsOf (immStore v))
        (by evm_ov) (by decide)
        (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
      simp only [uniswapV3Pool_block_15465_taken_stack, Bool.toUInt256_false] at rdFlag
      exact Or.inl ⟨safeTransferRequireFalseX (v := v) rdFlag (by evm_ov),
        safeTransferRevertsCall imms evm evm' token recipient value out hcall⟩
  | true =>
      have rdData := uniswapV3Pool_block_15465_fallthrough (immWords := wordsOf (immStore v))
        (by evm_ov) (by decide) rd
      simp only [uniswapV3Pool_block_15465_fallthrough_stack] at rdData
      rcases safeTransferDataX (v := v) rdData hlen hword hsize ha hptr (by evm_ov) with
        ⟨rdRevert, hne, hbad⟩ | ⟨hgood, aw', k', C', rdReturn, ha'⟩
      · refine Or.inl ⟨rdRevert, ?_⟩
        rcases hbad with hdecode | hfalse
        · exact safeTransferRevertsDecode imms evm evm' token recipient value out hcall hne hdecode
        · exact safeTransferRevertsFalse imms evm evm' token recipient value out hcall hne hfalse
      · have rdDone := uniswapV3Pool_block_15565 (immWords := wordsOf (immStore v))
          (by evm_ov) hret rdReturn
        exact Or.inr ⟨aw', _, _, rdDone,
          safeTransferReturns imms evm evm' token recipient value out hcall hgood, ha'⟩

end Benchmarks.UniswapV3.Pool
