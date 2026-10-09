import Benchmarks.Morpho.MorphoBlue.SafeTransferGuards
import Benchmarks.Morpho.MorphoBlue.SafeTransferFrames

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

def safeTransferNoCodeMem (mem : ByteArray) : ByteArray :=
  morphoErrorMem (UInt256.ofNat 7)
    (UInt256.ofNat 49950756904998485017489289260265740881339390581579809577546532654664829108224) mem

theorem safeTransferCodeGuard_true {frame : Frame} {evm : EVM.State} {token : AccountAddress}
    (ht : frame.locals.get? "token" = some (.address token))
    (hc : extCodeSizeWord evm.accountMap (UInt256.ofNat token.val) ≠ UInt256.ofNat 0) :
    evalExpr? config frame evm safeTransferCodeGuard = .ok (.bool true) := by
  have hp := code_pos_of_codeSize_ne_zero (evm := evm) (accountAddress_roundtrip token).symm hc
  simp only [safeTransferCodeGuard, evalExpr?, ht, EvalResult.ofOption, pure, bind, EvalResult.bind,
    evalBinaryOp?]
  norm_num [hp]
  exact hp

theorem safeTransferCodeGuard_false {frame : Frame} {evm : EVM.State} {token : AccountAddress}
    (ht : frame.locals.get? "token" = some (.address token))
    (hc : extCodeSizeWord evm.accountMap (UInt256.ofNat token.val) = UInt256.ofNat 0) :
    evalExpr? config frame evm safeTransferCodeGuard = .ok (.bool false) := by
  have hp := code_zero_of_codeSize_zero (evm := evm) (accountAddress_roundtrip token).symm hc
  simp only [safeTransferCodeGuard, evalExpr?, ht, EvalResult.ofOption, pure, bind, EvalResult.bind,
    evalBinaryOp?]
  norm_num [hp]
  exact hp

theorem morphoTransferCodeMessage {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem out : ByteArray} {aw ptr cond next : UInt256} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} (hstack : R.length + 11 ≤ 1024)
    (hfree : memLoad (UInt256.ofNat 64) mem = ptr) (hfit : ptr.toNat + 64 < 2 ^ 64)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 14491)
      (UInt256.ofNat 585 :: cond :: next :: R) mem aw out σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 (UInt256.ofNat 12097)
      (cond :: ptr :: next :: R) (safeTransferNoCodeMem mem) aw' out σ k' C' := by
  obtain ⟨a0, k0, C0, rd0⟩ := morphoBlocks.morpho_block_14491_packed
    (immWords := wordsOf (immStore v)) (by change R.length + 2 + 5 ≤ 1024; omega)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h
  dsimp only [morphoBlocks.morpho_block_14491_stack] at rd0
  rw [hfree] at rd0
  have hp := uadd_word_ofNat_toNat ptr 64 (by change _ < 2 ^ 256; omega)
  obtain ⟨a1, k1, C1, rd1⟩ := morphoAlloc64 (v := v)
    (by change R.length + 4 + 5 ≤ 1024; omega)
    (by rw [morphoPatchedValidJumps v]; jump_dest)
    (by rw [ugt_zero (by rw [hp]; change _ ≤ 18446744073709551615; omega),
      ult_zero (by rw [hp]; omega)]; rfl) rd0
  obtain ⟨a2, k2, C2, rd2⟩ := morphoBlocks.morpho_block_14504_packed
    (immWords := wordsOf (immStore v)) (by change R.length + 2 + 5 ≤ 1024; omega)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rd1
  obtain ⟨a3, k3, C3, rd3⟩ := morphoBlocks.morpho_block_585_packed
    (immWords := wordsOf (immStore v)) (by change R.length + 1 + 3 ≤ 1024; omega)
    (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) rd2
  refine ⟨a3, k3, C3, ?_⟩
  dsimp only [safeTransferNoCodeMem, morphoErrorMem]
  rw [hfree]
  exact rd3

theorem morphoTransferCodeOk {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem out : ByteArray} {aw ptr cond next : UInt256} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} (hstack : R.length + 11 ≤ 1024)
    (hfree : memLoad (UInt256.ofNat 64) mem = ptr) (hfit : ptr.toNat + 64 < 2 ^ 64)
    (hc : cond ≠ UInt256.ofNat 0) (hvalid : (D_J (deployedRuntime v) 0).contains next = true)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 14491)
      (UInt256.ofNat 585 :: cond :: next :: R) mem aw out σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 next R (safeTransferNoCodeMem mem) aw' out σ k' C' := by
  obtain ⟨a0, k0, C0, rd0⟩ := morphoTransferCodeMessage hstack hfree hfit h
  obtain ⟨k1, C1, rd1⟩ := morphoRequireTrue (by omega) hvalid (isZero_eq_zero_of_ne hc) rd0
  exact ⟨a0, k1, C1, rd1⟩

theorem morphoTransferCodeRevert {v : MorphoImmutables} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem out : ByteArray} {aw ptr cond next : UInt256} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} (hstack : R.length + 11 ≤ 1024)
    (hm : MorphoHeap mem ptr 0) (hbad : 2 ^ 64 ≤ ptr.toNat + 64 ∨ cond = UInt256.ofNat 0)
    (h : RD (deployedRuntime v) ee g s0 (UInt256.ofNat 14491)
      (UInt256.ofNat 585 :: cond :: next :: R) mem aw out σ k C) : RDrev (deployedRuntime v) g s0 := by
  by_cases hf : ptr.toNat + 64 < 2 ^ 64
  · have hc := hbad.resolve_left (by omega)
    obtain ⟨a0, k0, C0, rd0⟩ := morphoTransferCodeMessage hstack hm.free hf h
    have he := (morphoErrorMem_properties_general (UInt256.ofNat 7)
      (UInt256.ofNat 49950756904998485017489289260265740881339390581579809577546532654664829108224)
      ptr mem hm.lower hm.free hm.size (by have hg := hm.gap; omega)
      (by have hs := hm.space; change _ < 2 ^ 256; omega)).2.2
    refine morphoRequireFalseShort hstack hc ?_ ?_ rd0
    · change UInt256.lt (UInt256.ofNat 0) (morphoErrorLength (morphoErrorMem _ _ mem) ptr) ≠ _
      rw [he]; decide
    · change UInt256.lt (UInt256.ofNat 32) (morphoErrorLength (morphoErrorMem _ _ mem) ptr) = _
      rw [he]; decide
  · obtain ⟨a0, k0, C0, rd0⟩ := morphoBlocks.morpho_block_14491_packed
      (immWords := wordsOf (immStore v)) (by change R.length + 2 + 5 ≤ 1024; omega)
      (by rw [morphoPatchedValidJumpsRuntime v]; jump_dest) h
    dsimp only [morphoBlocks.morpho_block_14491_stack] at rd0
    rw [hm.free] at rd0
    exact morphoAlloc64Overflow (by change R.length + 5 + 4 ≤ 1024; omega)
      (by have hh := hm.space; omega) (by omega) rd0

end Benchmarks.Morpho.MorphoBlue
