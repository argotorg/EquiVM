import Benchmarks.UniswapV3.Pool.SwapTransferBuild
import Benchmarks.UniswapV3.Pool.Balance
import Benchmarks.UniswapV3.Pool.BalanceCaller
import Benchmarks.UniswapV3.Pool.SourceFrame
import Benchmarks.UniswapV3.Pool.SourceCallFrames

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def swapBalanceBeforeReturn (zeroForOne : Bool) : UInt256 :=
  if zeroForOne then ⟨4602⟩ else ⟨4904⟩

def swapBalanceBeforeName (zeroForOne : Bool) : Ident :=
  if zeroForOne then "balance0Before" else "balance1Before"

def swapBalanceBeforeFrame (frame : Frame) (zeroForOne : Bool) (value : UInt256) : Frame :=
  resumeAfterInternalCall frame (swapBalanceBeforeName zeroForOne)
    (some [.int (Int.ofNat value.toNat)])

theorem swapBalanceBeforeFrame_parts (frame : Frame) (zeroForOne : Bool) (value : UInt256) :
    (swapBalanceBeforeFrame frame zeroForOne value).contract = frame.contract ∧
    (swapBalanceBeforeFrame frame zeroForOne value).immutables = frame.immutables := ⟨rfl, rfl⟩

theorem swapBalanceBeforeFrame_get (frame : Frame) (zeroForOne : Bool) (value : UInt256)
    (name : Ident) (hn : name ≠ swapBalanceBeforeName zeroForOne) :
    (swapBalanceBeforeFrame frame zeroForOne value).locals.get? name = frame.locals.get? name :=
  resumeAfterInternalCall_get frame _ name _ hn

theorem swapBalanceBeforeFrame_value (frame : Frame) (zeroForOne : Bool) (value : UInt256) :
    (swapBalanceBeforeFrame frame zeroForOne value).locals.get? (swapBalanceBeforeName zeroForOne) =
      some (.int (Int.ofNat value.toNat)) := Std.HashMap.getElem?_insert_self

theorem swapBalanceBeforeStmt_eq (zeroForOne : Bool) :
    (swapPaymentBody zeroForOne)[1]! =
      .internalCall (if !zeroForOne then "balance1" else "balance0") []
        (swapBalanceBeforeName zeroForOne) := by cases zeroForOne <;> rfl

theorem swapBalanceBeforeEntryX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (zeroForOne : Bool)
    (rd : RD (deployedRuntime v) ee g s0 (swapTransferExit zeroForOne) R mem aw rdata σ k C)
    (hov : R.length + 3 ≤ 1024) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 (balanceEntry (!zeroForOne))
      ([swapBalanceBeforeReturn zeroForOne, ⟨0⟩] ++ R) mem aw rdata σ k' C' := by
  cases zeroForOne
  · exact ⟨_, _, uniswapV3Pool_block_4894 (immWords := wordsOf (immStore v)) hov
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; native_decide) rd⟩
  · exact ⟨_, _, uniswapV3Pool_block_4592 (immWords := wordsOf (immStore v)) hov
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; native_decide) rd⟩

theorem swapBalanceBeforeX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw free : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (zeroForOne : Bool) (frame : Frame) (evm : EVM.State)
    (rd : RD (deployedRuntime v) ee g s0 (swapTransferExit zeroForOne) R mem aw rdata σ k C)
    (hsource : SourceState s0 ee σ evm) (hf : frame.contract = contract)
    (hi : frame.immutables = immStore v)
    (hm : HeapMemory mem aw free) (hmem : 128 ≤ mem.size)
    (hzero : memLoad (UInt256.ofNat 96) mem = ⟨0⟩)
    (hb : free.toNat + 2 ^ 138 + 163 ≤ 2 ^ 200) (hov : R.length + 19 ≤ 1024) :
    (ExecStmt config frame evm (swapPaymentBody zeroForOne)[1]! .reverted ∧
      RDrev (deployedRuntime v) g s0) ∨
    ∃ evm' σ' out mem' aw' next value k' C', SourceState s0 ee σ' evm' ∧
      ExecStmt config frame evm (swapPaymentBody zeroForOne)[1]!
        (.ok (swapBalanceBeforeFrame frame zeroForOne value) evm') ∧
      RD (deployedRuntime v) ee g s0 (swapBalanceBeforeReturn zeroForOne)
        ([value, ⟨0⟩] ++ R) mem' aw' out σ' k' C' ∧
      HeapMemory mem' aw' next ∧ MemoryPrefix mem mem' free.toNat ∧
      128 ≤ mem'.size ∧ memLoad (UInt256.ofNat 96) mem' = ⟨0⟩ ∧
      free.toNat ≤ next.toNat ∧ next.toNat ≤ free.toNat + 2 ^ 138 + 131 := by
  obtain ⟨k1, C1, r1⟩ := swapBalanceBeforeEntryX (v := v) zeroForOne rd (by omega)
  have hret : (D_J (deployedRuntime v) 0).contains (swapBalanceBeforeReturn zeroForOne) = true := by
    rw [uniswapV3PoolPatchedValidJumps v]; cases zeroForOne <;> native_decide
  rcases balanceGrowingX (v := v) (!zeroForOne) r1 hsource hm hmem hzero hb hret
      (by change R.length + 1 + 18 ≤ 1024; omega) with
    ⟨rr, hex⟩ | ⟨evm', σ', out, mem', aw', next, k', C', hsrc, hex, rr, hm', hpref, hlo, hhi⟩
  · have hx := poolBalanceReverts v frame.locals (swapBalanceBeforeName zeroForOne) evm
      (!zeroForOne) hex
    rw [← frame_eq_of_parts hf hi, ← swapBalanceBeforeStmt_eq] at hx
    exact Or.inl ⟨hx, rr⟩
  · have hx := poolBalanceReturns v frame.locals (swapBalanceBeforeName zeroForOne) evm evm'
      (!zeroForOne) (balanceValue out) _ hex
    have hx' : ExecStmt config frame evm (swapPaymentBody zeroForOne)[1]!
        (.ok (swapBalanceBeforeFrame frame zeroForOne (balanceValue out)) evm') := by
      rw [swapBalanceBeforeStmt_eq, frame_eq_of_parts hf hi]
      exact hx
    refine Or.inr ⟨evm', σ', out, mem', aw', next, balanceValue out, k', C', hsrc, hx', rr,
      hm', hpref, le_trans hmem hpref.size, ?_, hlo, hhi⟩
    rw [MemoryPrefix.memLoad hpref (UInt256.ofNat 96) (by decide) hm.lower hmem, hzero]

end Benchmarks.UniswapV3.Pool
