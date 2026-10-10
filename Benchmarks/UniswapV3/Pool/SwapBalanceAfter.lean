import Benchmarks.UniswapV3.Pool.SwapCallbackTrace
import Benchmarks.UniswapV3.Pool.Balance
import Benchmarks.UniswapV3.Pool.BalanceCaller
import Benchmarks.UniswapV3.Pool.SourceFrame
import Benchmarks.UniswapV3.Pool.SourceCallFrames

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def swapBalanceAfterReturn (zeroForOne : Bool) : UInt256 :=
  if zeroForOne then ⟨4766⟩ else ⟨5068⟩

def swapBalanceAfterName (zeroForOne : Bool) : Ident :=
  if zeroForOne then "__c25" else "__c30"

def swapBalanceAfterFrame (frame : Frame) (zeroForOne : Bool) (value : UInt256) : Frame :=
  resumeAfterInternalCall frame (swapBalanceAfterName zeroForOne)
    (some [.int (Int.ofNat value.toNat)])

theorem swapBalanceAfterFrame_parts (frame : Frame) (zeroForOne : Bool) (value : UInt256) :
    (swapBalanceAfterFrame frame zeroForOne value).contract = frame.contract ∧
    (swapBalanceAfterFrame frame zeroForOne value).immutables = frame.immutables := ⟨rfl, rfl⟩

theorem swapBalanceAfterFrame_get (frame : Frame) (zeroForOne : Bool) (value : UInt256)
    (name : Ident) (hn : name ≠ swapBalanceAfterName zeroForOne) :
    (swapBalanceAfterFrame frame zeroForOne value).locals.get? name = frame.locals.get? name :=
  resumeAfterInternalCall_get frame _ name _ hn

theorem swapBalanceAfterFrame_value (frame : Frame) (zeroForOne : Bool) (value : UInt256) :
    (swapBalanceAfterFrame frame zeroForOne value).locals.get? (swapBalanceAfterName zeroForOne) =
      some (.int (Int.ofNat value.toNat)) := Std.HashMap.getElem?_insert_self

theorem swapBalanceAfterStmt_eq (zeroForOne : Bool) :
    (swapPaymentBody zeroForOne)[5]! =
      .internalCall (if !zeroForOne then "balance1" else "balance0") []
        (swapBalanceAfterName zeroForOne) := by cases zeroForOne <;> rfl

theorem swapBalanceAfterEntryX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw junk0 junk1 junk2 junk3 : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (zeroForOne : Bool)
    (rd : RD (deployedRuntime v) ee g s0 (swapCallbackExit zeroForOne)
      (junk0 :: junk1 :: junk2 :: junk3 :: R) mem aw rdata σ k C)
    (hov : R.length + 4 ≤ 1024) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 (balanceEntry (!zeroForOne))
      (swapBalanceAfterReturn zeroForOne :: R) mem aw rdata σ k' C' := by
  cases zeroForOne
  · exact ⟨_, _, uniswapV3Pool_block_5056 (immWords := wordsOf (immStore v)) hov
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; native_decide) rd⟩
  · exact ⟨_, _, uniswapV3Pool_block_4754 (immWords := wordsOf (immStore v)) hov
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; native_decide) rd⟩

theorem swapBalanceAfterX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw free junk0 junk1 junk2 junk3 : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (zeroForOne : Bool) (frame : Frame) (evm : EVM.State)
    (rd : RD (deployedRuntime v) ee g s0 (swapCallbackExit zeroForOne)
      (junk0 :: junk1 :: junk2 :: junk3 :: R) mem aw rdata σ k C)
    (hsource : SourceState s0 ee σ evm) (hf : frame.contract = contract)
    (hi : frame.immutables = immStore v)
    (hm : HeapMemory mem aw free) (hmem : 128 ≤ mem.size)
    (hzero : memLoad (UInt256.ofNat 96) mem = ⟨0⟩)
    (hb : free.toNat + 2 ^ 138 + 163 ≤ 2 ^ 200) (hov : R.length + 18 ≤ 1024) :
    (ExecStmt config frame evm (swapPaymentBody zeroForOne)[5]! .reverted ∧
      RDrev (deployedRuntime v) g s0) ∨
    ∃ evm' σ' out mem' aw' next value k' C', SourceState s0 ee σ' evm' ∧
      ExecStmt config frame evm (swapPaymentBody zeroForOne)[5]!
        (.ok (swapBalanceAfterFrame frame zeroForOne value) evm') ∧
      RD (deployedRuntime v) ee g s0 (swapBalanceAfterReturn zeroForOne)
        (value :: R) mem' aw' out σ' k' C' ∧
      HeapMemory mem' aw' next ∧ MemoryPrefix mem mem' free.toNat ∧
      128 ≤ mem'.size ∧ memLoad (UInt256.ofNat 96) mem' = ⟨0⟩ ∧
      free.toNat ≤ next.toNat ∧ next.toNat ≤ free.toNat + 2 ^ 138 + 131 := by
  obtain ⟨k1, C1, r1⟩ := swapBalanceAfterEntryX (v := v) zeroForOne rd (by omega)
  have hret : (D_J (deployedRuntime v) 0).contains (swapBalanceAfterReturn zeroForOne) = true := by
    rw [uniswapV3PoolPatchedValidJumps v]; cases zeroForOne <;> native_decide
  rcases balanceGrowingX (v := v) (!zeroForOne) r1 hsource hm hmem hzero hb hret
      hov with
    ⟨rr, hex⟩ | ⟨evm', σ', out, mem', aw', next, k', C', hsrc, hex, rr, hm', hpref, hlo, hhi⟩
  · have hx := poolBalanceReverts v frame.locals (swapBalanceAfterName zeroForOne) evm
      (!zeroForOne) hex
    rw [← frame_eq_of_parts hf hi, ← swapBalanceAfterStmt_eq] at hx
    exact Or.inl ⟨hx, rr⟩
  · have hx := poolBalanceReturns v frame.locals (swapBalanceAfterName zeroForOne) evm evm'
      (!zeroForOne) (balanceValue out) _ hex
    have hx' : ExecStmt config frame evm (swapPaymentBody zeroForOne)[5]!
        (.ok (swapBalanceAfterFrame frame zeroForOne (balanceValue out)) evm') := by
      rw [swapBalanceAfterStmt_eq, frame_eq_of_parts hf hi]
      exact hx
    refine Or.inr ⟨evm', σ', out, mem', aw', next, balanceValue out, k', C', hsrc, hx', rr,
      hm', hpref, le_trans hmem hpref.size, ?_, hlo, hhi⟩
    rw [MemoryPrefix.memLoad hpref (UInt256.ofNat 96) (by decide) hm.lower hmem, hzero]

end Benchmarks.UniswapV3.Pool
