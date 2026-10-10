import Benchmarks.UniswapV4PoolManager.EntryTrace
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_022
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_035

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables

namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 2000000

-- GENERALIZES Reasoning.Theory.evalExpr_checkedSub256_revert to arbitrary frames.
theorem checkedSubSourceUnderflow {cfg : Config} {f : Frame} {evm : EVM.State}
    {lhs rhs : Expr} {a b : UInt256}
    (ha : evalExpr? cfg f evm lhs = .ok (.int (Int.ofNat a.toNat)))
    (hb : evalExpr? cfg f evm rhs = .ok (.int (Int.ofNat b.toNat)))
    (hlt : a.toNat < b.toNat) :
    evalExpr? cfg f evm (.inRange (.uint ⟨256, by decide⟩) (.binary .sub lhs rhs)) = .revert := by
  have hneg : (Int.ofNat a.toNat - Int.ofNat b.toNat) < 0 := by
    simp only [Int.ofNat_eq_natCast]; omega
  simp only [evalExpr?, ha, hb, bind, EvalResult.bind, evalBinaryOp?, hneg,
    decide_true, Bool.true_or, if_true]

-- LIBRARY CANDIDATE: the via-IR subtraction overflow check.
theorem subGuardOk {a b : UInt256} (hle : b.toNat ≤ a.toNat) :
    UInt256.gt (UInt256.sub a b) a = ⟨0⟩ := by
  show UInt256.fromBool (decide (UInt256.sub a b > a)) = ⟨0⟩
  rw [decide_eq_false (by change ¬(UInt256.sub a b).toNat > a.toNat; rw [usub_toNat hle]; omega)]
  rfl

-- LIBRARY CANDIDATE: the via-IR subtraction overflow check.
theorem subGuardUnderflow {a b : UInt256} (hlt : a.toNat < b.toNat) :
    UInt256.gt (UInt256.sub a b) a ≠ ⟨0⟩ := by
  have hgt : UInt256.sub a b > a := by
    change (UInt256.sub a b).toNat > a.toNat
    rw [usub_toNat_underflow hlt]
    have hb := b.val.isLt
    change b.toNat < UInt256.size at hb
    omega
  change UInt256.fromBool (decide (UInt256.sub a b > a)) ≠ ⟨0⟩
  rw [decide_eq_true hgt]
  decide

-- LIBRARY CANDIDATE: the via-IR addition overflow check.
theorem addGuardOk {a b : UInt256} (hfit : a.toNat + b.toNat < UInt256.size) :
    UInt256.gt a (a + b) = ⟨0⟩ := by
  show UInt256.fromBool (decide (a > a + b)) = ⟨0⟩
  rw [decide_eq_false (by change ¬a.toNat > (a + b).toNat; rw [uadd_toNat, Nat.mod_eq_of_lt hfit]; omega)]
  rfl

-- LIBRARY CANDIDATE: the via-IR addition overflow check.
theorem addGuardOverflow {a b : UInt256} (hover : UInt256.size ≤ a.toNat + b.toNat) :
    UInt256.gt a (a + b) ≠ ⟨0⟩ := by
  have h := u256_add_overflow_lt a b hover
  change UInt256.gt a (a + b) = ⟨1⟩ at h
  rw [h]
  decide

theorem checkedSubPass {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {a b ret : UInt256} {R : List UInt256} (v : PoolManagerImmutables)
    (hstack : R.length + 4 ≤ 1024) (hle : b.toNat ≤ a.toNat)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) I g s0 ⟨12269⟩ (a :: b :: ret :: R) mem aw rdata σ k C) :
    ∃ k' C', RD (deployedRuntime v) I g s0 ret (UInt256.sub a b :: R) mem aw rdata σ k' C' := by
  have hnext := poolManagerBlocks.poolManager_block_12269_fallthrough hstack (subGuardOk hle) h
  exact ⟨_, _, poolManagerBlocks.poolManager_block_12281 (by simp only [List.length_cons]; omega) hret hnext⟩

theorem checkedSubReverts {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {a b ret : UInt256} {R : List UInt256} (v : PoolManagerImmutables)
    (hstack : R.length + 4 ≤ 1024) (hlt : a.toNat < b.toNat)
    (h : RD (deployedRuntime v) I g s0 ⟨12269⟩ (a :: b :: ret :: R) mem aw rdata σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  have hj : (D_J (deployedRuntime v) 0).contains (UInt256.ofNat 7572) = true := by
    rw [deployedRuntime_jumps]; jump_dest
  have hnext := poolManagerBlocks.poolManager_block_12269_taken hstack (subGuardUnderflow hlt) hj h
  exact poolManagerBlocks.poolManager_block_7572
    (by simpa only [poolManagerBlocks.poolManager_block_12269_taken_stack, List.length_cons] using hstack) hnext

theorem checkedAddPass {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {a b ret : UInt256} {R : List UInt256} (v : PoolManagerImmutables)
    (hstack : R.length + 4 ≤ 1024) (hfit : a.toNat + b.toNat < UInt256.size)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) I g s0 ⟨12282⟩ (a :: b :: ret :: R) mem aw rdata σ k C) :
    ∃ k' C', RD (deployedRuntime v) I g s0 ret ((a + b) :: R) mem aw rdata σ k' C' := by
  have hnext := poolManagerBlocks.poolManager_block_12282_fallthrough hstack (addGuardOk hfit) h
  exact ⟨_, _, poolManagerBlocks.poolManager_block_12294 (by simp only [List.length_cons]; omega) hret hnext⟩

theorem checkedAddReverts {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {a b ret : UInt256} {R : List UInt256} (v : PoolManagerImmutables)
    (hstack : R.length + 4 ≤ 1024) (hover : UInt256.size ≤ a.toNat + b.toNat)
    (h : RD (deployedRuntime v) I g s0 ⟨12282⟩ (a :: b :: ret :: R) mem aw rdata σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  have hj : (D_J (deployedRuntime v) 0).contains (UInt256.ofNat 7572) = true := by
    rw [deployedRuntime_jumps]; jump_dest
  have hnext := poolManagerBlocks.poolManager_block_12282_taken hstack (addGuardOverflow hover) hj h
  exact poolManagerBlocks.poolManager_block_7572
    (by simpa only [poolManagerBlocks.poolManager_block_12282_taken_stack, List.length_cons] using hstack) hnext

end Benchmarks.UniswapV4PoolManager
