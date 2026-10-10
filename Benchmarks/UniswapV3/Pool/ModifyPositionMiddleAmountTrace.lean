import Benchmarks.UniswapV3.Pool.ModifyPositionMiddleSqrtSource
import Benchmarks.UniswapV3.Pool.ModifyPositionMiddleAmountEntryTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000
attribute [local irreducible] modifyPositionUpdatedState

def modifyPositionMiddleAmountReturn (second : Bool) : UInt256 :=
  if second then ⟨16705⟩ else ⟨16675⟩

noncomputable def modifyPositionMiddleOldAmount0 (a : ModifyPositionArgs) (evm : EVM.State)
    (second : Bool) : UInt256 :=
  if second then EVM.wordOfInt (signedAmountDeltaResult false (modifyPositionMiddleAmountArgs a evm false))
    else ⟨0⟩

noncomputable def modifyPositionMiddleSqrtWords (v : UniswapV3PoolImmutables) (a : ModifyPositionArgs)
    (evm : EVM.State) (p q key : UInt256) (second : Bool) : List UInt256 :=
  (if second then [EVM.wordOfInt a.lower, ⟨16693⟩]
    else [EVM.wordOfInt a.upper, ⟨16665⟩, slot0FieldWord 0 20 evm.accountMap evm.executionEnv]) ++
    [modifyPositionMiddleAmountReturn second, modifyPositionMiddleLiquidity v a evm, p, ⟨0⟩,
      modifyPositionMiddleOldAmount0 a evm second, key, q]

theorem modifyPositionMiddleAmountCallEntryX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p q key free : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (a : ModifyPositionArgs) (evm : EVM.State)
    (second : Bool)
    (rd : RD (deployedRuntime v) ee g s0 ⟨11629⟩
      (modifyPositionMiddleSqrtWords v a evm p q key second ++ R) mem aw rdata σ k C)
    (ha : a.Fits) (ht : validTicks a.lower a.upper)
    (hm : HeapMemory mem aw free) (hq : ModifyPositionParamsMemory mem q a)
    (hp : Slot0Memory mem p evm.accountMap evm.executionEnv)
    (hpb : p.toNat + 224 ≤ 2 ^ 200) (hqb : q.toNat + 128 ≤ 2 ^ 200)
    (hov : R.length + 17 ≤ 1024) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 (UInt256.ofNat (signedAmountDeltaEntry second))
      (signedAmountDeltaEntryWords (modifyPositionMiddleAmountArgs a evm second) ++
        modifyPositionMiddleAmountReturn second :: modifyPositionMiddleLiquidity v a evm ::
          p :: ⟨0⟩ :: modifyPositionMiddleOldAmount0 a evm second :: key :: q :: R)
      mem aw' rdata σ k' C' ∧ HeapMemory mem aw' free := by
  cases second
  · simp only [modifyPositionMiddleSqrtWords, modifyPositionMiddleAmountReturn,
      modifyPositionMiddleOldAmount0, Bool.false_eq_true, if_false, List.cons_append,
      List.nil_append] at rd
    obtain ⟨k1, C1, r1⟩ := tickSqrtCanonicalX (v := v) a.upper rd
      ha.2.1.1 ha.2.1.2 (modifyPositionTickValid a ht true)
      (by rw [uniswapV3PoolPatchedValidJumps v]; jump_dest) (by evm_ov)
    obtain ⟨aw2, k2, C2, r2, hm2⟩ := modifyPositionMiddleAmount0EntryX (v := v) a r1 hm hq hqb (by omega)
    exact ⟨aw2, k2, C2, r2, hm2⟩
  · simp only [modifyPositionMiddleSqrtWords, modifyPositionMiddleAmountReturn,
      modifyPositionMiddleOldAmount0, if_true, List.cons_append, List.nil_append] at rd
    obtain ⟨k1, C1, r1⟩ := tickSqrtCanonicalX (v := v) a.lower rd
      ha.1.1 ha.1.2 (modifyPositionTickValid a ht false)
      (by rw [uniswapV3PoolPatchedValidJumps v]; jump_dest) (by evm_ov)
    obtain ⟨aw2, k2, C2, r2, hm2⟩ := modifyPositionMiddleAmount1EntryX (v := v) a evm r1 hm hq hp
      hpb hqb (by omega)
    exact ⟨aw2, k2, C2, r2, hm2⟩

theorem modifyPositionMiddleAmountX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p q key free : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (a : ModifyPositionArgs) (evm evm' : EVM.State)
    (second : Bool)
    (rd : RD (deployedRuntime v) ee g s0 ⟨11629⟩
      (modifyPositionMiddleSqrtWords v a evm p q key second ++ R) mem aw rdata σ k C)
    (ha : a.Fits) (ht : validTicks a.lower a.upper)
    (hm : HeapMemory mem aw free) (hq : ModifyPositionParamsMemory mem q a)
    (hp : Slot0Memory mem p evm.accountMap evm.executionEnv)
    (hpb : p.toNat + 224 ≤ 2 ^ 200) (hqb : q.toNat + 128 ≤ 2 ^ 200)
    (hov : R.length + 42 ≤ 1024) :
    (ExecBlock config (modifyPositionMiddleBeforeSqrtFrame v a evm second) evm'
      (modifyPositionMiddleAmountBody second) .reverted ∧ RDrev (deployedRuntime v) g s0) ∨
    (ExecBlock config (modifyPositionMiddleBeforeSqrtFrame v a evm second) evm'
      (modifyPositionMiddleAmountBody second)
      (.ok (modifyPositionMiddleAssignedFrame v a evm second) evm') ∧
      signedAmountDeltaValid second (modifyPositionMiddleAmountArgs a evm second) ∧
      ∃ aw' k' C', RD (deployedRuntime v) ee g s0 (modifyPositionMiddleAmountReturn second)
        (EVM.wordOfInt (signedAmountDeltaResult second (modifyPositionMiddleAmountArgs a evm second)) ::
          modifyPositionMiddleLiquidity v a evm :: p :: ⟨0⟩ ::
            modifyPositionMiddleOldAmount0 a evm second :: key :: q :: R)
        mem aw' rdata σ k' C' ∧ HeapMemory mem aw' free) := by
  obtain ⟨aw1, k1, C1, r1, hm1⟩ := modifyPositionMiddleAmountCallEntryX (v := v) a evm second rd
    ha ht hm hq hp hpb hqb (by omega)
  have hsqrt := modifyPositionMiddleSqrtSource v a evm evm' second ha ht
  rcases signedAmountDeltaInternalX (v := v) second (modifyPositionMiddleAmountArgs a evm second)
    (modifyPositionMiddleSqrtFrame v a evm second) evm' (modifyPositionMiddleAmountExprs second)
    (modifyPositionMiddleAmountName second) (modifyPositionMiddleSqrtFrame_eq v a evm second)
    (evalModifyPositionMiddleAmountExprs v a evm evm' second) r1
    (modifyPositionMiddleAmountArgs_fits a evm second ha)
    (by cases second <;> rw [uniswapV3PoolPatchedValidJumps v] <;> jump_dest) (by evm_ov) with
      ⟨hcall, rr⟩ | ⟨hcall, hv, kr, Cr, rr⟩
  · exact Or.inl ⟨ExecBlock.consNormal hsqrt (ExecBlock.consRevert hcall), rr⟩
  · have hframe : resumeAfterInternalCall (modifyPositionMiddleSqrtFrame v a evm second)
        (modifyPositionMiddleAmountName second)
        (some [.int (signedAmountDeltaResult second (modifyPositionMiddleAmountArgs a evm second))]) =
        modifyPositionMiddleAmountFrame v a evm second := by cases second <;> rfl
    rw [hframe] at hcall
    exact Or.inr ⟨ExecBlock.consNormal hsqrt (ExecBlock.consNormal hcall
      (ExecBlock.consNormal (modifyPositionMiddleAssignAmountSource v a evm evm' second) ExecBlock.nil)),
      hv, aw1, kr, Cr, rr, hm1⟩

end Benchmarks.UniswapV3.Pool
