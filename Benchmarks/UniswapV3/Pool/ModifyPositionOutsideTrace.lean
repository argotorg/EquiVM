import Benchmarks.UniswapV3.Pool.ModifyPositionOutsideEntryTrace
import Benchmarks.UniswapV3.Pool.ModifyPositionOutsideSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem modifyPositionOutsideX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p q free key : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (a : ModifyPositionArgs)
    (evm evm' : EVM.State) (second : Bool)
    (rd : RD (deployedRuntime v) ee g s0 (modifyPositionOutsideEntry second)
      (p :: ⟨0⟩ :: ⟨0⟩ :: key :: q :: R) mem aw rdata σ k C)
    (ha : a.Fits) (ht : validTicks a.lower a.upper)
    (hm : HeapMemory mem aw free) (hq : ModifyPositionParamsMemory mem q a)
    (hb : q.toNat + 128 ≤ 2 ^ 200) (hov : R.length + 41 ≤ 1024) :
    (ExecBlock config (modifyPositionUpdatedFrame (immStore v) a evm) evm'
      (modifyPositionOutsideBody second) .reverted ∧ RDrev (deployedRuntime v) g s0) ∨
    (ExecBlock config (modifyPositionUpdatedFrame (immStore v) a evm) evm'
      (modifyPositionOutsideBody second)
      (.ok (modifyPositionOutsideFinalFrame (immStore v) a evm second) evm') ∧
      signedAmountDeltaValid second (modifyPositionOutsideArgs a) ∧
      ∃ aw' k' C', RD (deployedRuntime v) ee g s0 ⟨16801⟩
        (p :: (if second then EVM.wordOfInt (signedAmountDeltaResult second (modifyPositionOutsideArgs a))
          else ⟨0⟩) :: (if second then ⟨0⟩
          else EVM.wordOfInt (signedAmountDeltaResult second (modifyPositionOutsideArgs a))) ::
          key :: q :: R) mem aw' rdata σ k' C' ∧ HeapMemory mem aw' free) := by
  obtain ⟨aw1, k1, C1, r1, hm1⟩ := modifyPositionOutsideLowerEntryX (v := v) a second rd
    hm hq hb (by omega)
  obtain ⟨k2, C2, r2⟩ := tickSqrtCanonicalX (v := v) a.lower r1 ha.1.1 ha.1.2
    (modifyPositionTickValid a ht false)
    (by cases second <;> rw [uniswapV3PoolPatchedValidJumps v] <;> jump_dest) (by evm_ov)
  obtain ⟨aw3, k3, C3, r3, hm3⟩ := modifyPositionOutsideUpperEntryX (v := v) a second r2
    hm1 hq hb (by omega)
  obtain ⟨k4, C4, r4⟩ := tickSqrtCanonicalX (v := v) a.upper r3 ha.2.1.1 ha.2.1.2
    (modifyPositionTickValid a ht true)
    (by cases second <;> rw [uniswapV3PoolPatchedValidJumps v] <;> jump_dest) (by evm_ov)
  obtain ⟨aw5, k5, C5, r5, hm5⟩ := modifyPositionOutsideAmountEntryX (v := v) a second r4
    hm3 hq hb (by omega)
  have r5' : RD (deployedRuntime v) ee g s0 (UInt256.ofNat (signedAmountDeltaEntry second))
      (signedAmountDeltaEntryWords (modifyPositionOutsideArgs a) ++
        modifyPositionOutsideAmountReturn second :: p :: ⟨0⟩ :: ⟨0⟩ :: key :: q :: R)
      mem aw5 rdata σ k5 C5 := r5
  rcases signedAmountDeltaX (v := v) second (modifyPositionOutsideArgs a) r5'
    (modifyPositionOutsideArgs_fits a ha)
    (by cases second <;> rw [uniswapV3PoolPatchedValidJumps v] <;> jump_dest) (by evm_ov) with
      ⟨hbad, rr⟩ | ⟨hv, k6, C6, r6⟩
  · exact Or.inl ⟨modifyPositionOutsideReverts (immStore v) a evm evm' second ha ht hbad, rr⟩
  · obtain ⟨k7, C7, r7⟩ := modifyPositionOutsideDoneX (v := v) second r6 (by omega)
    exact Or.inr ⟨modifyPositionOutsideSource (immStore v) a evm evm' second ha ht hv,
      hv, aw5, k7, C7, r7, hm5⟩

end Benchmarks.UniswapV3.Pool
