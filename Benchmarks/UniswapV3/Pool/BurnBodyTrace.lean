import Benchmarks.UniswapV3.Pool.BurnModifyTrace
import Benchmarks.UniswapV3.Pool.BurnAmountsTrace
import Benchmarks.UniswapV3.Pool.BurnOwedTrace
import Benchmarks.UniswapV3.Pool.BurnFinishTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem burnBodyX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (a : BurnArgs) (evm : EVM.State)
    (hs : SourceState s0 ee σ evm)
    (rd : RD (deployedRuntime v) ee g s0 ⟨9648⟩
      (⟨0⟩ :: ⟨0⟩ :: a.amount :: EVM.wordOfInt a.upper :: EVM.wordOfInt a.lower :: ⟨621⟩ :: R)
      mem aw rdata σ k C)
    (ha : a.Fits) (hm : HeapMemory mem aw p) (hb : p.toNat + 1434 ≤ 2 ^ 200)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : slot0FieldWord 30 1 evm.accountMap evm.executionEnv ≠ ⟨0⟩)
    (hperm : ee.perm = true) (hov : R.length + 59 ≤ 1024) :
    (ExecTransitionBody config contract evm (burnLocals a) burnTransition.body .reverted (immStore v) ∧
      (RDrev (deployedRuntime v) g s0 ∨ RDinvalid (deployedRuntime v) g s0)) ∨
    (ExecTransitionBody config contract evm (burnLocals a) burnTransition.body
        .staticViolation (immStore v) ∧ RDstatic (deployedRuntime v) g s0) ∨
    (∃ (frame : Frame) (evm' : EVM.State) (amount0 amount1 : UInt256),
      ExecTransitionBody config contract evm (burnLocals a) burnTransition.body
        (.returned frame evm' (some [.int (Int.ofNat amount0.toNat), .int (Int.ofNat amount1.toNat)]))
        (immStore v) ∧ RDret (deployedRuntime v) g s0 evm'.accountMap
          (amount0.toByteArray ++ amount1.toByteArray)) := by
  rcases burnModifyX (v := v) a evm hs rd ha hm (by omega) hwv hunlocked hperm
      (by change R.length + 1 + 58 ≤ 1024; omega) with
    ⟨hsrc, rr⟩ | ⟨hsrc, rr⟩ |
    ⟨evm1, a0, a1, mem1, p1, aw1, σ1, k1, C1, hpre, hs1, r1, hm1, hp1⟩
  · exact Or.inl ⟨hsrc, rr⟩
  · exact Or.inr (Or.inl ⟨hsrc, rr⟩)
  · obtain ⟨k2, C2, r2⟩ := burnAmountsX (v := v) a0 a1 r1
      (by change R.length + 4 + 8 ≤ 1024; omega)
    obtain ⟨σ3, k3, C3, hs3, r3⟩ := burnOwedX (v := v)
      (modifyPositionKey (burnModifyArgs a evm)) a0 a1 evm1 hs1 r2 hperm
      (by change R.length + 4 + 12 ≤ 1024; omega)
    have rfinal := burnFinishX (v := v) r3 hs3 hperm ha.2.2 hm1 (by omega) (by omega)
    refine Or.inr (Or.inr
      ⟨burnFinalFrame v a (modifyPositionKey (burnModifyArgs a evm)) a0 a1 evm1,
        _, burnAmount a0, burnAmount a1, ?_, rfinal⟩)
    apply ExecFuncBody.execBlockRet
    have hpre12 : ExecBlock config (burnFrame v a) evm (burnTransition.body.take 12)
        (.ok (burnAmountsFrame v a (modifyPositionKey (burnModifyArgs a evm)) a0 a1) evm1) := by
      change ExecBlock config _ _ (burnTransition.body.take 7 ++
        (burnTransition.body.drop 7 |>.take 5)) _
      exact execBlock_append_ok hpre
        (burnAmountsSource v a (modifyPositionKey (burnModifyArgs a evm)) a0 a1 evm1)
    rw [← List.take_append_drop 12 burnTransition.body]
    apply execBlock_append_ok hpre12
    exact ExecBlock.consNormal
      (burnOwedChoiceSource v a (modifyPositionKey (burnModifyArgs a evm)) a0 a1 evm1)
      (burnFinishSource v a (modifyPositionKey (burnModifyArgs a evm)) a0 a1 evm1)

end Benchmarks.UniswapV3.Pool
