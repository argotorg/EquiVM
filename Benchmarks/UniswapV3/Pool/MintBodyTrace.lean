import Benchmarks.UniswapV3.Pool.MintBeforeCallbackTrace
import Benchmarks.UniswapV3.Pool.MintCallback
import Benchmarks.UniswapV3.Pool.MintRepaymentTrace
import Benchmarks.UniswapV3.Pool.MintFinishTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem mintBodyX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {len start : UInt256} {rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (a : MintArgs) (evm : EVM.State)
    (hs : SourceState s0 ee σ evm)
    (rd : RD (deployedRuntime v) ee g s0 ⟨5805⟩
      (⟨0⟩ :: ⟨0⟩ :: len :: start :: a.amount :: EVM.wordOfInt a.upper ::
        EVM.wordOfInt a.lower :: EVM.word a.recipient.val :: ⟨621⟩ :: R)
      solcFreePtrMem ⟨3⟩ rdata σ k C)
    (ha : a.Fits) (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : slot0FieldWord 30 1 evm.accountMap evm.executionEnv ≠ ⟨0⟩)
    (hperm : ee.perm = true)
    (hd : a.data = ee.calldata.extract start.toNat (start.toNat + len.toNat))
    (hc : start.toNat + len.toNat ≤ ee.calldata.size) (hl : len.toNat ≤ 2 ^ 32)
    (hov : R.length + 61 ≤ 1024) :
    (ExecTransitionBody config contract evm (mintLocals a) mintTransition.body .reverted (immStore v) ∧
      (RDrev (deployedRuntime v) g s0 ∨ RDinvalid (deployedRuntime v) g s0)) ∨
    (ExecTransitionBody config contract evm (mintLocals a) mintTransition.body
        .staticViolation (immStore v) ∧ RDstatic (deployedRuntime v) g s0) ∨
    (∃ (frame : Frame) (evm' : EVM.State) (amount0 amount1 : UInt256),
      ExecTransitionBody config contract evm (mintLocals a) mintTransition.body
        (.returned frame evm' (some [.int (Int.ofNat amount0.toNat), .int (Int.ofNat amount1.toNat)]))
        (immStore v) ∧ RDret (deployedRuntime v) g s0 evm'.accountMap
          (amount0.toByteArray ++ amount1.toByteArray)) := by
  rcases mintBeforeCallbackX (v := v) a evm hs rd ha hwv hunlocked hperm
      (by simpa only [List.length_cons] using hov) with hbad | hstatic |
      ⟨evm1, σ1, out1, mem1, aw1, p1, a0, a1, b0, b1, locals1, k1, C1,
        hpre, hs1, hv1, r1, hm1, hsize1, hzero1, hp1⟩
  · exact Or.inl hbad
  · exact Or.inr (Or.inl hstatic)
  let f1 : Frame := {contract := contract, locals := locals1, immutables := immStore v}
  rcases mintCallbackX (v := v) (frame := f1) r1 hs1 hperm hm1 hv1.core.amount0 hv1.core.amount1
      (by rw [← hd]; exact hv1.core.data) hc hl (by omega)
      (by change R.length + 5 + 22 ≤ 1024; omega) with ⟨rr, hbad⟩ |
      ⟨evm2, σ2, out2, aw2, k2, C2, hs2, hcallback, r2, hm2, hmem2⟩
  · refine Or.inl ⟨?_, Or.inl rr⟩
    apply ExecFuncBody.execBlockRevert
    rw [← List.take_append_drop 16 mintTransition.body]
    apply execBlock_append_ok hpre
    rw [← List.take_append_drop 3 (mintTransition.body.drop 16)]
    exact execBlockAppendReverted hbad
  let f2 := mintCallbackDoneFrame f1 ee.source
  have hv2 : MintCallValues f2.locals a a0 a1 b0 b1 := hv1.callback ee.source
  have hpre19 : ExecBlock config (mintFrame v a) evm (mintTransition.body.take 19)
      (.ok f2 evm2) := by
    change ExecBlock config _ _ (mintTransition.body.take 16 ++
      (mintTransition.body.drop 16).take 3) _
    exact execBlock_append_ok hpre hcallback
  have hsize2 := le_trans hsize1 hmem2.size
  have hzero2 : memLoad (UInt256.ofNat 96)
      (mintCallbackMem mem1 p1 a0 a1 ee.calldata start len) = ⟨0⟩ := by
    rw [MemoryPrefix.memLoad hmem2 (UInt256.ofNat 96) (by decide) hm1.lower hsize1, hzero1]
  rcases mintRepaymentX (v := v) a f2.locals hs2 r2 hv2 hm2 hsize2 hzero2 (by omega)
      (by change R.length + 7 + 24 ≤ 1024; omega) with ⟨hbad, rr⟩ |
      ⟨evm3, σ3, out3, mem3, aw3, p3, locals3, k3, C3, hs3, hrepay, hv3, r3, hm3, hp3⟩
  · refine Or.inl ⟨?_, Or.inl rr⟩
    apply ExecFuncBody.execBlockRevert
    rw [← List.take_append_drop 19 mintTransition.body]
    apply execBlock_append_ok hpre19
    rw [← List.take_append_drop 2 (mintTransition.body.drop 19)]
    exact execBlockAppendReverted hbad
  have rfinal := mintFinishX (v := v) r3 hs3 hperm hm3 (by omega) (by omega)
  refine Or.inr (Or.inr
    ⟨{contract := contract, locals := locals3, immutables := immStore v},
      storeSlot0Unlocked evm3 true, a0, a1, ?_, rfinal⟩)
  apply ExecFuncBody.execBlockRet
  have hpre21 : ExecBlock config (mintFrame v a) evm (mintTransition.body.take 21)
      (.ok {contract := contract, locals := locals3, immutables := immStore v} evm3) := by
    change ExecBlock config _ _ (mintTransition.body.take 19 ++
      (mintTransition.body.drop 19).take 2) _
    exact execBlock_append_ok hpre19 hrepay
  rw [← List.take_append_drop 21 mintTransition.body]
  exact execBlock_append_ok hpre21 (mintFinishSource v a locals3 a0 a1 evm3 hv3.core)

end Benchmarks.UniswapV3.Pool
