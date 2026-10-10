import Benchmarks.UniswapV3.Pool.MintModifyTrace
import Benchmarks.UniswapV3.Pool.MintBeforeBalances
import Benchmarks.UniswapV3.Pool.WordArrayFreshMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem mintBeforeCallbackX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {len start : UInt256} {rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (a : MintArgs) (evm : EVM.State)
    (hs : SourceState s0 ee σ evm)
    (rd : RD (deployedRuntime v) ee g s0 ⟨5805⟩
      (⟨0⟩ :: ⟨0⟩ :: len :: start :: a.amount :: EVM.wordOfInt a.upper ::
        EVM.wordOfInt a.lower :: EVM.word a.recipient.val :: R)
      solcFreePtrMem ⟨3⟩ rdata σ k C)
    (ha : a.Fits) (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : slot0FieldWord 30 1 evm.accountMap evm.executionEnv ≠ ⟨0⟩)
    (hperm : ee.perm = true) (hov : R.length + 60 ≤ 1024) :
    (ExecTransitionBody config contract evm (mintLocals a) mintTransition.body .reverted (immStore v) ∧
      (RDrev (deployedRuntime v) g s0 ∨ RDinvalid (deployedRuntime v) g s0)) ∨
    (ExecTransitionBody config contract evm (mintLocals a) mintTransition.body
        .staticViolation (immStore v) ∧ RDstatic (deployedRuntime v) g s0) ∨
    (∃ (evm' : EVM.State) (σ' : AccountMap) (out mem' : ByteArray)
      (aw' free amount0 amount1 before0 before1 : UInt256) (locals' : Store) (k' C' : Nat),
      ExecBlock config (mintFrame v a) evm (mintTransition.body.take 16)
        (.ok {contract := contract, locals := locals', immutables := immStore v} evm') ∧
      SourceState s0 ee σ' evm' ∧ MintCallValues locals' a amount0 amount1 before0 before1 ∧
      RD (deployedRuntime v) ee g s0 ⟨5966⟩
        (before1 :: before0 :: amount1 :: amount0 :: amount1 :: amount0 :: len :: start ::
          a.amount :: EVM.wordOfInt a.upper :: EVM.wordOfInt a.lower :: EVM.word a.recipient.val :: R)
        mem' aw' out σ' k' C' ∧ HeapMemory mem' aw' free ∧ 128 ≤ mem'.size ∧
      memLoad (UInt256.ofNat 96) mem' = ⟨0⟩ ∧ free.toNat ≤ 2 ^ 140) := by
  rcases mintModifyX (v := v) a evm hs rd ha freshHeapMemory (by decide) hwv hunlocked
      hperm hov with hbad | hstatic |
      ⟨evm1, a0, a1, mem1, free1, aw1, σ1, k1, C1, hsrc, hs1, r1, hm1, hp1, hmem1⟩
  · exact Or.inl hbad
  · exact Or.inr (Or.inl hstatic)
  have hsizeParams : 128 ≤
      (wordArrayAllocMem solcFreePtrMem ⟨128⟩ (mintModifyArgs a).words).size := by
    rw [wordArrayAllocMem_size _ _ _ (by decide) (by intro h; cases h), solcFreePtrMem_size]
    change 128 ≤ max 96 (128 + 32 * 4)
    decide
  have hsize1 := le_trans hsizeParams hmem1.size
  have hzero1 : memLoad (UInt256.ofNat 96) mem1 = ⟨0⟩ := by
    rw [MemoryPrefix.memLoad hmem1 (UInt256.ofNat 96) (by decide) (by decide) hsizeParams]
    exact wordArrayAllocMem_fresh_zero _ (by intro h; cases h)
  have hpre : ExecBlock config (mintFrame v a) evm (mintTransition.body.take 14)
      (.ok (mintBalancesInitFrame v a a0 a1) evm1) := by
    change ExecBlock config _ _ (mintTransition.body.take 8 ++
      (mintTransition.body.drop 8).take 4 ++ (mintTransition.body.drop 12).take 2) _
    exact execBlock_append_ok (execBlock_append_ok hsrc (mintAmountsSource v a a0 a1 evm1))
      (mintBalancesInitSource v a a0 a1 evm1)
  rcases mintBeforeBalancesX (v := v) a (mintBalancesInitFrame v a a0 a1).locals hs1 r1
      (mintCallValues_initial v a a0 a1) hm1 hsize1 hzero1
      (by change free1.toNat ≤ 128 + 1338 at hp1; omega)
      (by change R.length + 6 + 24 ≤ 1024; omega) with ⟨hbad, rr⟩ |
      ⟨evm2, σ2, out2, mem2, aw2, free2, locals2, b0, b1, k2, C2,
        hs2, hsrc2, hv2, r2, hm2, hsize2, hzero2, hp2⟩
  · refine Or.inl ⟨?_, Or.inl rr⟩
    apply ExecFuncBody.execBlockRevert
    rw [← List.take_append_drop 14 mintTransition.body]
    apply execBlock_append_ok hpre
    rw [← List.take_append_drop 2 (mintTransition.body.drop 14)]
    exact execBlockAppendReverted hbad
  · refine Or.inr (Or.inr ⟨evm2, σ2, out2, mem2, aw2, free2, EVM.wordOfInt a0,
      EVM.wordOfInt a1, b0, b1, locals2, k2, C2, ?_, hs2, hv2, r2, hm2, hsize2, hzero2, ?_⟩)
    · change ExecBlock config _ _ (mintTransition.body.take 14 ++
        (mintTransition.body.drop 14).take 2) _
      exact execBlock_append_ok hpre hsrc2
    · change free1.toNat ≤ 128 + 1338 at hp1
      omega

end Benchmarks.UniswapV3.Pool
