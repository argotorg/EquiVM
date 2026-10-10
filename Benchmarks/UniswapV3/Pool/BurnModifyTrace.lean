import Benchmarks.UniswapV3.Pool.BurnModifyEntryTrace
import Benchmarks.UniswapV3.Pool.BurnAmountsSource
import Benchmarks.UniswapV3.Pool.ModifyPositionInternal

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem burnModifyX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (a : BurnArgs) (evm : EVM.State)
    (hs : SourceState s0 ee σ evm)
    (rd : RD (deployedRuntime v) ee g s0 ⟨9648⟩
      (⟨0⟩ :: ⟨0⟩ :: a.amount :: EVM.wordOfInt a.upper :: EVM.wordOfInt a.lower :: R)
      mem aw rdata σ k C)
    (ha : a.Fits) (hm : HeapMemory mem aw p) (hb : p.toNat + 1338 ≤ 2 ^ 200)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : slot0FieldWord 30 1 evm.accountMap evm.executionEnv ≠ ⟨0⟩)
    (hperm : ee.perm = true) (hov : R.length + 58 ≤ 1024) :
    (ExecTransitionBody config contract evm (burnLocals a) burnTransition.body .reverted (immStore v) ∧
      (RDrev (deployedRuntime v) g s0 ∨ RDinvalid (deployedRuntime v) g s0)) ∨
    (ExecTransitionBody config contract evm (burnLocals a) burnTransition.body
        .staticViolation (immStore v) ∧ RDstatic (deployedRuntime v) g s0) ∨
    (∃ evm' a0 a1 mem' free aw' σ' k' C',
      ExecBlock config (burnFrame v a) evm (burnTransition.body.take 7)
        (.ok (burnResultFrame v a (modifyPositionKey (burnModifyArgs a evm)) a0 a1) evm') ∧
      SourceState s0 ee σ' evm' ∧
      RD (deployedRuntime v) ee g s0 ⟨9737⟩
        (EVM.wordOfInt a1 :: EVM.wordOfInt a0 ::
          solcMappingSlot ⟨7⟩ (modifyPositionKey (burnModifyArgs a evm)) ::
          ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: a.amount ::
          EVM.wordOfInt a.upper :: EVM.wordOfInt a.lower :: R)
        mem' aw' rdata σ' k' C' ∧ HeapMemory mem' aw' free ∧ free.toNat ≤ p.toNat + 1338) := by
  have hlock := burnLockPrefix v a evm hwv hunlocked
  rcases burnModifyEntryX (v := v) a evm hs rd ha hm (by omega) hperm (by omega) with
    ⟨hc, rr⟩ | ⟨hc, σ1, aw1, k1, C1, hs1, r1, hm1, hparams⟩
  · refine Or.inl ⟨?_, Or.inl rr⟩
    apply ExecFuncBody.execBlockRevert
    rw [← List.take_append_drop 5 burnTransition.body]
    exact execBlock_append_ok hlock (ExecBlock.consRevert hc)
  · have hp : (p + UInt256.ofNat 128).toNat = p.toNat + 128 :=
      uadd_word_ofNat_toNat p 128 (by change _ < 2 ^ 256; omega)
    have hpre : ExecBlock config (burnFrame v a) evm (burnTransition.body.take 6)
        (.ok (burnCastFrame v a) (storeSlot0Unlocked evm false)) := by
      change ExecBlock config _ _ (burnTransition.body.take 5 ++
        [.internalCall "SafeCast_toInt128" burnCastExprs "__c0"]) _
      exact execBlock_append_ok hlock (ExecBlock.consNormal hc ExecBlock.nil)
    have he : evalExprs? config (burnCastFrame v a) (storeSlot0Unlocked evm false)
        burnModifyExprs = .ok [(burnModifyArgs a evm).value] := by
      simpa only [burnModifyArgs_locked] using evalBurnModifyExprs v a (storeSlot0Unlocked evm false)
    rcases modifyPositionInternalX (v := v) (burnModifyArgs a evm) (burnCastFrame v a)
        (storeSlot0Unlocked evm false) burnModifyExprs "__c1" rfl he hs1 r1
        (burnModifyArgs_fits a evm ha) hm1 hparams (by have h := hm.lower; omega)
        (by rw [hp]) (by rw [hp]; omega) hperm
        (by rw [uniswapV3PoolPatchedValidJumps v]; jump_dest)
        (by change R.length + 8 + 50 ≤ 1024; omega) with
      ⟨hcall, rr⟩ | ⟨hcall, rr⟩ |
      ⟨evm', a0, a1, mem', free, aw', σ', k', C', hcall, ha0, ha1, hs', rr, hm', hfree, hmem⟩
    · refine Or.inl ⟨?_, rr⟩
      apply ExecFuncBody.execBlockRevert
      rw [← List.take_append_drop 6 burnTransition.body]
      exact execBlock_append_ok hpre (ExecBlock.consRevert hcall)
    · refine Or.inr (Or.inl ⟨?_, rr⟩)
      apply ExecFuncBody.execBlockStatic
      rw [← List.take_append_drop 6 burnTransition.body]
      exact execBlock_append_ok hpre (ExecBlock.consStatic hcall)
    · refine Or.inr (Or.inr ⟨evm', a0, a1, mem', free, aw', σ', k', C', ?_, hs', rr, hm', ?_⟩)
      · change ExecBlock config _ _ (burnTransition.body.take 6 ++
          [.internalCall "_modifyPosition" burnModifyExprs "__c1"]) _
        exact execBlock_append_ok hpre (ExecBlock.consNormal hcall ExecBlock.nil)
      · rw [hp] at hfree
        omega

end Benchmarks.UniswapV3.Pool
