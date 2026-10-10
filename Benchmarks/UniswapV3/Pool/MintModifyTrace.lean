import Benchmarks.UniswapV3.Pool.MintModifyEntryTrace
import Benchmarks.UniswapV3.Pool.MintAmountTrace
import Benchmarks.UniswapV3.Pool.MintAmountsSource
import Benchmarks.UniswapV3.Pool.ModifyPositionInternal

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem mintModifyX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p len start : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (a : MintArgs) (evm : EVM.State)
    (hs : SourceState s0 ee σ evm)
    (rd : RD (deployedRuntime v) ee g s0 ⟨5805⟩
      (⟨0⟩ :: ⟨0⟩ :: len :: start :: a.amount :: EVM.wordOfInt a.upper ::
        EVM.wordOfInt a.lower :: EVM.word a.recipient.val :: R) mem aw rdata σ k C)
    (ha : a.Fits) (hm : HeapMemory mem aw p) (hb : p.toNat + 1338 ≤ 2 ^ 200)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : slot0FieldWord 30 1 evm.accountMap evm.executionEnv ≠ ⟨0⟩)
    (hperm : ee.perm = true) (hov : R.length + 60 ≤ 1024) :
    (ExecTransitionBody config contract evm (mintLocals a) mintTransition.body .reverted (immStore v) ∧
      (RDrev (deployedRuntime v) g s0 ∨ RDinvalid (deployedRuntime v) g s0)) ∨
    (ExecTransitionBody config contract evm (mintLocals a) mintTransition.body
        .staticViolation (immStore v) ∧ RDstatic (deployedRuntime v) g s0) ∨
    (∃ evm' a0 a1 mem' free aw' σ' k' C',
      ExecBlock config (mintFrame v a) evm (mintTransition.body.take 8)
        (.ok (mintResultFrame v a a0 a1) evm') ∧ SourceState s0 ee σ' evm' ∧
      RD (deployedRuntime v) ee g s0 ⟨5915⟩
        (EVM.wordOfInt a1 :: EVM.wordOfInt a0 ::
          solcMappingSlot ⟨7⟩ (modifyPositionKey (mintModifyArgs a)) ::
          ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: len :: start :: a.amount :: EVM.wordOfInt a.upper ::
          EVM.wordOfInt a.lower :: EVM.word a.recipient.val :: R)
        mem' aw' rdata σ' k' C' ∧ HeapMemory mem' aw' free ∧
      free.toNat ≤ p.toNat + 1338 ∧
      MemoryPrefix (wordArrayAllocMem mem p (mintModifyArgs a).words) mem'
        (p + UInt256.ofNat 128).toNat) := by
  rcases mintLockAmountX (v := v) evm hs rd ha.2.2 hperm (by evm_ov) with
    ⟨rr, hz⟩ | ⟨hpos, k0, C0, r0⟩
  · exact Or.inl ⟨mintRevertsZero v a evm hwv hunlocked hz, Or.inl rr⟩
  have hprefix := mintAmountPrefix v a evm hwv hunlocked hpos
  have hs0 : SourceState s0 ee (storeSlot0Unlocked evm false).accountMap
      (storeSlot0Unlocked evm false) :=
    ⟨(storeSlot0Unlocked_originalAccounts evm false).trans hs.world,
      (storeSlot0Unlocked_executionEnv evm false).trans hs.env, rfl⟩
  rcases mintModifyEntryX (v := v) a (storeSlot0Unlocked evm false) r0 ha hm (by omega)
      (by omega) with ⟨hc, rr⟩ | ⟨hv, hc, aw1, k1, C1, r1, hm1, hparams⟩
  · refine Or.inl ⟨?_, Or.inl rr⟩
    apply ExecFuncBody.execBlockRevert
    rw [← List.take_append_drop 6 mintTransition.body]
    exact execBlock_append_ok hprefix (ExecBlock.consRevert hc)
  have hp : (p + UInt256.ofNat 128).toNat = p.toNat + 128 :=
    uadd_word_ofNat_toNat p 128 (by change _ < 2 ^ 256; omega)
  have hpre : ExecBlock config (mintFrame v a) evm (mintTransition.body.take 7)
      (.ok (mintCastFrame v a) (storeSlot0Unlocked evm false)) := by
    change ExecBlock config _ _ (mintTransition.body.take 6 ++
      [.internalCall "SafeCast_toInt128" mintCastExprs "__c0"]) _
    exact execBlock_append_ok hprefix (ExecBlock.consNormal hc ExecBlock.nil)
  rcases modifyPositionInternalX (v := v) (mintModifyArgs a) (mintCastFrame v a)
      (storeSlot0Unlocked evm false) mintModifyExprs "__c1" rfl
      (evalMintModifyExprs v a _) hs0 r1 (mintModifyArgs_fits a ha hv) hm1 hparams
      (by have h := hm.lower; omega) (by rw [hp]) (by rw [hp]; omega) hperm
      (by rw [uniswapV3PoolPatchedValidJumps v]; jump_dest)
      (by change R.length + 10 + 50 ≤ 1024; omega) with
    ⟨hcall, rr⟩ | ⟨hcall, rr⟩ |
    ⟨evm', a0, a1, mem', free, aw', σ', k', C', hcall, ha0, ha1, hs', rr, hm', hfree, hmem⟩
  · refine Or.inl ⟨?_, rr⟩
    apply ExecFuncBody.execBlockRevert
    rw [← List.take_append_drop 7 mintTransition.body]
    exact execBlock_append_ok hpre (ExecBlock.consRevert hcall)
  · refine Or.inr (Or.inl ⟨?_, rr⟩)
    apply ExecFuncBody.execBlockStatic
    rw [← List.take_append_drop 7 mintTransition.body]
    exact execBlock_append_ok hpre (ExecBlock.consStatic hcall)
  · refine Or.inr (Or.inr ⟨evm', a0, a1, mem', free, aw', σ', k', C',
      ?_, hs', rr, hm', ?_, ?_⟩)
    · change ExecBlock config _ _ (mintTransition.body.take 7 ++
        [.internalCall "_modifyPosition" mintModifyExprs "__c1"]) _
      exact execBlock_append_ok hpre (ExecBlock.consNormal hcall ExecBlock.nil)
    · rw [hp] at hfree
      omega
    · exact hmem

end Benchmarks.UniswapV3.Pool
