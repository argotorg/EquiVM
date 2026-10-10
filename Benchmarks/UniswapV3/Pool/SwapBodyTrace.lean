import Benchmarks.UniswapV3.Pool.SwapReadyModel
import Benchmarks.UniswapV3.Pool.SwapLoopFinish
import Benchmarks.UniswapV3.Pool.SwapSlotTrace
import Benchmarks.UniswapV3.Pool.SwapLimitTrace
import Benchmarks.UniswapV3.Pool.SwapGuardReverts
import Benchmarks.UniswapV3.Pool.WordArrayFreshMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

set_option maxHeartbeats 2000000 in
theorem swapBodyX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {len start : UInt256} {rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (a : SwapArgs) (evm : EVM.State)
    (hs : SourceState s0 ee σ evm)
    (rd : RD (deployedRuntime v) ee g s0 ⟨2292⟩
      (swapWords a start len ++ ⟨621⟩ :: R) solcFreePtrMem ⟨3⟩ rdata σ k C)
    (ha : a.Fits) (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hd : a.data = ee.calldata.extract start.toNat (start.toNat + len.toNat))
    (hc : start.toNat + len.toNat ≤ ee.calldata.size) (hl : len.toNat ≤ 2 ^ 32)
    (hov : R.length + 67 ≤ 1024) :
    (X (g.toNat + 1) (D_J (deployedRuntime v) 0) s0 = .error .OutOfGass) ∨
    (ExecTransitionBody config contract evm (swapLocals a) swapTransition.body .reverted
        (immStore v) ∧ (RDrev (deployedRuntime v) g s0 ∨ RDinvalid (deployedRuntime v) g s0)) ∨
    (ExecTransitionBody config contract evm (swapLocals a) swapTransition.body .staticViolation
        (immStore v) ∧ RDstatic (deployedRuntime v) g s0) ∨
    ∃ (frame : Frame) (evm' : EVM.State) (amount0 amount1 : Int),
      ExecTransitionBody config contract evm (swapLocals a) swapTransition.body
        (.returned frame evm' (some [.int amount0, .int amount1])) (immStore v) ∧
      RDret (deployedRuntime v) g s0 evm'.accountMap
        ((EVM.wordOfInt amount0).toByteArray ++ (EVM.wordOfInt amount1).toByteArray) ∧
      (-(2 ^ 255 : Int) ≤ amount0 ∧ amount0 < 2 ^ 255) ∧
      (-(2 ^ 255 : Int) ≤ amount1 ∧ amount1 < 2 ^ 255) := by
  rcases swapEntryX (v := v) a rd ha (by omega) with ⟨hbad, rr⟩ |
      ⟨hself, hn, k1, C1, r1⟩
  · refine Or.inr (Or.inl ⟨?_, Or.inl rr⟩)
    by_cases hself : evm.executionEnv.codeOwner = v.original
    · have hn : a.amountSpecified = 0 := by
        rcases hbad with hbad | hbad
        · exact False.elim (hbad (by rw [← hs.env]; exact hself))
        · exact hbad
      exact swapSpecifiedReverts v a evm hwv hself hn
    · exact swapDelegateReverts v a evm hwv hself
  have hself' : evm.executionEnv.codeOwner = v.original := by rw [hs.env]; exact hself
  rcases swapSlotReadBoundedX (v := v) (limit := 768) r1 freshHeapMemory
      ⟨by decide, by decide, by decide⟩ (by decide)
      (by change R.length + 9 + 6 ≤ 1024; omega) with
    ⟨hu, rr⟩ | ⟨hu, aw2, k2, C2, r2, hm2, hslot2, hb2⟩
  · exact Or.inr (Or.inl ⟨swapLockedReverts v a evm hwv hself' hn
      (by rw [← hs.accounts, hs.env]; exact hu), Or.inl rr⟩)
  have hu' : slot0FieldWord 30 1 evm.accountMap evm.executionEnv ≠ ⟨0⟩ := by
    rw [← hs.accounts, hs.env]; exact hu
  have hprice : UInt256.land (UInt256.ofNat (2 ^ 160 - 1))
      (memLoad ⟨128⟩ (wordArrayAllocMem solcFreePtrMem ⟨128⟩ (slot0StructWords σ ee))) =
      slot0FieldWord 0 20 σ ee := by
    rw [Slot0Memory.load_price hslot2 (by decide)]
    exact slot0Price_clean σ ee
  rcases swapLimitX (v := v) a r2 ha.2 hprice
      (by change R.length + 2 + 13 ≤ 1024; omega) with ⟨hlimit, rr⟩ |
      ⟨hlimit, k3, C3, r3⟩
  · exact Or.inr (Or.inl ⟨swapLimitReverts v a evm hwv hself' hn hu'
      (by simpa only [swapLimitValid, ← hs.accounts, hs.env] using hlimit), Or.inl rr⟩)
  have hlimit' : swapLimitValid a evm := by
    simpa only [swapLimitValid, ← hs.accounts, hs.env] using hlimit
  cases hperm : ee.perm with
  | false =>
    exact Or.inr (Or.inr (Or.inl ⟨swapStatic v a evm hwv hself' hn hu' hlimit'
      (by rw [hs.env]; exact hperm), swapLockStaticX (v := v) r3 hperm
      (by change R.length + 10 + 4 ≤ 1024; omega)⟩))
  | true =>
    have hb3 := hb2.expand32 (off := ⟨128⟩) (by decide)
    have hm3 : HeapMemory _ (M aw2 ⟨128⟩ ⟨32⟩) ⟨352⟩ := {hm2 with active := hb3.active}
    obtain ⟨aw4, k4, C4, r4, hm4, hpre, hslot4, hcache4, hb4, hcover4⟩ :=
      swapReadyBoundedX (v := v) a evm r3 hs hm3 hb3 hslot2 (by decide) (by decide)
        (by decide) hperm (by omega)
    rw [swapExactInput_word a ha] at r4
    let m2 := wordArrayAllocMem solcFreePtrMem ⟨128⟩ (slot0StructWords σ ee)
    let m4 := swapInitializedMem m2 ⟨352⟩ (poolProtocolDivisor (!a.zeroForOne) σ ee) a
      (storeSlot0Unlocked evm false).accountMap σ ee
    have hstate4 : SwapStateMemory m4 ⟨544⟩ (swapStateInitial a evm) :=
      swapInitializedMem_state a hs (by decide) (by decide)
    have hcache4' : SwapCacheMemory m4 ⟨352⟩ (swapCacheInitial a evm) := by
      unfold SwapCacheMemory
      rw [swapCacheInitial_words a hs]
      exact hcache4
    have hs4 : SourceState s0 ee (storeSlot0Unlocked evm false).accountMap
        (storeSlot0Unlocked evm false) :=
      ⟨(storeSlot0Unlocked_originalAccounts evm false).trans hs.world,
        (storeSlot0Unlocked_executionEnv evm false).trans hs.env, rfl⟩
    have hslot4' : Slot0Memory m4 ⟨128⟩ evm.accountMap evm.executionEnv := by
      rw [← hs.accounts, hs.env]; exact hslot4
    have hm2size : 128 ≤ m2.size := by
      rw [wordArrayAllocMem_size _ _ _ (by decide) (by simp [slot0StructWords])]
      simp only [solcFreePtrMem_size, slot0StructWords, List.length_cons, List.length_nil]
      decide
    have hm4size : 128 ≤ m4.size := hm2size.trans hpre.size
    have hz4 : memLoad (UInt256.ofNat 96) m4 = ⟨0⟩ := by
      rw [MemoryPrefix.memLoad hpre (UInt256.ofNat 96) (by decide) (by decide) hm2size]
      exact wordArrayAllocMem_fresh_zero _ (by simp [slot0StructWords])
    have hinit := swapInitSource v a evm hwv hself' hn hu' hlimit'
    rcases swapLoopFinishX (v := v) a (swapCacheInitial a evm) (swapStateInitial a evm)
        evm (swapReadyFrame v a evm) (storeSlot0Unlocked evm false) r4 hs4 rfl rfl hperm
        (swapReadyFrame_zero v a evm)
        (by simp only [swapReadyFrame]; swap_exact_get)
        (swapReadyFrame_exact v a evm)
        (by simp only [swapReadyFrame]; swap_exact_get)
        (old0 := .int 0) (old1 := .int 0)
        (by simp only [swapReadyFrame]; swap_exact_get)
        (by simp only [swapReadyFrame]; swap_exact_get)
        (by rw [← hd]; simp only [swapReadyFrame]; swap_exact_get)
        (swapReadyFrame_cache v a evm) (swapReadyFrame_state v a evm)
        (swapReadyFrame_slot v a evm) (swapReadyFrame_limit v a evm)
        (by simp only [swapReadyFrame]; swap_exact_get)
        (by simp only [swapReadyFrame]; swap_exact_get)
        (swapReadyFrame_growth v a evm)
        (by simp only [swapReadyFrame]; swap_exact_get)
        hm4 hcache4' hstate4 hslot4' ha (swapCacheInitial_fits a evm)
        (swapStateInitial_fits a evm ha) (by decide) (by decide) (by decide) (by decide)
        (by decide) hm4size hz4 hc hl hb4.memoryGas (by decide) hcover4 hov with
      hoog | (⟨hex, rr⟩ | (⟨hex, rr⟩ | ⟨f, e, a0, a1, hex, rr, h0, h1⟩))
    · exact Or.inl hoog
    · refine Or.inr (Or.inl ⟨?_, rr⟩)
      apply ExecFuncBody.execBlockRevert
      rw [← List.take_append_drop 13 swapTransition.body]
      exact execBlock_append_ok hinit hex
    · refine Or.inr (Or.inr (Or.inl ⟨?_, rr⟩))
      apply ExecFuncBody.execBlockStatic
      rw [← List.take_append_drop 13 swapTransition.body]
      exact execBlock_append_ok hinit hex
    · refine Or.inr (Or.inr (Or.inr ⟨f, e, a0, a1, ?_, rr, h0, h1⟩))
      apply ExecFuncBody.execBlockRet
      rw [← List.take_append_drop 13 swapTransition.body]
      exact execBlock_append_ok hinit hex

end Benchmarks.UniswapV3.Pool
