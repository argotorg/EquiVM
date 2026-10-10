import Benchmarks.UniswapV3.Pool.SwapObservationLoad
import Benchmarks.UniswapV3.Pool.SwapObservationStore
import Benchmarks.UniswapV3.Pool.OracleObserveSingleTrace
import Benchmarks.UniswapV3.Pool.OracleObserveSingleInternal

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem swapObservationX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C allowance : Nat} {aw q p exactWord cache snap free : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (c : SwapCacheData) (s : SwapStateData) (d : SwapIterationData)
    (initial : EVM.State) (frame : Frame) (evm : EVM.State)
    (rd : RD (deployedRuntime v) ee g s0 ⟨3691⟩ ([q, p, exactWord, cache, snap] ++ R)
      mem aw rdata σ k C)
    (hf : frame.contract = contract) (hst : SourceState s0 ee σ evm)
    (hcache : frame.locals.get? "cache" = some c.value)
    (hslot : frame.locals.get? "slot0Start" =
      some (slot0StructValue initial.accountMap initial.executionEnv))
    (hm : HeapMemory mem aw free) (hc : SwapCacheMemory mem cache c)
    (hs : SwapStateMemory mem p s) (hd : SwapIterationMemory mem q d)
    (hsnap : Slot0Memory mem snap initial.accountMap initial.executionEnv) (hfit : c.Fits)
    (hcl : 96 ≤ cache.toNat) (hsnapc : snap.toNat + 224 ≤ cache.toNat)
    (hcachep : cache.toNat + 192 ≤ p.toNat) (hpq : p.toNat + 224 ≤ q.toNat)
    (hqfree : q.toNat + 224 ≤ free.toNat) (hb : free.toNat ≤ 2 ^ 200)
    (hbudget : MemoryGasBound aw C allowance) (hallowance : allowance ≤ 2 ^ 200)
    (hcover : free.toNat ≤ aw.toNat * 32 + 32) (hov : R.length + 58 ≤ 1024) :
    (X (g.toNat + 1) (D_J (deployedRuntime v) 0) s0 = .error .OutOfGass) ∨
    (ExecBlock config frame evm swapObservationBody .reverted ∧
      (RDrev (deployedRuntime v) g s0 ∨ RDinvalid (deployedRuntime v) g s0)) ∨
    (∃ tick seconds, ExecBlock config frame evm swapObservationBody
        (.ok (swapObservationFrame frame c tick seconds) evm) ∧
      (swapObservationCache c tick seconds).Fits ∧
      ∃ mem' aw' free' k' C', C + 1 + (Cₘ aw' - Cₘ aw) ≤ C' ∧
        RD (deployedRuntime v) ee g s0 ⟨3775⟩ ([q, p, exactWord, cache, snap] ++ R)
          mem' aw' rdata σ k' C' ∧ HeapMemory mem' aw' free' ∧
        SwapCacheMemory mem' cache (swapObservationCache c tick seconds) ∧
        SwapStateMemory mem' p s ∧ SwapIterationMemory mem' q d ∧
        MemoryPrefix mem mem' cache.toNat ∧ free.toNat ≤ free'.toNat ∧
        free'.toNat ≤ aw'.toNat * 32 + 32) := by
  obtain ⟨a1, k1, C1, hC1, r1, hm1, hmono1⟩ :=
    swapObservationLoadX (v := v) c initial rd hm hc hsnap (by omega) (by omega) (by omega)
  have hbudget1 := hbudget.advance (show C + (Cₘ a1 - Cₘ aw) ≤ C1 by omega)
  have hcover1 : free.toNat ≤ a1.toNat * 32 + 32 := by omega
  have hi : (slot0FieldWord 23 2 initial.accountMap initial.executionEnv).toNat < 2 ^ 16 :=
    u256LandMaskToNatLtOfToNat _ _ (by decide)
  have hcard : (slot0FieldWord 25 2 initial.accountMap initial.executionEnv).toNat < 2 ^ 16 :=
    u256LandMaskToNatLtOfToNat _ _ (by decide)
  have ht : -(2 ^ 23 : Int) ≤ slot0TickValue initial.accountMap initial.executionEnv ∧
      slot0TickValue initial.accountMap initial.executionEnv < 2 ^ 23 :=
    normalizeSint_bounds ⟨24, by decide⟩ _
  have htime : UInt256.land (UInt256.ofNat 4294967295) c.blockTimestamp = c.blockTimestamp := by
    rw [u256_land_comm]
    exact u256LandMaskCleanOfToNat (bits := 32) _ _ (by decide) hfit.2.2.1
  have he := evalSwapObservationArgs (evm := evm) c initial hcache hslot
  rcases oracleObserveSingleX (v := v) r1 hi hcard htime rfl
      (slot0TickWord_idem initial.accountMap initial.executionEnv) hfit.2.1
      hm1 hbudget1 hallowance hcover1
      (by rw [uniswapV3PoolPatchedValidJumps v]; native_decide)
      (by change R.length + 5 + 53 ≤ 1024; omega) with hoog | (hfail | hout)
  · exact Or.inl hoog
  · refine Or.inr (Or.inl ⟨ExecBlock.consRevert ?_, hfail.2⟩)
    exact oracleObserveSingleInternalReverts frame evm c.blockTimestamp ⟨0⟩
      (slot0TickValue initial.accountMap initial.executionEnv)
      (slot0FieldWord 23 2 initial.accountMap initial.executionEnv) c.liquidityStart
      (slot0FieldWord 25 2 initial.accountMap initial.executionEnv) swapObservationArgs "__c12"
      hf he hcard ht (by simpa only [hst.env, ← hst.accounts] using hfail.1)
  · obtain ⟨out⟩ := hout
    let seconds := EVM.wordOfInt out.secondsValue
    have hsval : Int.ofNat seconds.toNat = out.secondsValue := by
      rw [wordOfInt_mod, Int.emod_eq_of_lt out.seconds_range.1 (by
        have h := out.seconds_range.2; omega)]
      exact Int.toNat_of_nonneg out.seconds_range.1
    have hseconds : seconds.toNat < 2 ^ 160 := by
      have h := out.seconds_range.2
      rw [← hsval, Int.ofNat_eq_natCast] at h
      exact_mod_cast h
    have hrun := out.run
    rw [← hsval] at hrun
    have hex := oracleObserveSingleInternalSource frame evm c.blockTimestamp ⟨0⟩
      (slot0TickValue initial.accountMap initial.executionEnv)
      (slot0FieldWord 23 2 initial.accountMap initial.executionEnv) c.liquidityStart
      (slot0FieldWord 25 2 initial.accountMap initial.executionEnv)
      [.int out.tickValue, .int (Int.ofNat seconds.toNat)] swapObservationArgs "__c12"
      hf he hcard ht (by simpa only [hst.env, ← hst.accounts] using hrun)
    have hc2 := MemoryPrefix.wordArray out.memory_prefix hc hcl
      (show cache.toNat + 192 ≤ free.toNat by omega)
    have hs2 := MemoryPrefix.wordArray out.memory_prefix hs (by omega)
      (show p.toNat + 224 ≤ free.toNat by omega)
    have hd2 := MemoryPrefix.wordArray out.memory_prefix hd (by omega) hqfree
    obtain ⟨a3, k3, C3, hC3, r3, hm3, hc3, hs3, hd3, hp3, hmono3⟩ :=
      swapObservationStoreX (v := v) c s d out.tickValue seconds out.rd out.heap hc2 hs2 hd2
        out.tick_word out.seconds_word out.tick_range hcl hcachep hpq (by omega)
        (by change R.length + 1 + 9 ≤ 1024; omega)
    refine Or.inr (Or.inr ⟨out.tickValue, seconds, ?_,
      swapObservationCache_fits c out.tickValue seconds hfit out.tick_range hseconds,
      _, a3, out.free, k3, C3, ?_, r3, hm3, hc3, hs3, hd3,
      (out.memory_prefix.mono (by omega)).trans hp3, out.free_mono, ?_⟩)
    · exact ExecBlock.consNormal hex (swapObservationStoresSource c out.tickValue seconds hcache)
    · have hC2 := out.cost_bound
      omega
    · have h := out.cover
      omega

end Benchmarks.UniswapV3.Pool
