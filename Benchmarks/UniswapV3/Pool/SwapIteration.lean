import Benchmarks.UniswapV3.Pool.SwapIterationTail
import Benchmarks.UniswapV3.Pool.SwapIterationFeesFrame

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def swapIterationWrites : List Ident := swapFeesWrites ++ swapTailWrites

structure SwapIterationExit (v : UniswapV3PoolImmutables) (ee : ExecutionEnv) (g : Sat256)
    (s0 : EVM.State) (rdata : ByteArray) (p cache snap : UInt256) (stack : List UInt256)
    (initial : EVM.State) (frame : Frame) (evm : EVM.State)
    (initMem : ByteArray) (initAw initFree : UInt256) (initCost : Nat) where
  cacheData : SwapCacheData
  stateData : SwapStateData
  frame' : Frame
  evm' : EVM.State
  accounts : AccountMap
  mem : ByteArray
  aw : UInt256
  free : UInt256
  k : Nat
  cost : Nat
  source : ExecBlock config frame evm swapLoopBody (.ok frame' evm')
  source_state : SourceState s0 ee accounts evm'
  contract_eq : frame'.contract = frame.contract
  immutables_eq : frame'.immutables = frame.immutables
  cache_get : frame'.locals.get? "cache" = some cacheData.value
  state_get : frame'.locals.get? "state" = some stateData.value
  locals_get : ∀ name, name ∉ swapIterationWrites →
    frame'.locals.get? name = frame.locals.get? name
  cache_fits : cacheData.Fits
  state_fits : stateData.Fits
  rd : RD (deployedRuntime v) ee g s0 ⟨2991⟩ stack mem aw rdata accounts k cost
  heap : HeapMemory mem aw free
  cache_mem : SwapCacheMemory mem cache cacheData
  state_mem : SwapStateMemory mem p stateData
  snapshot : Slot0Memory mem snap initial.accountMap initial.executionEnv
  memory_prefix : MemoryPrefix initMem mem cache.toNat
  free_mono : initFree.toNat ≤ free.toNat
  cover : free.toNat ≤ aw.toNat * 32 + 32
  cost_bound : initCost + 1 + (Cₘ aw - Cₘ initAw) ≤ cost

theorem swapIterationX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C allowance : Nat}
    {aw p q cache snap dataStart dataLength ret : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (a : SwapArgs) (c : SwapCacheData) (s : SwapStateData)
    (initial : EVM.State) (frame : Frame) (evm : EVM.State)
    (rd : RD (deployedRuntime v) ee g s0 ⟨3035⟩
      (swapLoopWords a p (swapExactInput a).toUInt256 cache snap dataStart dataLength ret R)
      mem aw rdata σ k C)
    (hsource : SourceState s0 ee σ evm) (hf : frame.contract = contract)
    (hi : frame.immutables = immStore v)
    (hz : frame.locals.get? "zeroForOne" = some (.bool a.zeroForOne))
    (hcget : frame.locals.get? "cache" = some c.value)
    (hsget : frame.locals.get? "state" = some s.value)
    (hslot : frame.locals.get? "slot0Start" =
      some (slot0StructValue initial.accountMap initial.executionEnv))
    (hlimit : frame.locals.get? "sqrtPriceLimitX96" = some (.int (Int.ofNat a.priceLimit.toNat)))
    (hexact : frame.locals.get? "exactInput" = some (.bool (swapExactInput a)))
    (hg : ∀ b, frame.locals.get? (feeGrowthName b) = none)
    (hm : HeapMemory mem aw q) (hc : SwapCacheMemory mem cache c)
    (hs : SwapStateMemory mem p s)
    (hsnap : Slot0Memory mem snap initial.accountMap initial.executionEnv)
    (ha : a.Fits) (hcf : c.Fits) (hsf : s.Fits)
    (hperm : ee.perm = true) (hcache : 96 ≤ cache.toNat) (hsl : 96 ≤ snap.toNat)
    (hsnapc : snap.toNat + 224 ≤ cache.toNat)
    (hcp : cache.toNat + 192 ≤ p.toNat) (hpq : p.toNat + 224 ≤ q.toNat)
    (hbudget : MemoryGasBound aw C allowance) (hallowance : allowance ≤ 2 ^ 200)
    (hcover : q.toNat ≤ aw.toNat * 32 + 32) (hov : R.length + 67 ≤ 1024) :
    (X (g.toNat + 1) (D_J (deployedRuntime v) 0) s0 = .error .OutOfGass) ∨
    (ExecBlock config frame evm swapLoopBody .reverted ∧
      (RDrev (deployedRuntime v) g s0 ∨ RDinvalid (deployedRuntime v) g s0)) ∨
    Nonempty (SwapIterationExit v ee g s0 rdata p cache snap
      (swapLoopWords a p (swapExactInput a).toUInt256 cache snap dataStart dataLength ret R)
      initial frame evm mem aw q C) := by
  rcases memoryGasCapacityOrOOG rd hbudget hallowance hcover with hoog | hcap
  · exact Or.inl hoog
  have hbody : swapLoopBody = swapLoopBody.take 16 ++ [swapLoopBody[16]!] := rfl
  rcases swapIterationFeesPrefixX (v := v) a c s frame evm rd hsource hf hi hcget hsget hz
      hlimit hexact hm hc hs ha hsf hcf hcache hcp hpq (by omega) (by omega) with
    ⟨hex1, hr⟩ | ⟨hex1, hfit1, m1, aw1, k1, C1, hC1, r1, hm1, hs1, hd1, hp1, hcvr1⟩
  · refine Or.inr (Or.inl ⟨?_, hr⟩)
    rw [hbody]
    exact execBlock_append_term hex1 (by intro _ _ h; cases h)
  · have hparts := swapIterationFeesFrame_parts frame v a c s evm
    have hget := swapIterationFeesFrame_get frame v a c s evm
    have hc1 : SwapCacheMemory m1 cache c := MemoryPrefix.wordArray hp1 hc hcache hcp
    have hsn1 : Slot0Memory m1 snap initial.accountMap initial.executionEnv :=
      MemoryPrefix.wordArray hp1 hsnap hsl (by change snap.toNat + 224 ≤ p.toNat; omega)
    have hbound := swapIterationFeesData_bounds v a c s evm hsf
    have hbudget1 := hbudget.advance (show C + (Cₘ aw1 - Cₘ aw) ≤ C1 by omega)
    have hfree : (q + (⟨224⟩ : UInt256)).toNat = q.toNat + 224 :=
      uadd_word_ofNat_toNat q 224 (by change _ < 2 ^ 256; omega)
    have hg1 : ∀ b, (swapIterationFeesFrame frame v a c s evm).locals.get?
        (feeGrowthName b) = none := by
      intro b
      exact (hget (feeGrowthName b) (by cases b <;> decide)).trans (hg b)
    rcases swapIterationTailX (v := v) a c (swapIterationFeesState v a c s evm)
        (swapIterationFeesData v a c s evm) initial (swapIterationFeesFrame frame v a c s evm)
        evm r1 hsource (hparts.1.trans hf) (hparts.2.trans hi)
        ((hget "zeroForOne" (by decide)).trans hz) ((hget "cache" (by decide)).trans hcget)
        (swapIterationFeesFrame_state frame v a c s evm)
        (swapIterationFeesFrame_step frame v a c s evm)
        ((hget "slot0Start" (by decide)).trans hslot) hg1 hm1 hc1 hs1 hd1 hsn1 hcf hfit1
        hbound.1 hbound.2.1 hbound.2.2 hperm hcache hsnapc hcp hpq
        (by rw [hfree]) (by rw [hfree]; omega) hbudget1 hallowance hcvr1 hov with
      hoog | (⟨hex2, hr⟩ | ⟨out⟩)
    · exact Or.inl hoog
    · refine Or.inr (Or.inl ⟨?_, hr⟩)
      rw [hbody]
      exact execBlock_append_ok hex1 (ExecBlock.consRevert hex2)
    · rcases out with ⟨out⟩
      have r2 := uniswapV3Pool_block_3993 (immWords := wordsOf (immStore v))
        (by change R.length + 13 + 1 ≤ 1024; omega)
        (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; native_decide) out.rd
      have hpre := (hp1.mono (show cache.toNat ≤ p.toNat by omega)).trans out.memory_prefix
      have hC2 := out.cost_bound
      have hf2 := out.free_mono
      refine Or.inr (Or.inr ⟨{
        cacheData := out.cacheData, stateData := out.stateData
        frame' := out.frame', evm' := out.evm', accounts := out.accounts
        mem := out.mem, aw := out.aw, free := out.free, k := out.k + 4, cost := out.cost + 14
        source := ?_, source_state := out.source_state
        contract_eq := out.contract_eq.trans hparts.1
        immutables_eq := out.immutables_eq.trans hparts.2
        cache_get := out.cache_get, state_get := out.state_get, locals_get := ?_
        cache_fits := out.cache_fits, state_fits := out.state_fits
        rd := r2, heap := out.heap, cache_mem := out.cache_mem, state_mem := out.state_mem
        snapshot := MemoryPrefix.wordArray hpre hsnap hsl hsnapc
        memory_prefix := hpre, free_mono := by rw [hfree] at hf2; omega
        cover := out.cover, cost_bound := by omega }⟩)
      · exact execBlock_append_ok hex1 out.source
      · intro name hn
        simp only [swapIterationWrites, List.mem_append, not_or] at hn
        exact (out.locals_get name hn.2).trans (hget name hn.1)

end Benchmarks.UniswapV3.Pool
