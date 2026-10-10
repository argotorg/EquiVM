import Benchmarks.UniswapV3.Pool.OracleObservePartialArrays
import Benchmarks.UniswapV3.Pool.OracleObserveLoopControl
import Benchmarks.UniswapV3.Pool.OracleObserveStoreTrace
import Benchmarks.UniswapV3.Pool.OracleObserveLoopResult
import Benchmarks.UniswapV3.Pool.OracleObserveSingleTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

set_option maxHeartbeats 800000 in
theorem oracleObserveLoopCursorX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C allowance i : Nat} {aw free agoPtr ticksPtr secondsPtr card liquidity index : UInt256}
    {tickRaw timeRaw ret time : UInt256} {tick : Int} {mem rdata : ByteArray}
    {rawAgos : List UInt256} {ticks seconds : List Int} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨17172⟩
      (oracleObserveStack i secondsPtr ticksPtr card liquidity index tickRaw agoPtr timeRaw ret R)
      mem aw rdata σ k C)
    (hindex : index.toNat < 2 ^ 16) (hc : card.toNat < 2 ^ 16)
    (htime : UInt256.land (UInt256.ofNat 4294967295) timeRaw = time)
    (htick : UInt256.signextend (UInt256.ofNat 2) tickRaw = EVM.wordOfInt tick)
    (hliq : liquidity.toNat < 2 ^ 128) (hn : rawAgos.length ≤ 2 ^ 64 - 1)
    (hi : i ≤ rawAgos.length) (hm : MemoryCursor mem aw free)
    (hl : OracleObserveLayout free agoPtr ticksPtr secondsPtr rawAgos.length)
    (ha : OracleObservePartialArrays mem agoPtr ticksPtr secondsPtr rawAgos ticks seconds i)
    (hbudget : MemoryGasBound aw C allowance) (hallowance : allowance ≤ 2 ^ 200)
    (hcover : free.toNat ≤ aw.toNat * 32 + 32)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hov : R.length + 64 ≤ 1024) :
    OracleObserveLoopOutcome v ee g s0 σ rdata ret R time rawAgos tick index liquidity card
      agoPtr ticksPtr secondsPtr i ticks seconds mem aw free C := by
  generalize hremain : rawAgos.length - i = remaining
  induction remaining using Nat.strong_induction_on generalizing i ticks seconds mem aw free k C with
  | h remaining ih =>
    have hae := hl.ago_end
    have hte := hl.ticks_end
    have hse := hl.seconds_end
    rcases memoryGasCapacityOrOOG rd hbudget hallowance hcover with hoog | hb
    · exact Or.inl hoog
    by_cases hin : i < rawAgos.length
    · have hin' : i < (oracleObserveCleanAgos rawAgos).length := by
        simpa only [oracleObserveCleanAgos, List.length_map] using hin
      have hnat := wordArrayElement_toNat agoPtr i (by change _ < 2 ^ 256; omega)
      have hba : (wordArrayElement agoPtr i).toNat + 32 ≤ 2 ^ 200 := by rw [hnat]; omega
      obtain ⟨k1, C1, hC1, r1⟩ := oracleObserveLoopCallX (v := v) rd hm.active ha.agos_mem
        (by omega) hin (by omega)
      have hm1 := hm.expand32 (wordArrayElement agoPtr i) hba
      have hb1 := hbudget.advance hC1
      have hmono1 := expandedWords_mono (size := ⟨32⟩) hm.active hba
      have hcover1 : free.toNat ≤ (M aw (wordArrayElement agoPtr i) ⟨32⟩).toNat * 32 + 32 := by
        change aw.toNat ≤ (M aw (wordArrayElement agoPtr i) ⟨32⟩).toNat at hmono1
        omega
      rcases oracleObserveSingleCursorX (v := v) r1 hindex hc htime rfl htick hliq hm1 hb1 hallowance
          hcover1 (by rw [uniswapV3PoolPatchedValidJumps v]; jump_dest)
          (by dsimp only [oracleObserveStack, List.length]; omega) with hoog | (hfail | hout)
      · exact Or.inl hoog
      · refine Or.inr (Or.inl ⟨.failure hin' ?_, hfail.2⟩)
        simpa only [oracleObserveCleanAgos, List.getElem_map] using hfail.1
      · obtain ⟨out⟩ := hout
        have hl2 := hl.mono out.free_mono
        have ha2 := ha.prefix hl out.memory_prefix
        have hb2 := hb1.advance out.cost_bound
        rcases memoryGasCapacityOrOOG out.rd hb2 hallowance out.cover with hoog | hbfree
        · exact Or.inl hoog
        have hse2 := hl2.seconds_end
        have ht := ha2.ticks_mem.header (by
          simp only [List.length_map, ha2.ticks_length]; change _ < 2 ^ 256; omega)
        have hs := ha2.seconds_mem.header (by
          simp only [List.length_map, ha2.seconds_length]; change _ < 2 ^ 256; omega)
        simp only [List.length_map, ha2.ticks_length, ha2.seconds_length] at ht hs
        obtain ⟨k3, C3, hC3, r3⟩ := oracleObserveLoopStoreX (v := v) out.rd out.heap.active ht hs hin
          hte (by omega) out.tick_word out.seconds_word
          (by dsimp only [List.length]; omega)
        have ha3 := ha2.update hl2 hin out.tick_range out.seconds_range
        have hnat3 := wordArrayElement_toNat secondsPtr i (by change _ < 2 ^ 256; omega)
        have hbs : (wordArrayElement secondsPtr i).toNat + 32 ≤ 2 ^ 200 := by rw [hnat3]; omega
        have hm3 := (oracleObserveUpdateCursor i out.tickValue out.secondsValue out.heap.cursor hl2).expand32
          (wordArrayElement secondsPtr i) hbs
        have hb3 := hb2.advance hC3
        have hmono3 := expandedWords_mono (size := ⟨32⟩) out.heap.active hbs
        have hcover3 : out.free.toNat ≤
            (M out.aw (wordArrayElement secondsPtr i) ⟨32⟩).toNat * 32 + 32 := by
          change out.aw.toNat ≤ (M out.aw (wordArrayElement secondsPtr i) ⟨32⟩).toNat at hmono3
          have h := out.cover
          omega
        have hrun : OracleObserveSingleRun time (oracleObserveCleanAgos rawAgos)[i]
            tick index liquidity card σ ee [.int out.tickValue, .int out.secondsValue] := by
          simpa only [oracleObserveCleanAgos, List.getElem_map] using out.run
        have hpre := (out.memory_prefix.mono (show ticksPtr.toNat ≤ free.toNat by omega)).trans
          (oracleObserveUpdatePrefix out.mem ticksPtr secondsPtr i out.tickValue out.secondsValue (by omega))
        rcases ih (rawAgos.length - (i + 1)) (by omega) r3 (by omega) hm3 hl2 ha3 hb3 hcover3 rfl with
            hoog | (hfail | hfinal)
        · exact Or.inl hoog
        · refine Or.inr (Or.inl ⟨.step hin' hrun ?_, hfail.2⟩)
          simpa only [List.map_set] using hfail.1
        · obtain ⟨final⟩ := hfinal
          exact Or.inr (Or.inr ⟨{ final with
            run := .step hin' hrun (by simpa only [List.map_set] using final.run)
            free_mono := out.free_mono.trans final.free_mono
            memory_prefix := hpre.trans final.memory_prefix
            cost_bound := by have h1 := out.cost_bound; have h2 := final.cost_bound; omega }⟩)
    · have rdone := oracleObserveLoopDoneX (v := v) rd ha.agos_mem
        (by change _ < 2 ^ 256; omega) (by omega) (by change _ < 2 ^ 256; omega) hret (by omega)
      have hba : agoPtr.toNat + 32 ≤ 2 ^ 200 := by omega
      have hmono := expandedWords_mono (size := ⟨32⟩) hm.active hba
      exact Or.inr (Or.inr ⟨{
        mem := mem
        aw := M aw agoPtr ⟨32⟩
        free := free
        ticks := ticks
        seconds := seconds
        k := _
        cost := _
        rd := rdone
        run := .done (by simpa only [oracleObserveCleanAgos, List.length_map] using Nat.le_of_not_gt hin)
        heap := hm.expand32 agoPtr hba
        layout := hl
        arrays := ha.complete (Nat.le_of_not_gt hin)
        free_mono := le_refl _
        memory_prefix := .refl _ _
        cover := by change aw.toNat ≤ (M aw agoPtr ⟨32⟩).toNat at hmono; omega
        cost_bound := by dsimp only [memExpansionCost]; omega }⟩)

theorem oracleObserveLoopX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C allowance i : Nat} {aw free agoPtr ticksPtr secondsPtr card liquidity index : UInt256}
    {tickRaw timeRaw ret time : UInt256} {tick : Int} {mem rdata : ByteArray}
    {rawAgos : List UInt256} {ticks seconds : List Int} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨17172⟩
      (oracleObserveStack i secondsPtr ticksPtr card liquidity index tickRaw agoPtr timeRaw ret R)
      mem aw rdata σ k C)
    (hindex : index.toNat < 2 ^ 16) (hc : card.toNat < 2 ^ 16)
    (htime : UInt256.land (UInt256.ofNat 4294967295) timeRaw = time)
    (htick : UInt256.signextend (UInt256.ofNat 2) tickRaw = EVM.wordOfInt tick)
    (hliq : liquidity.toNat < 2 ^ 128) (hn : rawAgos.length ≤ 2 ^ 64 - 1)
    (hi : i ≤ rawAgos.length) (hm : HeapMemory mem aw free)
    (hl : OracleObserveLayout free agoPtr ticksPtr secondsPtr rawAgos.length)
    (ha : OracleObserveArrays mem agoPtr ticksPtr secondsPtr rawAgos ticks seconds)
    (hbudget : MemoryGasBound aw C allowance) (hallowance : allowance ≤ 2 ^ 200)
    (hcover : free.toNat ≤ aw.toNat * 32 + 32)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hov : R.length + 64 ≤ 1024) :
    OracleObserveLoopOutcome v ee g s0 σ rdata ret R time rawAgos tick index liquidity card
      agoPtr ticksPtr secondsPtr i ticks seconds mem aw free C := by
  exact oracleObserveLoopCursorX (v := v) rd hindex hc htime htick hliq hn hi hm.cursor hl
    (ha.partial i) hbudget hallowance hcover hret hov

end Benchmarks.UniswapV3.Pool
