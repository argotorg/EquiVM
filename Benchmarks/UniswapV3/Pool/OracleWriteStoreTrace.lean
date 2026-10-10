import Benchmarks.UniswapV3.Pool.OracleWriteTransformTrace
import Benchmarks.UniswapV3.Pool.OracleWriteStaticTrace
import Benchmarks.UniswapV3.Pool.OracleObservationPacked

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem oracleWriteStoreRawX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p q free ret timeRaw : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (a : OracleWriteArgs)
    (obs : OracleObservation)
    (rd : RD (deployedRuntime v) ee g s0 ⟨15020⟩
      (oracleWriteTransformedWords {a with time := timeRaw} p q ++ ret :: R) mem aw rdata σ k C)
    (hfit : a.Fits) (hn : (oracleWriteCardinality a).toNat ≠ 0)
    (hh : HeapMemory mem aw free) (hm : ObservationMemory mem q obs) (hv : obs.Valid)
    (hb : q.toNat + 128 ≤ 2 ^ 200)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hov : R.length + 21 ≤ 1024) :
    (RDstatic (deployedRuntime v) g s0 ∧ ee.perm = false) ∨
      (ee.perm = true ∧ ∃ aw' k' C',
        RD (deployedRuntime v) ee g s0 ret (oracleWriteCardinality a :: oracleWriteIndex a :: R)
          mem aw' rdata (oracleObservationMap σ ee (oracleWriteIndex a) obs) k' C' ∧
        HeapMemory mem aw' free) := by
  have hi := oracleWriteIndex_lt a hfit hn
  have hmask : UInt256.land (UInt256.ofNat 65535) (oracleWriteIndex a) = oracleWriteIndex a := by
    rw [u256_land_comm]
    exact u256LandMaskCleanOfToNat (bits := 16) _ _ (by decide)
      (by change (oracleWriteIndex a).toNat < 65536; omega)
  have hsize : q.toNat + 128 < UInt256.size := by change _ < 2 ^ 256; omega
  have hl0 := hm.load_timestamp hsize
  have hl1 := hm.load_tick hsize
  have hl2 := hm.load_seconds hsize
  have hl3 : memLoad (q + UInt256.ofNat 96) mem = obs.initialized.toUInt256 := by
    have h := hm.load 3 (by change 3 < 4; decide) hsize
    cases hf : obs.initialized <;>
      simpa only [OracleObservation.words, List.getElem_cons_succ, List.getElem_cons_zero,
        hf, Bool.false_eq_true, if_false, if_true] using h
  have hb32 (n : Nat) (hle : n ≤ 96) : (q + UInt256.ofNat n).toNat + 32 ≤ 2 ^ 200 := by
    rw [uadd_word_ofNat_toNat q n (by change _ < 2 ^ 256; omega)]
    omega
  have hheap := (((hh.expand32 q (by omega)).expand32 (q + UInt256.ofNat 32)
    (hb32 32 (by decide))).expand32 (q + UInt256.ofNat 64) (hb32 64 (by decide))).expand32
    (q + UInt256.ofNat 96) (hb32 96 (by decide))
  simp only [oracleWriteTransformedWords, oracleWriteCardinality_setTime, oracleWriteIndex_setTime,
    List.cons_append, List.nil_append] at rd
  have r1 := uniswapV3Pool_block_15020_taken (immWords := wordsOf (immStore v)) (by evm_ov)
    (by rw [hmask, ult_one (show (oracleWriteIndex a).toNat < (UInt256.ofNat 65535).toNat from hi)]
        decide)
    (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
  simp only [uniswapV3Pool_block_15020_taken_stack, hmask] at r1
  obtain ⟨ks, Cs, rs⟩ := uniswapV3Pool_block_15037 (immWords := wordsOf (immStore v))
    (by evm_ov) r1
  simp only [uniswapV3Pool_block_15037_stack, hl0, hl1, hl2, hl3, hv.cleanTick] at rs
  cases hp : ee.perm
  · exact Or.inl ⟨oracleWriteStoreStaticX (v := v) rs hp (by evm_ov), rfl⟩
  · obtain ⟨kr, Cr, rr⟩ := uniswapV3Pool_block_15206 (immWords := wordsOf (immStore v))
      (by evm_ov) hp hret rs
    have hslot : (⟨8⟩ : UInt256) + oracleWriteIndex a = observationSlot (oracleWriteIndex a) :=
      u256_add_comm _ _
    simp only [uniswapV3Pool_block_15206_stack, hslot] at rr
    change RD (deployedRuntime v) ee g s0 ret (oracleWriteCardinality a :: oracleWriteIndex a :: R)
      mem _ rdata (sstoreAccountMap ee.codeOwner σ (observationSlot (oracleWriteIndex a))
        (oracleObservationPackedWord obs (solcSlotWordAt (observationSlot (oracleWriteIndex a)) σ ee)))
      kr Cr at rr
    rw [oracleObservationPackedWord_eq] at rr
    exact Or.inr ⟨rfl, _, kr, Cr, rr, hheap⟩

theorem oracleWriteStoreX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p q free ret : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (a : OracleWriteArgs)
    (obs : OracleObservation)
    (rd : RD (deployedRuntime v) ee g s0 ⟨15020⟩
      (oracleWriteTransformedWords a p q ++ ret :: R) mem aw rdata σ k C)
    (hfit : a.Fits) (hn : (oracleWriteCardinality a).toNat ≠ 0)
    (hh : HeapMemory mem aw free) (hm : ObservationMemory mem q obs) (hv : obs.Valid)
    (hb : q.toNat + 128 ≤ 2 ^ 200)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hov : R.length + 21 ≤ 1024) :
    (RDstatic (deployedRuntime v) g s0 ∧ ee.perm = false) ∨
      (ee.perm = true ∧ ∃ aw' k' C',
        RD (deployedRuntime v) ee g s0 ret (oracleWriteCardinality a :: oracleWriteIndex a :: R)
          mem aw' rdata (oracleObservationMap σ ee (oracleWriteIndex a) obs) k' C' ∧
        HeapMemory mem aw' free) := by
  exact oracleWriteStoreRawX (v := v) (timeRaw := a.time) a obs rd hfit hn hh hm hv hb hret hov

end Benchmarks.UniswapV3.Pool
