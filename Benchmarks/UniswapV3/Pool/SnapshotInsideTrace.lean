import Benchmarks.UniswapV3.Pool.SnapshotSlotRead
import Benchmarks.UniswapV3.Pool.SnapshotReturn
import Benchmarks.UniswapV3.Pool.OracleObserveTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem snapshotInsideRawTimeWords (current : OracleObservation) (timeRaw time : UInt256)
    (a b : TickOutside) (htime : UInt256.land timeRaw (UInt256.ofNat (2 ^ 32 - 1)) = time) :
    snapshotCleanWords (UInt256.sub (UInt256.sub timeRaw a.seconds) b.seconds)
      (UInt256.sub (UInt256.sub current.secondsPerLiquidity a.secondsPerLiquidity) b.secondsPerLiquidity)
      (UInt256.sub (UInt256.sub (EVM.wordOfInt current.tickCumulative)
        (EVM.wordOfInt a.cumulative)) (EVM.wordOfInt b.cumulative)) =
      (snapshotInside current time a b).words := by
  have hc : normalizeInt (.uint ⟨32, by decide⟩) (Int.ofNat timeRaw.toNat) = Int.ofNat time.toNat := by
    rw [normalizeUIntWord_mask ⟨32, by decide⟩ _ (UInt256.ofNat (2 ^ 32 - 1)) (by decide), htime]
  rw [snapshotInsideWords]
  simp only [SnapshotCumulatives.words, snapshotInside]
  rw [← normalizeInt_sub_left (.uint ⟨32, by decide⟩) (Int.ofNat timeRaw.toNat) (Int.ofNat a.seconds.toNat), hc]

theorem snapshotFinishX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw free seconds liquidity tick upperRaw lowerRaw : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨10448⟩
      (seconds :: liquidity :: tick :: upperRaw :: lowerRaw :: UInt256.ofNat 1952 :: R) mem aw rdata σ k C)
    (hm : HeapMemory mem aw free) (hb : free.toNat + 96 ≤ 2 ^ 200) (hov : R.length + 7 ≤ 1024) :
    RDret (deployedRuntime v) g s0 σ (wordBytes (snapshotCleanWords seconds liquidity tick)) := by
  have hr := uniswapV3Pool_block_10448 (immWords := wordsOf (immStore v)) (by evm_ov)
    (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
  simp only [uniswapV3Pool_block_10448_stack] at hr
  exact snapshotReturnX (v := v) hr hm hb hov

theorem snapshotInsideX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw free p lowerRaw upperRaw : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (lower upper : Int)
    (rd : RD (deployedRuntime v) ee g s0 ⟨10336⟩
      (snapshotReadyStack lower upper σ ee p lowerRaw upperRaw (UInt256.ofNat 1952) R) mem aw rdata σ k C)
    (hm : HeapMemory mem aw free) (hslot : Slot0Memory mem p σ ee)
    (hb : free.toNat + 480 ≤ 2 ^ 200) (hp : p.toNat + 224 ≤ 2 ^ 200)
    (hov : R.length + 55 ≤ 1024) :
    (RDinvalid (deployedRuntime v) g s0 ∧ ¬ (slot0FieldWord 23 2 σ ee).toNat < 65535) ∨
    (RDret (deployedRuntime v) g s0 σ
      (wordBytes (snapshotInside (snapshotCurrent σ ee) (blockTimestampWord ee)
        (tickOutside lower σ ee) (tickOutside upper σ ee)).words) ∧
      (slot0FieldWord 23 2 σ ee).toNat < 65535) := by
  simp only [snapshotReadyStack, List.cons_append, List.nil_append] at rd
  have rdTimestamp := uniswapV3Pool_block_10336 (immWords := wordsOf (immStore v)) (by evm_ov)
    (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
  simp only [uniswapV3Pool_block_10336_stack] at rdTimestamp
  obtain ⟨kt, Ct, rdTime⟩ := blockTimestampX (v := v) rdTimestamp
    (by rw [uniswapV3PoolPatchedValidJumps v]; jump_dest) (by evm_ov)
  have hpb : p.toNat + 224 < UInt256.size := by change _ < 2 ^ 256; omega
  have h32 := uadd_word_ofNat_toNat p 32 (show p.toNat + 32 < UInt256.size by omega)
  have h64 := uadd_word_ofNat_toNat p 64 (show p.toNat + 64 < UInt256.size by omega)
  have h96 := uadd_word_ofNat_toNat p 96 (show p.toNat + 96 < UInt256.size by omega)
  have hmask : UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128))
      (UInt256.ofNat 1) = UInt256.ofNat (2 ^ 128 - 1) := by native_decide
  obtain ⟨kc, Cc, rdCall⟩ := uniswapV3Pool_block_10345 (immWords := wordsOf (immStore v))
    (by evm_ov) (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rdTime
  simp only [uniswapV3Pool_block_10345_stack, hslot.load_tick hpb, hslot.load_index hpb,
    hslot.load_cardinality hpb, hmask, u256_land_comm (UInt256.ofNat (2 ^ 128 - 1))] at rdCall
  have hheap := ((hm.expand32 (p + UInt256.ofNat 32) (by rw [h32]; omega)).expand32
    (p + UInt256.ofNat 64) (by rw [h64]; omega)).expand32 (p + UInt256.ofNat 96) (by rw [h96]; omega)
  have hliq : (poolLiquidityWord σ ee).toNat < 2 ^ 128 :=
    u256LandMaskToNatLtOfToNat _ _ (by decide)
  by_cases hin : (slot0FieldWord 23 2 σ ee).toNat < 65535
  · obtain ⟨mem', aw', free', kr, Cr, rdReturn, hh, hf, _⟩ :=
      oracleObserveSingleZeroX (v := v) (time := blockTimestampWord ee) (tick := slot0TickValue σ ee)
        rdCall hheap (by omega) hin rfl (slot0TickWord_idem σ ee) hliq
        (by rw [uniswapV3PoolPatchedValidJumps v]; jump_dest) (by evm_ov)
    have hr := uniswapV3Pool_block_10399 (immWords := wordsOf (immStore v)) (by evm_ov)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rdReturn
    simp only [uniswapV3Pool_block_10399_stack] at hr
    have hret := snapshotFinishX (v := v) hr hh (by omega) (by evm_ov)
    rw [snapshotInsideRawTimeWords _ _ (blockTimestampWord ee) _ _ rfl] at hret
    exact Or.inr ⟨hret, hin⟩
  · exact Or.inl ⟨oracleObserveSingleZeroInvalidX (v := v) rdCall
      (u256LandMaskToNatLtOfToNat (bits := 16) _ _ (by native_decide)) hin (by evm_ov), hin⟩

end Benchmarks.UniswapV3.Pool
