import Benchmarks.UniswapV3.Pool.ModifyPositionSlotHeadTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem modifyPositionSlotX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p q : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (a : ModifyPositionArgs)
    (rd : RD (deployedRuntime v) ee g s0 ⟨16264⟩ (⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: q :: R)
      mem aw rdata σ k C)
    (hm : HeapMemory mem aw p) (hq : ModifyPositionParamsMemory mem q a)
    (hqlo : 96 ≤ q.toNat) (hqp : q.toNat + 128 ≤ p.toNat)
    (hb : p.toNat + 224 ≤ 2 ^ 200) (hov : R.length + 14 ≤ 1024) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 ⟨19151⟩
      (EVM.wordOfInt (slot0TickValue σ ee) :: EVM.wordOfInt a.delta :: EVM.wordOfInt a.upper ::
        EVM.wordOfInt a.lower :: EVM.word a.owner.val :: ⟨16428⟩ :: p ::
        ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: q :: R)
      (wordArrayAllocMem mem p (slot0StructWords σ ee)) aw' rdata σ k' C' ∧
      HeapMemory (wordArrayAllocMem mem p (slot0StructWords σ ee)) aw' (p + ⟨224⟩) ∧
      ModifyPositionParamsMemory (wordArrayAllocMem mem p (slot0StructWords σ ee)) q a ∧
      Slot0Memory (wordArrayAllocMem mem p (slot0StructWords σ ee)) p σ ee := by
  obtain ⟨aw1, k1, C1, r1, ha1⟩ := modifyPositionSlotHeadX (v := v) rd hm hb (by evm_ov)
  have hqw : q.toNat + 128 < UInt256.size := by change _ < 2 ^ 256; omega
  have hq2 : ModifyPositionParamsMemory (wordArrayAllocMem mem p (slot0StructWords σ ee)) q a :=
    MemoryPrefix.wordArray (wordArrayAllocMem_prefix mem p (slot0StructWords σ ee)) hq hqlo hqp
  let m := uniswapV3Pool_block_16345_memory (mem := slot0ReadHeadMem mem p σ ee)
    (x0 := slot0FieldWord 25 2 σ ee) (x2 := p + UInt256.ofNat 96)
    (x3 := UInt256.ofNat 65535) (x6 := solcSlotWordAt ⟨0⟩ σ ee) (x7 := p)
  have hmem : m = wordArrayAllocMem mem p (slot0StructWords σ ee) :=
    modifyPositionSlotTailMem_eq mem p σ ee hb
  have hstack : uniswapV3Pool_block_16345_stack (mem := slot0ReadHeadMem mem p σ ee)
      (x0 := slot0FieldWord 25 2 σ ee) (x1 := ⟨96⟩) (x2 := p + ⟨96⟩) (x3 := ⟨65535⟩)
      (x4 := ⟨32⟩) (x5 := EVM.wordOfInt (slot0TickValue σ ee)) (x6 := solcSlotWordAt ⟨0⟩ σ ee)
      (x7 := p) (x8 := ⟨64⟩) (x9 := ⟨0⟩) (x10 := ⟨0⟩) (x11 := ⟨0⟩) (x12 := q) (R := R) =
      (EVM.wordOfInt (slot0TickValue σ ee) :: EVM.wordOfInt a.upper :: EVM.wordOfInt a.delta ::
        EVM.wordOfInt a.lower :: EVM.word a.owner.val :: ⟨16428⟩ :: p ::
        ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: q :: R) := by
    change (EVM.wordOfInt (slot0TickValue σ ee) :: memLoad (q + UInt256.ofNat 64) m ::
      memLoad (q + UInt256.ofNat 96) m :: memLoad (q + UInt256.ofNat 32) m :: memLoad q m ::
      ⟨16428⟩ :: p :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: q :: R) = _
    rw [hmem, hq2.load_upper hqw, hq2.load_delta hqw, hq2.load_lower hqw, hq2.load_owner hqw]
  have r2 := uniswapV3Pool_block_16345 (immWords := wordsOf (immStore v)) (by evm_ov) r1
  have hmout := modifyPositionSlotTailMem_eq mem p σ ee hb
  simp only [show UInt256.ofNat 96 = (⟨96⟩ : UInt256) from rfl,
    show UInt256.ofNat 65535 = (⟨65535⟩ : UInt256) from rfl] at hmout
  rw [hstack, hmout] at r2
  have r3 := uniswapV3Pool_block_16421 (immWords := wordsOf (immStore v)) (by evm_ov)
    (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) r2
  simp only [uniswapV3Pool_block_16421_stack] at r3
  refine ⟨_, _, _, r3, ?_, hq2, wordArrayAllocMem_region mem p _ hm.lower (by
    simp only [slot0StructWords, ne_eq, List.cons_ne_nil, not_false_eq_true])⟩
  apply wordArrayAllocMem_heap mem p _ (slot0StructWords σ ee) hm.lower
    (by simp [slot0StructWords]) hb
  have hpadd (n : Nat) (hn : n ≤ 192) : (p + UInt256.ofNat n).toNat = p.toNat + n :=
    uadd_word_ofNat_toNat p n (by change _ < 2 ^ 256; omega)
  have hqadd (n : Nat) (hn : n ≤ 96) : (q + UInt256.ofNat n).toNat = q.toNat + n :=
    uadd_word_ofNat_toNat q n (by change _ < 2 ^ 256; omega)
  have hp96 : (p + (⟨96⟩ : UInt256)).toNat = p.toNat + 96 := hpadd 96 (by decide)
  have hq32 : (q + (⟨32⟩ : UInt256)).toNat = q.toNat + 32 := hqadd 32 (by decide)
  have hq64 : (q + (⟨64⟩ : UInt256)).toNat = q.toNat + 64 := hqadd 64 (by decide)
  have hq96 : (q + (⟨96⟩ : UInt256)).toNat = q.toNat + 96 := hqadd 96 (by decide)
  repeat' apply activeWords_expand32
  all_goals first | exact ha1 | (rw [hpadd _ (by decide)]; omega) |
    (rw [hp96]; omega) | (rw [hq32]; omega) | (rw [hq64]; omega) | (rw [hq96]; omega) | omega

end Benchmarks.UniswapV3.Pool
