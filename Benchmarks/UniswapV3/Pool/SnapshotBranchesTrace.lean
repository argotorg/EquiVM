import Benchmarks.UniswapV3.Pool.SnapshotInsideTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem snapshotBranchesX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw free p lowerRaw upperRaw : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (lower upper : Int)
    (rd : RD (deployedRuntime v) ee g s0
      (if slot0TickValue σ ee < lower then ⟨10298⟩ else ⟨10317⟩)
      (snapshotReadyStack lower upper σ ee p lowerRaw upperRaw (UInt256.ofNat 1952) R) mem aw rdata σ k C)
    (hm : HeapMemory mem aw free) (hslot : Slot0Memory mem p σ ee)
    (hb : free.toNat + 480 ≤ 2 ^ 200) (hp : p.toNat + 224 ≤ 2 ^ 200)
    (hticks : validTicks lower upper)
    (hu : UInt256.signextend (UInt256.ofNat 2) upperRaw = EVM.wordOfInt upper)
    (hov : R.length + 55 ≤ 1024) :
    (RDinvalid (deployedRuntime v) g s0 ∧ lower ≤ slot0TickValue σ ee ∧ slot0TickValue σ ee < upper ∧
      ¬ (slot0FieldWord 23 2 σ ee).toNat < 65535) ∨
    (RDret (deployedRuntime v) g s0 σ (wordBytes (snapshotResult lower upper σ ee).words) ∧
      (lower ≤ slot0TickValue σ ee → slot0TickValue σ ee < upper →
        (slot0FieldWord 23 2 σ ee).toNat < 65535)) := by
  simp only [snapshotReadyStack, List.cons_append, List.nil_append] at rd
  by_cases hbelow : slot0TickValue σ ee < lower
  · simp only [if_pos hbelow] at rd
    have hr := uniswapV3Pool_block_10298 (immWords := wordsOf (immStore v)) (by evm_ov)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
    simp only [uniswapV3Pool_block_10298_stack] at hr
    have hret := snapshotFinishX (v := v) hr hm (by omega) (by evm_ov)
    rw [snapshotDifferenceWords] at hret
    exact Or.inr ⟨by simpa only [snapshotResult, if_pos hbelow] using hret, by intro h; omega⟩
  · simp only [if_neg hbelow] at rd
    have hpb : p.toNat + 224 < UInt256.size := by change _ < 2 ^ 256; omega
    have htick := slot0TickValue_bounds σ ee
    have hc : UInt256.isZero (UInt256.slt
        (UInt256.signextend (UInt256.ofNat 2) (memLoad (UInt256.ofNat 32 + p) mem))
        (UInt256.signextend (UInt256.ofNat 2) upperRaw)) =
        if slot0TickValue σ ee < upper then (⟨0⟩ : UInt256) else ⟨1⟩ := by
      rw [u256_add_comm (UInt256.ofNat 32), hslot.load_tick hpb, slot0TickWord_idem, hu,
        slt_wordOfInt (slot0TickValue σ ee) upper (by omega) (by omega)
          (by obtain ⟨hord, hlo, _⟩ := hticks; omega) (by obtain ⟨_, _, hhi⟩ := hticks; omega)]
      split <;> rfl
    have h32 : (UInt256.ofNat 32 + p).toNat = p.toNat + 32 := by
      rw [u256_add_comm]
      exact uadd_word_ofNat_toNat p 32 (by omega)
    have hm' := hm.expand32 (UInt256.ofNat 32 + p) (by rw [h32]; omega)
    by_cases hinside : slot0TickValue σ ee < upper
    · have hr := uniswapV3Pool_block_10317_fallthrough (immWords := wordsOf (immStore v)) (by evm_ov)
        (by rw [hc, if_pos hinside]; rfl) rd
      rcases snapshotInsideX (v := v) lower upper hr hm' hslot hb hp hov with ⟨hi, hout⟩ | ⟨hs, hin⟩
      · exact Or.inl ⟨hi, by omega, hinside, hout⟩
      · exact Or.inr ⟨by simpa only [snapshotResult, if_neg hbelow, if_pos hinside] using hs,
          fun _ _ => hin⟩
    · have hr := uniswapV3Pool_block_10317_taken (immWords := wordsOf (immStore v)) (by evm_ov)
        (by rw [hc, if_neg hinside]; decide)
        (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
      have hr' := uniswapV3Pool_block_10433 (immWords := wordsOf (immStore v)) (by evm_ov) hr
      simp only [uniswapV3Pool_block_10433_stack] at hr'
      have hret := snapshotFinishX (v := v) hr' hm' (by omega) (by evm_ov)
      rw [snapshotDifferenceWords] at hret
      exact Or.inr ⟨by simpa only [snapshotResult, if_neg hbelow, if_neg hinside] using hret,
        by intro _ h; exact False.elim (hinside h)⟩

end Benchmarks.UniswapV3.Pool
