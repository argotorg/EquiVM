import Benchmarks.UniswapV3.Pool.ModifyPositionMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem modifyPositionSlotHeadX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨16264⟩ R mem aw rdata σ k C)
    (hm : HeapMemory mem aw p) (hb : p.toNat + 224 ≤ 2 ^ 200) (hov : R.length + 10 ≤ 1024) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 ⟨16345⟩
      (slot0FieldWord 25 2 σ ee :: ⟨96⟩ :: (p + ⟨96⟩) :: ⟨65535⟩ :: ⟨32⟩ ::
        EVM.wordOfInt (slot0TickValue σ ee) :: solcSlotWordAt ⟨0⟩ σ ee :: p :: ⟨64⟩ :: R)
      (slot0ReadHeadMem mem p σ ee) aw' rdata σ k' C' ∧ ActiveWords aw' := by
  have hload : memLoad (UInt256.ofNat 64) mem = p := hm.load64
  have h64 : M aw (UInt256.ofNat 64) ⟨32⟩ = aw := expandedWords64_eq hm.active
  have hp32 := uadd_word_ofNat_toNat p 32 (show p.toNat + 32 < UInt256.size by
    change _ < 2 ^ 256; omega)
  have hp64 := uadd_word_ofNat_toNat p 64 (show p.toNat + 64 < UInt256.size by
    change _ < 2 ^ 256; omega)
  have hc := slot0FieldShift 25 2 (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 200))
    (UInt256.ofNat 65535) σ ee (by native_decide) (by native_decide)
  obtain ⟨k1, C1, r1⟩ := uniswapV3Pool_block_16264 (immWords := wordsOf (immStore v)) hov rd
  simp only [uniswapV3Pool_block_16264_stack, hload, h64, modifyPositionSlotHeadMem_eq σ ee hm hb,
    signextend_idem ⟨24, by decide⟩ (UInt256.ofNat 2) _ (by decide) (by decide),
    u256_add_comm (UInt256.ofNat 64) p] at r1
  change RD (deployedRuntime v) ee g s0 ⟨16345⟩
    (UInt256.land (UInt256.ofNat 65535) (UInt256.div (solcSlotWordAt ⟨0⟩ σ ee)
      (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 200))) ::
      ⟨96⟩ :: (p + ⟨96⟩) :: ⟨65535⟩ :: ⟨32⟩ ::
      UInt256.signextend (UInt256.ofNat 2) (UInt256.div (solcSlotWordAt ⟨0⟩ σ ee)
        (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))) ::
      solcSlotWordAt ⟨0⟩ σ ee :: p :: ⟨64⟩ :: R)
    (slot0ReadHeadMem mem p σ ee) _ rdata σ k1 C1 at r1
  rw [← hc, ← slot0TickWord σ ee] at r1
  refine ⟨_, k1, C1, r1, ?_⟩
  exact activeWords_expand32
    (activeWords_expand32 (activeWords_expand32 hm.active (show p.toNat + 32 ≤ 2 ^ 200 by omega))
      (show (p + UInt256.ofNat 32).toNat + 32 ≤ 2 ^ 200 by rw [hp32]; omega))
    (show (p + UInt256.ofNat 64).toNat + 32 ≤ 2 ^ 200 by rw [hp64]; omega)

end Benchmarks.UniswapV3.Pool
