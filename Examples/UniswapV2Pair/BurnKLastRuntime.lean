import Examples.UniswapV2Pair.Routines
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace UniswapV2Pair
set_option maxRecDepth 2000000


set_option maxHeartbeats 1000000 in
theorem RD.uniswapBurnAfterUpdateFeeOff {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {supply fee aw : UInt256} {R : List UInt256} {mem rdata : ByteArray} {k C : Nat}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (rd : RD uniswapV2PairBytecode I g s0 ⟨4885⟩ (supply :: fee :: R) mem aw rdata acc k C)
    (hfee : fee = ⟨0⟩) (hov : R.length + 4 ≤ 1024) :
    ∃ k' C', RD uniswapV2PairBytecode I g s0 ⟨4933⟩ (supply :: fee :: R) mem aw rdata acc k' C' := by
  have rd4891 := evm_run rd with [jumpdest, dup2, iszero, push2 ⟨4933⟩]
  rw [hfee, show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ by native_decide] at rd4891
  subst fee
  exact ⟨_, _, evm_run rd4891 with [jumpiT one_ne_zero_uint (by jump_dest)]⟩

set_option maxHeartbeats 1000000 in
theorem RD.uniswapBurnAfterUpdateFeeOn {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {supply fee aw : UInt256} {R : List UInt256} {mem rdata : ByteArray} {k C : Nat}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (rd : RD uniswapV2PairBytecode I g s0 ⟨4885⟩ (supply :: fee :: R) mem aw rdata (cA, σ) k C)
    (hfee : fee ≠ ⟨0⟩)
    (hfit : (UInt256.land (uniswapSlotWord ⟨8⟩ σ I) reserve112Mask).toNat *
      (UInt256.land (UInt256.div (uniswapSlotWord ⟨8⟩ σ I) reserve112Shift) reserve112Mask).toNat < UInt256.size)
    (hperm : I.perm = true) (hov : R.length + 11 ≤ 1024) :
    ∃ k' C', RD uniswapV2PairBytecode I g s0 ⟨4933⟩ (supply :: fee :: R) mem aw rdata
      (cA, sstoreAccountMap I.codeOwner σ ⟨11⟩
        (UInt256.mul (UInt256.land (uniswapSlotWord ⟨8⟩ σ I) reserve112Mask)
          (UInt256.land (UInt256.div (uniswapSlotWord ⟨8⟩ σ I) reserve112Shift) reserve112Mask))) k' C' := by
  let slot8 := uniswapSlotWord ⟨8⟩ σ I
  let packedReserve0 := UInt256.land slot8 reserve112Mask
  let packedReserve1 := UInt256.land (UInt256.div slot8 reserve112Shift) reserve112Mask
  have rd4891 := evm_run rd with [jumpdest, dup2, iszero, push2 ⟨4933⟩]
  rw [isZero_eq_zero_of_ne hfee] at rd4891
  have rd4894 := evm_run rd4891 with [jumpiNT (by native_decide), push1 ⟨8⟩]
  obtain ⟨k4895, C4895, rd4895₀⟩ := rd4894.sload (by native_decide) (by evm_ov)
  have rd4895 : RD uniswapV2PairBytecode I g s0 ⟨4895⟩
      (slot8 :: supply :: fee :: R) mem aw rdata (cA, σ) k4895 C4895 := by
    simpa only [slot8, uniswapSlotWord] using rd4895₀
  have rd4928 := evm_run rd4895 with [
    push2 ⟨4929⟩, swap1, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨112⟩, shl, sub, dup1, dup3,
    and, swap2, push1 ⟨1⟩, push1 ⟨112⟩, shl, swap1, div, and, push4 ⟨0xffffffff⟩,
    push2 ⟨6780⟩, and]
  rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨112⟩) ⟨1⟩ = reserve112Mask from rfl,
    show UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨112⟩ = reserve112Shift from rfl,
    show UInt256.land (⟨6780⟩ : UInt256) ⟨0xffffffff⟩ = ⟨6780⟩ by native_decide] at rd4928
  have rd6780 := rd4928.jump (by native_decide) (by jump_dest) (by evm_ov)
  obtain ⟨_, _, rd4929⟩ := RD.uniswapSafeMathMulSuccess
    (a := packedReserve0) (b := packedReserve1) rd6780 hfit (by jump_dest)
    (by simp only [List.length_cons]; omega)
  have rd4932 := evm_run rd4929 with [jumpdest, push1 ⟨11⟩]
  obtain ⟨_, _, rd4933⟩ := rd4932.sstore hperm (by native_decide) (by evm_ov)
  exact ⟨_, _, rd4933⟩

end UniswapV2Pair
