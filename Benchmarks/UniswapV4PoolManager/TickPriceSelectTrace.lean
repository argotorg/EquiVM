import Benchmarks.UniswapV4PoolManager.TickPriceWords
import Benchmarks.UniswapV4PoolManager.TickSqrtTrace
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_052

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem tickPriceSelectTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw ret sqrtPrice low high : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length + 12 ≤ 1024)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (hs : sqrtPrice.toNat < 2^160) (hh : UInt256.signextend (UInt256.ofNat 2) high = high)
    (hne : low ≠ high)
    (h : RD (deployedRuntime v) I g s0 ⟨18577⟩ (sqrtPrice :: low :: high :: ret :: R) mem aw rdata σ k C) :
    (tickPriceChoose sqrtPrice low high = none ∧ RDrev (deployedRuntime v) g s0) ∨
    (∃ tick k' C', tickPriceChoose sqrtPrice low high = some tick ∧
      RD (deployedRuntime v) I g s0 ret (tick :: R) mem aw rdata σ k' C') := by
  have hm : UInt256.land (UInt256.ofNat 1461501637330902918203684832716283019655932542975) sqrtPrice = sqrtPrice := by
    rw [u256_land_comm]
    exact u256LandMaskCleanOfToNat sqrtPrice _ rfl hs
  have rd1 := poolManagerBlocks.poolManager_block_18577 (by simp only [List.length_cons]; omega)
    (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
  simp only [poolManagerBlocks.poolManager_block_18577_stack, hm] at rd1
  have hcall := tickSqrtTrace v (by simp only [List.length_cons]; omega)
    (by rw [poolManagerPatchedValidJumps v]; jump_dest) rd1
  simp only [hh] at hcall
  rcases hcall with ⟨hb, hr⟩ | ⟨hb, k2, C2, rd2⟩
  · exact .inl ⟨by simp only [tickPriceChoose, if_neg hne, if_neg (show ¬(EVM.signed high).natAbs ≤ 887272 by omega)], hr⟩
  · let priceHi := tickSqrtPrice (EVM.signed high)
    change RD (deployedRuntime v) I g s0 ⟨18629⟩
      (priceHi :: UInt256.ofNat (2^160-1) :: sqrtPrice :: low :: high :: ret :: R) mem aw rdata σ k2 C2 at rd2
    have hmask : UInt256.land priceHi (UInt256.ofNat (2^160-1)) = priceHi :=
      u256LandMaskCleanOfToNat priceHi _ rfl (tickSqrtPrice_lt_160 hb)
    by_cases hle : priceHi.toNat ≤ sqrtPrice.toNat
    · have hc : UInt256.gt (UInt256.land priceHi (UInt256.ofNat (2^160-1))) sqrtPrice = UInt256.ofNat 0 := by
        rw [hmask]; exact ugt_zero hle
      have rd3 := poolManagerBlocks.poolManager_block_18629_fallthrough (by simp only [List.length_cons]; omega) hc rd2
      have rd4 := poolManagerBlocks.poolManager_block_18636 (by omega) hret rd3
      change (tickSqrtPrice (EVM.signed high)).toNat ≤ sqrtPrice.toNat at hle
      exact .inr ⟨high, _, _, by simp only [tickPriceChoose, if_neg hne, if_pos hb, if_pos hle], rd4⟩
    · have hc : UInt256.gt (UInt256.land priceHi (UInt256.ofNat (2^160-1))) sqrtPrice ≠ UInt256.ofNat 0 := by
        rw [hmask, ugt_one (Nat.lt_of_not_ge hle)]; decide
      have rd3 := poolManagerBlocks.poolManager_block_18629_taken (by simp only [List.length_cons]; omega) hc
        (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd2
      have rd4 := poolManagerBlocks.poolManager_block_18639 (by omega) hret rd3
      change ¬(tickSqrtPrice (EVM.signed high)).toNat ≤ sqrtPrice.toNat at hle
      exact .inr ⟨low, _, _, by simp only [tickPriceChoose, if_neg hne, if_pos hb, if_neg hle], rd4⟩

end Benchmarks.UniswapV4PoolManager
