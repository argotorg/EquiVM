import Benchmarks.UniswapV3.Pool.ModifyPositionMemory
import Benchmarks.UniswapV3.Pool.SignedWordZero
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_053

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem modifyPositionNonzeroX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p q free key : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (a : ModifyPositionArgs)
    (rd : RD (deployedRuntime v) ee g s0 ⟨16428⟩
      (key :: p :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: q :: R) mem aw rdata σ k C)
    (ha : a.Fits) (hm : HeapMemory mem aw free) (hq : ModifyPositionParamsMemory mem q a)
    (hb : q.toNat + 128 ≤ 2 ^ 200) (hov : R.length + 7 ≤ 1024) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 (if a.delta = 0 then ⟨16801⟩ else ⟨16446⟩)
      (p :: ⟨0⟩ :: ⟨0⟩ :: key :: q :: R) mem aw' rdata σ k' C' ∧
      HeapMemory mem aw' free := by
  have hqw : q.toNat + 128 < UInt256.size := by change _ < 2 ^ 256; omega
  have hq96 := uadd_word_ofNat_toNat q 96 (show q.toNat + 96 < UInt256.size by omega)
  have hm' := hm.expand32 (q + UInt256.ofNat 96) (by rw [hq96]; omega)
  have hd : UInt256.signextend (UInt256.ofNat 15)
      (memLoad (UInt256.ofNat 96 + q) mem) = EVM.wordOfInt a.delta := by
    rw [u256_add_comm, hq.load_delta hqw,
      signextend_wordOfInt ⟨128, by decide⟩ _ _ (by decide) (by decide),
      normalizeSint_eq_self ⟨128, by decide⟩ _ ha.2.2.1 ha.2.2.2]
  by_cases hz : a.delta = 0
  · have rr := uniswapV3Pool_block_16428_taken (immWords := wordsOf (immStore v)) hov
      (by rw [hd, hz]; decide)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
    simp only [uniswapV3Pool_block_16428_taken_stack, u256_add_comm (UInt256.ofNat 96) q] at rr
    rw [if_pos hz]
    exact ⟨_, _, _, rr, hm'⟩
  · have hw : EVM.wordOfInt a.delta ≠ ⟨0⟩ := fun h ↦
      hz ((wordOfInt_zero_iff_signed a.delta (by have h := ha.2.2; omega)
        (by have h := ha.2.2; omega)).mp h)
    have hc : UInt256.eq (UInt256.ofNat 0) (EVM.wordOfInt a.delta) = ⟨0⟩ :=
      uInt256_eq_zero_of_ne (fun h ↦ hw (uInt256_eq_one_eq h).symm)
    have rr := uniswapV3Pool_block_16428_fallthrough (immWords := wordsOf (immStore v)) hov
      (by rw [hd]; exact hc) rd
    simp only [uniswapV3Pool_block_16428_fallthrough_stack,
      u256_add_comm (UInt256.ofNat 96) q] at rr
    rw [if_neg hz]
    exact ⟨_, _, _, rr, hm'⟩

theorem modifyPositionRangeX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p q free key amount0 amount1 : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (a : ModifyPositionArgs) (evm : EVM.State) (upper : Bool)
    (rd : RD (deployedRuntime v) ee g s0 (if upper then ⟨16513⟩ else ⟨16446⟩)
      (p :: amount1 :: amount0 :: key :: q :: R) mem aw rdata σ k C)
    (ha : a.Fits) (hm : HeapMemory mem aw free) (hq : ModifyPositionParamsMemory mem q a)
    (hp : Slot0Memory mem p evm.accountMap evm.executionEnv)
    (hbp : p.toNat + 224 ≤ 2 ^ 200) (hbq : q.toNat + 128 ≤ 2 ^ 200)
    (hov : R.length + 8 ≤ 1024) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0
      (if slot0TickValue evm.accountMap evm.executionEnv < (if upper then a.upper else a.lower)
        then (if upper then ⟨16536⟩ else ⟨16468⟩) else (if upper then ⟨16759⟩ else ⟨16513⟩))
      (p :: amount1 :: amount0 :: key :: q :: R) mem aw' rdata σ k' C' ∧
      HeapMemory mem aw' free := by
  have hqw : q.toNat + 128 < UInt256.size := by change _ < 2 ^ 256; omega
  have hpw : p.toNat + 224 < UInt256.size := by change _ < 2 ^ 256; omega
  have hload : memLoad (UInt256.ofNat (if upper then 64 else 32) + q) mem =
      EVM.wordOfInt (if upper then a.upper else a.lower) := by
    cases upper <;> rw [u256_add_comm]
    · exact hq.load_lower hqw
    · exact hq.load_upper hqw
  have hfit : -(2 ^ 23 : Int) ≤ (if upper then a.upper else a.lower) ∧
      (if upper then a.upper else a.lower) < 2 ^ 23 := by
    cases upper
    · exact ha.1
    · exact ha.2.1
  have htfit := slot0TickValue_bounds evm.accountMap evm.executionEnv
  have hc : UInt256.slt
      (UInt256.signextend (UInt256.ofNat 2) (memLoad (UInt256.ofNat 32 + p) mem))
      (UInt256.signextend (UInt256.ofNat 2)
        (memLoad (UInt256.ofNat (if upper then 64 else 32) + q) mem)) =
      if slot0TickValue evm.accountMap evm.executionEnv < (if upper then a.upper else a.lower)
        then ⟨1⟩ else ⟨0⟩ := by
    rw [u256_add_comm (UInt256.ofNat 32) p, hp.load_tick hpw, slot0TickWord_idem, hload,
      signextend_wordOfInt ⟨24, by decide⟩ _ _ (by decide) (by decide),
      normalizeSint_eq_self ⟨24, by decide⟩ _ hfit.1 hfit.2]
    exact slt_wordOfInt _ _ (by omega) (by omega) (by omega) (by omega)
  have hqoff : (q + UInt256.ofNat (if upper then 64 else 32)).toNat =
      q.toNat + (if upper then 64 else 32) :=
    uadd_word_ofNat_toNat q _ (by cases upper <;> dsimp <;> omega)
  have hp32 := uadd_word_ofNat_toNat p 32 (show p.toNat + 32 < UInt256.size by omega)
  have hm' := (hm.expand32 (q + UInt256.ofNat (if upper then 64 else 32))
    (by rw [hqoff]; cases upper <;> dsimp <;> omega)).expand32 (p + UInt256.ofNat 32)
      (by rw [hp32]; omega)
  by_cases ht : slot0TickValue evm.accountMap evm.executionEnv < (if upper then a.upper else a.lower)
  · rw [if_pos ht]
    rw [if_pos ht] at hc
    cases upper <;> simp only [Bool.false_eq_true, if_false, if_true] at hc hm' rd ⊢
    · have rr := uniswapV3Pool_block_16446_fallthrough (immWords := wordsOf (immStore v)) hov
        (by rw [hc]; rfl) rd
      simp only [u256_add_comm (UInt256.ofNat 32) q, u256_add_comm (UInt256.ofNat 32) p] at rr
      exact ⟨_, _, _, rr, hm'⟩
    · have rr := uniswapV3Pool_block_16513_fallthrough (immWords := wordsOf (immStore v)) hov
        (by rw [hc]; rfl) rd
      simp only [u256_add_comm (UInt256.ofNat 64) q, u256_add_comm (UInt256.ofNat 32) p] at rr
      exact ⟨_, _, _, rr, hm'⟩
  · rw [if_neg ht]
    rw [if_neg ht] at hc
    cases upper <;> simp only [Bool.false_eq_true, if_false, if_true] at hc hm' rd ⊢
    · have rr := uniswapV3Pool_block_16446_taken (immWords := wordsOf (immStore v)) hov
        (by rw [hc]; decide)
        (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
      simp only [u256_add_comm (UInt256.ofNat 32) q, u256_add_comm (UInt256.ofNat 32) p] at rr
      exact ⟨_, _, _, rr, hm'⟩
    · have rr := uniswapV3Pool_block_16513_taken (immWords := wordsOf (immStore v)) hov
        (by rw [hc]; decide)
        (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
      simp only [u256_add_comm (UInt256.ofNat 64) q, u256_add_comm (UInt256.ofNat 32) p] at rr
      exact ⟨_, _, _, rr, hm'⟩

theorem modifyPositionReturnX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p q key amount0 amount1 ret : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨16801⟩
      (p :: amount1 :: amount0 :: key :: q :: ret :: R) mem aw rdata σ k C)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hov : R.length + 6 ≤ 1024) :
    RD (deployedRuntime v) ee g s0 ret (amount1 :: amount0 :: key :: R)
      mem aw rdata σ (k + 8) (C + 25) :=
  uniswapV3Pool_block_16801 (immWords := wordsOf (immStore v)) hov hret rd

end Benchmarks.UniswapV3.Pool
