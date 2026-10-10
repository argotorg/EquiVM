import Benchmarks.UniswapV3.Pool.ModifyPositionGuardTrace
import Benchmarks.UniswapV3.Pool.SignedAmountDeltaEntryTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def modifyPositionOutsideEntry (second : Bool) : UInt256 :=
  if second then ⟨16759⟩ else ⟨16468⟩
def modifyPositionOutsideLowerReturn (second : Bool) : UInt256 :=
  if second then ⟨16775⟩ else ⟨16483⟩
def modifyPositionOutsideUpperReturn (second : Bool) : UInt256 :=
  if second then ⟨16788⟩ else ⟨16496⟩
def modifyPositionOutsideAmountReturn (second : Bool) : UInt256 :=
  if second then ⟨16798⟩ else ⟨16506⟩

theorem modifyPositionOutsideLowerEntryX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p q key free : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (a : ModifyPositionArgs) (second : Bool)
    (rd : RD (deployedRuntime v) ee g s0 (modifyPositionOutsideEntry second)
      (p :: ⟨0⟩ :: ⟨0⟩ :: key :: q :: R) mem aw rdata σ k C)
    (hm : HeapMemory mem aw free) (hq : ModifyPositionParamsMemory mem q a)
    (hb : q.toNat + 128 ≤ 2 ^ 200) (hov : R.length + 9 ≤ 1024) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 ⟨11629⟩
      (EVM.wordOfInt a.lower :: modifyPositionOutsideLowerReturn second ::
        modifyPositionOutsideAmountReturn second :: p :: ⟨0⟩ :: ⟨0⟩ :: key :: q :: R)
      mem aw' rdata σ k' C' ∧ HeapMemory mem aw' free := by
  have hqw : q.toNat + 128 < UInt256.size := by change _ < 2 ^ 256; omega
  have hq32 := uadd_word_ofNat_toNat q 32 (show q.toNat + 32 < UInt256.size by omega)
  have hm' := hm.expand32 (q + UInt256.ofNat 32) (by rw [hq32]; omega)
  cases second
  · have rr := uniswapV3Pool_block_16468 (immWords := wordsOf (immStore v)) hov
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
    simp only [uniswapV3Pool_block_16468_stack, u256_add_comm (UInt256.ofNat 32) q,
      hq.load_lower hqw] at rr
    exact ⟨_, _, _, rr, hm'⟩
  · have rr := uniswapV3Pool_block_16759 (immWords := wordsOf (immStore v)) hov
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
    simp only [uniswapV3Pool_block_16759_stack, u256_add_comm (UInt256.ofNat 32) q,
      hq.load_lower hqw] at rr
    exact ⟨_, _, _, rr, hm'⟩

theorem modifyPositionOutsideUpperEntryX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p q key free sqrt : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (a : ModifyPositionArgs) (second : Bool)
    (rd : RD (deployedRuntime v) ee g s0 (modifyPositionOutsideLowerReturn second)
      (sqrt :: modifyPositionOutsideAmountReturn second :: p :: ⟨0⟩ :: ⟨0⟩ :: key :: q :: R)
      mem aw rdata σ k C)
    (hm : HeapMemory mem aw free) (hq : ModifyPositionParamsMemory mem q a)
    (hb : q.toNat + 128 ≤ 2 ^ 200) (hov : R.length + 10 ≤ 1024) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 ⟨11629⟩
      (EVM.wordOfInt a.upper :: modifyPositionOutsideUpperReturn second :: sqrt ::
        modifyPositionOutsideAmountReturn second :: p :: ⟨0⟩ :: ⟨0⟩ :: key :: q :: R)
      mem aw' rdata σ k' C' ∧ HeapMemory mem aw' free := by
  have hqw : q.toNat + 128 < UInt256.size := by change _ < 2 ^ 256; omega
  have hq64 := uadd_word_ofNat_toNat q 64 (show q.toNat + 64 < UInt256.size by omega)
  have hm' := hm.expand32 (q + UInt256.ofNat 64) (by rw [hq64]; omega)
  cases second
  · have rr := uniswapV3Pool_block_16483 (immWords := wordsOf (immStore v)) hov
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
    simp only [uniswapV3Pool_block_16483_stack, u256_add_comm (UInt256.ofNat 64) q,
      hq.load_upper hqw] at rr
    exact ⟨_, _, _, rr, hm'⟩
  · have rr := uniswapV3Pool_block_16775 (immWords := wordsOf (immStore v)) hov
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
    simp only [uniswapV3Pool_block_16775_stack, u256_add_comm (UInt256.ofNat 64) q,
      hq.load_upper hqw] at rr
    exact ⟨_, _, _, rr, hm'⟩

theorem modifyPositionOutsideAmountEntryX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p q key free sqrtA sqrtB : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (a : ModifyPositionArgs) (second : Bool)
    (rd : RD (deployedRuntime v) ee g s0 (modifyPositionOutsideUpperReturn second)
      (sqrtB :: sqrtA :: modifyPositionOutsideAmountReturn second ::
        p :: ⟨0⟩ :: ⟨0⟩ :: key :: q :: R) mem aw rdata σ k C)
    (hm : HeapMemory mem aw free) (hq : ModifyPositionParamsMemory mem q a)
    (hb : q.toNat + 128 ≤ 2 ^ 200) (hov : R.length + 10 ≤ 1024) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 (UInt256.ofNat (signedAmountDeltaEntry second))
      (EVM.wordOfInt a.delta :: sqrtB :: sqrtA :: modifyPositionOutsideAmountReturn second ::
        p :: ⟨0⟩ :: ⟨0⟩ :: key :: q :: R) mem aw' rdata σ k' C' ∧ HeapMemory mem aw' free := by
  have hqw : q.toNat + 128 < UInt256.size := by change _ < 2 ^ 256; omega
  have hq96 := uadd_word_ofNat_toNat q 96 (show q.toNat + 96 < UInt256.size by omega)
  have hm' := hm.expand32 (q + UInt256.ofNat 96) (by rw [hq96]; omega)
  cases second
  · have rr := uniswapV3Pool_block_16496 (immWords := wordsOf (immStore v)) hov
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
    simp only [uniswapV3Pool_block_16496_stack, u256_add_comm (UInt256.ofNat 96) q,
      hq.load_delta hqw] at rr
    exact ⟨_, _, _, rr, hm'⟩
  · have rr := uniswapV3Pool_block_16788 (immWords := wordsOf (immStore v)) hov
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
    simp only [uniswapV3Pool_block_16788_stack, u256_add_comm (UInt256.ofNat 96) q,
      hq.load_delta hqw] at rr
    exact ⟨_, _, _, rr, hm'⟩

theorem modifyPositionOutsideDoneX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p q key amount : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (second : Bool)
    (rd : RD (deployedRuntime v) ee g s0 (modifyPositionOutsideAmountReturn second)
      (amount :: p :: ⟨0⟩ :: ⟨0⟩ :: key :: q :: R) mem aw rdata σ k C)
    (hov : R.length + 6 ≤ 1024) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 ⟨16801⟩
      (p :: (if second then amount else ⟨0⟩) :: (if second then ⟨0⟩ else amount) :: key :: q :: R)
      mem aw rdata σ k' C' := by
  cases second
  · exact ⟨_, _, uniswapV3Pool_block_16506 (immWords := wordsOf (immStore v)) (by evm_ov)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd⟩
  · exact ⟨_, _, uniswapV3Pool_block_16798 (immWords := wordsOf (immStore v)) (by evm_ov) rd⟩

end Benchmarks.UniswapV3.Pool
