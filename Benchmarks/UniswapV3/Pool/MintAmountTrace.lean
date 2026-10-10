import Benchmarks.UniswapV3.Pool.MintLockTrace
import Reasoning.ExternalCall

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem mintLockAmountX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw len start amount : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (evm : EVM.State)
    (hs : SourceState s0 ee σ evm)
    (rd : RD (deployedRuntime v) ee g s0 ⟨5805⟩
      (⟨0⟩ :: ⟨0⟩ :: len :: start :: amount :: R) mem aw rdata σ k C)
    (ha : amount.toNat < 2 ^ 128) (hperm : ee.perm = true) (hov : R.length + 9 ≤ 1024) :
    (RDrev (deployedRuntime v) g s0 ∧ amount = ⟨0⟩) ∨
      (0 < amount.toNat ∧ ∃ k' C', RD (deployedRuntime v) ee g s0 ⟨5837⟩
        (⟨0⟩ :: ⟨0⟩ :: len :: start :: amount :: R) mem aw rdata
        (storeSlot0Unlocked evm false).accountMap k' C') := by
  have hclean : UInt256.land amount
      (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128))
        (UInt256.ofNat 1)) = amount :=
    u256LandMaskCleanOfToNat amount _ (bits := 128) (by native_decide) ha
  have hs' := hs.readModifyWrite ⟨0⟩ (fun w ↦ slot0UnlockedWord w false)
  change SourceState s0 ee _ (storeSlot0Unlocked evm false) at hs'
  simp only [slot0UnlockedWord_false] at hs'
  by_cases hz : amount = ⟨0⟩
  · obtain ⟨k1, C1, r1⟩ := uniswapV3Pool_block_5805_fallthrough
      (immWords := wordsOf (immStore v)) hov hperm (by rw [hclean]; exact hz) rd
    exact Or.inl ⟨uniswapV3Pool_block_5833 (immWords := wordsOf (immStore v))
      (by evm_ov) r1, hz⟩
  · have hn : amount.toNat ≠ 0 := fun h ↦ hz (u256_inj h)
    obtain ⟨k1, C1, r1⟩ := uniswapV3Pool_block_5805_taken
      (immWords := wordsOf (immStore v)) hov hperm (by rw [hclean]; exact hz)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
    have hstore := hs'.accounts
    change sstoreAccountMap ee.codeOwner σ (UInt256.ofNat 0)
      (UInt256.land (UInt256.lnot (UInt256.shiftLeft (UInt256.ofNat 255) (UInt256.ofNat 240)))
        (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256)
          (fun ac ↦ ac.storage.getD (UInt256.ofNat 0) (⟨0⟩ : UInt256)))) =
        (storeSlot0Unlocked evm false).accountMap at hstore
    rw [hstore] at r1
    exact Or.inr ⟨by omega, k1, C1, r1⟩

end Benchmarks.UniswapV3.Pool
