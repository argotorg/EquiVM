import Benchmarks.UniswapV3.Pool.InitializeSlot0Word
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_033

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 1000

theorem initializeFinishX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 evm : EVM.State} {k C : Nat} {aw price tick ret : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨10817⟩
      (⟨1⟩ :: ⟨1⟩ :: ⟨0⟩ :: ⟨0⟩ :: tick :: price :: ret :: R) mem aw rdata σ k C)
    (hs : SourceState s0 ee σ evm) (hperm : ee.perm = true) (hp : price.toNat < 2 ^ 160)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hov : R.length + 20 ≤ 1024) :
    ∃ k' C' mem' aw', SourceState s0 ee (initializeSlot0State evm price (tickLogTick tick)).accountMap
        (initializeSlot0State evm price (tickLogTick tick)) ∧
      RD (deployedRuntime v) ee g s0 ret R mem' aw' rdata
        (initializeSlot0State evm price (tickLogTick tick)).accountMap k' C' := by
  have hprice : UInt256.land price
      (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) =
      price := u256LandMaskCleanOfToNat _ _ (by decide) hp
  have rbuild := uniswapV3Pool_block_10817 (immWords := wordsOf (immStore v)) (by evm_ov) rd
  simp only [uniswapV3Pool_block_10817_stack, hprice,
    show UInt256.land (⟨1⟩ : UInt256) (UInt256.ofNat 65535) = ⟨1⟩ by decide,
    show UInt256.land (UInt256.ofNat 65535) (⟨1⟩ : UInt256) = ⟨1⟩ by decide] at rbuild
  obtain ⟨k', C', rpacked⟩ := uniswapV3Pool_block_10896 (immWords := wordsOf (immStore v))
    (by evm_ov) rbuild
  simp only [uniswapV3Pool_block_10896_stack,
    signextend_idem ⟨24, by decide⟩ (UInt256.ofNat 2) tick (by decide) (by decide)] at rpacked
  obtain ⟨k'', C'', rout⟩ := uniswapV3Pool_block_11030 (immWords := wordsOf (immStore v))
    (by evm_ov) hperm hret rpacked
  change RD (deployedRuntime v) ee g s0 ret R _ _ rdata
    (sstoreAccountMap ee.codeOwner σ ⟨0⟩
      (initializeCompiledWord (solcSlotWordAt ⟨0⟩ σ ee) price tick)) k'' C'' at rout
  rw [initializeCompiledWord_eq _ _ _ hp] at rout
  have hs' := SourceState.initializeSlot0 hs price (tickLogTick tick)
  rw [hs'.accounts] at rout
  exact ⟨_, _, _, _, ⟨hs'.world, hs'.env, rfl⟩, rout⟩

end Benchmarks.UniswapV3.Pool
