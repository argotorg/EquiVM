import Reasoning.ExternalCall
import Benchmarks.UniswapV3.Pool.PackedLockStatic
import Benchmarks.UniswapV3.Pool.SwapModel
import Benchmarks.UniswapV3.Pool.Slot0Memory
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_012

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

local macro "pool_swap_decode" "(" v:term "," pc:term "," byte:term ","
    instr:term "," arg:term ")" : tactic =>
  `(tactic| immutable_decode(immutableLayout, uniswapV3PoolBytecode, wordsOf (immStore $v),
    (UInt256.ofNat $pc), (UInt8.ofNat $byte), $instr, $arg,
    immutableLayout_inBounds, immutableTemplate_size64))

theorem swapLockStaticX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨2723⟩ R mem aw rdata σ k C)
    (hperm : ee.perm = false) (hov : R.length + 4 ≤ 1024) :
    RDstatic (deployedRuntime v) g s0 := by
  exact packedLockStaticX (pc := ⟨2723⟩) ⟨0⟩ ⟨255⟩ ⟨240⟩ true
    (by pool_swap_decode(v, 2723, 91, .JUMPDEST, none))
    (by pool_swap_decode(v, 2724, 96, .Push .PUSH1, some (⟨0⟩, 1)))
    (by pool_swap_decode(v, 2726, 128, .DUP1, none))
    (by pool_swap_decode(v, 2727, 84, .SLOAD, none))
    (by pool_swap_decode(v, 2728, 96, .Push .PUSH1, some (⟨255⟩, 1)))
    (by pool_swap_decode(v, 2730, 96, .Push .PUSH1, some (⟨240⟩, 1)))
    (by pool_swap_decode(v, 2732, 27, .SHL, none))
    (by pool_swap_decode(v, 2733, 25, .NOT, none))
    (by pool_swap_decode(v, 2734, 22, .AND, none))
    (by pool_swap_decode(v, 2735, 129, .DUP2, none))
    (by pool_swap_decode(v, 2736, 85, .SSTORE, none)) rd hperm hov

theorem swapLockX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p x0 x1 x2 x3 x4 x5 x6 : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (zero : Bool) (evm : EVM.State)
    (rd : RD (deployedRuntime v) ee g s0 ⟨2723⟩
      (x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: zero.toUInt256 :: R) mem aw rdata σ k C)
    (hs : SourceState s0 ee σ evm) (hm : HeapMemory mem aw p)
    (hperm : ee.perm = true) (hov : R.length + 13 ≤ 1024) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 (if zero then ⟨2770⟩ else ⟨2754⟩)
      (p :: p :: ⟨0⟩ :: x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: zero.toUInt256 :: R)
      (writeWord mem 64 (p + UInt256.ofNat 192)) aw rdata
      (storeSlot0Unlocked evm false).accountMap k' C' := by
  have hload : memLoad (UInt256.ofNat 64) mem = p := hm.load64
  have h64 : M aw (UInt256.ofNat 64) ⟨32⟩ = aw := expandedWords64_eq hm.active
  have hmap := storeSlot0Unlocked_accountMap evm false
  rw [slot0UnlockedWord_false, ← hs.accounts, hs.env] at hmap
  change (storeSlot0Unlocked evm false).accountMap =
    sstoreAccountMap ee.codeOwner σ (UInt256.ofNat 0)
      (UInt256.land (UInt256.lnot (UInt256.shiftLeft (UInt256.ofNat 255)
        (UInt256.ofNat 240))) (solcSlotWordAt ⟨0⟩ σ ee)) at hmap
  cases zero
  · obtain ⟨kr, Cr, rr⟩ := uniswapV3Pool_block_2723_fallthrough
      (immWords := wordsOf (immStore v)) hov hperm rfl rd
    refine ⟨kr, Cr, ?_⟩
    simpa only [uniswapV3Pool_block_2723_fallthrough_stack,
      uniswapV3Pool_block_2723_fallthrough_memory, hload, h64, hmap,
      Reasoning.Theory.writeWord] using rr
  · obtain ⟨kr, Cr, rr⟩ := uniswapV3Pool_block_2723_taken
      (immWords := wordsOf (immStore v)) hov hperm (by decide)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
    refine ⟨kr, Cr, ?_⟩
    simpa only [uniswapV3Pool_block_2723_taken_stack,
      uniswapV3Pool_block_2723_taken_memory, hload, h64, hmap,
      Reasoning.Theory.writeWord] using rr

end Benchmarks.UniswapV3.Pool
