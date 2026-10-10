import Benchmarks.UniswapV3.Pool.PackedLockStatic
import Benchmarks.UniswapV3.Pool.Slot0Storage
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_031

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

local macro "pool_burn_decode" "(" v:term "," pc:term "," byte:term ","
    instr:term "," arg:term ")" : tactic =>
  `(tactic| immutable_decode(immutableLayout, uniswapV3PoolBytecode, wordsOf (immStore $v),
    (UInt256.ofNat $pc), (UInt8.ofNat $byte), $instr, $arg,
    immutableLayout_inBounds, immutableTemplate_size64))

theorem burnLockStaticX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨9648⟩ R mem aw rdata σ k C)
    (hperm : ee.perm = false) (hov : R.length + 4 ≤ 1024) : RDstatic (deployedRuntime v) g s0 := by
  exact packedLockStaticX (pc := ⟨9648⟩) ⟨0⟩ ⟨255⟩ ⟨240⟩ true
    (by pool_burn_decode(v, 9648, 91, .JUMPDEST, none))
    (by pool_burn_decode(v, 9649, 96, .Push .PUSH1, some (⟨0⟩, 1)))
    (by pool_burn_decode(v, 9651, 128, .DUP1, none))
    (by pool_burn_decode(v, 9652, 84, .SLOAD, none))
    (by pool_burn_decode(v, 9653, 96, .Push .PUSH1, some (⟨255⟩, 1)))
    (by pool_burn_decode(v, 9655, 96, .Push .PUSH1, some (⟨240⟩, 1)))
    (by pool_burn_decode(v, 9657, 27, .SHL, none))
    (by pool_burn_decode(v, 9658, 25, .NOT, none))
    (by pool_burn_decode(v, 9659, 22, .AND, none))
    (by pool_burn_decode(v, 9660, 129, .DUP2, none))
    (by pool_burn_decode(v, 9661, 85, .SSTORE, none)) rd hperm hov

theorem burnReadLockX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨9577⟩ R mem aw rdata σ k C)
    (hov : R.length + 7 ≤ 1024) :
    (RDrev (deployedRuntime v) g s0 ∧ slot0FieldWord 30 1 σ ee = ⟨0⟩) ∨
      (slot0FieldWord 30 1 σ ee ≠ ⟨0⟩ ∧ ∃ k' C', RD (deployedRuntime v) ee g s0 ⟨9648⟩
        (⟨0⟩ :: ⟨0⟩ :: R) mem aw rdata σ k' C') := by
  have hfield : UInt256.land (UInt256.ofNat 255)
      (UInt256.div (σ.get? ee.codeOwner |>.option (⟨0⟩ : UInt256)
        (fun ac ↦ ac.storage.getD (UInt256.ofNat 0) (⟨0⟩ : UInt256)))
        (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 240))) = slot0FieldWord 30 1 σ ee :=
    (slot0FieldWord_unlocked_evm σ ee).symm
  by_cases hlocked : slot0FieldWord 30 1 σ ee = ⟨0⟩
  · obtain ⟨kr, Cr, rr⟩ := uniswapV3Pool_block_9577_fallthrough (immWords := wordsOf (immStore v))
      (by omega) (by rw [hfield]; exact hlocked) rd
    exact Or.inl ⟨uniswapV3Pool_block_9598 (immWords := wordsOf (immStore v))
      (by change R.length + 2 + 5 ≤ 1024; omega) rr, hlocked⟩
  · exact Or.inr ⟨hlocked, uniswapV3Pool_block_9577_taken (immWords := wordsOf (immStore v))
      (by omega) (by rw [hfield]; exact hlocked)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd⟩

end Benchmarks.UniswapV3.Pool
