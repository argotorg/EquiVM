import Benchmarks.UniswapV3.Pool.BitMsbSource
import Benchmarks.UniswapV3.Pool.BitMsbStepTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool

def bitMsbRun (state : Nat × UInt256) (i : Nat) : Nat → Nat × UInt256
  | 0 => state
  | n + 1 => bitMsbRun (tickLogMsbStep state (2 ^ (7 - i))) (i + 1) n

theorem bitMsbRun_prefix (x : UInt256) : bitMsbRun (0, x) 0 7 = bitMsbPrefix x := by
  simp only [bitMsbRun, bitMsbPrefix, bitMsbPrefixBits, List.foldl_cons, List.foldl_nil,
    Nat.reduceAdd, Nat.reduceSub, Nat.reducePow]

theorem bitMsbFoldX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (state : Nat × UInt256)
    (i n : Nat) (hi : i + n ≤ 7)
    (rd : RD (deployedRuntime v) ee g s0 (bitMsbPC i)
      (UInt256.ofNat state.1 :: state.2 :: R) mem aw rdata σ k C)
    (hov : R.length + 4 ≤ 1024) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 (bitMsbPC (i + n))
      (UInt256.ofNat (bitMsbRun state i n).1 :: (bitMsbRun state i n).2 :: R)
        mem aw rdata σ k' C' := by
  induction n generalizing state i k C with
  | zero => exact RD.pack rd
  | succ n ih =>
    obtain ⟨k1, C1, r1⟩ := bitMsbStepX state ⟨i, by omega⟩ rd hov
    have ht := ih (tickLogMsbStep state (2 ^ (7 - i))) (i + 1) (by omega) r1
    rw [show i + 1 + n = i + (n + 1) by omega] at ht
    exact ht

end Benchmarks.UniswapV3.Pool
