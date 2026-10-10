import Benchmarks.UniswapV3.Pool.BitLsbStepTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool

def bitLsbRun (state : Nat × UInt256) (i : Nat) : Nat → Nat × UInt256
  | 0 => state
  | n + 1 => bitLsbRun (bitLsbStep state (2 ^ (6 - i))) (i + 1) n

def bitLsbBudget (i : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => 2 ^ (6 - i) + bitLsbBudget (i + 1) n

theorem bitLsbRun_prefix (x : UInt256) :
    bitLsbRun (bitLsbStep (255, x) 128) 0 6 = bitLsbPrefix x := by
  simp only [bitLsbRun, bitLsbPrefix, tickLogMsbBits, List.take, List.foldl_cons, List.foldl_nil,
    Nat.reduceAdd, Nat.reduceSub, Nat.reducePow]

theorem bitLsbFoldX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (state : Nat × UInt256)
    (i n : Nat) (hi : i + n ≤ 6) (hb : state.1 < 256)
    (hle : bitLsbBudget i n ≤ state.1)
    (rd : RD (deployedRuntime v) ee g s0 (bitLsbPC i)
      (UInt256.ofNat state.1 :: state.2 :: R) mem aw rdata σ k C)
    (hov : R.length + 4 ≤ 1024) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 (bitLsbPC (i + n))
      (UInt256.ofNat (bitLsbRun state i n).1 :: (bitLsbRun state i n).2 :: R)
        mem aw rdata σ k' C' := by
  induction n generalizing state i k C with
  | zero => exact RD.pack rd
  | succ n ih =>
    simp only [bitLsbBudget] at hle
    have hs := bitLsbStep_bounds state (2 ^ (6 - i))
    obtain ⟨k1, C1, r1⟩ := bitLsbStepX state ⟨i, by omega⟩ hb
      (by change 2 ^ (6 - i) ≤ state.1; omega) rd hov
    have ht := ih (bitLsbStep state (2 ^ (6 - i))) (i + 1) (by omega) (by omega) (by omega) r1
    rw [show i + 1 + n = i + (n + 1) by omega] at ht
    exact ht

end Benchmarks.UniswapV3.Pool
