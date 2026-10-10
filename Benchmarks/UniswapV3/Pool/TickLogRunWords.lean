import Benchmarks.UniswapV3.Pool.TickLogIterationWords

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool

def tickLogRun (r : UInt256) : Nat → UInt256
  | 0 => r
  | n + 1 => tickLogNext (tickLogRun r n)

def tickLogSquareAt (r : UInt256) (n : Nat) : UInt256 := tickLogSquare (tickLogRun r n)

def tickLogAccRun (r log : UInt256) : Nat → UInt256
  | 0 => log
  | n + 1 => tickLogAccumulate (tickLogAccRun r log n) (tickLogRun r n) (63 - n)

def tickLogCompiledRun (r : UInt256) : Nat → UInt256
  | 0 => r
  | n + 1 =>
    let square := tickLogSquare (tickLogCompiledRun r n)
    UInt256.shiftRight (UInt256.shiftRight square ⟨127⟩) (UInt256.shiftRight square ⟨255⟩)

def tickLogCompiledSquareAt (r : UInt256) (n : Nat) : UInt256 :=
  tickLogSquare (tickLogCompiledRun r n)

theorem tickLogCompiledRun_eq (r : UInt256) (n : Nat) :
    tickLogCompiledRun r n = tickLogRun r n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [tickLogCompiledRun, tickLogRun, ih, tickLogNext, tickLogScaled, tickLogDigit_eq]

theorem tickLogCompiledSquareAt_eq (r : UInt256) (n : Nat) :
    tickLogCompiledSquareAt r n = tickLogSquareAt r n := by
  rw [tickLogCompiledSquareAt, tickLogCompiledRun_eq]
  rfl

theorem tickLogRun_add (r : UInt256) (a b : Nat) :
    tickLogRun (tickLogRun r a) b = tickLogRun r (a + b) := by
  induction b with
  | zero => rfl
  | succ b ih => rw [tickLogRun, Nat.add_succ, tickLogRun, ih]

theorem tickLogSquareAt_add (r : UInt256) (a b : Nat) :
    tickLogSquareAt (tickLogRun r a) b = tickLogSquareAt r (a + b) := by
  rw [tickLogSquareAt, tickLogRun_add]
  rfl

end Benchmarks.UniswapV3.Pool
