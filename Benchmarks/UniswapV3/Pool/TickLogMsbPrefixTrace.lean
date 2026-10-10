import Benchmarks.UniswapV3.Pool.TickLogMsbWords
import Benchmarks.UniswapV3.Pool.TickLogStartTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem tickLogRatioClean (price : UInt256) :
    UInt256.land (UInt256.shiftLeft price (UInt256.ofNat 32))
      (UInt256.ofNat 6277101735386680763835789423207666416102355444459739545600) =
      tickLogRatio (tickLogPrice price) := by
  rw [show UInt256.ofNat 6277101735386680763835789423207666416102355444459739545600 =
    UInt256.shiftLeft (UInt256.ofNat (2 ^ 160 - 1)) (UInt256.ofNat 32) by decide]
  exact wordShiftLeft_land _ _ _ (by decide)

def tickLogMsbPrefixStack (ratio price : UInt256) (R : List UInt256) : List UInt256 :=
  UInt256.gt (tickLogMsbScan ratio 6) (UInt256.ofNat 3) ::
    tickLogMsbPart ratio 5 :: tickLogMsbScan ratio 6 :: tickLogMsbPart ratio 4 ::
    tickLogMsbPart ratio 3 :: tickLogMsbPart ratio 2 :: tickLogMsbPart ratio 1 ::
    tickLogMsbPart ratio 0 :: ratio :: ⟨0⟩ :: price :: R

def tickLogMsbCompiledChoice (r : UInt256) (p : Nat) : UInt256 :=
  UInt256.shiftLeft (UInt256.gt r (UInt256.ofNat (2 ^ (2 ^ p) - 1))) (UInt256.ofNat p)

def tickLogMsbCompiledScan (ratio : UInt256) : Nat → UInt256
  | 0 => ratio
  | i + 1 => UInt256.shiftRight (tickLogMsbCompiledScan ratio i)
      (tickLogMsbCompiledChoice (tickLogMsbCompiledScan ratio i) (7 - i))

def tickLogMsbCompiledPart (ratio : UInt256) (i : Nat) : UInt256 :=
  tickLogMsbCompiledChoice (tickLogMsbCompiledScan ratio i) (7 - i)

theorem tickLogMsbCompiledScan_eq (ratio : UInt256) (i : Nat) (hi : i ≤ 8) :
    tickLogMsbCompiledScan ratio i = tickLogMsbScan ratio i := by
  induction i with
  | zero => rfl
  | succ i ih =>
    simp only [tickLogMsbCompiledScan, tickLogMsbScan]
    rw [ih (by omega)]
    rw [tickLogMsbCompiledChoice, tickLogMsbChoice_eq _ _ (by omega)]

theorem tickLogMsbCompiledPart_eq (ratio : UInt256) (i : Nat) (hi : i ≤ 7) :
    tickLogMsbCompiledPart ratio i = tickLogMsbPart ratio i := by
  rw [tickLogMsbCompiledPart, tickLogMsbCompiledScan_eq _ _ (by omega)]
  exact tickLogMsbChoice_eq _ _ (by omega)

def tickLogMsbCompiledStack (ratio price : UInt256) (R : List UInt256) : List UInt256 :=
  UInt256.gt (tickLogMsbCompiledScan ratio 6) (UInt256.ofNat 3) ::
    tickLogMsbCompiledPart ratio 5 :: tickLogMsbCompiledScan ratio 6 ::
    tickLogMsbCompiledPart ratio 4 :: tickLogMsbCompiledPart ratio 3 ::
    tickLogMsbCompiledPart ratio 2 :: tickLogMsbCompiledPart ratio 1 ::
    tickLogMsbCompiledPart ratio 0 :: ratio :: ⟨0⟩ :: price :: R

theorem tickLogMsbCompiledStack_eq (ratio price : UInt256) (R : List UInt256) :
    tickLogMsbCompiledStack ratio price R = tickLogMsbPrefixStack ratio price R := by
  simp only [tickLogMsbCompiledStack, tickLogMsbPrefixStack,
    tickLogMsbCompiledScan_eq ratio 6 (by decide),
    tickLogMsbCompiledPart_eq ratio 5 (by decide),
    tickLogMsbCompiledPart_eq ratio 4 (by decide),
    tickLogMsbCompiledPart_eq ratio 3 (by decide),
    tickLogMsbCompiledPart_eq ratio 2 (by decide),
    tickLogMsbCompiledPart_eq ratio 1 (by decide),
    tickLogMsbCompiledPart_eq ratio 0 (by decide)]

theorem tickLogMsbBlockStack_eq (price : UInt256) (R : List UInt256) :
    uniswapV3Pool_block_14102_stack (x0 := ⟨0⟩) (x1 := price) (R := R) =
      tickLogMsbCompiledStack
        (UInt256.land (UInt256.shiftLeft price (UInt256.ofNat 32))
          (UInt256.ofNat 6277101735386680763835789423207666416102355444459739545600)) price R := by
  rfl

theorem tickLogMsbPrefixX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw price : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨14102⟩ (⟨0⟩ :: price :: R) mem aw rdata σ k C)
    (hov : R.length + 12 ≤ 1024) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 ⟨14216⟩
      (tickLogMsbPrefixStack (tickLogRatio (tickLogPrice price)) price R) mem aw rdata σ k' C' := by
  have rout := uniswapV3Pool_block_14102 (immWords := wordsOf (immStore v)) (by evm_ov) rd
  refine ⟨k + 64, C + 190, ?_⟩
  simpa only [tickLogMsbBlockStack_eq, tickLogRatioClean, tickLogMsbCompiledStack_eq] using rout

end Benchmarks.UniswapV3.Pool
