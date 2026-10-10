import Benchmarks.UniswapV4PoolManager.NarrowWords
import Benchmarks.UniswapV4PoolManager.SignedComparison

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def tickMinWord : UInt256 := UInt256.ofNat (2^256-887272)
def tickMaxWord : UInt256 := UInt256.ofNat 887272

theorem tickMinWord_signed : EVM.signed tickMinWord = -887272 := by decide +kernel
theorem tickMaxWord_signed : EVM.signed tickMaxWord = 887272 := by decide +kernel
theorem tickMinWord_canonical : int24Canonical tickMinWord := by decide +kernel
theorem tickMaxWord_canonical : int24Canonical tickMaxWord := by decide +kernel

def tickClampLower (tick : Int) : Int := if tick ≤ -887272 then -887272 else tick
def tickClamp (tick : Int) : Int := if tickClampLower tick ≥ 887272 then 887272 else tickClampLower tick

def tickClampLowerWord (tick : UInt256) : UInt256 :=
  if EVM.signed (UInt256.signextend (UInt256.ofNat 2) tick) ≤ -887272 then tickMinWord
  else UInt256.signextend (UInt256.ofNat 2) tick

def tickClampWord (tick : UInt256) : UInt256 :=
  if EVM.signed (tickClampLowerWord tick) ≥ 887272 then tickMaxWord else tickClampLowerWord tick

theorem tickClampLowerWord_signed (tick : UInt256) :
    EVM.signed (tickClampLowerWord tick) = tickClampLower (EVM.signed (UInt256.signextend (UInt256.ofNat 2) tick)) := by
  unfold tickClampLowerWord tickClampLower
  split <;> simp only [tickMinWord_signed]

theorem tickClampWord_signed (tick : UInt256) :
    EVM.signed (tickClampWord tick) = tickClamp (EVM.signed (UInt256.signextend (UInt256.ofNat 2) tick)) := by
  unfold tickClampWord tickClamp
  rw [tickClampLowerWord_signed]
  split <;> simp only [tickMaxWord_signed, tickClampLowerWord_signed]

theorem tickClampLowerWord_canonical (tick : UInt256) : int24Canonical (tickClampLowerWord tick) := by
  unfold tickClampLowerWord
  split
  · exact tickMinWord_canonical
  · exact signextend24_canonical _

theorem tickClampWord_canonical (tick : UInt256) : int24Canonical (tickClampWord tick) := by
  unfold tickClampWord
  split
  · exact tickMaxWord_canonical
  · exact tickClampLowerWord_canonical _

theorem tickClamp_bounds (tick : Int) : -887272 ≤ tickClamp tick ∧ tickClamp tick ≤ 887272 := by
  unfold tickClamp tickClampLower
  split <;> split <;> omega

theorem tickClampWord_bounds (tick : UInt256) :
    -887272 ≤ EVM.signed (tickClampWord tick) ∧ EVM.signed (tickClampWord tick) ≤ 887272 := by
  rw [tickClampWord_signed]
  exact tickClamp_bounds _

theorem tickClampWord_natAbs (tick : UInt256) : (EVM.signed (tickClampWord tick)).natAbs ≤ 887272 := by
  have hb := tickClampWord_bounds tick
  cases h : EVM.signed (tickClampWord tick) <;> simp only [h] at hb ⊢ <;> omega

end Benchmarks.UniswapV4PoolManager
