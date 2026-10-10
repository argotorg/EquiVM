import Benchmarks.UniswapV3.Pool.OracleObservationRead

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool

-- LIBRARY CANDIDATE: a memory-cost potential carried by a symbolic execution cursor.
def MemoryGasBound (aw : UInt256) (cost allowance : Nat) : Prop := Cₘ aw ≤ cost + allowance

theorem MemoryGasBound.advance {aw aw' : UInt256} {cost cost' allowance : Nat}
    (h : MemoryGasBound aw cost allowance)
    (hstep : cost + (Cₘ aw' - Cₘ aw) ≤ cost') : MemoryGasBound aw' cost' allowance := by
  unfold MemoryGasBound at h ⊢
  omega

theorem MemoryGasBound.mono_cost {aw : UInt256} {cost cost' allowance : Nat}
    (h : MemoryGasBound aw cost allowance) (hcost : cost ≤ cost') :
    MemoryGasBound aw cost' allowance := by
  unfold MemoryGasBound at h ⊢
  omega

theorem MemoryGasBound.words_lt {aw : UInt256} {cost allowance : Nat} {gas : Sat256}
    (h : MemoryGasBound aw cost allowance) (hc : cost ≤ gas.toNat) (ha : allowance ≤ 2 ^ 200) :
    aw.toNat < 2 ^ 134 := by
  by_contra hn
  have hm := Cₘ_monotone_of_lt (show 2 ^ 134 ≤ aw.toNat by omega) aw.val.isLt
  rw [u256_ofNat_toNat] at hm
  have hlarge : 2 ^ 257 ≤ Cₘ (UInt256.ofNat (2 ^ 134)) := by native_decide
  have hg : gas.toNat < 2 ^ 256 := gas.isLt
  unfold MemoryGasBound at h
  omega

theorem MemoryGasBound.capacity {aw p : UInt256} {cost allowance : Nat} {gas : Sat256}
    (h : MemoryGasBound aw cost allowance) (hc : cost ≤ gas.toNat) (ha : allowance ≤ 2 ^ 200)
    (hp : p.toNat ≤ aw.toNat * 32 + 32) : p.toNat + 4096 ≤ 2 ^ 200 := by
  have hw := h.words_lt hc ha
  omega

theorem memoryGasCapacityOrOOG {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : EVM.State}
    {pc aw p : UInt256} {stack : List UInt256} {mem rdata : ByteArray} {σ : AccountMap}
    {k C allowance : Nat}
    (rd : RD code ee g s0 pc stack mem aw rdata σ k C)
    (h : MemoryGasBound aw C allowance) (ha : allowance ≤ 2 ^ 200)
    (hp : p.toNat ≤ aw.toNat * 32 + 32) :
    X (g.toNat + 1) (D_J code 0) s0 = .error .OutOfGass ∨ p.toNat + 4096 ≤ 2 ^ 200 := by
  rcases rd with hoog | ⟨s, _, _, _, _, _, _, hc, _⟩
  · exact Or.inl hoog
  · exact Or.inr (h.capacity hc ha hp)

end Benchmarks.UniswapV3.Pool
