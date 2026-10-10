import Benchmarks.UniswapV3.Pool.MemoryGasBound

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool

-- LIBRARY CANDIDATE: a uniform bound for fixed-size memory initialization traces.
structure BoundedActiveWords (aw : UInt256) (limit : Nat) : Prop where
  lower : 3 ≤ aw.toNat
  upper : aw.toNat ≤ limit
  small : limit ≤ 2 ^ 200

theorem BoundedActiveWords.active {aw : UInt256} {limit : Nat}
    (h : BoundedActiveWords aw limit) : ActiveWords aw := ⟨h.lower, h.upper.trans h.small⟩

theorem BoundedActiveWords.of_active {aw : UInt256} (h : ActiveWords aw) :
    BoundedActiveWords aw (2 ^ 200) := ⟨h.1, h.2, le_refl _⟩

theorem BoundedActiveWords.expand32 {aw off : UInt256} {limit : Nat}
    (h : BoundedActiveWords aw limit) (hb : off.toNat + 32 ≤ limit) :
    BoundedActiveWords (expandedWords aw off ⟨32⟩) limit := by
  have hactive := activeWords_expand32 h.active (hb.trans h.small)
  refine ⟨hactive.1, ?_, h.small⟩
  rw [expandedWords32_toNat h.active (hb.trans h.small)]
  have hu := h.upper
  omega

theorem BoundedActiveWords.memoryGas {aw : UInt256} {cost limit : Nat}
    (h : BoundedActiveWords aw limit) :
    MemoryGasBound aw cost (Cₘ (UInt256.ofNat limit)) := by
  have hc := Cₘ_monotone_of_lt h.upper (show limit < UInt256.size by
    have hs := h.small; change limit < 2 ^ 256; omega)
  rw [u256_ofNat_toNat] at hc
  unfold MemoryGasBound
  omega

end Benchmarks.UniswapV3.Pool
