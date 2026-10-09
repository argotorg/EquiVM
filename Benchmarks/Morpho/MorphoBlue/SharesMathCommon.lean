import Benchmarks.Morpho.MorphoBlue.MathValues

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.Morpho.MorphoBlue

def virtualShares : UInt256 := UInt256.ofNat 1000000

def SharesDownFits (assets totalAssets totalShares : UInt256) : Prop :=
  totalShares.toNat + virtualShares.toNat < UInt256.size ∧
  totalAssets.toNat + 1 < UInt256.size ∧
  assets.toNat * (totalShares + virtualShares).toNat < UInt256.size

def sharesDownWord (assets totalAssets totalShares : UInt256) : UInt256 :=
  UInt256.div (UInt256.mul assets (totalShares + virtualShares)) (totalAssets + UInt256.ofNat 1)

theorem sharesDownDenom_nonzero (totalAssets : UInt256)
    (hfit : totalAssets.toNat + 1 < UInt256.size) : totalAssets + UInt256.ofNat 1 ≠ ⟨0⟩ := by
  have hn : (totalAssets + UInt256.ofNat 1).toNat = totalAssets.toNat + 1 := by
    rw [uadd_toNat, show (UInt256.ofNat 1).toNat = 1 from rfl, Nat.mod_eq_of_lt hfit]
  intro hz
  rw [hz] at hn
  change 0 = totalAssets.toNat + 1 at hn
  omega

end Benchmarks.Morpho.MorphoBlue
