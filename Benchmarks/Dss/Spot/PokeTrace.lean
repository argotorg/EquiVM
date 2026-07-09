import Benchmarks.Dss.Spot.PokeSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

namespace Benchmarks.Dss.Spot

theorem spotReachPokeBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = spotBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (spotSelBytes 8)) :
    ∃ k C, RD spotBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨185⟩ [spotSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  have hword : spotSelWord I = ⟨0x1504460f⟩ :=
    spotSelWord_eq_of_beq I hsz 0x15 0x04 0x46 0x0f ⟨0x1504460f⟩
      (by native_decide) (by simpa [spotSelBytes] using hsel)
  have hroot : UInt256.gt (armSelNat spotBytecode spotRootSplitPc) (spotSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  have heq0 : ∀ j, j < 0 →
      UInt256.eq (armSelNat spotBytecode (nthArmPc spotBytecode spotLowFirstArmPc j))
        (spotSelWord I) = ⟨0⟩ := by
    intro j hj
    omega
  have htake :
      UInt256.eq (armSelNat spotBytecode (nthArmPc spotBytecode spotLowFirstArmPc 0))
        (spotSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  exact spotReachLowBody 0 (by omega) ⟨185⟩ hcode hwv hsz hsize hroot heq0 htake
    (by jump_dest) (by native_decide)
end Benchmarks.Dss.Spot
