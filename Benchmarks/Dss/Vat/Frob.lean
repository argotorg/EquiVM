import Benchmarks.Dss.Vat.FrobLive

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

namespace Benchmarks.Dss.Vat

suppress_compilation

set_option maxHeartbeats 0 in
theorem vatFrobBodyCore : VatBodyTheorem 11 := by
  intro cA gh bl σ_evm σ_solm σ₀ A I g hcode hsize hperm hwv hsel hAccounts
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (vatSelBytes 11) rfl hsel
  have hreach := vatReachFrobBody (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
    (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz4 hsize hsel
  by_cases hsz196 : 196 ≤ I.calldata.size
  · have hdecode := vatDecode_frob_ok (I := I) hsz196
    obtain ⟨_, _, hdecoded⟩ := vatFrobX_decoded
      (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
      (A := A) (I := I) (g := Sat256.ofUInt256 g)
      hsz196 hsize hreach
    by_cases hlive : vatSlotWord ⟨10⟩ σ_evm I = ⟨1⟩
    · exact vatFrobBodyCoreLive hcode hsize hperm hwv hsel hAccounts hsz196 hdecode
        ⟨_, _, hdecoded⟩ hlive
    · exact vatFrobBodyCoreNotLive hcode hsize hwv hsz196 hlive
        (vatDispatchFrob hsel) hdecode hreach hAccounts
  · have hshort : I.calldata.size < 196 := by omega
    exact vatFrobBodyCoreDecodeFailed_short hcode hsize hsz4 hshort hsel hreach

end Benchmarks.Dss.Vat
