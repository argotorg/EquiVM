import Benchmarks.Dss.Vat.FrobLive

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.Vat

suppress_compilation

set_option maxHeartbeats 0 in
theorem vatFrobBodyCore : VatBodyTheoremAnyPerm 11 := by
  intro σ σ₀ A I g hcode hsize hwv hsel
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (vatSelBytes 11) rfl hsel
  have hreach := vatReachFrobBody (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz4 hsize hsel
  by_cases hsz196 : 196 ≤ I.calldata.size
  · have hdecode := vatDecode_frob_ok (I := I) hsz196
    obtain ⟨_, _, hdecoded⟩ := vatFrobX_decoded
      (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := Sat256.ofUInt256 g)
      hsz196 hsize hreach
    by_cases hlive : solcSlotWordAt ⟨10⟩ σ I = ⟨1⟩
    · exact vatFrobBodyCoreLive hcode hsize hwv hsel hsz196 hdecode
        ⟨_, _, hdecoded⟩ hlive
    · exact vatFrobBodyCoreNotLive hcode hsize hwv hsz196 hlive
        (vatDispatchFrob hsel) hdecode hreach
  · have hshort : I.calldata.size < 196 := by omega
    exact vatFrobBodyCoreDecodeFailed_short hcode hsize hsz4 hshort hsel hreach

end Benchmarks.Dss.Vat
