import Benchmarks.Dss.End.Trusted

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

namespace Benchmarks.Dss.End

theorem endDogBodyCore : endBodyObligation 3 := by
  intro cA gh bl σ_evm σ_solm σ₀ A I g hcode hsize hperm hwv hsel hAccounts
  sorry

end Benchmarks.Dss.End
