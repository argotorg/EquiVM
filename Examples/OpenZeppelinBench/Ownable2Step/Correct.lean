import Examples.OpenZeppelinBench.Ownable2Step.AcceptOwnership
import Examples.OpenZeppelinBench.Ownable2Step.Owner
import Examples.OpenZeppelinBench.Ownable2Step.PendingOwner
import Examples.OpenZeppelinBench.Ownable2Step.RenounceOwnership
import Examples.OpenZeppelinBench.Ownable2Step.TransferOwnership

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace OpenZeppelinBench.Ownable2Step

/-- The deployed Ownable2Step benchmark runtime bytecode refines the Solm specification. -/
theorem ownable2StepCorrect : runtimeEquivalence config ownable2StepBenchBytecode contract := by
  refine ⟨fun cA gh bl σ_evm σ_solm σ₀ g A I hcode hsize hperm hAccounts => ?_⟩
  by_cases hwv : I.weiValue = ⟨0⟩
  · by_cases hsz : 4 ≤ I.calldata.size
    · by_cases h0 : selIs I ⟨#[0x71, 0x50, 0x18, 0xa6]⟩
      · have hsz0 := ownable2StepRenounceOwnershipSelector_size h0
        have hm := ownable2StepMatches 0 (by omega) hsz0 h0
        have hreach := ownable2StepReachBody (cA := cA) (gh := gh) (bl := bl)
          (σ := σ_evm) (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g)
          0 (by omega) ⟨89⟩ hcode hwv hsz0 hsize
          hm.1 hm.2 (by jump_dest) (by decide)
        exact ownable2StepRenounceOwnershipBody hcode hsize hperm hwv h0 hreach hAccounts
      · by_cases h1 : selIs I ⟨#[0x79, 0xba, 0x50, 0x97]⟩
        · have hsz1 := ownable2StepAcceptOwnershipSelector_size h1
          have hm := ownable2StepMatches 1 (by omega) hsz1 h1
          have hreach := ownable2StepReachBody (cA := cA) (gh := gh) (bl := bl)
            (σ := σ_evm) (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g)
            1 (by omega) ⟨99⟩ hcode hwv hsz1 hsize
            hm.1 hm.2 (by jump_dest) (by decide)
          exact ownable2StepAcceptOwnershipBody hcode hsize hperm hwv h1 hreach hAccounts
        · by_cases h2 : selIs I ⟨#[0x8d, 0xa5, 0xcb, 0x5b]⟩
          · have hsz2 := ownable2StepOwnerSelector_size h2
            have hm := ownable2StepMatches 2 (by omega) hsz2 h2
            have hreach := ownable2StepReachBody (cA := cA) (gh := gh) (bl := bl)
              (σ := σ_evm) (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g)
              2 (by omega) ⟨107⟩ hcode hwv hsz2
              hsize hm.1 hm.2 (by jump_dest) (by decide)
            exact ownable2StepOwnerBody hcode hsize hperm hwv h2 hreach hAccounts
          · by_cases h3 : selIs I ⟨#[0xe3, 0x0c, 0x39, 0x78]⟩
            · have hsz3 := ownable2StepPendingOwnerSelector_size h3
              have hm := ownable2StepMatches 3 (by omega) hsz3 h3
              have hreach := ownable2StepReachBody (cA := cA) (gh := gh) (bl := bl)
                (σ := σ_evm) (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g)
                3 (by omega) ⟨147⟩ hcode hwv hsz3
                hsize hm.1 hm.2 (by jump_dest) (by decide)
              exact ownable2StepPendingOwnerBody hcode hsize hperm hwv h3 hreach hAccounts
            · by_cases h4 : selIs I ⟨#[0xf2, 0xfd, 0xe3, 0x8b]⟩
              · have hsz4 := ownable2StepTransferOwnershipSelector_size h4
                have hm := ownable2StepMatches 4 (by omega) hsz4 h4
                have hreach := ownable2StepReachBody (cA := cA) (gh := gh) (bl := bl)
                  (σ := σ_evm) (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g)
                  4 (by omega) ⟨164⟩ hcode hwv hsz4
                  hsize hm.1 hm.2 (by jump_dest) (by decide)
                exact ownable2StepTransferOwnershipBody hcode hsize hperm hwv h4 hreach hAccounts
              · refine ownable2StepNoDispatch hcode hsize hperm hwv ?_
                intro i hi
                interval_cases i
                · simpa [selIs, ownable2StepSelBytes] using h0
                · simpa [selIs, ownable2StepSelBytes] using h1
                · simpa [selIs, ownable2StepSelBytes] using h2
                · simpa [selIs, ownable2StepSelBytes] using h3
                · simpa [selIs, ownable2StepSelBytes] using h4
    · exact ownable2StepShortRevert hcode hsize hperm hwv (by omega)
  · exact ownable2StepNonPayable hcode hwv

end OpenZeppelinBench.Ownable2Step
