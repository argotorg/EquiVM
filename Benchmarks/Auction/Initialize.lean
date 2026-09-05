import Benchmarks.Auction.InitializeTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Refinement

set_option maxRecDepth 50000000
set_option maxHeartbeats 0

namespace Auction

theorem auctionInitializeBodyCore {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (_hcode : I.code = auctionBytecode)
    (_hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true)
    (_hsel : selIs I (auctionSelBytes 11))
    (_hAccounts : accountMapEquiv σ_evm σ_solm) :
    RuntimeCase (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
      (σ₀ := σ₀) (A := A) (I := I) g := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (auctionSelBytes 11) rfl _hsel
  have hdispatch := auctionDispatch_initialize _hsel
  have hreach := auctionReachInitializeBody (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    _hcode hsz4 _hsize _hsel
  by_cases hwv : I.weiValue = ⟨0⟩
  · by_cases hsz196 : 196 ≤ I.calldata.size
    · by_cases hbig : I.calldata.size < 2 ^ 255 + 4
      · by_cases hcanonNouns : (auctionInitializeNounsWord I).toNat < EVM.addressModulus
        · by_cases hcanonWeth : (auctionInitializeWethWord I).toNat < EVM.addressModulus
          · by_cases hcanonMinBid :
                (auctionInitializeMinBidIncrementPercentageWord I).toNat < EVM.twoPow 8
            · have hdecode := auctionDecode_initialize (I := I) hsz196 hbig hcanonNouns
                hcanonWeth hcanonMinBid
              let evmE := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I
              let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
              have hinitWord :=
                auctionInitializingByte_accountMapEquiv (σ := σ_evm) (τ := σ_solm)
                  (I := I) _hAccounts
              have hizedWord :=
                auctionInitializedByte_accountMapEquiv (σ := σ_evm) (τ := σ_solm)
                  (I := I) _hAccounts
              by_cases hinitZero :
                  UInt256.land (UInt256.div (auctionSlotWord ⟨0⟩ σ_evm I) ⟨256⟩)
                    ⟨255⟩ = ⟨0⟩
              · have hinitZeroSolm : auctionInitializingByte evmS = ⟨0⟩ := by
                  have hmap :
                      UInt256.land
                          (UInt256.div (auctionSlotWord ⟨0⟩ σ_solm I) ⟨256⟩) ⟨255⟩ =
                        ⟨0⟩ := by
                    rw [← hinitWord]
                    exact hinitZero
                  simpa [evmS, auctionInitializingByte_initState] using hmap
                by_cases hizedZero :
                    UInt256.land (auctionSlotWord ⟨0⟩ σ_evm I) ⟨255⟩ = ⟨0⟩
                · have hizedZeroSolm : auctionInitializedByte evmS = ⟨0⟩ := by
                    have hmap :
                        UInt256.land (auctionSlotWord ⟨0⟩ σ_solm I) ⟨255⟩ = ⟨0⟩ := by
                      rw [← hizedWord]
                      exact hizedZero
                    simpa [evmS, auctionInitializedByte_initState] using hmap
                  have hbody := auctionInitializeBodyReturns_top evmS I
                    (by simp only [evmS, initState]; exact hwv)
                    hinitZeroSolm hizedZeroSolm hcanonNouns hcanonWeth hcanonMinBid
                  have hpostAccountsEvm :
                      accountMapEquiv (auctionInitializeTopPostMap σ_evm I)
                        (auctionInitializeTopPostState evmE I).accountMap := by
                    simpa [evmE] using
                      (auctionInitializeTopPostMap_accountMap (cA := cA) (gh := gh)
                        (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I)
                        (g := Sat256.ofUInt256 g))
                  have hpostState :
                      EVMStateEquiv (auctionInitializeTopPostState evmE I)
                        (auctionInitializeTopPostState evmS I) := by
                    have hσ : EVMStateEquiv evmE evmS := by
                      exact EVMStateEquiv.initState _hAccounts
                    exact auctionInitializeTopPostState_equiv I hσ
                  exact (auctionX_initialize_success_top (g := Sat256.ofUInt256 g)
                      _hperm hwv hsz196 _hsize hbig hcanonNouns hcanonWeth hcanonMinBid
                      hinitZero hizedZero hreach)
                    |>.reEquivExecutionGenEVMStateEquiv _hcode hdispatch hdecode hbody
                      (by
                        simp [auctionInitializeTopPostState, auctionInitializeCorePostState,
                          auctionInitializeSetInitializingFalseState,
                          auctionInitializeSetInitializedTrueState,
                          auctionInitializeSetInitializingTrueState, auctionUnpausePostState,
                          auctionInitializeSetStatusState, auctionInitializeSetAddressState,
                          auctionPausePostState, auctionInitializeSetUint256State,
                          auctionInitializeSetMinBidState, evmE, initState,
                          storageStore_createdAccounts])
                      hpostAccountsEvm hpostState
                      (returnEquiv.fallthrough rfl rfl (by native_decide))
                · have hizedNzSolm : auctionInitializedByte evmS ≠ ⟨0⟩ := by
                    have hmap :
                        UInt256.land (auctionSlotWord ⟨0⟩ σ_solm I) ⟨255⟩ ≠ ⟨0⟩ := by
                      intro h
                      apply hizedZero
                      rw [hizedWord]
                      exact h
                    simpa [evmS, auctionInitializedByte_initState] using hmap
                  have hbody := auctionInitializeBodyReverts_initialized evmS I
                    (by simp only [evmS, initState]; exact hwv)
                    hinitZeroSolm hizedNzSolm
                  have hdecoded := auctionInitializeX_decoded (cA := cA) (gh := gh)
                    (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
                    (g := Sat256.ofUInt256 g) (sel := auctionSelWord I)
                    hwv hsz196 _hsize hbig hcanonNouns hcanonWeth hcanonMinBid hreach
                  exact (auctionInitializeX_revert_initialized (g := Sat256.ofUInt256 g)
                      hinitZero hizedZero hdecoded)
                    |>.reEquivExecutionRevert _hcode hdispatch hdecode hbody
              · have hinitNzSolm : auctionInitializingByte evmS ≠ ⟨0⟩ := by
                  have hmap :
                      UInt256.land
                          (UInt256.div (auctionSlotWord ⟨0⟩ σ_solm I) ⟨256⟩) ⟨255⟩ ≠
                        ⟨0⟩ := by
                    intro h
                    apply hinitZero
                    rw [hinitWord]
                    exact h
                  simpa [evmS, auctionInitializingByte_initState] using hmap
                have hbody := auctionInitializeBodyReturns_nested evmS I
                  (by simp only [evmS, initState]; exact hwv)
                  hinitNzSolm hcanonNouns hcanonWeth hcanonMinBid
                have hpostAccountsEvm :
                    accountMapEquiv (auctionInitializeCorePostMap σ_evm I)
                      (auctionInitializeNestedPostState evmE I).accountMap := by
                  simpa [evmE, auctionInitializeNestedPostState] using
                    (auctionInitializeCorePostMap_accountMap (cA := cA) (gh := gh)
                      (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I)
                      (g := Sat256.ofUInt256 g))
                have hpostState :
                    EVMStateEquiv (auctionInitializeNestedPostState evmE I)
                      (auctionInitializeNestedPostState evmS I) := by
                  have hσ : EVMStateEquiv evmE evmS := by
                    exact EVMStateEquiv.initState _hAccounts
                  exact auctionInitializeNestedPostState_equiv I hσ
                exact (auctionX_initialize_success_nested (g := Sat256.ofUInt256 g)
                    _hperm hwv hsz196 _hsize hbig hcanonNouns hcanonWeth hcanonMinBid
                    hinitZero hreach)
                  |>.reEquivExecutionGenEVMStateEquiv _hcode hdispatch hdecode hbody
                    (by
                      simp [auctionInitializeNestedPostState, auctionInitializeCorePostState,
                        auctionUnpausePostState, auctionInitializeSetStatusState,
                        auctionInitializeSetAddressState, auctionPausePostState,
                        auctionInitializeSetUint256State, auctionInitializeSetMinBidState,
                        evmE, initState, storageStore_createdAccounts])
                    hpostAccountsEvm hpostState
                    (returnEquiv.fallthrough rfl rfl (by native_decide))
            · exact (auctionInitializeX_decodeRevert_noncanon_minBid
                  (g := Sat256.ofUInt256 g) hwv hsz196 _hsize hbig hcanonNouns hcanonWeth
                  hcanonMinBid hreach)
                |>.reEquivDecodingFailed _hcode hdispatch
                  (auctionDecode_initialize_none_noncanon_minBid (I := I) hsz196 hbig
                    hcanonNouns hcanonWeth hcanonMinBid)
          · exact (auctionInitializeX_decodeRevert_noncanon_weth
                (g := Sat256.ofUInt256 g) hwv hsz196 _hsize hbig hcanonNouns hcanonWeth hreach)
              |>.reEquivDecodingFailed _hcode hdispatch
                (auctionDecode_initialize_none_noncanon_weth (I := I) hsz196 hbig
                  hcanonNouns hcanonWeth)
        · exact (auctionInitializeX_decodeRevert_noncanon_nouns
              (g := Sat256.ofUInt256 g) hwv hsz196 _hsize hbig hcanonNouns hreach)
            |>.reEquivDecodingFailed _hcode hdispatch
              (auctionDecode_initialize_none_noncanon_nouns (I := I) hsz196 hbig hcanonNouns)
      · have hbigLe : 2 ^ 255 + 4 ≤ I.calldata.size := by omega
        exact (auctionInitializeX_decodeRevert_huge (g := Sat256.ofUInt256 g)
            hwv _hsize hbigLe hreach)
          |>.reEquivDecodingFailed _hcode hdispatch
            (auctionDecode_initialize_none_huge (I := I) hbigLe)
    · have hshort : I.calldata.size < 196 := by omega
      exact (auctionInitializeX_decodeRevert_short (g := Sat256.ofUInt256 g)
          hwv hsz4 _hsize hshort hreach)
        |>.reEquivDecodingFailed _hcode hdispatch
          (auctionDecode_initialize_none_short (I := I) hsz4 hshort)
  · by_cases hsz196 : 196 ≤ I.calldata.size
    · by_cases hbig : I.calldata.size < 2 ^ 255 + 4
      · by_cases hcanonNouns : (auctionInitializeNounsWord I).toNat < EVM.addressModulus
        · by_cases hcanonWeth : (auctionInitializeWethWord I).toNat < EVM.addressModulus
          · by_cases hcanonMinBid :
                (auctionInitializeMinBidIncrementPercentageWord I).toNat < EVM.twoPow 8
            · have hdecode := auctionDecode_initialize (I := I) hsz196 hbig hcanonNouns
                hcanonWeth hcanonMinBid
              have hbody := auctionInitializeBodyReverts_callvalue
                (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I
                (by simpa [initState] using hwv)
              exact (auctionX_initialize_callvalue_ne hreach hwv)
                |>.reEquivExecutionRevert _hcode hdispatch hdecode hbody
            · exact (auctionX_initialize_callvalue_ne hreach hwv)
                |>.reEquivDecodingFailed _hcode hdispatch
                  (auctionDecode_initialize_none_noncanon_minBid (I := I) hsz196 hbig
                    hcanonNouns hcanonWeth hcanonMinBid)
          · exact (auctionX_initialize_callvalue_ne hreach hwv)
              |>.reEquivDecodingFailed _hcode hdispatch
                (auctionDecode_initialize_none_noncanon_weth (I := I) hsz196 hbig
                  hcanonNouns hcanonWeth)
        · exact (auctionX_initialize_callvalue_ne hreach hwv)
            |>.reEquivDecodingFailed _hcode hdispatch
              (auctionDecode_initialize_none_noncanon_nouns (I := I) hsz196 hbig hcanonNouns)
      · have hbigLe : 2 ^ 255 + 4 ≤ I.calldata.size := by omega
        exact (auctionX_initialize_callvalue_ne hreach hwv)
          |>.reEquivDecodingFailed _hcode hdispatch
            (auctionDecode_initialize_none_huge (I := I) hbigLe)
    · have hshort : I.calldata.size < 196 := by omega
      exact (auctionX_initialize_callvalue_ne hreach hwv)
        |>.reEquivDecodingFailed _hcode hdispatch
          (auctionDecode_initialize_none_short (I := I) hsz4 hshort)

end Auction
