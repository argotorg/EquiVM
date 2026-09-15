import Benchmarks.Auction.InitializeBody
import Benchmarks.Auction.InitializeDecoder
import Benchmarks.Auction.InitializerError

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 100000

namespace Auction

theorem initializeBodyCore {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = auctionBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hsel : selIs I (entryBytes 11))
    (hreach : EntryReached 11 cA gh bl σ_evm σ₀ A I g)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor auctionConfig auctionContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  by_cases hwv : I.weiValue = ⟨0⟩
  · have hd := dispatchEntry 11 hsel
    have hsz := calldata_size_ge_of_selIs I (entryBytes 11) (entryBytes_size 11) hsel
    obtain ⟨_, _, rd705⟩ := hreach
    obtain ⟨_, _, rd718⟩ := entryGuardZero 11 (by decide) rd705 hwv
    have rd5400 := evm_run rd718 with [
      push2 ⟨413⟩, push2 ⟨731⟩, calldatasize, push1 ⟨4⟩,
      push2 ⟨5400⟩, jump (by jump_dest) ]
    by_cases hlen : 196 ≤ I.calldata.size
    · by_cases hhi : I.calldata.size < 2 ^ 255 + 4
      · have hdec := initializeDecodeResult hlen hhi
        by_cases hc : (initializeArgs I.calldata).canonical
        · rw [if_pos hc] at hdec
          obtain ⟨_, _, rd731⟩ := initializeDecoderOk rd5400 hlen hhi hsize hc
            (by jump_dest) (by evm_ov)
          change RD _ _ _ _ _
            ((initializeArgs I.calldata).duration :: (initializeArgs I.calldata).minBidIncrement ::
              (initializeArgs I.calldata).reservePrice :: (initializeArgs I.calldata).timeBuffer ::
              (initializeArgs I.calldata).weth :: (initializeArgs I.calldata).nouns ::
              ⟨413⟩ :: [solcSelectorWord I]) _ _ _ _ _ _ at rd731
          have rd2130 := evm_run rd731 with [jumpdest, push2 ⟨2130⟩, jump (by jump_dest)]
          by_cases hg : initializingWord σ_evm I ≠ ⟨0⟩ ∨ initializedWord σ_evm I = ⟨0⟩
          · obtain ⟨_, _, rd413⟩ := initializeRuntime (initializeArgs I.calldata) rd2130 hc hg
              hperm (by jump_dest) (by evm_ov)
            have hbody := initializeBody
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
              (initializeArgs I.calldata) hwv hc (by
                change initializingWord σ_solm I ≠ ⟨0⟩ ∨ initializedWord σ_solm I = ⟨0⟩
                rw [← initializingWord_equiv hAccounts, ← initializedWord_equiv hAccounts]
                exact hg)
            exact (auctionStop rd413 (by evm_ov)).reEquivExecutionGenAccountMapEquiv
              hcode hd hdec hbody (by rw [initializeFinalState_created]; rfl)
              (initializeFinalState_accounts (initializeArgs I.calldata)
                (σ := σ_evm) (evm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                hAccounts)
              (.fallthrough rfl rfl (by native_decide))
          · have hi : initializingWord σ_evm I = ⟨0⟩ := by
              by_contra h; exact hg (Or.inl h)
            have hz : initializedWord σ_evm I ≠ ⟨0⟩ := fun h => hg (Or.inr h)
            have hbody := initializeBodyReverts
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
              (initializeArgs I.calldata) hwv
              (by change initializingWord σ_solm I = ⟨0⟩
                  rw [← initializingWord_equiv hAccounts]; exact hi)
              (by change initializedWord σ_solm I ≠ ⟨0⟩
                  rw [← initializedWord_equiv hAccounts]; exact hz)
            exact (initializeGuardRevert rd2130 hi hz (by evm_ov)).reEquivExecutionRevert
              hcode hd hdec hbody
        · rw [if_neg hc] at hdec
          exact (initializeDecoderNoncanonical rd5400 hlen hhi hsize hc
            (by evm_ov)).reEquivDecodingFailed hcode hd hdec
      · exact (initializeDecoderBadLength rd5400
          (solcCalldataStaticLenCheckHuge (words := 6) (by omega) hsize (by decide))
          (by evm_ov)).reEquivDecodingFailed hcode hd (initializeDecodeHuge (by omega))
    · exact (initializeDecoderBadLength rd5400
        (solcCalldataStaticLenCheckShort (words := 6) hsz (by omega) hsize (by decide))
        (by evm_ov)).reEquivDecodingFailed hcode hd (initializeDecodeShort (by omega))
  · exact entryNonpayableRevert 11 (by decide) hcode hsel hreach hwv

end Auction
