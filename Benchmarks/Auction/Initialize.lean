import Benchmarks.Auction.InitializeBody
import Benchmarks.Auction.InitializeDecoder
import Benchmarks.Auction.InitializerError

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 100000

namespace Auction

theorem initializeBodyCore {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = auctionBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (entryBytes 11))
    (hreach : EntryReached 11 σ σ₀ A I g) :
    runtimeRefinementFor auctionConfig auctionContract σ σ₀ g A I := by
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
          by_cases hg : initializingWord σ I ≠ ⟨0⟩ ∨ initializedWord σ I = ⟨0⟩
          · rcases initializeRuntimeSplit (initializeArgs I.calldata) rd2130 hc hg
              (by jump_dest) (by evm_ov) with
              ⟨_hperm, _, _, rd413⟩ | ⟨hperm, hstatic⟩
            swap
            · exact hstatic.reEquivStaticHalt hcode hd hdec
                (initializeBodyStatic (initState σ σ₀ (Sat256.ofUInt256 g) A I)
                  (initializeArgs I.calldata) hwv hg hperm)
            have hbody := initializeBody
              (initState σ σ₀ (Sat256.ofUInt256 g) A I)
              (initializeArgs I.calldata) hwv hc hg
            exact (auctionStop rd413 (by evm_ov)).reEquivExecutionGen
              hcode hd hdec hbody
              (initializeFinalState_accounts (initializeArgs I.calldata)
                (σ := σ) (evm := initState σ σ₀ (Sat256.ofUInt256 g) A I) rfl)
              (.fallthrough rfl rfl (by native_decide))
          · have hi : initializingWord σ I = ⟨0⟩ := by
              by_contra h; exact hg (Or.inl h)
            have hz : initializedWord σ I ≠ ⟨0⟩ := fun h => hg (Or.inr h)
            have hbody := initializeBodyReverts
              (initState σ σ₀ (Sat256.ofUInt256 g) A I)
              (initializeArgs I.calldata) hwv hi hz
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
