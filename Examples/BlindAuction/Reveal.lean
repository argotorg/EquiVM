import Examples.BlindAuction.Reveal.Decoded

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 10000000
namespace BlindAuction

/-- `reveal(uint256[],bool[],bytes32[])` body (pc 387) refines its transition. -/
theorem blindAuctionRevealBodyCore {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = blindAuctionBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hsel : selIs I ⟨#[0x90, 0x0f, 0x08, 0x0a]⟩)
    (hreach : ∃ k C, RD blindAuctionBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨387⟩
      [blindAuctionSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm)
      k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
 :
    runtimeEquivalenceFor blindAuctionConfig blindAuctionContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have _hsize : I.calldata.size < UInt256.size := hsize
  have _hperm : I.perm = true := hperm

  have hsz := blindAuctionRevealSelector_size hsel
  have hd := blindAuctionDispatch_reveal (cd := I.calldata) hsel
  by_cases hwv : I.weiValue = ⟨0⟩
  · have _hdecodeEntry :=
      blindAuctionX_reveal_decodeEntry (g := Sat256.ofUInt256 g) hwv hreach
    by_cases hshortHead : I.calldata.size < 100
    · have hdecNone := blindAuctionDecode_reveal_none_short (I := I) hsz hshortHead
      have hslt :
          UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨96⟩ =
            ⟨1⟩ := by
        have h :=
          solcCalldataStaticLenCheckShort (sz := I.calldata.size) (words := 3)
            hsz hshortHead hsize (by omega)
        simpa using h
      have hrev := blindAuctionRevealX_decode_head_revert
        (g := Sat256.ofUInt256 g) hslt _hdecodeEntry
      exact hrev.reEquivDecodingFailed hcode hd hdecNone
    · by_cases hhuge : 2 ^ 255 + 4 ≤ I.calldata.size
      · have hdecNone := blindAuctionDecode_reveal_none_huge (I := I) hhuge
        have hslt :
            UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨96⟩ =
              ⟨1⟩ := by
          have h :=
            solcCalldataStaticLenCheckHuge (sz := I.calldata.size) (words := 3)
              hhuge hsize (by omega)
          simpa using h
        have hrev := blindAuctionRevealX_decode_head_revert
          (g := Sat256.ofUInt256 g) hslt _hdecodeEntry
        exact hrev.reEquivDecodingFailed hcode hd hdecNone
      · have hslt :
            UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨96⟩ =
              ⟨0⟩ := by
          have h :=
            solcCalldataStaticLenCheckOk (sz := I.calldata.size) (words := 3)
              (by omega) (by omega) hsize
          simpa using h
        obtain ⟨k1806, C1806, rd1806⟩ :=
          blindAuctionRevealX_decode_head_ok (g := Sat256.ofUInt256 g) hslt _hdecodeEntry
        by_cases hcalldataSign : I.calldata.size < 2 ^ 255
        · by_cases hdecNone :
              decodeCalldata (revealTransition.params.map Param.name)
                (transitionSignature revealTransition).paramTypes I.calldata = none
          · have hrev :=
              scratch_blindAuctionRevealDecode1806_none_reverts
                (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
                (A := A) (I := I) (g := Sat256.ofUInt256 g) rd1806 (by omega)
                hcalldataSign hdecNone
            exact hrev.reEquivDecodingFailed hcode hd hdecNone
          · obtain ⟨callargs, hdec⟩ := Option.ne_none_iff_exists'.mp hdecNone
            exact scratch_blindAuctionReveal_decoded_ok_from1806
              (I := I) (g := g)
              (cA := cA) (gh := gh) (bl := bl)
              (σ_evm := σ_evm) (σ_solm := σ_solm) (σ₀ := σ₀) (A := A)
              (callargs := callargs)
              hcode hsize hperm hd hdec hwv hcalldataSign hAccounts
              ⟨k1806, C1806, rd1806⟩
        · have hcalldataGe : 2 ^ 255 ≤ I.calldata.size := by omega
          have hdecNone := blindAuctionDecode_reveal_none_huge_dynamic (I := I) hcalldataGe
          have hrev :=
            blindAuctionRevealDecode1806_hugeDynamic_reverts
              (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
              (A := A) (I := I) (g := Sat256.ofUInt256 g) rd1806 hcalldataGe hsize
          exact hrev.reEquivDecodingFailed hcode hd hdecNone
  · have hrev := blindAuctionX_reveal_nonpayable (g := Sat256.ofUInt256 g) hwv hreach
    by_cases hdecNone :
        decodeCalldata (revealTransition.params.map Param.name)
          (transitionSignature revealTransition).paramTypes I.calldata = none
    · exact hrev.reEquivDecodingFailed hcode hd hdecNone
    · obtain ⟨callargs, hdec⟩ := Option.ne_none_iff_exists'.mp hdecNone
      have hbody :
          ExecTransitionBody blindAuctionConfig blindAuctionContract
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) callargs
            revealTransition.body .reverted := by
        exact blindAuctionRevealBodyReverts_nonpayable
          (by simp only [initState]; exact hwv)
      exact hrev.reEquivExecutionRevert hcode hd hdec hbody

end BlindAuction
