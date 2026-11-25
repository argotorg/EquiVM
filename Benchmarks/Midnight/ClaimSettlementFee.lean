import Benchmarks.Midnight.Dispatch
import Benchmarks.Midnight.ClaimSettlementTrace
import Benchmarks.Midnight.AddressDecode
import Benchmarks.Midnight.TripleDecode

variable {fork : Ethereum.Fork}

/-!
# Midnight `claimSettlementFee(address,uint256,address)`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Stele body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 17638; reach lemma `midnightReachClaimSettlementFeeBody`.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

theorem claimSettlementBodyCore {σ σ₀ A I} {g : UInt256}
    {token receiver : AccountAddress} {amount aw : UInt256} {k C : Nat} {R : List UInt256}
    (hcode : I.code = midnightBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hhi : I.calldata.size < calldataLimit) (hgas : midnightGasBound g) (hfork : fork ≥ .osaka)
    (hd : dispatchMsg contract I.calldata = some claimSettlementFeeTransition)
    (hdec : config.externalABI.decodeCalldata? (claimSettlementFeeTransition.params.map Param.name)
      (transitionSignature claimSettlementFeeTransition).paramTypes I.calldata =
      some (claimSettlementArguments token amount receiver))
    (hstack : R.length + 14 ≤ 1024)
    (rd : RD fork midnightBytecode I (Sat256.ofUInt256 g) (initState σ σ₀ (Sat256.ofUInt256 g) A I)
      ⟨17674⟩ (UInt256.ofNat receiver.val :: amount :: UInt256.ofNat token.val :: R)
      midnightEntryMemory aw ByteArray.empty σ k C) :
    runtimeRefinementFor fork config contract σ σ₀ g A I := by
  let evm := initState σ σ₀ (Sat256.ofUInt256 g) A I
  have hs : SourceState evm I σ evm := SourceState.init
  have hbal : claimSettlementBalance evm token = solcSlotWordAt (claimSettlementSlot token) σ I := rfl
  by_cases hauth : solcSourceWord I = UInt256.land (solcSlotWordAt ⟨11⟩ σ I) solcAddrMask
  · obtain ⟨k1, C1, rd1⟩ := midnightBlocks.midnight_block_17674_fallthrough
      (by simp only [List.length_cons]; omega)
      (by rw [addressMask_computed]; exact u256_sub_eq_zero_iff_eq.mpr hauth) rd
    obtain ⟨aw2, k2, C2, rd2⟩ := claimSettlementTraceSubtract (by omega) rd1
    by_cases hbound : amount.toNat ≤ (solcSlotWordAt (claimSettlementSlot token) σ I).toNat
    · obtain ⟨k3, C3, rd3⟩ := midnightCheckedSub
        (by simp only [List.length_cons]; omega) hbound (by jump_dest) rd2
      by_cases hperm : I.perm = true
      · obtain ⟨aw4, k4, C4, rd4⟩ := claimSettlementTraceStore (by omega) hperm rd3
        have hs' : SourceState evm I
            (sstoreAccountMap I.codeOwner σ (claimSettlementSlot token)
              (UInt256.sub (solcSlotWordAt (claimSettlementSlot token) σ I) amount))
            (claimSettlementState evm token amount) :=
          hs.readModifyWrite (claimSettlementSlot token) (fun old ↦ UInt256.sub old amount)
        have hm := claimSettlementMemory_properties token amount
        rcases safeTransferSmallHeap false ∅ (sender := I.codeOwner) hstack
            (by rw [hm.1]; decide) (by decide) hm.2.1 hm.2.2 (by decide)
            hgas hfork hs' (by jump_dest) rd4 with
          hoog | ⟨hbody, hrev⟩ | ⟨evm', σ', out, mem', ptr', aw5, k5, C5,
            hbody, hs'', _, _, _, _, _, rd5⟩
        · exact reEquiv_outOfGas (Xi_error_of_X (by
            rw [← hcode] at hoog
            exact hoog))
        · exact hrev.reEquivExecutionRevert hcode hd hdec
            (claimSettlementCallReverts evm token amount receiver I.codeOwner hwv hhi hauth
              (hbal ▸ hbound) hperm hbody)
        · have hr := midnightBlocks.midnight_block_15786 (by omega) rd5
          exact hr.reEquivExecutionGen hcode hd hdec
            (claimSettlementReturns evm evm' token amount receiver I.codeOwner out hwv hhi hauth
              (hbal ▸ hbound) hperm hbody) hs''.accounts voidReturnEquiv
      · have hp : I.perm = false := Bool.eq_false_iff.mpr hperm
        have hr := claimSettlementTraceStatic
          (by simp only [List.length_cons]; omega) hp rd3
        exact hr.reEquivStaticHalt hcode hd hdec
          (claimSettlementStatic evm token amount receiver hwv hhi hauth (hbal ▸ hbound) hp)
    · have hr := midnightCheckedSubRevert (by simp only [List.length_cons]; omega)
        (Nat.lt_of_not_ge hbound) rd2
      exact hr.reEquivExecutionRevert hcode hd hdec
        (claimSettlementUnderflow evm token amount receiver hwv hhi hauth
          (by rw [hbal]; omega))
  · obtain ⟨k1, C1, rd1⟩ := midnightBlocks.midnight_block_17674_taken
      (by simp only [List.length_cons]; omega)
      (by rw [addressMask_computed]; exact fun h ↦ hauth (u256_sub_eq_zero_iff_eq.mp h))
      (by jump_dest) rd
    have hr := midnightBlocks.midnight_block_15788 (by simp only [List.length_cons]; omega) rd1
    exact hr.reEquivExecutionRevert hcode hd hdec
      (claimSettlementUnauthorized evm token amount receiver hwv hhi hauth)

/-- `claimSettlementFee(address,uint256,address)`: the theorem `Correct.lean` routes selector 4 to. -/
theorem midnightClaimSettlementFeeBody {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = midnightBytecode) (hsize : I.calldata.size < UInt256.size)
    (hfork : fork ≥ .osaka)
    (hgas : midnightGasBound g)
    (hsel : selIs I (midnightSelBytes 4)) :
    runtimeRefinementFor fork config contract σ σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (midnightSelBytes 4) rfl hsel
  have hd : dispatchMsg contract I.calldata = some claimSettlementFeeTransition := by
    apply midnightDispatch_claimSettlementFee <;>
      first | exact hsel | exact selectorNe_of_selIs hsel (by decide +kernel)
  obtain ⟨k, C, rd⟩ := midnightReachClaimSettlementFeeBody
    (σ := σ) (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g) hcode hsz hsize hsel
  by_cases hwv : I.weiValue = ⟨0⟩
  · have rd1 := midnightBlocks.midnight_block_17638_fallthrough (by simp) hwv rd
    by_cases hhi : I.calldata.size < calldataLimit
    · by_cases h100 : 100 ≤ I.calldata.size
      · have rd2 := midnightBlocks.midnight_block_17644_fallthrough (by simp)
          (entrySizeCheck_ok (bytes := 96) h100 hhi hsize) rd1
        have rd3 := midnightBlocks.midnight_block_17656 (by simp) (by jump_dest) rd2
        simp only [midnightBlocks.midnight_block_17656_stack] at rd3
        by_cases htoken : (calldataWord I.calldata 4).toNat < EVM.addressModulus
        · obtain ⟨k4, C4, rd4⟩ := midnightAddress4_ok (by simp) (by jump_dest) htoken rd3
          have rd5 := midnightBlocks.midnight_block_17663 (by simp) (by jump_dest) rd4
          simp only [midnightBlocks.midnight_block_17663_stack] at rd5
          by_cases hreceiver : (calldataWord I.calldata 68).toNat < EVM.addressModulus
          · obtain ⟨k6, C6, rd6⟩ := midnightAddress68_ok (by simp) (by jump_dest) hreceiver rd5
            change RD fork _ _ _ _ _ [calldataWord I.calldata 68, calldataWord I.calldata 36,
              calldataWord I.calldata 4, solcSelectorWord I] midnightEntryMemory _ _ _ _ _ at rd6
            have hdec := midnightDecodeTriple_ok "token" "amount" "receiver"
              (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
              h100 hhi hsize (decodeAddressWord (by omega) htoken)
              (decodeUint256Word (off := 36) (by omega)) (decodeAddressWord h100 hreceiver)
            have ht : UInt256.ofNat (AccountAddress.ofNat (calldataWord I.calldata 4).toNat).val =
                calldataWord I.calldata 4 := addressWord_eq_ofNat_address htoken
            have hr : UInt256.ofNat (AccountAddress.ofNat (calldataWord I.calldata 68).toNat).val =
                calldataWord I.calldata 68 := addressWord_eq_ofNat_address hreceiver
            rw [← ht, ← hr] at rd6
            exact claimSettlementBodyCore hcode hwv hhi hgas hfork hd hdec (by simp) rd6
          · have hr := midnightAddress68_revert (by simp) hreceiver rd5
            exact hr.reEquivDecodingFailed hcode hd
              (midnightDecodeTriple_none_right "token" "amount" "receiver" .address
                (.int (.uint ⟨256, by decide⟩)) .address h100 hhi hsize
                (decodeAddressWord (by omega) htoken)
                (decodeUint256Word (off := 36) (by omega)) (decodeAddressWord_none h100 hreceiver))
        · have hr := midnightAddress4_revert (by simp) htoken rd3
          exact hr.reEquivDecodingFailed hcode hd
            (midnightDecodeTriple_none_left "token" "amount" "receiver" .address
              (.int (.uint ⟨256, by decide⟩)) .address h100 hhi hsize
              (decodeAddressWord_none (by omega) htoken))
      · have rd2 := midnightBlocks.midnight_block_17644_taken (by simp)
          (by
            have hc : UInt256.slt (UInt256.lnot (UInt256.ofNat 3) + UInt256.ofNat I.calldata.size)
                (UInt256.ofNat 96) = ⟨1⟩ :=
              entrySizeCheck_short hsz (Nat.lt_of_not_ge h100) (by decide) hsize
            rw [hc]; decide)
          (by jump_dest) rd1
        have hr := midnightBlocks.midnight_block_6350 (by simp) rd2
        exact hr.reEquivDecodingFailed hcode hd
          (midnightDecodeTriple_none_short "token" "amount" "receiver" .address
            (.int (.uint ⟨256, by decide⟩)) .address hsz (Nat.lt_of_not_ge h100) hsize)
    · have rd2 := midnightBlocks.midnight_block_17644_taken (by simp)
        (by
          have hc : UInt256.slt (UInt256.lnot (UInt256.ofNat 3) + UInt256.ofNat I.calldata.size)
              (UInt256.ofNat 96) = ⟨1⟩ :=
            entrySizeCheck_huge (Nat.le_of_not_lt hhi) hsize (by decide)
          rw [hc]; decide)
        (by jump_dest) rd1
      have hr := midnightBlocks.midnight_block_6350 (by simp) rd2
      exact hr.reEquivDecodingFailed hcode hd
        (midnightDecodeTriple_none_huge "token" "amount" "receiver" .address
          (.int (.uint ⟨256, by decide⟩)) .address (Nat.le_of_not_lt hhi) hsize)
  · have rd1 := midnightBlocks.midnight_block_17638_taken (by simp) hwv (by jump_dest) rd
    have hr := midnightBlocks.midnight_block_6350 (by simp) rd1
    cases hdec : config.externalABI.decodeCalldata? (claimSettlementFeeTransition.params.map Param.name)
        (transitionSignature claimSettlementFeeTransition).paramTypes I.calldata with
    | none => exact hr.reEquivDecodingFailed hcode hd hdec
    | some args =>
      exact hr.reEquivExecutionRevert hcode hd hdec (bodyReverts_nonPayable hwv)

end Benchmarks.Midnight
