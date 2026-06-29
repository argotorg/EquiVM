import Examples.BlindAuction.Bid
import Examples.BlindAuction.Reveal
import Examples.BlindAuction.Withdraw
import Examples.BlindAuction.AuctionEnd
import Examples.BlindAuction.Bids
import Examples.BlindAuction.Ended
import Examples.BlindAuction.Beneficiary
import Examples.BlindAuction.BiddingEnd
import Examples.BlindAuction.RevealEnd
import Examples.BlindAuction.HighestBidder
import Examples.BlindAuction.HighestBid
import Reasoning.Initcode
import Reasoning.Refinement

/-!
# BlindAuction — top-level correctness proof

This file is the Phase 0 dispatcher assembly for
`blindAuctionCorrect : runtimeEquivalence!?! …`.  It follows the optimizer-on binary-search
dispatcher shape shared with Ballot/SimpleAuction, but with BlindAuction's payable top-level
dispatcher: calldata size and selector routing happen before any callvalue check, and non-payable
guards are proved inside the individual body files.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 2000000

namespace BlindAuction

/-- The deployed BlindAuction runtime bytecode refines the Solm specification. -/
theorem blindAuctionCorrect :
    runtimeEquivalence!?! blindAuctionConfig blindAuctionBytecode blindAuctionContract := by
  refine ⟨fun cA gh bl σ_evm σ_solm σ₀ g A I hcode hsize hperm
      hAccounts => ?_⟩
  by_cases hsz : 4 ≤ I.calldata.size
  · by_cases h0 : selIs I ⟨#[0x95, 0x7b, 0xb1, 0xe0]⟩
    · exact blindAuctionBidBodyCore hcode hsize hperm h0
        (blindAuctionReachHighBody 3 (by omega) ⟨449⟩ hcode hsz hsize
          (blindAuctionPivotNotTaken 3 (by omega) hsz
            (by simpa [selIs, blindAuctionHighSelBytes] using h0))
          (blindAuctionHighMatches 3 (by omega) hsz
            (by simpa [selIs, blindAuctionHighSelBytes] using h0)).1
          (blindAuctionHighMatches 3 (by omega) hsz
            (by simpa [selIs, blindAuctionHighSelBytes] using h0)).2
          (by jump_dest) (by decide)) hAccounts
    · by_cases h1 : selIs I ⟨#[0x90, 0x0f, 0x08, 0x0a]⟩
      · exact blindAuctionRevealBodyCore hcode hsize hperm h1
          (blindAuctionReachHighBody 1 (by omega) ⟨387⟩ hcode hsz hsize
            (blindAuctionPivotNotTaken 1 (by omega) hsz
              (by simpa [selIs, blindAuctionHighSelBytes] using h1))
            (blindAuctionHighMatches 1 (by omega) hsz
              (by simpa [selIs, blindAuctionHighSelBytes] using h1)).1
            (blindAuctionHighMatches 1 (by omega) hsz
              (by simpa [selIs, blindAuctionHighSelBytes] using h1)).2
            (by jump_dest) (by decide)) hAccounts
      · by_cases h2 : selIs I ⟨#[0x3c, 0xcf, 0xd6, 0x0b]⟩
        · exact blindAuctionWithdrawBodyCore hcode hsize hperm h2
            (blindAuctionReachLowBody 4 (by omega) ⟨332⟩ hcode hsz hsize
              (blindAuctionPivotTaken 4 (by omega) hsz
                (by simpa [selIs, blindAuctionLowSelBytes] using h2))
              (blindAuctionLowMatches 4 (by omega) hsz
                (by simpa [selIs, blindAuctionLowSelBytes] using h2)).1
              (blindAuctionLowMatches 4 (by omega) hsz
                (by simpa [selIs, blindAuctionLowSelBytes] using h2)).2
              (by jump_dest) (by decide)) hAccounts
        · by_cases h3 : selIs I ⟨#[0x2a, 0x24, 0xf4, 0x6c]⟩
          · exact blindAuctionAuctionEndBodyCore hcode hsize hperm h3
              (blindAuctionReachLowBody 2 (by omega) ⟨256⟩ hcode hsz hsize
                (blindAuctionPivotTaken 2 (by omega) hsz
                  (by simpa [selIs, blindAuctionLowSelBytes] using h3))
                (blindAuctionLowMatches 2 (by omega) hsz
                  (by simpa [selIs, blindAuctionLowSelBytes] using h3)).1
                (blindAuctionLowMatches 2 (by omega) hsz
                  (by simpa [selIs, blindAuctionLowSelBytes] using h3)).2
                (by jump_dest) (by decide)) hAccounts
          · by_cases h4 : selIs I ⟨#[0x38, 0xaf, 0x3e, 0xed]⟩
            · exact blindAuctionBeneficiaryBodyCore hcode hsize hperm h4
                (blindAuctionReachLowBody 3 (by omega) ⟨278⟩ hcode hsz hsize
                  (blindAuctionPivotTaken 3 (by omega) hsz
                    (by simpa [selIs, blindAuctionLowSelBytes] using h4))
                  (blindAuctionLowMatches 3 (by omega) hsz
                    (by simpa [selIs, blindAuctionLowSelBytes] using h4)).1
                  (blindAuctionLowMatches 3 (by omega) hsz
                    (by simpa [selIs, blindAuctionLowSelBytes] using h4)).2
                  (by jump_dest) (by decide)) hAccounts
            · by_cases h5 : selIs I ⟨#[0x42, 0x3b, 0x21, 0x7f]⟩
              · exact blindAuctionBiddingEndBodyCore hcode hsize hperm h5
                  (blindAuctionReachHighBody 0 (by omega) ⟨352⟩ hcode hsz hsize
                    (blindAuctionPivotNotTaken 0 (by omega) hsz
                      (by simpa [selIs, blindAuctionHighSelBytes] using h5))
                    (blindAuctionHighMatches 0 (by omega) hsz
                      (by simpa [selIs, blindAuctionHighSelBytes] using h5)).1
                    (blindAuctionHighMatches 0 (by omega) hsz
                      (by simpa [selIs, blindAuctionHighSelBytes] using h5)).2
                    (by jump_dest) (by decide)) hAccounts
              · by_cases h6 : selIs I ⟨#[0xa6, 0xe6, 0x64, 0x77]⟩
                · exact blindAuctionRevealEndBodyCore hcode hsize hperm h6
                    (blindAuctionReachHighBody 4 (by omega) ⟨468⟩ hcode hsz hsize
                      (blindAuctionPivotNotTaken 4 (by omega) hsz
                        (by simpa [selIs, blindAuctionHighSelBytes] using h6))
                      (blindAuctionHighMatches 4 (by omega) hsz
                        (by simpa [selIs, blindAuctionHighSelBytes] using h6)).1
                      (blindAuctionHighMatches 4 (by omega) hsz
                        (by simpa [selIs, blindAuctionHighSelBytes] using h6)).2
                      (by jump_dest) (by decide)) hAccounts
                · by_cases h7 : selIs I ⟨#[0x12, 0xfa, 0x6f, 0xeb]⟩
                  · exact blindAuctionEndedBodyCore hcode hsize hperm h7
                      (blindAuctionReachLowBody 1 (by omega) ⟨215⟩ hcode hsz hsize
                        (blindAuctionPivotTaken 1 (by omega) hsz
                          (by simpa [selIs, blindAuctionLowSelBytes] using h7))
                        (blindAuctionLowMatches 1 (by omega) hsz
                          (by simpa [selIs, blindAuctionLowSelBytes] using h7)).1
                        (blindAuctionLowMatches 1 (by omega) hsz
                          (by simpa [selIs, blindAuctionLowSelBytes] using h7)).2
                        (by jump_dest) (by decide)) hAccounts
                  · by_cases h8 : selIs I ⟨#[0x91, 0xf9, 0x01, 0x57]⟩
                    · exact blindAuctionHighestBidderBodyCore hcode hsize hperm h8
                        (blindAuctionReachHighBody 2 (by omega) ⟨418⟩ hcode hsz hsize
                          (blindAuctionPivotNotTaken 2 (by omega) hsz
                            (by simpa [selIs, blindAuctionHighSelBytes] using h8))
                          (blindAuctionHighMatches 2 (by omega) hsz
                            (by simpa [selIs, blindAuctionHighSelBytes] using h8)).1
                          (blindAuctionHighMatches 2 (by omega) hsz
                            (by simpa [selIs, blindAuctionHighSelBytes] using h8)).2
                          (by jump_dest) (by decide)) hAccounts
                    · by_cases h9 : selIs I ⟨#[0xd5, 0x7b, 0xde, 0x79]⟩
                      · exact blindAuctionHighestBidBodyCore hcode hsize hperm h9
                          (blindAuctionReachHighBody 5 (by omega) ⟨489⟩ hcode hsz hsize
                            (blindAuctionPivotNotTaken 5 (by omega) hsz
                              (by simpa [selIs, blindAuctionHighSelBytes] using h9))
                            (blindAuctionHighMatches 5 (by omega) hsz
                              (by simpa [selIs, blindAuctionHighSelBytes] using h9)).1
                            (blindAuctionHighMatches 5 (by omega) hsz
                              (by simpa [selIs, blindAuctionHighSelBytes] using h9)).2
                            (by jump_dest) (by decide)) hAccounts
                      · by_cases h10 : selIs I ⟨#[0x01, 0x49, 0x5c, 0x1c]⟩
                        · exact blindAuctionBidsBodyCore hcode hsize hperm h10
                            (blindAuctionReachLowBody 0 (by omega) ⟨158⟩ hcode hsz hsize
                              (blindAuctionPivotTaken 0 (by omega) hsz
                                (by simpa [selIs, blindAuctionLowSelBytes] using h10))
                              (blindAuctionLowMatches 0 (by omega) hsz
                                (by simpa [selIs, blindAuctionLowSelBytes] using h10)).1
                              (blindAuctionLowMatches 0 (by omega) hsz
                                (by simpa [selIs, blindAuctionLowSelBytes] using h10)).2
                              (by jump_dest) (by decide)) hAccounts
                        · refine blindAuctionNoDispatch hcode hsize hperm ?_
                          intro i hi
                          interval_cases i
                          · simpa [selIs, blindAuctionSelBytes] using h0
                          · simpa [selIs, blindAuctionSelBytes] using h1
                          · simpa [selIs, blindAuctionSelBytes] using h2
                          · simpa [selIs, blindAuctionSelBytes] using h3
                          · simpa [selIs, blindAuctionSelBytes] using h4
                          · simpa [selIs, blindAuctionSelBytes] using h5
                          · simpa [selIs, blindAuctionSelBytes] using h6
                          · simpa [selIs, blindAuctionSelBytes] using h7
                          · simpa [selIs, blindAuctionSelBytes] using h8
                          · simpa [selIs, blindAuctionSelBytes] using h9
                          · simpa [selIs, blindAuctionSelBytes] using h10
  · exact blindAuctionShortRevert hcode hsize hperm (by omega)

/-! ## Constructor side -/

theorem blindAuctionCtorPrefix_size : blindAuctionCtorPrefix.size = 146 := by
  native_decide

theorem blindAuctionBytecode_size : blindAuctionBytecode.size = 2137 := by
  native_decide

theorem blindAuctionInitcode_size : blindAuctionInitcode.size = 2283 := by
  rw [blindAuctionInitcode, ByteArray.size_append, blindAuctionCtorPrefix_size,
    blindAuctionBytecode_size]

theorem blindAuctionInitcode_runtime_window :
    blindAuctionInitcode.extract 146 (146 + 2137) = blindAuctionBytecode := by
  unfold blindAuctionInitcode
  exact extract_append_right' blindAuctionCtorPrefix blindAuctionBytecode 146 (146 + 2137)
    blindAuctionCtorPrefix_size.symm
    (by rw [blindAuctionCtorPrefix_size, blindAuctionBytecode_size])

noncomputable def blindAuctionCtorArgTail (biddingTime revealTime : UInt256)
    (beneficiaryAddress : AccountAddress) : ByteArray :=
  (EVM.Word.toBytesBE biddingTime).toByteArray
    ++ (EVM.Word.toBytesBE revealTime).toByteArray
    ++ (EVM.Word.toBytesBE (EVM.word beneficiaryAddress)).toByteArray

noncomputable def blindAuctionCtorCode (biddingTime revealTime : UInt256)
    (beneficiaryAddress : AccountAddress) : ByteArray :=
  blindAuctionInitcode ++ blindAuctionCtorArgTail biddingTime revealTime beneficiaryAddress

theorem blindAuctionCtorParams :
    blindAuctionContract.ctor.params =
      [ { name := "biddingTime", ty := uint256 },
        { name := "revealTime", ty := uint256 },
        { name := "beneficiaryAddress", ty := addr } ] :=
  rfl

theorem blindAuctionInitcode_decode_append (tail : ByteArray) (pc : UInt256)
    (hpc : pc.toNat < 146) :
    decode (blindAuctionInitcode ++ tail) pc = decode blindAuctionInitcode pc :=
  Reasoning.Theory.decode_append_left_window blindAuctionInitcode tail pc
    (by rw [blindAuctionInitcode_size]; omega) (by rw [blindAuctionInitcode_size]; norm_num)

macro "blind_ctor_decode" : tactic =>
  `(tactic|
    (first
      | rw [blindAuctionInitcode_decode_append _ _ (by decide)]
      | (unfold blindAuctionCtorCode; rw [blindAuctionInitcode_decode_append _ _ (by decide)]);
     native_decide))

macro "blind_ctor_jd" : tactic =>
  `(tactic|
    (first
      | (apply Reasoning.Theory.D_J_contains_append_left; native_decide)
      | (unfold blindAuctionCtorCode; apply Reasoning.Theory.D_J_contains_append_left; native_decide)))

open Lean in
macro "blind_ctor_run " base:term " with " "[" steps:evmStep,* "]" : term => do
  let mut acc := base
  for s in steps.getElems do
    match s with
    | `(evmStep| raw $op:ident $args*) =>
        acc ← `($(acc).$op $args*)
    | `(evmStep| $op:ident $args*) =>
        match op.getId with
        | `jump    => acc ← `($(acc).jump (by blind_ctor_decode) $(args[0]!) (by evm_ov))
        | `jumpiT  => acc ← `($(acc).jumpiT (by blind_ctor_decode) $(args[0]!) $(args[1]!)
                            (by evm_ov))
        | `jumpiNT => acc ← `($(acc).jumpiNT (by blind_ctor_decode) $(args[0]!) (by evm_ov))
        | _        => acc ← `($(acc).$op $args* (by blind_ctor_decode) (by evm_ov))
    | _ => Macro.throwUnsupported
  return acc

theorem blindAuctionDeployment_shape {args : List Value} {deployedInitcode : ByteArray} :
    blindAuctionConfig.selfDeployment blindAuctionInitcode args = some deployedInitcode →
    ∃ (biddingTime revealTime : Int) (beneficiaryAddress : AccountAddress),
      args = [.int biddingTime, .int revealTime, .address beneficiaryAddress]
        ∧ 0 ≤ biddingTime
        ∧ biddingTime < Int.ofNat (EVM.twoPow 256)
        ∧ 0 ≤ revealTime
        ∧ revealTime < Int.ofNat (EVM.twoPow 256)
        ∧ deployedInitcode =
            blindAuctionInitcode
              ++ (EVM.Word.toBytesBE (EVM.word biddingTime.toNat)).toByteArray
              ++ (EVM.Word.toBytesBE (EVM.word revealTime.toNat)).toByteArray
              ++ (EVM.Word.toBytesBE (EVM.word beneficiaryAddress)).toByteArray := by
  intro h
  change genSolidityConstructorDeployment blindAuctionContract.ctor.params
    blindAuctionInitcode args = some deployedInitcode at h
  rw [blindAuctionCtorParams] at h
  cases args with
  | nil =>
      simp [genSolidityConstructorDeployment, encodeABIValues?, encodeABIValuesFrom?,
        abiTupleHeadSize?, uint256, addr, uint256Int] at h
  | cons arg rest =>
      cases rest with
      | nil =>
          cases arg <;>
            simp [genSolidityConstructorDeployment, encodeABIValues?, encodeABIValuesFrom?,
              abiTupleHeadSize?, uint256, addr, uint256Int, staticABIEncodedSize?,
              isDynamicABIType, encodeABIValue?, encodeABIWord?] at h
      | cons arg2 rest =>
          cases rest with
          | nil =>
              cases arg <;> cases arg2 <;>
                simp [genSolidityConstructorDeployment, encodeABIValues?,
                  encodeABIValuesFrom?, abiTupleHeadSize?, uint256, addr, uint256Int,
                  staticABIEncodedSize?, isDynamicABIType, encodeABIValue?, encodeABIWord?] at h
          | cons arg3 rest =>
              cases rest with
              | cons arg4 rest =>
                  cases arg <;> cases arg2 <;> cases arg3 <;>
                    simp [genSolidityConstructorDeployment, encodeABIValues?,
                      encodeABIValuesFrom?, abiTupleHeadSize?, uint256, addr, uint256Int,
                      staticABIEncodedSize?, isDynamicABIType, encodeABIValue?, encodeABIWord?] at h
              | nil =>
                  cases arg <;> cases arg2 <;> cases arg3 <;>
                    simp [genSolidityConstructorDeployment, encodeABIValues?,
                      encodeABIValuesFrom?, abiTupleHeadSize?, uint256, addr, uint256Int,
                      staticABIEncodedSize?, isDynamicABIType, encodeABIValue?, encodeABIWord?] at h
                  rename_i biddingTime revealTime beneficiaryAddress
                  by_cases hbid :
                      0 ≤ biddingTime ∧ biddingTime < Int.ofNat (EVM.twoPow 256)
                  · by_cases hrev :
                        0 ≤ revealTime ∧ revealTime < Int.ofNat (EVM.twoPow 256)
                    · change ((((if 0 ≤ biddingTime ∧
                          biddingTime < Int.ofNat (EVM.twoPow 256) then
                            some (EVM.word biddingTime.toNat) else none).bind
                          fun word => some word.toBytesBE).bind
                        fun head => ((if 0 ≤ revealTime ∧
                          revealTime < Int.ofNat (EVM.twoPow 256) then
                            some (EVM.word revealTime.toNat) else none).bind
                          fun word => some word.toBytesBE).bind
                          fun tail => some (head ++
                            (tail ++ (EVM.word beneficiaryAddress).toBytesBE))).bind
                        fun args => some (blindAuctionInitcode ++ args.toByteArray))
                          = some deployedInitcode at h
                      rw [if_pos hbid, if_pos hrev] at h
                      simp at h
                      refine ⟨biddingTime, revealTime, beneficiaryAddress, rfl,
                        hbid.1, hbid.2, hrev.1, hrev.2, ?_⟩
                      simpa [ByteArray.append_assoc] using h.symm
                    · change ((((if 0 ≤ biddingTime ∧
                          biddingTime < Int.ofNat (EVM.twoPow 256) then
                            some (EVM.word biddingTime.toNat) else none).bind
                          fun word => some word.toBytesBE).bind
                        fun head => ((if 0 ≤ revealTime ∧
                          revealTime < Int.ofNat (EVM.twoPow 256) then
                            some (EVM.word revealTime.toNat) else none).bind
                          fun word => some word.toBytesBE).bind
                          fun tail => some (head ++
                            (tail ++ (EVM.word beneficiaryAddress).toBytesBE))).bind
                        fun args => some (blindAuctionInitcode ++ args.toByteArray))
                          = some deployedInitcode at h
                      rw [if_pos hbid, if_neg hrev] at h
                      simp at h
                  · change ((((if 0 ≤ biddingTime ∧
                        biddingTime < Int.ofNat (EVM.twoPow 256) then
                          some (EVM.word biddingTime.toNat) else none).bind
                        fun word => some word.toBytesBE).bind
                      fun head => ((if 0 ≤ revealTime ∧
                        revealTime < Int.ofNat (EVM.twoPow 256) then
                          some (EVM.word revealTime.toNat) else none).bind
                        fun word => some word.toBytesBE).bind
                        fun tail => some (head ++
                          (tail ++ (EVM.word beneficiaryAddress).toBytesBE))).bind
                      fun args => some (blindAuctionInitcode ++ args.toByteArray))
                        = some deployedInitcode at h
                    rw [if_neg hbid] at h
                    simp at h

noncomputable def blindAuctionBeneficiaryMem (biddingTime revealTime : UInt256)
    (beneficiaryAddress : AccountAddress) : ByteArray :=
  (blindAuctionCtorCode biddingTime revealTime beneficiaryAddress).write 2347 ByteArray.empty 0 32

noncomputable def blindAuctionBiddingMem (biddingTime revealTime : UInt256)
    (beneficiaryAddress : AccountAddress) : ByteArray :=
  (blindAuctionCtorCode biddingTime revealTime beneficiaryAddress).write 2283
    (blindAuctionBeneficiaryMem biddingTime revealTime beneficiaryAddress) 0 32

noncomputable def blindAuctionRevealMem (biddingTime revealTime : UInt256)
    (beneficiaryAddress : AccountAddress) : ByteArray :=
  (blindAuctionCtorCode biddingTime revealTime beneficiaryAddress).write 2315
    (blindAuctionBiddingMem biddingTime revealTime beneficiaryAddress) 0 32

theorem blindAuctionCtorArgTail_size (biddingTime revealTime : UInt256)
    (beneficiaryAddress : AccountAddress) :
    (blindAuctionCtorArgTail biddingTime revealTime beneficiaryAddress).size = 96 := by
  unfold blindAuctionCtorArgTail
  rw [ByteArray.size_append, ByteArray.size_append, word_toBytesBE_toByteArray_size,
    word_toBytesBE_toByteArray_size, word_toBytesBE_toByteArray_size]

theorem blindAuctionCtorCode_size (biddingTime revealTime : UInt256)
    (beneficiaryAddress : AccountAddress) :
    (blindAuctionCtorCode biddingTime revealTime beneficiaryAddress).size = 2379 := by
  rw [blindAuctionCtorCode, ByteArray.size_append, blindAuctionInitcode_size,
    blindAuctionCtorArgTail_size]

theorem blindAuctionBiddingArg_extract (biddingTime revealTime : UInt256)
    (beneficiaryAddress : AccountAddress) :
    (blindAuctionCtorCode biddingTime revealTime beneficiaryAddress).extract 2283 (2283 + 32)
      = (EVM.Word.toBytesBE biddingTime).toByteArray := by
  unfold blindAuctionCtorCode blindAuctionCtorArgTail
  rw [extract_append_right_window blindAuctionInitcode
    ((EVM.Word.toBytesBE biddingTime).toByteArray ++
      (EVM.Word.toBytesBE revealTime).toByteArray ++
      (EVM.Word.toBytesBE (EVM.word beneficiaryAddress)).toByteArray) 2283 (2283 + 32)
    (by rw [blindAuctionInitcode_size])]
  simp only [blindAuctionInitcode_size, Nat.sub_self, Nat.add_sub_cancel_left]
  rw [ByteArray.append_assoc]
  rw [extract_append_left (EVM.Word.toBytesBE biddingTime).toByteArray
    ((EVM.Word.toBytesBE revealTime).toByteArray ++
      (EVM.Word.toBytesBE (EVM.word beneficiaryAddress)).toByteArray) 0 32
    (by rw [word_toBytesBE_toByteArray_size])]
  rw [show 32 = (EVM.Word.toBytesBE biddingTime).toByteArray.size by
    rw [word_toBytesBE_toByteArray_size]]
  exact byteArray_extract_self _

theorem blindAuctionRevealArg_extract (biddingTime revealTime : UInt256)
    (beneficiaryAddress : AccountAddress) :
    (blindAuctionCtorCode biddingTime revealTime beneficiaryAddress).extract 2315 (2315 + 32)
      = (EVM.Word.toBytesBE revealTime).toByteArray := by
  unfold blindAuctionCtorCode blindAuctionCtorArgTail
  rw [extract_append_right_window blindAuctionInitcode
    ((EVM.Word.toBytesBE biddingTime).toByteArray ++
      (EVM.Word.toBytesBE revealTime).toByteArray ++
      (EVM.Word.toBytesBE (EVM.word beneficiaryAddress)).toByteArray) 2315 (2315 + 32)
    (by rw [blindAuctionInitcode_size]; omega)]
  simp only [blindAuctionInitcode_size]
  norm_num
  rw [extract_append_left
    ((EVM.Word.toBytesBE biddingTime).toByteArray ++
      (EVM.Word.toBytesBE revealTime).toByteArray)
    (EVM.Word.toBytesBE (EVM.word beneficiaryAddress)).toByteArray 32 64
    (by rw [ByteArray.size_append, word_toBytesBE_toByteArray_size,
      word_toBytesBE_toByteArray_size])]
  rw [extract_append_right_window (EVM.Word.toBytesBE biddingTime).toByteArray
    (EVM.Word.toBytesBE revealTime).toByteArray 32 64
    (by rw [word_toBytesBE_toByteArray_size])]
  simp only [word_toBytesBE_toByteArray_size, Nat.sub_self]
  norm_num
  rw [show 32 = (EVM.Word.toBytesBE revealTime).toByteArray.size by
    rw [word_toBytesBE_toByteArray_size]]
  exact byteArray_extract_self _

theorem blindAuctionBeneficiaryArg_extract (biddingTime revealTime : UInt256)
    (beneficiaryAddress : AccountAddress) :
    (blindAuctionCtorCode biddingTime revealTime beneficiaryAddress).extract 2347 (2347 + 32)
      = (EVM.Word.toBytesBE (EVM.word beneficiaryAddress)).toByteArray := by
  unfold blindAuctionCtorCode blindAuctionCtorArgTail
  rw [extract_append_right_window blindAuctionInitcode
    ((EVM.Word.toBytesBE biddingTime).toByteArray ++
      (EVM.Word.toBytesBE revealTime).toByteArray ++
      (EVM.Word.toBytesBE (EVM.word beneficiaryAddress)).toByteArray) 2347 (2347 + 32)
    (by rw [blindAuctionInitcode_size]; omega)]
  simp only [blindAuctionInitcode_size]
  norm_num
  rw [extract_append_right_window
    ((EVM.Word.toBytesBE biddingTime).toByteArray ++
      (EVM.Word.toBytesBE revealTime).toByteArray)
    (EVM.Word.toBytesBE (EVM.word beneficiaryAddress)).toByteArray 64 96
    (by rw [ByteArray.size_append, word_toBytesBE_toByteArray_size,
      word_toBytesBE_toByteArray_size])]
  simp only [ByteArray.size_append, word_toBytesBE_toByteArray_size]
  norm_num
  rw [show 32 = (EVM.Word.toBytesBE (EVM.word beneficiaryAddress)).toByteArray.size by
    rw [word_toBytesBE_toByteArray_size]]
  exact byteArray_extract_self _

theorem blindAuction_write0_size_ge_32 (src base : ByteArray) (srcAddr : ℕ)
    (hsrc : srcAddr + 32 ≤ src.size) :
    32 ≤ (src.write srcAddr base 0 32).size := by
  show 32 ≤ (src.write srcAddr base 0 32).data.size
  rw [write0_data_from src base srcAddr 32 (by decide) hsrc, Array.size_append]
  have hpart : (src.data.extract srcAddr (srcAddr + 32)).size = 32 := by
    rw [Array.size_extract]
    have : src.data.size = src.size := rfl
    omega
  omega

theorem blindAuctionBeneficiaryMem_read (biddingTime revealTime : UInt256)
    (beneficiaryAddress : AccountAddress) :
    (blindAuctionBeneficiaryMem biddingTime revealTime beneficiaryAddress).readWithPadding 0 32 =
      UInt256.toByteArray (EVM.word beneficiaryAddress) := by
  unfold blindAuctionBeneficiaryMem
  rw [write0_read_back_from_gen (blindAuctionCtorCode biddingTime revealTime beneficiaryAddress)
      ByteArray.empty 2347 32 (by decide)
    (by simp [blindAuctionCtorCode_size])
    (by decide)]
  rw [blindAuctionBeneficiaryArg_extract, word_toBytesBE_toByteArray_eq_toByteArray]

theorem blindAuctionBiddingMem_read (biddingTime revealTime : UInt256)
    (beneficiaryAddress : AccountAddress) :
    (blindAuctionBiddingMem biddingTime revealTime beneficiaryAddress).readWithPadding 0 32 =
      UInt256.toByteArray biddingTime := by
  unfold blindAuctionBiddingMem
  rw [write0_read_back_from_gen (blindAuctionCtorCode biddingTime revealTime beneficiaryAddress)
      (blindAuctionBeneficiaryMem biddingTime revealTime beneficiaryAddress) 2283 32 (by decide)
    (by simp [blindAuctionCtorCode_size])
    (by decide)]
  rw [blindAuctionBiddingArg_extract, word_toBytesBE_toByteArray_eq_toByteArray]

theorem blindAuctionRevealMem_read (biddingTime revealTime : UInt256)
    (beneficiaryAddress : AccountAddress) :
    (blindAuctionRevealMem biddingTime revealTime beneficiaryAddress).readWithPadding 0 32 =
      UInt256.toByteArray revealTime := by
  unfold blindAuctionRevealMem
  rw [write0_read_back_from_gen (blindAuctionCtorCode biddingTime revealTime beneficiaryAddress)
      (blindAuctionBiddingMem biddingTime revealTime beneficiaryAddress) 2315 32 (by decide)
    (by simp [blindAuctionCtorCode_size])
    (by decide)]
  rw [blindAuctionRevealArg_extract, word_toBytesBE_toByteArray_eq_toByteArray]

theorem blindAuctionBeneficiaryMem_mload (biddingTime revealTime : UInt256)
    (beneficiaryAddress : AccountAddress) :
    (if (⟨0⟩ : UInt256).toNat ≥
          (blindAuctionBeneficiaryMem biddingTime revealTime beneficiaryAddress).size
        ∨ (⟨0⟩ : UInt256) ≥ (UInt256.ofNat 1) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian
        ((blindAuctionBeneficiaryMem biddingTime revealTime beneficiaryAddress).readWithPadding 0 32)))
      = EVM.word beneficiaryAddress := by
  exact mloadWordValue_of_readWithPadding
    (mem := blindAuctionBeneficiaryMem biddingTime revealTime beneficiaryAddress)
    (aw := UInt256.ofNat 1) (off := ⟨0⟩) (v := EVM.word beneficiaryAddress)
    (by
      unfold blindAuctionBeneficiaryMem
      have hsz := blindAuction_write0_size_ge_32
          (blindAuctionCtorCode biddingTime revealTime beneficiaryAddress) ByteArray.empty 2347
        (by simp [blindAuctionCtorCode_size])
      have hz : (⟨0⟩ : UInt256).toNat = 0 := by decide
      rw [hz]
      omega)
    (by decide)
    (blindAuctionBeneficiaryMem_read biddingTime revealTime beneficiaryAddress)

theorem blindAuctionBiddingMem_mload (biddingTime revealTime : UInt256)
    (beneficiaryAddress : AccountAddress) :
    (if (⟨0⟩ : UInt256).toNat ≥
          (blindAuctionBiddingMem biddingTime revealTime beneficiaryAddress).size
        ∨ (⟨0⟩ : UInt256) ≥ (UInt256.ofNat 1) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian
        ((blindAuctionBiddingMem biddingTime revealTime beneficiaryAddress).readWithPadding 0 32)))
      = biddingTime := by
  exact mloadWordValue_of_readWithPadding
    (mem := blindAuctionBiddingMem biddingTime revealTime beneficiaryAddress)
    (aw := UInt256.ofNat 1) (off := ⟨0⟩) (v := biddingTime)
    (by
      unfold blindAuctionBiddingMem
      have hsz := blindAuction_write0_size_ge_32
        (blindAuctionCtorCode biddingTime revealTime beneficiaryAddress)
          (blindAuctionBeneficiaryMem biddingTime revealTime beneficiaryAddress) 2283
        (by simp [blindAuctionCtorCode_size])
      have hz : (⟨0⟩ : UInt256).toNat = 0 := by decide
      rw [hz]
      omega)
    (by decide)
    (blindAuctionBiddingMem_read biddingTime revealTime beneficiaryAddress)

theorem blindAuctionRevealMem_mload (biddingTime revealTime : UInt256)
    (beneficiaryAddress : AccountAddress) :
    (if (⟨0⟩ : UInt256).toNat ≥
          (blindAuctionRevealMem biddingTime revealTime beneficiaryAddress).size
        ∨ (⟨0⟩ : UInt256) ≥ (UInt256.ofNat 1) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian
        ((blindAuctionRevealMem biddingTime revealTime beneficiaryAddress).readWithPadding 0 32)))
      = revealTime := by
  exact mloadWordValue_of_readWithPadding
    (mem := blindAuctionRevealMem biddingTime revealTime beneficiaryAddress)
    (aw := UInt256.ofNat 1) (off := ⟨0⟩) (v := revealTime)
    (by
      unfold blindAuctionRevealMem
      have hsz := blindAuction_write0_size_ge_32
        (blindAuctionCtorCode biddingTime revealTime beneficiaryAddress)
          (blindAuctionBiddingMem biddingTime revealTime beneficiaryAddress) 2315
        (by simp [blindAuctionCtorCode_size])
      have hz : (⟨0⟩ : UInt256).toNat = 0 := by decide
      rw [hz]
      omega)
    (by decide)
    (blindAuctionRevealMem_read biddingTime revealTime beneficiaryAddress)

theorem blindAuctionCtorCheckedAddOverflowLt (base addend : UInt256)
    (hover : UInt256.size ≤ base.toNat + addend.toNat) :
    UInt256.lt (addend + base) base = ⟨1⟩ :=
  constructorCheckedAddOverflowLt base addend hover

theorem blindAuctionCtorCheckedAddNoOverflowLt (base addend : UInt256)
    (hno : ¬ UInt256.size ≤ base.toNat + addend.toNat) :
    UInt256.lt (addend + base) base = ⟨0⟩ :=
  constructorCheckedAddNoOverflowLt base addend hno

noncomputable def blindAuctionReturnMem (biddingTime revealTime : UInt256)
    (beneficiaryAddress : AccountAddress) : ByteArray :=
  (blindAuctionCtorCode biddingTime revealTime beneficiaryAddress).write 146
    (blindAuctionRevealMem biddingTime revealTime beneficiaryAddress) 0 2137

theorem blindAuctionRuntime_codecopy_mem (biddingTime revealTime : UInt256)
    (beneficiaryAddress : AccountAddress) :
    (blindAuctionCtorCode biddingTime revealTime beneficiaryAddress).write 146
      (blindAuctionRevealMem biddingTime revealTime beneficiaryAddress) 0 2137 =
        blindAuctionReturnMem biddingTime revealTime beneficiaryAddress := rfl

theorem blindAuctionReturnMem_read (biddingTime revealTime : UInt256)
    (beneficiaryAddress : AccountAddress) :
    (blindAuctionReturnMem biddingTime revealTime beneficiaryAddress).readWithPadding 0 2137 =
      blindAuctionBytecode := by
  unfold blindAuctionReturnMem
  rw [write0_read_back_from_gen (blindAuctionCtorCode biddingTime revealTime beneficiaryAddress)
    (blindAuctionRevealMem biddingTime revealTime beneficiaryAddress) 146 2137 (by decide)
    (by rw [blindAuctionCtorCode_size]; omega)
    (by decide)]
  have hleft :
      (blindAuctionCtorCode biddingTime revealTime beneficiaryAddress).extract 146 (146 + 2137) =
        blindAuctionInitcode.extract 146 (146 + 2137) := by
    have h := extract_append_left blindAuctionInitcode
      (blindAuctionCtorArgTail biddingTime revealTime beneficiaryAddress) 146 (146 + 2137)
      (by rw [blindAuctionInitcode_size])
    simpa [blindAuctionCtorCode] using h
  rw [hleft, blindAuctionInitcode_runtime_window]

def blindAuctionCtorOldBeneficiarySlot (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  (σ.find? I.codeOwner |>.option ⟨0⟩ (fun ac => ac.storage.findD ⟨0⟩ ⟨0⟩))

def blindAuctionCtorBeneficiaryStoreWord (σ : AccountMap) (I : ExecutionEnv)
    (beneficiaryAddress : AccountAddress) : UInt256 :=
  blindAuctionSetAddressWord (blindAuctionCtorOldBeneficiarySlot σ I)
    (EVM.word beneficiaryAddress)

def blindAuctionCtorAfterBiddingEndMap (σ : AccountMap) (I : ExecutionEnv)
    (biddingTime : UInt256) (beneficiaryAddress : AccountAddress) : AccountMap :=
  sstoreAccountMap I.codeOwner
    (sstoreAccountMap I.codeOwner σ ⟨0⟩
      (blindAuctionCtorBeneficiaryStoreWord σ I beneficiaryAddress))
    ⟨1⟩ (UInt256.ofNat I.header.timestamp + biddingTime)

def blindAuctionCtorBiddingEndWord (σ : AccountMap) (I : ExecutionEnv)
    (biddingTime : UInt256) (beneficiaryAddress : AccountAddress) : UInt256 :=
  ((blindAuctionCtorAfterBiddingEndMap σ I biddingTime beneficiaryAddress).find? I.codeOwner).option
    ⟨0⟩ (fun ac => ac.storage.findD ⟨1⟩ ⟨0⟩)

theorem blindAuctionInitcodeNonpayableRevert
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader}
    {blocks : ProcessedBlocks}
    {σ : AccountMap}
    {σ₀ : AccountMap}
    {A : Substate}
    {I : ExecutionEnv}
    {g : Sat256}
    (tail : ByteArray)
    (hcode : I.code = blindAuctionInitcode ++ tail)
    (hwv : I.weiValue ≠ ⟨0⟩) :
    RDrev (blindAuctionInitcode ++ tail) g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) := by
  have rd0 :
      RD (blindAuctionInitcode ++ tail) I g
        (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨0⟩ []
        ByteArray.empty (UInt256.ofNat 0) ByteArray.empty (createdAccounts, σ) 0 0 :=
    RD.initState hcode
  have rd6 := blind_ctor_run rd0 with [
    callvalue, dup1, iszero, push1 ⟨9⟩, jumpiNT (isZero_eq_zero_of_ne hwv)]
  exact rd6.revertStub (by blind_ctor_decode) (by blind_ctor_decode) (by blind_ctor_decode)
    (by simp)

theorem blindAuctionInitcodeBiddingOverflowRevert
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader}
    {blocks : ProcessedBlocks}
    {σ : AccountMap}
    {σ₀ : AccountMap}
    {A : Substate}
    {I : ExecutionEnv}
    {g : Sat256}
    (biddingTime revealTime : UInt256)
    (beneficiaryAddress : AccountAddress)
    (hcode : I.code = blindAuctionCtorCode biddingTime revealTime beneficiaryAddress)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hover : UInt256.size ≤ (UInt256.ofNat I.header.timestamp).toNat + biddingTime.toNat) :
    RDrev (blindAuctionCtorCode biddingTime revealTime beneficiaryAddress) g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) := by
  have rd0 :
      RD (blindAuctionCtorCode biddingTime revealTime beneficiaryAddress) I g
        (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨0⟩ []
        ByteArray.empty (UInt256.ofNat 0) ByteArray.empty (createdAccounts, σ) 0 0 :=
    RD.initState hcode
  let oldBeneficiarySlot : UInt256 :=
    (σ.find? I.codeOwner |>.option ⟨0⟩ (fun ac => ac.storage.findD ⟨0⟩ ⟨0⟩))
  have rdBeforeSload := blind_ctor_run rd0 with [
    callvalue, dup1, iszero, push1 ⟨9⟩,
    jumpiT (by rw [hwv]; decide) (by blind_ctor_jd),
    jumpdest, pop, push1 ⟨32⟩, push2 ⟨2347⟩, push0,
    raw codecopy 3 (blindAuctionBeneficiaryMem biddingTime revealTime beneficiaryAddress)
      (UInt256.ofNat 1)
      (by blind_ctor_decode)
      mem_cost
      rfl
      (by decide) (by evm_ov),
    push0,
    raw mload 0 (EVM.word beneficiaryAddress) (UInt256.ofNat 1)
      (by blind_ctor_decode)
      mem_cost
      (blindAuctionBeneficiaryMem_mload biddingTime revealTime beneficiaryAddress)
      (by decide) (by evm_ov),
    dup1, push20 solcAddrMask, and, push0]
  obtain ⟨kSload, CSload, rdAfterSload⟩ :=
    rdBeforeSload.sload (by blind_ctor_decode) (by evm_ov)
  have rdBeforeStore := blind_ctor_run rdAfterSload with [
    push20 solcAddrMask, not, and, lor, swap1, pop, push0]
  have hpacked :
      UInt256.lor (UInt256.land (UInt256.lnot solcAddrMask) oldBeneficiarySlot)
          (UInt256.land solcAddrMask (EVM.word beneficiaryAddress)) =
        blindAuctionSetAddressWord oldBeneficiarySlot (EVM.word beneficiaryAddress) := by
    unfold blindAuctionSetAddressWord
    rw [u256_land_comm (UInt256.lnot solcAddrMask) oldBeneficiarySlot,
      u256_land_comm solcAddrMask (EVM.word beneficiaryAddress)]
  rw [hpacked] at rdBeforeStore
  obtain ⟨k', C', rdAfterStore⟩ :=
    rdBeforeStore.sstore hperm (by blind_ctor_decode) (by evm_ov)
  have rdBeforeLt := blind_ctor_run rdAfterStore with [
    push1 ⟨32⟩, push2 ⟨2283⟩, push0,
    raw codecopy 0 (blindAuctionBiddingMem biddingTime revealTime beneficiaryAddress)
      (UInt256.ofNat 1)
      (by blind_ctor_decode)
      mem_cost
      rfl
      (by decide) (by evm_ov),
    push0,
    raw mload 0 biddingTime (UInt256.ofNat 1)
      (by blind_ctor_decode)
      mem_cost
      (blindAuctionBiddingMem_mload biddingTime revealTime beneficiaryAddress)
      (by decide) (by evm_ov),
    timestamp, dup1, dup3, add, lt]
  have hlt := blindAuctionCtorCheckedAddOverflowLt (UInt256.ofNat I.header.timestamp)
    biddingTime hover
  have rdBeforeJump := rdBeforeLt
  rw [hlt] at rdBeforeJump
  have rd142 := blind_ctor_run rdBeforeJump with [
    swap1, pop, push1 ⟨142⟩, jumpiT one_ne_zero_uint (by blind_ctor_jd), jumpdest]
  exact rd142.revertStub (by blind_ctor_decode) (by blind_ctor_decode) (by blind_ctor_decode)
    (by simp)

theorem blindAuctionInitcodeRevealOverflowRevert
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader}
    {blocks : ProcessedBlocks}
    {σ : AccountMap}
    {σ₀ : AccountMap}
    {A : Substate}
    {I : ExecutionEnv}
    {g : Sat256}
    (biddingTime revealTime : UInt256)
    (beneficiaryAddress : AccountAddress)
    (hcode : I.code = blindAuctionCtorCode biddingTime revealTime beneficiaryAddress)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hnoBid : ¬ UInt256.size ≤ (UInt256.ofNat I.header.timestamp).toNat + biddingTime.toNat)
    (hoverReveal : UInt256.size ≤
      (blindAuctionCtorBiddingEndWord σ I biddingTime beneficiaryAddress).toNat
        + revealTime.toNat) :
    RDrev (blindAuctionCtorCode biddingTime revealTime beneficiaryAddress) g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) := by
  have rd0 :
      RD (blindAuctionCtorCode biddingTime revealTime beneficiaryAddress) I g
        (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨0⟩ []
        ByteArray.empty (UInt256.ofNat 0) ByteArray.empty (createdAccounts, σ) 0 0 :=
    RD.initState hcode
  let oldBeneficiarySlot : UInt256 :=
    (σ.find? I.codeOwner |>.option ⟨0⟩ (fun ac => ac.storage.findD ⟨0⟩ ⟨0⟩))
  let beneficiaryStoreWord : UInt256 :=
    blindAuctionSetAddressWord oldBeneficiarySlot (EVM.word beneficiaryAddress)
  have rdBeforeSload := blind_ctor_run rd0 with [
    callvalue, dup1, iszero, push1 ⟨9⟩,
    jumpiT (by rw [hwv]; decide) (by blind_ctor_jd),
    jumpdest, pop, push1 ⟨32⟩, push2 ⟨2347⟩, push0,
    raw codecopy 3 (blindAuctionBeneficiaryMem biddingTime revealTime beneficiaryAddress)
      (UInt256.ofNat 1)
      (by blind_ctor_decode)
      mem_cost
      rfl
      (by decide) (by evm_ov),
    push0,
    raw mload 0 (EVM.word beneficiaryAddress) (UInt256.ofNat 1)
      (by blind_ctor_decode)
      mem_cost
      (blindAuctionBeneficiaryMem_mload biddingTime revealTime beneficiaryAddress)
      (by decide) (by evm_ov),
    dup1, push20 solcAddrMask, and, push0]
  obtain ⟨kSload, CSload, rdAfterSload⟩ :=
    rdBeforeSload.sload (by blind_ctor_decode) (by evm_ov)
  have rdBeforeStore := blind_ctor_run rdAfterSload with [
    push20 solcAddrMask, not, and, lor, swap1, pop, push0]
  have hpacked :
      UInt256.lor (UInt256.land (UInt256.lnot solcAddrMask) oldBeneficiarySlot)
          (UInt256.land solcAddrMask (EVM.word beneficiaryAddress)) =
        beneficiaryStoreWord := by
    unfold beneficiaryStoreWord blindAuctionSetAddressWord
    rw [u256_land_comm (UInt256.lnot solcAddrMask) oldBeneficiarySlot,
      u256_land_comm solcAddrMask (EVM.word beneficiaryAddress)]
  rw [hpacked] at rdBeforeStore
  obtain ⟨k', C', rdAfterBeneficiaryStore⟩ :=
    rdBeforeStore.sstore hperm (by blind_ctor_decode) (by evm_ov)
  have rdBeforeBidLt := blind_ctor_run rdAfterBeneficiaryStore with [
    push1 ⟨32⟩, push2 ⟨2283⟩, push0,
    raw codecopy 0 (blindAuctionBiddingMem biddingTime revealTime beneficiaryAddress)
      (UInt256.ofNat 1)
      (by blind_ctor_decode)
      mem_cost
      rfl
      (by decide) (by evm_ov),
    push0,
    raw mload 0 biddingTime (UInt256.ofNat 1)
      (by blind_ctor_decode)
      mem_cost
      (blindAuctionBiddingMem_mload biddingTime revealTime beneficiaryAddress)
      (by decide) (by evm_ov),
    timestamp, dup1, dup3, add, lt]
  have hbidLt := blindAuctionCtorCheckedAddNoOverflowLt (UInt256.ofNat I.header.timestamp)
    biddingTime hnoBid
  have rdBeforeBidJump := rdBeforeBidLt
  rw [hbidLt] at rdBeforeBidJump
  have rdBeforeBiddingEndStore := blind_ctor_run rdBeforeBidJump with [
    swap1, pop, push1 ⟨142⟩, jumpiNT (by decide),
    push0,
    raw mload 0 biddingTime (UInt256.ofNat 1)
      (by blind_ctor_decode)
      mem_cost
      (blindAuctionBiddingMem_mload biddingTime revealTime beneficiaryAddress)
      (by decide) (by evm_ov),
    timestamp, add, push1 ⟨1⟩]
  obtain ⟨k'', C'', rdAfterBiddingEndStore⟩ :=
    rdBeforeBiddingEndStore.sstore hperm (by blind_ctor_decode) (by evm_ov)
  have rdBeforeRevealLtSload := blind_ctor_run rdAfterBiddingEndStore with [
    push1 ⟨32⟩, push2 ⟨2315⟩, push0,
    raw codecopy 0 (blindAuctionRevealMem biddingTime revealTime beneficiaryAddress)
      (UInt256.ofNat 1)
      (by blind_ctor_decode)
      mem_cost
      rfl
      (by decide) (by evm_ov),
    push0,
    raw mload 0 revealTime (UInt256.ofNat 1)
      (by blind_ctor_decode)
      mem_cost
      (blindAuctionRevealMem_mload biddingTime revealTime beneficiaryAddress)
      (by decide) (by evm_ov),
    push1 ⟨1⟩]
  obtain ⟨kSloadBid, CSloadBid, rdAfterBidSload⟩ :=
    rdBeforeRevealLtSload.sload (by blind_ctor_decode) (by evm_ov)
  let biddingEndWord : UInt256 :=
    ((sstoreAccountMap I.codeOwner
      (sstoreAccountMap I.codeOwner σ ⟨0⟩ beneficiaryStoreWord)
      ⟨1⟩ (UInt256.ofNat I.header.timestamp + biddingTime)).find? I.codeOwner).option
        ⟨0⟩ (fun ac => ac.storage.findD ⟨1⟩ ⟨0⟩)
  change RD (blindAuctionCtorCode biddingTime revealTime beneficiaryAddress) I g
    (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) _
    [biddingEndWord, revealTime]
    (blindAuctionRevealMem biddingTime revealTime beneficiaryAddress) (UInt256.ofNat 1)
    ByteArray.empty _ _ _ at rdAfterBidSload
  have rdBeforeRevealLt := blind_ctor_run rdAfterBidSload with [
    dup1, dup3, add, lt]
  have hoverReveal' : UInt256.size ≤
      biddingEndWord.toNat + revealTime.toNat := by
    simpa [biddingEndWord, beneficiaryStoreWord, oldBeneficiarySlot,
      blindAuctionCtorBiddingEndWord, blindAuctionCtorAfterBiddingEndMap,
      blindAuctionCtorBeneficiaryStoreWord, blindAuctionCtorOldBeneficiarySlot] using hoverReveal
  have hrevLt := blindAuctionCtorCheckedAddOverflowLt
    biddingEndWord revealTime hoverReveal'
  have rdBeforeRevealJump := rdBeforeRevealLt
  rw [hrevLt] at rdBeforeRevealJump
  have rd142 := blind_ctor_run rdBeforeRevealJump with [
    swap1, pop, push1 ⟨142⟩, jumpiT one_ne_zero_uint (by blind_ctor_jd), jumpdest]
  exact rd142.revertStub (by blind_ctor_decode) (by blind_ctor_decode) (by blind_ctor_decode)
    (by simp)

theorem blindAuctionInitcodeSuccess
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader}
    {blocks : ProcessedBlocks}
    {σ : AccountMap}
    {σ₀ : AccountMap}
    {A : Substate}
    {I : ExecutionEnv}
    {g : Sat256}
    (biddingTime revealTime : UInt256)
    (beneficiaryAddress : AccountAddress)
    (hcode : I.code = blindAuctionCtorCode biddingTime revealTime beneficiaryAddress)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hnoBid : ¬ UInt256.size ≤ (UInt256.ofNat I.header.timestamp).toNat + biddingTime.toNat)
    (hnoReveal : ¬ UInt256.size ≤
      (blindAuctionCtorBiddingEndWord σ I biddingTime beneficiaryAddress).toNat
        + revealTime.toNat) :
    RDret (blindAuctionCtorCode biddingTime revealTime beneficiaryAddress) g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      (createdAccounts,
        sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner
            (sstoreAccountMap I.codeOwner σ ⟨0⟩
              (blindAuctionSetAddressWord
                (σ.find? I.codeOwner |>.option ⟨0⟩ (fun ac => ac.storage.findD ⟨0⟩ ⟨0⟩))
                (EVM.word beneficiaryAddress)))
            ⟨1⟩ (UInt256.ofNat I.header.timestamp + biddingTime))
          ⟨2⟩ (revealTime + blindAuctionCtorBiddingEndWord σ I biddingTime beneficiaryAddress))
      blindAuctionBytecode := by
  have rd0 :
      RD (blindAuctionCtorCode biddingTime revealTime beneficiaryAddress) I g
        (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨0⟩ []
        ByteArray.empty (UInt256.ofNat 0) ByteArray.empty (createdAccounts, σ) 0 0 :=
    RD.initState hcode
  let oldBeneficiarySlot : UInt256 :=
    (σ.find? I.codeOwner |>.option ⟨0⟩ (fun ac => ac.storage.findD ⟨0⟩ ⟨0⟩))
  let beneficiaryStoreWord : UInt256 :=
    blindAuctionSetAddressWord oldBeneficiarySlot (EVM.word beneficiaryAddress)
  have rdBeforeSload := blind_ctor_run rd0 with [
    callvalue, dup1, iszero, push1 ⟨9⟩,
    jumpiT (by rw [hwv]; decide) (by blind_ctor_jd),
    jumpdest, pop, push1 ⟨32⟩, push2 ⟨2347⟩, push0,
    raw codecopy 3 (blindAuctionBeneficiaryMem biddingTime revealTime beneficiaryAddress)
      (UInt256.ofNat 1)
      (by blind_ctor_decode)
      mem_cost
      rfl
      (by decide) (by evm_ov),
    push0,
    raw mload 0 (EVM.word beneficiaryAddress) (UInt256.ofNat 1)
      (by blind_ctor_decode)
      mem_cost
      (blindAuctionBeneficiaryMem_mload biddingTime revealTime beneficiaryAddress)
      (by decide) (by evm_ov),
    dup1, push20 solcAddrMask, and, push0]
  obtain ⟨kSload, CSload, rdAfterSload⟩ :=
    rdBeforeSload.sload (by blind_ctor_decode) (by evm_ov)
  have rdBeforeStore := blind_ctor_run rdAfterSload with [
    push20 solcAddrMask, not, and, lor, swap1, pop, push0]
  have hpacked :
      UInt256.lor (UInt256.land (UInt256.lnot solcAddrMask) oldBeneficiarySlot)
          (UInt256.land solcAddrMask (EVM.word beneficiaryAddress)) =
        beneficiaryStoreWord := by
    unfold beneficiaryStoreWord blindAuctionSetAddressWord
    rw [u256_land_comm (UInt256.lnot solcAddrMask) oldBeneficiarySlot,
      u256_land_comm solcAddrMask (EVM.word beneficiaryAddress)]
  rw [hpacked] at rdBeforeStore
  obtain ⟨k', C', rdAfterBeneficiaryStore⟩ :=
    rdBeforeStore.sstore hperm (by blind_ctor_decode) (by evm_ov)
  have rdBeforeBidLt := blind_ctor_run rdAfterBeneficiaryStore with [
    push1 ⟨32⟩, push2 ⟨2283⟩, push0,
    raw codecopy 0 (blindAuctionBiddingMem biddingTime revealTime beneficiaryAddress)
      (UInt256.ofNat 1)
      (by blind_ctor_decode)
      mem_cost
      rfl
      (by decide) (by evm_ov),
    push0,
    raw mload 0 biddingTime (UInt256.ofNat 1)
      (by blind_ctor_decode)
      mem_cost
      (blindAuctionBiddingMem_mload biddingTime revealTime beneficiaryAddress)
      (by decide) (by evm_ov),
    timestamp, dup1, dup3, add, lt]
  have hbidLt := blindAuctionCtorCheckedAddNoOverflowLt (UInt256.ofNat I.header.timestamp)
    biddingTime hnoBid
  have rdBeforeBidJump := rdBeforeBidLt
  rw [hbidLt] at rdBeforeBidJump
  have rdBeforeBiddingEndStore := blind_ctor_run rdBeforeBidJump with [
    swap1, pop, push1 ⟨142⟩, jumpiNT (by decide),
    push0,
    raw mload 0 biddingTime (UInt256.ofNat 1)
      (by blind_ctor_decode)
      mem_cost
      (blindAuctionBiddingMem_mload biddingTime revealTime beneficiaryAddress)
      (by decide) (by evm_ov),
    timestamp, add, push1 ⟨1⟩]
  obtain ⟨k'', C'', rdAfterBiddingEndStore⟩ :=
    rdBeforeBiddingEndStore.sstore hperm (by blind_ctor_decode) (by evm_ov)
  have rdBeforeRevealLtSload := blind_ctor_run rdAfterBiddingEndStore with [
    push1 ⟨32⟩, push2 ⟨2315⟩, push0,
    raw codecopy 0 (blindAuctionRevealMem biddingTime revealTime beneficiaryAddress)
      (UInt256.ofNat 1)
      (by blind_ctor_decode)
      mem_cost
      rfl
      (by decide) (by evm_ov),
    push0,
    raw mload 0 revealTime (UInt256.ofNat 1)
      (by blind_ctor_decode)
      mem_cost
      (blindAuctionRevealMem_mload biddingTime revealTime beneficiaryAddress)
      (by decide) (by evm_ov),
    push1 ⟨1⟩]
  obtain ⟨kSloadBid, CSloadBid, rdAfterBidSload⟩ :=
    rdBeforeRevealLtSload.sload (by blind_ctor_decode) (by evm_ov)
  let biddingEndWord : UInt256 :=
    ((sstoreAccountMap I.codeOwner
      (sstoreAccountMap I.codeOwner σ ⟨0⟩ beneficiaryStoreWord)
      ⟨1⟩ (UInt256.ofNat I.header.timestamp + biddingTime)).find? I.codeOwner).option
        ⟨0⟩ (fun ac => ac.storage.findD ⟨1⟩ ⟨0⟩)
  change RD (blindAuctionCtorCode biddingTime revealTime beneficiaryAddress) I g
    (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) _
    [biddingEndWord, revealTime]
    (blindAuctionRevealMem biddingTime revealTime beneficiaryAddress) (UInt256.ofNat 1)
    ByteArray.empty _ _ _ at rdAfterBidSload
  have rdBeforeRevealLt := blind_ctor_run rdAfterBidSload with [
    dup1, dup3, add, lt]
  have hnoReveal' : ¬ UInt256.size ≤
      biddingEndWord.toNat + revealTime.toNat := by
    simpa [biddingEndWord, beneficiaryStoreWord, oldBeneficiarySlot,
      blindAuctionCtorBiddingEndWord, blindAuctionCtorAfterBiddingEndMap,
      blindAuctionCtorBeneficiaryStoreWord, blindAuctionCtorOldBeneficiarySlot] using hnoReveal
  have hrevLt := blindAuctionCtorCheckedAddNoOverflowLt
    biddingEndWord revealTime hnoReveal'
  have rdBeforeRevealJump := rdBeforeRevealLt
  rw [hrevLt] at rdBeforeRevealJump
  have rdBeforeRevealEndStore := blind_ctor_run rdBeforeRevealJump with [
    swap1, pop, push1 ⟨142⟩, jumpiNT (by decide),
    push0,
    raw mload 0 revealTime (UInt256.ofNat 1)
      (by blind_ctor_decode)
      mem_cost
      (blindAuctionRevealMem_mload biddingTime revealTime beneficiaryAddress)
      (by decide) (by evm_ov),
    push1 ⟨1⟩]
  obtain ⟨kSloadBid', CSloadBid', rdAfterBidSload'⟩ :=
    rdBeforeRevealEndStore.sload (by blind_ctor_decode) (by evm_ov)
  have rdBeforeRevealEndStore' := blind_ctor_run rdAfterBidSload' with [
    add, push1 ⟨2⟩]
  obtain ⟨k''', C''', rdAfterRevealEndStore⟩ :=
    rdBeforeRevealEndStore'.sstore hperm (by blind_ctor_decode) (by evm_ov)
  have rdBeforeReturn := blind_ctor_run rdAfterRevealEndStore with [
    push2 ⟨2137⟩, push2 ⟨146⟩, push0,
    raw codecopy 206 (blindAuctionReturnMem biddingTime revealTime beneficiaryAddress)
      (UInt256.ofNat 67)
      (by blind_ctor_decode)
      mem_cost
      (blindAuctionRuntime_codecopy_mem biddingTime revealTime beneficiaryAddress)
      (by decide) (by evm_ov),
    push2 ⟨2137⟩, push0]
  simpa [beneficiaryStoreWord, oldBeneficiarySlot, blindAuctionCtorBiddingEndWord,
    blindAuctionCtorAfterBiddingEndMap, blindAuctionCtorBeneficiaryStoreWord,
    blindAuctionCtorOldBeneficiarySlot, u256_add_comm, u256_add_assoc] using
    rdBeforeReturn.ret 0 blindAuctionBytecode
      (by blind_ctor_decode)
      mem_cost
      (blindAuctionReturnMem_read biddingTime revealTime beneficiaryAddress)
      (by evm_ov)

def blindAuctionCtorLocals (biddingTime revealTime : Int)
    (beneficiaryAddress : AccountAddress) : Store :=
  Std.HashMap.ofList
    (List.zip (blindAuctionContract.ctor.params.map Param.name)
      [.int biddingTime, .int revealTime, .address beneficiaryAddress])

theorem blindAuctionBeneficiaryWord_toNat (beneficiaryAddress : AccountAddress) :
    (EVM.word beneficiaryAddress).toNat = beneficiaryAddress.val := by
  exact ulit_toNat' _ (lt_of_lt_of_le beneficiaryAddress.isLt
    (show AccountAddress.size ≤ UInt256.size from by decide))

theorem blindAuctionBeneficiary_ofNat (beneficiaryAddress : AccountAddress) :
    AccountAddress.ofNat (EVM.word beneficiaryAddress).toNat = beneficiaryAddress := by
  apply Fin.ext
  unfold AccountAddress.ofNat
  rw [blindAuctionBeneficiaryWord_toNat, Fin.val_ofNat]
  exact Nat.mod_eq_of_lt beneficiaryAddress.isLt

theorem blindAuctionBeneficiaryWord_canonical (beneficiaryAddress : AccountAddress) :
    (EVM.word beneficiaryAddress).toNat < EVM.addressModulus := by
  rw [blindAuctionBeneficiaryWord_toNat]
  simp [EVM.addressModulus, EVM.twoPow, AccountAddress.size]

theorem blindAuctionBiddingWord_toNat (biddingTime : Int)
    (h0 : 0 ≤ biddingTime)
    (hlt : biddingTime < Int.ofNat (EVM.twoPow 256)) :
    (EVM.word biddingTime.toNat).toNat = biddingTime.toNat :=
  constructorUInt256Word_toNat biddingTime h0 hlt

theorem blindAuctionRevealWord_toNat (revealTime : Int)
    (h0 : 0 ≤ revealTime)
    (hlt : revealTime < Int.ofNat (EVM.twoPow 256)) :
    (EVM.word revealTime.toNat).toNat = revealTime.toNat :=
  constructorUInt256Word_toNat revealTime h0 hlt

theorem blindAuctionCtorLocals_get_biddingTime (biddingTime revealTime : Int)
    (beneficiaryAddress : AccountAddress) :
    (blindAuctionCtorLocals biddingTime revealTime beneficiaryAddress).get? "biddingTime" =
      some (.int biddingTime) := by
  unfold blindAuctionCtorLocals
  simp only [blindAuctionContract, constructorDecl, List.map_cons, List.map_nil,
    List.zip_cons_cons, List.zip_nil_left]
  rw [show Std.HashMap.ofList
      [("biddingTime", Value.int biddingTime), ("revealTime", Value.int revealTime),
        ("beneficiaryAddress", Value.address beneficiaryAddress)] =
      ((((∅ : Store).insert "biddingTime" (Value.int biddingTime)).insert
        "revealTime" (Value.int revealTime)).insert
        "beneficiaryAddress" (Value.address beneficiaryAddress)) from rfl]
  rw [store_get_ne]
  · rw [store_get_ne]
    · rw [store_get_self]
    · decide
  · decide

theorem blindAuctionCtorLocals_get_revealTime (biddingTime revealTime : Int)
    (beneficiaryAddress : AccountAddress) :
    (blindAuctionCtorLocals biddingTime revealTime beneficiaryAddress).get? "revealTime" =
      some (.int revealTime) := by
  unfold blindAuctionCtorLocals
  simp only [blindAuctionContract, constructorDecl, List.map_cons, List.map_nil,
    List.zip_cons_cons, List.zip_nil_left]
  rw [show Std.HashMap.ofList
      [("biddingTime", Value.int biddingTime), ("revealTime", Value.int revealTime),
        ("beneficiaryAddress", Value.address beneficiaryAddress)] =
      ((((∅ : Store).insert "biddingTime" (Value.int biddingTime)).insert
        "revealTime" (Value.int revealTime)).insert
        "beneficiaryAddress" (Value.address beneficiaryAddress)) from rfl]
  rw [store_get_ne]
  · rw [store_get_self]
  · decide

theorem blindAuctionCtorLocals_get_beneficiaryAddress (biddingTime revealTime : Int)
    (beneficiaryAddress : AccountAddress) :
    (blindAuctionCtorLocals biddingTime revealTime beneficiaryAddress).get? "beneficiaryAddress" =
      some (.address beneficiaryAddress) := by
  unfold blindAuctionCtorLocals
  simp only [blindAuctionContract, constructorDecl, List.map_cons, List.map_nil,
    List.zip_cons_cons, List.zip_nil_left]
  rw [show Std.HashMap.ofList
      [("biddingTime", Value.int biddingTime), ("revealTime", Value.int revealTime),
        ("beneficiaryAddress", Value.address beneficiaryAddress)] =
      ((((∅ : Store).insert "biddingTime" (Value.int biddingTime)).insert
        "revealTime" (Value.int revealTime)).insert
        "beneficiaryAddress" (Value.address beneficiaryAddress)) from rfl]
  rw [store_get_self]

theorem blindAuctionCtorBiddingEndWord_eq (evm : EVM.State) (biddingTime : Int)
    (h0 : 0 ≤ biddingTime)
    (hlt : biddingTime < Int.ofNat (EVM.twoPow 256))
    (hno : ¬ UInt256.size ≤
      (UInt256.ofNat evm.executionEnv.header.timestamp).toNat +
        (EVM.word biddingTime.toNat).toNat) :
    EVM.word ((UInt256.ofNat evm.executionEnv.header.timestamp).toNat + biddingTime.toNat) =
      UInt256.ofNat evm.executionEnv.header.timestamp + EVM.word biddingTime.toNat :=
  constructorCheckedAddIntWordBaseFirst_eq
    (UInt256.ofNat evm.executionEnv.header.timestamp) biddingTime h0 hlt hno

theorem blindAuctionCtorCheckedAddWord_eq (base addend : UInt256)
    (hno : ¬ UInt256.size ≤ base.toNat + addend.toNat) :
    EVM.word (base.toNat + addend.toNat) = addend + base :=
  constructorCheckedAddWord_eq base addend hno

def blindAuctionCtorAfterBeneficiaryState
    (evm : EVM.State) (beneficiaryAddress : AccountAddress) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨0⟩
    (blindAuctionSetAddressWord
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩)
      (EVM.word beneficiaryAddress))

def blindAuctionCtorBiddingEndSolmWord (evm : EVM.State) (biddingTime : Int) : UInt256 :=
  EVM.word ((UInt256.ofNat evm.executionEnv.header.timestamp).toNat + biddingTime.toNat)

def blindAuctionCtorAfterBiddingEndState
    (evm : EVM.State) (biddingTime : Int) (beneficiaryAddress : AccountAddress) : EVM.State :=
  Solm.EVM.storageStore
    (blindAuctionCtorAfterBeneficiaryState evm beneficiaryAddress)
    evm.executionEnv.codeOwner ⟨1⟩
    (blindAuctionCtorBiddingEndSolmWord evm biddingTime)

theorem blindAuctionCtorAfterBiddingEndState_executionEnv
    (evm : EVM.State) (biddingTime : Int) (beneficiaryAddress : AccountAddress) :
    (blindAuctionCtorAfterBiddingEndState evm biddingTime beneficiaryAddress).executionEnv =
      evm.executionEnv := by
  simp [blindAuctionCtorAfterBiddingEndState, blindAuctionCtorAfterBeneficiaryState,
    storageStore_executionEnv]

def blindAuctionCtorRevealBaseWord
    (evm : EVM.State) (biddingTime : Int) (beneficiaryAddress : AccountAddress) : UInt256 :=
  let evm' := blindAuctionCtorAfterBiddingEndState evm biddingTime beneficiaryAddress
  Solm.EVM.storageLoad evm' evm'.executionEnv.codeOwner ⟨1⟩

def blindAuctionCtorRevealEndSolmWord
    (evm : EVM.State) (biddingTime revealTime : Int)
    (beneficiaryAddress : AccountAddress) : UInt256 :=
  EVM.word ((blindAuctionCtorRevealBaseWord evm biddingTime beneficiaryAddress).toNat +
    revealTime.toNat)

def blindAuctionCtorPostState
    (evm : EVM.State) (biddingTime revealTime : Int)
    (beneficiaryAddress : AccountAddress) : EVM.State :=
  Solm.EVM.storageStore
    (blindAuctionCtorAfterBiddingEndState evm biddingTime beneficiaryAddress)
    evm.executionEnv.codeOwner ⟨2⟩
    (blindAuctionCtorRevealEndSolmWord evm biddingTime revealTime beneficiaryAddress)

theorem blindAuctionCtorAssignBeneficiary (evm : EVM.State) (biddingTime revealTime : Int)
    (beneficiaryAddress : AccountAddress) :
    assignStorageRef? blindAuctionConfig
      { contract := blindAuctionContract,
        locals := blindAuctionCtorLocals biddingTime revealTime beneficiaryAddress }
      evm .storage beneficiaryRef (.address beneficiaryAddress) =
        .ok ({ contract := blindAuctionContract,
               locals := blindAuctionCtorLocals biddingTime revealTime beneficiaryAddress },
             blindAuctionCtorAfterBeneficiaryState evm beneficiaryAddress) := by
  apply assignStorageRef_storage_scalar_value (ty := addrSt)
      (hbase := by simp [blindAuctionCtorLocals, beneficiaryRef, blindAuctionContract,
        constructorDecl])
      (her := by
        simp [evalStorageRef, evalStorageRefSteps, beneficiaryRef, EvalResult.bind, pure, bind])
      (hty := by
        show storageTypeAt? blindAuctionContract.storage ({ base := "beneficiary", steps := [] } :
          EvaledStorageRef) = some addrSt
        decide)
      (hloc := blindAuctionConfig_storage_beneficiary)
      (hscalar := by trivial)
  simpa [blindAuctionCtorAfterBeneficiaryState, blindAuctionBeneficiary_ofNat] using
    blindAuctionStorageLocStore_address_offset0 evm ⟨0⟩ (EVM.word beneficiaryAddress)
      (blindAuctionBeneficiaryWord_canonical beneficiaryAddress)

theorem blindAuctionCtorBiddingEndExprReverts
    (evm : EVM.State) (biddingTime revealTime : Int) (beneficiaryAddress : AccountAddress)
    (h0 : 0 ≤ biddingTime)
    (hlt : biddingTime < Int.ofNat (EVM.twoPow 256))
    (hover : UInt256.size ≤
      (UInt256.ofNat evm.executionEnv.header.timestamp).toNat +
        (EVM.word biddingTime.toNat).toNat) :
    evalExpr? blindAuctionConfig
      { contract := blindAuctionContract,
        locals := blindAuctionCtorLocals biddingTime revealTime beneficiaryAddress }
      evm (u256 (.binary .add now (.var "biddingTime"))) = .revert := by
  have hword := blindAuctionBiddingWord_toNat biddingTime h0 hlt
  have hge :
      Int.ofNat ((UInt256.ofNat evm.executionEnv.header.timestamp).toNat + biddingTime.toNat)
        ≥ (2 : Int) ^ 256 := by
    rw [hword] at hover
    rw [UInt256.size] at hover
    exact Int.ofNat_le.mpr hover
  have hInt :
      Int.ofNat (UInt256.ofNat evm.executionEnv.header.timestamp).toNat + biddingTime =
        Int.ofNat ((UInt256.ofNat evm.executionEnv.header.timestamp).toNat + biddingTime.toNat) := by
    have hb : biddingTime = Int.ofNat biddingTime.toNat := by
      exact (Int.toNat_of_nonneg h0).symm
    rw [hb]
    exact (Int.natCast_add _ _).symm
  simp only [u256, evalExpr?, now, envValue, blindAuctionCtorLocals_get_biddingTime,
    EvalResult.ofOption, EvalResult.bind, bind, pure]
  simp only [evalBinaryOp?, uint256Int]
  rw [hInt]
  rw [if_pos (by
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    exact Or.inr hge)]

theorem blindAuctionCtorBiddingEndExprOK
    (evm : EVM.State) (biddingTime revealTime : Int) (beneficiaryAddress : AccountAddress)
    (h0 : 0 ≤ biddingTime)
    (hlt : biddingTime < Int.ofNat (EVM.twoPow 256))
    (hno : ¬ UInt256.size ≤
      (UInt256.ofNat evm.executionEnv.header.timestamp).toNat +
        (EVM.word biddingTime.toNat).toNat) :
    evalExpr? blindAuctionConfig
      { contract := blindAuctionContract,
        locals := blindAuctionCtorLocals biddingTime revealTime beneficiaryAddress }
      evm (u256 (.binary .add now (.var "biddingTime"))) =
        .ok (.int (Int.ofNat
          (blindAuctionCtorBiddingEndSolmWord evm biddingTime).toNat)) := by
  have hword := blindAuctionBiddingWord_toNat biddingTime h0 hlt
  have hsumlt :
      (UInt256.ofNat evm.executionEnv.header.timestamp).toNat + biddingTime.toNat <
        UInt256.size := by
    have hno' := hno
    rw [hword] at hno'
    exact Nat.lt_of_not_ge hno'
  have hInt :
      Int.ofNat (UInt256.ofNat evm.executionEnv.header.timestamp).toNat + biddingTime =
        Int.ofNat ((UInt256.ofNat evm.executionEnv.header.timestamp).toNat + biddingTime.toNat) := by
    have hb : biddingTime = Int.ofNat biddingTime.toNat := by
      exact (Int.toNat_of_nonneg h0).symm
    rw [hb]
    exact (Int.natCast_add _ _).symm
  have hsumWord :
      (EVM.word ((UInt256.ofNat evm.executionEnv.header.timestamp).toNat +
          biddingTime.toNat)).toNat =
        (UInt256.ofNat evm.executionEnv.header.timestamp).toNat + biddingTime.toNat := by
    exact ulit_toNat' _ hsumlt
  simp only [u256, evalExpr?, now, envValue, blindAuctionCtorLocals_get_biddingTime,
    EvalResult.ofOption, EvalResult.bind, bind, pure]
  simp only [evalBinaryOp?, uint256Int]
  rw [hInt]
  rw [if_neg]
  · rw [blindAuctionCtorBiddingEndSolmWord, hsumWord]
  · simp only [Bool.or_eq_true, decide_eq_true_eq, not_or]
    constructor
    · exact Int.not_lt_of_ge (Int.natCast_nonneg _)
    · intro hge
      have hpow : (2 : Int) ^ 256 = Int.ofNat UInt256.size := by
        norm_num [UInt256.size]
      rw [hpow] at hge
      exact Nat.not_le_of_gt hsumlt (Int.ofNat_le.mp hge)

theorem blindAuctionCtorAssignBiddingEnd (evm : EVM.State) (biddingTime revealTime : Int)
    (beneficiaryAddress : AccountAddress)
    (_h0 : 0 ≤ biddingTime)
    (_hlt : biddingTime < Int.ofNat (EVM.twoPow 256))
    (_hno : ¬ UInt256.size ≤
      (UInt256.ofNat evm.executionEnv.header.timestamp).toNat +
        (EVM.word biddingTime.toNat).toNat) :
    assignStorageRef? blindAuctionConfig
      { contract := blindAuctionContract,
        locals := blindAuctionCtorLocals biddingTime revealTime beneficiaryAddress }
      evm .storage biddingEndRef
      (.int (Int.ofNat (blindAuctionCtorBiddingEndSolmWord evm biddingTime).toNat)) =
        .ok ({ contract := blindAuctionContract,
               locals := blindAuctionCtorLocals biddingTime revealTime beneficiaryAddress },
             Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨1⟩
               (blindAuctionCtorBiddingEndSolmWord evm biddingTime)) := by
  apply assignStorageRef_storage_scalar (ty := uint256St)
      (hbase := by
        unfold blindAuctionCtorLocals
        simp only [blindAuctionContract, constructorDecl, List.map_cons, List.map_nil,
          List.zip_cons_cons, List.zip_nil_left]
        rw [show Std.HashMap.ofList
            [("biddingTime", Value.int biddingTime), ("revealTime", Value.int revealTime),
              ("beneficiaryAddress", Value.address beneficiaryAddress)] =
            ((((∅ : Store).insert "biddingTime" (Value.int biddingTime)).insert
              "revealTime" (Value.int revealTime)).insert
              "beneficiaryAddress" (Value.address beneficiaryAddress)) from rfl]
        rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
          store_get_ne _ _ (by decide)]
        simp)
      (her := by
        simp [evalStorageRef, evalStorageRefSteps, biddingEndRef, EvalResult.bind, pure, bind])
      (hty := by
        simp [storageTypeAt?, blindAuctionContract, storageDecls, uint256St])
      (hloc := blindAuctionConfig_storage_biddingEnd)
  exact blindAuctionStorageLocStore_uint256 evm ⟨1⟩
    (blindAuctionCtorBiddingEndSolmWord evm biddingTime)

theorem blindAuctionCtorRevealEndExprReverts
    (evm : EVM.State) (biddingTime revealTime : Int) (beneficiaryAddress : AccountAddress)
    (h0 : 0 ≤ revealTime)
    (hlt : revealTime < Int.ofNat (EVM.twoPow 256))
    (hover : UInt256.size ≤
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩).toNat +
        (EVM.word revealTime.toNat).toNat) :
    evalExpr? blindAuctionConfig
      { contract := blindAuctionContract,
        locals := blindAuctionCtorLocals biddingTime revealTime beneficiaryAddress }
      evm (u256 (.binary .add (.storage biddingEndRef) (.var "revealTime"))) = .revert := by
  have hword := blindAuctionRevealWord_toNat revealTime h0 hlt
  have hstorage :
      evalExpr? blindAuctionConfig
        { contract := blindAuctionContract,
          locals := blindAuctionCtorLocals biddingTime revealTime beneficiaryAddress }
        evm (.storage biddingEndRef) =
          .ok (.int (Int.ofNat
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩).toNat)) := by
    have her : evalStorageRef blindAuctionConfig
        { contract := blindAuctionContract,
          locals := blindAuctionCtorLocals biddingTime revealTime beneficiaryAddress }
        evm biddingEndRef = .ok { base := "biddingEnd", steps := [] } := by
      simp [evalStorageRef, evalStorageRefSteps, biddingEndRef, EvalResult.bind, pure, bind]
    have hty : storageTypeAt? blindAuctionContract.storage
        ({ base := "biddingEnd", steps := [] } : EvaledStorageRef) =
        some uint256St := by
      decide
    rw [evalExpr_storage_scalar (t := .int uint256Int)
      (hbase := by simp [blindAuctionCtorLocals, biddingEndRef, blindAuctionContract,
        constructorDecl])
      (her := her) (hty := hty) (hloc := blindAuctionConfig_storage_biddingEnd)]
    rw [blindAuctionStorageLocLoad_uint256]
  have hge :
      Int.ofNat ((Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩).toNat +
          revealTime.toNat) ≥ (2 : Int) ^ 256 := by
    rw [hword] at hover
    have hpow : (2 : Int) ^ 256 = Int.ofNat UInt256.size := by
      norm_num [UInt256.size]
    rw [hpow]
    exact Int.ofNat_le.mpr hover
  have hInt :
      Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩).toNat + revealTime =
        Int.ofNat ((Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩).toNat +
          revealTime.toNat) := by
    have hb : revealTime = Int.ofNat revealTime.toNat := by
      exact (Int.toNat_of_nonneg h0).symm
    rw [hb]
    exact (Int.natCast_add _ _).symm
  simp only [u256, evalExpr?, hstorage, blindAuctionCtorLocals_get_revealTime,
    EvalResult.ofOption, EvalResult.bind, bind, pure]
  simp only [evalBinaryOp?, uint256Int]
  rw [hInt]
  rw [if_pos (by
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    exact Or.inr hge)]

theorem blindAuctionCtorRevealEndExprOK
    (evm : EVM.State) (biddingTime revealTime : Int) (beneficiaryAddress : AccountAddress)
    (h0 : 0 ≤ revealTime)
    (hlt : revealTime < Int.ofNat (EVM.twoPow 256))
    (hno : ¬ UInt256.size ≤
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩).toNat +
        (EVM.word revealTime.toNat).toNat) :
    evalExpr? blindAuctionConfig
      { contract := blindAuctionContract,
        locals := blindAuctionCtorLocals biddingTime revealTime beneficiaryAddress }
      evm (u256 (.binary .add (.storage biddingEndRef) (.var "revealTime"))) =
        .ok (.int (Int.ofNat
          (EVM.word ((Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩).toNat +
            revealTime.toNat)).toNat)) := by
  have hword := blindAuctionRevealWord_toNat revealTime h0 hlt
  have hstorage :
      evalExpr? blindAuctionConfig
        { contract := blindAuctionContract,
          locals := blindAuctionCtorLocals biddingTime revealTime beneficiaryAddress }
        evm (.storage biddingEndRef) =
          .ok (.int (Int.ofNat
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩).toNat)) := by
    have her : evalStorageRef blindAuctionConfig
        { contract := blindAuctionContract,
          locals := blindAuctionCtorLocals biddingTime revealTime beneficiaryAddress }
        evm biddingEndRef = .ok { base := "biddingEnd", steps := [] } := by
      simp [evalStorageRef, evalStorageRefSteps, biddingEndRef, EvalResult.bind, pure, bind]
    have hty : storageTypeAt? blindAuctionContract.storage
        ({ base := "biddingEnd", steps := [] } : EvaledStorageRef) =
        some uint256St := by
      decide
    rw [evalExpr_storage_scalar (t := .int uint256Int)
      (hbase := by simp [blindAuctionCtorLocals, biddingEndRef, blindAuctionContract,
        constructorDecl])
      (her := her) (hty := hty) (hloc := blindAuctionConfig_storage_biddingEnd)]
    rw [blindAuctionStorageLocLoad_uint256]
  have hsumlt :
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩).toNat + revealTime.toNat <
        UInt256.size := by
    have hno' := hno
    rw [hword] at hno'
    exact Nat.lt_of_not_ge hno'
  have hInt :
      Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩).toNat + revealTime =
        Int.ofNat ((Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩).toNat +
          revealTime.toNat) := by
    have hb : revealTime = Int.ofNat revealTime.toNat := by
      exact (Int.toNat_of_nonneg h0).symm
    rw [hb]
    exact (Int.natCast_add _ _).symm
  have hsumWord :
      (EVM.word ((Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩).toNat +
          revealTime.toNat)).toNat =
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩).toNat +
          revealTime.toNat := by
    exact ulit_toNat' _ hsumlt
  simp only [u256, evalExpr?, hstorage, blindAuctionCtorLocals_get_revealTime,
    EvalResult.ofOption, EvalResult.bind, bind, pure]
  simp only [evalBinaryOp?, uint256Int]
  rw [hInt]
  rw [if_neg]
  · rw [hsumWord]
  · simp only [Bool.or_eq_true, decide_eq_true_eq, not_or]
    constructor
    · exact Int.not_lt_of_ge (Int.natCast_nonneg _)
    · intro hge
      have hpow : (2 : Int) ^ 256 = Int.ofNat UInt256.size := by
        norm_num [UInt256.size]
      rw [hpow] at hge
      exact Nat.not_le_of_gt hsumlt (Int.ofNat_le.mp hge)

theorem blindAuctionCtorAssignRevealEnd (evm : EVM.State) (biddingTime revealTime : Int)
    (beneficiaryAddress : AccountAddress) (val : UInt256) :
    assignStorageRef? blindAuctionConfig
      { contract := blindAuctionContract,
        locals := blindAuctionCtorLocals biddingTime revealTime beneficiaryAddress }
      evm .storage revealEndRef
      (.int (Int.ofNat val.toNat)) =
        .ok ({ contract := blindAuctionContract,
               locals := blindAuctionCtorLocals biddingTime revealTime beneficiaryAddress },
             Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨2⟩ val) := by
  apply assignStorageRef_storage_scalar (ty := uint256St)
      (hbase := by
        unfold blindAuctionCtorLocals
        simp only [blindAuctionContract, constructorDecl, List.map_cons, List.map_nil,
          List.zip_cons_cons, List.zip_nil_left]
        rw [show Std.HashMap.ofList
            [("biddingTime", Value.int biddingTime), ("revealTime", Value.int revealTime),
              ("beneficiaryAddress", Value.address beneficiaryAddress)] =
            ((((∅ : Store).insert "biddingTime" (Value.int biddingTime)).insert
              "revealTime" (Value.int revealTime)).insert
              "beneficiaryAddress" (Value.address beneficiaryAddress)) from rfl]
        rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
          store_get_ne _ _ (by decide)]
        simp)
      (her := by
        simp [evalStorageRef, evalStorageRefSteps, revealEndRef, EvalResult.bind, pure, bind])
      (hty := by
        simp [storageTypeAt?, blindAuctionContract, storageDecls, uint256St])
      (hloc := blindAuctionConfig_storage_revealEnd)
  exact blindAuctionStorageLocStore_uint256 evm ⟨2⟩ val

theorem blindAuctionSolmCtorExecReverts_nonpayable
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader}
    {blocks : ProcessedBlocks}
    {σ : AccountMap}
    {σ₀ : AccountMap}
    {g : UInt256}
    {A : Substate}
    {I : ExecutionEnv}
    (biddingTime revealTime : Int)
    (beneficiaryAddress : AccountAddress)
    (hwv : I.weiValue ≠ ⟨0⟩) :
    solmCtorExec blindAuctionConfig blindAuctionContract
      [.int biddingTime, .int revealTime, .address beneficiaryAddress]
      createdAccounts genesisBlockHeader blocks σ σ₀ g A I .reverted := by
  refine solmCtorExec.intro
    (evmState := initState createdAccounts genesisBlockHeader blocks σ σ₀ (Sat256.ofUInt256 g) A I)
    (argsStore := blindAuctionCtorLocals biddingTime revealTime beneficiaryAddress)
    ?_ rfl ?_ ?_
  · rfl
  · simp [blindAuctionCtorLocals, blindAuctionContract, constructorDecl]
  · exact bodyReverts_nonPayable (cfg := blindAuctionConfig) (contract := blindAuctionContract)
      (locals := blindAuctionCtorLocals biddingTime revealTime beneficiaryAddress)
      hwv

theorem blindAuctionSolmCtorExecReverts_biddingOverflow
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader}
    {blocks : ProcessedBlocks}
    {σ : AccountMap}
    {σ₀ : AccountMap}
    {g : UInt256}
    {A : Substate}
    {I : ExecutionEnv}
    (biddingTime revealTime : Int)
    (beneficiaryAddress : AccountAddress)
    (h0Bid : 0 ≤ biddingTime)
    (hltBid : biddingTime < Int.ofNat (EVM.twoPow 256))
    (hwv : I.weiValue = ⟨0⟩)
    (hoverBid : UInt256.size ≤
      (UInt256.ofNat I.header.timestamp).toNat + (EVM.word biddingTime.toNat).toNat) :
    solmCtorExec blindAuctionConfig blindAuctionContract
      [.int biddingTime, .int revealTime, .address beneficiaryAddress]
      createdAccounts genesisBlockHeader blocks σ σ₀ g A I .reverted := by
  refine solmCtorExec.intro
    (evmState := initState createdAccounts genesisBlockHeader blocks σ σ₀ (Sat256.ofUInt256 g) A I)
    (argsStore := blindAuctionCtorLocals biddingTime revealTime beneficiaryAddress)
    ?_ rfl ?_ ?_
  · rfl
  · simp [blindAuctionCtorLocals, blindAuctionContract, constructorDecl]
  · refine ExecFuncBody.execBlockRevert ?_
    let frame : Frame :=
      { contract := blindAuctionContract,
        locals := blindAuctionCtorLocals biddingTime revealTime beneficiaryAddress }
    let evm0 := initState createdAccounts genesisBlockHeader blocks σ σ₀ (Sat256.ofUInt256 g) A I
    let evm1 := blindAuctionCtorAfterBeneficiaryState evm0 beneficiaryAddress
    refine ExecBlock.consNormal (solm' := frame) (evm' := evm0)
      (ExecStmt.requireTrue (evalCallvalueEq_true (cfg := blindAuctionConfig)
        (solm := frame)
        (evm := evm0)
        (by simpa [evm0, initState] using hwv))) ?_
    refine ExecBlock.consNormal (solm' := frame) (evm' := evm1) ?_ ?_
    · exact ExecStmt.assign (value := .address beneficiaryAddress)
        (by
          show evalExpr? blindAuctionConfig frame evm0 (.var "beneficiaryAddress") =
            .ok (.address beneficiaryAddress)
          unfold frame
          simp only [evalExpr?, blindAuctionCtorLocals_get_beneficiaryAddress,
            EvalResult.ofOption])
        (by
          unfold evm1 evm0 frame
          exact blindAuctionCtorAssignBeneficiary
            (initState createdAccounts genesisBlockHeader blocks σ σ₀ (Sat256.ofUInt256 g) A I)
            biddingTime revealTime beneficiaryAddress)
    · exact ExecBlock.consRevert
        (ExecStmt.assignExprRevert
          (blindAuctionCtorBiddingEndExprReverts
            evm1 biddingTime revealTime beneficiaryAddress h0Bid hltBid (by
              unfold evm1 evm0
              simpa [blindAuctionCtorAfterBeneficiaryState, storageStore_executionEnv, initState]
                using hoverBid)))

theorem blindAuctionSolmCtorExecReverts_revealOverflow
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader}
    {blocks : ProcessedBlocks}
    {σ : AccountMap}
    {σ₀ : AccountMap}
    {g : UInt256}
    {A : Substate}
    {I : ExecutionEnv}
    (biddingTime revealTime : Int)
    (beneficiaryAddress : AccountAddress)
    (h0Bid : 0 ≤ biddingTime)
    (hltBid : biddingTime < Int.ofNat (EVM.twoPow 256))
    (h0Reveal : 0 ≤ revealTime)
    (hltReveal : revealTime < Int.ofNat (EVM.twoPow 256))
    (hwv : I.weiValue = ⟨0⟩)
    (hnoBid : ¬ UInt256.size ≤
      (UInt256.ofNat I.header.timestamp).toNat + (EVM.word biddingTime.toNat).toNat)
    (hoverReveal : UInt256.size ≤
      (blindAuctionCtorRevealBaseWord
        (initState createdAccounts genesisBlockHeader blocks σ σ₀ (Sat256.ofUInt256 g) A I)
        biddingTime beneficiaryAddress).toNat + (EVM.word revealTime.toNat).toNat) :
    solmCtorExec blindAuctionConfig blindAuctionContract
      [.int biddingTime, .int revealTime, .address beneficiaryAddress]
      createdAccounts genesisBlockHeader blocks σ σ₀ g A I .reverted := by
  refine solmCtorExec.intro
    (evmState := initState createdAccounts genesisBlockHeader blocks σ σ₀ (Sat256.ofUInt256 g) A I)
    (argsStore := blindAuctionCtorLocals biddingTime revealTime beneficiaryAddress)
    ?_ rfl ?_ ?_
  · rfl
  · simp [blindAuctionCtorLocals, blindAuctionContract, constructorDecl]
  · refine ExecFuncBody.execBlockRevert ?_
    let frame : Frame :=
      { contract := blindAuctionContract,
        locals := blindAuctionCtorLocals biddingTime revealTime beneficiaryAddress }
    let evm0 := initState createdAccounts genesisBlockHeader blocks σ σ₀ (Sat256.ofUInt256 g) A I
    let evm1 := blindAuctionCtorAfterBeneficiaryState evm0 beneficiaryAddress
    let evm2 := blindAuctionCtorAfterBiddingEndState evm0 biddingTime beneficiaryAddress
    let biddingEndWord := blindAuctionCtorBiddingEndSolmWord evm0 biddingTime
    refine ExecBlock.consNormal (solm' := frame) (evm' := evm0)
      (ExecStmt.requireTrue (evalCallvalueEq_true (cfg := blindAuctionConfig)
        (solm := frame)
        (evm := evm0)
        (by simpa [evm0, initState] using hwv))) ?_
    refine ExecBlock.consNormal (solm' := frame) (evm' := evm1) ?_ ?_
    · exact ExecStmt.assign (value := .address beneficiaryAddress)
        (by
          show evalExpr? blindAuctionConfig frame evm0 (.var "beneficiaryAddress") =
            .ok (.address beneficiaryAddress)
          unfold frame
          simp only [evalExpr?, blindAuctionCtorLocals_get_beneficiaryAddress,
            EvalResult.ofOption])
        (by
          unfold evm1 evm0 frame
          exact blindAuctionCtorAssignBeneficiary
            (initState createdAccounts genesisBlockHeader blocks σ σ₀ (Sat256.ofUInt256 g) A I)
            biddingTime revealTime beneficiaryAddress)
    · refine ExecBlock.consNormal (solm' := frame) (evm' := evm2) ?_ ?_
      · exact ExecStmt.assign (value := .int (Int.ofNat biddingEndWord.toNat))
          (by
            unfold biddingEndWord evm1 evm0 frame
            simpa [blindAuctionCtorBiddingEndSolmWord, blindAuctionCtorAfterBeneficiaryState,
              storageStore_executionEnv, initState]
              using blindAuctionCtorBiddingEndExprOK
                (blindAuctionCtorAfterBeneficiaryState
                  (initState createdAccounts genesisBlockHeader blocks σ σ₀
                    (Sat256.ofUInt256 g) A I)
                  beneficiaryAddress)
                biddingTime revealTime beneficiaryAddress h0Bid hltBid (by
                  simpa [blindAuctionCtorAfterBeneficiaryState, storageStore_executionEnv,
                    initState] using hnoBid))
          (by
            unfold biddingEndWord evm2 evm1 evm0 frame
            simpa [blindAuctionCtorAfterBiddingEndState, blindAuctionCtorBiddingEndSolmWord,
              blindAuctionCtorAfterBeneficiaryState, storageStore_executionEnv, initState]
              using blindAuctionCtorAssignBiddingEnd
                (blindAuctionCtorAfterBeneficiaryState
                  (initState createdAccounts genesisBlockHeader blocks σ σ₀
                    (Sat256.ofUInt256 g) A I)
                  beneficiaryAddress)
                biddingTime revealTime beneficiaryAddress h0Bid hltBid (by
                  simpa [blindAuctionCtorAfterBeneficiaryState, storageStore_executionEnv,
                    initState] using hnoBid))
      · exact ExecBlock.consRevert
          (ExecStmt.assignExprRevert
            (blindAuctionCtorRevealEndExprReverts
              evm2 biddingTime revealTime beneficiaryAddress h0Reveal hltReveal (by
                simpa [evm2, evm0, blindAuctionCtorRevealBaseWord,
                  blindAuctionCtorAfterBiddingEndState_executionEnv, initState]
                  using hoverReveal)))

theorem blindAuctionSolmCtorExecSuccess
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader}
    {blocks : ProcessedBlocks}
    {σ : AccountMap}
    {σ₀ : AccountMap}
    {g : UInt256}
    {A : Substate}
    {I : ExecutionEnv}
    (biddingTime revealTime : Int)
    (beneficiaryAddress : AccountAddress)
    (h0Bid : 0 ≤ biddingTime)
    (hltBid : biddingTime < Int.ofNat (EVM.twoPow 256))
    (h0Reveal : 0 ≤ revealTime)
    (hltReveal : revealTime < Int.ofNat (EVM.twoPow 256))
    (hwv : I.weiValue = ⟨0⟩)
    (hnoBid : ¬ UInt256.size ≤
      (UInt256.ofNat I.header.timestamp).toNat + (EVM.word biddingTime.toNat).toNat)
    (hnoReveal : ¬ UInt256.size ≤
      (blindAuctionCtorRevealBaseWord
        (initState createdAccounts genesisBlockHeader blocks σ σ₀ (Sat256.ofUInt256 g) A I)
        biddingTime beneficiaryAddress).toNat + (EVM.word revealTime.toNat).toNat) :
    solmCtorExec blindAuctionConfig blindAuctionContract
      [.int biddingTime, .int revealTime, .address beneficiaryAddress]
      createdAccounts genesisBlockHeader blocks σ σ₀ g A I
      (.returned
        { contract := blindAuctionContract,
          locals := blindAuctionCtorLocals biddingTime revealTime beneficiaryAddress }
        (blindAuctionCtorPostState
          (initState createdAccounts genesisBlockHeader blocks σ σ₀ (Sat256.ofUInt256 g) A I)
          biddingTime revealTime beneficiaryAddress)
        none) := by
  refine solmCtorExec.intro
    (evmState := initState createdAccounts genesisBlockHeader blocks σ σ₀ (Sat256.ofUInt256 g) A I)
    (argsStore := blindAuctionCtorLocals biddingTime revealTime beneficiaryAddress)
    ?_ rfl ?_ ?_
  · rfl
  · simp [blindAuctionCtorLocals, blindAuctionContract, constructorDecl]
  · refine ExecFuncBody.execBlockOK ?_
    let frame : Frame :=
      { contract := blindAuctionContract,
        locals := blindAuctionCtorLocals biddingTime revealTime beneficiaryAddress }
    let evm0 := initState createdAccounts genesisBlockHeader blocks σ σ₀ (Sat256.ofUInt256 g) A I
    let evm1 := blindAuctionCtorAfterBeneficiaryState evm0 beneficiaryAddress
    let evm2 := blindAuctionCtorAfterBiddingEndState evm0 biddingTime beneficiaryAddress
    let evm3 := blindAuctionCtorPostState evm0 biddingTime revealTime beneficiaryAddress
    let biddingEndWord := blindAuctionCtorBiddingEndSolmWord evm0 biddingTime
    let revealEndWord := blindAuctionCtorRevealEndSolmWord evm0 biddingTime revealTime beneficiaryAddress
    refine ExecBlock.consNormal (solm' := frame) (evm' := evm0)
      (ExecStmt.requireTrue (evalCallvalueEq_true (cfg := blindAuctionConfig)
        (solm := frame)
        (evm := evm0)
        (by simpa [evm0, initState] using hwv))) ?_
    refine ExecBlock.consNormal (solm' := frame) (evm' := evm1) ?_ ?_
    · exact ExecStmt.assign (value := .address beneficiaryAddress)
        (by
          show evalExpr? blindAuctionConfig frame evm0 (.var "beneficiaryAddress") =
            .ok (.address beneficiaryAddress)
          unfold frame
          simp only [evalExpr?, blindAuctionCtorLocals_get_beneficiaryAddress,
            EvalResult.ofOption])
        (by
          unfold evm1 evm0 frame
          exact blindAuctionCtorAssignBeneficiary
            (initState createdAccounts genesisBlockHeader blocks σ σ₀ (Sat256.ofUInt256 g) A I)
            biddingTime revealTime beneficiaryAddress)
    · refine ExecBlock.consNormal (solm' := frame) (evm' := evm2) ?_ ?_
      · exact ExecStmt.assign (value := .int (Int.ofNat biddingEndWord.toNat))
          (by
            unfold biddingEndWord evm1 evm0 frame
            simpa [blindAuctionCtorBiddingEndSolmWord, blindAuctionCtorAfterBeneficiaryState,
              storageStore_executionEnv, initState]
              using blindAuctionCtorBiddingEndExprOK
                (blindAuctionCtorAfterBeneficiaryState
                  (initState createdAccounts genesisBlockHeader blocks σ σ₀
                    (Sat256.ofUInt256 g) A I)
                  beneficiaryAddress)
                biddingTime revealTime beneficiaryAddress h0Bid hltBid (by
                  simpa [blindAuctionCtorAfterBeneficiaryState, storageStore_executionEnv,
                    initState] using hnoBid))
          (by
            unfold biddingEndWord evm2 evm1 evm0 frame
            simpa [blindAuctionCtorAfterBiddingEndState, blindAuctionCtorBiddingEndSolmWord,
              blindAuctionCtorAfterBeneficiaryState, storageStore_executionEnv, initState]
              using blindAuctionCtorAssignBiddingEnd
                (blindAuctionCtorAfterBeneficiaryState
                  (initState createdAccounts genesisBlockHeader blocks σ σ₀
                    (Sat256.ofUInt256 g) A I)
                  beneficiaryAddress)
                biddingTime revealTime beneficiaryAddress h0Bid hltBid (by
                  simpa [blindAuctionCtorAfterBeneficiaryState, storageStore_executionEnv,
                    initState] using hnoBid))
      · refine ExecBlock.consNormal ?_ ExecBlock.nil
        exact ExecStmt.assign (value := .int (Int.ofNat revealEndWord.toNat))
          (by
            unfold revealEndWord evm2 evm0 frame blindAuctionCtorRevealEndSolmWord
            simpa [blindAuctionCtorRevealBaseWord, storageStore_executionEnv]
              using blindAuctionCtorRevealEndExprOK
                (blindAuctionCtorAfterBiddingEndState
                  (initState createdAccounts genesisBlockHeader blocks σ σ₀
                    (Sat256.ofUInt256 g) A I)
                  biddingTime beneficiaryAddress)
                biddingTime revealTime beneficiaryAddress h0Reveal hltReveal (by
                  simpa [blindAuctionCtorRevealBaseWord,
                    blindAuctionCtorAfterBiddingEndState_executionEnv, initState]
                    using hnoReveal))
          (by
            unfold revealEndWord evm2 evm0 frame blindAuctionCtorPostState
            simpa [blindAuctionCtorRevealEndSolmWord, blindAuctionCtorRevealBaseWord,
              blindAuctionCtorAfterBiddingEndState_executionEnv, storageStore_executionEnv]
              using blindAuctionCtorAssignRevealEnd
                (blindAuctionCtorAfterBiddingEndState
                  (initState createdAccounts genesisBlockHeader blocks σ σ₀
                    (Sat256.ofUInt256 g) A I)
                  biddingTime beneficiaryAddress)
                biddingTime revealTime beneficiaryAddress
                (blindAuctionCtorRevealEndSolmWord
                  (initState createdAccounts genesisBlockHeader blocks σ σ₀
                    (Sat256.ofUInt256 g) A I)
                  biddingTime revealTime beneficiaryAddress))

/-- The Solm constructor's post-bidding `biddingEnd` load matches the EVM initcode's slot-1 load. -/
theorem blindAuctionCtorRevealBaseWord_equiv
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader}
    {blocks : ProcessedBlocks}
    {σ_evm σ_solm σ₀ : AccountMap}
    {g : UInt256}
    {A : Substate}
    {I : ExecutionEnv}
    (biddingTime : Int)
    (beneficiaryAddress : AccountAddress)
    (h0Bid : 0 ≤ biddingTime)
    (hltBid : biddingTime < Int.ofNat (EVM.twoPow 256))
    (hnoBid : ¬ UInt256.size ≤
      (UInt256.ofNat I.header.timestamp).toNat + (EVM.word biddingTime.toNat).toNat)
    (hσ : accountMapEquiv σ_evm σ_solm) :
    blindAuctionCtorBiddingEndWord σ_evm I (EVM.word biddingTime.toNat) beneficiaryAddress =
      blindAuctionCtorRevealBaseWord
        (initState createdAccounts genesisBlockHeader blocks σ_solm σ₀
          (Sat256.ofUInt256 g) A I)
        biddingTime beneficiaryAddress := by
  let oldSlotEvm : UInt256 :=
    (σ_evm.find? I.codeOwner |>.option ⟨0⟩ (fun ac => ac.storage.findD ⟨0⟩ ⟨0⟩))
  let oldSlotSolm : UInt256 :=
    (σ_solm.find? I.codeOwner |>.option ⟨0⟩ (fun ac => ac.storage.findD ⟨0⟩ ⟨0⟩))
  let beneficiaryStoreWordEvm : UInt256 :=
    blindAuctionSetAddressWord oldSlotEvm (EVM.word beneficiaryAddress)
  let beneficiaryStoreWordSolm : UInt256 :=
    blindAuctionSetAddressWord oldSlotSolm (EVM.word beneficiaryAddress)
  let biddingEndWordEvm : UInt256 :=
    UInt256.ofNat I.header.timestamp + EVM.word biddingTime.toNat
  let biddingEndWordSolm : UInt256 :=
    blindAuctionCtorBiddingEndSolmWord
      (initState createdAccounts genesisBlockHeader blocks σ_solm σ₀
        (Sat256.ofUInt256 g) A I)
      biddingTime
  have hOldSlot : oldSlotEvm = oldSlotSolm := by
    exact accountMapEquiv_storage_findD hσ I.codeOwner ⟨0⟩ ⟨0⟩
  have hBeneficiaryStoreWord : beneficiaryStoreWordEvm = beneficiaryStoreWordSolm := by
    simp [beneficiaryStoreWordEvm, beneficiaryStoreWordSolm, oldSlotEvm, oldSlotSolm, hOldSlot]
  have hBiddingEndWord : biddingEndWordEvm = biddingEndWordSolm := by
    simpa [biddingEndWordEvm, biddingEndWordSolm, blindAuctionCtorBiddingEndSolmWord,
      initState] using (blindAuctionCtorBiddingEndWord_eq
      (initState createdAccounts genesisBlockHeader blocks σ_solm σ₀
        (Sat256.ofUInt256 g) A I)
      biddingTime h0Bid hltBid (by simpa [initState] using hnoBid)).symm
  have hmap0 :
      accountMapEquiv
        (sstoreAccountMap I.codeOwner σ_evm ⟨0⟩ beneficiaryStoreWordEvm)
        (sstoreAccountMap I.codeOwner σ_solm ⟨0⟩ beneficiaryStoreWordSolm) := by
    rw [← hBeneficiaryStoreWord]
    exact accountMapEquiv_sstoreAccountMap I.codeOwner ⟨0⟩ beneficiaryStoreWordEvm hσ
  have hmap1 :
      accountMapEquiv
        (sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner σ_evm ⟨0⟩ beneficiaryStoreWordEvm)
          ⟨1⟩ biddingEndWordEvm)
        (sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner σ_solm ⟨0⟩ beneficiaryStoreWordSolm)
          ⟨1⟩ biddingEndWordSolm) := by
    rw [← hBiddingEndWord]
    exact accountMapEquiv_sstoreAccountMap I.codeOwner ⟨1⟩ biddingEndWordEvm hmap0
  have hslot := accountMapEquiv_storage_findD hmap1 I.codeOwner ⟨1⟩ ⟨0⟩
  simpa [blindAuctionCtorBiddingEndWord, blindAuctionCtorAfterBiddingEndMap,
    blindAuctionCtorBeneficiaryStoreWord, blindAuctionCtorOldBeneficiarySlot,
    blindAuctionCtorRevealBaseWord, blindAuctionCtorAfterBiddingEndState,
    blindAuctionCtorAfterBeneficiaryState, blindAuctionCtorBiddingEndSolmWord,
    oldSlotEvm, oldSlotSolm, beneficiaryStoreWordEvm, beneficiaryStoreWordSolm,
    biddingEndWordEvm, biddingEndWordSolm, hOldSlot, hBiddingEndWord, storageStore_accountMap,
    storageStore_executionEnv, initState, Solm.EVM.storageLoad, State.lookupAccount,
    Account.lookupStorage] using hslot

/-- The creation/initcode bytecode refines the BlindAuction Solm constructor specification. -/
theorem blindAuctionConstructorCorrect :
    constructorEquivalence blindAuctionConfig blindAuctionInitcode blindAuctionContract
      blindAuctionBytecode := by
  refine constructorEquivalence.intro ?_
  intro createdAccounts genesisBlockHeader blocks σ_evm σ_solm σ₀ g A I
      args deployedInitcode hdeploy hcode hcalldata hperm hσ
  rcases blindAuctionDeployment_shape hdeploy with
    ⟨biddingTime, revealTime, beneficiaryAddress, hargs, h0Bid, hltBid, h0Reveal, hltReveal,
      hdeployed⟩
  subst args
  let bidWord : UInt256 := EVM.word biddingTime.toNat
  let revealWord : UInt256 := EVM.word revealTime.toNat
  have hcodeCtor : I.code = blindAuctionCtorCode bidWord revealWord beneficiaryAddress := by
    rw [hcode, hdeployed]
    unfold blindAuctionCtorCode blindAuctionCtorArgTail bidWord revealWord
    simp [ByteArray.append_assoc]
  by_cases hwv : I.weiValue = ⟨0⟩
  · by_cases hoverBid : UInt256.size ≤
        (UInt256.ofNat I.header.timestamp).toNat + bidWord.toNat
    · have hrd := blindAuctionInitcodeBiddingOverflowRevert
        (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
        (blocks := blocks) (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I)
        (g := Sat256.ofUInt256 g) bidWord revealWord beneficiaryAddress hcodeCtor
        hperm hwv hoverBid
      rcases hrd.xiResult hcodeCtor with hOOG | ⟨g', o, hrev⟩
      · exact constructorEquivalenceFor.outOfGas (by simpa [Sat256.ofUInt256] using hOOG)
      · refine constructorEquivalenceFor.execution (by simpa [Sat256.ofUInt256] using hrev)
          (blindAuctionSolmCtorExecReverts_biddingOverflow
            (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
            (blocks := blocks) (σ := σ_solm) (σ₀ := σ₀) (g := g) (A := A) (I := I)
            biddingTime revealTime beneficiaryAddress h0Bid hltBid hwv (by
              simpa [bidWord] using hoverBid)) ?_
        exact ctorResultEquiv.revert rfl rfl
    · have hRevealBase :=
        blindAuctionCtorRevealBaseWord_equiv
          (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
          (blocks := blocks) (σ_evm := σ_evm) (σ_solm := σ_solm) (σ₀ := σ₀)
          (g := g) (A := A) (I := I)
          biddingTime beneficiaryAddress h0Bid hltBid (by simpa [bidWord] using hoverBid) hσ
      by_cases hoverReveal : UInt256.size ≤
          (blindAuctionCtorBiddingEndWord σ_evm I bidWord beneficiaryAddress).toNat
            + revealWord.toNat
      · have hrd := blindAuctionInitcodeRevealOverflowRevert
          (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
          (blocks := blocks) (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I)
          (g := Sat256.ofUInt256 g) bidWord revealWord beneficiaryAddress hcodeCtor
          hperm hwv (by simpa [bidWord] using hoverBid) hoverReveal
        rcases hrd.xiResult hcodeCtor with hOOG | ⟨g', o, hrev⟩
        · exact constructorEquivalenceFor.outOfGas (by simpa [Sat256.ofUInt256] using hOOG)
        · refine constructorEquivalenceFor.execution (by simpa [Sat256.ofUInt256] using hrev)
            (blindAuctionSolmCtorExecReverts_revealOverflow
              (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
              (blocks := blocks) (σ := σ_solm) (σ₀ := σ₀) (g := g) (A := A) (I := I)
              biddingTime revealTime beneficiaryAddress h0Bid hltBid h0Reveal hltReveal hwv
              (by simpa [bidWord] using hoverBid)
              (by
                rw [← hRevealBase]
                simpa [revealWord] using hoverReveal)) ?_
          exact ctorResultEquiv.revert rfl rfl
      · have hrd := blindAuctionInitcodeSuccess
          (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
          (blocks := blocks) (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I)
          (g := Sat256.ofUInt256 g) bidWord revealWord beneficiaryAddress hcodeCtor
          hperm hwv (by simpa [bidWord] using hoverBid) hoverReveal
        rcases hrd with hOOG | ⟨s, hX, hacc⟩
        · exact constructorEquivalenceFor.outOfGas
            (Xi_error_of_X (g := g) (by
              rw [← hcodeCtor] at hOOG
              simpa [Sat256.ofUInt256] using hOOG))
        · have hsuccess := Xi_success_of_X (g := g) (by
            rw [← hcodeCtor] at hX
            simpa [Sat256.ofUInt256] using hX)
          let oldSlotEvm : UInt256 :=
            (σ_evm.find? I.codeOwner |>.option ⟨0⟩ (fun ac => ac.storage.findD ⟨0⟩ ⟨0⟩))
          let oldSlotSolm : UInt256 :=
            (σ_solm.find? I.codeOwner |>.option ⟨0⟩ (fun ac => ac.storage.findD ⟨0⟩ ⟨0⟩))
          let beneficiaryStoreWordEvm : UInt256 :=
            blindAuctionSetAddressWord oldSlotEvm (EVM.word beneficiaryAddress)
          let beneficiaryStoreWordSolm : UInt256 :=
            blindAuctionSetAddressWord oldSlotSolm (EVM.word beneficiaryAddress)
          let biddingEndWordEvm : UInt256 :=
            UInt256.ofNat I.header.timestamp + bidWord
          let biddingEndWordSolm : UInt256 :=
            blindAuctionCtorBiddingEndSolmWord
              (initState createdAccounts genesisBlockHeader blocks σ_solm σ₀
                (Sat256.ofUInt256 g) A I)
              biddingTime
          let revealEndWordEvm : UInt256 :=
            revealWord + blindAuctionCtorBiddingEndWord σ_evm I bidWord beneficiaryAddress
          let revealEndWordSolm : UInt256 :=
            blindAuctionCtorRevealEndSolmWord
              (initState createdAccounts genesisBlockHeader blocks σ_solm σ₀
                (Sat256.ofUInt256 g) A I)
              biddingTime revealTime beneficiaryAddress
          have hcA : s.createdAccounts = createdAccounts := congrArg Prod.fst hacc
          have hσFinal : s.accountMap =
              sstoreAccountMap I.codeOwner
                (sstoreAccountMap I.codeOwner
                  (sstoreAccountMap I.codeOwner σ_evm ⟨0⟩ beneficiaryStoreWordEvm)
                  ⟨1⟩ biddingEndWordEvm)
                ⟨2⟩ revealEndWordEvm := by
            simpa [beneficiaryStoreWordEvm, oldSlotEvm, biddingEndWordEvm, revealEndWordEvm,
              bidWord] using congrArg Prod.snd hacc
          rw [hcA, hσFinal] at hsuccess
          refine constructorEquivalenceFor.execution hsuccess
            (blindAuctionSolmCtorExecSuccess
              (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
              (blocks := blocks) (σ := σ_solm) (σ₀ := σ₀) (g := g) (A := A) (I := I)
              biddingTime revealTime beneficiaryAddress h0Bid hltBid h0Reveal hltReveal hwv
              (by simpa [bidWord] using hoverBid)
              (by
                rw [← hRevealBase]
                simpa [revealWord] using hoverReveal)) ?_
          refine ctorResultEquiv.success rfl rfl ?_ ?_ rfl
          · simp [blindAuctionCtorPostState, blindAuctionCtorAfterBiddingEndState,
              blindAuctionCtorAfterBeneficiaryState, storageStore_createdAccounts, initState]
          · have hOldSlot : oldSlotEvm = oldSlotSolm := by
              exact accountMapEquiv_storage_findD hσ I.codeOwner ⟨0⟩ ⟨0⟩
            have hBeneficiaryStoreWord : beneficiaryStoreWordEvm = beneficiaryStoreWordSolm := by
              simp [beneficiaryStoreWordEvm, beneficiaryStoreWordSolm, oldSlotEvm,
                oldSlotSolm, hOldSlot]
            have hBiddingEndWord : biddingEndWordEvm = biddingEndWordSolm := by
              simpa [biddingEndWordEvm, biddingEndWordSolm, blindAuctionCtorBiddingEndSolmWord,
                bidWord, initState] using (blindAuctionCtorBiddingEndWord_eq
                (initState createdAccounts genesisBlockHeader blocks σ_solm σ₀
                  (Sat256.ofUInt256 g) A I)
                biddingTime h0Bid hltBid (by simpa [initState, bidWord] using hoverBid)).symm
            have hRevealEndWord : revealEndWordEvm = revealEndWordSolm := by
              unfold revealEndWordEvm revealEndWordSolm
              rw [hRevealBase]
              unfold blindAuctionCtorRevealEndSolmWord
              rw [← blindAuctionRevealWord_toNat revealTime h0Reveal hltReveal]
              exact (blindAuctionCtorCheckedAddWord_eq
                (blindAuctionCtorRevealBaseWord
                  (initState createdAccounts genesisBlockHeader blocks σ_solm σ₀
                    (Sat256.ofUInt256 g) A I)
                  biddingTime beneficiaryAddress)
                revealWord (by
                  rw [← hRevealBase]
                  simpa [revealWord] using hoverReveal)).symm
            have hmap0 :
                accountMapEquiv
                  (sstoreAccountMap I.codeOwner σ_evm ⟨0⟩ beneficiaryStoreWordEvm)
                  (sstoreAccountMap I.codeOwner σ_solm ⟨0⟩ beneficiaryStoreWordSolm) := by
              rw [← hBeneficiaryStoreWord]
              exact accountMapEquiv_sstoreAccountMap I.codeOwner ⟨0⟩ beneficiaryStoreWordEvm hσ
            have hmap1 :
                accountMapEquiv
                  (sstoreAccountMap I.codeOwner
                    (sstoreAccountMap I.codeOwner σ_evm ⟨0⟩ beneficiaryStoreWordEvm)
                    ⟨1⟩ biddingEndWordEvm)
                  (sstoreAccountMap I.codeOwner
                    (sstoreAccountMap I.codeOwner σ_solm ⟨0⟩ beneficiaryStoreWordSolm)
                    ⟨1⟩ biddingEndWordSolm) := by
              rw [← hBiddingEndWord]
              exact accountMapEquiv_sstoreAccountMap I.codeOwner ⟨1⟩ biddingEndWordEvm hmap0
            have hmap2 :
                accountMapEquiv
                  (sstoreAccountMap I.codeOwner
                    (sstoreAccountMap I.codeOwner
                      (sstoreAccountMap I.codeOwner σ_evm ⟨0⟩ beneficiaryStoreWordEvm)
                      ⟨1⟩ biddingEndWordEvm)
                    ⟨2⟩ revealEndWordEvm)
                  (sstoreAccountMap I.codeOwner
                    (sstoreAccountMap I.codeOwner
                      (sstoreAccountMap I.codeOwner σ_solm ⟨0⟩ beneficiaryStoreWordSolm)
                      ⟨1⟩ biddingEndWordSolm)
                    ⟨2⟩ revealEndWordSolm) := by
              rw [← hRevealEndWord]
              exact accountMapEquiv_sstoreAccountMap I.codeOwner ⟨2⟩ revealEndWordEvm hmap1
            simpa [blindAuctionCtorPostState, blindAuctionCtorAfterBiddingEndState,
              blindAuctionCtorAfterBeneficiaryState, storageStore_accountMap,
              storageStore_executionEnv, initState, beneficiaryStoreWordSolm,
              oldSlotSolm, biddingEndWordSolm, revealEndWordSolm] using hmap2
  · let bidWordBytes := (EVM.Word.toBytesBE bidWord).toByteArray
    let revealWordBytes := (EVM.Word.toBytesBE revealWord).toByteArray
    let beneficiaryWordBytes := (EVM.Word.toBytesBE (EVM.word beneficiaryAddress)).toByteArray
    let tail := bidWordBytes ++ revealWordBytes ++ beneficiaryWordBytes
    have hcodeTail : I.code = blindAuctionInitcode ++ tail := by
      rw [hcode, hdeployed]
      simp only [tail, bidWordBytes, revealWordBytes, beneficiaryWordBytes, bidWord, revealWord]
      simp [ByteArray.append_assoc]
    have hrd := blindAuctionInitcodeNonpayableRevert
      (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
      (blocks := blocks) (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I)
      (g := Sat256.ofUInt256 g) tail hcodeTail hwv
    rcases hrd.xiResult hcodeTail with hOOG | ⟨g', o, hrev⟩
    · exact constructorEquivalenceFor.outOfGas (by simpa [Sat256.ofUInt256] using hOOG)
    · refine constructorEquivalenceFor.execution (by simpa [Sat256.ofUInt256] using hrev)
        (blindAuctionSolmCtorExecReverts_nonpayable
          (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
          (blocks := blocks) (σ := σ_solm) (σ₀ := σ₀) (g := g) (A := A) (I := I)
          biddingTime revealTime beneficiaryAddress hwv) ?_
      exact ctorResultEquiv.revert rfl rfl

/-- The full BlindAuction contract equivalence combines constructor/initcode and runtime proofs. -/
theorem blindAuctionContractCorrect :
    contractEquivalence blindAuctionConfig blindAuctionInitcode blindAuctionBytecode
      blindAuctionContract :=
  contractEquivalence.intro blindAuctionConstructorCorrect blindAuctionCorrect

end BlindAuction
