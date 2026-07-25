import Examples.SimpleAuction.Bid
import Examples.SimpleAuction.Withdraw
import Examples.SimpleAuction.AuctionEnd
import Examples.SimpleAuction.Beneficiary
import Examples.SimpleAuction.AuctionEndTime
import Examples.SimpleAuction.HighestBidder
import Examples.SimpleAuction.HighestBid
import Reasoning.Refinement
import Reasoning.Initcode
import Reasoning.Memory
import Reasoning.Solc

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace SimpleAuction

/-!
# SimpleAuction — top-level correctness proof

This file is intentionally thin: it drives the payable binary-search dispatcher to the matched body
PC, then hands control to one per-function body theorem.
-/

/-- Calldata shorter than a selector (`size < 4`) reverts before Solm dispatch. -/
theorem simpleAuctionShortRevert {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = simpleAuctionBytecode) (_hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hsz : I.calldata.size < 4) :
    runtimeEquivalenceFor simpleAuctionConfig simpleAuctionContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  exact (simpleAuctionX_short (g := Sat256.ofUInt256 g) hcode hsz).reEquivNoDispatch hcode
    (simpleAuctionDispatch_none_short hsz)

/-- `size ≥ 4` but no selector matches: no Solm dispatch and EVM fallthrough reverts. -/
theorem simpleAuctionNoDispatch {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = simpleAuctionBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true)
    (hnm : ∀ i, i < 7 → (simpleAuctionSelBytes i == I.calldata.extract 0 4) = false) :
    runtimeEquivalenceFor simpleAuctionConfig simpleAuctionContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  by_cases hsz : 4 ≤ I.calldata.size
  · exact (simpleAuctionX_noMatch (g := Sat256.ofUInt256 g) hcode hsz hsize hnm)
      |>.reEquivNoDispatch hcode (simpleAuctionDispatch_none_nomatch hnm)
  · have hshort : I.calldata.size < 4 := by omega
    exact (simpleAuctionX_short (g := Sat256.ofUInt256 g) hcode hshort).reEquivNoDispatch hcode
      (simpleAuctionDispatch_none_short hshort)

/-- The deployed SimpleAuction runtime bytecode refines the Solm specification. -/
theorem simpleAuctionCorrect :
    runtimeEquivalence simpleAuctionConfig simpleAuctionBytecode simpleAuctionContract := by
  refine ⟨fun cA gh bl σ_evm σ_solm σ₀ g A I hcode hsize hperm
      hAccounts => ?_⟩
  by_cases hsz : 4 ≤ I.calldata.size
  · by_cases h0 : selIs I ⟨#[0x19, 0x98, 0xae, 0xef]⟩
    · exact simpleAuctionBidBody hcode hsize hperm h0
        (simpleAuctionReachLowBody 0 (by omega) ⟨114⟩ hcode hsz hsize
          (simpleAuctionPivotTaken 0 (by omega) hsz
            (by simpa [selIs, simpleAuctionLowSelBytes] using h0))
          (simpleAuctionLowMatches 0 (by omega) hsz
            (by simpa [selIs, simpleAuctionLowSelBytes] using h0)).1
          (simpleAuctionLowMatches 0 (by omega) hsz
            (by simpa [selIs, simpleAuctionLowSelBytes] using h0)).2
          (by jump_dest) (by decide))
        hAccounts
    · by_cases h1 : selIs I ⟨#[0x3c, 0xcf, 0xd6, 0x0b]⟩
      · exact simpleAuctionWithdrawBody hcode hsize hperm h1
          (simpleAuctionReachHighBody 0 (by omega) ⟨203⟩ hcode hsz hsize
            (simpleAuctionPivotNotTaken 0 (by omega) hsz
              (by simpa [selIs, simpleAuctionHighSelBytes] using h1))
            (simpleAuctionHighMatches 0 (by omega) hsz
              (by simpa [selIs, simpleAuctionHighSelBytes] using h1)).1
            (simpleAuctionHighMatches 0 (by omega) hsz
              (by simpa [selIs, simpleAuctionHighSelBytes] using h1)).2
            (by jump_dest) (by decide))
          hAccounts
      · by_cases h2 : selIs I ⟨#[0x2a, 0x24, 0xf4, 0x6c]⟩
        · exact simpleAuctionAuctionEndBody hcode hsize hperm h2
            (simpleAuctionReachLowBody 1 (by omega) ⟨124⟩ hcode hsz hsize
              (simpleAuctionPivotTaken 1 (by omega) hsz
                (by simpa [selIs, simpleAuctionLowSelBytes] using h2))
              (simpleAuctionLowMatches 1 (by omega) hsz
                (by simpa [selIs, simpleAuctionLowSelBytes] using h2)).1
              (simpleAuctionLowMatches 1 (by omega) hsz
                (by simpa [selIs, simpleAuctionLowSelBytes] using h2)).2
              (by jump_dest) (by decide))
            hAccounts
        · by_cases h3 : selIs I ⟨#[0x38, 0xaf, 0x3e, 0xed]⟩
          · exact simpleAuctionBeneficiaryBody hcode hsize hperm h3
              (simpleAuctionReachLowBody 2 (by omega) ⟨144⟩ hcode hsz hsize
                (simpleAuctionPivotTaken 2 (by omega) hsz
                  (by simpa [selIs, simpleAuctionLowSelBytes] using h3))
                (simpleAuctionLowMatches 2 (by omega) hsz
                  (by simpa [selIs, simpleAuctionLowSelBytes] using h3)).1
                (simpleAuctionLowMatches 2 (by omega) hsz
                  (by simpa [selIs, simpleAuctionLowSelBytes] using h3)).2
                (by jump_dest) (by decide))
              hAccounts
          · by_cases h4 : selIs I ⟨#[0x4b, 0x44, 0x9c, 0xba]⟩
            · exact simpleAuctionAuctionEndTimeBody hcode hsize hperm h4
                (simpleAuctionReachHighBody 1 (by omega) ⟨239⟩ hcode hsz hsize
                  (simpleAuctionPivotNotTaken 1 (by omega) hsz
                    (by simpa [selIs, simpleAuctionHighSelBytes] using h4))
                  (simpleAuctionHighMatches 1 (by omega) hsz
                    (by simpa [selIs, simpleAuctionHighSelBytes] using h4)).1
                  (simpleAuctionHighMatches 1 (by omega) hsz
                    (by simpa [selIs, simpleAuctionHighSelBytes] using h4)).2
                  (by jump_dest) (by decide))
                hAccounts
            · by_cases h5 : selIs I ⟨#[0x91, 0xf9, 0x01, 0x57]⟩
              · exact simpleAuctionHighestBidderBody hcode hsize hperm h5
                  (simpleAuctionReachHighBody 2 (by omega) ⟨274⟩ hcode hsz hsize
                    (simpleAuctionPivotNotTaken 2 (by omega) hsz
                      (by simpa [selIs, simpleAuctionHighSelBytes] using h5))
                    (simpleAuctionHighMatches 2 (by omega) hsz
                      (by simpa [selIs, simpleAuctionHighSelBytes] using h5)).1
                    (simpleAuctionHighMatches 2 (by omega) hsz
                      (by simpa [selIs, simpleAuctionHighSelBytes] using h5)).2
                    (by jump_dest) (by decide))
                  hAccounts
              · by_cases h6 : selIs I ⟨#[0xd5, 0x7b, 0xde, 0x79]⟩
                · exact simpleAuctionHighestBidBody hcode hsize hperm h6
                    (simpleAuctionReachHighBody 3 (by omega) ⟨305⟩ hcode hsz hsize
                      (simpleAuctionPivotNotTaken 3 (by omega) hsz
                        (by simpa [selIs, simpleAuctionHighSelBytes] using h6))
                      (simpleAuctionHighMatches 3 (by omega) hsz
                        (by simpa [selIs, simpleAuctionHighSelBytes] using h6)).1
                      (simpleAuctionHighMatches 3 (by omega) hsz
                        (by simpa [selIs, simpleAuctionHighSelBytes] using h6)).2
                      (by jump_dest) (by decide))
                    hAccounts
                · refine simpleAuctionNoDispatch hcode hsize hperm ?_
                  intro i hi
                  interval_cases i
                  · simpa [selIs, simpleAuctionSelBytes] using h0
                  · simpa [selIs, simpleAuctionSelBytes] using h1
                  · simpa [selIs, simpleAuctionSelBytes] using h2
                  · simpa [selIs, simpleAuctionSelBytes] using h3
                  · simpa [selIs, simpleAuctionSelBytes] using h4
                  · simpa [selIs, simpleAuctionSelBytes] using h5
                  · simpa [selIs, simpleAuctionSelBytes] using h6
  · exact simpleAuctionShortRevert hcode hsize hperm (by omega)

/-! ## Constructor side -/

theorem simpleAuctionCtorPrefix_size : simpleAuctionCtorPrefix.size = 115 := by
  native_decide

theorem simpleAuctionBytecode_size : simpleAuctionBytecode.size = 1047 := by
  native_decide

theorem simpleAuctionInitcode_size : simpleAuctionInitcode.size = 1162 := by
  rw [simpleAuctionInitcode, ByteArray.size_append, simpleAuctionCtorPrefix_size,
    simpleAuctionBytecode_size]

theorem simpleAuctionInitcode_runtime_window :
    simpleAuctionInitcode.extract 115 (115 + 1047) = simpleAuctionBytecode := by
  unfold simpleAuctionInitcode
  exact extract_append_right' simpleAuctionCtorPrefix simpleAuctionBytecode 115 (115 + 1047)
    simpleAuctionCtorPrefix_size.symm
    (by rw [simpleAuctionCtorPrefix_size, simpleAuctionBytecode_size])

noncomputable def simpleAuctionCtorArgTail (biddingTime : UInt256)
    (beneficiaryAddress : AccountAddress) : ByteArray :=
  (EVM.Word.toBytesBE biddingTime).toByteArray
    ++ (EVM.Word.toBytesBE (EVM.word beneficiaryAddress)).toByteArray

noncomputable def simpleAuctionCtorCode (biddingTime : UInt256)
    (beneficiaryAddress : AccountAddress) : ByteArray :=
  simpleAuctionInitcode ++ simpleAuctionCtorArgTail biddingTime beneficiaryAddress

theorem simpleAuctionInitcode_decode_append (tail : ByteArray) (pc : UInt256)
    (hpc : pc.toNat < 115) :
    decode (simpleAuctionInitcode ++ tail) pc = decode simpleAuctionInitcode pc :=
  Reasoning.Theory.decode_append_left_window simpleAuctionInitcode tail pc
    (by rw [simpleAuctionInitcode_size]; omega) (by rw [simpleAuctionInitcode_size]; norm_num)

macro "simple_ctor_decode" : tactic =>
  `(tactic|
    (first
      | rw [simpleAuctionInitcode_decode_append _ _ (by decide)]
      | (unfold simpleAuctionCtorCode; rw [simpleAuctionInitcode_decode_append _ _ (by decide)]);
     native_decide))

macro "simple_ctor_jd" : tactic =>
  `(tactic|
    (first
      | (apply Reasoning.Theory.D_J_contains_append_left; native_decide)
      | (unfold simpleAuctionCtorCode; apply Reasoning.Theory.D_J_contains_append_left; native_decide)))

open Lean in
macro "simple_ctor_run " base:term " with " "[" steps:evmStep,* "]" : term => do
  let mut acc := base
  for s in steps.getElems do
    match s with
    | `(evmStep| raw $op:ident $args*) =>
        acc ← `($(acc).$op $args*)
    | `(evmStep| $op:ident $args*) =>
        match op.getId with
        | `jump    => acc ← `($(acc).jump (by simple_ctor_decode) $(args[0]!) (by evm_ov))
        | `jumpiT  => acc ← `($(acc).jumpiT (by simple_ctor_decode) $(args[0]!) $(args[1]!)
                            (by evm_ov))
        | `jumpiNT => acc ← `($(acc).jumpiNT (by simple_ctor_decode) $(args[0]!) (by evm_ov))
        | _        => acc ← `($(acc).$op $args* (by simple_ctor_decode) (by evm_ov))
    | _ => Macro.throwUnsupported
  return acc

theorem simpleAuctionDeployment_shape {args : List Value} {deployedInitcode : ByteArray} :
    simpleAuctionConfig.selfDeployment simpleAuctionInitcode args = some deployedInitcode →
    ∃ (biddingTime : Int) (beneficiaryAddress : AccountAddress),
      args = [.int biddingTime, .address beneficiaryAddress]
        ∧ 0 ≤ biddingTime
        ∧ biddingTime < Int.ofNat (EVM.twoPow 256)
        ∧ deployedInitcode =
            simpleAuctionInitcode
              ++ (EVM.Word.toBytesBE (EVM.word biddingTime.toNat)).toByteArray
              ++ (EVM.Word.toBytesBE (EVM.word beneficiaryAddress)).toByteArray := by
  intro h
  cases args with
  | nil =>
      simp [simpleAuctionConfig, genSolidityConstructorDeployment, simpleAuctionContract,
        constructorDecl, encodeABIValues?, encodeABIValuesFrom?, abiTupleHeadSize?,
        uint256, addr] at h
  | cons arg rest =>
      cases rest with
      | nil =>
          cases arg <;>
            simp [simpleAuctionConfig, genSolidityConstructorDeployment, simpleAuctionContract,
              constructorDecl, encodeABIValues?, encodeABIValuesFrom?, abiTupleHeadSize?,
              uint256, addr, staticABIEncodedSize?, isDynamicABIType, encodeABIValue?,
              encodeABIWord?] at h
      | cons arg2 rest =>
          cases rest with
          | cons arg3 rest =>
              cases arg <;> cases arg2 <;>
                simp [simpleAuctionConfig, genSolidityConstructorDeployment, simpleAuctionContract,
                  constructorDecl, encodeABIValues?, encodeABIValuesFrom?, abiTupleHeadSize?,
                  uint256, addr, staticABIEncodedSize?, isDynamicABIType, encodeABIValue?,
                  encodeABIWord?] at h
          | nil =>
              cases arg <;> cases arg2 <;>
                simp [simpleAuctionConfig, genSolidityConstructorDeployment, simpleAuctionContract,
                  constructorDecl, encodeABIValues?, encodeABIValuesFrom?, abiTupleHeadSize?,
                  uint256, addr, staticABIEncodedSize?, isDynamicABIType, encodeABIValue?,
                  encodeABIWord?] at h
              rename_i biddingTime beneficiaryAddress
              by_cases hbounds : 0 ≤ biddingTime ∧ biddingTime < Int.ofNat (EVM.twoPow 256)
              · change ((((if 0 ≤ biddingTime ∧ biddingTime < Int.ofNat (EVM.twoPow 256) then
                      some (EVM.word biddingTime.toNat) else none).bind
                    fun word => some word.toBytesBE).bind
                    fun head => ((some (EVM.word beneficiaryAddress).toBytesBE).bind
                      fun tail => some (head ++ tail))).bind
                    fun args => some (simpleAuctionInitcode ++ args.toByteArray))
                      = some deployedInitcode at h
                split at h
                · simp at h
                  refine ⟨biddingTime, beneficiaryAddress, rfl, hbounds.1, hbounds.2, ?_⟩
                  exact h.symm
                · rename_i hnot
                  exact False.elim (hnot hbounds)
              · change ((((if 0 ≤ biddingTime ∧ biddingTime < Int.ofNat (EVM.twoPow 256) then
                      some (EVM.word biddingTime.toNat) else none).bind
                    fun word => some word.toBytesBE).bind
                    fun head => ((some (EVM.word beneficiaryAddress).toBytesBE).bind
                      fun tail => some (head ++ tail))).bind
                    fun args => some (simpleAuctionInitcode ++ args.toByteArray))
                      = some deployedInitcode at h
                rw [if_neg hbounds] at h
                simp at h

noncomputable def simpleAuctionBeneficiaryMem (biddingTime : UInt256)
    (beneficiaryAddress : AccountAddress) : ByteArray :=
  (simpleAuctionCtorCode biddingTime beneficiaryAddress).write 1194 ByteArray.empty 0 32

noncomputable def simpleAuctionBiddingMem (biddingTime : UInt256)
    (beneficiaryAddress : AccountAddress) : ByteArray :=
  (simpleAuctionCtorCode biddingTime beneficiaryAddress).write 1162
    (simpleAuctionBeneficiaryMem biddingTime beneficiaryAddress) 0 32

theorem simpleAuctionCtorArgTail_size (biddingTime : UInt256)
    (beneficiaryAddress : AccountAddress) :
    (simpleAuctionCtorArgTail biddingTime beneficiaryAddress).size = 64 := by
  unfold simpleAuctionCtorArgTail
  rw [ByteArray.size_append, word_toBytesBE_toByteArray_size, word_toBytesBE_toByteArray_size]

theorem simpleAuctionCtorCode_size (biddingTime : UInt256)
    (beneficiaryAddress : AccountAddress) :
    (simpleAuctionCtorCode biddingTime beneficiaryAddress).size = 1226 := by
  rw [simpleAuctionCtorCode, ByteArray.size_append, simpleAuctionInitcode_size,
    simpleAuctionCtorArgTail_size]

theorem simpleAuctionBeneficiaryArg_extract (biddingTime : UInt256)
    (beneficiaryAddress : AccountAddress) :
    (simpleAuctionCtorCode biddingTime beneficiaryAddress).extract 1194 (1194 + 32)
      = (EVM.Word.toBytesBE (EVM.word beneficiaryAddress)).toByteArray := by
  unfold simpleAuctionCtorCode simpleAuctionCtorArgTail
  rw [← ByteArray.append_assoc]
  exact extract_append_right' (simpleAuctionInitcode ++ (EVM.Word.toBytesBE biddingTime).toByteArray)
    (EVM.Word.toBytesBE (EVM.word beneficiaryAddress)).toByteArray 1194 (1194 + 32)
    (by rw [ByteArray.size_append, simpleAuctionInitcode_size, word_toBytesBE_toByteArray_size])
    (by rw [ByteArray.size_append, simpleAuctionInitcode_size, word_toBytesBE_toByteArray_size,
      word_toBytesBE_toByteArray_size])

theorem simpleAuctionBiddingArg_extract (biddingTime : UInt256)
    (beneficiaryAddress : AccountAddress) :
    (simpleAuctionCtorCode biddingTime beneficiaryAddress).extract 1162 (1162 + 32)
      = (EVM.Word.toBytesBE biddingTime).toByteArray := by
  unfold simpleAuctionCtorCode simpleAuctionCtorArgTail
  rw [← ByteArray.append_assoc]
  rw [extract_append_left _ _ _ _ (by
    rw [ByteArray.size_append, simpleAuctionInitcode_size, word_toBytesBE_toByteArray_size])]
  exact extract_append_right' simpleAuctionInitcode
      (EVM.Word.toBytesBE biddingTime).toByteArray 1162 (1162 + 32)
    simpleAuctionInitcode_size.symm
    (by rw [simpleAuctionInitcode_size, word_toBytesBE_toByteArray_size])

theorem simpleAuction_write0_size_ge_32 (src base : ByteArray) (srcAddr : ℕ)
    (hsrc : srcAddr + 32 ≤ src.size) :
    32 ≤ (src.write srcAddr base 0 32).size := by
  show 32 ≤ (src.write srcAddr base 0 32).data.size
  rw [write0_data_from src base srcAddr 32 (by decide) hsrc, Array.size_append]
  have hpart : (src.data.extract srcAddr (srcAddr + 32)).size = 32 := by
    rw [Array.size_extract]
    have : src.data.size = src.size := rfl
    omega
  omega

theorem simpleAuctionBeneficiaryMem_read (biddingTime : UInt256)
    (beneficiaryAddress : AccountAddress) :
    (simpleAuctionBeneficiaryMem biddingTime beneficiaryAddress).readWithPadding 0 32 =
      UInt256.toByteArray (EVM.word beneficiaryAddress) := by
  unfold simpleAuctionBeneficiaryMem
  rw [write0_read_back_from_gen (simpleAuctionCtorCode biddingTime beneficiaryAddress)
      ByteArray.empty 1194 32 (by decide)
    (by simp [simpleAuctionCtorCode_size])
    (by decide)]
  rw [simpleAuctionBeneficiaryArg_extract, word_toBytesBE_toByteArray_eq_toByteArray]

theorem simpleAuctionBiddingMem_read (biddingTime : UInt256)
    (beneficiaryAddress : AccountAddress) :
    (simpleAuctionBiddingMem biddingTime beneficiaryAddress).readWithPadding 0 32 =
      UInt256.toByteArray biddingTime := by
  unfold simpleAuctionBiddingMem
  rw [write0_read_back_from_gen (simpleAuctionCtorCode biddingTime beneficiaryAddress)
      (simpleAuctionBeneficiaryMem biddingTime beneficiaryAddress) 1162 32 (by decide)
    (by simp [simpleAuctionCtorCode_size])
    (by decide)]
  rw [simpleAuctionBiddingArg_extract, word_toBytesBE_toByteArray_eq_toByteArray]

theorem simpleAuctionBeneficiaryMem_mload (biddingTime : UInt256)
    (beneficiaryAddress : AccountAddress) :
    (if (⟨0⟩ : UInt256).toNat ≥ (simpleAuctionBeneficiaryMem biddingTime beneficiaryAddress).size
        ∨ (⟨0⟩ : UInt256) ≥ (UInt256.ofNat 1) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian
        ((simpleAuctionBeneficiaryMem biddingTime beneficiaryAddress).readWithPadding 0 32)))
      = EVM.word beneficiaryAddress := by
  exact mloadWordValue_of_readWithPadding
    (mem := simpleAuctionBeneficiaryMem biddingTime beneficiaryAddress)
    (aw := UInt256.ofNat 1) (off := ⟨0⟩) (v := EVM.word beneficiaryAddress)
    (by
      unfold simpleAuctionBeneficiaryMem
      have hsz := simpleAuction_write0_size_ge_32
          (simpleAuctionCtorCode biddingTime beneficiaryAddress) ByteArray.empty 1194
        (by simp [simpleAuctionCtorCode_size])
      have hz : (⟨0⟩ : UInt256).toNat = 0 := by decide
      rw [hz]
      omega)
    (by decide)
    (simpleAuctionBeneficiaryMem_read biddingTime beneficiaryAddress)

theorem simpleAuctionBiddingMem_mload (biddingTime : UInt256)
    (beneficiaryAddress : AccountAddress) :
    (if (⟨0⟩ : UInt256).toNat ≥ (simpleAuctionBiddingMem biddingTime beneficiaryAddress).size
        ∨ (⟨0⟩ : UInt256) ≥ (UInt256.ofNat 1) * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat (fromByteArrayBigEndian
        ((simpleAuctionBiddingMem biddingTime beneficiaryAddress).readWithPadding 0 32)))
      = biddingTime := by
  exact mloadWordValue_of_readWithPadding
    (mem := simpleAuctionBiddingMem biddingTime beneficiaryAddress)
    (aw := UInt256.ofNat 1) (off := ⟨0⟩) (v := biddingTime)
    (by
      unfold simpleAuctionBiddingMem
      have hsz := simpleAuction_write0_size_ge_32
        (simpleAuctionCtorCode biddingTime beneficiaryAddress)
          (simpleAuctionBeneficiaryMem biddingTime beneficiaryAddress) 1162
        (by simp [simpleAuctionCtorCode_size])
      have hz : (⟨0⟩ : UInt256).toNat = 0 := by decide
      rw [hz]
      omega)
    (by decide)
    (simpleAuctionBiddingMem_read biddingTime beneficiaryAddress)

theorem simpleAuctionCtorCheckedAddOverflowLt (timestamp biddingTime : UInt256)
    (hover : UInt256.size ≤ timestamp.toNat + biddingTime.toNat) :
    UInt256.lt (biddingTime + timestamp) timestamp = ⟨1⟩ :=
  constructorCheckedAddOverflowLt timestamp biddingTime hover

theorem simpleAuctionCtorCheckedAddNoOverflowLt (timestamp biddingTime : UInt256)
    (hno : ¬ UInt256.size ≤ timestamp.toNat + biddingTime.toNat) :
    UInt256.lt (biddingTime + timestamp) timestamp = ⟨0⟩ :=
  constructorCheckedAddNoOverflowLt timestamp biddingTime hno

noncomputable def simpleAuctionReturnMem (biddingTime : UInt256)
    (beneficiaryAddress : AccountAddress) : ByteArray :=
  (simpleAuctionCtorCode biddingTime beneficiaryAddress).write 115
    (simpleAuctionBiddingMem biddingTime beneficiaryAddress) 0 1047

theorem simpleAuctionRuntime_codecopy_mem (biddingTime : UInt256)
    (beneficiaryAddress : AccountAddress) :
    (simpleAuctionCtorCode biddingTime beneficiaryAddress).write 115
      (simpleAuctionBiddingMem biddingTime beneficiaryAddress) 0 1047 =
        simpleAuctionReturnMem biddingTime beneficiaryAddress := rfl

theorem simpleAuctionReturnMem_read (biddingTime : UInt256)
    (beneficiaryAddress : AccountAddress) :
    (simpleAuctionReturnMem biddingTime beneficiaryAddress).readWithPadding 0 1047 =
      simpleAuctionBytecode := by
  unfold simpleAuctionReturnMem
  rw [write0_read_back_from_gen (simpleAuctionCtorCode biddingTime beneficiaryAddress)
    (simpleAuctionBiddingMem biddingTime beneficiaryAddress) 115 1047 (by decide)
    (by rw [simpleAuctionCtorCode_size]; omega)
    (by decide)]
  have hleft :
      (simpleAuctionCtorCode biddingTime beneficiaryAddress).extract 115 (115 + 1047) =
        simpleAuctionInitcode.extract 115 (115 + 1047) := by
    have h := extract_append_left simpleAuctionInitcode
      (simpleAuctionCtorArgTail biddingTime beneficiaryAddress) 115 (115 + 1047)
      (by rw [simpleAuctionInitcode_size])
    simpa [simpleAuctionCtorCode] using h
  rw [hleft, simpleAuctionInitcode_runtime_window]

theorem simpleAuctionInitcodeNonpayableRevert
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader}
    {blocks : ProcessedBlocks}
    {σ : AccountMap}
    {σ₀ : AccountMap}
    {A : Substate}
    {I : ExecutionEnv}
    {g : Sat256}
    (tail : ByteArray)
    (hcode : I.code = simpleAuctionInitcode ++ tail)
    (hwv : I.weiValue ≠ ⟨0⟩) :
    RDrev (simpleAuctionInitcode ++ tail) g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) := by
  have rd0 :
      RD (simpleAuctionInitcode ++ tail) I g
        (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨0⟩ []
        ByteArray.empty (UInt256.ofNat 0) ByteArray.empty (createdAccounts, σ) 0 0 :=
    RD.initState hcode
  have rd6 := simple_ctor_run rd0 with [
    callvalue, dup1, iszero, push1 ⟨9⟩, jumpiNT (isZero_eq_zero_of_ne hwv)]
  exact rd6.revertStub (by simple_ctor_decode) (by simple_ctor_decode) (by simple_ctor_decode)
    (by simp)

theorem simpleAuctionInitcodeOverflowRevert
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader}
    {blocks : ProcessedBlocks}
    {σ : AccountMap}
    {σ₀ : AccountMap}
    {A : Substate}
    {I : ExecutionEnv}
    {g : Sat256}
    (biddingTime : UInt256)
    (beneficiaryAddress : AccountAddress)
    (hcode : I.code = simpleAuctionCtorCode biddingTime beneficiaryAddress)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hover : UInt256.size ≤ (UInt256.ofNat I.header.timestamp).toNat + biddingTime.toNat) :
    RDrev (simpleAuctionCtorCode biddingTime beneficiaryAddress) g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) := by
    have rd0 :
        RD (simpleAuctionCtorCode biddingTime beneficiaryAddress) I g
          (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨0⟩ []
          ByteArray.empty (UInt256.ofNat 0) ByteArray.empty (createdAccounts, σ) 0 0 :=
      RD.initState hcode
    let oldBeneficiarySlot : UInt256 :=
      (σ.find? I.codeOwner |>.option ⟨0⟩ (fun ac => ac.storage.findD ⟨0⟩ ⟨0⟩))
    have rdBeforeSload := simple_ctor_run rd0 with [
      callvalue, dup1, iszero, push1 ⟨9⟩,
      jumpiT (by rw [hwv]; decide) (by simple_ctor_jd),
      jumpdest, pop, push1 ⟨32⟩, push2 ⟨1194⟩, push0,
      raw codecopy 3 (simpleAuctionBeneficiaryMem biddingTime beneficiaryAddress) (UInt256.ofNat 1)
        (by simple_ctor_decode)
        mem_cost
      rfl
      (by decide) (by evm_ov),
    push0,
    raw mload 0 (EVM.word beneficiaryAddress) (UInt256.ofNat 1)
      (by simple_ctor_decode)
        mem_cost
        (simpleAuctionBeneficiaryMem_mload biddingTime beneficiaryAddress)
        (by decide) (by evm_ov),
      dup1, push20 solcAddrMask, and, push0]
    obtain ⟨kSload, CSload, rdAfterSload⟩ :=
      rdBeforeSload.sload (by simple_ctor_decode) (by evm_ov)
    have rdBeforeStore := simple_ctor_run rdAfterSload with [
      push20 solcAddrMask, not, and, lor, swap1, pop, push0]
    have hpacked :
        UInt256.lor (UInt256.land (UInt256.lnot solcAddrMask) oldBeneficiarySlot)
            (UInt256.land solcAddrMask (EVM.word beneficiaryAddress)) =
          simpleAuctionSetAddressWord oldBeneficiarySlot (EVM.word beneficiaryAddress) := by
      unfold simpleAuctionSetAddressWord
      rw [u256_land_comm (UInt256.lnot solcAddrMask) oldBeneficiarySlot,
        u256_land_comm solcAddrMask (EVM.word beneficiaryAddress)]
    rw [hpacked] at rdBeforeStore
    obtain ⟨k', C', rdAfterStore⟩ :=
      rdBeforeStore.sstore hperm (by simple_ctor_decode) (by evm_ov)
    have rdBeforeLt := simple_ctor_run rdAfterStore with [
      push1 ⟨32⟩, push2 ⟨1162⟩, push0,
    raw codecopy 0 (simpleAuctionBiddingMem biddingTime beneficiaryAddress) (UInt256.ofNat 1)
      (by simple_ctor_decode)
      mem_cost
      rfl
      (by decide) (by evm_ov),
    push0,
    raw mload 0 biddingTime (UInt256.ofNat 1)
      (by simple_ctor_decode)
      mem_cost
      (simpleAuctionBiddingMem_mload biddingTime beneficiaryAddress)
      (by decide) (by evm_ov),
    timestamp, dup1, dup3, add, lt]
    have hlt := simpleAuctionCtorCheckedAddOverflowLt (UInt256.ofNat I.header.timestamp)
      biddingTime hover
    have rdBeforeJump := rdBeforeLt
    rw [hlt] at rdBeforeJump
    have rd61 := simple_ctor_run rdBeforeJump with [
      swap1, pop, push1 ⟨111⟩, jumpiT one_ne_zero_uint (by simple_ctor_jd), jumpdest]
    exact rd61.revertStub (by simple_ctor_decode) (by simple_ctor_decode) (by simple_ctor_decode)
      (by simp)

theorem simpleAuctionInitcodeSuccess
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader}
    {blocks : ProcessedBlocks}
    {σ : AccountMap}
    {σ₀ : AccountMap}
    {A : Substate}
    {I : ExecutionEnv}
    {g : Sat256}
    (biddingTime : UInt256)
    (beneficiaryAddress : AccountAddress)
    (hcode : I.code = simpleAuctionCtorCode biddingTime beneficiaryAddress)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hno : ¬ UInt256.size ≤ (UInt256.ofNat I.header.timestamp).toNat + biddingTime.toNat) :
    RDret (simpleAuctionCtorCode biddingTime beneficiaryAddress) g
      (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I)
      (createdAccounts,
        sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner σ ⟨0⟩
            (simpleAuctionSetAddressWord
              (σ.find? I.codeOwner |>.option ⟨0⟩ (fun ac => ac.storage.findD ⟨0⟩ ⟨0⟩))
              (EVM.word beneficiaryAddress)))
          ⟨1⟩ (biddingTime + UInt256.ofNat I.header.timestamp))
      simpleAuctionBytecode := by
  have rd0 :
      RD (simpleAuctionCtorCode biddingTime beneficiaryAddress) I g
        (initState createdAccounts genesisBlockHeader blocks σ σ₀ g A I) ⟨0⟩ []
        ByteArray.empty (UInt256.ofNat 0) ByteArray.empty (createdAccounts, σ) 0 0 :=
    RD.initState hcode
  let oldBeneficiarySlot : UInt256 :=
    (σ.find? I.codeOwner |>.option ⟨0⟩ (fun ac => ac.storage.findD ⟨0⟩ ⟨0⟩))
  let beneficiaryStoreWord : UInt256 :=
    simpleAuctionSetAddressWord oldBeneficiarySlot (EVM.word beneficiaryAddress)
  have rdBeforeSload := simple_ctor_run rd0 with [
    callvalue, dup1, iszero, push1 ⟨9⟩,
    jumpiT (by rw [hwv]; decide) (by simple_ctor_jd),
    jumpdest, pop, push1 ⟨32⟩, push2 ⟨1194⟩, push0,
    raw codecopy 3 (simpleAuctionBeneficiaryMem biddingTime beneficiaryAddress) (UInt256.ofNat 1)
      (by simple_ctor_decode)
      mem_cost
      rfl
      (by decide) (by evm_ov),
    push0,
    raw mload 0 (EVM.word beneficiaryAddress) (UInt256.ofNat 1)
      (by simple_ctor_decode)
      mem_cost
      (simpleAuctionBeneficiaryMem_mload biddingTime beneficiaryAddress)
      (by decide) (by evm_ov),
    dup1, push20 solcAddrMask, and, push0]
  obtain ⟨kSload, CSload, rdAfterSload⟩ :=
    rdBeforeSload.sload (by simple_ctor_decode) (by evm_ov)
  have rdBeforeStore := simple_ctor_run rdAfterSload with [
    push20 solcAddrMask, not, and, lor, swap1, pop, push0]
  have hpacked :
      UInt256.lor (UInt256.land (UInt256.lnot solcAddrMask) oldBeneficiarySlot)
          (UInt256.land solcAddrMask (EVM.word beneficiaryAddress)) =
        beneficiaryStoreWord := by
    unfold beneficiaryStoreWord simpleAuctionSetAddressWord
    rw [u256_land_comm (UInt256.lnot solcAddrMask) oldBeneficiarySlot,
      u256_land_comm solcAddrMask (EVM.word beneficiaryAddress)]
  rw [hpacked] at rdBeforeStore
  obtain ⟨k', C', rdAfterBeneficiaryStore⟩ :=
    rdBeforeStore.sstore hperm (by simple_ctor_decode) (by evm_ov)
  have rdBeforeLt := simple_ctor_run rdAfterBeneficiaryStore with [
    push1 ⟨32⟩, push2 ⟨1162⟩, push0,
    raw codecopy 0 (simpleAuctionBiddingMem biddingTime beneficiaryAddress) (UInt256.ofNat 1)
      (by simple_ctor_decode)
      mem_cost
      rfl
      (by decide) (by evm_ov),
    push0,
    raw mload 0 biddingTime (UInt256.ofNat 1)
      (by simple_ctor_decode)
      mem_cost
      (simpleAuctionBiddingMem_mload biddingTime beneficiaryAddress)
      (by decide) (by evm_ov),
    timestamp, dup1, dup3, add, lt]
  have hlt := simpleAuctionCtorCheckedAddNoOverflowLt (UInt256.ofNat I.header.timestamp)
    biddingTime hno
  have rdBeforeJump := rdBeforeLt
  rw [hlt] at rdBeforeJump
  have rdBeforeAuctionEndStore := simple_ctor_run rdBeforeJump with [
    swap1, pop, push1 ⟨111⟩, jumpiNT (by decide),
    push0,
    raw mload 0 biddingTime (UInt256.ofNat 1)
      (by simple_ctor_decode)
      mem_cost
      (simpleAuctionBiddingMem_mload biddingTime beneficiaryAddress)
      (by decide) (by evm_ov),
    timestamp, add, push1 ⟨1⟩]
  obtain ⟨k'', C'', rdAfterAuctionEndStore⟩ :=
    rdBeforeAuctionEndStore.sstore hperm (by simple_ctor_decode) (by evm_ov)
  have rdBeforeReturn := simple_ctor_run rdAfterAuctionEndStore with [
    push2 ⟨1047⟩, push1 ⟨115⟩, push0,
    raw codecopy 98 (simpleAuctionReturnMem biddingTime beneficiaryAddress) (UInt256.ofNat 33)
      (by simple_ctor_decode)
      mem_cost
      (simpleAuctionRuntime_codecopy_mem biddingTime beneficiaryAddress)
      (by decide) (by evm_ov),
    push2 ⟨1047⟩, push0]
  simpa [beneficiaryStoreWord, oldBeneficiarySlot, u256_add_comm] using
    rdBeforeReturn.ret 0 simpleAuctionBytecode
      (by simple_ctor_decode)
      mem_cost
      (simpleAuctionReturnMem_read biddingTime beneficiaryAddress)
      (by evm_ov)

def simpleAuctionCtorLocals (biddingTime : Int) (beneficiaryAddress : AccountAddress) : Store :=
  Std.HashMap.ofList
    (List.zip (simpleAuctionContract.ctor.params.map Param.name)
      [.int biddingTime, .address beneficiaryAddress])

theorem simpleAuctionBeneficiaryWord_toNat (beneficiaryAddress : AccountAddress) :
    (EVM.word beneficiaryAddress).toNat = beneficiaryAddress.val := by
  exact ulit_toNat' _ (lt_of_lt_of_le beneficiaryAddress.isLt
    (show AccountAddress.size ≤ UInt256.size from by decide))

theorem simpleAuctionBeneficiary_ofNat (beneficiaryAddress : AccountAddress) :
    AccountAddress.ofNat (EVM.word beneficiaryAddress).toNat = beneficiaryAddress := by
  apply Fin.ext
  unfold AccountAddress.ofNat
  rw [simpleAuctionBeneficiaryWord_toNat, Fin.val_ofNat]
  exact Nat.mod_eq_of_lt beneficiaryAddress.isLt

theorem simpleAuctionBeneficiaryWord_canonical (beneficiaryAddress : AccountAddress) :
    (EVM.word beneficiaryAddress).toNat < EVM.addressModulus := by
  rw [simpleAuctionBeneficiaryWord_toNat]
  simp [EVM.addressModulus, EVM.twoPow, AccountAddress.size]

theorem simpleAuctionBiddingWord_toNat (biddingTime : Int)
    (h0 : 0 ≤ biddingTime)
    (hlt : biddingTime < Int.ofNat (EVM.twoPow 256)) :
    (EVM.word biddingTime.toNat).toNat = biddingTime.toNat :=
  constructorUInt256Word_toNat biddingTime h0 hlt

theorem simpleAuctionCtorLocals_get_biddingTime (biddingTime : Int)
    (beneficiaryAddress : AccountAddress) :
    (simpleAuctionCtorLocals biddingTime beneficiaryAddress).get? "biddingTime" =
      some (.int biddingTime) := by
  unfold simpleAuctionCtorLocals
  simp only [simpleAuctionContract, constructorDecl, List.map_cons, List.map_nil,
    List.zip_cons_cons, List.zip_nil_left]
  rw [show Std.HashMap.ofList
      [("biddingTime", Value.int biddingTime),
        ("beneficiaryAddress", Value.address beneficiaryAddress)] =
      (((∅ : Store).insert "biddingTime" (Value.int biddingTime)).insert
        "beneficiaryAddress" (Value.address beneficiaryAddress)) from rfl]
  rw [store_get_ne]
  · rw [store_get_self]
  · decide

theorem simpleAuctionCtorLocals_get_beneficiaryAddress (biddingTime : Int)
    (beneficiaryAddress : AccountAddress) :
    (simpleAuctionCtorLocals biddingTime beneficiaryAddress).get? "beneficiaryAddress" =
      some (.address beneficiaryAddress) := by
  unfold simpleAuctionCtorLocals
  simp only [simpleAuctionContract, constructorDecl, List.map_cons, List.map_nil,
    List.zip_cons_cons, List.zip_nil_left]
  rw [show Std.HashMap.ofList
      [("biddingTime", Value.int biddingTime),
        ("beneficiaryAddress", Value.address beneficiaryAddress)] =
      (((∅ : Store).insert "biddingTime" (Value.int biddingTime)).insert
        "beneficiaryAddress" (Value.address beneficiaryAddress)) from rfl]
  rw [store_get_self]

theorem simpleAuctionCtorAuctionEndWord_eq (evm : EVM.State) (biddingTime : Int)
    (h0 : 0 ≤ biddingTime)
    (hlt : biddingTime < Int.ofNat (EVM.twoPow 256))
    (hno : ¬ UInt256.size ≤
      (UInt256.ofNat evm.executionEnv.header.timestamp).toNat +
        (EVM.word biddingTime.toNat).toNat) :
    EVM.word ((UInt256.ofNat evm.executionEnv.header.timestamp).toNat + biddingTime.toNat) =
      EVM.word biddingTime.toNat + UInt256.ofNat evm.executionEnv.header.timestamp :=
  constructorCheckedAddIntWord_eq
    (UInt256.ofNat evm.executionEnv.header.timestamp) biddingTime h0 hlt hno

def simpleAuctionCtorAfterBeneficiaryState
    (evm : EVM.State) (beneficiaryAddress : AccountAddress) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨0⟩
    (simpleAuctionSetAddressWord
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩)
      (EVM.word beneficiaryAddress))

theorem simpleAuctionCtorAssignBeneficiary (evm : EVM.State) (biddingTime : Int)
    (beneficiaryAddress : AccountAddress) :
    assignStorageRef? simpleAuctionConfig
      { contract := simpleAuctionContract, locals := simpleAuctionCtorLocals biddingTime beneficiaryAddress }
      evm .storage beneficiaryRef (.address beneficiaryAddress) =
        .ok ({ contract := simpleAuctionContract,
               locals := simpleAuctionCtorLocals biddingTime beneficiaryAddress },
             simpleAuctionCtorAfterBeneficiaryState evm beneficiaryAddress) := by
  apply assignStorageRef_storage_scalar_value (ty := addrSt)
      (hbase := by simp [simpleAuctionCtorLocals, beneficiaryRef, simpleAuctionContract,
        constructorDecl])
      (her := by
        simp [evalStorageRef, evalStorageRefSteps, beneficiaryRef, EvalResult.bind, pure, bind])
      (hty := by
        show storageTypeAt? simpleAuctionContract.storage ({ base := "beneficiary", steps := [] } :
          EvaledStorageRef) = some addrSt
        decide)
      (hloc := simpleAuctionConfig_storage_beneficiary)
      (hscalar := by trivial)
  simpa [simpleAuctionCtorAfterBeneficiaryState, simpleAuctionBeneficiary_ofNat] using
    simpleAuctionStorageLocStore_address_offset0 evm ⟨0⟩ (EVM.word beneficiaryAddress)
      (simpleAuctionBeneficiaryWord_canonical beneficiaryAddress)

theorem simpleAuctionCtorAuctionEndExprReverts
    (evm : EVM.State) (biddingTime : Int) (beneficiaryAddress : AccountAddress)
    (h0 : 0 ≤ biddingTime)
    (hlt : biddingTime < Int.ofNat (EVM.twoPow 256))
    (hover : UInt256.size ≤
      (UInt256.ofNat evm.executionEnv.header.timestamp).toNat +
        (EVM.word biddingTime.toNat).toNat) :
    evalExpr? simpleAuctionConfig
      { contract := simpleAuctionContract, locals := simpleAuctionCtorLocals biddingTime beneficiaryAddress }
      evm (u256 (.binary .add now (.var "biddingTime"))) = .revert := by
  have hword : (EVM.word biddingTime.toNat).toNat = biddingTime.toNat := by
    exact ulit_toNat' _ (by
      have hltNat : biddingTime.toNat < EVM.twoPow 256 := by
        have hlt' : Int.ofNat biddingTime.toNat < Int.ofNat (EVM.twoPow 256) := by
          simpa [Int.toNat_of_nonneg h0] using hlt
        exact Int.ofNat_lt.mp hlt'
      simpa [EVM.twoPow, UInt256.size] using hltNat)
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
  have hlookup :
      (simpleAuctionCtorLocals biddingTime beneficiaryAddress).get? "biddingTime" =
        some (.int biddingTime) := by
    unfold simpleAuctionCtorLocals
    simp only [simpleAuctionContract, constructorDecl, List.map_cons, List.map_nil,
      List.zip_cons_cons, List.zip_nil_left]
    rw [show Std.HashMap.ofList
        [("biddingTime", Value.int biddingTime),
          ("beneficiaryAddress", Value.address beneficiaryAddress)] =
        (((∅ : Store).insert "biddingTime" (Value.int biddingTime)).insert
          "beneficiaryAddress" (Value.address beneficiaryAddress)) from rfl]
    rw [store_get_ne]
    · rw [store_get_self]
    · decide
  simp only [u256, evalExpr?, now, envValue, hlookup, EvalResult.ofOption, EvalResult.bind, bind,
    pure]
  simp only [evalBinaryOp?, uint256Int]
  rw [hInt]
  rw [if_pos (by
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    exact Or.inr hge)]

theorem simpleAuctionCtorAuctionEndExprOK
    (evm : EVM.State) (biddingTime : Int) (beneficiaryAddress : AccountAddress)
    (h0 : 0 ≤ biddingTime)
    (hlt : biddingTime < Int.ofNat (EVM.twoPow 256))
    (hno : ¬ UInt256.size ≤
      (UInt256.ofNat evm.executionEnv.header.timestamp).toNat +
        (EVM.word biddingTime.toNat).toNat) :
    evalExpr? simpleAuctionConfig
      { contract := simpleAuctionContract, locals := simpleAuctionCtorLocals biddingTime beneficiaryAddress }
      evm (u256 (.binary .add now (.var "biddingTime"))) =
        .ok (.int (Int.ofNat
          (EVM.word ((UInt256.ofNat evm.executionEnv.header.timestamp).toNat +
            biddingTime.toNat)).toNat)) := by
  have hword := simpleAuctionBiddingWord_toNat biddingTime h0 hlt
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
  simp only [u256, evalExpr?, now, envValue,
    simpleAuctionCtorLocals_get_biddingTime, EvalResult.ofOption, EvalResult.bind, bind,
    pure]
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

theorem simpleAuctionCtorAssignAuctionEndTime (evm : EVM.State) (biddingTime : Int)
    (beneficiaryAddress : AccountAddress)
    (_h0 : 0 ≤ biddingTime)
    (_hlt : biddingTime < Int.ofNat (EVM.twoPow 256))
    (_hno : ¬ UInt256.size ≤
      (UInt256.ofNat evm.executionEnv.header.timestamp).toNat +
        (EVM.word biddingTime.toNat).toNat) :
    assignStorageRef? simpleAuctionConfig
      { contract := simpleAuctionContract, locals := simpleAuctionCtorLocals biddingTime beneficiaryAddress }
      evm .storage auctionEndTimeRef
      (.int (Int.ofNat
        (EVM.word ((UInt256.ofNat evm.executionEnv.header.timestamp).toNat +
          biddingTime.toNat)).toNat)) =
        .ok ({ contract := simpleAuctionContract,
               locals := simpleAuctionCtorLocals biddingTime beneficiaryAddress },
             Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨1⟩
               (EVM.word ((UInt256.ofNat evm.executionEnv.header.timestamp).toNat +
                 biddingTime.toNat))) := by
  apply assignStorageRef_storage_scalar (ty := uint256St)
      (hbase := by
        unfold simpleAuctionCtorLocals
        simp only [simpleAuctionContract, constructorDecl, List.map_cons, List.map_nil,
          List.zip_cons_cons, List.zip_nil_left]
        rw [show Std.HashMap.ofList
            [("biddingTime", Value.int biddingTime),
              ("beneficiaryAddress", Value.address beneficiaryAddress)] =
            (((∅ : Store).insert "biddingTime" (Value.int biddingTime)).insert
              "beneficiaryAddress" (Value.address beneficiaryAddress)) from rfl]
        rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide)]
        simp)
      (her := by
        simp [evalStorageRef, evalStorageRefSteps, auctionEndTimeRef, EvalResult.bind, pure, bind])
      (hty := by
        simp [storageTypeAt?, simpleAuctionContract, storageDecls, uint256St])
      (hloc := simpleAuctionConfig_storage_auctionEndTime)
  exact simpleAuctionStorageLocStore_uint256 evm ⟨1⟩
    (EVM.word ((UInt256.ofNat evm.executionEnv.header.timestamp).toNat + biddingTime.toNat))

theorem simpleAuctionSolmCtorExecReverts_overflow
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader}
    {blocks : ProcessedBlocks}
    {σ : AccountMap}
    {σ₀ : AccountMap}
    {g : UInt256}
    {A : Substate}
    {I : ExecutionEnv}
    (biddingTime : Int)
    (beneficiaryAddress : AccountAddress)
    (h0 : 0 ≤ biddingTime)
    (hlt : biddingTime < Int.ofNat (EVM.twoPow 256))
    (hwv : I.weiValue = ⟨0⟩)
    (hover : UInt256.size ≤
      (UInt256.ofNat I.header.timestamp).toNat + (EVM.word biddingTime.toNat).toNat) :
    solmCtorExec simpleAuctionConfig simpleAuctionContract
      [.int biddingTime, .address beneficiaryAddress]
      createdAccounts genesisBlockHeader blocks σ σ₀ g A I .reverted := by
  refine solmCtorExec.intro
    (evmState := initState createdAccounts genesisBlockHeader blocks σ σ₀ (Sat256.ofUInt256 g) A I)
    (argsStore := simpleAuctionCtorLocals biddingTime beneficiaryAddress)
    ?_ rfl ?_ ?_
  · rfl
  · simp [simpleAuctionCtorLocals, simpleAuctionContract, constructorDecl]
  · refine ExecFuncBody.execBlockRevert ?_
    let frame : Frame :=
      { contract := simpleAuctionContract,
        locals := simpleAuctionCtorLocals biddingTime beneficiaryAddress }
    let evm0 := initState createdAccounts genesisBlockHeader blocks σ σ₀ (Sat256.ofUInt256 g) A I
    let evm1 := simpleAuctionCtorAfterBeneficiaryState evm0 beneficiaryAddress
    have hlookupBeneficiary :
        (simpleAuctionCtorLocals biddingTime beneficiaryAddress).get? "beneficiaryAddress" =
          some (.address beneficiaryAddress) := by
      unfold simpleAuctionCtorLocals
      simp only [simpleAuctionContract, constructorDecl, List.map_cons, List.map_nil,
        List.zip_cons_cons, List.zip_nil_left]
      rw [show Std.HashMap.ofList
          [("biddingTime", Value.int biddingTime),
            ("beneficiaryAddress", Value.address beneficiaryAddress)] =
          (((∅ : Store).insert "biddingTime" (Value.int biddingTime)).insert
            "beneficiaryAddress" (Value.address beneficiaryAddress)) from rfl]
      rw [store_get_self]
    refine ExecBlock.consNormal (solm' := frame) (evm' := evm0)
      (ExecStmt.requireTrue (evalCallvalueEq_true (cfg := simpleAuctionConfig)
      (solm := frame)
      (evm := evm0)
      (by simpa [initState] using hwv))) ?_
    refine ExecBlock.consNormal (solm' := frame) (evm' := evm1) ?_ ?_
    · exact ExecStmt.assign (value := .address beneficiaryAddress)
        (by
          show evalExpr? simpleAuctionConfig frame evm0 (.var "beneficiaryAddress") =
            .ok (.address beneficiaryAddress)
          unfold frame
          simp only [evalExpr?, hlookupBeneficiary, EvalResult.ofOption])
        (by
          unfold evm1 evm0 frame
          exact simpleAuctionCtorAssignBeneficiary
            (initState createdAccounts genesisBlockHeader blocks σ σ₀ (Sat256.ofUInt256 g) A I)
            biddingTime beneficiaryAddress)
    · exact ExecBlock.consRevert
        (ExecStmt.assignExprRevert
          (simpleAuctionCtorAuctionEndExprReverts
            evm1
            biddingTime beneficiaryAddress h0 hlt (by
              unfold evm1 evm0
              simpa [simpleAuctionCtorAfterBeneficiaryState, storageStore_executionEnv, initState]
                using hover)))

theorem simpleAuctionSolmCtorExecReverts_nonpayable
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader}
    {blocks : ProcessedBlocks}
    {σ : AccountMap}
    {σ₀ : AccountMap}
    {g : UInt256}
    {A : Substate}
    {I : ExecutionEnv}
    (biddingTime : Int)
    (beneficiaryAddress : AccountAddress)
    (hwv : I.weiValue ≠ ⟨0⟩) :
    solmCtorExec simpleAuctionConfig simpleAuctionContract
      [.int biddingTime, .address beneficiaryAddress]
      createdAccounts genesisBlockHeader blocks σ σ₀ g A I .reverted := by
  refine solmCtorExec.intro
    (evmState := initState createdAccounts genesisBlockHeader blocks σ σ₀ (Sat256.ofUInt256 g) A I)
    (argsStore := Std.HashMap.ofList
      (List.zip (simpleAuctionContract.ctor.params.map Param.name)
        [.int biddingTime, .address beneficiaryAddress]))
    ?_ rfl rfl ?_
  · rfl
  · exact bodyReverts_nonPayable (cfg := simpleAuctionConfig) (contract := simpleAuctionContract)
      (locals := Std.HashMap.ofList
        (List.zip (simpleAuctionContract.ctor.params.map Param.name)
          [.int biddingTime, .address beneficiaryAddress]))
      hwv

theorem simpleAuctionSolmCtorExecSuccess
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader}
    {blocks : ProcessedBlocks}
    {σ : AccountMap}
    {σ₀ : AccountMap}
    {g : UInt256}
    {A : Substate}
    {I : ExecutionEnv}
    (biddingTime : Int)
    (beneficiaryAddress : AccountAddress)
    (h0 : 0 ≤ biddingTime)
    (hlt : biddingTime < Int.ofNat (EVM.twoPow 256))
    (hwv : I.weiValue = ⟨0⟩)
    (hno : ¬ UInt256.size ≤
      (UInt256.ofNat I.header.timestamp).toNat + (EVM.word biddingTime.toNat).toNat) :
    solmCtorExec simpleAuctionConfig simpleAuctionContract
      [.int biddingTime, .address beneficiaryAddress]
      createdAccounts genesisBlockHeader blocks σ σ₀ g A I
      (.returned
        { contract := simpleAuctionContract,
          locals := simpleAuctionCtorLocals biddingTime beneficiaryAddress }
        (Solm.EVM.storageStore
          (simpleAuctionCtorAfterBeneficiaryState
            (initState createdAccounts genesisBlockHeader blocks σ σ₀ (Sat256.ofUInt256 g) A I)
            beneficiaryAddress)
          I.codeOwner ⟨1⟩
          (EVM.word ((UInt256.ofNat I.header.timestamp).toNat + biddingTime.toNat)))
        none) := by
  refine solmCtorExec.intro
    (evmState := initState createdAccounts genesisBlockHeader blocks σ σ₀ (Sat256.ofUInt256 g) A I)
    (argsStore := simpleAuctionCtorLocals biddingTime beneficiaryAddress)
    ?_ rfl ?_ ?_
  · rfl
  · simp [simpleAuctionCtorLocals, simpleAuctionContract, constructorDecl]
  · refine ExecFuncBody.execBlockOK ?_
    let frame : Frame :=
      { contract := simpleAuctionContract,
        locals := simpleAuctionCtorLocals biddingTime beneficiaryAddress }
    let evm0 := initState createdAccounts genesisBlockHeader blocks σ σ₀ (Sat256.ofUInt256 g) A I
    let evm1 := simpleAuctionCtorAfterBeneficiaryState evm0 beneficiaryAddress
    let auctionEndWord : UInt256 :=
      EVM.word ((UInt256.ofNat I.header.timestamp).toNat + biddingTime.toNat)
    refine ExecBlock.consNormal (solm' := frame) (evm' := evm0)
      (ExecStmt.requireTrue (evalCallvalueEq_true (cfg := simpleAuctionConfig)
        (solm := frame)
        (evm := evm0)
        (by simpa [evm0, initState] using hwv))) ?_
    refine ExecBlock.consNormal (solm' := frame) (evm' := evm1) ?_ ?_
    · exact ExecStmt.assign (value := .address beneficiaryAddress)
        (by
          show evalExpr? simpleAuctionConfig frame evm0 (.var "beneficiaryAddress") =
            .ok (.address beneficiaryAddress)
          unfold frame
          simp only [evalExpr?, simpleAuctionCtorLocals_get_beneficiaryAddress,
            EvalResult.ofOption])
        (by
          unfold evm1 evm0 frame
          exact simpleAuctionCtorAssignBeneficiary
            (initState createdAccounts genesisBlockHeader blocks σ σ₀ (Sat256.ofUInt256 g) A I)
            biddingTime beneficiaryAddress)
    · refine ExecBlock.consNormal ?_ ExecBlock.nil
      exact ExecStmt.assign (value := .int (Int.ofNat auctionEndWord.toNat))
        (by
          unfold auctionEndWord evm1 evm0 frame
          simpa [simpleAuctionCtorAfterBeneficiaryState, storageStore_executionEnv, initState]
            using simpleAuctionCtorAuctionEndExprOK
              (simpleAuctionCtorAfterBeneficiaryState
                (initState createdAccounts genesisBlockHeader blocks σ σ₀ (Sat256.ofUInt256 g) A I)
                beneficiaryAddress)
              biddingTime beneficiaryAddress h0 hlt (by
                simpa [simpleAuctionCtorAfterBeneficiaryState, storageStore_executionEnv, initState]
                  using hno))
        (by
          unfold auctionEndWord evm1 evm0 frame
          simpa [simpleAuctionCtorAfterBeneficiaryState, storageStore_executionEnv, initState]
            using simpleAuctionCtorAssignAuctionEndTime
              (simpleAuctionCtorAfterBeneficiaryState
                (initState createdAccounts genesisBlockHeader blocks σ σ₀ (Sat256.ofUInt256 g) A I)
                beneficiaryAddress)
              biddingTime beneficiaryAddress h0 hlt (by
                simpa [simpleAuctionCtorAfterBeneficiaryState, storageStore_executionEnv, initState]
                  using hno))

theorem simpleAuctionConstructorEquiv_nonpayable
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader}
    {blocks : ProcessedBlocks}
    {σ_evm : AccountMap}
    {σ_solm : AccountMap}
    {σ₀ : AccountMap}
    {g : UInt256}
    {A : Substate}
    {I : ExecutionEnv}
    {args : List Value}
    {deployedInitcode : ByteArray}
    (hdeploy : simpleAuctionConfig.selfDeployment simpleAuctionInitcode args = some deployedInitcode)
    (hcode : I.code = deployedInitcode)
    (_hcalldata : I.calldata = .empty)
    (_hperm : I.perm = true)
    (_hσ : accountMapEquiv σ_evm σ_solm)
    (hwv : I.weiValue ≠ ⟨0⟩) :
    constructorEquivalenceFor simpleAuctionConfig simpleAuctionContract args createdAccounts
      genesisBlockHeader blocks σ_evm σ_solm σ₀ g A I simpleAuctionBytecode := by
  rcases simpleAuctionDeployment_shape hdeploy with
    ⟨biddingTime, beneficiaryAddress, hargs, _h0, _hlt, hdeployed⟩
  subst args
  let bidWordBytes := (EVM.Word.toBytesBE (EVM.word biddingTime.toNat)).toByteArray
  let beneficiaryWordBytes := (EVM.Word.toBytesBE (EVM.word beneficiaryAddress)).toByteArray
  let tail := bidWordBytes ++ beneficiaryWordBytes
  have hcodeTail : I.code = simpleAuctionInitcode ++ tail := by
    rw [hcode, hdeployed]
    simp only [tail, bidWordBytes, beneficiaryWordBytes]
    rw [ByteArray.append_assoc]
  have hrd := simpleAuctionInitcodeNonpayableRevert
    (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
    (blocks := blocks) (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I)
    (g := Sat256.ofUInt256 g) tail hcodeTail hwv
  rcases hrd.xiResult hcodeTail with hOOG | ⟨g', o, hrev⟩
  · exact constructorEquivalenceFor.outOfGas (by simpa [Sat256.ofUInt256] using hOOG)
  · refine constructorEquivalenceFor.execution (by simpa [Sat256.ofUInt256] using hrev)
      (simpleAuctionSolmCtorExecReverts_nonpayable
        (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
        (blocks := blocks) (σ := σ_solm) (σ₀ := σ₀) (g := g) (A := A) (I := I)
        biddingTime beneficiaryAddress hwv) ?_
    exact ctorResultEquiv.revert rfl rfl

theorem simpleAuctionConstructorEquiv_overflow
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader}
    {blocks : ProcessedBlocks}
    {σ_evm : AccountMap}
    {σ_solm : AccountMap}
    {σ₀ : AccountMap}
    {g : UInt256}
    {A : Substate}
    {I : ExecutionEnv}
    {args : List Value}
    {deployedInitcode : ByteArray}
    (hdeploy : simpleAuctionConfig.selfDeployment simpleAuctionInitcode args = some deployedInitcode)
    (hcode : I.code = deployedInitcode)
    (_hcalldata : I.calldata = .empty)
    (hperm : I.perm = true)
    (_hσ : accountMapEquiv σ_evm σ_solm)
    (hwv : I.weiValue = ⟨0⟩)
    (hoverShape : ∀ biddingTime : Int, 0 ≤ biddingTime →
      biddingTime < Int.ofNat (EVM.twoPow 256) →
      args.head? = some (.int biddingTime) →
      UInt256.size ≤
        (UInt256.ofNat I.header.timestamp).toNat + (EVM.word biddingTime.toNat).toNat) :
    constructorEquivalenceFor simpleAuctionConfig simpleAuctionContract args createdAccounts
      genesisBlockHeader blocks σ_evm σ_solm σ₀ g A I simpleAuctionBytecode := by
  rcases simpleAuctionDeployment_shape hdeploy with
    ⟨biddingTime, beneficiaryAddress, hargs, h0, hlt, hdeployed⟩
  subst args
  have hover : UInt256.size ≤
      (UInt256.ofNat I.header.timestamp).toNat + (EVM.word biddingTime.toNat).toNat := by
    exact hoverShape biddingTime h0 hlt rfl
  have hcodeCtor : I.code =
      simpleAuctionCtorCode (EVM.word biddingTime.toNat) beneficiaryAddress := by
    rw [hcode, hdeployed]
    unfold simpleAuctionCtorCode simpleAuctionCtorArgTail
    rw [ByteArray.append_assoc]
  have hrd := simpleAuctionInitcodeOverflowRevert
    (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
    (blocks := blocks) (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I)
    (g := Sat256.ofUInt256 g) (EVM.word biddingTime.toNat) beneficiaryAddress hcodeCtor
    hperm hwv hover
  rcases hrd.xiResult hcodeCtor with hOOG | ⟨g', o, hrev⟩
  · exact constructorEquivalenceFor.outOfGas (by simpa [Sat256.ofUInt256] using hOOG)
  · refine constructorEquivalenceFor.execution (by simpa [Sat256.ofUInt256] using hrev)
      (simpleAuctionSolmCtorExecReverts_overflow
        (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
        (blocks := blocks) (σ := σ_solm) (σ₀ := σ₀) (g := g) (A := A) (I := I)
        biddingTime beneficiaryAddress h0 hlt hwv hover) ?_
    exact ctorResultEquiv.revert rfl rfl

theorem simpleAuctionConstructorEquiv_success
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader}
    {blocks : ProcessedBlocks}
    {σ_evm : AccountMap}
    {σ_solm : AccountMap}
    {σ₀ : AccountMap}
    {g : UInt256}
    {A : Substate}
    {I : ExecutionEnv}
    {args : List Value}
    {deployedInitcode : ByteArray}
    (hdeploy : simpleAuctionConfig.selfDeployment simpleAuctionInitcode args = some deployedInitcode)
    (hcode : I.code = deployedInitcode)
    (_hcalldata : I.calldata = .empty)
    (hperm : I.perm = true)
    (hσ : accountMapEquiv σ_evm σ_solm)
    (hwv : I.weiValue = ⟨0⟩)
    (hnoShape : ∀ biddingTime : Int, 0 ≤ biddingTime →
      biddingTime < Int.ofNat (EVM.twoPow 256) →
      args.head? = some (.int biddingTime) →
      ¬ UInt256.size ≤
        (UInt256.ofNat I.header.timestamp).toNat + (EVM.word biddingTime.toNat).toNat) :
    constructorEquivalenceFor simpleAuctionConfig simpleAuctionContract args createdAccounts
      genesisBlockHeader blocks σ_evm σ_solm σ₀ g A I simpleAuctionBytecode := by
  rcases simpleAuctionDeployment_shape hdeploy with
    ⟨biddingTime, beneficiaryAddress, hargs, h0, hlt, hdeployed⟩
  subst args
  have hno : ¬ UInt256.size ≤
      (UInt256.ofNat I.header.timestamp).toNat + (EVM.word biddingTime.toNat).toNat := by
    exact hnoShape biddingTime h0 hlt rfl
  have hcodeCtor : I.code =
      simpleAuctionCtorCode (EVM.word biddingTime.toNat) beneficiaryAddress := by
    rw [hcode, hdeployed]
    unfold simpleAuctionCtorCode simpleAuctionCtorArgTail
    rw [ByteArray.append_assoc]
  have hrd := simpleAuctionInitcodeSuccess
    (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
    (blocks := blocks) (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I)
    (g := Sat256.ofUInt256 g) (EVM.word biddingTime.toNat) beneficiaryAddress hcodeCtor
    hperm hwv hno
  rcases hrd with hOOG | ⟨s, hX, hacc⟩
  · exact constructorEquivalenceFor.outOfGas
      (Xi_error_of_X (g := g) (by
        rw [← hcodeCtor] at hOOG
        simpa [Sat256.ofUInt256] using hOOG))
  · have hsuccess := Xi_success_of_X (g := g) (by
      rw [← hcodeCtor] at hX
      simpa [Sat256.ofUInt256] using hX)
    let beneficiaryStoreWordEvm : UInt256 :=
      simpleAuctionSetAddressWord
        (σ_evm.find? I.codeOwner |>.option ⟨0⟩ (fun ac => ac.storage.findD ⟨0⟩ ⟨0⟩))
        (EVM.word beneficiaryAddress)
    let beneficiaryStoreWordSolm : UInt256 :=
      simpleAuctionSetAddressWord
        (σ_solm.find? I.codeOwner |>.option ⟨0⟩ (fun ac => ac.storage.findD ⟨0⟩ ⟨0⟩))
        (EVM.word beneficiaryAddress)
    let auctionEndWordEvm : UInt256 :=
      EVM.word biddingTime.toNat + UInt256.ofNat I.header.timestamp
    let auctionEndWordSolm : UInt256 :=
      EVM.word ((UInt256.ofNat I.header.timestamp).toNat + biddingTime.toNat)
    have hcA : s.createdAccounts = createdAccounts := congrArg Prod.fst hacc
    have hσ' : s.accountMap =
        sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner σ_evm ⟨0⟩ beneficiaryStoreWordEvm)
          ⟨1⟩ auctionEndWordEvm := by
      simpa [beneficiaryStoreWordEvm, auctionEndWordEvm] using congrArg Prod.snd hacc
    rw [hcA, hσ'] at hsuccess
    refine constructorEquivalenceFor.execution hsuccess
      (simpleAuctionSolmCtorExecSuccess
        (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
        (blocks := blocks) (σ := σ_solm) (σ₀ := σ₀) (g := g) (A := A) (I := I)
        biddingTime beneficiaryAddress h0 hlt hwv hno) ?_
    refine ctorResultEquiv.success rfl rfl ?_ ?_ rfl
    · simp only [storageStore_createdAccounts, initState, simpleAuctionCtorAfterBeneficiaryState]
    · have hOldSlot :
          (σ_evm.find? I.codeOwner |>.option ⟨0⟩ (fun ac => ac.storage.findD ⟨0⟩ ⟨0⟩)) =
            (σ_solm.find? I.codeOwner |>.option ⟨0⟩
              (fun ac => ac.storage.findD ⟨0⟩ ⟨0⟩)) := by
        exact accountMapEquiv_storage_findD hσ I.codeOwner ⟨0⟩ ⟨0⟩
      have hAuctionEnd :
          EVM.word ((UInt256.ofNat I.header.timestamp).toNat + biddingTime.toNat) =
            auctionEndWordEvm := by
        unfold auctionEndWordEvm
        exact simpleAuctionCtorAuctionEndWord_eq
          (initState createdAccounts genesisBlockHeader blocks σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          biddingTime h0 hlt (by simpa [initState] using hno)
      simp only [storageStore_accountMap, initState, simpleAuctionCtorAfterBeneficiaryState]
      simp only [Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage]
      rw [← hOldSlot, hAuctionEnd]
      exact accountMapEquiv_sstoreAccountMap I.codeOwner ⟨1⟩ auctionEndWordEvm
        (accountMapEquiv_sstoreAccountMap I.codeOwner ⟨0⟩ beneficiaryStoreWordEvm hσ)

/-- The creation/initcode bytecode refines the Solm constructor specification. -/
theorem simpleAuctionConstructorCorrect :
    constructorEquivalence simpleAuctionConfig simpleAuctionInitcode simpleAuctionContract
      simpleAuctionBytecode := by
  refine constructorEquivalence.intro ?_
  intro createdAccounts genesisBlockHeader blocks σ_evm σ_solm σ₀ g A I
      args deployedInitcode hdeploy hcode hcalldata hperm hσ
  rcases simpleAuctionDeployment_shape hdeploy with
    ⟨biddingTime, beneficiaryAddress, hargs, h0, hlt, hdeployed⟩
  subst args
  by_cases hwv : I.weiValue = ⟨0⟩
  · by_cases hover : UInt256.size ≤
        (UInt256.ofNat I.header.timestamp).toNat + (EVM.word biddingTime.toNat).toNat
    · exact simpleAuctionConstructorEquiv_overflow
        (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
        (blocks := blocks) (σ_evm := σ_evm) (σ_solm := σ_solm) (σ₀ := σ₀)
        (g := g) (A := A) (I := I) (args := [.int biddingTime, .address beneficiaryAddress])
        (deployedInitcode := deployedInitcode) hdeploy hcode hcalldata hperm hσ hwv
        (by
          intro biddingTime' _h0' _hlt' hhead
          simp only [List.head?_cons] at hhead
          injection hhead with hval
          injection hval with hb
          subst biddingTime'
          exact hover)
    · exact simpleAuctionConstructorEquiv_success
        (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
        (blocks := blocks) (σ_evm := σ_evm) (σ_solm := σ_solm) (σ₀ := σ₀)
        (g := g) (A := A) (I := I) (args := [.int biddingTime, .address beneficiaryAddress])
        (deployedInitcode := deployedInitcode) hdeploy hcode hcalldata hperm hσ hwv
        (by
          intro biddingTime' _h0' _hlt' hhead
          simp only [List.head?_cons] at hhead
          injection hhead with hval
          injection hval with hb
          subst biddingTime'
          exact hover)
  · exact simpleAuctionConstructorEquiv_nonpayable
      (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
      (blocks := blocks) (σ_evm := σ_evm) (σ_solm := σ_solm) (σ₀ := σ₀)
      (g := g) (A := A) (I := I) (args := [.int biddingTime, .address beneficiaryAddress])
      (deployedInitcode := deployedInitcode) hdeploy hcode hcalldata hperm hσ hwv

/-- The full contract equivalence combines constructor/initcode and runtime equivalence. -/
theorem simpleAuctionContractCorrect :
    contractEquivalence simpleAuctionConfig simpleAuctionInitcode simpleAuctionBytecode
      simpleAuctionContract :=
  contractEquivalence.intro simpleAuctionConstructorCorrect simpleAuctionCorrect

end SimpleAuction
