import Examples.BlindAuction.Storage
import Reasoning.Refinement
import Reasoning.SolmBody
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Nat.Digits.Lemmas

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace BlindAuction

/-! ## `ended()` getter -/

def endedWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨3⟩ ⟨0⟩)

abbrev endedMaskedWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.land ⟨255⟩ (endedWord σ I)

abbrev endedReturnWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.isZero (UInt256.isZero (endedMaskedWord σ I))

-- PROMOTE -> Common.lean: generic `fromBytes' = Nat.ofDigits 256` bridge.
theorem blindAuctionFromBytes'_eq_ofDigits (bs : List UInt8) :
    fromBytes' bs = Nat.ofDigits 256 (bs.map (fun b => b.toNat)) := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp [fromBytes', Nat.ofDigits, ih]

-- PROMOTE -> Common.lean / Reasoning.EVMWord: `Nat.land` is commutative.
theorem blindAuctionNat_land_comm (a b : ℕ) : Nat.land a b = Nat.land b a := by
  apply Nat.eq_of_testBit_eq
  intro i
  show (a &&& b).testBit i = (b &&& a).testBit i
  rw [Nat.testBit_and, Nat.testBit_and, Bool.and_comm]

-- PROMOTE -> Common.lean / Reasoning.EVMWord: `UInt256.land` is commutative.
theorem blindAuctionU256_land_comm (a b : UInt256) : UInt256.land a b = UInt256.land b a := by
  apply u256_inj
  show Nat.land a.toNat b.toNat % UInt256.size =
    Nat.land b.toNat a.toNat % UInt256.size
  rw [blindAuctionNat_land_comm]

-- PROMOTE -> Common.lean / Reasoning.EVMWord: low-bit mask as modulus.
theorem blindAuctionNat_land_mask_eq_mod (n k : Nat) :
    Nat.land n (2 ^ k - 1) = n % 2 ^ k := by
  apply Nat.eq_of_testBit_eq
  intro i
  show (n &&& (2 ^ k - 1)).testBit i = (n % 2 ^ k).testBit i
  rw [Nat.testBit_and, Nat.testBit_two_pow_sub_one, Nat.testBit_mod_two_pow]
  by_cases hi : i < k
  · rw [decide_eq_true hi]
    simp
  · rw [decide_eq_false hi]
    simp

-- PROMOTE -> Common.lean: low byte of an EVM word as the Solidity packed bool byte.
theorem blindAuctionFromBytes'_take1_wordLE (w : UInt256) :
    fromBytes' ((EVM.Word.toBytesLEWithSizeProof w).1.take 1) =
      (UInt256.land w ⟨255⟩).toNat := by
  let bs := (EVM.Word.toBytesLEWithSizeProof w).1
  have hfull : Nat.ofDigits 256 (bs.map (fun b : UInt8 => b.toNat)) = w.toNat := by
    rw [← blindAuctionFromBytes'_eq_ofDigits bs]
    exact fromBytes'_toBytesLEWithSizeProof w
  have hlt : ∀ l ∈ bs.map (fun b : UInt8 => b.toNat), l < 256 := by
    intro l hl
    simp only [List.mem_map] at hl
    rcases hl with ⟨b, _hb, rfl⟩
    exact b.toFin.isLt
  have htake := Nat.ofDigits_mod_pow_eq_ofDigits_take (p := 256) 1 (by decide)
    (bs.map (fun b : UInt8 => b.toNat)) hlt
  rw [blindAuctionFromBytes'_eq_ofDigits ((EVM.Word.toBytesLEWithSizeProof w).1.take 1)]
  change Nat.ofDigits 256 ((bs.take 1).map fun b : UInt8 => b.toNat) = _
  rw [List.map_take, ← htake, hfull]
  show w.toNat % 256 ^ 1 = (Nat.land w.toNat (⟨255⟩ : UInt256).toNat) % UInt256.size
  rw [show 256 ^ 1 = 2 ^ 8 by norm_num]
  rw [show (⟨255⟩ : UInt256).toNat = 2 ^ 8 - 1 by decide]
  rw [blindAuctionNat_land_mask_eq_mod]
  have hsmall : w.toNat % 2 ^ 8 < UInt256.size :=
    lt_of_lt_of_le (Nat.mod_lt _ (by norm_num : 0 < 2 ^ 8)) (by norm_num [UInt256.size])
  conv_rhs => rw [Nat.mod_eq_of_lt hsmall]

-- PROMOTE -> Common.lean: BlindAuction packed bool `storageLocLoad` for byte offset 0.
theorem blindAuctionStorageLocLoad_bool_offset0 (evm : EVM.State) (slot : UInt256) :
    storageLocLoad evm (blindAuctionBoolLoc slot) =
      wordToElem .bool
        (UInt256.land ⟨255⟩ (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)) := by
  unfold storageLocLoad blindAuctionBoolLoc
  simp only [Fin.val_zero, Nat.zero_add]
  congr
  change fromBytes' ((EVM.Word.toBytesLEWithSizeProof
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).1.take 1) = _
  rw [blindAuctionFromBytes'_take1_wordLE]
  exact congrArg UInt256.toNat
    (blindAuctionU256_land_comm (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) ⟨255⟩)

-- PROMOTE -> Common.lean: ABI-encoding `false` as a one-word bool return.
theorem blindAuctionBoolFalseReturnEncoding :
    encodeReturnValue? boolTy (.bool false) = some (UInt256.toByteArray ⟨0⟩) := by
  simpa [boolTy] using
    scalarReturnEncoding (t := .bool) (w := (⟨0⟩ : UInt256)) rfl
      (by simp only [abiTupleHeadSize?, staticABIEncodedSize?, isDynamicABIType, bind,
        Option.bind]; decide)
      (by simp [encodeABIValue?, encodeABIWord?, Bool.toUInt256_false]; rfl)

theorem blindAuctionBoolTrueReturnEncoding :
    encodeReturnValue? boolTy (.bool true) = some (UInt256.toByteArray ⟨1⟩) := by
  simpa [boolTy] using boolTrueReturnEncoding

theorem blindAuctionBoolReturnEncoding (w : UInt256) :
    encodeReturnValue? boolTy (wordToElem .bool (UInt256.land ⟨255⟩ w)) =
      some (UInt256.toByteArray (UInt256.isZero (UInt256.isZero (UInt256.land ⟨255⟩ w)))) := by
  by_cases hval : (UInt256.land ⟨255⟩ w).val = 0
  · have hz : UInt256.land ⟨255⟩ w = ⟨0⟩ := by
      apply u256_inj
      exact congrArg Fin.val hval
    have hnorm : UInt256.isZero (UInt256.isZero (⟨0⟩ : UInt256)) = ⟨0⟩ := by decide
    simpa [wordToElem, hz, hnorm] using blindAuctionBoolFalseReturnEncoding
  · have hz : UInt256.land ⟨255⟩ w ≠ ⟨0⟩ := by
      intro hx
      apply hval
      rw [hx]
    have hiz : UInt256.isZero (UInt256.land ⟨255⟩ w) = ⟨0⟩ := isZero_eq_zero_of_ne hz
    have hnorm : UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ := by decide
    simpa [wordToElem, hval, hiz, hnorm] using blindAuctionBoolTrueReturnEncoding

theorem blindAuctionEndedBodyReturns (evm : EVM.State) (locals : Store)
    (h : evm.executionEnv.weiValue = ⟨0⟩)
    (hlocals : locals.get? "ended" = none) :
    ExecTransitionBody blindAuctionConfig blindAuctionContract evm locals endedGetter.body
      (.returned { contract := blindAuctionContract, locals := locals } evm
        (some (wordToElem .bool
          (UInt256.land ⟨255⟩ (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨3⟩))))) := by
  exact ExecFuncBody.execBlockRet <|
    (ABlock.start.requireStep (evalCallvalueEq_true h)).returns (by
      have her : evalStorageRef blindAuctionConfig
          { contract := blindAuctionContract, locals := locals } evm endedRef =
          .ok { base := "ended", steps := [] } := by
        simp [evalStorageRef, evalStorageRefSteps, endedRef, EvalResult.bind, pure, bind]
      have hty : storageTypeAt? blindAuctionContract.storage
          ({ base := "ended", steps := [] } : EvaledStorageRef) = some (.elem .bool) := by
        decide
      rw [evalExpr_storage_scalar (t := .bool) (hbase := hlocals) (her := her)
        (hty := hty) (hloc := blindAuctionConfig_storage_ended),
        blindAuctionStorageLocLoad_bool_offset0])

theorem blindAuctionX_ended {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩)
    (hreach : ∃ k C, RD blindAuctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨215⟩ [blindAuctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret blindAuctionBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (endedReturnWord σ I)) := by
  obtain ⟨_, _, rd215⟩ := hreach
  have rd228 := evm_run rd215 with [
    jumpdest, callvalue, dup1, iszero, push2 ⟨226⟩,
    jumpiT (by rw [hwv]; decide) (by jump_dest),
    jumpdest, pop, push1 ⟨3⟩]
  obtain ⟨_, _, rd231₀⟩ := rd228.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd231⟩ :
      ∃ k C, RD blindAuctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨231⟩
        [endedWord σ I, blindAuctionSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [endedWord, initState] using rd231₀⟩
  have rd240 := evm_run rd231 with [
    push2 ⟨240⟩, swap1, push1 ⟨255⟩, and, dup2, jump (by jump_dest)]
  have rd206 := evm_run rd240 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost
      solcFreePtrMem_mload64
      (by decide) (by evm_ov),
    swap1, iszero, iszero, dup2,
    raw mstore 6 (solcReturnMem (endedReturnWord σ I)) (UInt256.ofNat 5)
      (by decide) mem_cost
      (by
        rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide]
        rfl)
      (by decide) (by evm_ov),
    push1 ⟨32⟩, add, push2 ⟨206⟩, jump (by jump_dest)]
  exact evm_run rd206 with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) (by decide)
      mem_cost
      (solcReturnMem_mload64 (endedReturnWord σ I))
      (by decide) (by evm_ov),
    dup1, swap2, sub, swap1,
    raw ret 0 (UInt256.toByteArray (endedReturnWord σ I)) (by decide)
      mem_cost
      (by
        rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide,
          show (UInt256.sub ((⟨32⟩ : UInt256) + ⟨128⟩) ⟨128⟩).toNat = 32 from by decide]
        simpa using solcReturnMem_read128 (endedReturnWord σ I))
      (by evm_ov)]

theorem blindAuctionX_ended_nonpayable {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue ≠ ⟨0⟩)
    (hreach : ∃ k C, RD blindAuctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨215⟩ [blindAuctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev blindAuctionBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd215⟩ := hreach
  have rd223 := evm_run rd215 with [
    jumpdest, callvalue, dup1, iszero, push2 ⟨226⟩,
    jumpiNT (isZero_eq_zero_of_ne hwv)]
  exact rd223.revertStub (by decide) (by decide) (by decide)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem blindAuctionEndedSelector_size {I : ExecutionEnv}
    (hsel : selIs I ⟨#[0x12, 0xfa, 0x6f, 0xeb]⟩) :
    4 ≤ I.calldata.size := by
  have hs := byteArray_size_eq_of_beq hsel
  have hleft : (⟨#[0x12, 0xfa, 0x6f, 0xeb]⟩ : ByteArray).size = 4 := rfl
  rw [hleft, ByteArray.size_extract] at hs
  omega

theorem blindAuctionDispatch_ended {cd : ByteArray}
    (hsel : ((⟨#[0x12, 0xfa, 0x6f, 0xeb]⟩ : ByteArray) == cd.extract 0 4) = true) :
    dispatchMsg blindAuctionContract cd = some endedGetter := by
  have hcd : cd.extract 0 4 = (⟨#[0x12, 0xfa, 0x6f, 0xeb]⟩ : ByteArray) :=
    (blindAuctionByteArray_eq_of_beq hsel).symm
  refine dispatchMsg_eq_some_of_split
    (pre := [bidTransition, revealTransition, withdrawTransition, auctionEndTransition,
      beneficiaryGetter, biddingEndGetter, revealEndGetter])
    (post := [highestBidderGetter, highestBidGetter, bidsGetter])
    rfl ?_ (by rw [selectorOf, blindAuctionEndedSelectorBytes]; exact hsel)
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [selectorOf, blindAuctionBidSelectorBytes, hcd]; decide
  · rw [selectorOf, blindAuctionRevealSelectorBytes, hcd]; decide
  · rw [selectorOf, blindAuctionWithdrawSelectorBytes, hcd]; decide
  · rw [selectorOf, blindAuctionAuctionEndSelectorBytes, hcd]; decide
  · rw [selectorOf, blindAuctionBeneficiarySelectorBytes, hcd]; decide
  · rw [selectorOf, blindAuctionBiddingEndSelectorBytes, hcd]; decide
  · rw [selectorOf, blindAuctionRevealEndSelectorBytes, hcd]; decide

theorem blindAuctionDecode_ended {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldata (endedGetter.params.map Param.name)
      (transitionSignature endedGetter).paramTypes I.calldata = some ∅ := by
  show decodeCalldata [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz

/-- `ended()` getter body (pc 215) refines its transition. -/
theorem blindAuctionEndedBodyCore {cA gh bl σ_evm σ₀_evm σ_solm σ₀_solm A I} {g : UInt256}
    (hcode : I.code = blindAuctionBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hsel : selIs I ⟨#[0x12, 0xfa, 0x6f, 0xeb]⟩)
    (hreach : ∃ k C, RD blindAuctionBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀_evm (Sat256.ofUInt256 g) A I) ⟨215⟩
      [blindAuctionSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm)
      k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hOriginalAccounts : accountMapEquiv σ₀_evm σ₀_solm) :
    runtimeEquivalenceFor blindAuctionConfig blindAuctionContract cA gh bl
      σ_evm σ₀_evm σ_solm σ₀_solm g A I := by
  have _hsize : I.calldata.size < UInt256.size := hsize
  have _hperm : I.perm = true := hperm
  have _hOriginalAccounts : accountMapEquiv σ₀_evm σ₀_solm := hOriginalAccounts
  have hsz := blindAuctionEndedSelector_size hsel
  have hd := blindAuctionDispatch_ended (cd := I.calldata) hsel
  have hdec := blindAuctionDecode_ended (I := I) hsz
  by_cases hwv : I.weiValue = ⟨0⟩
  · have hword : endedWord σ_evm I = endedWord σ_solm I :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨3⟩ ⟨0⟩
    have hbody :
        ExecTransitionBody blindAuctionConfig blindAuctionContract
          (initState cA gh bl σ_solm σ₀_solm (Sat256.ofUInt256 g) A I) ∅
          endedGetter.body
          (.returned { contract := blindAuctionContract, locals := ∅ }
            (initState cA gh bl σ_solm σ₀_solm (Sat256.ofUInt256 g) A I)
            (some (wordToElem .bool (endedMaskedWord σ_solm I)))) := by
      simpa [endedWord, endedMaskedWord, initState, Solm.EVM.storageLoad, State.lookupAccount] using
        blindAuctionEndedBodyReturns
          (initState cA gh bl σ_solm σ₀_solm (Sat256.ofUInt256 g) A I) ∅
          (by simp only [initState]; exact hwv) (by simp)
    exact (blindAuctionX_ended (g := Sat256.ofUInt256 g) hwv hreach)
      |>.reEquivExecutionTransport hcode hd hdec hbody (by simp [endedMaskedWord, hword])
        hAccounts
        (returnEquiv_of_encode (blindAuctionBoolReturnEncoding (endedWord σ_evm I)))
  · have hbody :
        ExecTransitionBody blindAuctionConfig blindAuctionContract
          (initState cA gh bl σ_solm σ₀_solm (Sat256.ofUInt256 g) A I) ∅
          endedGetter.body .reverted := by
      simpa [endedGetter, initState] using
        (bodyReverts_nonPayable (cfg := blindAuctionConfig) (contract := blindAuctionContract)
          (evm := initState cA gh bl σ_solm σ₀_solm (Sat256.ofUInt256 g) A I)
          (locals := (∅ : Store))
          (rest := [.return (.storage endedRef)])
          (by simp only [initState]; exact hwv))
    exact (blindAuctionX_ended_nonpayable (g := Sat256.ofUInt256 g) hwv hreach)
      |>.reEquivExecutionRevert hcode hd hdec hbody

end BlindAuction
