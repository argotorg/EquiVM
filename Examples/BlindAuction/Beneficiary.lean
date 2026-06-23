import Examples.BlindAuction.Storage
import Reasoning.Refinement
import Reasoning.SolmBody
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Nat.Digits.Lemmas

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace BlindAuction

/-! ## `beneficiary()` getter -/

def beneficiaryWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨0⟩ ⟨0⟩)

abbrev beneficiaryReturnWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.land (beneficiaryWord σ I) solcAddrMask

-- PROMOTE -> Common.lean: generic `fromBytes' = Nat.ofDigits 256` bridge.
theorem beneficiaryFromBytes'_eq_ofDigits (bs : List UInt8) :
    fromBytes' bs = Nat.ofDigits 256 (bs.map (fun b => b.toNat)) := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp [fromBytes', Nat.ofDigits, ih]

-- PROMOTE -> Common.lean / Reasoning.EVMWord: low-bit mask as modulus.
theorem beneficiaryNat_land_mask_eq_mod (n k : Nat) :
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

-- PROMOTE -> Common.lean / Reasoning.EVMWord: `Nat.land` is commutative.
theorem beneficiaryNat_land_comm (a b : ℕ) : Nat.land a b = Nat.land b a := by
  apply Nat.eq_of_testBit_eq
  intro i
  show (a &&& b).testBit i = (b &&& a).testBit i
  rw [Nat.testBit_and, Nat.testBit_and, Bool.and_comm]

-- PROMOTE -> Common.lean / Reasoning.EVMWord: `UInt256.land` is commutative.
theorem beneficiaryU256_land_comm (a b : UInt256) : UInt256.land a b = UInt256.land b a := by
  apply u256_inj
  show Nat.land a.toNat b.toNat % UInt256.size =
    Nat.land b.toNat a.toNat % UInt256.size
  rw [beneficiaryNat_land_comm]

-- PROMOTE -> Common.lean: low 20 little-endian bytes of an EVM word as an address word.
theorem beneficiaryFromBytes'_take20_wordLE (w : UInt256) :
    fromBytes' ((EVM.Word.toBytesLEWithSizeProof w).1.take 20) =
      (UInt256.land w solcAddrMask).toNat := by
  let bs := (EVM.Word.toBytesLEWithSizeProof w).1
  have hfull : Nat.ofDigits 256 (bs.map (fun b : UInt8 => b.toNat)) = w.toNat := by
    rw [← beneficiaryFromBytes'_eq_ofDigits bs]
    exact fromBytes'_toBytesLEWithSizeProof w
  have hlt : ∀ l ∈ bs.map (fun b : UInt8 => b.toNat), l < 256 := by
    intro l hl
    simp only [List.mem_map] at hl
    rcases hl with ⟨b, _hb, rfl⟩
    exact b.toFin.isLt
  have htake := Nat.ofDigits_mod_pow_eq_ofDigits_take (p := 256) 20 (by decide)
    (bs.map (fun b : UInt8 => b.toNat)) hlt
  rw [beneficiaryFromBytes'_eq_ofDigits (bs.take 20), List.map_take]
  rw [← htake, hfull]
  show w.toNat % 256 ^ 20 = (Nat.land w.toNat solcAddrMask.toNat) % UInt256.size
  rw [show 256 ^ 20 = 2 ^ 160 by norm_num]
  rw [show solcAddrMask.toNat = 2 ^ 160 - 1 by decide]
  rw [beneficiaryNat_land_mask_eq_mod]
  have hsmall : w.toNat % 2 ^ 160 < UInt256.size :=
    lt_of_lt_of_le (Nat.mod_lt _ (by norm_num : 0 < 2 ^ 160))
      (by norm_num [UInt256.size])
  conv_rhs => rw [Nat.mod_eq_of_lt hsmall]

-- PROMOTE -> Common.lean: BlindAuction full-slot Solidity address `storageLocLoad` helper.
theorem beneficiaryStorageLocLoad_address_offset0 (evm : EVM.State) (slot : UInt256) :
    storageLocLoad evm (blindAuctionAddrLoc slot) =
      .address (AccountAddress.ofNat
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)
          solcAddrMask).toNat) := by
  unfold storageLocLoad blindAuctionAddrLoc wordToElem
  simp only [Fin.val_zero, Nat.zero_add]
  change Value.address (AccountAddress.ofNat
      (fromBytes' (((EVM.Word.toBytesLEWithSizeProof
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).1).extract 0 20))) = _
  rw [List.extract_eq_take_drop, List.drop_zero]
  rw [beneficiaryFromBytes'_take20_wordLE]

-- PROMOTE -> Common.lean / Reasoning.EVMWord: address-mask result is canonical.
theorem beneficiarySolcAddrMask_result_canonical (w : UInt256) :
    (UInt256.land w solcAddrMask).toNat < EVM.addressModulus := by
  have hlandle : ∀ a b : ℕ, Nat.land a b ≤ b := by
    intro a b
    refine Nat.le_of_testBit fun i hi => ?_
    change (a &&& b).testBit i = true at hi
    rw [Nat.testBit_and] at hi
    simp only [Bool.and_eq_true] at hi
    exact hi.2
  show (Nat.land w.toNat solcAddrMask.toNat) % UInt256.size < EVM.addressModulus
  have hle : Nat.land w.toNat solcAddrMask.toNat ≤ solcAddrMask.toNat := hlandle _ _
  have hltSize : Nat.land w.toNat solcAddrMask.toNat < UInt256.size :=
    lt_of_le_of_lt hle (by decide)
  rw [Nat.mod_eq_of_lt hltSize]
  exact lt_of_le_of_lt hle (by decide)

-- PROMOTE -> Common.lean: ABI encoding for a Solidity address return word.
theorem beneficiaryAddressReturnEncoding (w : UInt256) :
    encodeReturnValue? addr (.address (AccountAddress.ofNat (UInt256.land w solcAddrMask).toNat)) =
      some (UInt256.toByteArray (UInt256.land w solcAddrMask)) := by
  have hcanon := beneficiarySolcAddrMask_result_canonical w
  have haddrMod : (UInt256.land w solcAddrMask).toNat % AccountAddress.size =
      (UInt256.land w solcAddrMask).toNat := by
    apply Nat.mod_eq_of_lt
    simpa [EVM.addressModulus, EVM.twoPow, AccountAddress.size] using hcanon
  have hword : EVM.word (UInt256.land w solcAddrMask).toNat = UInt256.land w solcAddrMask :=
    u256_ofNat_toNat _
  refine scalarReturnEncoding (t := .address) (w := UInt256.land w solcAddrMask) rfl ?_ ?_
  · simp only [abiTupleHeadSize?, staticABIEncodedSize?, isDynamicABIType, bind, Option.bind]
    decide
  · simp [encodeABIValue?, encodeABIWord?, AccountAddress.ofNat, haddrMod, hword]

abbrev beneficiaryRetEnd : UInt256 := (⟨32⟩ : UInt256) + ⟨128⟩

theorem beneficiarySubRet32_toNat :
    (UInt256.sub beneficiaryRetEnd ⟨128⟩).toNat = 32 := by
  decide

theorem beneficiaryRoutineEncodeAddress {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {val ret : UInt256} {R : List UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD blindAuctionBytecode ee g s0 ⟨308⟩ (val :: ret :: R)
        solcFreePtrMem (UInt256.ofNat 3) rdata acc k C)
    (hov : R.length + 8 ≤ 1024) :
    ∃ k' C', RD blindAuctionBytecode ee g s0 ⟨206⟩ (beneficiaryRetEnd :: ret :: R)
      (solcReturnMem (UInt256.land val solcAddrMask)) (UInt256.ofNat 5) rdata acc k' C' := by
  let rd := evm_run h with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost
      solcFreePtrMem_mload64
      (by decide) (by evm_ov),
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub,
    swap1, swap2, and, dup2,
    raw mstore 6 (solcReturnMem (UInt256.land val solcAddrMask)) (UInt256.ofNat 5)
      (by decide) mem_cost
      (by
        rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
          solcAddrMask from by decide]
        rfl)
      (by decide) (by evm_ov),
    push1 ⟨32⟩, add, push2 ⟨206⟩, jump (by jump_dest)]
  exact ⟨_, _, by simpa using rd⟩

theorem beneficiaryReturnOneWord206 {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {val : UInt256} {R : List UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD blindAuctionBytecode ee g s0 ⟨206⟩ (beneficiaryRetEnd :: R)
        (solcReturnMem val) (UInt256.ofNat 5) rdata acc k C)
    (hov : R.length + 5 ≤ 1024) :
    RDret blindAuctionBytecode g s0 acc (UInt256.toByteArray val) := by
  exact evm_run h with [
    jumpdest, push1 ⟨64⟩,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) (by decide)
      mem_cost
      (solcReturnMem_mload64 val)
      (by decide) (by evm_ov),
    dup1, swap2, sub, swap1,
    raw ret 0 (UInt256.toByteArray val) (by decide)
      mem_cost
      (by
        rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide,
          beneficiarySubRet32_toNat]
        simpa using solcReturnMem_read128 val)
      (by evm_ov)]

theorem blindAuctionBeneficiaryBodyReturns (evm : EVM.State) (locals : Store)
    (h : evm.executionEnv.weiValue = ⟨0⟩)
    (hlocals : locals.get? "beneficiary" = none) :
    ExecTransitionBody blindAuctionConfig blindAuctionContract evm locals beneficiaryGetter.body
      (.returned { contract := blindAuctionContract, locals := locals } evm
        (some (.address (AccountAddress.ofNat
          (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩)
            solcAddrMask).toNat)))) := by
  exact ExecFuncBody.execBlockRet <|
    (ABlock.start.requireStep (evalCallvalueEq_true h)).returns (by
      have her : evalStorageRef blindAuctionConfig
          { contract := blindAuctionContract, locals := locals } evm beneficiaryRef =
          .ok { base := "beneficiary", steps := [] } := by
        simp [evalStorageRef, evalStorageRefSteps, beneficiaryRef, EvalResult.bind, pure, bind]
      have hty : storageTypeAt? blindAuctionContract.storage
          ({ base := "beneficiary", steps := [] } : EvaledStorageRef) =
          some (.elem .address) := by
        decide
      rw [evalExpr_storage_scalar (t := .address) (hbase := hlocals) (her := her)
        (hty := hty) (hloc := blindAuctionConfig_storage_beneficiary),
        beneficiaryStorageLocLoad_address_offset0])

theorem blindAuctionX_beneficiary {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩)
    (hreach : ∃ k C, RD blindAuctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨278⟩ [blindAuctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret blindAuctionBytecode g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (beneficiaryReturnWord σ I)) := by
  obtain ⟨_, _, rd278⟩ := hreach
  have rd289 := evm_run rd278 with [
    jumpdest, callvalue, dup1, iszero, push2 ⟨289⟩,
    jumpiT (by rw [hwv]; decide) (by jump_dest)]
  have rd292 := evm_run rd289 with [jumpdest, pop, push0]
  obtain ⟨_, _, rd293₀⟩ := rd292.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd293⟩ :
      ∃ k C, RD blindAuctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨293⟩
        [beneficiaryWord σ I, blindAuctionSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [beneficiaryWord, initState] using rd293₀⟩
  have rd308 := evm_run rd293 with [
    push2 ⟨308⟩, swap1, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩,
    shl, sub, and, dup2, jump (by jump_dest)]
  obtain ⟨_, _, rd206⟩ := beneficiaryRoutineEncodeAddress
    (val := UInt256.land solcAddrMask (beneficiaryWord σ I)) (ret := ⟨308⟩)
    (R := [blindAuctionSelWord I]) rd308 (by simp only [List.length_singleton]; omega)
  have hval : UInt256.land solcAddrMask (beneficiaryWord σ I) =
      UInt256.land (beneficiaryWord σ I) solcAddrMask :=
    beneficiaryU256_land_comm solcAddrMask (beneficiaryWord σ I)
  have hclean : UInt256.land (UInt256.land solcAddrMask (beneficiaryWord σ I)) solcAddrMask =
      beneficiaryReturnWord σ I := by
    rw [hval]
    exact solcAddrMask_clean (beneficiarySolcAddrMask_result_canonical (beneficiaryWord σ I))
  have hret := beneficiaryReturnOneWord206 (R := [⟨308⟩, blindAuctionSelWord I]) rd206
    (by simp only [List.length_cons, List.length_nil]; omega)
  simpa [beneficiaryReturnWord, hclean] using hret

theorem blindAuctionX_beneficiary_nonpayable {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue ≠ ⟨0⟩)
    (hreach : ∃ k C, RD blindAuctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨278⟩ [blindAuctionSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev blindAuctionBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd278⟩ := hreach
  have rd286 := evm_run rd278 with [
    jumpdest, callvalue, dup1, iszero, push2 ⟨289⟩,
    jumpiNT (isZero_eq_zero_of_ne hwv)]
  exact rd286.revertStub (by decide) (by decide) (by decide)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem blindAuctionBeneficiarySelector_size {I : ExecutionEnv}
    (hsel : selIs I ⟨#[0x38, 0xaf, 0x3e, 0xed]⟩) :
    4 ≤ I.calldata.size := by
  have hs := byteArray_size_eq_of_beq hsel
  have hleft : (⟨#[0x38, 0xaf, 0x3e, 0xed]⟩ : ByteArray).size = 4 := rfl
  rw [hleft, ByteArray.size_extract] at hs
  omega

theorem blindAuctionDispatch_beneficiary {cd : ByteArray}
    (hsel : ((⟨#[0x38, 0xaf, 0x3e, 0xed]⟩ : ByteArray) == cd.extract 0 4) = true) :
    dispatchMsg blindAuctionContract cd = some beneficiaryGetter := by
  have hcd : cd.extract 0 4 = (⟨#[0x38, 0xaf, 0x3e, 0xed]⟩ : ByteArray) :=
    (blindAuctionByteArray_eq_of_beq hsel).symm
  refine dispatchMsg_eq_some_of_split
    (pre := [bidTransition, revealTransition, withdrawTransition, auctionEndTransition])
    (post := [biddingEndGetter, revealEndGetter, endedGetter, highestBidderGetter,
      highestBidGetter, bidsGetter])
    rfl ?_ (by rw [selectorOf, blindAuctionBeneficiarySelectorBytes]; exact hsel)
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl
  · rw [selectorOf, blindAuctionBidSelectorBytes, hcd]; decide
  · rw [selectorOf, blindAuctionRevealSelectorBytes, hcd]; decide
  · rw [selectorOf, blindAuctionWithdrawSelectorBytes, hcd]; decide
  · rw [selectorOf, blindAuctionAuctionEndSelectorBytes, hcd]; decide

theorem blindAuctionDecode_beneficiary {I : ExecutionEnv} (hsz : 4 ≤ I.calldata.size) :
    decodeCalldata (beneficiaryGetter.params.map Param.name)
      (transitionSignature beneficiaryGetter).paramTypes I.calldata = some ∅ := by
  show decodeCalldata [] [] I.calldata = some ∅
  exact decodeCalldata_empty_ok hsz

/-- `beneficiary()` getter body (pc 278) refines its transition. -/
theorem blindAuctionBeneficiaryBodyCore {cA gh bl σ_evm σ₀_evm σ_solm σ₀_solm A I}
    {g : UInt256}
    (hcode : I.code = blindAuctionBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hsel : selIs I ⟨#[0x38, 0xaf, 0x3e, 0xed]⟩)
    (hreach : ∃ k C, RD blindAuctionBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀_evm (Sat256.ofUInt256 g) A I) ⟨278⟩
      [blindAuctionSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm)
      k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hOriginalAccounts : accountMapEquiv σ₀_evm σ₀_solm) :
    runtimeEquivalenceFor blindAuctionConfig blindAuctionContract cA gh bl
      σ_evm σ₀_evm σ_solm σ₀_solm g A I := by
  have _hsize : I.calldata.size < UInt256.size := hsize
  have _hperm : I.perm = true := hperm
  have _hOriginalAccounts : accountMapEquiv σ₀_evm σ₀_solm := hOriginalAccounts
  have hsz := blindAuctionBeneficiarySelector_size hsel
  have hd := blindAuctionDispatch_beneficiary (cd := I.calldata) hsel
  have hdec := blindAuctionDecode_beneficiary (I := I) hsz
  by_cases hwv : I.weiValue = ⟨0⟩
  · have hword : beneficiaryWord σ_evm I = beneficiaryWord σ_solm I :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨0⟩ ⟨0⟩
    have hbody :
        ExecTransitionBody blindAuctionConfig blindAuctionContract
          (initState cA gh bl σ_solm σ₀_solm (Sat256.ofUInt256 g) A I) ∅
          beneficiaryGetter.body
          (.returned { contract := blindAuctionContract, locals := ∅ }
            (initState cA gh bl σ_solm σ₀_solm (Sat256.ofUInt256 g) A I)
            (some (.address (AccountAddress.ofNat (beneficiaryReturnWord σ_solm I).toNat)))) := by
      simpa [beneficiaryWord, beneficiaryReturnWord, initState, Solm.EVM.storageLoad,
        State.lookupAccount] using blindAuctionBeneficiaryBodyReturns
          (initState cA gh bl σ_solm σ₀_solm (Sat256.ofUInt256 g) A I) ∅
          (by simp only [initState]; exact hwv) (by simp)
    exact (blindAuctionX_beneficiary (g := Sat256.ofUInt256 g) hwv hreach)
      |>.reEquivExecutionTransport hcode hd hdec hbody
        (by simp [beneficiaryReturnWord, hword]) hAccounts
        (returnEquiv_of_encode (beneficiaryAddressReturnEncoding (beneficiaryWord σ_evm I)))
  · have hbody :
        ExecTransitionBody blindAuctionConfig blindAuctionContract
          (initState cA gh bl σ_solm σ₀_solm (Sat256.ofUInt256 g) A I) ∅
          beneficiaryGetter.body .reverted := by
      simpa [beneficiaryGetter, initState] using
        (bodyReverts_nonPayable (cfg := blindAuctionConfig) (contract := blindAuctionContract)
          (evm := initState cA gh bl σ_solm σ₀_solm (Sat256.ofUInt256 g) A I)
          (locals := (∅ : Store))
          (rest := [.return (.storage beneficiaryRef)])
          (by simp only [initState]; exact hwv))
    exact (blindAuctionX_beneficiary_nonpayable (g := Sat256.ofUInt256 g) hwv hreach)
      |>.reEquivExecutionRevert hcode hd hdec hbody

end BlindAuction
