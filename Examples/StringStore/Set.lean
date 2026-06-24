import Examples.StringStore.Getters

/-!
# StringStore — `set(string)` branch scaffolding

This file isolates selector/reach facts and the Solm-side body skeleton for `set(string)`.  The
remaining bytecode proof should provide the storage-operation facts consumed by `setBodyReturns`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace StringStore

theorem stringStoreDispatch_set {cd : ByteArray}
    (hsel : ((⟨#[0x4e, 0xd3, 0x88, 0x5e]⟩ : ByteArray) == cd.extract 0 4) = true) :
    dispatchMsg stringStoreContract cd = some setTransition := by
  have hcd : cd.extract 0 4 = (⟨#[0x4e, 0xd3, 0x88, 0x5e]⟩ : ByteArray) :=
    (byteArray_eq_of_beq hsel).symm
  refine dispatchMsg_eq_some_of_split
    (pre := []) (post := [appendToHistoryTransition, replaceFromHistoryTransition,
      dropLastTransition, clearCurrentTransition, clearAllTransition, storeRawTransition,
      currentLengthGetter, historyLengthGetter, rawLengthGetter]) rfl ?_
    (by rw [selectorOf, setSelectorBytes]; exact hsel)
  intro t ht
  simp at ht

theorem stringStoreReachSet {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = stringStoreBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0x4e, 0xd3, 0x88, 0x5e]⟩) :
    ∃ k C, RD stringStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨238⟩
      [stringStoreSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C := by
  have hmatches := stringStoreLowMatches 2 (by omega) hsz hsel
  exact stringStoreReachLowBody 2 (by omega) ⟨238⟩ hcode hwv hsz hsize
    (stringStorePivotTaken 2 (by omega) hsz hsel)
    hmatches.1 hmatches.2 (by jump_dest) (by decide)

theorem stringStoreReachSetDecoder {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = stringStoreBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0x4e, 0xd3, 0x88, 0x5e]⟩) :
    ∃ k C, RD stringStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2815⟩
      [⟨4⟩, UInt256.ofNat I.calldata.size, ⟨259⟩, ⟨264⟩, stringStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C := by
  obtain ⟨k0, C0, hreach⟩ := stringStoreReachSet
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) hcode hwv hsz hsize hsel
  have hsizeWord :
      (⟨4⟩ : UInt256) + UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩ =
        UInt256.ofNat I.calldata.size := by
    exact uadd_lit_usub_ofNat_lit hsz hsize
  exact ⟨_, _, by
    simpa [hsizeWord] using
      (evm_run hreach with [
        jumpdest, push2 ⟨264⟩, push1 ⟨4⟩, dup1, calldatasize, sub, dup2, add, swap1,
        push2 ⟨259⟩, swap2, swap1, push2 ⟨2815⟩,
        jump (by jump_dest) ])⟩

theorem stringStoreX_setDecoderHeadShort {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = stringStoreBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0x4e, 0xd3, 0x88, 0x5e]⟩)
    (hshort : I.calldata.size < 36) :
    RDrev stringStoreBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨k0, C0, hdec⟩ := stringStoreReachSetDecoder
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) hcode hwv hsz hsize hsel
  have hslt :
      UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨1⟩ :=
    solcDecodeLenCheckShort_4_32 hsz hshort hsize
  exact evm_run hdec with [
    jumpdest, push0, push0, push1 ⟨32⟩, dup4, dup6, sub, slt, iszero, push2 ⟨2837⟩,
    jumpiNT (by rw [hslt]; decide),
    push2 ⟨2836⟩, push2 ⟨2406⟩,
    jump (by jump_dest),
    jumpdest, raw revertStub (by decide) (by decide) (by decide) (by evm_ov) ]

theorem stringStoreX_setDecoderHeadHuge {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = stringStoreBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0x4e, 0xd3, 0x88, 0x5e]⟩)
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) :
    RDrev stringStoreBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨k0, C0, hdec⟩ := stringStoreReachSetDecoder
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) hcode hwv hsz hsize hsel
  have hslt :
      UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨1⟩ :=
    solcDecodeLenCheckHuge_4_32 hbig hsize
  exact evm_run hdec with [
    jumpdest, push0, push0, push1 ⟨32⟩, dup4, dup6, sub, slt, iszero, push2 ⟨2837⟩,
    jumpiNT (by rw [hslt]; decide),
    push2 ⟨2836⟩, push2 ⟨2406⟩,
    jump (by jump_dest),
    jumpdest, raw revertStub (by decide) (by decide) (by decide) (by evm_ov) ]

theorem stringStoreX_setDecoderOffsetHuge {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = stringStoreBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0x4e, 0xd3, 0x88, 0x5e]⟩)
    (hoff : ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat) :
    RDrev stringStoreBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨k0, C0, hdec⟩ := stringStoreReachSetDecoder
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) hcode hwv (by omega) hsize hsel
  have hslt :
      UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨0⟩ :=
    solcDecodeLenCheckOk_4_32 hsz36 hhi hsize
  have hgt :
      UInt256.gt (calldataWord I.calldata 4) ⟨18446744073709551615⟩ = ⟨1⟩ := by
    exact ugt_one (by simpa [ABI.solcMaxU64] using hoff)
  have hgt' :
      UInt256.gt
          (uInt256OfByteArray (I.calldata.readBytes ((⟨4⟩ : UInt256) + ⟨0⟩).toNat 32))
          ⟨18446744073709551615⟩ = ⟨1⟩ := by
    simpa [calldataWord] using hgt
  have rd2842 := evm_run hdec with [
    jumpdest, push0, push0, push1 ⟨32⟩, dup4, dup6, sub, slt, iszero, push2 ⟨2837⟩,
    jumpiT (by rw [hslt]; decide) (by jump_dest),
    jumpdest, push0, dup4, add, calldataload]
  have rd2851 := RD.pushConst rd2842 ⟨18446744073709551615⟩
    (width := 8) (op := .PUSH8) (by decide) (by native_decide) (by evm_ov)
  exact evm_run rd2851 with [
    dup2,
    gt, iszero, push2 ⟨2866⟩,
    jumpiNT (by rw [hgt']; decide),
    push2 ⟨2865⟩, push2 ⟨2410⟩,
    jump (by jump_dest),
    jumpdest, raw revertStub (by decide) (by decide) (by decide) (by evm_ov) ]

theorem stringStoreX_stringDecoder2730LengthShort {cA gh bl σ σ₀ A I} {g : Sat256}
    {k C : Nat} {start ennd ret headOff : UInt256} {R : List UInt256}
    (rd : RD stringStoreBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2730⟩
      (start :: ennd :: ret :: headOff :: R) solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C)
    (hstart : UInt256.slt (start + ⟨31⟩) ennd = ⟨0⟩)
    (hov : R.length + 12 ≤ 1024) :
    RDrev stringStoreBytecode g (initState cA gh bl σ σ₀ g A I) := by
  exact evm_run rd with [
    jumpdest, push0, push0, dup4, push1 ⟨31⟩, dup5, add, slt, push2 ⟨2751⟩,
    jumpiNT (by exact hstart),
    push2 ⟨2750⟩, push2 ⟨2718⟩, jump (by jump_dest),
    jumpdest, raw revertStub (by decide) (by decide) (by decide) (by evm_ov) ]

set_option maxHeartbeats 1200000 in
theorem stringStoreX_setDecoderLengthShort {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = stringStoreBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0x4e, 0xd3, 0x88, 0x5e]⟩)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hlenShort : I.calldata.size < 4 + (calldataWord I.calldata 4).toNat + 32) :
    RDrev stringStoreBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨k0, C0, hdec⟩ := stringStoreReachSetDecoder
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) hcode hwv (by omega) hsize hsel
  have hslt :
      UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨0⟩ :=
    solcDecodeLenCheckOk_4_32 hsz36 hhi hsize
  have hgt :
      UInt256.gt (calldataWord I.calldata 4) ⟨18446744073709551615⟩ = ⟨0⟩ := by
    apply ugt_zero
    rw [show (⟨18446744073709551615⟩ : UInt256).toNat = ABI.solcMaxU64 by native_decide]
    exact Nat.le_of_not_gt hoffMax
  have hgt' :
      UInt256.gt
          (uInt256OfByteArray (I.calldata.readBytes ((⟨4⟩ : UInt256) + ⟨0⟩).toNat 32))
          ⟨18446744073709551615⟩ = ⟨0⟩ := by
    simpa [calldataWord] using hgt
  have hoffLeMax : (calldataWord I.calldata 4).toNat ≤ 18446744073709551615 := by
    simpa [ABI.solcMaxU64] using Nat.le_of_not_gt hoffMax
  have hoffSmall : (calldataWord I.calldata 4).toNat < 2 ^ 255 := by
    omega
  have hstart31ToNat :
      ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨31⟩).toNat) =
        4 + (calldataWord I.calldata 4).toNat + 31 := by
    have hoffSize : (calldataWord I.calldata 4).toNat < UInt256.size :=
      (calldataWord I.calldata 4).val.isLt
    have hoffOfNat :
        (UInt256.ofNat (calldataWord I.calldata 4).toNat).toNat =
          (calldataWord I.calldata 4).toNat :=
      ulit_toNat' _ hoffSize
    rw [← u256_ofNat_toNat (calldataWord I.calldata 4)]
    simpa [hoffOfNat] using (uadd3_ofNat_toNat (a := 4)
      (b := (calldataWord I.calldata 4).toNat)
      (c := 31)
      (by norm_num [UInt256.size])
      (lt_size_of_lt_sign hoffSmall)
      (by norm_num [UInt256.size])
      (lt_size_of_lt_sign (by omega : 4 + (calldataWord I.calldata 4).toNat < 2 ^ 255))
      (lt_size_of_lt_sign (by omega :
        4 + (calldataWord I.calldata 4).toNat + 31 < 2 ^ 255)))
  have hstart :
      UInt256.slt ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨31⟩))
          (UInt256.ofNat I.calldata.size) = ⟨0⟩ := by
    by_cases hsizeSign : I.calldata.size < 2 ^ 255
    · apply slt_lit_zero hsizeSign
      · rw [hstart31ToNat]
        omega
      · rw [hstart31ToNat]
        omega
    · apply slt_zero_of_left_low_right_high
      · rw [hstart31ToNat]
        omega
      · rw [ulit_toNat' I.calldata.size hsize]
        omega
  have rd2842 := evm_run hdec with [
    jumpdest, push0, push0, push1 ⟨32⟩, dup4, dup6, sub, slt, iszero, push2 ⟨2837⟩,
    jumpiT (by rw [hslt]; decide) (by jump_dest),
    jumpdest, push0, dup4, add, calldataload]
  have rd2851 := RD.pushConst rd2842 ⟨18446744073709551615⟩
    (width := 8) (op := .PUSH8) (by decide) (by native_decide) (by evm_ov)
  have rd2866 := evm_run rd2851 with [
    dup2, gt, iszero, push2 ⟨2866⟩,
    jumpiT (by rw [hgt']; decide) (by jump_dest)]
  have rd2730 := evm_run rd2866 with [
    jumpdest, push2 ⟨2878⟩, dup6, dup3, dup7, add, push2 ⟨2730⟩,
    jump (by jump_dest)]
  exact stringStoreX_stringDecoder2730LengthShort rd2730
    (by simpa [calldataWord] using hstart) (by evm_ov)

theorem decodeCalldata_set_none_headShort {I : ExecutionEnv}
    (hsz : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36) :
    decodeCalldata (setTransition.params.map Param.name)
      (transitionSignature setTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["value"] [.string] I.calldata = none
  unfold decodeCalldata
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  have hlen4 : ¬ I.calldata.toList.length < 4 := by
    omega
  have hnotRead : ¬ 32 ≤ I.calldata.toList.length - 4 := by
    omega
  have hread : ABI.readNat? (I.calldata.toList.drop 4) 0 = none := by
    unfold ABI.readNat? ABI.readWord? ABI.readBytes?
    simp [hnotRead]
  rw [if_neg hlen4]
  have hnotHuge :
      ¬ ([ABIType.string].isEmpty = false ∧ 2 ^ 255 ≤ (I.calldata.toList.drop 4).length) := by
    intro h
    rw [List.length_drop, htlen] at h
    omega
  rw [if_neg hnotHuge]
  change (match decodeCalldata.decodeArgs ["value"] [.string] (I.calldata.toList.drop 4) ∅ with
    | some (store, _) => some store
    | none => none) = none
  simp only [decodeCalldata.decodeArgs, ABI.abiTupleHeadSize?, ABI.decodeABIValues?,
    ABI.isDynamicABIType, hread, bind, Option.bind_none, Option.bind_some, if_true]

theorem decodeCalldata_set_none_offsetHuge {I : ExecutionEnv}
    (hsz36 : 36 ≤ I.calldata.size)
    (hoff : ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat) :
    decodeCalldata (setTransition.params.map Param.name)
      (transitionSignature setTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["value"] [.string] I.calldata = none
  exact decodeCalldata_string_none_offset_huge (x := "value") hsz36 hoff

theorem decodeCalldata_set_none_huge {I : ExecutionEnv}
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) :
    decodeCalldata (setTransition.params.map Param.name)
      (transitionSignature setTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["value"] [.string] I.calldata = none
  exact decodeCalldata_string_none_huge (x := "value") hbig

theorem decodeCalldata_set_none_lengthShort {I : ExecutionEnv}
    (hsz36 : 36 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hshort : I.calldata.size < 4 + (calldataWord I.calldata 4).toNat + 32) :
    decodeCalldata (setTransition.params.map Param.name)
      (transitionSignature setTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["value"] [.string] I.calldata = none
  exact decodeCalldata_string_none_length_short (x := "value") hsz36 hhi hshort

theorem stringStoreSetHeadShortRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = stringStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x4e, 0xd3, 0x88, 0x5e]⟩)
    (_hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36) :
    runtimeEquivalenceFor stringStoreConfig stringStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsel' : ((⟨#[0x4e, 0xd3, 0x88, 0x5e]⟩ : ByteArray) == I.calldata.extract 0 4) =
      true := by
    simpa [selIs] using hsel
  have hd := stringStoreDispatch_set (cd := I.calldata) hsel'
  have hdec := decodeCalldata_set_none_headShort (I := I) hsz hshort
  have hrev := stringStoreX_setDecoderHeadShort
    (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I)
    (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hsel hshort
  exact hrev.reEquivElim hcode fun _ _ hrun => by
    exact reEquiv_decodingFailed hd hdec hrun

theorem stringStoreSetHeadHugeRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = stringStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x4e, 0xd3, 0x88, 0x5e]⟩)
    (_hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz : 4 ≤ I.calldata.size) (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) :
    runtimeEquivalenceFor stringStoreConfig stringStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsel' : ((⟨#[0x4e, 0xd3, 0x88, 0x5e]⟩ : ByteArray) == I.calldata.extract 0 4) =
      true := by
    simpa [selIs] using hsel
  have hd := stringStoreDispatch_set (cd := I.calldata) hsel'
  have hdec := decodeCalldata_set_none_huge (I := I) hbig
  have hrev := stringStoreX_setDecoderHeadHuge
    (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I)
    (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hsel hbig
  exact hrev.reEquivElim hcode fun _ _ hrun => by
    exact reEquiv_decodingFailed hd hdec hrun

theorem stringStoreSetLengthShortRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = stringStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x4e, 0xd3, 0x88, 0x5e]⟩)
    (_hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz36 : 36 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hshort : I.calldata.size < 4 + (calldataWord I.calldata 4).toNat + 32) :
    runtimeEquivalenceFor stringStoreConfig stringStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsel' : ((⟨#[0x4e, 0xd3, 0x88, 0x5e]⟩ : ByteArray) == I.calldata.extract 0 4) =
      true := by
    simpa [selIs] using hsel
  have hd := stringStoreDispatch_set (cd := I.calldata) hsel'
  have hdec := decodeCalldata_set_none_lengthShort (I := I) hsz36 hhi hshort
  have hrev := stringStoreX_setDecoderLengthShort
    (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I)
    (g := Sat256.ofUInt256 g) hcode hwv hsz36 hhi hsize hsel hoffMax hshort
  exact hrev.reEquivElim hcode fun _ _ hrun => by
    exact reEquiv_decodingFailed hd hdec hrun

theorem stringStoreSetOffsetHugeRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = stringStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x4e, 0xd3, 0x88, 0x5e]⟩)
    (_hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz36 : 36 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hoff : ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat) :
    runtimeEquivalenceFor stringStoreConfig stringStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsel' : ((⟨#[0x4e, 0xd3, 0x88, 0x5e]⟩ : ByteArray) == I.calldata.extract 0 4) =
      true := by
    simpa [selIs] using hsel
  have hd := stringStoreDispatch_set (cd := I.calldata) hsel'
  have hdec := decodeCalldata_set_none_offsetHuge (I := I) hsz36 hoff
  have hrev := stringStoreX_setDecoderOffsetHuge
    (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I)
    (g := Sat256.ofUInt256 g) hcode hwv hsz36 hhi hsize hsel hoff
  exact hrev.reEquivElim hcode fun _ _ hrun => by
    exact reEquiv_decodingFailed hd hdec hrun

theorem setBodyReturns {evm evmCurrent evmHistory evmRaw : EVM.State} {value : ByteArray}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hassignCurrent :
      assignStorageRef? stringStoreConfig
        { contract := stringStoreContract
          locals := ((∅ : Store).insert "value" (.bytes value)).insert "copy" (.bytes value) }
        evm .storage currentRef (.bytes value) =
          .ok ({ contract := stringStoreContract
                 locals := ((∅ : Store).insert "value" (.bytes value)).insert "copy" (.bytes value) },
              evmCurrent))
    (hpush :
      pushArray? stringStoreConfig
        { contract := stringStoreContract
          locals := ((∅ : Store).insert "value" (.bytes value)).insert "copy" (.bytes value) }
        evmCurrent historyRef (some (.bytes value)) = .ok evmHistory)
    (hassignRaw :
      assignStorageRef? stringStoreConfig
        { contract := stringStoreContract
          locals := ((∅ : Store).insert "value" (.bytes value)).insert "copy" (.bytes value) }
        evmHistory .storage rawRef (.bytes value) =
          .ok ({ contract := stringStoreContract
                 locals := ((∅ : Store).insert "value" (.bytes value)).insert "copy" (.bytes value) },
              evmRaw)) :
    ExecTransitionBody stringStoreConfig stringStoreContract evm
      ((∅ : Store).insert "value" (.bytes value)) setTransition.body
      (.returned
        { contract := stringStoreContract
          locals := ((∅ : Store).insert "value" (.bytes value)).insert "copy" (.bytes value) }
        evmRaw (some (.int value.size))) := by
  let locals0 : Store := (∅ : Store).insert "value" (.bytes value)
  let locals1 : Store := locals0.insert "copy" (.bytes value)
  let solm0 : Frame := { contract := stringStoreContract, locals := locals0 }
  let solm1 : Frame := { contract := stringStoreContract, locals := locals1 }
  have hvalue : evalExpr? stringStoreConfig solm0 evm (.var "value") = .ok (.bytes value) := by
    simp [solm0, locals0, evalExpr?, EvalResult.ofOption]
  have hcopy : evalExpr? stringStoreConfig solm1 evm (.var "copy") = .ok (.bytes value) := by
    simp [solm1, locals1, locals0, evalExpr?, EvalResult.ofOption]
  have hcopyHistory :
      evalExpr? stringStoreConfig solm1 evmCurrent (.var "copy") = .ok (.bytes value) := by
    simp [solm1, locals1, locals0, evalExpr?, EvalResult.ofOption]
  have hcopyRaw :
      evalExpr? stringStoreConfig solm1 evmHistory (.var "copy") = .ok (.bytes value) := by
    simp [solm1, locals1, locals0, evalExpr?, EvalResult.ofOption]
  have hret :
      evalExpr? stringStoreConfig solm1 evmRaw (.arrayLength .localVar { base := "copy" }) =
        .ok (.int value.size) := by
    simp [solm1, locals1, locals0, evalExpr?, readLocalPath?, EvalResult.bind, bind, pure]
  exact ExecFuncBody.execBlockRet <|
    ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consNormal (ExecStmt.letDecl hvalue) <|
        ExecBlock.consNormal (ExecStmt.assign hcopy (by simpa [solm1, locals1, locals0] using hassignCurrent)) <|
          ExecBlock.consNormal (ExecStmt.pushVal hcopyHistory (by simpa [solm1, locals1, locals0] using hpush)) <|
            ExecBlock.consNormal (ExecStmt.assign hcopyRaw (by simpa [solm1, locals1, locals0] using hassignRaw)) <|
              ExecBlock.consReturn (ExecStmt.return hret)

end StringStore
