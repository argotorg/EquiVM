import Benchmarks.EAS.EAS.Entry

variable {fork : Ethereum.Fork}

/-! # Scalar calldata decoding for the pinned solc 0.8 ABI mode -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

-- LIBRARY CANDIDATE: the two EVM signed-comparison presentations agree.
theorem sltBool_signed (a b : UInt256) :
    UInt256.sltBool a b = decide (EVM.signed a < EVM.signed b) := by
  have haBound := a.val.isLt
  have hbBound := b.val.isLt
  change a.toNat < 2^256 at haBound
  change b.toNat < 2^256 at hbBound
  change (if 2^255 ≤ a.toNat then
      (if 2^255 ≤ b.toNat then decide (a.toNat < b.toNat) else true)
    else (if 2^255 ≤ b.toNat then false else decide (a.toNat < b.toNat))) =
    decide ((if a.toNat < 2^255 then (a.toNat : Int) else (a.toNat : Int) - 2^256) <
      (if b.toNat < 2^255 then (b.toNat : Int) else (b.toNat : Int) - 2^256))
  by_cases ha : a.toNat < 2^255 <;> by_cases hb : b.toNat < 2^255
  · simp only [ha, hb, not_le_of_gt ha, not_le_of_gt hb, if_pos, if_false]
    congr 1
    apply propext
    omega
  · simp only [ha, hb, not_le_of_gt ha, Nat.le_of_not_gt hb, if_pos, if_false]
    rw [decide_eq_false (by omega)]
  · simp only [ha, hb, Nat.le_of_not_gt ha, not_le_of_gt hb, if_pos, if_false]
    rw [decide_eq_true (by omega)]
  · simp only [ha, hb, Nat.le_of_not_gt ha, Nat.le_of_not_gt hb, if_pos, if_false]
    congr 1
    apply propext
    omega

theorem solcSLT_sub4_of_check {size : Nat} {need : UInt256} {bit : Bool}
    (h : UInt256.slt (UInt256.sub (UInt256.ofNat size) ⟨4⟩) need = UInt256.fromBool bit) :
    ABI.Solc08Calldata.solcSLT (ABI.Solc08Calldata.solcSub size 4) need.toNat = bit := by
  unfold ABI.Solc08Calldata.solcSLT ABI.Solc08Calldata.solcSub
  change decide (EVM.signed (UInt256.ofNat (UInt256.sub (UInt256.ofNat size) ⟨4⟩).toNat) <
    EVM.signed (UInt256.ofNat need.toNat)) = bit
  rw [u256_ofNat_toNat, u256_ofNat_toNat, ← sltBool_signed]
  change UInt256.fromBool _ = UInt256.fromBool bit at h
  cases hc : UInt256.sltBool (UInt256.sub (UInt256.ofNat size) ⟨4⟩) need <;>
    cases bit <;> simp_all [UInt256.fromBool, Bool.toUInt256]
  all_goals first
    | exact (by decide : (UInt256.ofNat 0 : UInt256) ≠ UInt256.ofNat 1) h
    | exact (by decide : (UInt256.ofNat 1 : UInt256) ≠ UInt256.ofNat 0) h

abbrev easPlanTable : List (Nat × List CalldataPlan) :=
  Syntax.abiCalldataPlans

def easPlans (selector : Nat) : List CalldataPlan :=
  ((easPlanTable.find? (fun entry => entry.1 == selector)).map Prod.snd).getD []

theorem easPlans_noTopDefer (selector : Nat) :
    ((easPlans selector).headD {}).deferErrors.contains [] = false := by
  simp only [easPlans, easPlanTable, Syntax.abiCalldataPlans, List.find?]
  cases h1 : (1152239886 == selector) <;>
    cases h2 : (1287121381 == selector) <;>
    cases h3 : (2199782817 == selector) <;>
    cases h4 : (3831301113 == selector) <;>
    cases h5 : (4050855399 == selector) <;>
    rfl

theorem easDecodeScalar_none_check {cd : ByteArray} (name : Ident) (ty : ElemType)
    (h4 : 4 ≤ cd.size)
    (hcheck : ABI.Solc08Calldata.solcSLT (ABI.Solc08Calldata.solcSub cd.size 4) 32 = true) :
    config.externalABI.decodeCalldata? [name] [.elem ty] cd = none := by
  have hlen : cd.toList.length = cd.size := by rw [byteArray_toList_eq, Array.length_toList]; rfl
  simp only [decodeCalldataWithMode, decodeCalldata, hlen, show ¬ cd.size < 4 by omega,
    if_false, List.any_cons, List.any_nil, isDynamicABIType, Bool.false_or, Bool.false_eq_true,
    false_and, config, ExternalCallABI.withMode, Syntax.abiDecodeMode,
    ABI.Solc08Calldata.decodeArgs?, List.isEmpty_cons,
    Bool.false_eq_true, abiTupleHeadSize?, staticABIEncodedSize?, bind, Option.bind,
    hcheck, if_true]

theorem easDecodeScalar_eq {cd : ByteArray} (name : Ident) (ty : ElemType)
    (h36 : 36 ≤ cd.size)
    (hcheck : ABI.Solc08Calldata.solcSLT (ABI.Solc08Calldata.solcSub cd.size 4) 32 = false) :
    config.externalABI.decodeCalldata? [name] [.elem ty] cd =
      (decodeABIValue? (.elem ty) ((cd.toList.drop 4).take 32) 0).map
        (fun value => (∅ : Store).insert name value.1) := by
  have hlen : cd.toList.length = cd.size := by rw [byteArray_toList_eq, Array.length_toList]; rfl
  have htake : ((cd.toList.drop 4).take 32).length = 32 := by
    simp only [List.length_take, List.length_drop, hlen]; omega
  have hread : ABI.Solc08Calldata.solcReadBytes cd.toList 4 32 = (cd.toList.drop 4).take 32 := by
    simp only [ABI.Solc08Calldata.solcReadBytes,
      show 4 % EVM.wordModulus = 4 from rfl, htake, Nat.sub_self, List.replicate_zero, List.append_nil]
  simp only [decodeCalldataWithMode, decodeCalldata, hlen, show ¬ cd.size < 4 by omega,
    if_false, List.any_cons, List.any_nil, isDynamicABIType, Bool.false_or, Bool.false_eq_true,
    false_and, config, ExternalCallABI.withMode, Syntax.abiDecodeMode,
    ABI.Solc08Calldata.decodeArgs?, List.isEmpty_cons,
    abiTupleHeadSize?, staticABIEncodedSize?, bind, Option.bind, hcheck,
    ABI.Solc08Calldata.decodeFields?, ABI.Solc08Calldata.stride?]
  have hdefer := easPlans_noTopDefer (ABI.bytesToWord (cd.toList.take 4)).toNat
  simp only [easPlans, easPlanTable, config, Syntax.abiDecodeMode] at hdefer
  simp only [ABI.Solc08Calldata.retainFailure]
  rw [hdefer]
  simp only [Bool.false_eq_true, if_false, ABI.Solc08Calldata.decodeValue?,
    show ABI.Solc08Calldata.solcAdd 4 0 = 4 from rfl, hread]
  cases decodeABIValue? (.elem ty) ((cd.toList.drop 4).take 32) 0 <;> rfl

theorem easDecodeScalar_none_short {cd : ByteArray} (name : Ident) (ty : ElemType)
    (h4 : 4 ≤ cd.size) (hshort : cd.size < 36) (hsize : cd.size < UInt256.size) :
    config.externalABI.decodeCalldata? [name] [.elem ty] cd = none :=
  easDecodeScalar_none_check name ty h4
    (solcSLT_sub4_of_check (need := ⟨32⟩) (bit := true)
      (solcDecodeLenCheckShort_4_32 h4 hshort hsize))

theorem easDecodeScalar_none_huge {cd : ByteArray} (name : Ident) (ty : ElemType)
    (hbig : 2^255 + 4 ≤ cd.size) (hsize : cd.size < UInt256.size) :
    config.externalABI.decodeCalldata? [name] [.elem ty] cd = none :=
  easDecodeScalar_none_check name ty (by omega)
    (solcSLT_sub4_of_check (need := ⟨32⟩) (bit := true)
      (solcDecodeLenCheckHuge_4_32 hbig hsize))

theorem easDecodeAddress_ok {cd : ByteArray} (name : Ident)
    (h36 : 36 ≤ cd.size) (hbig : cd.size < 2^255 + 4) (hsize : cd.size < UInt256.size)
    (hcanon : (calldataWord cd 4).toNat < EVM.addressModulus) :
    config.externalABI.decodeCalldata? [name] [.elem .address] cd =
      some ((∅ : Store).insert name (.address (AccountAddress.ofNat (calldataWord cd 4).toNat))) := by
  rw [easDecodeScalar_eq name .address h36
    (solcSLT_sub4_of_check (need := ⟨32⟩) (bit := false)
      (solcDecodeLenCheckOk_4_32 h36 hbig hsize))]
  have hlen : cd.toList.length = cd.size := by rw [byteArray_toList_eq, Array.length_toList]; rfl
  have htake : ((cd.toList.drop 4).take 32).length = 32 := by
    simp only [List.length_take, List.length_drop, hlen]; omega
  have hword := decode_word_at_eq cd 4 (by omega : 4 + 32 ≤ cd.size) (by decide : 4 < 2^64)
  rw [decodeABIValue_address_ok
    (by simpa only [List.drop_zero, List.take_take, Nat.min_self] using htake)
    (by simpa only [List.drop_zero, List.take_take, Nat.min_self, hword] using hcanon)]
  simp only [Option.map, List.drop_zero, List.take_take, Nat.min_self, hword]

theorem easDecodeAddress_none_noncanon {cd : ByteArray} (name : Ident)
    (h36 : 36 ≤ cd.size) (hbig : cd.size < 2^255 + 4) (hsize : cd.size < UInt256.size)
    (hcanon : ¬ (calldataWord cd 4).toNat < EVM.addressModulus) :
    config.externalABI.decodeCalldata? [name] [.elem .address] cd = none := by
  rw [easDecodeScalar_eq name .address h36
    (solcSLT_sub4_of_check (need := ⟨32⟩) (bit := false)
      (solcDecodeLenCheckOk_4_32 h36 hbig hsize))]
  have hlen : cd.toList.length = cd.size := by rw [byteArray_toList_eq, Array.length_toList]; rfl
  have htake : ((cd.toList.drop 4).take 32).length = 32 := by
    simp only [List.length_take, List.length_drop, hlen]; omega
  have hword := decode_word_at_eq cd 4 (by omega : 4 + 32 ≤ cd.size) (by decide : 4 < 2^64)
  rw [decodeABIValue_address_none_noncanon
    (by simpa only [List.drop_zero, List.take_take, Nat.min_self] using htake)
    (by simpa only [List.drop_zero, List.take_take, Nat.min_self, hword] using hcanon)]
  rfl

theorem easDecodeAddressEVM_ok {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {ret : UInt256} {R : List UInt256} (v : EASImmutables)
    (hstack : R.length + 4 ≤ 1024)
    (hcanon : (calldataWord ee.calldata 4).toNat < EVM.addressModulus)
    (hvalid : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨4274⟩ (ret :: R) mem aw rdata σ k C) :
    ∃ k' C', RD fork (deployedRuntime v) ee g s0 ret (calldataWord ee.calldata 4 :: R)
      mem aw rdata σ k' C' := by
  have rd1 := easBlocks.eas_block_4274_fallthrough (immWords := wordsOf (immStore v)) hstack
    (by change UInt256.sub (calldataWord ee.calldata 4)
          (UInt256.land (calldataWord ee.calldata 4) solcAddrMask) = ⟨0⟩
        rw [solcAddrMask_clean hcanon, u256_sub_self]) rd
  have rd2 := easBlocks.eas_block_4308 (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega) hvalid rd1
  exact ⟨_, _, rd2⟩

theorem easDecodeAddressEVM_revert {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {ret : UInt256} {R : List UInt256} (v : EASImmutables)
    (hstack : R.length + 4 ≤ 1024)
    (hcanon : ¬ (calldataWord ee.calldata 4).toNat < EVM.addressModulus)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨4274⟩ (ret :: R) mem aw rdata σ k C) :
    RDrev fork (deployedRuntime v) g s0 := by
  have hmask : calldataWord ee.calldata 4 ≠ UInt256.land (calldataWord ee.calldata 4) solcAddrMask := by
    intro heq
    exact hcanon (heq ▸ solcAddrMask_result_canonical (calldataWord ee.calldata 4))
  have rd1 := easBlocks.eas_block_4274_taken (immWords := wordsOf (immStore v)) hstack
    (u256_sub_ne_zero_of_ne hmask)
    (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
  exact easBlocks.eas_block_402 (immWords := wordsOf (immStore v))
    (by simp only [easBlocks.eas_block_4274_taken_stack, List.length_cons]; omega) rd1

theorem easCalldataSub4 {cd : ByteArray} (hsz : 4 ≤ cd.size)
    (hsize : cd.size < UInt256.size) :
    UInt256.ofNat cd.size + UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639932 =
      UInt256.sub (UInt256.ofNat cd.size) (UInt256.ofNat 4) := by
  change UInt256.ofNat cd.size + UInt256.ofNat (UInt256.size - 4) = _
  rw [easCalldataRemainder hsz hsize]
  apply u256_inj
  rw [usub_ofNat_lit_toNat hsz hsize, ulit_toNat' _ (by omega)]

theorem easDecodeBytes32_ok {cd : ByteArray} (name : Ident)
    (h36 : 36 ≤ cd.size) (hbig : cd.size < 2^255 + 4) (hsize : cd.size < UInt256.size) :
    config.externalABI.decodeCalldata? [name] [abiBytes32] cd =
      some ((∅ : Store).insert name
        (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE (calldataWord cd 4)))) := by
  rw [easDecodeScalar_eq name (.bytes abiBytes32Width) h36
    (solcSLT_sub4_of_check (need := ⟨32⟩) (bit := false)
      (solcDecodeLenCheckOk_4_32 h36 hbig hsize))]
  have hlen : cd.toList.length = cd.size := by rw [byteArray_toList_eq, Array.length_toList]; rfl
  have htake : ((cd.toList.drop 4).take 32).length = 32 := by
    simp only [List.length_take, List.length_drop, hlen]; omega
  rw [decodeABIValue_bytes32_ok
    (by simpa only [List.drop_zero, List.take_take, Nat.min_self] using htake)]
  simp only [Option.map, List.drop_zero, List.take_take, Nat.min_self]
  have hword : ABI.bytesToWord ((cd.toList.drop 4).take 32) = calldataWord cd 4 :=
    decode_word_at_eq cd 4 (by omega) (by decide)
  rw [← hword, toBytesBE_bytesToWord_of_length htake]

theorem easPlans_tail_nil (selector : Nat) : (easPlans selector).tail = [] := by
  simp only [easPlans, easPlanTable, Syntax.abiCalldataPlans, List.find?]
  cases h1 : (1152239886 == selector) <;>
    cases h2 : (1287121381 == selector) <;>
    cases h3 : (2199782817 == selector) <;>
    cases h4 : (3831301113 == selector) <;>
    cases h5 : (4050855399 == selector) <;> rfl

theorem easDecodePair_none_check {cd : ByteArray} (x y : Ident) (t u : ElemType)
    (h4 : 4 ≤ cd.size)
    (hcheck : ABI.Solc08Calldata.solcSLT (ABI.Solc08Calldata.solcSub cd.size 4) 64 = true) :
    config.externalABI.decodeCalldata? [x, y] [.elem t, .elem u] cd = none := by
  have hlen : cd.toList.length = cd.size := by rw [byteArray_toList_eq, Array.length_toList]; rfl
  simp only [decodeCalldataWithMode, decodeCalldata, hlen, show ¬ cd.size < 4 by omega,
    if_false, List.any_cons, List.any_nil, isDynamicABIType, Bool.false_or, Bool.false_eq_true,
    false_and, config, ExternalCallABI.withMode, Syntax.abiDecodeMode,
    ABI.Solc08Calldata.decodeArgs?, List.isEmpty_cons,
    abiTupleHeadSize?, staticABIEncodedSize?, bind, Option.bind,
    show (32 : Nat) + 32 = 64 from rfl, hcheck, if_true]

theorem easDecodePair_eq {cd : ByteArray} (x y : Ident) (t u : ElemType)
    (h68 : 68 ≤ cd.size)
    (hcheck : ABI.Solc08Calldata.solcSLT (ABI.Solc08Calldata.solcSub cd.size 4) 64 = false) :
    config.externalABI.decodeCalldata? [x, y] [.elem t, .elem u] cd =
      (decodeABIValue? (.elem t) ((cd.toList.drop 4).take 32) 0).bind (fun a =>
        (decodeABIValue? (.elem u) ((cd.toList.drop 36).take 32) 0).map (fun b =>
          ((∅ : Store).insert x a.1).insert y b.1)) := by
  have hlen : cd.toList.length = cd.size := by rw [byteArray_toList_eq, Array.length_toList]; rfl
  have hread (offset : Nat) (hbound : offset + 32 ≤ cd.size) (hoff : offset < EVM.wordModulus) :
      ABI.Solc08Calldata.solcReadBytes cd.toList offset 32 = (cd.toList.drop offset).take 32 := by
    have ht : ((cd.toList.drop offset).take 32).length = 32 := by
      simp only [List.length_take, List.length_drop, hlen]; omega
    simp only [ABI.Solc08Calldata.solcReadBytes, Nat.mod_eq_of_lt hoff,
      ht, Nat.sub_self, List.replicate_zero, List.append_nil]
  have hread4 := hread 4 (by omega) (by decide)
  have hread36 := hread 36 h68 (by decide)
  simp only [decodeCalldataWithMode, decodeCalldata, hlen, show ¬ cd.size < 4 by omega,
    if_false, List.any_cons, List.any_nil, isDynamicABIType, Bool.false_or, Bool.false_eq_true,
    false_and, config, ExternalCallABI.withMode, Syntax.abiDecodeMode,
    ABI.Solc08Calldata.decodeArgs?, List.isEmpty_cons,
    abiTupleHeadSize?, staticABIEncodedSize?, bind, Option.bind,
    show (32 : Nat) + 32 = 64 from rfl, hcheck,
    ABI.Solc08Calldata.decodeFields?, ABI.Solc08Calldata.stride?]
  have hdefer := easPlans_noTopDefer (ABI.bytesToWord (cd.toList.take 4)).toNat
  have htail := easPlans_tail_nil (ABI.bytesToWord (cd.toList.take 4)).toNat
  simp only [easPlans, easPlanTable, config, Syntax.abiDecodeMode] at hdefer htail
  rw [htail]
  simp only [ABI.Solc08Calldata.retainFailure]
  rw [hdefer]
  simp only [Bool.false_eq_true, if_false, List.headD_nil,
    show ({} : CalldataPlan).deferErrors.contains [] = false from rfl,
    ABI.Solc08Calldata.decodeValue?,
    show ABI.Solc08Calldata.solcAdd 4 0 = 4 from rfl,
    show ABI.Solc08Calldata.solcAdd 4 (0 + 32) = 36 from rfl,
    hread4, hread36]
  cases decodeABIValue? (.elem t) ((cd.toList.drop 4).take 32) 0 <;>
    cases decodeABIValue? (.elem u) ((cd.toList.drop 36).take 32) 0 <;> rfl

theorem easDecodePair_none_short {cd : ByteArray} (x y : Ident) (t u : ElemType)
    (h4 : 4 ≤ cd.size) (hshort : cd.size < 68) (hsize : cd.size < UInt256.size) :
    config.externalABI.decodeCalldata? [x, y] [.elem t, .elem u] cd = none :=
  easDecodePair_none_check x y t u h4
    (solcSLT_sub4_of_check (need := ⟨64⟩) (bit := true)
      (solcDecodeLenCheckShort_4_64 h4 hshort hsize))

theorem easDecodePair_none_huge {cd : ByteArray} (x y : Ident) (t u : ElemType)
    (hbig : 2^255 + 4 ≤ cd.size) (hsize : cd.size < UInt256.size) :
    config.externalABI.decodeCalldata? [x, y] [.elem t, .elem u] cd = none :=
  easDecodePair_none_check x y t u (by omega)
    (solcSLT_sub4_of_check (need := ⟨64⟩) (bit := true)
      (solcDecodeLenCheckHuge_4_64 hbig hsize))

theorem easDecodeAddressBytes32_ok {cd : ByteArray} (x y : Ident)
    (h68 : 68 ≤ cd.size) (hbig : cd.size < 2^255 + 4) (hsize : cd.size < UInt256.size)
    (hcanon : (calldataWord cd 4).toNat < EVM.addressModulus) :
    config.externalABI.decodeCalldata? [x, y] [.elem .address, abiBytes32] cd =
      some (((∅ : Store).insert x (.address (AccountAddress.ofNat (calldataWord cd 4).toNat))).insert y
        (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE (calldataWord cd 36)))) := by
  rw [easDecodePair_eq x y .address (.bytes abiBytes32Width) h68
    (solcSLT_sub4_of_check (need := ⟨64⟩) (bit := false)
      (solcDecodeLenCheckOk_4_64 h68 hbig hsize))]
  have hlen : cd.toList.length = cd.size := by rw [byteArray_toList_eq, Array.length_toList]; rfl
  have htake (off : Nat) (hb : off + 32 ≤ cd.size) : ((cd.toList.drop off).take 32).length = 32 := by
    simp only [List.length_take, List.length_drop, hlen]; omega
  have hword4 : ABI.bytesToWord ((cd.toList.drop 4).take 32) = calldataWord cd 4 :=
    decode_word_at_eq cd 4 (by omega) (by decide)
  have hword36 : ABI.bytesToWord ((cd.toList.drop 36).take 32) = calldataWord cd 36 :=
    decode_word_at_eq cd 36 h68 (by decide)
  rw [decodeABIValue_address_ok
    (by simpa only [List.drop_zero, List.take_take, Nat.min_self] using htake 4 (by omega))
    (by simpa only [List.drop_zero, List.take_take, Nat.min_self, hword4] using hcanon)]
  simp only [Option.bind]
  rw [decodeABIValue_bytes32_ok
    (by simpa only [List.drop_zero, List.take_take, Nat.min_self] using htake 36 h68)]
  simp only [Option.map, List.drop_zero, List.take_take, Nat.min_self, hword4]
  rw [← hword36, toBytesBE_bytesToWord_of_length (htake 36 h68)]

theorem easDecodeAddressBytes32_none_noncanon {cd : ByteArray} (x y : Ident)
    (h68 : 68 ≤ cd.size) (hbig : cd.size < 2^255 + 4) (hsize : cd.size < UInt256.size)
    (hcanon : ¬ (calldataWord cd 4).toNat < EVM.addressModulus) :
    config.externalABI.decodeCalldata? [x, y] [.elem .address, abiBytes32] cd = none := by
  rw [easDecodePair_eq x y .address (.bytes abiBytes32Width) h68
    (solcSLT_sub4_of_check (need := ⟨64⟩) (bit := false)
      (solcDecodeLenCheckOk_4_64 h68 hbig hsize))]
  have hlen : cd.toList.length = cd.size := by rw [byteArray_toList_eq, Array.length_toList]; rfl
  have htake : ((cd.toList.drop 4).take 32).length = 32 := by
    simp only [List.length_take, List.length_drop, hlen]; omega
  have hword : ABI.bytesToWord ((cd.toList.drop 4).take 32) = calldataWord cd 4 :=
    decode_word_at_eq cd 4 (by omega) (by decide)
  rw [decodeABIValue_address_none_noncanon
    (by simpa only [List.drop_zero, List.take_take, Nat.min_self] using htake)
    (by simpa only [List.drop_zero, List.take_take, Nat.min_self, hword] using hcanon)]
  rfl

end Benchmarks.EAS.EAS
