import Benchmarks.Dss.ExponentialDecrease.PriceSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.ExponentialDecrease

-- LIBRARY CANDIDATE: legacy solc05 decoding for `(uint256,uint256)`.
theorem stairstepDecodeABIValues_uint256_uint256_legacy_ok {bytes : List UInt8}
    (hlen0 : (bytes.take 32).length = 32)
    (hlen32 : ((bytes.drop 32).take 32).length = 32) :
    decodeABIValues? [abiUInt256, abiUInt256] bytes 0 0 64 64 DecodeMode.legacySolc05 =
      some ([.int (Int.ofNat (ABI.bytesToWord (bytes.take 32)).toNat),
        .int (Int.ofNat (ABI.bytesToWord ((bytes.drop 32).take 32)).toNat)], 64) := by
  have hread32 : 32 ≤ bytes.length - 32 := by
    rw [List.length_take, List.length_drop] at hlen32
    omega
  have hmod0 :
      (Int.ofNat (ABI.bytesToWord (bytes.take 32)).val % Int.ofNat (EVM.twoPow 256)) =
        Int.ofNat (UInt256.toNat (ABI.bytesToWord (bytes.take 32))) := by
    rw [Int.emod_eq_of_lt]
    · simp [UInt256.toNat]
    · exact Int.natCast_nonneg _
    · have hlt : (ABI.bytesToWord (bytes.take 32)).val < EVM.twoPow 256 := by
        simpa [EVM.twoPow, UInt256.size] using (ABI.bytesToWord (bytes.take 32)).val.isLt
      exact Int.ofNat_lt.mpr hlt
  have hmod32 :
      (Int.ofNat (ABI.bytesToWord ((bytes.drop 32).take 32)).val %
          Int.ofNat (EVM.twoPow 256)) =
        Int.ofNat (UInt256.toNat (ABI.bytesToWord ((bytes.drop 32).take 32))) := by
    rw [Int.emod_eq_of_lt]
    · simp [UInt256.toNat]
    · exact Int.natCast_nonneg _
    · have hlt : (ABI.bytesToWord ((bytes.drop 32).take 32)).val < EVM.twoPow 256 := by
        simpa [EVM.twoPow, UInt256.size] using
          (ABI.bytesToWord ((bytes.drop 32).take 32)).val.isLt
      exact Int.ofNat_lt.mpr hlt
  simp [decodeABIValues?, abiUInt256, isDynamicABIType, staticABIEncodedSize?,
    decodeABIValue?, readWord?, readBytes?, decodeABIWord?, hlen0, hread32]
  exact ⟨hmod0, hmod32⟩

-- LIBRARY CANDIDATE: legacy solc05 short-calldata rejection for `(uint256,uint256)`.
theorem stairstepDecodeABIValues_uint256_uint256_legacy_none_short {bytes : List UInt8}
    (hshort : bytes.length < 64) :
    decodeABIValues? [abiUInt256, abiUInt256] bytes 0 0 64 64 DecodeMode.legacySolc05 =
      none := by
  simp only [decodeABIValues?, abiUInt256, isDynamicABIType, Bool.false_eq_true, if_false,
    staticABIEncodedSize?, bind, Option.bind, Nat.zero_add]
  by_cases h32 : bytes.length < 32
  · have hnot : ¬ 32 ≤ bytes.length := by omega
    simp [decodeABIValue?, readWord?, readBytes?, hnot]
  · have htake0 : (bytes.take 32).length = 32 := by
      rw [List.length_take]
      omega
    have hnot : ¬ 32 ≤ bytes.length - 32 := by
      omega
    simp [decodeABIValue?, readWord?, readBytes?, decodeABIWord?, htake0, hnot]

theorem stairstepDecodeCalldata_legacyUInt256_uint256_ok {cd : ByteArray}
    {x y : Solm.Ident} (hsz68 : 68 ≤ cd.size) :
    decodeCalldataWithMode DecodeMode.legacySolc05 [x, y] [abiUInt256, abiUInt256] cd =
      some (((∅ : Solm.Store).insert x
        (.int (Int.ofNat (calldataWord cd 4).toNat))).insert y
        (.int (Int.ofNat (calldataWord cd 36).toNat))) := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have htake4 : ((cd.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have htake36 : ((cd.toList.drop 36).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have hword4 : ABI.bytesToWord ((cd.toList.drop 4).take 32) = calldataWord cd 4 :=
    decode_word_at_eq cd 4 (by omega) (by norm_num)
  have hword36 : ABI.bytesToWord ((cd.toList.drop 36).take 32) = calldataWord cd 36 :=
    decode_word_at_eq cd 36 (by omega) (by norm_num)
  unfold decodeCalldataWithMode decodeCalldata
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_neg (by simp [abiUInt256, isDynamicABIType])]
  simp only [decodeCalldata.decodeArgs]
  rw [show abiTupleHeadSize? [abiUInt256, abiUInt256] = some 64 by native_decide]
  simp only [bind, Option.bind]
  rw [stairstepDecodeABIValues_uint256_uint256_legacy_ok (bytes := cd.toList.drop 4)
    (by simpa using htake4)
    (by simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using htake36)]
  rw [if_neg (by rw [List.length_drop, htlen]; omega :
    ¬ (cd.toList.drop 4).length < 64)]
  simp [decodeCalldata.insertValues]
  rw [hword4, hword36]

theorem stairstepDecodeCalldata_legacyUInt256_uint256_none_short {cd : ByteArray}
    {x y : Solm.Ident} (hsz4 : 4 ≤ cd.size) (hshort : cd.size < 68) :
    decodeCalldataWithMode DecodeMode.legacySolc05 [x, y] [abiUInt256, abiUInt256] cd =
      none := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  unfold decodeCalldataWithMode decodeCalldata
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_neg (by simp [abiUInt256, isDynamicABIType])]
  simp only [decodeCalldata.decodeArgs]
  rw [show abiTupleHeadSize? [abiUInt256, abiUInt256] = some 64 by native_decide]
  simp only [bind, Option.bind]
  by_cases hbytes : (cd.toList.drop 4).length < 64
  · rw [if_pos hbytes]
  · rw [if_neg hbytes]
    rw [stairstepDecodeABIValues_uint256_uint256_legacy_none_short
      (bytes := cd.toList.drop 4) (by
        rw [List.length_drop, htlen]
        omega)]

theorem stairstepDecode_price_ok {I : ExecutionEnv} (hsz68 : 68 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (priceTransition.params.map Param.name)
      (transitionSignature priceTransition).paramTypes I.calldata =
        some (priceLocals I) := by
  simpa [config, priceTransition, uint256, uint256Int, priceLocals, priceTop, priceDur,
    abiUInt256] using
    (stairstepDecodeCalldata_legacyUInt256_uint256_ok (cd := I.calldata) (x := "top")
      (y := "dur") hsz68)

theorem stairstepDecode_price_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 68) :
    decodeCalldataWithMode config.abiDecodeMode (priceTransition.params.map Param.name)
      (transitionSignature priceTransition).paramTypes I.calldata = none := by
  simpa [config, priceTransition, uint256, uint256Int, abiUInt256] using
    (stairstepDecodeCalldata_legacyUInt256_uint256_none_short (cd := I.calldata)
      (x := "top") (y := "dur") hsz4 hshort)

theorem stairstepReachPriceBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = exponentialDecreaseBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (stairstepSelBytes 3)) :
    ∃ k C, RD exponentialDecreaseBytecode I g
        (initState cA gh bl σ σ₀ g A I)
        stairstepPriceEntryPc [stairstepSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
  have hword : stairstepSelWord I = ⟨0x487a2395⟩ :=
    stairstepSelWord_eq_of_beq I hsz 0x48 0x7a 0x23 0x95 ⟨0x487a2395⟩
      (by native_decide) (by simpa [stairstepSelBytes] using hsel)
  have heq0 : ∀ j, j < 1 →
      UInt256.eq
        (armSelNat exponentialDecreaseBytecode
          (nthArmPc exponentialDecreaseBytecode stairstepFirstArmPc j))
        (stairstepSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j
    rw [hword]
    native_decide
  have htake :
      UInt256.eq
        (armSelNat exponentialDecreaseBytecode
          (nthArmPc exponentialDecreaseBytecode stairstepFirstArmPc 1))
        (stairstepSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  exact stairstepReachBody 1 (by omega) stairstepPriceEntryPc hcode hwv hsz hsize
    heq0 htake (by jump_dest) (by native_decide)

theorem RD.stairstepPriceDecodeToRoutine {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {sel de : UInt256}
    (h : RD exponentialDecreaseBytecode I g s0 ⟨162⟩
      (de :: ⟨4⟩ :: ⟨175⟩ :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD exponentialDecreaseBytecode I g s0 ⟨627⟩
      [priceDur I, priceTop I, ⟨175⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have rd665 := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw calldataload (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw calldataload (by native_decide) (by evm_ov),
    raw push2 ⟨627⟩ (by native_decide) (by evm_ov),
    raw jump (by native_decide) (by jump_dest) (by evm_ov)]
  exact ⟨_, _, by simpa [priceDur, priceTop, calldataWord] using rd665⟩

theorem stairstepPriceX_decoded {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD exponentialDecreaseBytecode I g
      (initState cA gh bl σ σ₀ g A I) stairstepPriceEntryPc [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD exponentialDecreaseBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨627⟩
        [priceDur I, priceTop I, ⟨175⟩, sel]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, hdecoded⟩ := RD.solcTwoAddressExternalLenOk
    (code := exponentialDecreaseBytecode) (sel := sel)
    (entry := stairstepPriceEntryPc) (ret := ⟨175⟩) (decoded := ⟨162⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by jump_dest) hsz68 hsize
  exact RD.stairstepPriceDecodeToRoutine hdecoded

theorem stairstepPriceX_shortarg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 68)
    (hreach : ∃ k C, RD exponentialDecreaseBytecode I g
      (initState cA gh bl σ σ₀ g A I) stairstepPriceEntryPc [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev exponentialDecreaseBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨1⟩ := by
    apply ult_one
    rw [usub_ofNat_word_toNat (by simpa using hsz4) hsize]
    change I.calldata.size - 4 < 64
    omega
  exact RD.solcExternalStaticArgsShortReverts
    (code := exponentialDecreaseBytecode) (sel := sel)
    (entry := stairstepPriceEntryPc) (ret := ⟨175⟩) (decoded := ⟨162⟩)
    (need := ⟨64⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) hlt

set_option maxHeartbeats 1000000 in
theorem stairstepPriceToRpow {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {sel : UInt256}
    (h : RD exponentialDecreaseBytecode I g s0 ⟨627⟩
      [priceDur I, priceTop I, ⟨175⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD exponentialDecreaseBytecode I g s0 ⟨987⟩
      (stairstepRay :: priceN σ I :: priceCutWord σ I :: ⟨658⟩ :: priceTop I ::
        ⟨663⟩ :: ⟨0⟩ :: priceDur I :: priceTop I :: ⟨175⟩ :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have rd654pre := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw push2 ⟨663⟩ (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw push2 ⟨658⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov)]
  obtain ⟨k640, C640, rd640raw⟩ := rd654pre.sload (by native_decide) (by evm_ov)
  have rd640 : RD exponentialDecreaseBytecode I g s0 ⟨640⟩
      (priceCutWord σ I :: ⟨658⟩ :: priceTop I :: ⟨663⟩ :: ⟨0⟩ ::
        priceDur I :: priceTop I :: ⟨175⟩ :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k640 C640 := by
    simpa [priceCutWord, stairstepSlotWord] using rd640raw
  have rd641 := evm_run rd640 with [
    raw dup6 (by native_decide) (by evm_ov)]
  have rd654 := rd641.pushConst stairstepRay
    (width := 12) (op := .PUSH12) (by decide) (by native_decide) (by evm_ov)
  have rd987pre := evm_run rd654 with [
    raw push2 ⟨987⟩ (by native_decide) (by evm_ov)]
  have rd987 := rd987pre.jump (by native_decide) (by jump_dest) (by evm_ov)
  exact ⟨_, _, by simpa [stairstepRay, priceN] using rd987⟩

set_option maxHeartbeats 1000000 in
theorem stairstepPriceRpowNZero_toRmul {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {sel : UInt256}
    (h : RD exponentialDecreaseBytecode I g s0 ⟨987⟩
      (stairstepRay :: ⟨0⟩ :: priceCutWord σ I :: ⟨658⟩ :: priceTop I ::
        ⟨663⟩ :: ⟨0⟩ :: priceDur I :: priceTop I :: ⟨175⟩ :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD exponentialDecreaseBytecode I g s0 ⟨658⟩
      (stairstepRay :: priceTop I :: ⟨663⟩ :: ⟨0⟩ :: priceDur I ::
        priceTop I :: ⟨175⟩ :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have rd1051pre := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw iszero (by native_decide) (by evm_ov),
    raw push2 ⟨1165⟩ (by native_decide) (by evm_ov)]
  have hnZero : UInt256.isZero (⟨0⟩ : UInt256) ≠ ⟨0⟩ := by decide
  have rd1165 := rd1051pre.jumpiT (by native_decide) hnZero (by jump_dest) (by evm_ov)
  have rd1169pre := evm_run rd1165 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw jumpdest (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw swap4 (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov)]
  exact ⟨_, _, by simpa [stairstepRay] using
    rd1169pre.jump (by native_decide) (by jump_dest) (by evm_ov)⟩

theorem stairstepPriceRpowXZeroNNonzero_toRmul {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {sel : UInt256}
    (hn : priceN σ I ≠ ⟨0⟩)
    (hcut : priceCutWord σ I = ⟨0⟩)
    (h : RD exponentialDecreaseBytecode I g s0 ⟨987⟩
      (stairstepRay :: priceN σ I :: priceCutWord σ I :: ⟨658⟩ :: priceTop I ::
        ⟨663⟩ :: ⟨0⟩ :: priceDur I :: priceTop I :: ⟨175⟩ :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD exponentialDecreaseBytecode I g s0 ⟨658⟩
      (⟨0⟩ :: priceTop I :: ⟨663⟩ :: ⟨0⟩ :: priceDur I ::
        priceTop I :: ⟨175⟩ :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  exact RD.stairstepRpowXZeroNNonzeroReturns
    (R := priceTop I :: ⟨663⟩ :: ⟨0⟩ :: priceDur I :: priceTop I :: ⟨175⟩ :: [sel])
    (by simp) hn (by simpa [hcut] using h)

set_option maxHeartbeats 1000000 in
theorem stairstepPriceRpowReturnToRmul {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {sel pow : UInt256}
    (h : RD exponentialDecreaseBytecode I g s0 ⟨658⟩
      (pow :: priceTop I :: ⟨663⟩ :: ⟨0⟩ :: priceDur I ::
        priceTop I :: ⟨175⟩ :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD exponentialDecreaseBytecode I g s0 ⟨1177⟩
      (pow :: priceTop I :: ⟨663⟩ :: ⟨0⟩ :: priceDur I ::
        priceTop I :: ⟨175⟩ :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have rd1232pre := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push2 ⟨1177⟩ (by native_decide) (by evm_ov)]
  exact ⟨_, _, rd1232pre.jump (by native_decide) (by jump_dest) (by evm_ov)⟩

set_option maxHeartbeats 1000000 in
theorem stairstepPriceRmulRayReturns {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {sel : UInt256}
    (hfit : stairstepRay.toNat * (priceTop I).toNat < UInt256.size)
    (h : RD exponentialDecreaseBytecode I g s0 ⟨1177⟩
      (stairstepRay :: priceTop I :: ⟨663⟩ :: ⟨0⟩ :: priceDur I ::
        priceTop I :: ⟨175⟩ :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD exponentialDecreaseBytecode I g s0 ⟨663⟩
      (priceTop I :: ⟨0⟩ :: priceDur I :: priceTop I :: ⟨175⟩ :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  let prod := stairstepRay * priceTop I
  have rd1242pre := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw mul (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw iszero (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw push2 ⟨1201⟩ (by native_decide) (by evm_ov)]
  have hRayNonzero : UInt256.isZero stairstepRay = ⟨0⟩ := by native_decide
  have rd1243 := rd1242pre.jumpiNT (by native_decide) hRayNonzero (by evm_ov)
  have rd1253pre := evm_run rd1243 with [
    raw pop (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw push2 ⟨1198⟩ (by native_decide) (by evm_ov)]
  have rd1253 := rd1253pre.jumpiT (by native_decide)
    (by native_decide : stairstepRay ≠ ⟨0⟩) (by jump_dest) (by evm_ov)
  have hdiv : UInt256.div prod stairstepRay = priceTop I := by
    simpa [prod] using stairstepRay_mul_div_cancel (priceTop I) hfit
  have hdiv' :
      UInt256.div (UInt256.mul stairstepRay (priceTop I)) stairstepRay = priceTop I := by
    simpa [prod, HMul.hMul, Mul.mul] using hdiv
  have rd1256pre := evm_run rd1253 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw div (by native_decide) (by evm_ov),
    raw eq (by native_decide) (by evm_ov)]
  rw [hdiv', u256_eq_refl] at rd1256pre
  have rd1265pre := evm_run rd1256pre with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push2 ⟨1210⟩ (by native_decide) (by evm_ov)]
  have rd1265 := rd1265pre.jumpiT (by native_decide) one_ne_zero_uint
    (by jump_dest) (by evm_ov)
  have rd1266 := evm_run rd1265 with [
    raw jumpdest (by native_decide) (by evm_ov)]
  have rd1279 := rd1266.pushConst stairstepRay
    (width := 12) (op := .PUSH12) (by decide) (by native_decide) (by evm_ov)
  have rd1285pre := evm_run rd1279 with [
    raw swap1 (by native_decide) (by evm_ov),
    raw div (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov)]
  exact ⟨_, _, by simpa [prod, hdiv, hdiv'] using
    rd1285pre.jump (by native_decide) (by jump_dest) (by evm_ov)⟩

set_option maxHeartbeats 1000000 in
theorem stairstepPriceRmulRayOverflowReverts {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {sel : UInt256}
    (hover : UInt256.size ≤ stairstepRay.toNat * (priceTop I).toNat)
    (h : RD exponentialDecreaseBytecode I g s0 ⟨1177⟩
      (stairstepRay :: priceTop I :: ⟨663⟩ :: ⟨0⟩ :: priceDur I ::
        priceTop I :: ⟨175⟩ :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev exponentialDecreaseBytecode g s0 := by
  have rd1242pre := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw mul (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw iszero (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw push2 ⟨1201⟩ (by native_decide) (by evm_ov)]
  have hRayNonzero : UInt256.isZero stairstepRay = ⟨0⟩ := by native_decide
  have rd1243 := rd1242pre.jumpiNT (by native_decide) hRayNonzero (by evm_ov)
  have rd1253pre := evm_run rd1243 with [
    raw pop (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw push2 ⟨1198⟩ (by native_decide) (by evm_ov)]
  have rd1253 := rd1253pre.jumpiT (by native_decide)
    (by native_decide : stairstepRay ≠ ⟨0⟩) (by jump_dest) (by evm_ov)
  have hdivNe :
      UInt256.div (UInt256.mul stairstepRay (priceTop I)) stairstepRay ≠ priceTop I := by
    simpa [HMul.hMul, Mul.mul] using stairstepRay_mul_div_overflow_ne (priceTop I) hover
  have rd1256pre := evm_run rd1253 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw div (by native_decide) (by evm_ov),
    raw eq (by native_decide) (by evm_ov)]
  have heq : UInt256.eq
      (UInt256.div (UInt256.mul stairstepRay (priceTop I)) stairstepRay)
      (priceTop I) = ⟨0⟩ := u256_eq_of_ne hdivNe
  rw [heq] at rd1256pre
  have rd1261pre := evm_run rd1256pre with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push2 ⟨1210⟩ (by native_decide) (by evm_ov),
    raw jumpiNT (by native_decide) rfl (by evm_ov)]
  exact RD.solcPush1Dup1Revert0 rd1261pre
    (by native_decide) (by native_decide) (by native_decide) (by evm_ov)

set_option maxHeartbeats 1000000 in
theorem stairstepPriceRmulReturns {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {sel pow : UInt256}
    (hfit : pow.toNat * (priceTop I).toNat < UInt256.size)
    (h : RD exponentialDecreaseBytecode I g s0 ⟨1177⟩
      (pow :: priceTop I :: ⟨663⟩ :: ⟨0⟩ :: priceDur I ::
        priceTop I :: ⟨175⟩ :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD exponentialDecreaseBytecode I g s0 ⟨663⟩
      (UInt256.div (pow * priceTop I) stairstepRay :: ⟨0⟩ :: priceDur I ::
        priceTop I :: ⟨175⟩ :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have rd1242pre := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw mul (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw iszero (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw push2 ⟨1201⟩ (by native_decide) (by evm_ov)]
  by_cases hpow0 : pow = ⟨0⟩
  · have hpowZero : UInt256.isZero pow ≠ ⟨0⟩ := by
      rw [hpow0]
      decide
    have rd1256 := rd1242pre.jumpiT (by native_decide) hpowZero (by jump_dest) (by evm_ov)
    have rd1265pre := evm_run rd1256 with [
      raw jumpdest (by native_decide) (by evm_ov),
      raw push2 ⟨1210⟩ (by native_decide) (by evm_ov)]
    have rd1265 := rd1265pre.jumpiT (by native_decide) hpowZero
      (by jump_dest) (by evm_ov)
    have rd1266 := evm_run rd1265 with [
      raw jumpdest (by native_decide) (by evm_ov)]
    have rd1279 := rd1266.pushConst stairstepRay
      (width := 12) (op := .PUSH12) (by decide) (by native_decide) (by evm_ov)
    have rd1285pre := evm_run rd1279 with [
      raw swap1 (by native_decide) (by evm_ov),
      raw div (by native_decide) (by evm_ov),
      raw swap3 (by native_decide) (by evm_ov),
      raw swap2 (by native_decide) (by evm_ov),
      raw pop (by native_decide) (by evm_ov),
      raw pop (by native_decide) (by evm_ov)]
    exact ⟨_, _, by simpa [hpow0] using
      rd1285pre.jump (by native_decide) (by jump_dest) (by evm_ov)⟩
  · have hpowNonzero : UInt256.isZero pow = ⟨0⟩ := isZero_eq_zero_of_ne hpow0
    have rd1243 := rd1242pre.jumpiNT (by native_decide) hpowNonzero (by evm_ov)
    have rd1253pre := evm_run rd1243 with [
      raw pop (by native_decide) (by evm_ov),
      raw dup3 (by native_decide) (by evm_ov),
      raw dup3 (by native_decide) (by evm_ov),
      raw dup3 (by native_decide) (by evm_ov),
      raw dup2 (by native_decide) (by evm_ov),
      raw push2 ⟨1198⟩ (by native_decide) (by evm_ov)]
    have rd1253 := rd1253pre.jumpiT (by native_decide) hpow0 (by jump_dest) (by evm_ov)
    have hpowNatNe : pow.toNat ≠ 0 := by
      intro hzero
      exact hpow0 (uint256_toNat_eq_zero hzero)
    have hdiv : UInt256.div (pow * priceTop I) pow = priceTop I := by
      apply u256_inj
      rw [udiv_toNat]
      have hprod : (pow * priceTop I).toNat = pow.toNat * (priceTop I).toNat := by
        rw [umul_toNat pow (priceTop I) hfit]
      rw [hprod]
      exact Nat.mul_div_right (priceTop I).toNat (Nat.pos_of_ne_zero hpowNatNe)
    have hdiv' : UInt256.div (UInt256.mul pow (priceTop I)) pow = priceTop I := by
      simpa [HMul.hMul, Mul.mul] using hdiv
    have rd1256pre := evm_run rd1253 with [
      raw jumpdest (by native_decide) (by evm_ov),
      raw div (by native_decide) (by evm_ov),
      raw eq (by native_decide) (by evm_ov)]
    rw [hdiv', u256_eq_refl] at rd1256pre
    have rd1265pre := evm_run rd1256pre with [
      raw jumpdest (by native_decide) (by evm_ov),
      raw push2 ⟨1210⟩ (by native_decide) (by evm_ov)]
    have rd1265 := rd1265pre.jumpiT (by native_decide) one_ne_zero_uint
      (by jump_dest) (by evm_ov)
    have rd1266 := evm_run rd1265 with [
      raw jumpdest (by native_decide) (by evm_ov)]
    have rd1279 := rd1266.pushConst stairstepRay
      (width := 12) (op := .PUSH12) (by decide) (by native_decide) (by evm_ov)
    have rd1285pre := evm_run rd1279 with [
      raw swap1 (by native_decide) (by evm_ov),
      raw div (by native_decide) (by evm_ov),
      raw swap3 (by native_decide) (by evm_ov),
      raw swap2 (by native_decide) (by evm_ov),
      raw pop (by native_decide) (by evm_ov),
      raw pop (by native_decide) (by evm_ov)]
    exact ⟨_, _, by simpa [hdiv, hdiv'] using
      rd1285pre.jump (by native_decide) (by jump_dest) (by evm_ov)⟩

set_option maxHeartbeats 1000000 in
theorem stairstepPriceRmulOverflowReverts {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {sel pow : UInt256}
    (hover : UInt256.size ≤ pow.toNat * (priceTop I).toNat)
    (h : RD exponentialDecreaseBytecode I g s0 ⟨1177⟩
      (pow :: priceTop I :: ⟨663⟩ :: ⟨0⟩ :: priceDur I ::
        priceTop I :: ⟨175⟩ :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev exponentialDecreaseBytecode g s0 := by
  have hpowNe : pow ≠ ⟨0⟩ := by
    intro hzero
    have hprod0 : pow.toNat * (priceTop I).toNat = 0 := by simp [hzero]
    have hsizePos : 0 < UInt256.size := by norm_num [UInt256.size]
    omega
  have hdivNe : UInt256.div (pow * priceTop I) pow ≠ priceTop I :=
    price_u256_mul_div_overflow_ne (priceTop I) pow (by simpa [Nat.mul_comm] using hover)
  have hdivNe' : UInt256.div (UInt256.mul pow (priceTop I)) pow ≠ priceTop I := by
    simpa [HMul.hMul, Mul.mul] using hdivNe
  have rd1242pre := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw mul (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw iszero (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw push2 ⟨1201⟩ (by native_decide) (by evm_ov)]
  have hpowNonzero : UInt256.isZero pow = ⟨0⟩ := isZero_eq_zero_of_ne hpowNe
  have rd1243 := rd1242pre.jumpiNT (by native_decide) hpowNonzero (by evm_ov)
  have rd1253pre := evm_run rd1243 with [
    raw pop (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw push2 ⟨1198⟩ (by native_decide) (by evm_ov)]
  have rd1253 := rd1253pre.jumpiT (by native_decide) hpowNe (by jump_dest) (by evm_ov)
  have rd1256pre := evm_run rd1253 with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw div (by native_decide) (by evm_ov),
    raw eq (by native_decide) (by evm_ov)]
  have heq :
      UInt256.eq (UInt256.div (UInt256.mul pow (priceTop I)) pow) (priceTop I) = ⟨0⟩ :=
    u256_eq_of_ne hdivNe'
  rw [heq] at rd1256pre
  have rd1261pre := evm_run rd1256pre with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push2 ⟨1210⟩ (by native_decide) (by evm_ov),
    raw jumpiNT (by native_decide) rfl (by evm_ov)]
  exact RD.solcPush1Dup1Revert0 rd1261pre
    (by native_decide) (by native_decide) (by native_decide) (by evm_ov)

set_option maxHeartbeats 1000000 in
theorem stairstepPriceFinishReturn {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {sel out : UInt256}
    (h : RD exponentialDecreaseBytecode I g s0 ⟨663⟩
      (out :: ⟨0⟩ :: priceDur I :: priceTop I :: ⟨175⟩ :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret exponentialDecreaseBytecode g s0 (cA, σ) (UInt256.toByteArray out) := by
  have rd718pre := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw swap4 (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov)]
  have rd202 := rd718pre.jump (by native_decide) (by jump_dest) (by evm_ov)
  exact RD.solcReturnWordFromMem
    (code := exponentialDecreaseBytecode) (g := g) (s0 := s0)
    (ee := I) (pc := ⟨175⟩) (val := out) (ret := sel) (R := [])
    (memout := solcReturnMem out)
    rd202
    (by
      unfold solcReturnWordFromMemWf
      repeat' first | apply And.intro | native_decide)
    solcFreePtrMem_mload64
    (by rfl)
    (solcReturnMem_mload64 out)
    (solcReturnMem_read128 out)
    (by simp)
set_option maxHeartbeats 2000000 in
theorem stairstepPriceBody {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = exponentialDecreaseBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (stairstepSelBytes 3))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (stairstepSelBytes 3) rfl hsel
  have hdispatch : dispatchMsg contract I.calldata = some priceTransition :=
    stairstepDispatchPrice hsel
  have hreach := stairstepReachPriceBody (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz4 hsize hsel
  by_cases hsz68 : 68 ≤ I.calldata.size
  · let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
    have hcutWordEq : priceCutWord σ_evm I = priceCutWord σ_solm I := by
      simpa [priceCutWord, stairstepSlotWord] using
        accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨1⟩ ⟨0⟩
    have hnEq : priceN σ_evm I = priceN σ_solm I := by
      simp [priceN]
    have hcutLoadSolm :
        Solm.EVM.storageLoad evmSolm evmSolm.executionEnv.codeOwner ⟨1⟩ =
            priceCutWord σ_solm I := by
      simp [evmSolm, priceCutWord, stairstepSlotWord, initState, Solm.EVM.storageLoad,
        State.lookupAccount, Account.lookupStorage, solcSlotWord]
    obtain ⟨_, _, rd627⟩ := stairstepPriceX_decoded
      (g := Sat256.ofUInt256 g) hsz68 hsize hreach
    obtain ⟨_, _, rd987⟩ := stairstepPriceToRpow (g := Sat256.ofUInt256 g) rd627
    by_cases hn : priceN σ_evm I = ⟨0⟩
    · have hnSolm : priceN σ_solm I = ⟨0⟩ := by
        rwa [← hnEq]
      obtain ⟨_, _, rd658⟩ :=
        stairstepPriceRpowNZero_toRmul (by simpa [hn] using rd987)
      obtain ⟨_, _, rd1177⟩ := stairstepPriceRpowReturnToRmul rd658
      by_cases hfit : stairstepRay.toNat * (priceTop I).toNat < UInt256.size
      · have hbody :
            ExecTransitionBody config contract evmSolm (priceLocals I)
              priceTransition.body
              (.returned
                { contract := contract,
                  locals := priceLocalsOut σ_solm I stairstepRay (priceTop I) }
                evmSolm (some [.int (Int.ofNat (priceTop I).toNat)])) :=
          stairstepPriceSourceNZeroReturns
            (evm := evmSolm) (σ := σ_solm) (I := I)
            (by simp only [evmSolm, initState]; exact hwv)
            hcutLoadSolm hnSolm hfit
        obtain ⟨_, _, rd663⟩ := stairstepPriceRmulRayReturns hfit rd1177
        have hret := stairstepPriceFinishReturn rd663
        have henc :
            returnEquiv (UInt256.toByteArray (priceTop I))
              (some [.int (Int.ofNat (priceTop I).toNat)]) priceTransition.returnType := by
          rw [show priceTransition.returnType = [uint256] by rfl]
          exact returnEquiv_of_encode
            (by simpa [uint256] using uint256ReturnEncoding (priceTop I))
        exact hret.reEquivExecution hcode hdispatch (stairstepDecode_price_ok hsz68)
          hbody hAccounts henc
      · have hover : UInt256.size ≤ stairstepRay.toNat * (priceTop I).toNat := by
          omega
        have hbody :
            ExecTransitionBody config contract evmSolm (priceLocals I)
              priceTransition.body .reverted :=
          stairstepPriceSourceNZeroRmulOverflowReverts
            (evm := evmSolm) (σ := σ_solm) (I := I)
            (by simp only [evmSolm, initState]; exact hwv)
            hcutLoadSolm hnSolm hover
        have hrev := stairstepPriceRmulRayOverflowReverts hover rd1177
        exact hrev.reEquivExecutionRevert hcode hdispatch
          (stairstepDecode_price_ok hsz68) hbody
    · have hnSolm : priceN σ_solm I ≠ ⟨0⟩ := by
        intro hzero
        exact hn (by rw [hnEq, hzero])
      by_cases hcut : priceCutWord σ_evm I = ⟨0⟩
      · have hcutSolm : priceCutWord σ_solm I = ⟨0⟩ := by
          rw [← hcutWordEq]
          exact hcut
        have hbody :
            ExecTransitionBody config contract evmSolm (priceLocals I)
              priceTransition.body
              (.returned
                { contract := contract, locals := priceLocalsOut σ_solm I ⟨0⟩ ⟨0⟩ }
                evmSolm (some [.int 0])) :=
          stairstepPriceSourceXZeroNNonzeroReturns
            (evm := evmSolm) (σ := σ_solm) (I := I)
            (by simp only [evmSolm, initState]; exact hwv)
            hcutLoadSolm hnSolm hcutSolm
        obtain ⟨_, _, rd658⟩ :=
          stairstepPriceRpowXZeroNNonzero_toRmul hn hcut rd987
        obtain ⟨_, _, rd1177⟩ := stairstepPriceRpowReturnToRmul rd658
        have hfitZero : (⟨0⟩ : UInt256).toNat * (priceTop I).toNat < UInt256.size := by
          norm_num [UInt256.size]
        obtain ⟨_, _, rd663⟩ := stairstepPriceRmulReturns hfitZero rd1177
        have hzeroOut :
            UInt256.div ((⟨0⟩ : UInt256) * priceTop I) stairstepRay =
              (⟨0⟩ : UInt256) := by
          rw [uint256_zero_mul, uint256_div_zero_num]
        have hret : RDret exponentialDecreaseBytecode (Sat256.ofUInt256 g)
            (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) (cA, σ_evm)
            (UInt256.toByteArray (⟨0⟩ : UInt256)) := by
          simpa [hzeroOut] using stairstepPriceFinishReturn rd663
        have henc :
            returnEquiv (UInt256.toByteArray (⟨0⟩ : UInt256))
              (some [.int 0]) priceTransition.returnType := by
          rw [show priceTransition.returnType = [uint256] by rfl]
          exact returnEquiv_of_encode
            (by
              simpa [uint256, stairstepUInt256Zero_toNat] using
                uint256ReturnEncoding (⟨0⟩ : UInt256))
        exact hret.reEquivExecution hcode hdispatch (stairstepDecode_price_ok hsz68)
          hbody hAccounts henc
      · have hcutSolmNe : priceCutWord σ_solm I ≠ ⟨0⟩ := by
          intro hzero
          apply hcut
          rw [hcutWordEq, hzero]
        have hcoupled :=
          rpowFunctionCoupled
            (I := I) (g := Sat256.ofUInt256 g)
            (s0 := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
            (x := priceCutWord σ_solm I) (n := priceN σ_solm I) (b := stairstepRay)
            (evm := evmSolm)
            (mem := solcFreePtrMem) (out := ByteArray.empty) (aw := UInt256.ofNat 3)
            (acc := (cA, σ_evm))
            (R := priceTop I :: ⟨663⟩ :: ⟨0⟩ :: priceDur I ::
              priceTop I :: ⟨175⟩ :: [stairstepSelWord I])
            (hRlen := by simp)
            (hn := hnSolm)
            (hx := hcutSolmNe)
            (hb := by native_decide)
            (by simpa [hnEq, hcutWordEq] using rd987)
        cases hcoupled with
        | inr hrev =>
            rcases hrev with ⟨hrpowBody, hrdRev⟩
            have hbody :
                ExecTransitionBody config contract evmSolm (priceLocals I)
                  priceTransition.body .reverted :=
              stairstepPriceSourceRpowReverts
                (evm := evmSolm) (σ := σ_solm) (I := I)
                (by simp only [evmSolm, initState]; exact hwv)
                hcutLoadSolm hrpowBody
            exact hrdRev.reEquivExecutionRevert hcode hdispatch
              (stairstepDecode_price_ok hsz68) hbody
        | inl hretRpow =>
            rcases hretRpow with
              ⟨xFinal, pow, rpowLocals, k658, C658, hfinalStore, hrpowBody, rd658⟩
            obtain ⟨_, _, rd1177⟩ := stairstepPriceRpowReturnToRmul rd658
            by_cases hfit : pow.toNat * (priceTop I).toNat < UInt256.size
            · have hbody :
                  ExecTransitionBody config contract evmSolm (priceLocals I)
                    priceTransition.body
                    (.returned
                      { contract := contract,
                        locals :=
                          priceLocalsOut σ_solm I pow
                            (UInt256.div (pow * priceTop I) stairstepRay) }
                      evmSolm
                      (some
                        [.int (Int.ofNat
                          (UInt256.div (pow * priceTop I) stairstepRay).toNat)])) :=
                stairstepPriceSourceRpowReturns
                  (evm := evmSolm) (σ := σ_solm) (I := I)
                  (pow := pow) (rpowLocals := rpowLocals)
                  (by simp only [evmSolm, initState]; exact hwv)
                  hcutLoadSolm hrpowBody hfit
              obtain ⟨_, _, rd663⟩ := stairstepPriceRmulReturns hfit rd1177
              have hret := stairstepPriceFinishReturn rd663
              have henc :
                  returnEquiv
                    (UInt256.toByteArray
                      (UInt256.div (pow * priceTop I) stairstepRay))
                    (some
                      [.int (Int.ofNat
                        (UInt256.div (pow * priceTop I) stairstepRay).toNat)])
                    priceTransition.returnType := by
                rw [show priceTransition.returnType = [uint256] by rfl]
                exact returnEquiv_of_encode
                  (by
                    simpa [uint256] using
                      uint256ReturnEncoding
                        (UInt256.div (pow * priceTop I) stairstepRay))
              exact hret.reEquivExecution hcode hdispatch
                (stairstepDecode_price_ok hsz68) hbody hAccounts henc
            · have hover : UInt256.size ≤ pow.toNat * (priceTop I).toNat := by
                omega
              have hbody :
                  ExecTransitionBody config contract evmSolm (priceLocals I)
                    priceTransition.body .reverted :=
                stairstepPriceSourceRpowReturnsRmulOverflowReverts
                  (evm := evmSolm) (σ := σ_solm) (I := I)
                  (pow := pow) (rpowLocals := rpowLocals)
                  (by simp only [evmSolm, initState]; exact hwv)
                  hcutLoadSolm hrpowBody hover
              have hrev := stairstepPriceRmulOverflowReverts hover rd1177
              exact hrev.reEquivExecutionRevert hcode hdispatch
                (stairstepDecode_price_ok hsz68) hbody
  · exact (stairstepPriceX_shortarg (g := Sat256.ofUInt256 g) hsz4 hsize (by omega)
        hreach)
      |>.reEquivDecodingFailed hcode hdispatch
        (stairstepDecode_price_none_short hsz4 (by omega))

end Benchmarks.Dss.ExponentialDecrease
