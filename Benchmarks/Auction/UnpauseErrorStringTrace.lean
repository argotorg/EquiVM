import Benchmarks.Auction.UnpauseMintFailureTraceSub

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 50000000
set_option maxHeartbeats 0

namespace Auction

theorem decodeReturnValue_string_some_facts {returndata : ByteArray} {decoded : Value}
    (hdec : ABI.decodeReturnValue? .string returndata = some decoded) :
    ∃ off len payload,
      ABI.readNat? returndata.toList 0 = some off ∧
      ¬ ABI.solcMaxU64 < off ∧
      ABI.readNat? returndata.toList off = some len ∧
      ¬ ABI.solcMaxU64 < len ∧
      ABI.readBytes? returndata.toList (off + 32) len = some payload ∧
      decoded = .bytes (ByteArray.mk payload.toArray) := by
  unfold ABI.decodeReturnValue? at hdec
  unfold ABI.decodeReturnValues? at hdec
  by_cases hhuge :
    [ABIType.string].isEmpty = false ∧ (2 : Nat) ^ 255 ≤ returndata.toList.length
  · rw [if_pos hhuge] at hdec
    simp at hdec
  · rw [if_neg hhuge] at hdec
    simp [ABI.abiTupleHeadSize?, ABI.decodeABIValues?, ABI.isDynamicABIType] at hdec
    cases hoff : ABI.readNat? returndata.toList 0 with
    | none =>
        simp [hoff, ABI.decodeABIValues?, ABI.isDynamicABIType] at hdec
    | some off =>
        by_cases hoffMax : ABI.solcMaxU64 < off
        · simp [hoff, hoffMax, ABI.decodeABIValues?, ABI.isDynamicABIType] at hdec
        · simp [hoff, hoffMax, ABI.isDynamicABIType] at hdec
          unfold ABI.decodeABIValue? at hdec
          cases hlen : ABI.readNat? returndata.toList off with
          | none =>
              simp [hlen] at hdec
          | some len =>
              by_cases hlenMax : ABI.solcMaxU64 < len
              · simp [hlen, hlenMax] at hdec
              · simp [hlen, hlenMax] at hdec
                cases hpayload : ABI.readBytes? returndata.toList (off + 32) len with
                | none =>
                    simp [hpayload] at hdec
                | some payload =>
                    simp [hpayload, ABI.decodeABIValues?] at hdec
                    exact ⟨off, len, payload, rfl, hoffMax, hlen, hlenMax, hpayload,
                      hdec.symm⟩

-- LIBRARY CANDIDATE: positive-length `ABI.readBytes?` success implies the requested window is in
-- bounds. Zero-length reads are allowed past the end by the current ABI helper.
theorem readBytes?_some_length_of_pos {bytes : List UInt8} {off len : Nat} {out : List UInt8}
    (hpos : 0 < len) (h : ABI.readBytes? bytes off len = some out) :
    off + len ≤ bytes.length := by
  unfold ABI.readBytes? at h
  by_cases hlen : ((bytes.drop off).take len).length = len
  · rw [if_pos hlen] at h
    rw [List.length_take, List.length_drop] at hlen
    omega
  · rw [if_neg hlen] at h
    cases h

-- LIBRARY CANDIDATE: an in-bounds ABI byte window can be read.
theorem readBytes?_exists_of_length {bytes : List UInt8} {off len : Nat}
    (h : off + len ≤ bytes.length) : ∃ out, ABI.readBytes? bytes off len = some out := by
  unfold ABI.readBytes?
  have hlen : ((bytes.drop off).take len).length = len := by
    rw [List.length_take, List.length_drop]
    omega
  exact ⟨(bytes.drop off).take len, by simp [hlen]⟩

-- LIBRARY CANDIDATE: an in-bounds ABI word can be read as a natural number.
theorem readNat?_exists_of_length {bytes : List UInt8} {off : Nat}
    (h : off + 32 ≤ bytes.length) : ∃ n, ABI.readNat? bytes off = some n := by
  unfold ABI.readNat? ABI.readWord?
  obtain ⟨wordBytes, hbytes⟩ := readBytes?_exists_of_length h
  exact ⟨(ABI.bytesToWord wordBytes).val, by simp [hbytes]⟩

-- LIBRARY CANDIDATE: `readNat?` returns the value of an EVM word, hence it is word-sized.
theorem readNat?_some_lt_uint256 {bytes : List UInt8} {off n : Nat}
    (h : ABI.readNat? bytes off = some n) : n < UInt256.size := by
  unfold ABI.readNat? ABI.readWord? at h
  cases hbytes : ABI.readBytes? bytes off 32 with
  | none =>
      simp [hbytes] at h
  | some wordBytes =>
      simp [hbytes, ABI.bytesToWord] at h
      cases h
      exact (UInt256.ofNat (fromByteArrayBigEndian (ByteArray.mk wordBytes.toArray))).val.isLt

-- LIBRARY CANDIDATE: decoding a dynamic string return from the primitive ABI reads.
theorem decodeReturnValue_string_some_of_reads {returndata : ByteArray}
    {off len : Nat} {payload : List UInt8}
    (hsmall : returndata.size < (2 : Nat) ^ 255)
    (hoff : ABI.readNat? returndata.toList 0 = some off)
    (hoffMax : off ≤ ABI.solcMaxU64)
    (hlen : ABI.readNat? returndata.toList off = some len)
    (hlenMax : len ≤ ABI.solcMaxU64)
    (hpayload : ABI.readBytes? returndata.toList (off + 32) len = some payload) :
    ABI.decodeReturnValue? .string returndata = some (.bytes (ByteArray.mk payload.toArray)) := by
  unfold ABI.decodeReturnValue?
  unfold ABI.decodeReturnValues?
  have hhuge : ¬ ([ABIType.string].isEmpty = false ∧ (2 : Nat) ^ 255 ≤ returndata.toList.length) := by
    intro h
    have hlen : returndata.toList.length = returndata.size := by
      rw [byteArray_toList_eq, Array.length_toList]
      rfl
    rw [hlen] at h
    omega
  rw [if_neg hhuge]
  simp [ABI.abiTupleHeadSize?, ABI.decodeABIValues?, ABI.isDynamicABIType, hoff]
  have hoffMaxNot : ¬ ABI.solcMaxU64 < off := by omega
  simp [hoffMaxNot]
  unfold ABI.decodeABIValue?
  simp [hlen]
  have hlenMaxNot : ¬ ABI.solcMaxU64 < len := by omega
  simp [hlenMaxNot, hpayload]

theorem decodeReturnValue_string_some_bounds {returndata : ByteArray} {decoded : Value}
    (hdec : ABI.decodeReturnValue? .string returndata = some decoded) :
    ∃ off len payload,
      ABI.readNat? returndata.toList 0 = some off ∧
      off ≤ ABI.solcMaxU64 ∧
      ABI.readNat? returndata.toList off = some len ∧
      len ≤ ABI.solcMaxU64 ∧
      ABI.readBytes? returndata.toList (off + 32) len = some payload ∧
      off + 32 ≤ returndata.size ∧
      off + 32 + len ≤ returndata.size ∧
      decoded = .bytes (ByteArray.mk payload.toArray) := by
  obtain ⟨off, len, payload, hoff, hoffMax, hlen, hlenMax, hpayload, hdecoded⟩ :=
    decodeReturnValue_string_some_facts hdec
  refine ⟨off, len, payload, hoff, ?_, hlen, ?_, hpayload, ?_, ?_, hdecoded⟩
  · omega
  · omega
  · have h := readNat?_some_length hlen
    simpa [byteArray_toList_eq] using h
  · by_cases hzero : len = 0
    · have h := readNat?_some_length hlen
      simpa [hzero, byteArray_toList_eq] using h
    · have hpos : 0 < len := Nat.pos_of_ne_zero hzero
      have h := readBytes?_some_length_of_pos hpos hpayload
      simpa [byteArray_toList_eq] using h

-- LIBRARY CANDIDATE: a word whose low bit is set is nonzero.
theorem u256_lor_one_ne_zero (x : UInt256) : UInt256.lor (⟨1⟩ : UInt256) x ≠ ⟨0⟩ := by
  intro h
  have hmod := congrArg (fun w : UInt256 => w.toNat % 2) h
  change (UInt256.lor (⟨1⟩ : UInt256) x).toNat % 2 =
    (⟨0⟩ : UInt256).toNat % 2 at hmod
  rw [u256_lor_toNat] at hmod
  have htwo : 2 ∣ UInt256.size := by
    norm_num [UInt256.size]
  rw [Nat.mod_mod_of_dvd _ htwo] at hmod
  change (Nat.lor 1 x.toNat) % 2 = 0 at hmod
  have hlor : (Nat.lor 1 x.toNat) % 2 = 1 := by
    rw [Nat.mod_two_of_bodd]
    have hbit : Nat.testBit (Nat.lor 1 x.toNat) 0 = true := by
      change Nat.testBit (1 ||| x.toNat) 0 = true
      simp
    simpa [Nat.testBit, Nat.shiftRight_zero, Nat.bodd_eq_one_and_ne_zero] using hbit
  omega

theorem errorStringNewFreeWord_toNat {off len : Nat}
    (hoffMax : off ≤ ABI.solcMaxU64) (hlenMax : len ≤ ABI.solcMaxU64) :
    let offW := UInt256.ofNat off
    let lenW := UInt256.ofNat len
    let payloadLen : UInt256 := (offW + lenW) + ⟨32⟩
    let roundedLen : UInt256 :=
      UInt256.land (UInt256.lnot (⟨31⟩ : UInt256)) (payloadLen + ⟨31⟩)
    ((⟨128⟩ : UInt256) + roundedLen).toNat = errorStringNewFreeNat off len := by
  intro offW lenW payloadLen roundedLen
  have hoffLt : off < UInt256.size := by
    norm_num [ABI.solcMaxU64, UInt256.size] at hoffMax ⊢
    omega
  have hlenLt : len < UInt256.size := by
    norm_num [ABI.solcMaxU64, UInt256.size] at hlenMax ⊢
    omega
  have hsumLt : off + len + 63 < UInt256.size := by
    norm_num [ABI.solcMaxU64, UInt256.size] at hoffMax hlenMax ⊢
    omega
  have hoffW : offW.toNat = off := by
    dsimp [offW]
    exact UInt256.toNat_ofNat_of_lt hoffLt
  have hlenW : lenW.toNat = len := by
    dsimp [lenW]
    exact UInt256.toNat_ofNat_of_lt hlenLt
  have h32 : (⟨32⟩ : UInt256).toNat = 32 := by decide
  have h31 : (⟨31⟩ : UInt256).toNat = 31 := by decide
  have h128 : (⟨128⟩ : UInt256).toNat = 128 := by decide
  have hpayload : payloadLen.toNat = off + len + 32 := by
    dsimp [payloadLen]
    rw [uadd_toNat, uadd_toNat, hoffW, hlenW, h32]
    rw [Nat.mod_eq_of_lt (by omega : off + len < UInt256.size)]
    rw [Nat.mod_eq_of_lt (by omega : off + len + 32 < UInt256.size)]
  have hround : roundedLen.toNat = errorStringRoundedAllocNat off len := by
    dsimp [roundedLen, errorStringRoundedAllocNat]
    rw [uland_toNat, lnot31_toNat, uadd_toNat, hpayload, h31]
    rw [Nat.mod_eq_of_lt hsumLt]
    change (2 ^ 256 - 32) &&& (off + len + 63) =
      (UInt256.size - 32) &&& (off + len + 63)
    norm_num [UInt256.size]
  have hroundLe : errorStringRoundedAllocNat off len ≤ off + len + 63 := by
    dsimp [errorStringRoundedAllocNat]
    exact Nat.and_le_right
  have hnewLt : 128 + errorStringRoundedAllocNat off len < UInt256.size := by
    have hle := hroundLe
    norm_num [ABI.solcMaxU64, UInt256.size] at hoffMax hlenMax ⊢
    omega
  dsimp [roundedLen]
  rw [uadd_toNat, h128, hround, Nat.mod_eq_of_lt hnewLt]
  rfl

theorem errorStringNewFreeWord_gt_max64_zero {off len : Nat}
    (hoffMax : off ≤ ABI.solcMaxU64) (hlenMax : len ≤ ABI.solcMaxU64)
    (halloc : errorStringNewFreeNat off len ≤ ABI.solcMaxU64) :
    let offW := UInt256.ofNat off
    let lenW := UInt256.ofNat len
    let payloadLen : UInt256 := (offW + lenW) + ⟨32⟩
    let roundedLen : UInt256 :=
      UInt256.land (UInt256.lnot (⟨31⟩ : UInt256)) (payloadLen + ⟨31⟩)
    UInt256.gt ((⟨128⟩ : UInt256) + roundedLen) (⟨0xffffffffffffffff⟩ : UInt256) =
      ⟨0⟩ := by
  intro offW lenW payloadLen roundedLen
  apply ugt_zero
  rw [errorStringNewFreeWord_toNat hoffMax hlenMax]
  change errorStringNewFreeNat off len ≤ ABI.solcMaxU64
  exact halloc

theorem errorStringNewFreeWord_lt_128_zero {off len : Nat}
    (hoffMax : off ≤ ABI.solcMaxU64) (hlenMax : len ≤ ABI.solcMaxU64) :
    let offW := UInt256.ofNat off
    let lenW := UInt256.ofNat len
    let payloadLen : UInt256 := (offW + lenW) + ⟨32⟩
    let roundedLen : UInt256 :=
      UInt256.land (UInt256.lnot (⟨31⟩ : UInt256)) (payloadLen + ⟨31⟩)
    UInt256.lt ((⟨128⟩ : UInt256) + roundedLen) (⟨128⟩ : UInt256) = ⟨0⟩ := by
  intro offW lenW payloadLen roundedLen
  apply ult_zero
  rw [errorStringNewFreeWord_toNat hoffMax hlenMax]
  change 128 ≤ errorStringNewFreeNat off len
  simp [errorStringNewFreeNat]

theorem errorStringNewFreeWord_gt_max64_one {off len : Nat}
    (hoffMax : off ≤ ABI.solcMaxU64) (hlenMax : len ≤ ABI.solcMaxU64)
    (halloc : ABI.solcMaxU64 < errorStringNewFreeNat off len) :
    let offW := UInt256.ofNat off
    let lenW := UInt256.ofNat len
    let payloadLen : UInt256 := (offW + lenW) + ⟨32⟩
    let roundedLen : UInt256 :=
      UInt256.land (UInt256.lnot (⟨31⟩ : UInt256)) (payloadLen + ⟨31⟩)
    UInt256.gt ((⟨128⟩ : UInt256) + roundedLen) (⟨0xffffffffffffffff⟩ : UInt256) =
      ⟨1⟩ := by
  intro offW lenW payloadLen roundedLen
  apply ugt_one
  rw [errorStringNewFreeWord_toNat hoffMax hlenMax]
  change ABI.solcMaxU64 < errorStringNewFreeNat off len
  exact halloc

theorem errorStringPayloadBoundsLeft_toNat {off len : Nat}
    (hoffMax : off ≤ ABI.solcMaxU64) (hlenMax : len ≤ ABI.solcMaxU64) :
    let offW := UInt256.ofNat off
    let lenW := UInt256.ofNat len
    ((((⟨128⟩ : UInt256) + offW) + lenW) + ⟨32⟩).toNat = 160 + off + len := by
  intro offW lenW
  have hoffLt : off < UInt256.size := by
    norm_num [ABI.solcMaxU64, UInt256.size] at hoffMax ⊢
    omega
  have hlenLt : len < UInt256.size := by
    norm_num [ABI.solcMaxU64, UInt256.size] at hlenMax ⊢
    omega
  have hoffW : offW.toNat = off := by
    dsimp [offW]
    exact UInt256.toNat_ofNat_of_lt hoffLt
  have hlenW : lenW.toNat = len := by
    dsimp [lenW]
    exact UInt256.toNat_ofNat_of_lt hlenLt
  have h128 : (⟨128⟩ : UInt256).toNat = 128 := by decide
  have h32 : (⟨32⟩ : UInt256).toNat = 32 := by decide
  rw [uadd_toNat, uadd_toNat, uadd_toNat, h128, hoffW, hlenW, h32]
  rw [Nat.mod_eq_of_lt (by
    norm_num [ABI.solcMaxU64, UInt256.size] at hoffMax ⊢
    omega : 128 + off < UInt256.size)]
  rw [Nat.mod_eq_of_lt (by
    norm_num [ABI.solcMaxU64, UInt256.size] at hoffMax hlenMax ⊢
    omega : 128 + off + len < UInt256.size)]
  rw [Nat.mod_eq_of_lt (by
    norm_num [ABI.solcMaxU64, UInt256.size] at hoffMax hlenMax ⊢
    omega : 128 + off + len + 32 < UInt256.size)]
  omega

theorem errorStringPayloadBoundsRight_toNat {o : ByteArray}
    (hosz : o.size < UInt256.size) (hsmall : o.size < (2 : Nat) ^ 138) :
    (((⟨128⟩ : UInt256) + UInt256.ofNat o.size) + UInt256.lnot (⟨3⟩ : UInt256)).toNat =
      124 + o.size := by
  have h128 : (⟨128⟩ : UInt256).toNat = 128 := by decide
  have hsizeWord : (UInt256.ofNat o.size).toNat = o.size :=
    UInt256.toNat_ofNat_of_lt hosz
  have hlnot3 : (UInt256.lnot (⟨3⟩ : UInt256)).toNat = UInt256.size - 4 := by
    unfold UInt256.lnot
    decide
  have hbase :
      ((⟨128⟩ : UInt256) + UInt256.ofNat o.size).toNat = 128 + o.size := by
    rw [uadd_toNat, h128, hsizeWord]
    rw [Nat.mod_eq_of_lt (by
      norm_num [UInt256.size] at hsmall ⊢
      omega : 128 + o.size < UInt256.size)]
  rw [uadd_toNat, hbase, hlnot3]
  have hsum : 128 + o.size + (UInt256.size - 4) = UInt256.size + (124 + o.size) := by
    norm_num [UInt256.size] at hsmall ⊢
    omega
  rw [hsum, Nat.add_mod_left]
  rw [Nat.mod_eq_of_lt (by
    norm_num [UInt256.size] at hsmall ⊢
    omega : 124 + o.size < UInt256.size)]

theorem errorStringPayloadBoundsGuard_zero {o : ByteArray} {off len : Nat}
    (hosz : o.size < UInt256.size) (hsmall : o.size < (2 : Nat) ^ 138)
    (hoffMax : off ≤ ABI.solcMaxU64) (hlenMax : len ≤ ABI.solcMaxU64)
    (hpayloadBound : off + len + 36 ≤ o.size) :
    let offW := UInt256.ofNat off
    let lenW := UInt256.ofNat len
    UInt256.gt ((((⟨128⟩ : UInt256) + offW) + lenW) + ⟨32⟩)
        (((⟨128⟩ : UInt256) + UInt256.ofNat o.size) + UInt256.lnot (⟨3⟩ : UInt256)) =
      ⟨0⟩ := by
  intro offW lenW
  apply ugt_zero
  rw [errorStringPayloadBoundsLeft_toNat hoffMax hlenMax,
    errorStringPayloadBoundsRight_toNat hosz hsmall]
  omega

theorem errorStringPayloadBoundsGuard_one {o : ByteArray} {off len : Nat}
    (hosz : o.size < UInt256.size) (hsmall : o.size < (2 : Nat) ^ 138)
    (hoffMax : off ≤ ABI.solcMaxU64) (hlenMax : len ≤ ABI.solcMaxU64)
    (hpayloadBound : o.size < off + len + 36) :
    let offW := UInt256.ofNat off
    let lenW := UInt256.ofNat len
    UInt256.gt ((((⟨128⟩ : UInt256) + offW) + lenW) + ⟨32⟩)
        (((⟨128⟩ : UInt256) + UInt256.ofNat o.size) + UInt256.lnot (⟨3⟩ : UInt256)) =
      ⟨1⟩ := by
  intro offW lenW
  apply ugt_one
  rw [errorStringPayloadBoundsLeft_toNat hoffMax hlenMax,
    errorStringPayloadBoundsRight_toNat hosz hsmall]
  omega

theorem typedMintCall_output_size_lt_2pow138 {evm evm' : EVM.State} {target : EVM.Address}
    {z : Bool} {out : ByteArray}
    (hcall : typedCallViaEVM auctionConfig evm target "mint" 0 [] (z, evm', out) true)
    (hout : 0 < out.size) :
    out.size < (2 : Nat) ^ 138 := by
  rcases hcall with ⟨calldata, henc, hraw⟩
  have hcalldata : calldata = mintSelector := by
    simp [auctionConfig, auctionExternalABI] at henc
    exact henc.symm
  cases hraw with
  | callMade hvalue htheta hevme hbalance hdepth =>
      rcases htheta with ⟨callGas, A_in, hthetaEq⟩
      rw [hvalue] at hthetaEq
      exact Theta_returnData_size_lt_2pow138_of_eq
        evm.executionEnv.blobVersionedHashes evm.createdAccounts evm.genesisBlockHeader
        evm.blocks evm.accountMap evm.σ₀ A_in evm.executionEnv.codeOwner
        evm.executionEnv.sender target (Ethereum.toExecute evm.accountMap target) callGas
        (.ofNat evm.executionEnv.gasPrice) (EVM.wordOfInt (0 : ℤ)) (EVM.wordOfInt (0 : ℤ))
        calldata (evm.executionEnv.depth + 1) evm.executionEnv.header true hthetaEq
        (by rw [hcalldata]; native_decide)
  | callNotMade hA hevme hnot =>
      simp at hout

noncomputable def auctionEventMemFrom (mem : ByteArray) (I : ExecutionEnv)
    (fmp : UInt256) : ByteArray :=
  (UInt256.toByteArray (auctionSourceWord I)).write 0 mem fmp.toNat 32

-- GENERALIZES Reasoning.Memory.write_eq_gen_from by allowing the write to extend the destination.
theorem write_eq_gen_from_extend (src base : ByteArray) (srcAddr destAddr len : ℕ)
    (hlen : len ≠ 0) (hsrc : srcAddr + len ≤ src.size) (hdest : destAddr ≤ base.size)
    (hext : base.size < destAddr + len) :
    src.write srcAddr base destAddr len =
      base.extract 0 destAddr ++ src.extract srcAddr (srcAddr + len) := by
  apply ByteArray.ext
  unfold ByteArray.write
  rw [if_neg hlen, if_neg (show ¬ srcAddr ≥ src.size from by omega)]
  have hsize : src.data.size = src.size := rfl
  have hpL : min len (src.size - srcAddr) = len := by omega
  have hsp : min base.size (destAddr + len) - (destAddr + len) = 0 := by
    rw [Nat.min_eq_left (by omega)]
    omega
  have hdp : destAddr - base.size = 0 := Nat.sub_eq_zero_of_le hdest
  have hz0 : ffi.ByteArray.zeroes (⟨↑(0 : ℕ)⟩ : USize) = ByteArray.empty :=
    zeroes_zero (by rfl)
  simp only [hdp, hz0, ByteArray.data_copySlice, ByteArray.data_append,
    ByteArray.data_extract, show (ByteArray.empty).data = (#[] : Array UInt8) from rfl,
    Array.append_empty, hsize, hpL, hsp, Nat.add_zero,
    show base.data.size = base.size from rfl]
  have htail : base.data.extract (destAddr + len) base.size = #[] :=
    Array.extract_eq_empty_of_le (by omega)
  rw [htail, Array.append_empty]

-- LIBRARY CANDIDATE: read back the prefix of an arbitrary source-window write.
theorem write_from_read_back_prefix (src base : ByteArray) (srcAddr destAddr len readLen : ℕ)
    (hlen : len ≠ 0) (hreadPos : readLen ≠ 0) (hread : readLen ≤ len)
    (hsrc : srcAddr + len ≤ src.size) (hdest : destAddr ≤ base.size)
    (hread64 : readLen < 2 ^ 64) :
    (src.write srcAddr base destAddr len).readWithPadding destAddr readLen =
      src.extract srcAddr (srcAddr + readLen) := by
  have hreadPosLt : 0 < readLen := Nat.pos_of_ne_zero hreadPos
  by_cases hin : destAddr + len ≤ base.size
  · rw [write_eq_gen_from src base srcAddr destAddr len hlen hsrc hin]
    rw [readWithPadding_eq_extract' _ destAddr readLen hreadPosLt hread64 (by
      rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
        ByteArray.size_extract, ByteArray.size_extract]
      omega)]
    rw [extract_append_left _ _ _ _ (by
      rw [ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract]
      omega)]
    rw [extract_append_right_window _ _ _ _ (by
      rw [ByteArray.size_extract]
      omega)]
    rw [show destAddr - (base.extract 0 destAddr).size = 0 by
      rw [ByteArray.size_extract]
      omega]
    rw [show destAddr + readLen - (base.extract 0 destAddr).size = readLen by
      rw [ByteArray.size_extract]
      omega]
    rw [extract_extract_BA]
    rw [Nat.add_zero]
    rw [show min (srcAddr + readLen) (srcAddr + len) = srcAddr + readLen by omega]
  · rw [write_eq_gen_from_extend src base srcAddr destAddr len hlen hsrc hdest (by omega)]
    rw [readWithPadding_eq_extract' _ destAddr readLen hreadPosLt hread64 (by
      rw [ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract]
      omega)]
    rw [extract_append_right_window _ _ _ _ (by
      rw [ByteArray.size_extract]
      omega)]
    rw [show destAddr - (base.extract 0 destAddr).size = 0 by
      rw [ByteArray.size_extract]
      omega]
    rw [show destAddr + readLen - (base.extract 0 destAddr).size = readLen by
      rw [ByteArray.size_extract]
      omega]
    rw [extract_extract_BA]
    rw [Nat.add_zero]
    rw [show min (srcAddr + readLen) (srcAddr + len) = srcAddr + readLen by omega]

-- LIBRARY CANDIDATE: read back an interior window of an arbitrary source-window write.
theorem write_from_read_window (src base : ByteArray) (srcAddr destAddr len start readLen : ℕ)
    (hlen : len ≠ 0) (hreadPos : readLen ≠ 0) (hwithin : start + readLen ≤ len)
    (hsrc : srcAddr + len ≤ src.size) (hdest : destAddr ≤ base.size)
    (hread64 : readLen < 2 ^ 64) :
    (src.write srcAddr base destAddr len).readWithPadding (destAddr + start) readLen =
      src.extract (srcAddr + start) (srcAddr + start + readLen) := by
  have hreadPosLt : 0 < readLen := Nat.pos_of_ne_zero hreadPos
  by_cases hin : destAddr + len ≤ base.size
  · rw [write_eq_gen_from src base srcAddr destAddr len hlen hsrc hin]
    have hbasePrefix : (base.extract 0 destAddr).size = destAddr := by
      rw [ByteArray.size_extract]
      omega
    have hsrcPrefix : (src.extract srcAddr (srcAddr + len)).size = len := by
      rw [ByteArray.size_extract]
      omega
    rw [readWithPadding_eq_extract' _ (destAddr + start) readLen hreadPosLt hread64 (by
      rw [ByteArray.size_append, ByteArray.size_append, hbasePrefix, hsrcPrefix,
        ByteArray.size_extract]
      omega)]
    rw [extract_append_left _ _ _ _ (by
      rw [ByteArray.size_append, hbasePrefix, hsrcPrefix]
      omega)]
    rw [extract_append_right_window _ _ _ _ (by rw [hbasePrefix]; omega)]
    rw [hbasePrefix]
    rw [show destAddr + start - destAddr = start by omega]
    rw [show destAddr + start + readLen - destAddr = start + readLen by omega]
    rw [extract_extract_BA]
    rw [show min (srcAddr + (start + readLen)) (srcAddr + len) =
      srcAddr + start + readLen by omega]
  · rw [write_eq_gen_from_extend src base srcAddr destAddr len hlen hsrc hdest (by omega)]
    have hbasePrefix : (base.extract 0 destAddr).size = destAddr := by
      rw [ByteArray.size_extract]
      omega
    have hsrcPrefix : (src.extract srcAddr (srcAddr + len)).size = len := by
      rw [ByteArray.size_extract]
      omega
    rw [readWithPadding_eq_extract' _ (destAddr + start) readLen hreadPosLt hread64 (by
      rw [ByteArray.size_append, hbasePrefix, hsrcPrefix]
      omega)]
    rw [extract_append_right_window _ _ _ _ (by rw [hbasePrefix]; omega)]
    rw [hbasePrefix]
    rw [show destAddr + start - destAddr = start by omega]
    rw [show destAddr + start + readLen - destAddr = start + readLen by omega]
    rw [extract_extract_BA]
    rw [show min (srcAddr + (start + readLen)) (srcAddr + len) =
      srcAddr + start + readLen by omega]

-- GENERALIZES Reasoning.Memory.write32_read_above by allowing an arbitrary in-bounds write
-- length.
theorem write_read_above_gen (src base : ByteArray) (destAddr len readAddr : ℕ)
    (hlen : len ≠ 0) (hsrc : len ≤ src.size) (hin : destAddr + len ≤ base.size)
    (habove : destAddr + len ≤ readAddr) (hread : readAddr + 32 ≤ base.size) :
    (src.write 0 base destAddr len).readWithPadding readAddr 32 =
      base.readWithPadding readAddr 32 := by
  have hbsz : (base.extract 0 destAddr).size = destAddr := by
    rw [ByteArray.size_extract]
    omega
  have hssz : (src.extract 0 len).size = len := by
    rw [ByteArray.size_extract]
    omega
  have hcsz : (base.extract (destAddr + len) base.size).size =
      base.size - (destAddr + len) := by
    rw [ByteArray.size_extract]
    omega
  have habsz : (base.extract 0 destAddr ++ src.extract 0 len).size =
      destAddr + len := by
    rw [ByteArray.size_append, hbsz, hssz]
  rw [write_eq_gen src base destAddr len hlen hsrc hin,
      readWithPadding_eq_extract _ readAddr
        (by rw [ByteArray.size_append, ByteArray.size_append, hbsz, hssz, hcsz]; omega),
      readWithPadding_eq_extract _ readAddr hread,
      extract_append_right_window _ _ _ _ (by rw [habsz]; omega),
      habsz, extract_extract_BA,
      show destAddr + len + (readAddr - (destAddr + len)) = readAddr from by omega,
      show min (destAddr + len + (readAddr + 32 - (destAddr + len))) base.size =
        readAddr + 32 from by omega]

theorem readNat?_some_mload_word {b : ByteArray} {off n : Nat}
    (h : ABI.readNat? b.toList off = some n) :
    UInt256.ofNat (fromByteArrayBigEndian (b.readWithPadding off 32)) =
      UInt256.ofNat n := by
  have hlen : off + 32 ≤ b.size := by
    have hlenList := readNat?_some_length h
    simpa [byteArray_toList_eq] using hlenList
  have hword := readNat?_some_bytesToWord h
  have hreadBytes := decode_word_at_eq_any b off hlen
  have hreadPad :
      b.readWithPadding off 32 = b.readBytes off 32 := by
    apply ByteArray.ext
    apply Array.toList_inj.mp
    rw [← byteArray_toList_eq (b.readWithPadding off 32)]
    rw [readWithPadding_eq_extract b off hlen]
    rw [byteArray_toList_eq (b.extract off (off + 32)), ByteArray.data_extract,
      Array.toList_extract, List.extract_eq_take_drop]
    rw [readBytes_at_toList_any b off hlen]
    simp
  rw [hreadPad]
  rw [← uInt256OfByteArray_eq]
  exact hreadBytes.symm.trans hword

theorem errorStringCopyLen_toNat {n : Nat} (hlo : 4 ≤ n) (hhi : n < UInt256.size) :
    (UInt256.add (UInt256.ofNat n) (UInt256.lnot (⟨3⟩ : UInt256))).toNat = n - 4 := by
  have hlnot : (UInt256.lnot (⟨3⟩ : UInt256)).toNat = UInt256.size - 4 := by
    native_decide
  rw [show UInt256.add (UInt256.ofNat n) (UInt256.lnot (⟨3⟩ : UInt256)) =
    UInt256.ofNat n + UInt256.lnot (⟨3⟩ : UInt256) from rfl]
  rw [uadd_toNat, ulit_toNat' n hhi, hlnot]
  have hge : UInt256.size ≤ n + (UInt256.size - 4) := by omega
  have hlt : n + (UInt256.size - 4) - UInt256.size < UInt256.size := by omega
  rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt hlt]
  omega

theorem errorStringCopyLen_word {n : Nat} (hlo : 4 ≤ n) (hhi : n < UInt256.size) :
    UInt256.add (UInt256.ofNat n) (UInt256.lnot (⟨3⟩ : UInt256)) =
      UInt256.ofNat (n - 4) := by
  apply u256_inj
  rw [errorStringCopyLen_toNat hlo hhi, ulit_toNat' (n - 4) (by omega)]

theorem auctionErrorStringCopy_awCopy_bounds {n : Nat} (hlo : 68 ≤ n)
    (hsmall : n < (2 : Nat) ^ 138) :
    let m := MachineState.M (UInt256.ofNat 5).toNat 128 (n - 4)
    6 ≤ m ∧ m < UInt256.size ∧ m * 32 < UInt256.size ∧
      128 + (n - 4) ≤ m * 32 := by
  intro m
  have hseedNat : (UInt256.ofNat 5).toNat = 5 := by native_decide
  have hseedLt : (UInt256.ofNat 5).toNat < UInt256.size := (UInt256.ofNat 5).val.isLt
  have hseedMulLt : (UInt256.ofNat 5).toNat * 32 < UInt256.size := by
    rw [hseedNat]
    norm_num [UInt256.size]
  have hqGe : 6 ≤ (128 + (n - 4) + 31) / 32 := by
    rw [Nat.le_div_iff_mul_le (by decide : 0 < 32)]
    omega
  have hqCover : 128 + (n - 4) ≤ ((128 + (n - 4) + 31) / 32) * 32 := by
    have hmod := Nat.mod_lt (128 + (n - 4) + 31) (by decide : 0 < 32)
    have hdecomp := Nat.div_add_mod (128 + (n - 4) + 31) 32
    omega
  have hqLt : (128 + (n - 4) + 31) / 32 < UInt256.size := by
    have hle := Nat.div_le_self (128 + (n - 4) + 31) 32
    have hnum : 128 + (n - 4) + 31 < UInt256.size := by
      norm_num [UInt256.size] at *
      omega
    omega
  have hqMulLt : ((128 + (n - 4) + 31) / 32) * 32 < UInt256.size := by
    have hle := Nat.div_mul_le_self (128 + (n - 4) + 31) 32
    have hnum : 128 + (n - 4) + 31 < UInt256.size := by
      norm_num [UInt256.size] at *
      omega
    omega
  have hbaseGe : (128 + (n - 4) + 31) / 32 ≤ m := by
    dsimp [m]
    unfold MachineState.M
    split
    · omega
    · exact Nat.le_max_right _ _
  have hbaseLt : m < UInt256.size := by
    dsimp [m]
    unfold MachineState.M
    split
    · exact hseedLt
    · exact max_lt hseedLt hqLt
  have hbaseMulLt : m * 32 < UInt256.size := by
    dsimp [m]
    unfold MachineState.M
    split
    · exact hseedMulLt
    · rw [max_mul]
      exact max_lt hseedMulLt hqMulLt
  have hbase6 : 6 ≤ m := le_trans hqGe hbaseGe
  have hcover : 128 + (n - 4) ≤ m * 32 :=
    le_trans hqCover (Nat.mul_le_mul_right 32 hbaseGe)
  exact ⟨hbase6, hbaseLt, hbaseMulLt, hcover⟩

theorem auctionErrorStringCopy_awLoad_bounds {n : Nat} {aw : UInt256} (hlo : 68 ≤ n)
    (hsmall : n < (2 : Nat) ^ 138)
    (haw : aw.toNat = MachineState.M (UInt256.ofNat 5).toNat 128 (n - 4)) :
    let m := MachineState.M aw.toNat 128 32
    aw.toNat ≤ m ∧ m < UInt256.size ∧ m * 32 < UInt256.size := by
  intro m
  have hbase := auctionErrorStringCopy_awCopy_bounds hlo hsmall
  have hAwLt : aw.toNat < UInt256.size := by
    rw [haw]
    exact hbase.2.1
  have hAwMulLt : aw.toNat * 32 < UInt256.size := by
    rw [haw]
    exact hbase.2.2.1
  dsimp [m]
  unfold MachineState.M
  split
  · omega
  · constructor
    · exact Nat.le_max_left _ _
    · constructor
      · exact max_lt hAwLt (by norm_num [UInt256.size])
      · rw [max_mul]
        exact max_lt hAwMulLt (by norm_num [UInt256.size])

theorem auctionErrorStringCopy_awDecoded_bounds {n off : Nat} (hlo : 68 ≤ n)
    (hsmall : n < (2 : Nat) ^ 138) (hoffBound : off + 36 ≤ n)
    (hosz : n < UInt256.size) :
    let copyLen := UInt256.lnot (⟨3⟩ : UInt256) + UInt256.ofNat n
    let aw64 := UInt256.ofNat
      (MachineState.M (UInt256.ofNat 5).toNat (⟨64⟩ : UInt256).toNat 32)
    let awCopy := UInt256.ofNat (MachineState.M aw64.toNat 128 copyLen.toNat)
    let awOff := UInt256.ofNat
      (MachineState.M awCopy.toNat (⟨128⟩ : UInt256).toNat 32)
    let awLen := UInt256.ofNat
      (MachineState.M awOff.toNat ((⟨128⟩ : UInt256) + UInt256.ofNat off).toNat 32)
    3 ≤ awLen.toNat ∧ awLen.toNat * 32 < UInt256.size := by
  intro copyLen aw64 awCopy awOff awLen
  have hcopyLen : copyLen.toNat = n - 4 := by
    dsimp [copyLen]
    rw [u256_add_comm]
    exact errorStringCopyLen_toNat (n := n) (by omega) hosz
  have hbase := auctionErrorStringCopy_awCopy_bounds hlo hsmall
  have hceil64 : (((⟨64⟩ : UInt256).toNat + 32 + 31) / 32) = 3 := by
    native_decide
  have haw64 : aw64.toNat = (UInt256.ofNat 5).toNat := by
    dsimp [aw64]
    have hMlt :
        MachineState.M (UInt256.ofNat 5).toNat (⟨64⟩ : UInt256).toNat 32 <
          UInt256.size := by
      dsimp [MachineState.M]
      rw [hceil64]
      apply max_lt (UInt256.ofNat 5).val.isLt
      norm_num [UInt256.size]
    rw [UInt256.toNat_ofNat_of_lt hMlt]
    dsimp [MachineState.M]
    rw [hceil64, max_eq_left]
    native_decide
  have hawCopyNat : awCopy.toNat = MachineState.M (UInt256.ofNat 5).toNat 128 (n - 4) := by
    dsimp [awCopy]
    have hMlt : MachineState.M aw64.toNat 128 copyLen.toNat < UInt256.size := by
      rw [haw64, hcopyLen]
      exact hbase.2.1
    rw [UInt256.toNat_ofNat_of_lt hMlt, haw64, hcopyLen]
  have hload := auctionErrorStringCopy_awLoad_bounds hlo hsmall hawCopyNat
  have hawOffNat :
      awOff.toNat = MachineState.M awCopy.toNat (⟨128⟩ : UInt256).toNat 32 := by
    dsimp [awOff]
    have hMlt : MachineState.M awCopy.toNat (⟨128⟩ : UInt256).toNat 32 <
        UInt256.size := by
      simpa using hload.2.1
    rw [UInt256.toNat_ofNat_of_lt hMlt]
  have hawOffMul : awOff.toNat * 32 < UInt256.size := by
    rw [hawOffNat]
    exact hload.2.2
  have hawOffGe : 6 ≤ awOff.toNat := by
    rw [hawOffNat]
    have hawCopyGe : 6 ≤ awCopy.toNat := by
      rw [hawCopyNat]
      exact hbase.1
    exact le_trans hawCopyGe hload.1
  have hoffLt' : off < UInt256.size := by
    norm_num [UInt256.size] at hsmall ⊢
    omega
  have haddrNat : (((⟨128⟩ : UInt256) + UInt256.ofNat off).toNat) = 128 + off := by
    rw [uadd_toNat, show (⟨128⟩ : UInt256).toNat = 128 from by decide,
      UInt256.toNat_ofNat_of_lt hoffLt']
    rw [Nat.mod_eq_of_lt]
    norm_num [UInt256.size] at hsmall ⊢
    omega
  have hcover : 128 + off + 32 ≤ awOff.toNat * 32 := by
    have hcopyCover : 128 + (n - 4) ≤ awCopy.toNat * 32 := by
      rw [hawCopyNat]
      exact hbase.2.2.2
    have hcopyLe : awCopy.toNat ≤ awOff.toNat := by
      rw [hawOffNat]
      exact hload.1
    have hcoverOff : 128 + off + 32 ≤ 128 + (n - 4) := by
      omega
    exact le_trans hcoverOff (le_trans hcopyCover (Nat.mul_le_mul_right 32 hcopyLe))
  have hceilLe : (((128 + off) + 32 + 31) / 32) ≤ awOff.toNat := by
    rw [Nat.div_le_iff_le_mul_add_pred (by decide : 0 < 32)]
    omega
  have hawLenNat : awLen.toNat = awOff.toNat := by
    dsimp [awLen]
    have hMlt :
        MachineState.M awOff.toNat (((⟨128⟩ : UInt256) + UInt256.ofNat off).toNat) 32 <
          UInt256.size := by
      dsimp [MachineState.M]
      rw [haddrNat]
      apply max_lt awOff.val.isLt
      exact lt_of_le_of_lt hceilLe awOff.val.isLt
    rw [UInt256.toNat_ofNat_of_lt hMlt]
    dsimp [MachineState.M]
    rw [haddrNat, max_eq_left hceilLe]
  constructor
  · rw [hawLenNat]
    exact le_trans (by decide : 3 ≤ 6) hawOffGe
  · rw [hawLenNat]
    exact hawOffMul

theorem auctionMintFailureMemSel_read64 (I : ExecutionEnv) {o : ByteArray}
    (ho32 : 32 ≤ o.size) (hosz : o.size < UInt256.size) :
    let mintFailureMem :=
      o.write 0 (auctionUnpauseMintSelMem I) 128
        ((⟨32⟩ : UInt256) ⊓ UInt256.ofNat o.size).toNat
    (o.write 0 mintFailureMem 0 4).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  intro mintFailureMem
  have hbaseSize : mintFailureMem.size = 160 := by
    simpa [mintFailureMem] using auctionUnpauseMintCallMem_size_eq160 I ho32 hosz
  have hbaseRead :
      mintFailureMem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    simpa [mintFailureMem] using auctionUnpauseMintCallMem_read64 I hosz
  have hpres := write_read_above_gen o mintFailureMem 0 4 64 (by decide) (by omega)
    (by rw [hbaseSize]; omega) (by omega) (by rw [hbaseSize]; omega)
  exact hpres.trans hbaseRead

theorem auctionMintFailureMemSel_mload64 (I : ExecutionEnv) {o : ByteArray}
    (ho32 : 32 ≤ o.size) (hosz : o.size < UInt256.size) :
    let mintFailureMem :=
      o.write 0 (auctionUnpauseMintSelMem I) 128
        ((⟨32⟩ : UInt256) ⊓ UInt256.ofNat o.size).toNat
    let memSel := o.write 0 mintFailureMem 0 4
    (if (⟨64⟩ : UInt256).toNat ≥ memSel.size ∨
        (⟨64⟩ : UInt256) ≥ UInt256.ofNat 5 * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian (memSel.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
      ⟨128⟩ := by
  intro mintFailureMem memSel
  have hbaseSize : mintFailureMem.size = 160 := by
    simpa [mintFailureMem] using auctionUnpauseMintCallMem_size_eq160 I ho32 hosz
  have hmemSelSize : 64 < memSel.size := by
    have hwrite := write_eq_gen o mintFailureMem 0 4 (by decide) (by omega)
      (by rw [hbaseSize]; omega)
    change 64 < (o.write 0 mintFailureMem 0 4).size
    rw [hwrite, ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
      ByteArray.size_extract, ByteArray.size_extract, hbaseSize]
    omega
  exact mloadFreePtrValue hmemSelSize (by decide)
    (by simpa [mintFailureMem, memSel] using auctionMintFailureMemSel_read64 I ho32 hosz)

theorem auctionMintFailureMemSel_size_ge128 (I : ExecutionEnv) {o : ByteArray}
    (ho32 : 32 ≤ o.size) (hosz : o.size < UInt256.size) :
    let mintFailureMem :=
      o.write 0 (auctionUnpauseMintSelMem I) 128
        ((⟨32⟩ : UInt256) ⊓ UInt256.ofNat o.size).toNat
    128 ≤ (o.write 0 mintFailureMem 0 4).size := by
  intro mintFailureMem
  have hbaseSize : mintFailureMem.size = 160 := by
    simpa [mintFailureMem] using auctionUnpauseMintCallMem_size_eq160 I ho32 hosz
  have hwrite := write_eq_gen o mintFailureMem 0 4 (by decide) (by omega)
    (by rw [hbaseSize]; omega)
  change 128 ≤ (o.write 0 mintFailureMem 0 4).size
  rw [hwrite, ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract, hbaseSize]
  omega

theorem auctionErrorStringCopy_mloadOffset (I : ExecutionEnv) {o : ByteArray} {off : Nat}
    (hlong : 68 ≤ o.size) (hosz : o.size < UInt256.size)
    (hsmall : o.size < (2 : Nat) ^ 138)
    (hoff : ABI.readNat? (o.extract 4 o.size).toList 0 = some off) :
    let mintFailureMem :=
      o.write 0 (auctionUnpauseMintSelMem I) 128
        ((⟨32⟩ : UInt256) ⊓ UInt256.ofNat o.size).toNat
    let memSel := o.write 0 mintFailureMem 0 4
    let copyLen := UInt256.lnot (⟨3⟩ : UInt256) + UInt256.ofNat o.size
    let memCopy := o.write 4 memSel 128 copyLen.toNat
    let awCopy := UInt256.ofNat (MachineState.M (UInt256.ofNat 5).toNat 128 copyLen.toNat)
    (if (⟨128⟩ : UInt256).toNat ≥ memCopy.size ∨
        (⟨128⟩ : UInt256) ≥ awCopy * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian (memCopy.readWithPadding (⟨128⟩ : UInt256).toNat 32))) =
      UInt256.ofNat off := by
  intro mintFailureMem memSel copyLen memCopy awCopy
  have hcopyNat : copyLen.toNat = o.size - 4 := by
    dsimp [copyLen]
    rw [u256_add_comm]
    exact errorStringCopyLen_toNat (n := o.size) (by omega) hosz
  have hread : memCopy.readWithPadding 128 32 =
      (o.extract 4 o.size).readWithPadding 0 32 := by
    dsimp [memCopy]
    rw [hcopyNat]
    have hsrc : 4 + (o.size - 4) ≤ o.size := by omega
    have hdest : 128 ≤ memSel.size := by
      dsimp [memSel, mintFailureMem]
      simpa [mintFailureMem] using
        auctionMintFailureMemSel_size_ge128 I (by omega : 32 ≤ o.size) hosz
    have hwin := write_from_read_back_prefix o memSel 4 128 (o.size - 4) 32
      (by omega) (by decide) (by omega) hsrc hdest (by norm_num)
    have hret : (o.extract 4 o.size).readWithPadding 0 32 = o.extract 4 36 := by
      rw [readWithPadding_eq_extract' _ 0 32 (by norm_num) (by norm_num) (by
        rw [ByteArray.size_extract]
        omega)]
      rw [extract_extract_BA]
      rw [show 4 + 0 = 4 by omega]
      rw [show 4 + 32 = 36 by omega]
      rw [show min 36 o.size = 36 by omega]
    exact hwin.trans hret.symm
  have hoffWord := readNat?_some_mload_word (b := o.extract 4 o.size) (off := 0) hoff
  have hword : UInt256.ofNat (fromByteArrayBigEndian (memCopy.readWithPadding 128 32)) =
      UInt256.ofNat off := by
    rw [hread]
    simpa using hoffWord
  have hmemSize : ¬ (128 ≥ memCopy.size) := by
    dsimp [memCopy]
    rw [hcopyNat]
    have hsrc : 4 + (o.size - 4) ≤ o.size := by omega
    have hdest : 128 ≤ memSel.size := by
      dsimp [memSel, mintFailureMem]
      simpa [mintFailureMem] using
        auctionMintFailureMemSel_size_ge128 I (by omega : 32 ≤ o.size) hosz
    by_cases hin : 128 + (o.size - 4) ≤ memSel.size
    · rw [write_eq_gen_from o memSel 4 128 (o.size - 4) (by omega) hsrc hin]
      rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
        ByteArray.size_extract, ByteArray.size_extract]
      omega
    · rw [write_eq_gen_from_extend o memSel 4 128 (o.size - 4) (by omega) hsrc hdest
        (by omega)]
      rw [ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract]
      omega
  have haw : ¬ ((⟨128⟩ : UInt256) ≥ awCopy * ⟨32⟩) := by
    have hbounds := auctionErrorStringCopy_awCopy_bounds (n := o.size) hlong hsmall
    have hawCopyNoWrap :
        awCopy.toNat = MachineState.M (UInt256.ofNat 5).toNat 128 (o.size - 4) := by
      dsimp [awCopy]
      rw [hcopyNat]
      exact UInt256.toNat_ofNat_of_lt hbounds.2.1
    have hmul : (awCopy * ⟨32⟩).toNat = awCopy.toNat * 32 := by
      rw [umul_toNat _ _ (by
        rw [hawCopyNoWrap, show (⟨32⟩ : UInt256).toNat = 32 from by native_decide]
        exact hbounds.2.2.1)]
      rw [show (⟨32⟩ : UInt256).toNat = 32 from by native_decide]
    intro h
    change (awCopy * ⟨32⟩).toNat ≤ (⟨128⟩ : UInt256).toNat at h
    rw [show (⟨128⟩ : UInt256).toNat = 128 from by native_decide] at h
    rw [hmul, hawCopyNoWrap] at h
    have hcover := hbounds.2.2.2
    omega
  split_ifs with hif
  · rcases hif with hbad | hbad
    · exact False.elim (hmemSize hbad)
    · exact False.elim (haw hbad)
  · exact hword

theorem auctionErrorStringCopy_mloadLength (I : ExecutionEnv) {o : ByteArray} {off len : Nat}
    (hlong : 68 ≤ o.size) (hosz : o.size < UInt256.size)
    (hsmall : o.size < (2 : Nat) ^ 138)
    (hoffBound : off + 36 ≤ o.size)
    (hlen : ABI.readNat? (o.extract 4 o.size).toList off = some len) :
    let mintFailureMem :=
      o.write 0 (auctionUnpauseMintSelMem I) 128
        ((⟨32⟩ : UInt256) ⊓ UInt256.ofNat o.size).toNat
    let memSel := o.write 0 mintFailureMem 0 4
    let copyLen := UInt256.lnot (⟨3⟩ : UInt256) + UInt256.ofNat o.size
    let memCopy := o.write 4 memSel 128 copyLen.toNat
    let awCopy := UInt256.ofNat (MachineState.M (UInt256.ofNat 5).toNat 128 copyLen.toNat)
    let offW := UInt256.ofNat off
    let awOff := UInt256.ofNat (MachineState.M awCopy.toNat 128 32)
    (if (⟨128⟩ + offW).toNat ≥ memCopy.size ∨
        (⟨128⟩ + offW) ≥ awOff * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian (memCopy.readWithPadding (⟨128⟩ + offW).toNat 32))) =
      UInt256.ofNat len := by
  intro mintFailureMem memSel copyLen memCopy awCopy offW awOff
  have hcopyNat : copyLen.toNat = o.size - 4 := by
    dsimp [copyLen]
    rw [u256_add_comm]
    exact errorStringCopyLen_toNat (n := o.size) (by omega) hosz
  have hoffLt : off < UInt256.size := by
    have hlt : off + 36 < UInt256.size := by omega
    omega
  have hoffWNat : offW.toNat = off := by
    dsimp [offW]
    exact UInt256.toNat_ofNat_of_lt hoffLt
  have haddrNat : ((⟨128⟩ : UInt256) + offW).toNat = 128 + off := by
    rw [uadd_toNat, hoffWNat, show (⟨128⟩ : UInt256).toNat = 128 from by decide]
    rw [Nat.mod_eq_of_lt]
    norm_num [UInt256.size] at hsmall ⊢
    omega
  have hread : memCopy.readWithPadding (128 + off) 32 =
      (o.extract 4 o.size).readWithPadding off 32 := by
    dsimp [memCopy]
    rw [hcopyNat]
    have hsrc : 4 + (o.size - 4) ≤ o.size := by omega
    have hdest : 128 ≤ memSel.size := by
      dsimp [memSel, mintFailureMem]
      simpa [mintFailureMem] using
        auctionMintFailureMemSel_size_ge128 I (by omega : 32 ≤ o.size) hosz
    have hwin := write_from_read_window o memSel 4 128 (o.size - 4) off 32
      (by omega) (by decide) (by omega) hsrc hdest (by norm_num)
    have hret :
        (o.extract 4 o.size).readWithPadding off 32 =
          o.extract (4 + off) (4 + (off + 32)) := by
      rw [readWithPadding_eq_extract' _ off 32 (by norm_num) (by norm_num) (by
        rw [ByteArray.size_extract]
        omega)]
      rw [extract_extract_BA]
      rw [show min (4 + (off + 32)) o.size = 4 + (off + 32) by omega]
    exact hwin.trans hret.symm
  have hlenWord := readNat?_some_mload_word (b := o.extract 4 o.size) hlen
  have hword :
      UInt256.ofNat (fromByteArrayBigEndian (memCopy.readWithPadding (128 + off) 32)) =
        UInt256.ofNat len := by
    rw [hread]
    simpa using hlenWord
  have hmemSize : ¬ (128 + off ≥ memCopy.size) := by
    dsimp [memCopy]
    rw [hcopyNat]
    have hsrc : 4 + (o.size - 4) ≤ o.size := by omega
    have hdest : 128 ≤ memSel.size := by
      dsimp [memSel, mintFailureMem]
      simpa [mintFailureMem] using
        auctionMintFailureMemSel_size_ge128 I (by omega : 32 ≤ o.size) hosz
    by_cases hin : 128 + (o.size - 4) ≤ memSel.size
    · rw [write_eq_gen_from o memSel 4 128 (o.size - 4) (by omega) hsrc hin]
      rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
        ByteArray.size_extract, ByteArray.size_extract]
      omega
    · rw [write_eq_gen_from_extend o memSel 4 128 (o.size - 4) (by omega) hsrc hdest
        (by omega)]
      rw [ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract]
      omega
  have hawCopyNoWrap : awCopy.toNat =
      MachineState.M (UInt256.ofNat 5).toNat 128 (o.size - 4) := by
    have hbounds := auctionErrorStringCopy_awCopy_bounds (n := o.size) hlong hsmall
    dsimp [awCopy]
    rw [hcopyNat]
    exact UInt256.toNat_ofNat_of_lt hbounds.2.1
  have haw : ¬ ((⟨128⟩ + offW : UInt256) ≥ awOff * ⟨32⟩) := by
    have hbounds := auctionErrorStringCopy_awCopy_bounds (n := o.size) hlong hsmall
    have hboundsOff :=
      auctionErrorStringCopy_awLoad_bounds (n := o.size) hlong hsmall hawCopyNoWrap
    have hawOffNoWrap : awOff.toNat = MachineState.M awCopy.toNat 128 32 := by
      dsimp [awOff]
      exact UInt256.toNat_ofNat_of_lt hboundsOff.2.1
    have hmul : (awOff * ⟨32⟩).toNat = awOff.toNat * 32 := by
      rw [umul_toNat _ _ (by
        rw [hawOffNoWrap, show (⟨32⟩ : UInt256).toNat = 32 from by native_decide]
        exact hboundsOff.2.2)]
      rw [show (⟨32⟩ : UInt256).toNat = 32 from by native_decide]
    intro h
    change (awOff * ⟨32⟩).toNat ≤ ((⟨128⟩ + offW : UInt256)).toNat at h
    rw [haddrNat, hmul, hawOffNoWrap] at h
    have hcover := hbounds.2.2.2
    have hmono := Nat.mul_le_mul_right 32 hboundsOff.1
    omega
  split_ifs with hif
  · rcases hif with hbad | hbad
    · rw [haddrNat] at hbad
      exact False.elim (hmemSize hbad)
    · exact False.elim (haw hbad)
  · rw [haddrNat]
    exact hword

set_option maxHeartbeats 1000000 in
theorem auctionCreateAuction_mintCallFailureErrorStringToDecoder {cA gh bl σInit σ₀ A I}
    {g : Sat256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {k C : ℕ} {d0 d1 d2 preSel : UInt256} {R : List UInt256}
    (rd : RD auctionBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨3067⟩
      (⟨0⟩ :: d0 :: d1 :: d2 :: R) mem (UInt256.ofNat 5) o acc k C)
    (hlen : 4 ≤ o.size) (hosz : o.size < UInt256.size)
    (hword :
      (if (⟨0⟩ : UInt256).toNat ≥ (o.write 0 mem 0 4).size ∨
          (⟨0⟩ : UInt256) ≥ UInt256.ofNat 5 * ⟨32⟩ then ⟨0⟩
        else UInt256.ofNat
          (fromByteArrayBigEndian ((o.write 0 mem 0 4).readWithPadding
            (⟨0⟩ : UInt256).toNat 32))) = preSel)
    (hshr : UInt256.shiftRight preSel ⟨224⟩ = (⟨0x08c379a0⟩ : UInt256))
    (hov : R.length + 8 ≤ 1024) :
    ∃ k' C', RD auctionBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨5926⟩
      (⟨3143⟩ :: R) (o.write 0 mem 0 4) (UInt256.ofNat 5) o acc k' C' := by
  obtain ⟨_, _, rd3123⟩ :=
    auctionCreateAuction_mintCallFailureSelectorToSwitch rd hlen hosz hword hshr hov
  have rd3134₀ := evm_run rd3123 with [dup1, push4 ⟨0x08c379a0⟩, sub]
  have rd3134 := rd3134₀
  rw [show UInt256.sub (⟨0x08c379a0⟩ : UInt256) ⟨0x08c379a0⟩ = ⟨0⟩ by decide]
    at rd3134
  exact ⟨_, _, evm_run rd3134 with [push2 ⟨3162⟩, jumpiNT (by decide), pop,
    push2 ⟨3143⟩, push2 ⟨5925⟩, jump (by jump_dest), jumpdest]⟩

set_option maxHeartbeats 1000000 in
theorem auctionCreateAuction_errorStringDecoderLongGuard {cA gh bl σInit σ₀ A I}
    {g : Sat256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {aw : UInt256} {k C : ℕ} {R : List UInt256}
    (rd : RD auctionBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨5926⟩
      (⟨3143⟩ :: R) mem aw o acc k C)
    (hlong : 68 ≤ o.size) (hosz : o.size < UInt256.size)
    (hov : R.length + 4 ≤ 1024) :
    ∃ k' C', RD auctionBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨5939⟩
      (⟨0⟩ :: ⟨3143⟩ :: R) mem aw o acc k' C' := by
  have hlt : UInt256.lt (UInt256.ofNat o.size) (⟨68⟩ : UInt256) = ⟨0⟩ := by
    apply ult_zero
    change (⟨68⟩ : UInt256).toNat ≤ (UInt256.ofNat o.size).toNat
    rw [UInt256.toNat_ofNat_of_lt hosz]
    simpa using hlong
  have rd5931₀ := evm_run rd with [push0, push1 ⟨68⟩, returndatasize, lt]
  have rd5931 := rd5931₀
  rw [hlt] at rd5931
  have rd5932₀ := evm_run rd5931 with [iszero]
  have rd5932 := rd5932₀
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd5932
  exact ⟨_, _, evm_run rd5932 with [push2 ⟨5938⟩, jumpiT (by decide) (by jump_dest),
    jumpdest]⟩

set_option maxHeartbeats 1000000 in
theorem auctionCreateAuction_errorStringDecoderLoadFreePtr {cA gh bl σInit σ₀ A I}
    {g : Sat256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {aw fmp : UInt256} {k C : ℕ} {R : List UInt256}
    (rd : RD auctionBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨5939⟩
      (⟨0⟩ :: ⟨3143⟩ :: R) mem aw o acc k C)
    (hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size ∨ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        fmp)
    (hov : R.length + 3 ≤ 1024) :
    ∃ k' C', RD auctionBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨5942⟩
      (fmp :: ⟨0⟩ :: ⟨3143⟩ :: R) mem
      (UInt256.ofNat (MachineState.M aw.toNat (⟨64⟩ : UInt256).toNat 32)) o acc k' C' := by
  let awLoad := UInt256.ofNat (MachineState.M aw.toNat (⟨64⟩ : UInt256).toNat 32)
  have rd5941 := RD.push1 rd ⟨64⟩ (by decide)
    (by simp only [List.length_cons]; omega)
  have rd5942 := RD.mload (Cₘ awLoad - Cₘ aw) fmp awLoad rd5941 (by decide)
    (fun _ haws hstks => auctionMloadCost_of_stack haws hstks (by rfl))
    hmload64 (by rfl)
    (by simp only [List.length_cons]; omega)
  exact ⟨_, _, by simpa [awLoad] using rd5942⟩

set_option maxHeartbeats 1000000 in
theorem auctionCreateAuction_errorStringDecoderPrepareCopy {cA gh bl σInit σ₀ A I}
    {g : Sat256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {aw fmp : UInt256} {k C : ℕ} {R : List UInt256}
    (rd : RD auctionBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨5942⟩
      (fmp :: ⟨0⟩ :: ⟨3143⟩ :: R) mem aw o acc k C)
    (hov : R.length + 8 ≤ 1024) :
    ∃ k' C', RD auctionBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨5951⟩
      (fmp :: ⟨4⟩ :: (UInt256.lnot (⟨3⟩ : UInt256) + UInt256.ofNat o.size) ::
        UInt256.lnot (⟨3⟩ : UInt256) :: fmp :: ⟨0⟩ :: ⟨3143⟩ :: R)
      mem aw o acc k' C' := by
  have rd5944 := RD.push1 rd ⟨3⟩ (by decide)
    (by simp only [List.length_cons]; omega)
  have rd5945 := RD.not rd5944 (by decide)
    (by simp only [List.length_cons]; omega)
  have rd5946 := RD.returndatasize rd5945 (by decide)
    (by simp only [List.length_cons]; omega)
  have rd5947 := RD.dup2 rd5946 (by decide)
    (by simp only [List.length_cons]; omega)
  have rd5948 := RD.add rd5947 (by decide)
    (by simp only [List.length_cons]; omega)
  have rd5950 := RD.push1 rd5948 ⟨4⟩ (by decide)
    (by simp only [List.length_cons]; omega)
  have rd5951 := RD.dup4 rd5950 (by decide)
    (by simp only [List.length_cons]; omega)
  exact ⟨_, _, by simpa using rd5951⟩

set_option maxHeartbeats 1000000 in
theorem auctionCreateAuction_errorStringDecoderReturndataCopy {cA gh bl σInit σ₀ A I}
    {g : Sat256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {aw fmp copyLen : UInt256} {k C : ℕ} {R : List UInt256}
    (rd : RD auctionBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨5951⟩
      (fmp :: ⟨4⟩ :: copyLen :: UInt256.lnot (⟨3⟩ : UInt256) :: fmp :: ⟨0⟩ ::
        ⟨3143⟩ :: R) mem aw o acc k C)
    (hcopyLen : copyLen = UInt256.lnot (⟨3⟩ : UInt256) + UInt256.ofNat o.size)
    (hlong : 68 ≤ o.size) (hosz : o.size < UInt256.size) (hov : R.length + 4 ≤ 1024) :
    ∃ k' C', RD auctionBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨5952⟩
      (UInt256.lnot (⟨3⟩ : UInt256) :: fmp :: ⟨0⟩ :: ⟨3143⟩ :: R)
      (o.write 4 mem fmp.toNat copyLen.toNat)
      (UInt256.ofNat (MachineState.M aw.toNat fmp.toNat copyLen.toNat)) o acc k' C' := by
  have hcopyNat : copyLen.toNat = o.size - 4 := by
    rw [hcopyLen, u256_add_comm]
    exact errorStringCopyLen_toNat (n := o.size) (by omega) hosz
  have rd5952 := RD.returndatacopy
    (Cₘ (UInt256.ofNat (MachineState.M aw.toNat fmp.toNat copyLen.toNat)) - Cₘ aw)
    (o.write 4 mem fmp.toNat copyLen.toNat)
    (UInt256.ofNat (MachineState.M aw.toNat fmp.toNat copyLen.toNat))
    rd (by decide)
    (by
      change 4 + copyLen.toNat ≤ o.size
      rw [hcopyNat]
      omega)
    (fun s haw hstk => by
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk])
    (by rfl) (by rfl)
    (by simp only [List.length_cons]; omega)
  exact ⟨_, _, rd5952⟩

set_option maxHeartbeats 1000000 in
theorem auctionCreateAuction_errorStringDecoderLoadOffset {cA gh bl σInit σ₀ A I}
    {g : Sat256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {aw fmp off : UInt256} {k C : ℕ} {R : List UInt256}
    (rd : RD auctionBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨5952⟩
      (UInt256.lnot (⟨3⟩ : UInt256) :: fmp :: ⟨0⟩ :: ⟨3143⟩ :: R)
      mem aw o acc k C)
    (hmloadFmp :
      (if fmp.toNat ≥ mem.size ∨ fmp ≥ aw * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding fmp.toNat 32))) =
        off)
    (hov : R.length + 6 ≤ 1024) :
    ∃ k' C', RD auctionBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨5954⟩
      (off :: UInt256.lnot (⟨3⟩ : UInt256) :: fmp :: ⟨0⟩ :: ⟨3143⟩ :: R)
      mem (UInt256.ofNat (MachineState.M aw.toNat fmp.toNat 32)) o acc k' C' := by
  let awLoad := UInt256.ofNat (MachineState.M aw.toNat fmp.toNat 32)
  have rd5953 := RD.dup2 rd (by decide)
    (by simp only [List.length_cons]; omega)
  have rd5954 := RD.mload (Cₘ awLoad - Cₘ aw) off awLoad rd5953 (by decide)
    (fun _ haws hstks => auctionMloadCost_of_stack haws hstks (by rfl))
    hmloadFmp (by rfl)
    (by simp only [List.length_cons]; omega)
  exact ⟨_, _, by simpa [awLoad] using rd5954⟩

set_option maxHeartbeats 1000000 in
theorem auctionCreateAuction_errorStringDecoderOffsetBoundsOk {cA gh bl σInit σ₀ A I}
    {g : Sat256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {aw off : UInt256} {k C : ℕ} {R : List UInt256}
    (rd : RD auctionBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨5954⟩
      (off :: UInt256.lnot (⟨3⟩ : UInt256) :: R) mem aw o acc k C)
    (hoffMax : off.toNat ≤ ABI.solcMaxU64)
    (hoffBound : off.toNat + 36 ≤ o.size)
    (hosz : o.size < UInt256.size) (hov : R.length + 8 ≤ 1024) :
    ∃ k' C', RD auctionBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨5987⟩
      (⟨0xffffffffffffffff⟩ :: UInt256.ofNat o.size :: off ::
        UInt256.lnot (⟨3⟩ : UInt256) :: R)
      mem aw o acc k' C' := by
  let max64 : UInt256 := ⟨0xffffffffffffffff⟩
  have hoffAddNat : (off + (⟨36⟩ : UInt256)).toNat = off.toNat + 36 := by
    rw [uadd_toNat, show (⟨36⟩ : UInt256).toNat = 36 from by decide]
    rw [Nat.mod_eq_of_lt]
    have hmax : ABI.solcMaxU64 + 36 < UInt256.size := by
      norm_num [ABI.solcMaxU64, UInt256.size]
    omega
  have hgtLen : UInt256.gt (off + (⟨36⟩ : UInt256)) (UInt256.ofNat o.size) = ⟨0⟩ := by
    apply ugt_zero
    rw [hoffAddNat, UInt256.toNat_ofNat_of_lt hosz]
    exact hoffBound
  have hgtMax : UInt256.gt off max64 = ⟨0⟩ := by
    apply ugt_zero
    change off.toNat ≤ max64.toNat
    simp [max64]
    exact hoffMax
  have rd5955 := RD.returndatasize rd (by decide)
    (by simp only [List.length_cons]; omega)
  have rd5964 := RD.pushConst rd5955 max64 (width := 8) (op := .PUSH8)
    (by decide) (by decide) (by simp only [List.length_cons]; omega)
  have rd5965 := RD.dup2 rd5964 (by decide)
    (by simp only [List.length_cons]; omega)
  have rd5967 := RD.push1 rd5965 ⟨36⟩ (by decide)
    (by simp only [List.length_cons]; omega)
  have rd5968 := RD.dup5 rd5967 (by decide)
    (by simp only [List.length_cons]; omega)
  have rd5969 := RD.add rd5968 (by decide)
    (by simp only [List.length_cons]; omega)
  have rd5970₀ := RD.gt rd5969 (by decide)
    (by simp only [List.length_cons]; omega)
  have rd5970 := rd5970₀
  rw [hgtLen] at rd5970
  have rd5971 := RD.dup2 rd5970 (by decide)
    (by simp only [List.length_cons]; omega)
  have rd5972 := RD.dup5 rd5971 (by decide)
    (by simp only [List.length_cons]; omega)
  have rd5973₀ := RD.gt rd5972 (by decide)
    (by simp only [List.length_cons]; omega)
  have rd5973 := rd5973₀
  rw [hgtMax] at rd5973
  have rd5974₀ := RD.lor rd5973 (by decide)
    (by simp only [List.length_cons]; omega)
  have rd5974 := rd5974₀
  rw [show UInt256.lor (⟨0⟩ : UInt256) ⟨0⟩ = ⟨0⟩ by decide] at rd5974
  have rd5975₀ := RD.iszero rd5974 (by decide)
    (by simp only [List.length_cons]; omega)
  have rd5975 := rd5975₀
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd5975
  have rd5986 := RD.push2 rd5975 ⟨5986⟩ (by decide)
    (by simp only [List.length_cons]; omega)
  have rd5986' := RD.jumpiT rd5986 (by decide) (by decide) (by jump_dest)
    (by simp only [List.length_cons]; omega)
  have rd5987 := RD.jumpdest rd5986' (by decide)
    (by simp only [List.length_cons]; omega)
  exact ⟨_, _, by simpa [max64] using rd5987⟩

set_option maxHeartbeats 1000000 in
theorem auctionCreateAuction_errorStringDecoderOffsetBoundsFail {cA gh bl σInit σ₀ A I}
    {g : Sat256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {aw off fmp : UInt256} {k C : ℕ} {R : List UInt256}
    (rd : RD auctionBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨5954⟩
      (off :: UInt256.lnot (⟨3⟩ : UInt256) :: fmp :: ⟨0⟩ :: ⟨3143⟩ :: R)
      mem aw o acc k C)
    (hguard :
      UInt256.lor (UInt256.gt off (⟨0xffffffffffffffff⟩ : UInt256))
          (UInt256.gt (off + (⟨36⟩ : UInt256)) (UInt256.ofNat o.size)) ≠
        ⟨0⟩)
    (hov : R.length + 12 ≤ 1024) :
    ∃ k' C', RD auctionBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨3143⟩
      (⟨0⟩ :: R) mem aw o acc k' C' := by
  let max64 : UInt256 := ⟨0xffffffffffffffff⟩
  have rd5955 := RD.returndatasize rd (by decide)
    (by simp only [List.length_cons]; omega)
  have rd5964 := RD.pushConst rd5955 max64 (width := 8) (op := .PUSH8)
    (by decide) (by decide) (by simp only [List.length_cons]; omega)
  have rd5965 := RD.dup2 rd5964 (by decide)
    (by simp only [List.length_cons]; omega)
  have rd5967 := RD.push1 rd5965 ⟨36⟩ (by decide)
    (by simp only [List.length_cons]; omega)
  have rd5968 := RD.dup5 rd5967 (by decide)
    (by simp only [List.length_cons]; omega)
  have rd5969 := RD.add rd5968 (by decide)
    (by simp only [List.length_cons]; omega)
  have rd5970 := RD.gt rd5969 (by decide)
    (by simp only [List.length_cons]; omega)
  have rd5971 := RD.dup2 rd5970 (by decide)
    (by simp only [List.length_cons]; omega)
  have rd5972 := RD.dup5 rd5971 (by decide)
    (by simp only [List.length_cons]; omega)
  have rd5973 := RD.gt rd5972 (by decide)
    (by simp only [List.length_cons]; omega)
  have rd5974 := RD.lor rd5973 (by decide)
    (by simp only [List.length_cons]; omega)
  have hcond :
      UInt256.isZero
          (UInt256.lor (UInt256.gt off max64)
            (UInt256.gt (off + (⟨36⟩ : UInt256)) (UInt256.ofNat o.size))) =
        ⟨0⟩ := by
    exact isZero_eq_zero_of_ne (by simpa [max64] using hguard)
  have rd5975₀ := RD.iszero rd5974 (by decide)
    (by simp only [List.length_cons]; omega)
  have rd5975 := rd5975₀
  rw [hcond] at rd5975
  have rd3143 := evm_run rd5975 with [
    push2 ⟨5986⟩, jumpiNT (by decide), pop, pop, pop, pop, pop, swap1,
    jump (by jump_dest)]
  exact ⟨_, _, by simpa [max64] using rd3143⟩

set_option maxHeartbeats 1000000 in
theorem auctionCreateAuction_errorStringDecoderLoadLengthOk {cA gh bl σInit σ₀ A I}
    {g : Sat256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {aw fmp off len : UInt256} {k C : ℕ} {R : List UInt256}
    (rd : RD auctionBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨5987⟩
      (⟨0xffffffffffffffff⟩ :: UInt256.ofNat o.size :: off ::
        UInt256.lnot (⟨3⟩ : UInt256) :: fmp :: ⟨0⟩ :: ⟨3143⟩ :: R)
      mem aw o acc k C)
    (hmloadLen :
      (if (fmp + off).toNat ≥ mem.size ∨ (fmp + off) ≥ aw * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding (fmp + off).toNat 32))) =
        len)
    (hlenMax : len.toNat ≤ ABI.solcMaxU64)
    (hov : R.length + 10 ≤ 1024) :
    ∃ k' C', RD auctionBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨6011⟩
      (len :: ⟨0xffffffffffffffff⟩ :: (fmp + off) :: off ::
        UInt256.lnot (⟨3⟩ : UInt256) :: fmp :: ⟨0⟩ :: ⟨3143⟩ :: R)
      mem (UInt256.ofNat (MachineState.M aw.toNat (fmp + off).toNat 32)) o acc k' C' := by
  let max64 : UInt256 := ⟨0xffffffffffffffff⟩
  let lenPtr : UInt256 := fmp + off
  let awLoad := UInt256.ofNat (MachineState.M aw.toNat lenPtr.toNat 32)
  have hgtLenMax : UInt256.gt len max64 = ⟨0⟩ := by
    apply ugt_zero
    change len.toNat ≤ max64.toNat
    simp [max64]
    exact hlenMax
  have rd5988 := RD.dup3 rd (by decide)
    (by simp only [List.length_cons]; omega)
  have rd5989 := RD.dup6 rd5988 (by decide)
    (by simp only [List.length_cons]; omega)
  have rd5990 := RD.add rd5989 (by decide)
    (by simp only [List.length_cons]; omega)
  have rd5991 := RD.swap2 rd5990 (by decide)
    (by simp only [List.length_cons]; omega)
  have rd5992 := RD.pop rd5991 (by decide)
    (by simp only [List.length_cons]; omega)
  have rd5993 := RD.dup2 rd5992 (by decide)
    (by simp only [List.length_cons]; omega)
  have rd5994 := RD.mload (Cₘ awLoad - Cₘ aw) len awLoad rd5993 (by decide)
    (fun _ haws hstks => auctionMloadCost_of_stack haws hstks (by rfl))
    (by simpa [lenPtr] using hmloadLen) (by rfl)
    (by simp only [List.length_cons]; omega)
  have rd5995 := RD.dup2 rd5994 (by decide)
    (by simp only [List.length_cons]; omega)
  have rd5996 := RD.dup2 rd5995 (by decide)
    (by simp only [List.length_cons]; omega)
  have rd5997₀ := RD.gt rd5996 (by decide)
    (by simp only [List.length_cons]; omega)
  have rd5997 := rd5997₀
  rw [hgtLenMax] at rd5997
  have rd5998₀ := RD.iszero rd5997 (by decide)
    (by simp only [List.length_cons]; omega)
  have rd5998 := rd5998₀
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd5998
  have rd6001 := RD.push2 rd5998 ⟨6010⟩ (by decide)
    (by simp only [List.length_cons]; omega)
  have rd6010 := RD.jumpiT rd6001 (by decide) (by decide) (by jump_dest)
    (by simp only [List.length_cons]; omega)
  have rd6011 := RD.jumpdest rd6010 (by decide)
    (by simp only [List.length_cons]; omega)
  exact ⟨_, _, by simpa [max64, lenPtr, awLoad] using rd6011⟩

set_option maxHeartbeats 1000000 in
theorem auctionCreateAuction_errorStringDecoderLoadLengthFail {cA gh bl σInit σ₀ A I}
    {g : Sat256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {aw fmp off len : UInt256} {k C : ℕ} {R : List UInt256}
    (rd : RD auctionBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨5987⟩
      (⟨0xffffffffffffffff⟩ :: UInt256.ofNat o.size :: off ::
        UInt256.lnot (⟨3⟩ : UInt256) :: fmp :: ⟨0⟩ :: ⟨3143⟩ :: R)
      mem aw o acc k C)
    (hmloadLen :
      (if (fmp + off).toNat ≥ mem.size ∨ (fmp + off) ≥ aw * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding (fmp + off).toNat 32))) =
        len)
    (hguard : UInt256.gt len (⟨0xffffffffffffffff⟩ : UInt256) ≠ ⟨0⟩)
    (hov : R.length + 16 ≤ 1024) :
    ∃ k' C', RD auctionBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨3143⟩
      (⟨0⟩ :: R) mem (UInt256.ofNat (MachineState.M aw.toNat (fmp + off).toNat 32)) o
      acc k' C' := by
  let max64 : UInt256 := ⟨0xffffffffffffffff⟩
  let lenPtr : UInt256 := fmp + off
  let awLoad := UInt256.ofNat (MachineState.M aw.toNat lenPtr.toNat 32)
  have hcond : UInt256.isZero (UInt256.gt len max64) = ⟨0⟩ := by
    exact isZero_eq_zero_of_ne (by simpa [max64] using hguard)
  have rd5988 := RD.dup3 rd (by decide)
    (by simp only [List.length_cons]; omega)
  have rd5989 := RD.dup6 rd5988 (by decide)
    (by simp only [List.length_cons]; omega)
  have rd5990 := RD.add rd5989 (by decide)
    (by simp only [List.length_cons]; omega)
  have rd5991 := RD.swap2 rd5990 (by decide)
    (by simp only [List.length_cons]; omega)
  have rd5992 := RD.pop rd5991 (by decide)
    (by simp only [List.length_cons]; omega)
  have rd5993 := RD.dup2 rd5992 (by decide)
    (by simp only [List.length_cons]; omega)
  have rd5994 := RD.mload (Cₘ awLoad - Cₘ aw) len awLoad rd5993 (by decide)
    (fun _ haws hstks => auctionMloadCost_of_stack haws hstks (by rfl))
    (by simpa [lenPtr] using hmloadLen) (by rfl)
    (by simp only [List.length_cons]; omega)
  have rd5995 := RD.dup2 rd5994 (by decide)
    (by simp only [List.length_cons]; omega)
  have rd5996 := RD.dup2 rd5995 (by decide)
    (by simp only [List.length_cons]; omega)
  have rd5997 := RD.gt rd5996 (by decide)
    (by simp only [List.length_cons]; omega)
  have rd5998₀ := RD.iszero rd5997 (by decide)
    (by simp only [List.length_cons]; omega)
  have rd5998 := rd5998₀
  rw [hcond] at rd5998
  have rd3143 := evm_run rd5998 with [
    push2 ⟨6010⟩, jumpiNT (by decide), pop, pop, pop, pop, pop, pop, swap1,
    jump (by jump_dest)]
  exact ⟨_, _, by simpa [max64, lenPtr, awLoad] using rd3143⟩

set_option maxHeartbeats 1000000 in
theorem auctionCreateAuction_errorStringDecoderPayloadBoundsOk {cA gh bl σInit σ₀ A I}
    {g : Sat256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {aw fmp off len : UInt256} {k C : ℕ} {R : List UInt256}
    (rd : RD auctionBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨6011⟩
      (len :: ⟨0xffffffffffffffff⟩ :: (fmp + off) :: off ::
        UInt256.lnot (⟨3⟩ : UInt256) :: fmp :: ⟨0⟩ :: ⟨3143⟩ :: R)
      mem aw o acc k C)
    (hgtPayload :
      UInt256.gt (((fmp + off) + len) + ⟨32⟩)
        ((fmp + UInt256.ofNat o.size) + UInt256.lnot (⟨3⟩ : UInt256)) = ⟨0⟩)
    (hov : R.length + 12 ≤ 1024) :
    ∃ k' C', RD auctionBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨6037⟩
      (len :: ⟨0xffffffffffffffff⟩ :: (fmp + off) :: off ::
        UInt256.lnot (⟨3⟩ : UInt256) :: fmp :: ⟨0⟩ :: ⟨3143⟩ :: R)
      mem aw o acc k' C' := by
  let max64 : UInt256 := ⟨0xffffffffffffffff⟩
  let copiedEnd : UInt256 := (fmp + UInt256.ofNat o.size) + UInt256.lnot (⟨3⟩ : UInt256)
  let payloadEnd : UInt256 := ((fmp + off) + len) + ⟨32⟩
  have rd6012 := RD.dup5 rd (by decide)
    (by simp only [List.length_cons]; omega)
  have rd6013 := RD.returndatasize rd6012 (by decide)
    (by simp only [List.length_cons]; omega)
  have rd6014 := RD.dup8 rd6013 (by decide)
    (by simp only [List.length_cons]; omega)
  have rd6015 := RD.add rd6014 (by decide)
    (by simp only [List.length_cons]; omega)
  have rd6016 := RD.add rd6015 (by decide)
    (by simp only [List.length_cons]; omega)
  have rd6018 := RD.push1 rd6016 ⟨32⟩ (by decide)
    (by simp only [List.length_cons]; omega)
  have rd6019 := RD.dup3 rd6018 (by decide)
    (by simp only [List.length_cons]; omega)
  have rd6020 := RD.dup6 rd6019 (by decide)
    (by simp only [List.length_cons]; omega)
  have rd6021 := RD.add rd6020 (by decide)
    (by simp only [List.length_cons]; omega)
  have rd6022 := RD.add rd6021 (by decide)
    (by simp only [List.length_cons]; omega)
  have rd6023₀ := RD.gt rd6022 (by decide)
    (by simp only [List.length_cons]; omega)
  have rd6023 := rd6023₀
  rw [hgtPayload] at rd6023
  have rd6024₀ := RD.iszero rd6023 (by decide)
    (by simp only [List.length_cons]; omega)
  have rd6024 := rd6024₀
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd6024
  have rd6027 := RD.push2 rd6024 ⟨6036⟩ (by decide)
    (by simp only [List.length_cons]; omega)
  have rd6036 := RD.jumpiT rd6027 (by decide) (by decide) (by jump_dest)
    (by simp only [List.length_cons]; omega)
  have rd6037 := RD.jumpdest rd6036 (by decide)
    (by simp only [List.length_cons]; omega)
  exact ⟨_, _, by simpa [max64, copiedEnd, payloadEnd] using rd6037⟩

set_option maxHeartbeats 1000000 in
theorem auctionCreateAuction_errorStringDecoderPayloadBoundsFail {cA gh bl σInit σ₀ A I}
    {g : Sat256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {aw fmp off len : UInt256} {k C : ℕ} {R : List UInt256}
    (rd : RD auctionBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨6011⟩
      (len :: ⟨0xffffffffffffffff⟩ :: (fmp + off) :: off ::
        UInt256.lnot (⟨3⟩ : UInt256) :: fmp :: ⟨0⟩ :: ⟨3143⟩ :: R)
      mem aw o acc k C)
    (hguard :
      UInt256.gt (((fmp + off) + len) + ⟨32⟩)
          ((fmp + UInt256.ofNat o.size) + UInt256.lnot (⟨3⟩ : UInt256)) ≠
        ⟨0⟩)
    (hov : R.length + 16 ≤ 1024) :
    ∃ k' C', RD auctionBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨3143⟩
      (⟨0⟩ :: R) mem aw o acc k' C' := by
  let max64 : UInt256 := ⟨0xffffffffffffffff⟩
  let copiedEnd : UInt256 := (fmp + UInt256.ofNat o.size) + UInt256.lnot (⟨3⟩ : UInt256)
  let payloadEnd : UInt256 := ((fmp + off) + len) + ⟨32⟩
  have hcond : UInt256.isZero (UInt256.gt payloadEnd copiedEnd) = ⟨0⟩ := by
    exact isZero_eq_zero_of_ne (by simpa [payloadEnd, copiedEnd] using hguard)
  have rd6012 := RD.dup5 rd (by decide)
    (by simp only [List.length_cons]; omega)
  have rd6013 := RD.returndatasize rd6012 (by decide)
    (by simp only [List.length_cons]; omega)
  have rd6014 := RD.dup8 rd6013 (by decide)
    (by simp only [List.length_cons]; omega)
  have rd6015 := RD.add rd6014 (by decide)
    (by simp only [List.length_cons]; omega)
  have rd6016 := RD.add rd6015 (by decide)
    (by simp only [List.length_cons]; omega)
  have rd6018 := RD.push1 rd6016 ⟨32⟩ (by decide)
    (by simp only [List.length_cons]; omega)
  have rd6019 := RD.dup3 rd6018 (by decide)
    (by simp only [List.length_cons]; omega)
  have rd6020 := RD.dup6 rd6019 (by decide)
    (by simp only [List.length_cons]; omega)
  have rd6021 := RD.add rd6020 (by decide)
    (by simp only [List.length_cons]; omega)
  have rd6022 := RD.add rd6021 (by decide)
    (by simp only [List.length_cons]; omega)
  have rd6023 := RD.gt rd6022 (by decide)
    (by simp only [List.length_cons]; omega)
  have rd6024₀ := RD.iszero rd6023 (by decide)
    (by simp only [List.length_cons]; omega)
  have rd6024 := rd6024₀
  rw [hcond] at rd6024
  have rd3143 := evm_run rd6024 with [
    push2 ⟨6036⟩, jumpiNT (by decide), pop, pop, pop, pop, pop, pop, swap1,
    jump (by jump_dest)]
  exact ⟨_, _, by simpa [max64, copiedEnd, payloadEnd] using rd3143⟩

set_option maxHeartbeats 10000000 in
theorem auctionCreateAuction_errorStringDecoderCopyToReturn {cA gh bl σInit σ₀ A I}
    {g : Sat256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {aw fmp off len : UInt256} {k C : ℕ} {R : List UInt256}
    (rd : RD auctionBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨6037⟩
      (len :: ⟨0xffffffffffffffff⟩ :: (fmp + off) :: off ::
        UInt256.lnot (⟨3⟩ : UInt256) :: fmp :: ⟨0⟩ :: ⟨3143⟩ :: R)
      mem aw o acc k C)
    (hgtNewFree :
      UInt256.gt
          (fmp +
            UInt256.land (UInt256.lnot (⟨31⟩ : UInt256))
              ((((off + len) + ⟨32⟩ : UInt256) + ⟨31⟩)))
          (⟨0xffffffffffffffff⟩ : UInt256) =
        ⟨0⟩)
    (hltNewFree :
      UInt256.lt
          (fmp +
            UInt256.land (UInt256.lnot (⟨31⟩ : UInt256))
              ((((off + len) + ⟨32⟩ : UInt256) + ⟨31⟩)))
          fmp =
        ⟨0⟩)
    (hov : R.length + 16 ≤ 1024) :
    let payloadLen : UInt256 := (off + len) + ⟨32⟩
    let roundedLen : UInt256 :=
      UInt256.land (UInt256.lnot (⟨31⟩ : UInt256)) (payloadLen + ⟨31⟩)
    let newFree : UInt256 := fmp + roundedLen
    let memFree : ByteArray := (UInt256.toByteArray newFree).write 0 mem 64 32
    let awFree := UInt256.ofNat (MachineState.M aw.toNat (⟨64⟩ : UInt256).toNat 32)
    ∃ k' C',
      RD auctionBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨3143⟩
        ((fmp + off) :: R) memFree awFree o acc k' C' := by
  let max64 : UInt256 := ⟨0xffffffffffffffff⟩
  let payloadLen : UInt256 := (off + len) + ⟨32⟩
  let roundedLen : UInt256 :=
    UInt256.land (UInt256.lnot (⟨31⟩ : UInt256)) (payloadLen + ⟨31⟩)
  let newFree : UInt256 := fmp + roundedLen
  let memFree : ByteArray := (UInt256.toByteArray newFree).write 0 mem 64 32
  let awFree := UInt256.ofNat (MachineState.M aw.toNat (⟨64⟩ : UInt256).toNat 32)
  have hgtNewFree' : UInt256.gt newFree max64 = ⟨0⟩ := by
    simpa [newFree, roundedLen, payloadLen, max64] using hgtNewFree
  have hltNewFree' : UInt256.lt newFree fmp = ⟨0⟩ := by
    simpa [newFree, roundedLen, payloadLen] using hltNewFree
  have rd5868₀ := evm_run rd with [
    push2 ⟨6051⟩, push1 ⟨32⟩, dup3, dup7, add, add, dup8, push2 ⟨5868⟩,
    jump (by jump_dest)]
  have rd5868 : ∃ k' C', RD auctionBytecode I g (initState cA gh bl σInit σ₀ g A I)
      ⟨5868⟩
      (fmp :: payloadLen :: ⟨6051⟩ :: len :: max64 :: (fmp + off) :: off ::
        UInt256.lnot (⟨3⟩ : UInt256) :: fmp :: ⟨0⟩ :: ⟨3143⟩ :: R)
      mem aw o acc k' C' := by
    exact ⟨_, _, by simpa [payloadLen, max64] using rd5868₀⟩
  obtain ⟨_, _, rd5868⟩ := rd5868
  have rd5869 := RD.jumpdest rd5868 (by decide)
    (by simp only [List.length_cons]; omega)
  have rd5871 := RD.push1 rd5869 ⟨31⟩ (by decide)
    (by simp only [List.length_cons]; omega)
  have rd5872 := RD.dup3 rd5871 (by decide)
    (by simp only [List.length_cons]; omega)
  have rd5873 := RD.add rd5872 (by decide)
    (by simp only [List.length_cons]; omega)
  have rd5875 := RD.push1 rd5873 ⟨31⟩ (by decide)
    (by simp only [List.length_cons]; omega)
  have rd5876 := RD.not rd5875 (by decide)
    (by simp only [List.length_cons]; omega)
  have rd5877 := RD.and rd5876 (by decide)
    (by simp only [List.length_cons]; omega)
  have rd5878 := RD.dup2 rd5877 (by decide)
    (by simp only [List.length_cons]; omega)
  have rd5879 := RD.add rd5878 (by decide)
    (by simp only [List.length_cons]; omega)
  have rd5888 := RD.pushConst rd5879 max64 (width := 8) (op := .PUSH8)
    (by decide) (by decide) (by simp only [List.length_cons]; omega)
  have rd5889 := RD.dup2 rd5888 (by decide)
    (by simp only [List.length_cons]; omega)
  have rd5890₀ := RD.gt rd5889 (by decide)
    (by simp only [List.length_cons]; omega)
  have rd5890 := rd5890₀
  rw [hgtNewFree'] at rd5890
  have rd5891 := RD.dup3 rd5890 (by decide)
    (by simp only [List.length_cons]; omega)
  have rd5892 := RD.dup3 rd5891 (by decide)
    (by simp only [List.length_cons]; omega)
  have rd5893₀ := RD.lt rd5892 (by decide)
    (by simp only [List.length_cons]; omega)
  have rd5893 := rd5893₀
  rw [hltNewFree'] at rd5893
  have rd5894₀ := RD.lor rd5893 (by decide)
    (by simp only [List.length_cons]; omega)
  have rd5894 := rd5894₀
  rw [show UInt256.lor (⟨0⟩ : UInt256) ⟨0⟩ = ⟨0⟩ by decide] at rd5894
  have rd5895₀ := RD.iszero rd5894 (by decide)
    (by simp only [List.length_cons]; omega)
  have rd5895 := rd5895₀
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd5895
  have rd5898 := RD.push2 rd5895 ⟨5918⟩ (by decide)
    (by simp only [List.length_cons]; omega)
  have rd5918 := RD.jumpiT rd5898 (by decide) (by decide) (by jump_dest)
    (by simp only [List.length_cons]; omega)
  have rd5922₀ := evm_run rd5918 with [
    jumpdest, push1 ⟨64⟩,
    raw mstore (Cₘ awFree - Cₘ aw) memFree awFree (by decide)
      (fun s haw hstk => by
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk, awFree])
      (by rfl) (by rfl) (by simp only [List.length_cons]; omega)]
  have rd3143 := evm_run rd5922₀ with [
    pop, pop, jump (by jump_dest), jumpdest, pop, swap1, swap6, swap5,
    pop, pop, pop, pop, pop, jump (by jump_dest)]
  exact ⟨_, _, by simpa [max64, payloadLen, roundedLen, newFree, memFree, awFree]
    using rd3143⟩

theorem errorStringMemFree_mload64_of_aw (mem : ByteArray) (aw newFree : UInt256)
    (haw3 : 3 ≤ aw.toNat) (hawMul : aw.toNat * 32 < UInt256.size) :
    let memFree : ByteArray := (UInt256.toByteArray newFree).write 0 mem 64 32
    let awFree := UInt256.ofNat (MachineState.M aw.toNat (⟨64⟩ : UInt256).toNat 32)
    (if (⟨64⟩ : UInt256).toNat ≥ memFree.size ∨
        (⟨64⟩ : UInt256) ≥ awFree * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian (memFree.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
      newFree := by
  intro memFree awFree
  apply mloadWordValue_of_readWithPadding
  · dsimp [memFree]
    have hgap : 64 - mem.size < USize.size :=
      lt_of_le_of_lt (Nat.sub_le _ _) (by native_decide : 64 < USize.size)
    have hsz := toByteArray_write_size_ge_off_add32 newFree mem 64 hgap
    change 64 < ((UInt256.toByteArray newFree).write 0 mem 64 32).size
    omega
  · intro h
    have hceil : (((⟨64⟩ : UInt256).toNat + 32 + 31) / 32) = 3 := by native_decide
    have hawNat : awFree.toNat = aw.toNat := by
      dsimp [awFree]
      rw [UInt256.toNat_ofNat_of_lt]
      · dsimp [MachineState.M]
        rw [hceil, max_eq_left haw3]
      · dsimp [MachineState.M]
        rw [hceil]
        exact max_lt aw.val.isLt (by norm_num [UInt256.size])
    have hmulNat : (awFree * (⟨32⟩ : UInt256)).toNat = aw.toNat * 32 := by
      rw [umul_toNat]
      · rw [hawNat]
        rfl
      · simpa [hawNat, show (⟨32⟩ : UInt256).toNat = 32 from by decide] using hawMul
    have hle : (awFree * (⟨32⟩ : UInt256)).toNat ≤ 64 := by
      simpa [show (⟨64⟩ : UInt256).toNat = 64 from by decide] using h
    rw [hmulNat] at hle
    omega
  · exact toByteArray_write_read_back_of_gap newFree mem 64
      (lt_of_le_of_lt (Nat.sub_le _ _) (by native_decide : 64 < USize.size))

-- LIBRARY CANDIDATE: generic `MLOAD 0x40` readback from a known word and active-word bound.
theorem mload64_of_readWithPadding_of_aw {mem : ByteArray} {aw val : UInt256}
    (hmem : 64 < mem.size)
    (hread : mem.readWithPadding 64 32 = UInt256.toByteArray val)
    (haw3 : 3 ≤ aw.toNat) (hawMul : aw.toNat * 32 < UInt256.size) :
    (if (⟨64⟩ : UInt256).toNat ≥ mem.size ∨ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
      val := by
  apply mloadWordValue_of_readWithPadding
  · simpa [show (⟨64⟩ : UInt256).toNat = 64 from by decide] using hmem
  · intro h
    have hmulNat : (aw * (⟨32⟩ : UInt256)).toNat = aw.toNat * 32 := by
      rw [umul_toNat]
      · rfl
      · simpa [show (⟨32⟩ : UInt256).toNat = 32 from by decide] using hawMul
    have hle : (aw * (⟨32⟩ : UInt256)).toNat ≤ 64 := by
      simpa [show (⟨64⟩ : UInt256).toNat = 64 from by decide] using h
    rw [hmulNat] at hle
    omega
  · simpa [show (⟨64⟩ : UInt256).toNat = 64 from by decide] using hread

theorem auctionAwMstore32_bounds {aw addr : UInt256}
    (haw3 : 3 ≤ aw.toNat) (hawMul : aw.toNat * 32 < UInt256.size)
    (haddrLe : addr.toNat ≤ ABI.solcMaxU64 + 68) :
    let aw' := UInt256.ofNat (MachineState.M aw.toNat addr.toNat 32)
    3 ≤ aw'.toNat ∧ aw'.toNat * 32 < UInt256.size := by
  intro aw'
  let ceilA := (addr.toNat + 32 + 31) / 32
  have hceilMulLe : ceilA * 32 ≤ addr.toNat + 63 := by
    dsimp [ceilA]
    omega
  have hceilMulLt : ceilA * 32 < UInt256.size := by
    have hmax : addr.toNat + 63 < UInt256.size := by
      norm_num [ABI.solcMaxU64, UInt256.size] at haddrLe ⊢
      omega
    exact lt_of_le_of_lt hceilMulLe hmax
  have hceilLt : ceilA < UInt256.size := by
    nlinarith [hceilMulLt]
  have hMlt : MachineState.M aw.toNat addr.toNat 32 < UInt256.size := by
    dsimp [MachineState.M]
    exact max_lt aw.val.isLt (by simpa [ceilA] using hceilLt)
  have haw'Nat : aw'.toNat = MachineState.M aw.toNat addr.toNat 32 := by
    dsimp [aw']
    rw [UInt256.toNat_ofNat_of_lt hMlt]
  constructor
  · rw [haw'Nat]
    dsimp [MachineState.M]
    exact le_max_of_le_left haw3
  · rw [haw'Nat]
    dsimp [MachineState.M]
    rw [Nat.mul_comm, mul_max, Nat.mul_comm 32 aw.toNat, Nat.mul_comm 32 ceilA]
    exact max_lt hawMul (by simpa [ceilA] using hceilMulLt)

theorem auctionErrorStringEvent_aw_bounds {aw fmp : UInt256}
    (haw3 : 3 ≤ aw.toNat) (hawMul : aw.toNat * 32 < UInt256.size)
    (hfmpLe : fmp.toNat ≤ ABI.solcMaxU64) :
    let aw64 := UInt256.ofNat (MachineState.M aw.toNat (⟨64⟩ : UInt256).toNat 32)
    let awEvent := UInt256.ofNat (MachineState.M aw64.toNat fmp.toNat 32)
    3 ≤ awEvent.toNat ∧ awEvent.toNat * 32 < UInt256.size := by
  intro aw64 awEvent
  have hceil64 : (((⟨64⟩ : UInt256).toNat + 32 + 31) / 32) = 3 := by
    native_decide
  have haw64Nat : aw64.toNat = aw.toNat := by
    dsimp [aw64]
    rw [UInt256.toNat_ofNat_of_lt]
    · dsimp [MachineState.M]
      rw [hceil64, max_eq_left haw3]
    · dsimp [MachineState.M]
      rw [hceil64]
      exact max_lt aw.val.isLt (by norm_num [UInt256.size])
  let ceilF := (fmp.toNat + 32 + 31) / 32
  have hceilMulLe : ceilF * 32 ≤ fmp.toNat + 63 := by
    dsimp [ceilF]
    omega
  have hceilMulLt : ceilF * 32 < UInt256.size := by
    have hmax : fmp.toNat + 63 < UInt256.size := by
      norm_num [ABI.solcMaxU64, UInt256.size] at hfmpLe ⊢
      omega
    exact lt_of_le_of_lt hceilMulLe hmax
  have hceilLt : ceilF < UInt256.size := by
    nlinarith [hceilMulLt]
  have hMlt : MachineState.M aw64.toNat fmp.toNat 32 < UInt256.size := by
    dsimp [MachineState.M]
    apply max_lt
    · rw [haw64Nat]
      exact aw.val.isLt
    · simpa [ceilF]
  have hawEventNat : awEvent.toNat = MachineState.M aw64.toNat fmp.toNat 32 := by
    dsimp [awEvent]
    rw [UInt256.toNat_ofNat_of_lt hMlt]
  constructor
  · rw [hawEventNat]
    dsimp [MachineState.M]
    exact le_max_of_le_left (by simpa [haw64Nat] using haw3)
  · rw [hawEventNat]
    dsimp [MachineState.M]
    rw [Nat.mul_comm, mul_max, Nat.mul_comm 32 aw64.toNat, Nat.mul_comm 32 ceilF]
    exact max_lt (by simpa [haw64Nat] using hawMul) (by simpa [ceilF] using hceilMulLt)

theorem auctionEventMemFrom_mload64_of_base {mem : ByteArray} {aw fmp : UInt256}
    (I : ExecutionEnv)
    (hmem : 96 ≤ mem.size)
    (hread : mem.readWithPadding 64 32 = UInt256.toByteArray fmp)
    (haw3 : 3 ≤ aw.toNat) (hawMul : aw.toNat * 32 < UInt256.size)
    (hfmpGe : 96 ≤ fmp.toNat) (hfmpLe : fmp.toNat ≤ ABI.solcMaxU64) :
    (if (⟨64⟩ : UInt256).toNat ≥ (auctionEventMemFrom mem I fmp).size ∨
        (⟨64⟩ : UInt256) ≥
          (UInt256.ofNat
            (MachineState.M
              (UInt256.ofNat (MachineState.M aw.toNat (⟨64⟩ : UInt256).toNat 32)).toNat
              fmp.toNat 32)) * ⟨32⟩ then
        ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((auctionEventMemFrom mem I fmp).readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
      fmp := by
  have hgap : fmp.toNat - mem.size < USize.size := by
    have hfmpU : fmp.toNat < USize.size :=
      lt_of_le_of_lt hfmpLe (by native_decide : ABI.solcMaxU64 < USize.size)
    exact lt_of_le_of_lt (Nat.sub_le _ _) hfmpU
  have hsizeEvent : 64 < (auctionEventMemFrom mem I fmp).size := by
    have hsz := toByteArray_write_size_ge_off_add32 (auctionSourceWord I) mem
      fmp.toNat hgap
    simp [auctionEventMemFrom]
    omega
  have hreadEvent :
      (auctionEventMemFrom mem I fmp).readWithPadding 64 32 =
        UInt256.toByteArray fmp := by
    have hpres := toByteArray_write_read_below_of_gap (auctionSourceWord I) mem
      fmp.toNat 64 hmem hfmpGe hgap
    rw [auctionEventMemFrom]
    rw [hpres]
    exact hread
  have hawEvent := auctionErrorStringEvent_aw_bounds (aw := aw) (fmp := fmp)
    haw3 hawMul hfmpLe
  exact mload64_of_readWithPadding_of_aw hsizeEvent hreadEvent
    (by simpa using hawEvent.1) (by simpa using hawEvent.2)

noncomputable def auctionPausablePausedMem0From (mem : ByteArray) (fmp : UInt256) :
    ByteArray :=
  (UInt256.toByteArray solcErrorStringSelector).write 0 mem fmp.toNat 32

noncomputable def auctionPausablePausedMem1From (mem : ByteArray) (fmp : UInt256) :
    ByteArray :=
  (UInt256.toByteArray (⟨32⟩ : UInt256)).write 0
    (auctionPausablePausedMem0From mem fmp) (fmp + (⟨4⟩ : UInt256)).toNat 32

noncomputable def auctionPausablePausedMem2From (mem : ByteArray) (fmp : UInt256) :
    ByteArray :=
  (UInt256.toByteArray (⟨16⟩ : UInt256)).write 0
    (auctionPausablePausedMem1From mem fmp) (fmp + (⟨36⟩ : UInt256)).toNat 32

noncomputable def auctionPausablePausedMem3From (mem : ByteArray) (fmp : UInt256) :
    ByteArray :=
  (UInt256.toByteArray auctionPausablePausedStringWord).write 0
    (auctionPausablePausedMem2From mem fmp) (fmp + (⟨68⟩ : UInt256)).toNat 32

def auctionPausablePausedAw64From (aw : UInt256) : UInt256 :=
  UInt256.ofNat (MachineState.M aw.toNat (⟨64⟩ : UInt256).toNat 32)

def auctionPausablePausedAw0From (aw fmp : UInt256) : UInt256 :=
  UInt256.ofNat (MachineState.M (auctionPausablePausedAw64From aw).toNat fmp.toNat 32)

def auctionPausablePausedAw1From (aw fmp : UInt256) : UInt256 :=
  UInt256.ofNat
    (MachineState.M (auctionPausablePausedAw0From aw fmp).toNat
      (fmp + (⟨4⟩ : UInt256)).toNat 32)

def auctionPausablePausedAw2From (aw fmp : UInt256) : UInt256 :=
  UInt256.ofNat
    (MachineState.M (auctionPausablePausedAw1From aw fmp).toNat
      (fmp + (⟨36⟩ : UInt256)).toNat 32)

def auctionPausablePausedAw3From (aw fmp : UInt256) : UInt256 :=
  UInt256.ofNat
    (MachineState.M (auctionPausablePausedAw2From aw fmp).toNat
      (fmp + (⟨68⟩ : UInt256)).toNat 32)

theorem auctionPausablePausedAw3From_bounds {aw fmp : UInt256}
    (haw3 : 3 ≤ aw.toNat) (hawMul : aw.toNat * 32 < UInt256.size)
    (hfmpLe : fmp.toNat ≤ ABI.solcMaxU64) :
    3 ≤ (auctionPausablePausedAw3From aw fmp).toNat ∧
      (auctionPausablePausedAw3From aw fmp).toNat * 32 < UInt256.size := by
  have haddr64 : (⟨64⟩ : UInt256).toNat ≤ ABI.solcMaxU64 + 68 := by
    native_decide
  have haw64 := auctionAwMstore32_bounds (aw := aw) (addr := (⟨64⟩ : UInt256))
    haw3 hawMul haddr64
  have hfmpAddr : fmp.toNat ≤ ABI.solcMaxU64 + 68 := by
    omega
  have haw0 := auctionAwMstore32_bounds
    (aw := auctionPausablePausedAw64From aw) (addr := fmp)
    (by simpa [auctionPausablePausedAw64From] using haw64.1)
    (by simpa [auctionPausablePausedAw64From] using haw64.2)
    hfmpAddr
  have hfmp4 : (fmp + (⟨4⟩ : UInt256)).toNat ≤ ABI.solcMaxU64 + 68 := by
    have hnat : (fmp + (⟨4⟩ : UInt256)).toNat = fmp.toNat + 4 := by
      rw [uadd_toNat]
      rw [show (⟨4⟩ : UInt256).toNat = 4 from by decide]
      rw [Nat.mod_eq_of_lt]
      norm_num [ABI.solcMaxU64, UInt256.size] at hfmpLe ⊢
      omega
    rw [hnat]
    omega
  have haw1 := auctionAwMstore32_bounds
    (aw := auctionPausablePausedAw0From aw fmp) (addr := fmp + (⟨4⟩ : UInt256))
    (by simpa [auctionPausablePausedAw0From] using haw0.1)
    (by simpa [auctionPausablePausedAw0From] using haw0.2)
    hfmp4
  have hfmp36 : (fmp + (⟨36⟩ : UInt256)).toNat ≤ ABI.solcMaxU64 + 68 := by
    have hnat : (fmp + (⟨36⟩ : UInt256)).toNat = fmp.toNat + 36 := by
      rw [uadd_toNat]
      rw [show (⟨36⟩ : UInt256).toNat = 36 from by decide]
      rw [Nat.mod_eq_of_lt]
      norm_num [ABI.solcMaxU64, UInt256.size] at hfmpLe ⊢
      omega
    rw [hnat]
    omega
  have haw2 := auctionAwMstore32_bounds
    (aw := auctionPausablePausedAw1From aw fmp) (addr := fmp + (⟨36⟩ : UInt256))
    (by simpa [auctionPausablePausedAw1From] using haw1.1)
    (by simpa [auctionPausablePausedAw1From] using haw1.2)
    hfmp36
  have hfmp68 : (fmp + (⟨68⟩ : UInt256)).toNat ≤ ABI.solcMaxU64 + 68 := by
    have hnat : (fmp + (⟨68⟩ : UInt256)).toNat = fmp.toNat + 68 := by
      rw [uadd_toNat]
      rw [show (⟨68⟩ : UInt256).toNat = 68 from by decide]
      rw [Nat.mod_eq_of_lt]
      norm_num [ABI.solcMaxU64, UInt256.size] at hfmpLe ⊢
      omega
    rw [hnat]
    omega
  have haw3' := auctionAwMstore32_bounds
    (aw := auctionPausablePausedAw2From aw fmp) (addr := fmp + (⟨68⟩ : UInt256))
    (by simpa [auctionPausablePausedAw2From] using haw2.1)
    (by simpa [auctionPausablePausedAw2From] using haw2.2)
    hfmp68
  simpa [auctionPausablePausedAw3From] using haw3'

theorem auctionPausablePausedMem3From_mload64_of_base {mem : ByteArray}
    {aw fmp : UInt256}
    (hmem : 96 ≤ mem.size)
    (hread : mem.readWithPadding 64 32 = UInt256.toByteArray fmp)
    (haw3 : 3 ≤ aw.toNat) (hawMul : aw.toNat * 32 < UInt256.size)
    (hfmpGe : 96 ≤ fmp.toNat) (hfmpLe : fmp.toNat ≤ ABI.solcMaxU64) :
    (if (⟨64⟩ : UInt256).toNat ≥ (auctionPausablePausedMem3From mem fmp).size ∨
        (⟨64⟩ : UInt256) ≥ auctionPausablePausedAw3From aw fmp * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          ((auctionPausablePausedMem3From mem fmp).readWithPadding
            (⟨64⟩ : UInt256).toNat 32))) =
      fmp := by
  let mem0 := auctionPausablePausedMem0From mem fmp
  let mem1 := auctionPausablePausedMem1From mem fmp
  let mem2 := auctionPausablePausedMem2From mem fmp
  let mem3 := auctionPausablePausedMem3From mem fmp
  have hfmpU : fmp.toNat < USize.size :=
    lt_of_le_of_lt hfmpLe (by native_decide : ABI.solcMaxU64 < USize.size)
  have hgap0 : fmp.toNat - mem.size < USize.size :=
    lt_of_le_of_lt (Nat.sub_le _ _) hfmpU
  have hsz0 : fmp.toNat + 32 ≤ mem0.size := by
    dsimp [mem0, auctionPausablePausedMem0From]
    exact toByteArray_write_size_ge_off_add32 solcErrorStringSelector mem fmp.toNat hgap0
  have hmem0 : 96 ≤ mem0.size := by
    omega
  have hread0 : mem0.readWithPadding 64 32 = UInt256.toByteArray fmp := by
    have hpres := toByteArray_write_read_below_of_gap solcErrorStringSelector mem
      fmp.toNat 64 hmem hfmpGe hgap0
    dsimp [mem0, auctionPausablePausedMem0From]
    rw [hpres]
    exact hread
  have hfmp4Nat : (fmp + (⟨4⟩ : UInt256)).toNat = fmp.toNat + 4 := by
    rw [uadd_toNat]
    rw [show (⟨4⟩ : UInt256).toNat = 4 from by decide]
    rw [Nat.mod_eq_of_lt]
    norm_num [ABI.solcMaxU64, UInt256.size] at hfmpLe ⊢
    omega
  have hoff1Le : (fmp + (⟨4⟩ : UInt256)).toNat ≤ mem0.size := by
    rw [hfmp4Nat]
    omega
  have hgap1 : (fmp + (⟨4⟩ : UInt256)).toNat - mem0.size < USize.size := by
    rw [Nat.sub_eq_zero_of_le hoff1Le]
    exact USize.size_pos
  have hsz1 : (fmp + (⟨4⟩ : UInt256)).toNat + 32 ≤ mem1.size := by
    dsimp [mem1, auctionPausablePausedMem1From, mem0]
    exact toByteArray_write_size_ge_off_add32 (⟨32⟩ : UInt256)
      (auctionPausablePausedMem0From mem fmp) (fmp + (⟨4⟩ : UInt256)).toNat hgap1
  have hmem1 : 96 ≤ mem1.size := by
    rw [hfmp4Nat] at hsz1
    omega
  have hread1 : mem1.readWithPadding 64 32 = UInt256.toByteArray fmp := by
    have hbelow : 64 + 32 ≤ (fmp + (⟨4⟩ : UInt256)).toNat := by
      rw [hfmp4Nat]
      omega
    have hpres := toByteArray_write_read_below_of_gap (⟨32⟩ : UInt256)
      (auctionPausablePausedMem0From mem fmp) (fmp + (⟨4⟩ : UInt256)).toNat 64
      hmem0 hbelow hgap1
    dsimp [mem1, auctionPausablePausedMem1From]
    rw [hpres]
    exact hread0
  have hfmp36Nat : (fmp + (⟨36⟩ : UInt256)).toNat = fmp.toNat + 36 := by
    rw [uadd_toNat]
    rw [show (⟨36⟩ : UInt256).toNat = 36 from by decide]
    rw [Nat.mod_eq_of_lt]
    norm_num [ABI.solcMaxU64, UInt256.size] at hfmpLe ⊢
    omega
  have hoff2Le : (fmp + (⟨36⟩ : UInt256)).toNat ≤ mem1.size := by
    rw [hfmp36Nat]
    rw [hfmp4Nat] at hsz1
    omega
  have hgap2 : (fmp + (⟨36⟩ : UInt256)).toNat - mem1.size < USize.size := by
    rw [Nat.sub_eq_zero_of_le hoff2Le]
    exact USize.size_pos
  have hsz2 : (fmp + (⟨36⟩ : UInt256)).toNat + 32 ≤ mem2.size := by
    dsimp [mem2, auctionPausablePausedMem2From, mem1]
    exact toByteArray_write_size_ge_off_add32 (⟨16⟩ : UInt256)
      (auctionPausablePausedMem1From mem fmp) (fmp + (⟨36⟩ : UInt256)).toNat hgap2
  have hmem2 : 96 ≤ mem2.size := by
    rw [hfmp36Nat] at hsz2
    omega
  have hread2 : mem2.readWithPadding 64 32 = UInt256.toByteArray fmp := by
    have hbelow : 64 + 32 ≤ (fmp + (⟨36⟩ : UInt256)).toNat := by
      rw [hfmp36Nat]
      omega
    have hpres := toByteArray_write_read_below_of_gap (⟨16⟩ : UInt256)
      (auctionPausablePausedMem1From mem fmp) (fmp + (⟨36⟩ : UInt256)).toNat 64
      hmem1 hbelow hgap2
    dsimp [mem2, auctionPausablePausedMem2From]
    rw [hpres]
    exact hread1
  have hfmp68Nat : (fmp + (⟨68⟩ : UInt256)).toNat = fmp.toNat + 68 := by
    rw [uadd_toNat]
    rw [show (⟨68⟩ : UInt256).toNat = 68 from by decide]
    rw [Nat.mod_eq_of_lt]
    norm_num [ABI.solcMaxU64, UInt256.size] at hfmpLe ⊢
    omega
  have hoff3Le : (fmp + (⟨68⟩ : UInt256)).toNat ≤ mem2.size := by
    rw [hfmp68Nat]
    rw [hfmp36Nat] at hsz2
    omega
  have hgap3 : (fmp + (⟨68⟩ : UInt256)).toNat - mem2.size < USize.size := by
    rw [Nat.sub_eq_zero_of_le hoff3Le]
    exact USize.size_pos
  have hsz3 : (fmp + (⟨68⟩ : UInt256)).toNat + 32 ≤ mem3.size := by
    dsimp [mem3, auctionPausablePausedMem3From, mem2]
    exact toByteArray_write_size_ge_off_add32 auctionPausablePausedStringWord
      (auctionPausablePausedMem2From mem fmp) (fmp + (⟨68⟩ : UInt256)).toNat hgap3
  have hsize3 : 64 < mem3.size := by
    rw [hfmp68Nat] at hsz3
    omega
  have hread3 : mem3.readWithPadding 64 32 = UInt256.toByteArray fmp := by
    have hbelow : 64 + 32 ≤ (fmp + (⟨68⟩ : UInt256)).toNat := by
      rw [hfmp68Nat]
      omega
    have hpres := toByteArray_write_read_below_of_gap auctionPausablePausedStringWord
      (auctionPausablePausedMem2From mem fmp) (fmp + (⟨68⟩ : UInt256)).toNat 64
      hmem2 hbelow hgap3
    dsimp [mem3, auctionPausablePausedMem3From]
    rw [hpres]
    exact hread2
  have hawErr := auctionPausablePausedAw3From_bounds (aw := aw) (fmp := fmp)
    haw3 hawMul hfmpLe
  exact mload64_of_readWithPadding_of_aw (mem := mem3)
    (aw := auctionPausablePausedAw3From aw fmp) (val := fmp)
    hsize3 hread3 hawErr.1 hawErr.2

set_option maxHeartbeats 10000000 in
theorem auctionCreateAuction_errorStringDecoderCopyToReturnAllocFail {cA gh bl σInit σ₀ A I}
    {g : Sat256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {aw fmp off len : UInt256} {k C : ℕ} {R : List UInt256}
    (rd : RD auctionBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨6037⟩
      (len :: ⟨0xffffffffffffffff⟩ :: (fmp + off) :: off ::
        UInt256.lnot (⟨3⟩ : UInt256) :: fmp :: ⟨0⟩ :: ⟨3143⟩ :: R)
      mem aw o acc k C)
    (hguard :
      UInt256.lor
          (UInt256.gt
            (fmp +
              UInt256.land (UInt256.lnot (⟨31⟩ : UInt256))
                ((((off + len) + ⟨32⟩ : UInt256) + ⟨31⟩)))
            (⟨0xffffffffffffffff⟩ : UInt256))
          (UInt256.lt
            (fmp +
              UInt256.land (UInt256.lnot (⟨31⟩ : UInt256))
                ((((off + len) + ⟨32⟩ : UInt256) + ⟨31⟩)))
            fmp) ≠
        ⟨0⟩)
    (hov : R.length + 16 ≤ 1024) :
    RDrev auctionBytecode g (initState cA gh bl σInit σ₀ g A I) := by
  let max64 : UInt256 := ⟨0xffffffffffffffff⟩
  let payloadLen : UInt256 := (off + len) + ⟨32⟩
  let roundedLen : UInt256 :=
    UInt256.land (UInt256.lnot (⟨31⟩ : UInt256)) (payloadLen + ⟨31⟩)
  let newFree : UInt256 := fmp + roundedLen
  have hguardRev : UInt256.lor (UInt256.lt newFree fmp) (UInt256.gt newFree max64) ≠
      ⟨0⟩ := by
    intro h
    apply hguard
    rw [← u256_lor_comm] at h
    simpa [newFree, roundedLen, payloadLen, max64] using h
  have hguard' : UInt256.isZero (UInt256.lor (UInt256.lt newFree fmp)
      (UInt256.gt newFree max64)) = ⟨0⟩ := by
    exact isZero_eq_zero_of_ne hguardRev
  have rd5868₀ := evm_run rd with [
    push2 ⟨6051⟩, push1 ⟨32⟩, dup3, dup7, add, add, dup8, push2 ⟨5868⟩,
    jump (by jump_dest)]
  have rd5868 : ∃ k' C', RD auctionBytecode I g (initState cA gh bl σInit σ₀ g A I)
      ⟨5868⟩
      (fmp :: payloadLen :: ⟨6051⟩ :: len :: max64 :: (fmp + off) :: off ::
        UInt256.lnot (⟨3⟩ : UInt256) :: fmp :: ⟨0⟩ :: ⟨3143⟩ :: R)
      mem aw o acc k' C' := by
    exact ⟨_, _, by simpa [payloadLen, max64] using rd5868₀⟩
  obtain ⟨_, _, rd5868⟩ := rd5868
  have rd5869 := RD.jumpdest rd5868 (by decide)
    (by simp only [List.length_cons]; omega)
  have rd5871 := RD.push1 rd5869 ⟨31⟩ (by decide)
    (by simp only [List.length_cons]; omega)
  have rd5872 := RD.dup3 rd5871 (by decide)
    (by simp only [List.length_cons]; omega)
  have rd5873 := RD.add rd5872 (by decide)
    (by simp only [List.length_cons]; omega)
  have rd5875 := RD.push1 rd5873 ⟨31⟩ (by decide)
    (by simp only [List.length_cons]; omega)
  have rd5876 := RD.not rd5875 (by decide)
    (by simp only [List.length_cons]; omega)
  have rd5877 := RD.and rd5876 (by decide)
    (by simp only [List.length_cons]; omega)
  have rd5878 := RD.dup2 rd5877 (by decide)
    (by simp only [List.length_cons]; omega)
  have rd5879 := RD.add rd5878 (by decide)
    (by simp only [List.length_cons]; omega)
  have rd5888 := RD.pushConst rd5879 max64 (width := 8) (op := .PUSH8)
    (by decide) (by decide) (by simp only [List.length_cons]; omega)
  have rd5889 := RD.dup2 rd5888 (by decide)
    (by simp only [List.length_cons]; omega)
  have rd5890 := RD.gt rd5889 (by decide)
    (by simp only [List.length_cons]; omega)
  have rd5891 := RD.dup3 rd5890 (by decide)
    (by simp only [List.length_cons]; omega)
  have rd5892 := RD.dup3 rd5891 (by decide)
    (by simp only [List.length_cons]; omega)
  have rd5893 := RD.lt rd5892 (by decide)
    (by simp only [List.length_cons]; omega)
  have rd5894 := RD.lor rd5893 (by decide)
    (by simp only [List.length_cons]; omega)
  have rd5895₀ := RD.iszero rd5894 (by decide)
    (by simp only [List.length_cons]; omega)
  have rd5895 := rd5895₀
  rw [hguard'] at rd5895
  have rd5898 := evm_run rd5895 with [push2 ⟨5918⟩, jumpiNT (by decide)]
  have hsel : UInt256.shiftLeft (⟨0x4e487b71⟩ : UInt256) ⟨224⟩ =
      ⟨35408467139433450592217433187231851964531694900788300625387963629091585785856⟩ := by
    decide
  let panicSelector : UInt256 :=
    ⟨35408467139433450592217433187231851964531694900788300625387963629091585785856⟩
  let mem0 := (UInt256.toByteArray panicSelector).write 0 mem 0 32
  let aw0 := UInt256.ofNat (MachineState.M aw.toNat 0 32)
  have rd5907₀ := evm_run rd5898 with [push4 ⟨0x4e487b71⟩, push1 ⟨224⟩, shl]
  have rd5907 := rd5907₀
  rw [hsel] at rd5907
  have rd5909 := evm_run rd5907 with [
    push0,
    raw mstore (Cₘ aw0 - Cₘ aw) mem0 aw0 (by decide)
      (fun s haw hstk => by
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk, aw0])
      (by rfl) (by rfl) (by simp only [List.length_cons]; omega)]
  let mem1 := (UInt256.toByteArray (⟨65⟩ : UInt256)).write 0 mem0 4 32
  let aw1 := UInt256.ofNat (MachineState.M aw0.toNat 4 32)
  have rd5917 := evm_run rd5909 with [
    push1 ⟨65⟩, push1 ⟨4⟩,
    raw mstore (Cₘ aw1 - Cₘ aw0) mem1 aw1 (by decide)
      (fun s haw hstk => by
        have h4 : (⟨4⟩ : UInt256).toNat = 4 := by decide
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk, aw1, h4])
      (by rfl) (by rfl) (by simp only [List.length_cons]; omega),
    push1 ⟨36⟩, push0]
  exact RD.rev
    (Cₘ (UInt256.ofNat (MachineState.M aw1.toNat 0 36)) - Cₘ aw1)
    rd5917 (by decide)
    (fun s haw hstk => by
      have h36 : (⟨36⟩ : UInt256).toNat = 36 := by decide
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk, aw1, h36])
    (by simp only [List.length_cons]; omega)

set_option maxHeartbeats 1000000 in
theorem auctionCreateAuction_errorStringDecodedToPause {cA gh bl σInit σ₀ A I}
    {g : Sat256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {aw ptr : UInt256} {k C : ℕ} {R : List UInt256}
    (rd : RD auctionBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨3143⟩
      (ptr :: R) mem aw o acc k C)
    (hptr : ptr ≠ ⟨0⟩)
    (hov : R.length + 4 ≤ 1024) :
    ∃ k' C', RD auctionBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨3655⟩
      (⟨2850⟩ :: ptr :: R) mem aw o acc k' C' := by
  have rd3148 := evm_run rd with [jumpdest, dup1, push2 ⟨3154⟩]
  have rd3154 := RD.jumpiT rd3148 (by decide) hptr (by jump_dest)
    (by simp only [List.length_cons]; omega)
  exact ⟨_, _, evm_run rd3154 with [
    jumpdest, push2 ⟨2850⟩, push2 ⟨3655⟩, jump (by jump_dest)]⟩

set_option maxHeartbeats 1000000 in
theorem auctionCreateAuction_errorStringDecodedNullRevert {cA gh bl σInit σ₀ A I}
    {g : Sat256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {aw : UInt256} {k C : ℕ} {R : List UInt256}
    (rd : RD auctionBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨3143⟩
      (⟨0⟩ :: R) mem aw o acc k C)
    (hosz : o.size < UInt256.size) (hov : R.length + 8 ≤ 1024) :
    RDrev auctionBytecode g (initState cA gh bl σInit σ₀ g A I) := by
  have rd3165 := evm_run rd with [
    jumpdest, dup1, push2 ⟨3154⟩, jumpiNT (by decide), pop,
    push2 ⟨3164⟩, jump (by jump_dest), jumpdest]
  exact auctionCreateAuction_mintCallFailureBubbleRevertTail
    (mem := mem) (aw := aw) rd3165 hosz hov

set_option maxHeartbeats 1000000 in
theorem auctionCreateAuction_errorStringPauseReturnTail {cA gh bl σInit σ₀ A I}
    {g : Sat256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {aw ptr : UInt256} {k C : ℕ}
    (rd : RD auctionBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨2850⟩
      [ptr, ⟨1163⟩, ⟨413⟩, auctionSelWord I] mem aw o acc k C) :
    RDret auctionBytecode g (initState cA gh bl σInit σ₀ g A I) acc ByteArray.empty := by
  have rd1163 := evm_run rd with [jumpdest, pop, jump (by jump_dest), jumpdest]
  have rd413 := evm_run rd1163 with [jump (by jump_dest), jumpdest]
  exact rd413.stop (by decide) (by evm_ov)

set_option maxHeartbeats 10000000 in
theorem auctionPauseRoutine_revert_paused_from_mem {cA accA gh bl σInit σ σ₀ A I}
    {g : Sat256}
    {mem rdata : ByteArray} {aw fmp : UInt256} {k C : ℕ} {ret : UInt256}
    {R : List UInt256}
    (hperm : I.perm = true)
    (hnz : auctionPausedWord σ I ≠ ⟨0⟩)
    (hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size ∨ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        fmp)
    (hmload64Err :
      (if (⟨64⟩ : UInt256).toNat ≥ (auctionPausablePausedMem3From mem fmp).size ∨
          (⟨64⟩ : UInt256) ≥ auctionPausablePausedAw3From aw fmp * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          ((auctionPausablePausedMem3From mem fmp).readWithPadding
            (⟨64⟩ : UInt256).toNat 32))) =
        fmp)
    (hlen100 : UInt256.sub ((⟨100⟩ : UInt256) + fmp) fmp = ⟨100⟩)
    (hov : R.length + 8 ≤ 1024)
    (h : RD auctionBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨3655⟩
      (ret :: R) mem aw rdata (accA, σ) k C) :
    RDrev auctionBytecode g (initState cA gh bl σInit σ₀ g A I) := by
  have rd3663₀ := evm_run h with [jumpdest, push1 ⟨51⟩]
  obtain ⟨_, _, rd3659₀⟩ := rd3663₀.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd3659⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σInit σ₀ g A I) ⟨3659⟩
      (auctionSlotWord ⟨51⟩ σ I :: ret :: R) mem aw rdata (accA, σ) k C := by
    exact ⟨_, _, by simpa [auctionSlotWord] using rd3659₀⟩
  have rd3663 := evm_run rd3659 with [push1 ⟨255⟩, and, iszero]
  have hmask : UInt256.land ⟨255⟩ (auctionSlotWord ⟨51⟩ σ I) = auctionPausedWord σ I := by
    rw [auctionPausedWord, u256_land_comm]
  have hcond : UInt256.isZero (UInt256.land ⟨255⟩ (auctionSlotWord ⟨51⟩ σ I)) = ⟨0⟩ := by
    exact isZero_eq_zero_of_ne (by simpa [hmask] using hnz)
  have rd3667 := evm_run rd3663 with [
    push2 ⟨3725⟩, jumpiNT hcond]
  let aw64 := UInt256.ofNat (MachineState.M aw.toNat (⟨64⟩ : UInt256).toNat 32)
  have rd3670 := evm_run rd3667 with [
    push1 ⟨64⟩,
    raw mload (Cₘ aw64 - Cₘ aw) fmp aw64 (by decide)
      (fun s haw hstk => by
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk, aw64])
      hmload64 (by rfl) (by simp only [List.length_cons]; omega)]
  have rd3674 := rd3670.pushConst (⟨0x461bcd⟩ : UInt256) (width := 3) (op := .PUSH3)
    (by decide) (by decide) (by evm_ov)
  let mem0 := auctionPausablePausedMem0From mem fmp
  let aw0 := UInt256.ofNat (MachineState.M aw64.toNat fmp.toNat 32)
  let mem1 := auctionPausablePausedMem1From mem fmp
  let aw1 := UInt256.ofNat (MachineState.M aw0.toNat (fmp + (⟨4⟩ : UInt256)).toNat 32)
  let mem2 := auctionPausablePausedMem2From mem fmp
  let aw2 := UInt256.ofNat (MachineState.M aw1.toNat (fmp + (⟨36⟩ : UInt256)).toNat 32)
  let mem3 := auctionPausablePausedMem3From mem fmp
  let aw3 := UInt256.ofNat (MachineState.M aw2.toNat (fmp + (⟨68⟩ : UInt256)).toNat 32)
  have rd3693 := evm_run rd3674 with [
    push1 ⟨229⟩, shl, dup2,
    raw mstore (Cₘ aw0 - Cₘ aw64) mem0 aw0
      (by decide)
      (fun s haw hstk => by
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk, aw0])
      (by rfl) (by rfl) (by simp only [List.length_cons]; omega),
    push1 ⟨32⟩, push1 ⟨4⟩, dup3, add,
    raw mstore (Cₘ aw1 - Cₘ aw0) mem1 aw1
      (by decide)
      (fun s haw hstk => by
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk, aw1])
      (by rfl) (by rfl) (by simp only [List.length_cons]; omega),
    push1 ⟨16⟩, push1 ⟨36⟩, dup3, add,
    raw mstore (Cₘ aw2 - Cₘ aw1) mem2 aw2
      (by decide)
      (fun s haw hstk => by
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk, aw2])
      (by rfl) (by rfl) (by simp only [List.length_cons]; omega)]
  have rd3710 := rd3693.pushConst auctionPausablePausedRawStringWord
    (width := 16) (op := .PUSH16) (by decide) (by decide) (by evm_ov)
  have rd3713₀ := evm_run rd3710 with [push1 ⟨130⟩, shl]
  have hword :
      UInt256.shiftLeft auctionPausablePausedRawStringWord ⟨130⟩ =
        auctionPausablePausedStringWord := by
    native_decide
  have rd3713 := rd3713₀
  rw [hword] at rd3713
  have rd3721₀ := evm_run rd3713 with [
    push1 ⟨68⟩, dup3, add,
    raw mstore (Cₘ aw3 - Cₘ aw2) mem3 aw3
      (by decide)
      (fun s haw hstk => by
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk, aw3])
      (by rfl) (by rfl) (by simp only [List.length_cons]; omega),
    push1 ⟨100⟩, add]
  have rd3721 := rd3721₀
  have rd994 := evm_run rd3721 with [push2 ⟨994⟩, jump (by jump_dest)]
  let aw64Err := UInt256.ofNat (MachineState.M aw3.toNat (⟨64⟩ : UInt256).toNat 32)
  have rd1001₀ := evm_run rd994 with [
    jumpdest, push1 ⟨64⟩,
    raw mload (Cₘ aw64Err - Cₘ aw3) fmp aw64Err (by decide)
      (fun s haw hstk => by
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk, aw64Err])
      (by
        simpa [mem3, aw3, aw2, aw1, aw0, aw64, auctionPausablePausedAw3From,
          auctionPausablePausedAw2From, auctionPausablePausedAw1From,
          auctionPausablePausedAw0From, auctionPausablePausedAw64From] using hmload64Err)
      (by rfl)
      (by simp only [List.length_cons]; omega),
    dup1, swap2, sub, swap1]
  have rd1001 := rd1001₀
  rw [hlen100] at rd1001
  exact RD.rev
    (Cₘ (UInt256.ofNat (MachineState.M aw64Err.toNat fmp.toNat (⟨100⟩ : UInt256).toNat)) -
      Cₘ aw64Err)
    rd1001 (by decide)
    (fun s haws hstks => by
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks, aw64Err])
    (by simp only [List.length_cons]; omega)

set_option maxHeartbeats 1000000 in
theorem auctionPauseRoutine_success_from_mem {cA accA gh bl σInit σ σ₀ A I} {g : Sat256}
    {mem rdata : ByteArray} {aw fmp : UInt256} {k C : ℕ} {ret : UInt256}
    {R : List UInt256}
    (hperm : I.perm = true)
    (hzero : auctionPausedWord σ I = ⟨0⟩)
    (hret : (D_J auctionBytecode 0).contains ret = true)
    (hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size ∨ (⟨64⟩ : UInt256) ≥ aw * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        fmp)
    (hmload64Event :
      (if (⟨64⟩ : UInt256).toNat ≥ (auctionEventMemFrom mem I fmp).size ∨
          (⟨64⟩ : UInt256) ≥
            (UInt256.ofNat
              (MachineState.M
                (UInt256.ofNat (MachineState.M aw.toNat (⟨64⟩ : UInt256).toNat 32)).toNat
                fmp.toNat 32)) * ⟨32⟩ then
          ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          ((auctionEventMemFrom mem I fmp).readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        fmp)
    (hlen32 : UInt256.sub ((⟨32⟩ : UInt256) + fmp) fmp = ⟨32⟩)
    (hov : R.length + 8 ≤ 1024)
    (h : RD auctionBytecode I g (initState cA gh bl σInit σ₀ g A I) ⟨3655⟩
      (ret :: R) mem aw rdata (accA, σ) k C) :
    ∃ mem' aw' k' C',
      RD auctionBytecode I g (initState cA gh bl σInit σ₀ g A I) ret R mem' aw' rdata
        (accA, auctionPausePostMap σ I) k' C' := by
  have rd3663₀ := evm_run h with [jumpdest, push1 ⟨51⟩]
  obtain ⟨_, _, rd3659₀⟩ := rd3663₀.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd3659⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σInit σ₀ g A I) ⟨3659⟩
      (auctionSlotWord ⟨51⟩ σ I :: ret :: R) mem aw rdata (accA, σ) k C := by
    exact ⟨_, _, by simpa [auctionSlotWord] using rd3659₀⟩
  have rd3663 := evm_run rd3659 with [push1 ⟨255⟩, and, iszero]
  have hmask : UInt256.land ⟨255⟩ (auctionSlotWord ⟨51⟩ σ I) = auctionPausedWord σ I := by
    rw [auctionPausedWord, u256_land_comm]
  have hcond : UInt256.isZero (UInt256.land ⟨255⟩ (auctionSlotWord ⟨51⟩ σ I)) ≠ ⟨0⟩ := by
    rw [hmask, hzero]
    decide
  have rd3725 := evm_run rd3663 with [
    push2 ⟨3725⟩, jumpiT hcond (by jump_dest), jumpdest]
  have rd3734₀ := evm_run rd3725 with [push1 ⟨51⟩, dup1]
  obtain ⟨_, _, rd3730₀⟩ := rd3734₀.sload (by decide) (by evm_ov)
  obtain ⟨_, _, rd3730⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σInit σ₀ g A I) ⟨3730⟩
      (auctionSlotWord ⟨51⟩ σ I :: ⟨51⟩ :: ret :: R) mem aw rdata (accA, σ) k C := by
    exact ⟨_, _, by simpa [auctionSlotWord] using rd3730₀⟩
  have rd3737₀ := evm_run rd3730 with [push1 ⟨255⟩, not, and, push1 ⟨1⟩]
  have rd3737₁ := rd3737₀
  have hland : UInt256.land (UInt256.lnot ⟨255⟩) (auctionSlotWord ⟨51⟩ σ I) =
      UInt256.land (auctionSlotWord ⟨51⟩ σ I) (UInt256.lnot ⟨255⟩) := by
    exact u256_land_comm (UInt256.lnot ⟨255⟩) (auctionSlotWord ⟨51⟩ σ I)
  rw [hland] at rd3737₁
  have rd3737₂ := RD.lor rd3737₁ (by decide) (by evm_ov)
  have hlor :
      UInt256.lor ⟨1⟩
          (UInt256.land (auctionSlotWord ⟨51⟩ σ I) (UInt256.lnot ⟨255⟩)) =
        auctionPausedSetTrueWord (auctionSlotWord ⟨51⟩ σ I) := by
    unfold auctionPausedSetTrueWord
    exact u256_lor_comm ⟨1⟩
      (UInt256.land (auctionSlotWord ⟨51⟩ σ I) (UInt256.lnot ⟨255⟩))
  rw [hlor] at rd3737₂
  have rd3738 := evm_run rd3737₂ with [swap1]
  obtain ⟨_, _, rd3739₀⟩ := rd3738.sstore hperm (by decide) (by evm_ov)
  obtain ⟨_, _, rd3739⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σInit σ₀ g A I) ⟨3739⟩ (ret :: R) mem aw rdata
      (accA, auctionPausePostMap σ I) k C := by
    exact ⟨_, _, by simpa [auctionPausePostMap] using rd3739₀⟩
  have rd3772 := rd3739.pushConst auctionPausedTopic (width := 32) (op := .PUSH32)
    (by decide) (by decide) (by evm_ov)
  have rd2971 := evm_run rd3772 with [push2 ⟨2971⟩, caller, swap1, jump (by jump_dest)]
  let aw64 := UInt256.ofNat (MachineState.M aw.toNat (⟨64⟩ : UInt256).toNat 32)
  have rd2988₀ := evm_run rd2971 with [
    jumpdest, push1 ⟨64⟩,
    raw mload (Cₘ aw64 - Cₘ aw) fmp aw64 (by decide)
      (fun s haw hstk => by
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk, aw64])
      hmload64 (by rfl) (by simp only [List.length_cons]; omega),
    push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, swap1, swap2, and, dup2]
  have rd2988 := rd2988₀
  have haddrMask : UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask := by
    decide
  rw [haddrMask] at rd2988
  have hcaller : UInt256.land (UInt256.ofNat I.source.val) solcAddrMask = auctionSourceWord I := by
    rw [u256_land_comm]
    simpa [auctionSourceWord] using solcAddrMask_clean_left (auctionSourceWord_canonical I)
  rw [hcaller] at rd2988
  let awEvent := UInt256.ofNat (MachineState.M aw64.toNat fmp.toNat 32)
  have rd2991 := evm_run rd2988 with [
    raw mstore (Cₘ awEvent - Cₘ aw64) (auctionEventMemFrom mem I fmp) awEvent
      (by decide)
      (fun s haw hstk => by
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk, awEvent])
      (by rfl) (by rfl) (by simp only [List.length_cons]; omega)]
  let aw64Event := UInt256.ofNat (MachineState.M awEvent.toNat (⟨64⟩ : UInt256).toNat 32)
  have rd2998₀ := evm_run rd2991 with [
    push1 ⟨32⟩, add, push1 ⟨64⟩,
    raw mload (Cₘ aw64Event - Cₘ awEvent) fmp aw64Event (by decide)
      (fun s haw hstk => by
        simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk, aw64Event])
      (by simpa [aw64, awEvent] using hmload64Event) (by rfl)
      (by simp only [List.length_cons]; omega),
    dup1, swap2, sub, swap1]
  have rd2998 := rd2998₀
  rw [hlen32] at rd2998
  let awLog :=
    UInt256.ofNat
      (MachineState.M aw64Event.toNat fmp.toNat
        (⟨32⟩ : UInt256).toNat)
  have rd2999 := RD.log1 (Cₘ awLog - Cₘ aw64Event) awLog rd2998 (by decide) hperm
    (fun s haw hstk => by
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', haw, hstk, awLog])
    (by rfl) (by simp only [List.length_cons]; omega)
  exact ⟨_, _, _, _, evm_run rd2999 with [jump hret]⟩

end Auction
