import Benchmarks.Auction.InitializeSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Refinement

set_option maxRecDepth 50000000

namespace Auction

theorem auctionDispatch_initialize {I : ExecutionEnv}
    (hsel : selIs I (auctionSelBytes 11)) :
    dispatchMsg auctionContract I.calldata = some initializeTransition := by
  apply dispatchMsg_eq_some_of_split (hfallback := by rfl)
    (pre := [])
    (post := [createBidTransition, settleAndCreateTransition, settleAuctionTransition,
      pauseTransition, unpauseTransition, setTimeBufferTransition, setReservePriceTransition,
      setMinBidIncTransition, transferOwnershipTransition, renounceOwnershipTransition,
      ownerGetter, pausedGetter, nounsGetter, wethGetter, timeBufferGetter, reservePriceGetter,
      minBidIncGetter, durationGetter, auctionGetter])
    (ti := initializeTransition)
    (htr := by rfl)
  · intro t ht
    simp at ht
  · rw [selectorOf, initializeSelectorBytes]
    simpa [selIs, auctionSelBytes] using hsel

-- LIBRARY CANDIDATE: ABI scalar-word decode for
-- `(address,address,uint256,uint256,uint8,uint256)`.
theorem auctionDecodeScalarWords_initialize_ok {bytes : List UInt8}
    (hlen0 : (bytes.take 32).length = 32)
    (hlen32 : ((bytes.drop 32).take 32).length = 32)
    (hlen64 : ((bytes.drop 64).take 32).length = 32)
    (hlen96 : ((bytes.drop 96).take 32).length = 32)
    (hlen128 : ((bytes.drop 128).take 32).length = 32)
    (hlen160 : ((bytes.drop 160).take 32).length = 32)
    (hcanon0 : (ABI.bytesToWord (bytes.take 32)).toNat < EVM.addressModulus)
    (hcanon32 : (ABI.bytesToWord ((bytes.drop 32).take 32)).toNat < EVM.addressModulus)
    (hcanon128 : (ABI.bytesToWord ((bytes.drop 128).take 32)).toNat < EVM.twoPow 8) :
    decodeScalarWords? [addr, addr, uint256, uint256, uint8, uint256] bytes 0 =
      some [.address (AccountAddress.ofNat (ABI.bytesToWord (bytes.take 32)).toNat),
        .address (AccountAddress.ofNat
          (ABI.bytesToWord ((bytes.drop 32).take 32)).toNat),
        .int (Int.ofNat (ABI.bytesToWord ((bytes.drop 64).take 32)).toNat),
        .int (Int.ofNat (ABI.bytesToWord ((bytes.drop 96).take 32)).toNat),
        .int (Int.ofNat (ABI.bytesToWord ((bytes.drop 128).take 32)).toNat),
        .int (Int.ofNat (ABI.bytesToWord ((bytes.drop 160).take 32)).toNat)] := by
  simp only [decodeScalarWords?, Nat.zero_add, addr, uint256, uint256Int]
  rw [decodeScalarWord_address_ok (start := 0) (by simpa using hlen0)
    (by simpa using hcanon0)]
  simp only [Option.bind, bind]
  rw [decodeScalarWord_address_ok (start := 32) hlen32 hcanon32]
  rw [decodeScalarWord_uint256_ok (start := 64) hlen64]
  rw [decodeScalarWord_uint256_ok (start := 96) hlen96]
  rw [auctionDecodeScalarWord_uint8_ok (start := 128) hlen128 hcanon128]
  rw [decodeScalarWord_uint256_ok (start := 160) hlen160]
  rfl

-- LIBRARY CANDIDATE: first address non-canonical branch for
-- `(address,address,uint256,uint256,uint8,uint256)`.
theorem auctionDecodeScalarWords_initialize_none_noncanon0 {bytes : List UInt8}
    (hlen0 : (bytes.take 32).length = 32)
    (hnc0 : ¬ (ABI.bytesToWord (bytes.take 32)).toNat < EVM.addressModulus) :
    decodeScalarWords? [addr, addr, uint256, uint256, uint8, uint256] bytes 0 = none := by
  simp only [decodeScalarWords?, Nat.zero_add, addr, uint256, uint256Int]
  rw [decodeScalarWord_address_none_noncanon (start := 0) (by simpa using hlen0)
    (by simpa using hnc0)]
  simp only [Option.bind, bind]

-- LIBRARY CANDIDATE: second address non-canonical branch for
-- `(address,address,uint256,uint256,uint8,uint256)`.
theorem auctionDecodeScalarWords_initialize_none_noncanon1 {bytes : List UInt8}
    (hlen0 : (bytes.take 32).length = 32)
    (hlen32 : ((bytes.drop 32).take 32).length = 32)
    (hcanon0 : (ABI.bytesToWord (bytes.take 32)).toNat < EVM.addressModulus)
    (hnc32 : ¬ (ABI.bytesToWord ((bytes.drop 32).take 32)).toNat < EVM.addressModulus) :
    decodeScalarWords? [addr, addr, uint256, uint256, uint8, uint256] bytes 0 = none := by
  simp only [decodeScalarWords?, Nat.zero_add, addr, uint256, uint256Int]
  rw [decodeScalarWord_address_ok (start := 0) (by simpa using hlen0)
    (by simpa using hcanon0)]
  simp only [Option.bind, bind]
  rw [decodeScalarWord_address_none_noncanon (start := 32) hlen32 hnc32]

-- LIBRARY CANDIDATE: uint8 non-canonical branch for
-- `(address,address,uint256,uint256,uint8,uint256)`.
theorem auctionDecodeScalarWords_initialize_none_noncanon4 {bytes : List UInt8}
    (hlen0 : (bytes.take 32).length = 32)
    (hlen32 : ((bytes.drop 32).take 32).length = 32)
    (hlen64 : ((bytes.drop 64).take 32).length = 32)
    (hlen96 : ((bytes.drop 96).take 32).length = 32)
    (hlen128 : ((bytes.drop 128).take 32).length = 32)
    (hcanon0 : (ABI.bytesToWord (bytes.take 32)).toNat < EVM.addressModulus)
    (hcanon32 : (ABI.bytesToWord ((bytes.drop 32).take 32)).toNat < EVM.addressModulus)
    (hnc128 : ¬ (ABI.bytesToWord ((bytes.drop 128).take 32)).toNat < EVM.twoPow 8) :
    decodeScalarWords? [addr, addr, uint256, uint256, uint8, uint256] bytes 0 = none := by
  simp only [decodeScalarWords?, Nat.zero_add, addr, uint256, uint256Int]
  rw [decodeScalarWord_address_ok (start := 0) (by simpa using hlen0)
    (by simpa using hcanon0)]
  simp only [Option.bind, bind]
  rw [decodeScalarWord_address_ok (start := 32) hlen32 hcanon32]
  rw [decodeScalarWord_uint256_ok (start := 64) hlen64]
  rw [decodeScalarWord_uint256_ok (start := 96) hlen96]
  rw [auctionDecodeScalarWord_uint8_none_noncanon (start := 128) hlen128 hnc128]

-- LIBRARY CANDIDATE: short calldata branch for
-- `(address,address,uint256,uint256,uint8,uint256)`.
theorem auctionDecodeScalarWords_initialize_none_short {bytes : List UInt8}
    (hshort : bytes.length < 192) :
    decodeScalarWords? [addr, addr, uint256, uint256, uint8, uint256] bytes 0 = none := by
  cases hdec :
      decodeScalarWords? [addr, addr, uint256, uint256, uint8, uint256] bytes 0 with
  | none => rfl
  | some values =>
      have hlen := decodeScalarWords?_some_length (types :=
        [addr, addr, uint256, uint256, uint8, uint256]) (bytes := bytes) (cursor := 0)
        (values := values) (Nat.zero_le _) hdec
      exfalso
      norm_num at hlen
      omega

theorem auctionDecode_initialize {I : ExecutionEnv}
    (hsz196 : 196 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hcanonNouns : (auctionInitializeNounsWord I).toNat < EVM.addressModulus)
    (hcanonWeth : (auctionInitializeWethWord I).toNat < EVM.addressModulus)
    (hcanonMinBid : (auctionInitializeMinBidIncrementPercentageWord I).toNat <
      EVM.twoPow 8) :
    decodeCalldataWithMode auctionConfig.abiDecodeMode
        (initializeTransition.params.map Param.name)
        (transitionSignature initializeTransition).paramTypes I.calldata =
      some (auctionInitializeStore I) := by
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have htake4 : ((I.calldata.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have htake36 : ((I.calldata.toList.drop 36).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have htake68 : ((I.calldata.toList.drop 68).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have htake100 : ((I.calldata.toList.drop 100).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have htake132 : ((I.calldata.toList.drop 132).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have htake164 : ((I.calldata.toList.drop 164).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have hword4 : ABI.bytesToWord ((I.calldata.toList.drop 4).take 32) =
      auctionInitializeNounsWord I := by
    simpa [auctionInitializeNounsWord] using decode_word_at_eq I.calldata 4 (by omega)
      (by norm_num)
  have hword36 : ABI.bytesToWord ((I.calldata.toList.drop 36).take 32) =
      auctionInitializeWethWord I := by
    simpa [auctionInitializeWethWord] using decode_word_at_eq I.calldata 36 (by omega)
      (by norm_num)
  have hword68 : ABI.bytesToWord ((I.calldata.toList.drop 68).take 32) =
      auctionInitializeTimeBufferWord I := by
    simpa [auctionInitializeTimeBufferWord] using decode_word_at_eq I.calldata 68 (by omega)
      (by norm_num)
  have hword100 : ABI.bytesToWord ((I.calldata.toList.drop 100).take 32) =
      auctionInitializeReservePriceWord I := by
    simpa [auctionInitializeReservePriceWord] using decode_word_at_eq I.calldata 100
      (by omega) (by norm_num)
  have hword132 : ABI.bytesToWord ((I.calldata.toList.drop 132).take 32) =
      auctionInitializeMinBidIncrementPercentageWord I := by
    simpa [auctionInitializeMinBidIncrementPercentageWord] using
      decode_word_at_eq I.calldata 132 (by omega) (by norm_num)
  have hword164 : ABI.bytesToWord ((I.calldata.toList.drop 164).take 32) =
      auctionInitializeDurationWord I := by
    simpa [auctionInitializeDurationWord] using decode_word_at_eq I.calldata 164
      (by omega) (by norm_num)
  have htake36' : (((I.calldata.toList.drop 4).drop 32).take 32).length = 32 := by
    simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using htake36
  have htake68' : (((I.calldata.toList.drop 4).drop 64).take 32).length = 32 := by
    simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using htake68
  have htake100' : (((I.calldata.toList.drop 4).drop 96).take 32).length = 32 := by
    simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using htake100
  have htake132' : (((I.calldata.toList.drop 4).drop 128).take 32).length = 32 := by
    simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using htake132
  have htake164' : (((I.calldata.toList.drop 4).drop 160).take 32).length = 32 := by
    simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using htake164
  show decodeCalldata ["_nouns", "_weth", "_timeBuffer", "_reservePrice",
      "_minBidIncrementPercentage", "_duration"] [addr, addr, uint256, uint256, uint8,
        uint256] I.calldata =
    some (auctionInitializeStore I)
  rw [decodeCalldata_scalarWords_eq (names :=
    ["_nouns", "_weth", "_timeBuffer", "_reservePrice", "_minBidIncrementPercentage",
      "_duration"]) (types := [addr, addr, uint256, uint256, uint8, uint256])
      (cd := I.calldata) (by decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ I.calldata.toList.length < 4)]
  rw [if_neg (by rintro ⟨_, hc⟩; rw [List.length_drop, htlen] at hc; omega)]
  rw [auctionDecodeScalarWords_initialize_ok (bytes := I.calldata.toList.drop 4)
    htake4 htake36' htake68' htake100' htake132' htake164'
    (by rw [hword4]; exact hcanonNouns)
    (by
      rw [show ABI.bytesToWord (((I.calldata.toList.drop 4).drop 32).take 32) =
          auctionInitializeWethWord I from by
        simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hword36]
      exact hcanonWeth)
    (by
      rw [show ABI.bytesToWord (((I.calldata.toList.drop 4).drop 128).take 32) =
          auctionInitializeMinBidIncrementPercentageWord I from by
        simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hword132]
      exact hcanonMinBid)]
  change decodeCalldata.insertValues
      ["_nouns", "_weth", "_timeBuffer", "_reservePrice", "_minBidIncrementPercentage",
        "_duration"]
      [.address (AccountAddress.ofNat
          (ABI.bytesToWord ((I.calldata.toList.drop 4).take 32)).toNat),
        .address (AccountAddress.ofNat
          (ABI.bytesToWord (((I.calldata.toList.drop 4).drop 32).take 32)).toNat),
        .int (Int.ofNat
          (ABI.bytesToWord (((I.calldata.toList.drop 4).drop 64).take 32)).toNat),
        .int (Int.ofNat
          (ABI.bytesToWord (((I.calldata.toList.drop 4).drop 96).take 32)).toNat),
        .int (Int.ofNat
          (ABI.bytesToWord (((I.calldata.toList.drop 4).drop 128).take 32)).toNat),
        .int (Int.ofNat
          (ABI.bytesToWord (((I.calldata.toList.drop 4).drop 160).take 32)).toNat)] ∅ =
    some (auctionInitializeStore I)
  simp only [List.drop_drop, Nat.reduceAdd]
  rw [hword4, hword36, hword68, hword100, hword132, hword164]
  rfl

theorem auctionDecode_initialize_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 196) :
    decodeCalldataWithMode auctionConfig.abiDecodeMode
        (initializeTransition.params.map Param.name)
        (transitionSignature initializeTransition).paramTypes I.calldata = none := by
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  show decodeCalldata ["_nouns", "_weth", "_timeBuffer", "_reservePrice",
      "_minBidIncrementPercentage", "_duration"] [addr, addr, uint256, uint256, uint8,
        uint256] I.calldata = none
  rw [decodeCalldata_scalarWords_eq (names :=
    ["_nouns", "_weth", "_timeBuffer", "_reservePrice", "_minBidIncrementPercentage",
      "_duration"]) (types := [addr, addr, uint256, uint256, uint8, uint256])
      (cd := I.calldata) (by decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ I.calldata.toList.length < 4)]
  rw [if_neg (by rintro ⟨_, hc⟩; rw [List.length_drop, htlen] at hc; omega)]
  rw [auctionDecodeScalarWords_initialize_none_short (bytes := I.calldata.toList.drop 4) (by
    rw [List.length_drop, htlen]
    omega)]

theorem auctionDecode_initialize_none_huge {I : ExecutionEnv}
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) :
    decodeCalldataWithMode auctionConfig.abiDecodeMode
        (initializeTransition.params.map Param.name)
        (transitionSignature initializeTransition).paramTypes I.calldata = none := by
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  show decodeCalldata ["_nouns", "_weth", "_timeBuffer", "_reservePrice",
      "_minBidIncrementPercentage", "_duration"] [addr, addr, uint256, uint256, uint8,
        uint256] I.calldata = none
  rw [decodeCalldata_scalarWords_eq (names :=
    ["_nouns", "_weth", "_timeBuffer", "_reservePrice", "_minBidIncrementPercentage",
      "_duration"]) (types := [addr, addr, uint256, uint256, uint8, uint256])
      (cd := I.calldata) (by decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ I.calldata.toList.length < 4)]
  rw [if_pos]
  · exact ⟨rfl, by rw [List.length_drop, htlen]; omega⟩

theorem auctionDecode_initialize_none_noncanon_nouns {I : ExecutionEnv}
    (hsz196 : 196 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hnc : ¬ (auctionInitializeNounsWord I).toNat < EVM.addressModulus) :
    decodeCalldataWithMode auctionConfig.abiDecodeMode
        (initializeTransition.params.map Param.name)
        (transitionSignature initializeTransition).paramTypes I.calldata = none := by
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have htake4 : ((I.calldata.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have hword4 : ABI.bytesToWord ((I.calldata.toList.drop 4).take 32) =
      auctionInitializeNounsWord I := by
    simpa [auctionInitializeNounsWord] using decode_word_at_eq I.calldata 4 (by omega)
      (by norm_num)
  show decodeCalldata ["_nouns", "_weth", "_timeBuffer", "_reservePrice",
      "_minBidIncrementPercentage", "_duration"] [addr, addr, uint256, uint256, uint8,
        uint256] I.calldata = none
  rw [decodeCalldata_scalarWords_eq (names :=
    ["_nouns", "_weth", "_timeBuffer", "_reservePrice", "_minBidIncrementPercentage",
      "_duration"]) (types := [addr, addr, uint256, uint256, uint8, uint256])
      (cd := I.calldata) (by decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ I.calldata.toList.length < 4)]
  rw [if_neg (by rintro ⟨_, hc⟩; rw [List.length_drop, htlen] at hc; omega)]
  rw [auctionDecodeScalarWords_initialize_none_noncanon0 (bytes := I.calldata.toList.drop 4)
    htake4 (by rw [hword4]; exact hnc)]

theorem auctionDecode_initialize_none_noncanon_weth {I : ExecutionEnv}
    (hsz196 : 196 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hcanonNouns : (auctionInitializeNounsWord I).toNat < EVM.addressModulus)
    (hnc : ¬ (auctionInitializeWethWord I).toNat < EVM.addressModulus) :
    decodeCalldataWithMode auctionConfig.abiDecodeMode
        (initializeTransition.params.map Param.name)
        (transitionSignature initializeTransition).paramTypes I.calldata = none := by
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have htake4 : ((I.calldata.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have htake36 : ((I.calldata.toList.drop 36).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have hword4 : ABI.bytesToWord ((I.calldata.toList.drop 4).take 32) =
      auctionInitializeNounsWord I := by
    simpa [auctionInitializeNounsWord] using decode_word_at_eq I.calldata 4 (by omega)
      (by norm_num)
  have hword36 : ABI.bytesToWord ((I.calldata.toList.drop 36).take 32) =
      auctionInitializeWethWord I := by
    simpa [auctionInitializeWethWord] using decode_word_at_eq I.calldata 36 (by omega)
      (by norm_num)
  have htake36' : (((I.calldata.toList.drop 4).drop 32).take 32).length = 32 := by
    simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using htake36
  show decodeCalldata ["_nouns", "_weth", "_timeBuffer", "_reservePrice",
      "_minBidIncrementPercentage", "_duration"] [addr, addr, uint256, uint256, uint8,
        uint256] I.calldata = none
  rw [decodeCalldata_scalarWords_eq (names :=
    ["_nouns", "_weth", "_timeBuffer", "_reservePrice", "_minBidIncrementPercentage",
      "_duration"]) (types := [addr, addr, uint256, uint256, uint8, uint256])
      (cd := I.calldata) (by decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ I.calldata.toList.length < 4)]
  rw [if_neg (by rintro ⟨_, hc⟩; rw [List.length_drop, htlen] at hc; omega)]
  rw [auctionDecodeScalarWords_initialize_none_noncanon1 (bytes := I.calldata.toList.drop 4)
    htake4 htake36' (by rw [hword4]; exact hcanonNouns)
    (by
      rw [show ABI.bytesToWord (((I.calldata.toList.drop 4).drop 32).take 32) =
          auctionInitializeWethWord I from by
        simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hword36]
      exact hnc)]

theorem auctionDecode_initialize_none_noncanon_minBid {I : ExecutionEnv}
    (hsz196 : 196 ≤ I.calldata.size) (hbig : I.calldata.size < 2 ^ 255 + 4)
    (hcanonNouns : (auctionInitializeNounsWord I).toNat < EVM.addressModulus)
    (hcanonWeth : (auctionInitializeWethWord I).toNat < EVM.addressModulus)
    (hnc : ¬ (auctionInitializeMinBidIncrementPercentageWord I).toNat < EVM.twoPow 8) :
    decodeCalldataWithMode auctionConfig.abiDecodeMode
        (initializeTransition.params.map Param.name)
        (transitionSignature initializeTransition).paramTypes I.calldata = none := by
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have htake4 : ((I.calldata.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have htake36 : ((I.calldata.toList.drop 36).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have htake68 : ((I.calldata.toList.drop 68).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have htake100 : ((I.calldata.toList.drop 100).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have htake132 : ((I.calldata.toList.drop 132).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have hword4 : ABI.bytesToWord ((I.calldata.toList.drop 4).take 32) =
      auctionInitializeNounsWord I := by
    simpa [auctionInitializeNounsWord] using decode_word_at_eq I.calldata 4 (by omega)
      (by norm_num)
  have hword36 : ABI.bytesToWord ((I.calldata.toList.drop 36).take 32) =
      auctionInitializeWethWord I := by
    simpa [auctionInitializeWethWord] using decode_word_at_eq I.calldata 36 (by omega)
      (by norm_num)
  have hword132 : ABI.bytesToWord ((I.calldata.toList.drop 132).take 32) =
      auctionInitializeMinBidIncrementPercentageWord I := by
    simpa [auctionInitializeMinBidIncrementPercentageWord] using
      decode_word_at_eq I.calldata 132 (by omega) (by norm_num)
  have htake36' : (((I.calldata.toList.drop 4).drop 32).take 32).length = 32 := by
    simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using htake36
  have htake68' : (((I.calldata.toList.drop 4).drop 64).take 32).length = 32 := by
    simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using htake68
  have htake100' : (((I.calldata.toList.drop 4).drop 96).take 32).length = 32 := by
    simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using htake100
  have htake132' : (((I.calldata.toList.drop 4).drop 128).take 32).length = 32 := by
    simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using htake132
  show decodeCalldata ["_nouns", "_weth", "_timeBuffer", "_reservePrice",
      "_minBidIncrementPercentage", "_duration"] [addr, addr, uint256, uint256, uint8,
        uint256] I.calldata = none
  rw [decodeCalldata_scalarWords_eq (names :=
    ["_nouns", "_weth", "_timeBuffer", "_reservePrice", "_minBidIncrementPercentage",
      "_duration"]) (types := [addr, addr, uint256, uint256, uint8, uint256])
      (cd := I.calldata) (by decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ I.calldata.toList.length < 4)]
  rw [if_neg (by rintro ⟨_, hc⟩; rw [List.length_drop, htlen] at hc; omega)]
  rw [auctionDecodeScalarWords_initialize_none_noncanon4 (bytes := I.calldata.toList.drop 4)
    htake4 htake36' htake68' htake100' htake132'
    (by rw [hword4]; exact hcanonNouns)
    (by
      rw [show ABI.bytesToWord (((I.calldata.toList.drop 4).drop 32).take 32) =
          auctionInitializeWethWord I from by
        simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hword36]
      exact hcanonWeth)
    (by
      rw [show ABI.bytesToWord (((I.calldata.toList.drop 4).drop 128).take 32) =
          auctionInitializeMinBidIncrementPercentageWord I from by
        simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hword132]
      exact hnc)]

theorem auctionReachInitializeBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = auctionBytecode)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (auctionSelBytes 11)) :
    ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨705⟩
      [auctionSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hsel' : ((⟨#[0x87, 0xf4, 0x9f, 0x54]⟩ : ByteArray) == I.calldata.extract 0 4) =
      true := by
    simpa [selIs, auctionSelBytes] using hsel
  have hword : auctionSelWord I = ⟨0x87f49f54⟩ :=
    auctionSelWord_eq_of_beq I hsz 0x87 0xf4 0x9f 0x54 ⟨0x87f49f54⟩
      (by native_decide) hsel'
  obtain ⟨_, _, hsplit⟩ := auctionReachRootSplit (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hsz hsize
  have hroot :
      UInt256.gt (armSelNat auctionBytecode auctionSplitPc) (auctionSelWord I) = ⟨0⟩ := by
    rw [hword]
    native_decide
  have h29 := auctionSelectorSplitNotTakenTo hsplit auctionSplitWellFormed hroot
      auctionRootSplitNextPc (by simp)
  have hupper :
      UInt256.gt (armSelNat auctionBytecode auctionUpperSplitPc) (auctionSelWord I) ≠
        ⟨0⟩ := by
    rw [hword]
    native_decide
  have h98 := auctionSelectorSplitTakenTo h29 auctionUpperSplitWellFormed hupper
      auctionUpperSplitTargetPc
    (by jump_dest) (by simp)
  have h99 := h98.jumpdest (by native_decide) (by simp)
  have heq0 : ∀ j, j < 1 →
      UInt256.eq (armSelNat auctionBytecode
        (nthArmPc auctionBytecode auctionUpperLowFirstArmPc j)) (auctionSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j <;> rw [hword] <;> native_decide
  have htake :
      UInt256.eq
        (armSelNat auctionBytecode (nthArmPc auctionBytecode auctionUpperLowFirstArmPc 1))
        (auctionSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  exact RD.dispatchTo (code := auctionBytecode) (ee := I) (g := g)
    (s0 := initState cA gh bl σ σ₀ g A I) (selWord := auctionSelWord I)
    (mem := solcFreePtrMem) (aw := UInt256.ofNat 3) (rdata := ByteArray.empty)
    (acc := (cA, σ)) ⟨705⟩ 1 h99
    (fun j hj => auctionUpperLowArmsWellFormed j (by omega)) heq0 htake
    (by jump_dest)
    (by native_decide)
    (by simp)

theorem auctionX_initialize_callvalue_ne {cA gh bl σ σ₀ A I} {g : Sat256}
    (hreach : ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨705⟩
      [auctionSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hwv : I.weiValue ≠ ⟨0⟩) :
    RDrev auctionBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd705⟩ := hreach
  exact evm_run rd705 with [
    jumpdest, callvalue, dup1, iszero, push2 ⟨716⟩,
    jumpiNT (isZero_eq_zero_of_ne hwv),
    push0, dup1, raw rev 0 (by native_decide) mem_cost (by evm_ov)]

theorem auctionInitializeX_toDecoder {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hreach : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨705⟩ [sel] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C)
    (hwv : I.weiValue = ⟨0⟩) :
    ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5400⟩
      [⟨4⟩, UInt256.ofNat I.calldata.size, ⟨731⟩, ⟨413⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd705⟩ := hreach
  exact ⟨_, _, evm_run rd705 with [
    jumpdest, callvalue, dup1, iszero, push2 ⟨716⟩,
    jumpiT (by rw [hwv]; decide) (by jump_dest),
    jumpdest, pop, push2 ⟨413⟩, push2 ⟨731⟩, calldatasize, push1 ⟨4⟩,
    push2 ⟨5400⟩, jump (by jump_dest)]⟩

set_option maxHeartbeats 1200000 in
theorem auctionDecodeInitializeOk5400 {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {ret : UInt256} {R : List UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD auctionBytecode ee g s0 ⟨5400⟩
        (⟨4⟩ :: UInt256.ofNat ee.calldata.size :: ret :: R) mem aw rdata acc k C)
    (hsltval : UInt256.slt (UInt256.sub (UInt256.ofNat ee.calldata.size) ⟨4⟩) ⟨192⟩ =
      ⟨0⟩)
    (hcanonNouns : (calldataWord ee.calldata 4).toNat < EVM.addressModulus)
    (hcanonWeth : (calldataWord ee.calldata 36).toNat < EVM.addressModulus)
    (hcanonMinBid : (calldataWord ee.calldata 132).toNat < EVM.twoPow 8)
    (hret : (D_J auctionBytecode 0).contains ret = true)
    (hov : R.length + 40 ≤ 1024) :
    ∃ k' C', RD auctionBytecode ee g s0 ret
      ([calldataWord ee.calldata 164, calldataWord ee.calldata 132,
        calldataWord ee.calldata 100, calldataWord ee.calldata 68,
        calldataWord ee.calldata 36, calldataWord ee.calldata 4] ++ R)
      mem aw rdata acc k' C' := by
  have rd5421 := evm_run h with [
    jumpdest, push0, dup1, push0, dup1, push0, dup1, push1 ⟨192⟩,
    dup8, dup10, sub, slt, iszero, push2 ⟨5421⟩,
    jumpiT (by rw [hsltval]; decide) (by jump_dest), jumpdest]
  have rd5380a := evm_run rd5421 with [
    dup7, calldataload, push2 ⟨5432⟩, dup2, push2 ⟨5380⟩, jump (by jump_dest)]
  have rd5392a₀ := evm_run rd5380a with [
    jumpdest, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup2, and, dup2, eq]
  have heqA : UInt256.eq
      (uInt256OfByteArray (ee.calldata.readBytes (⟨4⟩ : UInt256).toNat 32))
      (UInt256.land
        (uInt256OfByteArray (ee.calldata.readBytes (⟨4⟩ : UInt256).toNat 32))
        solcAddrMask) = ⟨1⟩ := by
    simpa [calldataWord] using solcAddrCanon_eq hcanonNouns
  have rd5392a := rd5392a₀
  rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask by decide] at rd5392a
  rw [heqA] at rd5392a
  have rd5432 := evm_run rd5392a with [
    push2 ⟨2850⟩, jumpiT (by decide) (by jump_dest), jumpdest, pop, jump (by jump_dest),
    jumpdest]
  have rd5380b := evm_run rd5432 with [
    swap6, pop, push1 ⟨32⟩, dup8, add, calldataload, push2 ⟨5448⟩, dup2,
    push2 ⟨5380⟩, jump (by jump_dest)]
  have rd5392b₀ := evm_run rd5380b with [
    jumpdest, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup2, and, dup2, eq]
  have heqB : UInt256.eq
      (uInt256OfByteArray (ee.calldata.readBytes ((⟨4⟩ : UInt256) + ⟨32⟩).toNat 32))
      (UInt256.land
        (uInt256OfByteArray (ee.calldata.readBytes ((⟨4⟩ : UInt256) + ⟨32⟩).toNat 32))
        solcAddrMask) = ⟨1⟩ := by
    simpa [calldataWord, show ((⟨4⟩ : UInt256) + ⟨32⟩).toNat = 36 from by decide] using
      solcAddrCanon_eq hcanonWeth
  have rd5392b := rd5392b₀
  rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask by decide] at rd5392b
  rw [heqB] at rd5392b
  have rd5448 := evm_run rd5392b with [
    push2 ⟨2850⟩, jumpiT (by decide) (by jump_dest), jumpdest, pop, jump (by jump_dest),
    jumpdest]
  have rd5476pre := evm_run rd5448 with [
    swap5, pop, push1 ⟨64⟩, dup8, add, calldataload, swap4, pop,
    push1 ⟨96⟩, dup8, add, calldataload, swap3, pop,
    push2 ⟨5476⟩, push1 ⟨128⟩, dup9, add, push2 ⟨5304⟩, jump (by jump_dest)]
  have hclean : UInt256.land (calldataWord ee.calldata 132) ⟨255⟩ =
      calldataWord ee.calldata 132 :=
    auctionLand255_eq_self_of_uint8 (calldataWord ee.calldata 132) hcanonMinBid
  have heqU : UInt256.eq (calldataWord ee.calldata 132)
      (UInt256.land (calldataWord ee.calldata 132) ⟨255⟩) = ⟨1⟩ := by
    rw [hclean, u256_eq_refl]
  have rd5320 := evm_run rd5476pre with [
    jumpdest, dup1, calldataload, push1 ⟨255⟩, dup2, and, dup2, eq, push2 ⟨5320⟩,
    jumpiT (by
      change UInt256.eq
        (uInt256OfByteArray (ee.calldata.readBytes ((⟨4⟩ : UInt256) + ⟨128⟩).toNat 32))
        (UInt256.land
          (uInt256OfByteArray (ee.calldata.readBytes
            ((⟨4⟩ : UInt256) + ⟨128⟩).toNat 32)) ⟨255⟩) ≠ ⟨0⟩
      simpa [calldataWord, show ((⟨4⟩ : UInt256) + ⟨128⟩).toNat = 132 from by decide] using
        (show UInt256.eq (calldataWord ee.calldata 132)
          (UInt256.land (calldataWord ee.calldata 132) ⟨255⟩) ≠ ⟨0⟩ from by
          rw [heqU]; decide)) (by jump_dest), jumpdest]
  have rd5476 := evm_run rd5320 with [swap2, swap1, pop, jump (by jump_dest), jumpdest]
  exact ⟨_, _, by
    simpa [calldataWord,
      show ((⟨4⟩ : UInt256) + ⟨64⟩).toNat = 68 from by decide,
      show ((⟨4⟩ : UInt256) + ⟨96⟩).toNat = 100 from by decide,
      show ((⟨4⟩ : UInt256) + ⟨128⟩).toNat = 132 from by decide,
      show ((⟨4⟩ : UInt256) + ⟨160⟩).toNat = 164 from by decide] using
      evm_run rd5476 with [
        swap2, pop, push1 ⟨160⟩, dup8, add, calldataload, swap1, pop,
        swap3, swap6, pop, swap3, swap6, pop, swap3, swap6, jump hret]⟩

theorem auctionDecodeInitializeLenRevert5400 {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {ret : UInt256} {R : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD auctionBytecode ee g s0 ⟨5400⟩
        (⟨4⟩ :: UInt256.ofNat ee.calldata.size :: ret :: R) mem aw rdata acc k C)
    (hsltval : UInt256.slt (UInt256.sub (UInt256.ofNat ee.calldata.size) ⟨4⟩) ⟨192⟩ =
      ⟨1⟩)
    (hov : R.length + 40 ≤ 1024) :
    RDrev auctionBytecode g s0 := by
  exact evm_run h with [
    jumpdest, push0, dup1, push0, dup1, push0, dup1, push1 ⟨192⟩,
    dup8, dup10, sub, slt, iszero, push2 ⟨5421⟩,
    jumpiNT (by rw [hsltval]; decide),
    push0, dup1, raw rev 0 (by native_decide) (fun s _ hstk => memExpRevert0 s hstk) (by
      have hR : R.length ≤ 1024 - 40 := Nat.le_sub_of_add_le hov
      simp only [List.length_cons]
      omega)]

set_option maxHeartbeats 800000 in
theorem auctionDecodeInitializeNoncanonNounsRevert5400 {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {ret : UInt256} {R : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD auctionBytecode ee g s0 ⟨5400⟩
        (⟨4⟩ :: UInt256.ofNat ee.calldata.size :: ret :: R) mem aw rdata acc k C)
    (hsltval : UInt256.slt (UInt256.sub (UInt256.ofNat ee.calldata.size) ⟨4⟩) ⟨192⟩ =
      ⟨0⟩)
    (hnc : ¬ (calldataWord ee.calldata 4).toNat < EVM.addressModulus)
    (hov : R.length + 40 ≤ 1024) :
    RDrev auctionBytecode g s0 := by
  have rd5421 := evm_run h with [
    jumpdest, push0, dup1, push0, dup1, push0, dup1, push1 ⟨192⟩,
    dup8, dup10, sub, slt, iszero, push2 ⟨5421⟩,
    jumpiT (by rw [hsltval]; decide) (by jump_dest), jumpdest]
  have rd5380a := evm_run rd5421 with [
    dup7, calldataload, push2 ⟨5432⟩, dup2, push2 ⟨5380⟩, jump (by jump_dest)]
  have rd5392a₀ := evm_run rd5380a with [
    jumpdest, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup2, and, dup2, eq]
  have heq0word : UInt256.eq (calldataWord ee.calldata 4)
      (UInt256.land (calldataWord ee.calldata 4) solcAddrMask) = ⟨0⟩ := by
    apply u256_eq_of_ne
    intro heqword
    apply hnc
    apply solcAddrCanonical_of_clean
    rw [← heqword, u256_eq_refl]
  have heq0 : UInt256.eq
      (uInt256OfByteArray (ee.calldata.readBytes (⟨4⟩ : UInt256).toNat 32))
      (UInt256.land
        (uInt256OfByteArray (ee.calldata.readBytes (⟨4⟩ : UInt256).toNat 32))
        solcAddrMask) = ⟨0⟩ := by
    simpa [calldataWord] using heq0word
  have rd5392a := rd5392a₀
  rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask by decide] at rd5392a
  rw [heq0] at rd5392a
  exact evm_run rd5392a with [
    push2 ⟨2850⟩, jumpiNT (by decide),
    push0, dup1, raw rev 0 (by native_decide) (fun s _ hstk => memExpRevert0 s hstk) (by
      have hR : R.length ≤ 1024 - 40 := Nat.le_sub_of_add_le hov
      simp only [List.length_cons]
      omega)]

set_option maxHeartbeats 1000000 in
theorem auctionDecodeInitializeNoncanonWethRevert5400 {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {ret : UInt256} {R : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD auctionBytecode ee g s0 ⟨5400⟩
        (⟨4⟩ :: UInt256.ofNat ee.calldata.size :: ret :: R) mem aw rdata acc k C)
    (hsltval : UInt256.slt (UInt256.sub (UInt256.ofNat ee.calldata.size) ⟨4⟩) ⟨192⟩ =
      ⟨0⟩)
    (hcanonNouns : (calldataWord ee.calldata 4).toNat < EVM.addressModulus)
    (hnc : ¬ (calldataWord ee.calldata 36).toNat < EVM.addressModulus)
    (hov : R.length + 40 ≤ 1024) :
    RDrev auctionBytecode g s0 := by
  have rd5421 := evm_run h with [
    jumpdest, push0, dup1, push0, dup1, push0, dup1, push1 ⟨192⟩,
    dup8, dup10, sub, slt, iszero, push2 ⟨5421⟩,
    jumpiT (by rw [hsltval]; decide) (by jump_dest), jumpdest]
  have rd5380a := evm_run rd5421 with [
    dup7, calldataload, push2 ⟨5432⟩, dup2, push2 ⟨5380⟩, jump (by jump_dest)]
  have rd5392a₀ := evm_run rd5380a with [
    jumpdest, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup2, and, dup2, eq]
  have heqA : UInt256.eq
      (uInt256OfByteArray (ee.calldata.readBytes (⟨4⟩ : UInt256).toNat 32))
      (UInt256.land
        (uInt256OfByteArray (ee.calldata.readBytes (⟨4⟩ : UInt256).toNat 32))
        solcAddrMask) = ⟨1⟩ := by
    simpa [calldataWord] using solcAddrCanon_eq hcanonNouns
  have rd5392a := rd5392a₀
  rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask by decide] at rd5392a
  rw [heqA] at rd5392a
  have rd5432 := evm_run rd5392a with [
    push2 ⟨2850⟩, jumpiT (by decide) (by jump_dest), jumpdest, pop, jump (by jump_dest),
    jumpdest]
  have rd5380b := evm_run rd5432 with [
    swap6, pop, push1 ⟨32⟩, dup8, add, calldataload, push2 ⟨5448⟩, dup2,
    push2 ⟨5380⟩, jump (by jump_dest)]
  have rd5392b₀ := evm_run rd5380b with [
    jumpdest, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup2, and, dup2, eq]
  have heq0word : UInt256.eq (calldataWord ee.calldata 36)
      (UInt256.land (calldataWord ee.calldata 36) solcAddrMask) = ⟨0⟩ := by
    apply u256_eq_of_ne
    intro heqword
    apply hnc
    apply solcAddrCanonical_of_clean
    rw [← heqword, u256_eq_refl]
  have heq0 : UInt256.eq
      (uInt256OfByteArray (ee.calldata.readBytes ((⟨4⟩ : UInt256) + ⟨32⟩).toNat 32))
      (UInt256.land
        (uInt256OfByteArray (ee.calldata.readBytes ((⟨4⟩ : UInt256) + ⟨32⟩).toNat 32))
        solcAddrMask) = ⟨0⟩ := by
    simpa [calldataWord, show ((⟨4⟩ : UInt256) + ⟨32⟩).toNat = 36 from by decide] using
      heq0word
  have rd5392b := rd5392b₀
  rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask by decide] at rd5392b
  rw [heq0] at rd5392b
  exact evm_run rd5392b with [
    push2 ⟨2850⟩, jumpiNT (by decide),
    push0, dup1, raw rev 0 (by native_decide) (fun s _ hstk => memExpRevert0 s hstk) (by
      have hR : R.length ≤ 1024 - 40 := Nat.le_sub_of_add_le hov
      simp only [List.length_cons]
      omega)]

set_option maxHeartbeats 1200000 in
theorem auctionDecodeInitializeNoncanonMinBidRevert5400 {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {ret : UInt256} {R : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD auctionBytecode ee g s0 ⟨5400⟩
        (⟨4⟩ :: UInt256.ofNat ee.calldata.size :: ret :: R) mem aw rdata acc k C)
    (hsltval : UInt256.slt (UInt256.sub (UInt256.ofNat ee.calldata.size) ⟨4⟩) ⟨192⟩ =
      ⟨0⟩)
    (hcanonNouns : (calldataWord ee.calldata 4).toNat < EVM.addressModulus)
    (hcanonWeth : (calldataWord ee.calldata 36).toNat < EVM.addressModulus)
    (hnc : ¬ (calldataWord ee.calldata 132).toNat < EVM.twoPow 8)
    (hov : R.length + 40 ≤ 1024) :
    RDrev auctionBytecode g s0 := by
  have rd5421 := evm_run h with [
    jumpdest, push0, dup1, push0, dup1, push0, dup1, push1 ⟨192⟩,
    dup8, dup10, sub, slt, iszero, push2 ⟨5421⟩,
    jumpiT (by rw [hsltval]; decide) (by jump_dest), jumpdest]
  have rd5380a := evm_run rd5421 with [
    dup7, calldataload, push2 ⟨5432⟩, dup2, push2 ⟨5380⟩, jump (by jump_dest)]
  have rd5392a₀ := evm_run rd5380a with [
    jumpdest, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup2, and, dup2, eq]
  have heqA : UInt256.eq
      (uInt256OfByteArray (ee.calldata.readBytes (⟨4⟩ : UInt256).toNat 32))
      (UInt256.land
        (uInt256OfByteArray (ee.calldata.readBytes (⟨4⟩ : UInt256).toNat 32))
        solcAddrMask) = ⟨1⟩ := by
    simpa [calldataWord] using solcAddrCanon_eq hcanonNouns
  have rd5392a := rd5392a₀
  rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask by decide] at rd5392a
  rw [heqA] at rd5392a
  have rd5432 := evm_run rd5392a with [
    push2 ⟨2850⟩, jumpiT (by decide) (by jump_dest), jumpdest, pop, jump (by jump_dest),
    jumpdest]
  have rd5380b := evm_run rd5432 with [
    swap6, pop, push1 ⟨32⟩, dup8, add, calldataload, push2 ⟨5448⟩, dup2,
    push2 ⟨5380⟩, jump (by jump_dest)]
  have rd5392b₀ := evm_run rd5380b with [
    jumpdest, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup2, and, dup2, eq]
  have heqB : UInt256.eq
      (uInt256OfByteArray (ee.calldata.readBytes ((⟨4⟩ : UInt256) + ⟨32⟩).toNat 32))
      (UInt256.land
        (uInt256OfByteArray (ee.calldata.readBytes ((⟨4⟩ : UInt256) + ⟨32⟩).toNat 32))
        solcAddrMask) = ⟨1⟩ := by
    simpa [calldataWord, show ((⟨4⟩ : UInt256) + ⟨32⟩).toNat = 36 from by decide] using
      solcAddrCanon_eq hcanonWeth
  have rd5392b := rd5392b₀
  rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask by decide] at rd5392b
  rw [heqB] at rd5392b
  have rd5448 := evm_run rd5392b with [
    push2 ⟨2850⟩, jumpiT (by decide) (by jump_dest), jumpdest, pop, jump (by jump_dest),
    jumpdest]
  have rd5476pre := evm_run rd5448 with [
    swap5, pop, push1 ⟨64⟩, dup8, add, calldataload, swap4, pop,
    push1 ⟨96⟩, dup8, add, calldataload, swap3, pop,
    push2 ⟨5476⟩, push1 ⟨128⟩, dup9, add, push2 ⟨5304⟩, jump (by jump_dest)]
  have hne : calldataWord ee.calldata 132 ≠
      UInt256.land (calldataWord ee.calldata 132) ⟨255⟩ :=
    (auctionLand255_ne_self_of_not_uint8 (calldataWord ee.calldata 132) hnc).symm
  have heq0 : UInt256.eq (calldataWord ee.calldata 132)
      (UInt256.land (calldataWord ee.calldata 132) ⟨255⟩) = ⟨0⟩ := by
    exact u256_eq_of_ne hne
  exact evm_run rd5476pre with [
    jumpdest, dup1, calldataload, push1 ⟨255⟩, dup2, and, dup2, eq, push2 ⟨5320⟩,
    jumpiNT (by
      change UInt256.eq
        (uInt256OfByteArray (ee.calldata.readBytes ((⟨4⟩ : UInt256) + ⟨128⟩).toNat 32))
        (UInt256.land
          (uInt256OfByteArray (ee.calldata.readBytes
            ((⟨4⟩ : UInt256) + ⟨128⟩).toNat 32)) ⟨255⟩) = ⟨0⟩
      simpa [calldataWord, show ((⟨4⟩ : UInt256) + ⟨128⟩).toNat = 132 from by decide] using
        heq0),
    push0, dup1, raw rev 0 (by native_decide) (fun s _ hstk => memExpRevert0 s hstk) (by
      have hR : R.length ≤ 1024 - 40 := Nat.le_sub_of_add_le hov
      simp only [List.length_cons]
      omega)]

theorem auctionInitializeX_decoded {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hsz196 : 196 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonNouns : (auctionInitializeNounsWord I).toNat < EVM.addressModulus)
    (hcanonWeth : (auctionInitializeWethWord I).toNat < EVM.addressModulus)
    (hcanonMinBid : (auctionInitializeMinBidIncrementPercentageWord I).toNat <
      EVM.twoPow 8)
    (hreach : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨705⟩ [sel] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD auctionBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2130⟩
      [auctionInitializeDurationWord I, auctionInitializeMinBidIncrementPercentageWord I,
        auctionInitializeReservePriceWord I, auctionInitializeTimeBufferWord I,
        auctionInitializeWethWord I, auctionInitializeNounsWord I, ⟨413⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨192⟩ =
      ⟨0⟩ :=
    solcDecodeLenCheckOk (sz := I.calldata.size) (head := (⟨4⟩ : UInt256))
      (need := (⟨192⟩ : UInt256)) (by simpa using hsz196) (by simpa using hszhi)
      hsize (by native_decide)
  obtain ⟨_, _, rd5400⟩ := auctionInitializeX_toDecoder (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) hreach hwv
  obtain ⟨_, _, rd731₀⟩ :=
    auctionDecodeInitializeOk5400 (R := [⟨413⟩, sel]) rd5400 hslt
      (by simpa [auctionInitializeNounsWord] using hcanonNouns)
      (by simpa [auctionInitializeWethWord] using hcanonWeth)
      (by simpa [auctionInitializeMinBidIncrementPercentageWord] using hcanonMinBid)
      (by jump_dest) (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨_, _, rd731⟩ : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨731⟩
      [calldataWord I.calldata 164, calldataWord I.calldata 132,
        calldataWord I.calldata 100, calldataWord I.calldata 68,
        calldataWord I.calldata 36, calldataWord I.calldata 4, ⟨413⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa using rd731₀⟩
  exact ⟨_, _, by
    simpa [auctionInitializeDurationWord, auctionInitializeMinBidIncrementPercentageWord,
      auctionInitializeReservePriceWord, auctionInitializeTimeBufferWord,
      auctionInitializeWethWord, auctionInitializeNounsWord] using
      evm_run rd731 with [jumpdest, push2 ⟨2130⟩, jump (by jump_dest)]⟩

theorem auctionInitializeX_decodeRevert_short {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 196)
    (hreach : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨705⟩ [sel] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C) :
    RDrev auctionBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨192⟩ =
      ⟨1⟩ :=
    solcDecodeLenCheckShort (sz := I.calldata.size) (head := (⟨4⟩ : UInt256))
      (need := (⟨192⟩ : UInt256)) (by simpa using hsz4) (by simpa using hshort)
      hsize (by native_decide)
  obtain ⟨_, _, rd5400⟩ := auctionInitializeX_toDecoder (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) hreach hwv
  exact auctionDecodeInitializeLenRevert5400 (R := [⟨413⟩, sel]) rd5400 hslt
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem auctionInitializeX_decodeRevert_huge {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hsize : I.calldata.size < UInt256.size) (hbig : 2 ^ 255 + 4 ≤ I.calldata.size)
    (hreach : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨705⟩ [sel] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C) :
    RDrev auctionBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨192⟩ =
      ⟨1⟩ :=
    solcDecodeLenCheckHuge (sz := I.calldata.size) (head := (⟨4⟩ : UInt256))
      (need := (⟨192⟩ : UInt256)) (by simpa using hbig) hsize (by native_decide)
  obtain ⟨_, _, rd5400⟩ := auctionInitializeX_toDecoder (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) hreach hwv
  exact auctionDecodeInitializeLenRevert5400 (R := [⟨413⟩, sel]) rd5400 hslt
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem auctionInitializeX_decodeRevert_noncanon_nouns {cA gh bl σ σ₀ A I}
    {g : Sat256} {sel : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hsz196 : 196 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hnc : ¬ (auctionInitializeNounsWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨705⟩ [sel] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C) :
    RDrev auctionBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨192⟩ =
      ⟨0⟩ :=
    solcDecodeLenCheckOk (sz := I.calldata.size) (head := (⟨4⟩ : UInt256))
      (need := (⟨192⟩ : UInt256)) (by simpa using hsz196) (by simpa using hszhi)
      hsize (by native_decide)
  obtain ⟨_, _, rd5400⟩ := auctionInitializeX_toDecoder (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) hreach hwv
  exact auctionDecodeInitializeNoncanonNounsRevert5400 (R := [⟨413⟩, sel]) rd5400 hslt
    (by simpa [auctionInitializeNounsWord] using hnc)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem auctionInitializeX_decodeRevert_noncanon_weth {cA gh bl σ σ₀ A I}
    {g : Sat256} {sel : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hsz196 : 196 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonNouns : (auctionInitializeNounsWord I).toNat < EVM.addressModulus)
    (hnc : ¬ (auctionInitializeWethWord I).toNat < EVM.addressModulus)
    (hreach : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨705⟩ [sel] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C) :
    RDrev auctionBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨192⟩ =
      ⟨0⟩ :=
    solcDecodeLenCheckOk (sz := I.calldata.size) (head := (⟨4⟩ : UInt256))
      (need := (⟨192⟩ : UInt256)) (by simpa using hsz196) (by simpa using hszhi)
      hsize (by native_decide)
  obtain ⟨_, _, rd5400⟩ := auctionInitializeX_toDecoder (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) hreach hwv
  exact auctionDecodeInitializeNoncanonWethRevert5400 (R := [⟨413⟩, sel]) rd5400 hslt
    (by simpa [auctionInitializeNounsWord] using hcanonNouns)
    (by simpa [auctionInitializeWethWord] using hnc)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem auctionInitializeX_decodeRevert_noncanon_minBid {cA gh bl σ σ₀ A I}
    {g : Sat256} {sel : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hsz196 : 196 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hszhi : I.calldata.size < 2 ^ 255 + 4)
    (hcanonNouns : (auctionInitializeNounsWord I).toNat < EVM.addressModulus)
    (hcanonWeth : (auctionInitializeWethWord I).toNat < EVM.addressModulus)
    (hnc : ¬ (auctionInitializeMinBidIncrementPercentageWord I).toNat < EVM.twoPow 8)
    (hreach : ∃ k C, RD auctionBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨705⟩ [sel] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C) :
    RDrev auctionBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hslt : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨192⟩ =
      ⟨0⟩ :=
    solcDecodeLenCheckOk (sz := I.calldata.size) (head := (⟨4⟩ : UInt256))
      (need := (⟨192⟩ : UInt256)) (by simpa using hsz196) (by simpa using hszhi)
      hsize (by native_decide)
  obtain ⟨_, _, rd5400⟩ := auctionInitializeX_toDecoder (cA := cA) (gh := gh)
    (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) (sel := sel) hreach hwv
  exact auctionDecodeInitializeNoncanonMinBidRevert5400 (R := [⟨413⟩, sel]) rd5400 hslt
    (by simpa [auctionInitializeNounsWord] using hcanonNouns)
    (by simpa [auctionInitializeWethWord] using hcanonWeth)
    (by simpa [auctionInitializeMinBidIncrementPercentageWord] using hnc)
    (by simp only [List.length_cons, List.length_nil]; omega)

end Auction
