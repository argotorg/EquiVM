import Examples.UniswapV2Pair.Spec
import Reasoning.ABI

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

set_option maxRecDepth 2000000

namespace UniswapV2Pair

/-!
# Legacy address ABI helpers

Uniswap V2 Pair was compiled by solc 0.5.16 with optimizer enabled. Its static external wrappers
mask address calldata words instead of rejecting non-canonical high bits. The `legacyAddr` ABI type
keeps the external selector string `address` while decoding the low 160 bits.
-/

-- LIBRARY CANDIDATE: Reasoning.ABI - legacy/optimizer solc masked-address scalar decode.
theorem decodeScalarWord_legacyAddress_ok {bytes : List UInt8} {start : Nat}
    (hlen : ((bytes.drop start).take 32).length = 32) :
    decodeScalarWord? legacyAddr bytes start =
      some (.address (AccountAddress.ofNat
          (ABI.bytesToWord ((bytes.drop start).take 32)).toNat), start + 32) := by
  rw [← decodeABIValue_scalarWord_eq (ty := legacyAddr) (bytes := bytes)
    (start := start) (by decide)]
  simp only [legacyAddr, decodeABIValue?, readWord?, readBytes?, decodeABIWord?, bind,
    Option.bind]
  rw [if_pos hlen]
  rfl

-- LIBRARY CANDIDATE: Reasoning.ABI - legacy/optimizer solc masked-address short decode.
theorem decodeScalarWord_legacyAddress_none_short {bytes : List UInt8} {start : Nat}
    (hshort : ¬ ((bytes.drop start).take 32).length = 32) :
    decodeScalarWord? legacyAddr bytes start = none := by
  rw [← decodeABIValue_scalarWord_eq (ty := legacyAddr) (bytes := bytes)
    (start := start) (by decide)]
  simp only [legacyAddr, decodeABIValue?, readWord?, readBytes?, decodeABIWord?, bind,
    Option.bind]
  rw [if_neg hshort]

-- LIBRARY CANDIDATE: Reasoning.ABI - static calldata tuples containing a legacy/optimizer
-- address argument skip the signed huge-calldata guard.
theorem legacyAddress_staticSignedGuard_false {cd : ByteArray} (tys : List ABIType) :
    ¬ ((legacyAddr :: tys).isEmpty = false ∧
        usesLegacyAddressTypes (legacyAddr :: tys) = false ∧
        2 ^ 255 ≤ (cd.toList.drop 4).length) := by
  rintro ⟨_, hlegacy, _⟩
  have huses : usesLegacyAddressTypes (legacyAddr :: tys) = true := by
    simp [legacyAddr, usesLegacyAddressTypes, usesLegacyAddressType]
  rw [huses] at hlegacy
  contradiction

-- LIBRARY CANDIDATE: Reasoning.ABI - one legacy address calldata tuple.
theorem decodeCalldata_legacyAddress_ok {cd : ByteArray} {x : Solm.Ident}
    (hsz36 : 36 ≤ cd.size) :
    decodeCalldata [x] [legacyAddr] cd =
      some ((∅ : Solm.Store).insert x
        (.address (AccountAddress.ofNat (calldataWord cd 4).toNat))) := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  have htake4 : ((cd.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]; omega
  have hword4 : ABI.bytesToWord ((cd.toList.drop 4).take 32) = calldataWord cd 4 :=
    decode_word_at_eq cd 4 (by omega) (by norm_num)
  rw [decodeCalldata_scalarWords_eq (names := [x]) (types := [legacyAddr]) (cd := cd)
    (by decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_neg (legacyAddress_staticSignedGuard_false (cd := cd) [])]
  simp only [decodeScalarWords?]
  rw [decodeScalarWord_legacyAddress_ok (bytes := cd.toList.drop 4) htake4]
  change decodeCalldata.insertValues [x]
      [.address (AccountAddress.ofNat
        (ABI.bytesToWord ((cd.toList.drop 4).take 32)).toNat)] ∅ =
    some ((∅ : Solm.Store).insert x (.address (AccountAddress.ofNat (calldataWord cd 4).toNat)))
  rw [hword4]
  simp [decodeCalldata.insertValues]

-- LIBRARY CANDIDATE: Reasoning.ABI - one legacy address short calldata tuple.
theorem decodeCalldata_legacyAddress_none_short {cd : ByteArray} {x : Solm.Ident}
    (hsz4 : 4 ≤ cd.size) (hshort : cd.size < 36) :
    decodeCalldata [x] [legacyAddr] cd = none := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  rw [decodeCalldata_scalarWords_eq (names := [x]) (types := [legacyAddr]) (cd := cd)
    (by decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_neg (legacyAddress_staticSignedGuard_false (cd := cd) [])]
  simp only [decodeScalarWords?]
  have htake0n : ¬ ((cd.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  rw [decodeScalarWord_legacyAddress_none_short (start := 0) (by simpa using htake0n)]
  simp only [Option.bind, bind]

-- LIBRARY CANDIDATE: Reasoning.ABI - legacy address plus uint256 calldata tuple.
theorem decodeCalldata_legacyAddress_uint256_ok {cd : ByteArray} {x y : Solm.Ident}
    (hsz68 : 68 ≤ cd.size) :
    decodeCalldata [x, y] [legacyAddr, abiUInt256] cd =
      some (((∅ : Solm.Store).insert x
        (.address (AccountAddress.ofNat (calldataWord cd 4).toNat))).insert y
        (.int (Int.ofNat (calldataWord cd 36).toNat))) := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  have htake4 : ((cd.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]; omega
  have htake36 : ((cd.toList.drop 4).drop 32 |>.take 32).length = 32 := by
    rw [List.length_take, List.length_drop, List.length_drop, htlen]; omega
  have hword4 : ABI.bytesToWord ((cd.toList.drop 4).take 32) = calldataWord cd 4 :=
    decode_word_at_eq cd 4 (by omega) (by norm_num)
  have hword36 : ABI.bytesToWord (((cd.toList.drop 4).drop 32).take 32) =
      calldataWord cd 36 := by
    simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      using decode_word_at_eq cd 36 (by omega) (by norm_num)
  rw [decodeCalldata_scalarWords_eq (names := [x, y]) (types := [legacyAddr, abiUInt256])
    (cd := cd) (by decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_neg (legacyAddress_staticSignedGuard_false (cd := cd) [abiUInt256])]
  simp only [decodeScalarWords?]
  rw [decodeScalarWord_legacyAddress_ok (bytes := cd.toList.drop 4) htake4]
  rw [decodeScalarWord_uint256_ok (bytes := cd.toList.drop 4) (start := 32) htake36]
  change decodeCalldata.insertValues [x, y]
      [.address (AccountAddress.ofNat (ABI.bytesToWord ((cd.toList.drop 4).take 32)).toNat),
        .int (Int.ofNat (ABI.bytesToWord (((cd.toList.drop 4).drop 32).take 32)).toNat)] ∅ =
    some (((∅ : Solm.Store).insert x
      (.address (AccountAddress.ofNat (calldataWord cd 4).toNat))).insert y
      (.int (Int.ofNat (calldataWord cd 36).toNat)))
  rw [hword4, hword36]
  simp [decodeCalldata.insertValues]

-- LIBRARY CANDIDATE: Reasoning.ABI - legacy address plus uint256 short calldata tuple.
theorem decodeCalldata_legacyAddress_uint256_none_short {cd : ByteArray} {x y : Solm.Ident}
    (hsz4 : 4 ≤ cd.size) (hshort : cd.size < 68) :
    decodeCalldata [x, y] [legacyAddr, abiUInt256] cd = none := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  rw [decodeCalldata_scalarWords_eq (names := [x, y]) (types := [legacyAddr, abiUInt256])
    (cd := cd) (by decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_neg (legacyAddress_staticSignedGuard_false (cd := cd) [abiUInt256])]
  by_cases hlen0 : 32 ≤ (cd.toList.drop 4).length
  · have htake0 : ((cd.toList.drop 4).take 32).length = 32 := by
      rw [List.length_take]
      omega
    simp only [decodeScalarWords?]
    rw [decodeScalarWord_legacyAddress_ok (bytes := cd.toList.drop 4) htake0]
    have htake32n : ¬ (((cd.toList.drop 4).drop 32).take 32).length = 32 := by
      rw [List.length_take, List.length_drop, List.length_drop, htlen]
      omega
    rw [decodeScalarWord_uint256_none_short (start := 32) (by simpa using htake32n)]
    simp only [Option.bind, bind]
  · have htake0n : ¬ ((cd.toList.drop 4).take 32).length = 32 := by
      rw [List.length_take]
      omega
    simp only [decodeScalarWords?]
    rw [decodeScalarWord_legacyAddress_none_short (start := 0) (by simpa using htake0n)]
    simp only [Option.bind, bind]

-- LIBRARY CANDIDATE: Reasoning.ABI - two legacy-address calldata tuple.
theorem decodeCalldata_legacyAddress_legacyAddress_ok {cd : ByteArray} {x y : Solm.Ident}
    (hsz68 : 68 ≤ cd.size) :
    decodeCalldata [x, y] [legacyAddr, legacyAddr] cd =
      some (((∅ : Solm.Store).insert x
        (.address (AccountAddress.ofNat (calldataWord cd 4).toNat))).insert y
        (.address (AccountAddress.ofNat (calldataWord cd 36).toNat))) := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  have htake4 : ((cd.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]; omega
  have htake36 : ((cd.toList.drop 4).drop 32 |>.take 32).length = 32 := by
    rw [List.length_take, List.length_drop, List.length_drop, htlen]; omega
  have hword4 : ABI.bytesToWord ((cd.toList.drop 4).take 32) = calldataWord cd 4 :=
    decode_word_at_eq cd 4 (by omega) (by norm_num)
  have hword36 : ABI.bytesToWord (((cd.toList.drop 4).drop 32).take 32) =
      calldataWord cd 36 := by
    simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      using decode_word_at_eq cd 36 (by omega) (by norm_num)
  rw [decodeCalldata_scalarWords_eq (names := [x, y]) (types := [legacyAddr, legacyAddr])
    (cd := cd) (by decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_neg (legacyAddress_staticSignedGuard_false (cd := cd) [legacyAddr])]
  simp only [decodeScalarWords?]
  rw [decodeScalarWord_legacyAddress_ok (bytes := cd.toList.drop 4) htake4]
  rw [decodeScalarWord_legacyAddress_ok (bytes := cd.toList.drop 4) (start := 32) htake36]
  change decodeCalldata.insertValues [x, y]
      [.address (AccountAddress.ofNat (ABI.bytesToWord ((cd.toList.drop 4).take 32)).toNat),
        .address (AccountAddress.ofNat
          (ABI.bytesToWord (((cd.toList.drop 4).drop 32).take 32)).toNat)] ∅ =
    some (((∅ : Solm.Store).insert x
      (.address (AccountAddress.ofNat (calldataWord cd 4).toNat))).insert y
      (.address (AccountAddress.ofNat (calldataWord cd 36).toNat)))
  rw [hword4, hword36]
  simp [decodeCalldata.insertValues]

-- LIBRARY CANDIDATE: Reasoning.ABI - two legacy-address short calldata tuple.
theorem decodeCalldata_legacyAddress_legacyAddress_none_short {cd : ByteArray}
    {x y : Solm.Ident} (hsz4 : 4 ≤ cd.size) (hshort : cd.size < 68) :
    decodeCalldata [x, y] [legacyAddr, legacyAddr] cd = none := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  rw [decodeCalldata_scalarWords_eq (names := [x, y]) (types := [legacyAddr, legacyAddr])
    (cd := cd) (by decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_neg (legacyAddress_staticSignedGuard_false (cd := cd) [legacyAddr])]
  by_cases hlen0 : 32 ≤ (cd.toList.drop 4).length
  · have htake0 : ((cd.toList.drop 4).take 32).length = 32 := by
      rw [List.length_take]
      omega
    simp only [decodeScalarWords?]
    rw [decodeScalarWord_legacyAddress_ok (bytes := cd.toList.drop 4) htake0]
    have htake32n : ¬ (((cd.toList.drop 4).drop 32).take 32).length = 32 := by
      rw [List.length_take, List.length_drop, List.length_drop, htlen]
      omega
    rw [decodeScalarWord_legacyAddress_none_short (start := 32) (by simpa using htake32n)]
    simp only [Option.bind, bind]
  · have htake0n : ¬ ((cd.toList.drop 4).take 32).length = 32 := by
      rw [List.length_take]
      omega
    simp only [decodeScalarWords?]
    rw [decodeScalarWord_legacyAddress_none_short (start := 0) (by simpa using htake0n)]
    simp only [Option.bind, bind]

-- LIBRARY CANDIDATE: Reasoning.ABI - two legacy addresses plus uint256 calldata tuple.
theorem decodeCalldata_legacyAddress_legacyAddress_uint256_ok {cd : ByteArray}
    {x y z : Solm.Ident}
    (hsz100 : 100 ≤ cd.size) :
    decodeCalldata [x, y, z] [legacyAddr, legacyAddr, abiUInt256] cd =
      some ((((∅ : Solm.Store).insert x
        (.address (AccountAddress.ofNat (calldataWord cd 4).toNat))).insert y
        (.address (AccountAddress.ofNat (calldataWord cd 36).toNat))).insert z
        (.int (Int.ofNat (calldataWord cd 68).toNat))) := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  have htake4 : ((cd.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]; omega
  have htake36 : ((cd.toList.drop 4).drop 32 |>.take 32).length = 32 := by
    rw [List.length_take, List.length_drop, List.length_drop, htlen]; omega
  have htake68 : ((cd.toList.drop 4).drop 64 |>.take 32).length = 32 := by
    rw [List.length_take, List.length_drop, List.length_drop, htlen]; omega
  have hword4 : ABI.bytesToWord ((cd.toList.drop 4).take 32) = calldataWord cd 4 :=
    decode_word_at_eq cd 4 (by omega) (by norm_num)
  have hword36 : ABI.bytesToWord (((cd.toList.drop 4).drop 32).take 32) =
      calldataWord cd 36 := by
    simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      using decode_word_at_eq cd 36 (by omega) (by norm_num)
  have hword68 : ABI.bytesToWord (((cd.toList.drop 4).drop 64).take 32) =
      calldataWord cd 68 := by
    simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      using decode_word_at_eq cd 68 (by omega) (by norm_num)
  rw [decodeCalldata_scalarWords_eq (names := [x, y, z])
    (types := [legacyAddr, legacyAddr, abiUInt256]) (cd := cd) (by decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_neg (legacyAddress_staticSignedGuard_false (cd := cd) [legacyAddr, abiUInt256])]
  simp only [decodeScalarWords?]
  rw [decodeScalarWord_legacyAddress_ok (bytes := cd.toList.drop 4) htake4]
  rw [decodeScalarWord_legacyAddress_ok (bytes := cd.toList.drop 4) (start := 32) htake36]
  rw [decodeScalarWord_uint256_ok (bytes := cd.toList.drop 4) (start := 64)
    htake68]
  simp only [Option.bind, bind]
  change decodeCalldata.insertValues [x, y, z]
      [.address (AccountAddress.ofNat (ABI.bytesToWord ((cd.toList.drop 4).take 32)).toNat),
        .address (AccountAddress.ofNat
          (ABI.bytesToWord (((cd.toList.drop 4).drop 32).take 32)).toNat),
        .int (Int.ofNat
          (ABI.bytesToWord (((cd.toList.drop 4).drop 64).take 32)).toNat)] ∅ =
    some ((((∅ : Solm.Store).insert x
      (.address (AccountAddress.ofNat (calldataWord cd 4).toNat))).insert y
      (.address (AccountAddress.ofNat (calldataWord cd 36).toNat))).insert z
      (.int (Int.ofNat (calldataWord cd 68).toNat)))
  rw [hword4, hword36, hword68]
  simp [decodeCalldata.insertValues]

-- LIBRARY CANDIDATE: Reasoning.ABI - two legacy addresses plus uint256 short calldata tuple.
theorem decodeCalldata_legacyAddress_legacyAddress_uint256_none_short {cd : ByteArray}
    {x y z : Solm.Ident} (hsz4 : 4 ≤ cd.size) (hshort : cd.size < 100) :
    decodeCalldata [x, y, z] [legacyAddr, legacyAddr, abiUInt256] cd = none := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  rw [decodeCalldata_scalarWords_eq (names := [x, y, z])
    (types := [legacyAddr, legacyAddr, abiUInt256]) (cd := cd) (by decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_neg (legacyAddress_staticSignedGuard_false (cd := cd) [legacyAddr, abiUInt256])]
  by_cases hlen0 : 32 ≤ (cd.toList.drop 4).length
  · have htake0 : ((cd.toList.drop 4).take 32).length = 32 := by
      rw [List.length_take]
      omega
    simp only [decodeScalarWords?]
    rw [decodeScalarWord_legacyAddress_ok (bytes := cd.toList.drop 4) htake0]
    by_cases hlen32 : 64 ≤ (cd.toList.drop 4).length
    · have htake32 : (((cd.toList.drop 4).drop 32).take 32).length = 32 := by
        rw [List.length_take, List.length_drop]
        omega
      rw [decodeScalarWord_legacyAddress_ok (bytes := cd.toList.drop 4) (start := 32)
        htake32]
      have htake64n : ¬ (((cd.toList.drop 4).drop 64).take 32).length = 32 := by
        rw [List.length_take, List.length_drop, List.length_drop, htlen]
        omega
      rw [decodeScalarWord_uint256_none_short (start := 64) (by simpa using htake64n)]
      simp only [Option.bind, bind]
    · have htake32n : ¬ (((cd.toList.drop 4).drop 32).take 32).length = 32 := by
        rw [List.length_take, List.length_drop]
        omega
      rw [decodeScalarWord_legacyAddress_none_short (start := 32) (by simpa using htake32n)]
      simp only [Option.bind, bind]
  · have htake0n : ¬ ((cd.toList.drop 4).take 32).length = 32 := by
      rw [List.length_take]
      omega
    simp only [decodeScalarWords?]
    rw [decodeScalarWord_legacyAddress_none_short (start := 0) (by simpa using htake0n)]
    simp only [Option.bind, bind]

end UniswapV2Pair
