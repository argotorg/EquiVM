import Benchmarks.Dss.Clipper.Fallback

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Dss.Clipper.Immutables

namespace Benchmarks.Dss.Clipper

set_option linter.unusedTactic false

/-! ## Shared one-`uint256` external ABI entry helpers -/

-- LIBRARY CANDIDATE: legacy solc-0.5/0.6 one-word uint256 ABI decoding.
theorem decodeCalldataWithMode_legacyUint256_ok {cd : ByteArray} {x : Solm.Ident}
    (hsz36 : 36 ≤ cd.size) :
    decodeCalldataWithMode DecodeMode.legacySolc05 [x] [uint256] cd =
      some ((∅ : Solm.Store).insert x (.int (Int.ofNat (calldataWord cd 4).toNat))) := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have htake4 : ((cd.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have hword4 : ABI.bytesToWord ((cd.toList.drop 4).take 32) = calldataWord cd 4 := by
    exact decode_word_at_eq cd 4 (by omega) (by norm_num)
  rw [decodeCalldataWithMode_legacyScalarWords_eq (names := [x]) (types := [uint256])
    (cd := cd) (by decide +native)]
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  simp only [decodeScalarWordsWithMode?]
  change (match do
      let decoded ← decodeScalarWordWithMode? DecodeMode.legacySolc05 abiUInt256
        (List.drop 4 cd.toList) 0
      let values ← some []
      some (decoded.1 :: values) with
    | some values => decodeCalldata.insertValues [x] values ∅
    | none => none) = _
  rw [decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05)
    (bytes := cd.toList.drop 4) (start := 0) (by simpa using htake4)]
  change decodeCalldata.insertValues [x]
      [.int (Int.ofNat (ABI.bytesToWord ((cd.toList.drop 4).take 32)).toNat)] ∅ =
    some ((∅ : Solm.Store).insert x (.int (Int.ofNat (calldataWord cd 4).toNat)))
  simp [decodeCalldata.insertValues]
  rw [hword4]

-- LIBRARY CANDIDATE: legacy solc-0.5/0.6 one-word uint256 short-calldata rejection.
theorem decodeCalldataWithMode_legacyUint256_none_short {cd : ByteArray} {x : Solm.Ident}
    (hsz4 : 4 ≤ cd.size) (hshort : cd.size < 36) :
    decodeCalldataWithMode DecodeMode.legacySolc05 [x] [uint256] cd = none := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  rw [decodeCalldataWithMode_legacyScalarWords_eq (names := [x]) (types := [uint256])
    (cd := cd) (by decide +native)]
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  simp only [decodeScalarWordsWithMode?]
  have htake0n : ¬ ((cd.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  change (match do
      let decoded ← decodeScalarWordWithMode? DecodeMode.legacySolc05 abiUInt256
        (List.drop 4 cd.toList) 0
      let values ← some []
      some (decoded.1 :: values) with
    | some values => decodeCalldata.insertValues [x] values ∅
    | none => none) = none
  rw [decodeScalarWordWithMode_uint256_none_short (mode := DecodeMode.legacySolc05)
    (start := 0) (by simpa using htake0n)]
  simp only [Option.bind, bind]

-- GENERALIZES Reasoning.Solc.RD.solcOneAddressExternalLenOk: one-word external
-- entries whose decoded block loads a uint256 argument and jumps without address masking.
@[reducible] def solcOneUintExternalDecodedPc (pc : UInt256) : UInt256 :=
  solcOneAddressExternalDecodedPc pc

@[reducible] def solcOneUintExternalEntryWf
    (code : ByteArray) (pc ret routine : UInt256) : Prop :=
  let p1 := pc + ⟨1⟩
  let p4 := p1 + UInt256.ofNat 3
  let p6 := p4 + UInt256.ofNat 2
  let p7 := p6 + ⟨1⟩
  let p8 := p7 + ⟨1⟩
  let p9 := p8 + ⟨1⟩
  let p11 := p9 + UInt256.ofNat 2
  let p12 := p11 + ⟨1⟩
  let p13 := p12 + ⟨1⟩
  let p14 := p13 + ⟨1⟩
  let p17 := p14 + UInt256.ofNat 3
  let p18 := p17 + ⟨1⟩
  let p20 := p18 + UInt256.ofNat 2
  let p21 := p20 + ⟨1⟩
  let p22 := solcOneUintExternalDecodedPc pc
  let p23 := p22 + ⟨1⟩
  let p24 := p23 + ⟨1⟩
  let p25 := p24 + ⟨1⟩
  let p28 := p25 + UInt256.ofNat 3
  decode code pc = some (.JUMPDEST, .none)
  ∧ decode code p1 = some (.Push .PUSH2, some (ret, 2))
  ∧ decode code p4 = some (.Push .PUSH1, some (⟨4⟩, 1))
  ∧ decode code p6 = some (.DUP1, .none)
  ∧ decode code p7 = some (.CALLDATASIZE, .none)
  ∧ decode code p8 = some (.SUB, .none)
  ∧ decode code p9 = some (.Push .PUSH1, some (⟨32⟩, 1))
  ∧ decode code p11 = some (.DUP2, .none)
  ∧ decode code p12 = some (.LT, .none)
  ∧ decode code p13 = some (.ISZERO, .none)
  ∧ decode code p14 = some (.Push .PUSH2, some (p22, 2))
  ∧ decode code p17 = some (.JUMPI, .none)
  ∧ decode code p18 = some (.Push .PUSH1, some (⟨0⟩, 1))
  ∧ decode code p20 = some (.DUP1, .none)
  ∧ decode code p21 = some (.REVERT, .none)
  ∧ decode code p22 = some (.JUMPDEST, .none)
  ∧ decode code p23 = some (.POP, .none)
  ∧ decode code p24 = some (.CALLDATALOAD, .none)
  ∧ decode code p25 = some (.Push .PUSH2, some (routine, 2))
  ∧ decode code p28 = some (.JUMP, .none)

set_option maxHeartbeats 1000000 in
theorem solcOneUintExternalLenOk {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    {code : ByteArray} {entry ret routine : UInt256}
    (hreach : ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I) entry [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hwf : solcOneUintExternalEntryWf code entry ret routine)
    (hdecoded : (D_J code 0).contains (solcOneUintExternalDecodedPc entry) = true)
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size) :
    ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I)
      (solcOneUintExternalDecodedPc entry)
      (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩ :: ⟨4⟩ :: ret :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  rcases hwf with
    ⟨hd0, hd1, hd4, hd6, hd7, hd8, hd9, hd11, hd12, hd13, hd14, hd17, _hd18,
      _hd20, _hd21, _hd22, _hd23, _hd24, _hd25, _hd28⟩
  exact RD.solcOneAddressExternalLenOk hreach hd0 hd1 hd4 hd6 hd7 hd8 hd9 hd11
    hd12 hd13 hd14 hd17 hdecoded hsz36 hsize

set_option maxHeartbeats 1000000 in
theorem solcOneUintExternalLoadAndJump {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {entry ret routine de : UInt256}
    {R : List UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD code ee g s0 (solcOneUintExternalDecodedPc entry)
      (de :: ⟨4⟩ :: ret :: R) solcFreePtrMem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hwf : solcOneUintExternalEntryWf code entry ret routine)
    (hroutine : (D_J code 0).contains routine = true)
    (hov : R.length + 4 ≤ 1024) :
    ∃ k' C', RD code ee g s0 routine
      (calldataWord ee.calldata 4 :: ret :: R)
      solcFreePtrMem (UInt256.ofNat 3) rdata (cA, σ) k' C' := by
  rcases hwf with
    ⟨_hd0, _hd1, _hd4, _hd6, _hd7, _hd8, _hd9, _hd11, _hd12, _hd13, _hd14,
      _hd17, _hd18, _hd20, _hd21, hd22, hd23, hd24, hd25, hd28⟩
  have rd23 := h.jumpdest hd22 (by evm_ov)
  have rd24 := rd23.pop hd23 (by evm_ov)
  have rd25 := rd24.calldataload hd24 (by evm_ov)
  have rd28 := rd25.push2 routine hd25 (by evm_ov)
  exact ⟨_, _, by
    simpa [calldataWord, show (⟨4⟩ : UInt256).toNat = 4 from by decide] using
      rd28.jump hd28 hroutine (by evm_ov)⟩

set_option maxHeartbeats 1000000 in
theorem solcOneUintExternalShort {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel entry ret routine : UInt256} {code : ByteArray}
    (hreach : ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I) entry [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hwf : solcOneUintExternalEntryWf code entry ret routine)
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 36) :
    RDrev code g (initState cA gh bl σ σ₀ g A I) := by
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨1⟩ := by
    apply ult_one
    rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide,
      usub_ofNat_word_toNat (c := (⟨4⟩ : UInt256)) (by simpa using hsz4) hsize,
      show (⟨4⟩ : UInt256).toNat = 4 from by decide]
    omega
  rcases hwf with
    ⟨hd0, hd1, hd4, hd6, hd7, hd8, hd9, hd11, hd12, hd13, hd14, hd17, hd18,
      hd20, hd21, _hd22, _hd23, _hd24, _hd25, _hd28⟩
  exact RD.solcExternalStaticArgsShortReverts hreach hd0 hd1 hd4 hd6 hd7 hd8 hd9
    hd11 hd12 hd13 hd14 hd17 hd18 hd20 hd21 hlt

end Benchmarks.Dss.Clipper
