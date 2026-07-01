import Examples.UniswapV2Pair.Storage

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace UniswapV2Pair

/-! # Shared Uniswap V2 Pair routine-shape helpers -/

/-! ## Shared two-address external entry -/

/-- PC of the post-length-check decode block in Uniswap's optimized two-address wrappers. -/
@[reducible] def uniswapTwoAddressExternalDecodedPc (pc : UInt256) : UInt256 :=
  uniswapTwoAddressGetterDecodedPc pc

/-- Bytecode shape for Uniswap's optimized external two-address wrappers.

The wrapper checks that two static ABI words are present, masks both address words, and jumps to a
routine while preserving the caller-supplied return/continuation pc.
-/
@[reducible] def uniswapTwoAddressExternalEntryWf
    (pc ret routine : UInt256) : Prop :=
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
  let p22 := uniswapTwoAddressExternalDecodedPc pc
  let p23 := p22 + ⟨1⟩
  let p24 := p23 + ⟨1⟩
  let p26 := p24 + UInt256.ofNat 2
  let p28 := p26 + UInt256.ofNat 2
  let p30 := p28 + UInt256.ofNat 2
  let p31 := p30 + ⟨1⟩
  let p32 := p31 + ⟨1⟩
  let p33 := p32 + ⟨1⟩
  let p34 := p33 + ⟨1⟩
  let p35 := p34 + ⟨1⟩
  let p36 := p35 + ⟨1⟩
  let p37 := p36 + ⟨1⟩
  let p39 := p37 + UInt256.ofNat 2
  let p40 := p39 + ⟨1⟩
  let p41 := p40 + ⟨1⟩
  let p42 := p41 + ⟨1⟩
  let p45 := p42 + UInt256.ofNat 3
  decode UniswapV2Pair.uniswapV2PairBytecode pc = some (.JUMPDEST, .none)
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode p1 =
      some (.Push .PUSH2, some (ret, 2))
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode p4 =
      some (.Push .PUSH1, some (⟨4⟩, 1))
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode p6 = some (.DUP1, .none)
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode p7 = some (.CALLDATASIZE, .none)
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode p8 = some (.SUB, .none)
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode p9 =
      some (.Push .PUSH1, some (⟨64⟩, 1))
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode p11 = some (.DUP2, .none)
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode p12 = some (.LT, .none)
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode p13 = some (.ISZERO, .none)
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode p14 =
      some (.Push .PUSH2, some (p22, 2))
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode p17 = some (.JUMPI, .none)
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode p18 =
      some (.Push .PUSH1, some (⟨0⟩, 1))
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode p20 = some (.DUP1, .none)
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode p21 = some (.REVERT, .none)
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode p22 = some (.JUMPDEST, .none)
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode p23 = some (.POP, .none)
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode p24 =
      some (.Push .PUSH1, some (⟨1⟩, 1))
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode p26 =
      some (.Push .PUSH1, some (⟨1⟩, 1))
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode p28 =
      some (.Push .PUSH1, some (⟨160⟩, 1))
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode p30 = some (.SHL, .none)
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode p31 = some (.SUB, .none)
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode p32 = some (.DUP2, .none)
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode p33 = some (.CALLDATALOAD, .none)
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode p34 = some (.DUP2, .none)
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode p35 = some (.AND, .none)
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode p36 = some (.SWAP2, .none)
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode p37 =
      some (.Push .PUSH1, some (⟨32⟩, 1))
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode p39 = some (.ADD, .none)
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode p40 = some (.CALLDATALOAD, .none)
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode p41 = some (.AND, .none)
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode p42 =
      some (.Push .PUSH2, some (routine, 2))
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode p45 = some (.JUMP, .none)

/-- Discharge a concrete Uniswap two-address external entry bytecode-shape proof. -/
macro "uniswap_two_address_external_entry_wf" : term =>
  `(by
    unfold UniswapV2Pair.uniswapTwoAddressExternalEntryWf
    repeat' first | apply And.intro | native_decide)

-- GENERALIZES Reasoning.Reach.RD.uniswapTwoAddressGetterLenOk — parameterizes the continuation
-- pc instead of hardcoding Uniswap's one-word return wrapper at pc 861.
-- LIBRARY CANDIDATE: Reasoning.Reach — first half of an optimizer-on solc two-address external
-- wrapper, parameterized by bytecode, entry PC, continuation PC, and target routine.
set_option maxHeartbeats 1000000 in
theorem RD.uniswapTwoAddressExternalLenOk {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    {entry ret routine : UInt256}
    (hreach : ∃ k C, RD UniswapV2Pair.uniswapV2PairBytecode I g
      (Reasoning.Theory.initState cA gh bl σ σ₀ g A I) entry [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hwf : uniswapTwoAddressExternalEntryWf entry ret routine)
    (hdecoded : (D_J UniswapV2Pair.uniswapV2PairBytecode 0).contains
      (uniswapTwoAddressExternalDecodedPc entry) = true)
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size) :
    ∃ k C, RD UniswapV2Pair.uniswapV2PairBytecode I g
      (Reasoning.Theory.initState cA gh bl σ σ₀ g A I)
      (uniswapTwoAddressExternalDecodedPc entry)
      (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩ :: ⟨4⟩ :: ret :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rdEntry⟩ := hreach
  rcases hwf with
    ⟨hd0, hd1, hd4, hd6, hd7, hd8, hd9, hd11, hd12, hd13, hd14, hd17, _hd18,
      _hd20, _hd21, hd22, _hd23, _hd24, _hd26, _hd28, _hd30, _hd31, _hd32,
      _hd33, _hd34, _hd35, _hd36, _hd37, _hd39, _hd40, _hd41, _hd42, _hd45⟩
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨0⟩ :=
    UniswapV2Pair.uniswapDecodeLenCheckOk_4_64_lt hsz68 hsize
  have hjumpCond :
      UInt256.isZero (UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩) ≠
        ⟨0⟩ := by
    rw [hlt]
    decide
  have rd1 := rdEntry.jumpdest hd0 (by simp only [List.length_singleton]; omega)
  have rd4 := rd1.push2 ret hd1 (by evm_ov)
  have rd6 := rd4.push1 ⟨4⟩ hd4 (by evm_ov)
  have rd7 := rd6.dup1 hd6 (by evm_ov)
  have rd8 := rd7.calldatasize hd7 (by evm_ov)
  have rd9 := rd8.sub hd8 (by evm_ov)
  have rd11 := rd9.push1 ⟨64⟩ hd9 (by evm_ov)
  have rd12 := rd11.dup2 hd11 (by evm_ov)
  have rd13 := rd12.lt hd12 (by evm_ov)
  have rd14 := rd13.iszero hd13 (by evm_ov)
  have rd17 := rd14.push2 (uniswapTwoAddressExternalDecodedPc entry) hd14 (by evm_ov)
  exact ⟨_, _, rd17.jumpiT hd17 hjumpCond hdecoded (by evm_ov)⟩

-- GENERALIZES Reasoning.Reach.RD.uniswapTwoAddressGetterMaskAndJump — parameterizes the
-- continuation pc instead of hardcoding Uniswap's one-word return wrapper at pc 861.
-- LIBRARY CANDIDATE: Reasoning.Reach — second half of an optimizer-on solc two-address external
-- wrapper, parameterized by bytecode, entry PC, continuation PC, and target routine.
set_option maxHeartbeats 1000000 in
theorem RD.uniswapTwoAddressExternalMaskAndJump {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {entry ret routine de : UInt256} {R : List UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0
      (uniswapTwoAddressExternalDecodedPc entry) (de :: ⟨4⟩ :: ret :: R)
      solcFreePtrMem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hwf : uniswapTwoAddressExternalEntryWf entry ret routine)
    (hcanon0 : (calldataWord ee.calldata 4).toNat < EVM.addressModulus)
    (hcanon1 : (calldataWord ee.calldata 36).toNat < EVM.addressModulus)
    (hroutine : (D_J UniswapV2Pair.uniswapV2PairBytecode 0).contains routine = true)
    (hov : R.length + 7 ≤ 1024) :
    ∃ k' C', RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 routine
      (calldataWord ee.calldata 36 :: calldataWord ee.calldata 4 :: ret :: R)
      solcFreePtrMem (UInt256.ofNat 3) rdata (cA, σ) k' C' := by
  rcases hwf with
    ⟨_hd0, _hd1, _hd4, _hd6, _hd7, _hd8, _hd9, _hd11, _hd12, _hd13, _hd14,
      _hd17, _hd18, _hd20, _hd21, hd22, hd23, hd24, hd26, hd28, hd30, hd31,
      hd32, hd33, hd34, hd35, hd36, hd37, hd39, hd40, hd41, hd42, hd45⟩
  have hmask0 :
      UInt256.land (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩)
          (calldataWord ee.calldata 4) =
        calldataWord ee.calldata 4 := by
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide]
    exact solcAddrMask_clean_left hcanon0
  have hmask1 :
      UInt256.land (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩)
          (calldataWord ee.calldata 36) =
        calldataWord ee.calldata 36 := by
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide]
    exact solcAddrMask_clean_left hcanon1
  have hmask1Right :
      UInt256.land (calldataWord ee.calldata 36)
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) =
        calldataWord ee.calldata 36 := by
    rw [u256_land_comm]
    exact hmask1
  have rd23 := h.jumpdest hd22 (by evm_ov)
  have rd24 := rd23.pop hd23 (by evm_ov)
  have rd26 := rd24.push1 ⟨1⟩ hd24 (by evm_ov)
  have rd28 := rd26.push1 ⟨1⟩ hd26 (by evm_ov)
  have rd30 := rd28.push1 ⟨160⟩ hd28 (by evm_ov)
  have rd31 := rd30.shl hd30 (by evm_ov)
  have rd32 := rd31.sub hd31 (by evm_ov)
  have rd33 := rd32.dup2 hd32 (by evm_ov)
  have rd34 := rd33.calldataload hd33 (by evm_ov)
  have rd35 := rd34.dup2 hd34 (by evm_ov)
  have rd36 := rd35.and hd35 (by evm_ov)
  have rd37 := rd36.swap2 hd36 (by evm_ov)
  have rd39 := rd37.push1 ⟨32⟩ hd37 (by evm_ov)
  have rd40 := rd39.add hd39 (by evm_ov)
  have rd41 := rd40.calldataload hd40 (by evm_ov)
  have rd42 := rd41.and hd41 (by evm_ov)
  have rd45 := rd42.push2 routine hd42 (by evm_ov)
  exact ⟨_, _, by
    simpa [calldataWord, show (⟨4⟩ : UInt256).toNat = 4 from by decide,
      show ((⟨32⟩ : UInt256) + ⟨4⟩).toNat = 36 from by decide,
      hmask0, hmask1, hmask1Right]
      using rd45.jump hd45 hroutine (by evm_ov)⟩

/-! ## Shared address/uint256 external entry -/

/-- PC of the post-length-check decode block in Uniswap's optimized address/uint256 wrappers. -/
@[reducible] def uniswapAddressUint256ExternalDecodedPc (pc : UInt256) : UInt256 :=
  uniswapTwoAddressGetterDecodedPc pc

/-- Bytecode shape for Uniswap's optimized external address/uint256 wrappers.

The wrapper checks that two static ABI words are present, masks the address word, leaves the
`uint256` word raw, and jumps to a routine while preserving the return/continuation pc.
-/
@[reducible] def uniswapAddressUint256ExternalEntryWf
    (pc ret routine : UInt256) : Prop :=
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
  let p22 := uniswapAddressUint256ExternalDecodedPc pc
  let p23 := p22 + ⟨1⟩
  let p24 := p23 + ⟨1⟩
  let p26 := p24 + UInt256.ofNat 2
  let p28 := p26 + UInt256.ofNat 2
  let p30 := p28 + UInt256.ofNat 2
  let p31 := p30 + ⟨1⟩
  let p32 := p31 + ⟨1⟩
  let p33 := p32 + ⟨1⟩
  let p34 := p33 + ⟨1⟩
  let p35 := p34 + ⟨1⟩
  let p36 := p35 + ⟨1⟩
  let p38 := p36 + UInt256.ofNat 2
  let p39 := p38 + ⟨1⟩
  let p40 := p39 + ⟨1⟩
  let p43 := p40 + UInt256.ofNat 3
  decode UniswapV2Pair.uniswapV2PairBytecode pc = some (.JUMPDEST, .none)
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode p1 =
      some (.Push .PUSH2, some (ret, 2))
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode p4 =
      some (.Push .PUSH1, some (⟨4⟩, 1))
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode p6 = some (.DUP1, .none)
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode p7 = some (.CALLDATASIZE, .none)
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode p8 = some (.SUB, .none)
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode p9 =
      some (.Push .PUSH1, some (⟨64⟩, 1))
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode p11 = some (.DUP2, .none)
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode p12 = some (.LT, .none)
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode p13 = some (.ISZERO, .none)
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode p14 =
      some (.Push .PUSH2, some (p22, 2))
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode p17 = some (.JUMPI, .none)
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode p18 =
      some (.Push .PUSH1, some (⟨0⟩, 1))
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode p20 = some (.DUP1, .none)
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode p21 = some (.REVERT, .none)
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode p22 = some (.JUMPDEST, .none)
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode p23 = some (.POP, .none)
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode p24 =
      some (.Push .PUSH1, some (⟨1⟩, 1))
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode p26 =
      some (.Push .PUSH1, some (⟨1⟩, 1))
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode p28 =
      some (.Push .PUSH1, some (⟨160⟩, 1))
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode p30 = some (.SHL, .none)
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode p31 = some (.SUB, .none)
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode p32 = some (.DUP2, .none)
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode p33 = some (.CALLDATALOAD, .none)
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode p34 = some (.AND, .none)
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode p35 = some (.SWAP1, .none)
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode p36 =
      some (.Push .PUSH1, some (⟨32⟩, 1))
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode p38 = some (.ADD, .none)
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode p39 = some (.CALLDATALOAD, .none)
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode p40 =
      some (.Push .PUSH2, some (routine, 2))
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode p43 = some (.JUMP, .none)

/-- Discharge a concrete Uniswap address/uint256 external entry bytecode-shape proof. -/
macro "uniswap_address_uint256_external_entry_wf" : term =>
  `(by
    unfold UniswapV2Pair.uniswapAddressUint256ExternalEntryWf
    repeat' first | apply And.intro | native_decide)

-- GENERALIZES Reasoning.Reach.RD.uniswapTwoAddressGetterLenOk — same static two-word length
-- check, but parameterized over a non-getter return pc and an address/uint256 continuation.
-- LIBRARY CANDIDATE: Reasoning.Reach — first half of an optimizer-on solc address/uint256
-- external wrapper, parameterized by bytecode, entry PC, continuation PC, and target routine.
set_option maxHeartbeats 1000000 in
theorem RD.uniswapAddressUint256ExternalLenOk {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256} {entry ret routine : UInt256}
    (hreach : ∃ k C, RD UniswapV2Pair.uniswapV2PairBytecode I g
      (Reasoning.Theory.initState cA gh bl σ σ₀ g A I) entry [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hwf : uniswapAddressUint256ExternalEntryWf entry ret routine)
    (hdecoded : (D_J UniswapV2Pair.uniswapV2PairBytecode 0).contains
      (uniswapAddressUint256ExternalDecodedPc entry) = true)
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size) :
    ∃ k C, RD UniswapV2Pair.uniswapV2PairBytecode I g
      (Reasoning.Theory.initState cA gh bl σ σ₀ g A I)
      (uniswapAddressUint256ExternalDecodedPc entry)
      (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩ :: ⟨4⟩ :: ret :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rdEntry⟩ := hreach
  rcases hwf with
    ⟨hd0, hd1, hd4, hd6, hd7, hd8, hd9, hd11, hd12, hd13, hd14, hd17, _hd18,
      _hd20, _hd21, hd22, _hd23, _hd24, _hd26, _hd28, _hd30, _hd31, _hd32,
      _hd33, _hd34, _hd35, _hd36, _hd38, _hd39, _hd40, _hd43⟩
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨0⟩ :=
    UniswapV2Pair.uniswapDecodeLenCheckOk_4_64_lt hsz68 hsize
  have hjumpCond :
      UInt256.isZero (UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩) ≠
        ⟨0⟩ := by
    rw [hlt]
    decide
  have rd1 := rdEntry.jumpdest hd0 (by simp only [List.length_singleton]; omega)
  have rd4 := rd1.push2 ret hd1 (by evm_ov)
  have rd6 := rd4.push1 ⟨4⟩ hd4 (by evm_ov)
  have rd7 := rd6.dup1 hd6 (by evm_ov)
  have rd8 := rd7.calldatasize hd7 (by evm_ov)
  have rd9 := rd8.sub hd8 (by evm_ov)
  have rd11 := rd9.push1 ⟨64⟩ hd9 (by evm_ov)
  have rd12 := rd11.dup2 hd11 (by evm_ov)
  have rd13 := rd12.lt hd12 (by evm_ov)
  have rd14 := rd13.iszero hd13 (by evm_ov)
  have rd17 := rd14.push2 (uniswapAddressUint256ExternalDecodedPc entry) hd14 (by evm_ov)
  exact ⟨_, _, rd17.jumpiT hd17 hjumpCond hdecoded (by evm_ov)⟩

-- GENERALIZES Reasoning.Reach.RD.uniswapTwoAddressGetterMaskAndJump — keeps the second static ABI
-- word raw instead of applying the solc address mask to both words.
-- LIBRARY CANDIDATE: Reasoning.Reach — second half of an optimizer-on solc address/uint256
-- external wrapper, parameterized by bytecode, entry PC, continuation PC, and target routine.
set_option maxHeartbeats 1000000 in
theorem RD.uniswapAddressUint256ExternalMaskAndJump {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {entry ret routine de : UInt256} {R : List UInt256}
    {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0
      (uniswapAddressUint256ExternalDecodedPc entry) (de :: ⟨4⟩ :: ret :: R)
      solcFreePtrMem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hwf : uniswapAddressUint256ExternalEntryWf entry ret routine)
    (hcanon : (calldataWord ee.calldata 4).toNat < EVM.addressModulus)
    (hroutine : (D_J UniswapV2Pair.uniswapV2PairBytecode 0).contains routine = true)
    (hov : R.length + 6 ≤ 1024) :
    ∃ k' C', RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 routine
      (calldataWord ee.calldata 36 :: calldataWord ee.calldata 4 :: ret :: R)
      solcFreePtrMem (UInt256.ofNat 3) rdata (cA, σ) k' C' := by
  rcases hwf with
    ⟨_hd0, _hd1, _hd4, _hd6, _hd7, _hd8, _hd9, _hd11, _hd12, _hd13, _hd14,
      _hd17, _hd18, _hd20, _hd21, hd22, hd23, hd24, hd26, hd28, hd30, hd31,
      hd32, hd33, hd34, hd35, hd36, hd38, hd39, hd40, hd43⟩
  have hmask :
      UInt256.land (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩)
          (calldataWord ee.calldata 4) =
        calldataWord ee.calldata 4 := by
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide]
    exact solcAddrMask_clean_left hcanon
  have hmaskRight :
      UInt256.land (calldataWord ee.calldata 4)
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) =
        calldataWord ee.calldata 4 := by
    rw [u256_land_comm]
    exact hmask
  have rd23 := h.jumpdest hd22 (by evm_ov)
  have rd24 := rd23.pop hd23 (by evm_ov)
  have rd26 := rd24.push1 ⟨1⟩ hd24 (by evm_ov)
  have rd28 := rd26.push1 ⟨1⟩ hd26 (by evm_ov)
  have rd30 := rd28.push1 ⟨160⟩ hd28 (by evm_ov)
  have rd31 := rd30.shl hd30 (by evm_ov)
  have rd32 := rd31.sub hd31 (by evm_ov)
  have rd33 := rd32.dup2 hd32 (by evm_ov)
  have rd34 := rd33.calldataload hd33 (by evm_ov)
  have rd35 := rd34.and hd34 (by evm_ov)
  have rd36 := rd35.swap1 hd35 (by evm_ov)
  have rd38 := rd36.push1 ⟨32⟩ hd36 (by evm_ov)
  have rd39 := rd38.add hd38 (by evm_ov)
  have rd40 := rd39.calldataload hd39 (by evm_ov)
  have rd43 := rd40.push2 routine hd40 (by evm_ov)
  exact ⟨_, _, by
    simpa [calldataWord, show (⟨4⟩ : UInt256).toNat = 4 from by decide,
      show ((⟨32⟩ : UInt256) + ⟨4⟩).toNat = 36 from by decide, hmaskRight]
      using rd43.jump hd43 hroutine (by evm_ov)⟩

-- GENERALIZES Reasoning.Reach.RD.uniswapTwoAddressGetterMaskAndJump - keeps the second static ABI
-- word raw, and exposes the masked address word instead of requiring canonical calldata.
-- LIBRARY CANDIDATE: Reasoning.Reach - optimizer-on solc address/uint256 external wrapper that
-- returns the low-160-bit masked address word.
set_option maxHeartbeats 1000000 in
theorem RD.uniswapAddressUint256ExternalMaskAndJumpMasked {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {entry ret routine de : UInt256} {R : List UInt256}
    {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0
      (uniswapAddressUint256ExternalDecodedPc entry) (de :: ⟨4⟩ :: ret :: R)
      solcFreePtrMem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hwf : uniswapAddressUint256ExternalEntryWf entry ret routine)
    (hroutine : (D_J UniswapV2Pair.uniswapV2PairBytecode 0).contains routine = true)
    (hov : R.length + 6 ≤ 1024) :
    ∃ k' C', RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 routine
      (calldataWord ee.calldata 36 :: UInt256.land solcAddrMask (calldataWord ee.calldata 4) ::
        ret :: R)
      solcFreePtrMem (UInt256.ofNat 3) rdata (cA, σ) k' C' := by
  rcases hwf with
    ⟨_hd0, _hd1, _hd4, _hd6, _hd7, _hd8, _hd9, _hd11, _hd12, _hd13, _hd14,
      _hd17, _hd18, _hd20, _hd21, hd22, hd23, hd24, hd26, hd28, hd30, hd31,
      hd32, hd33, hd34, hd35, hd36, hd38, hd39, hd40, hd43⟩
  have rd23 := h.jumpdest hd22 (by evm_ov)
  have rd24 := rd23.pop hd23 (by evm_ov)
  have rd26 := rd24.push1 ⟨1⟩ hd24 (by evm_ov)
  have rd28 := rd26.push1 ⟨1⟩ hd26 (by evm_ov)
  have rd30 := rd28.push1 ⟨160⟩ hd28 (by evm_ov)
  have rd31 := rd30.shl hd30 (by evm_ov)
  have rd32 := rd31.sub hd31 (by evm_ov)
  have rd33 := rd32.dup2 hd32 (by evm_ov)
  have rd34 := rd33.calldataload hd33 (by evm_ov)
  have rd35 := rd34.and hd34 (by evm_ov)
  have rd36 := rd35.swap1 hd35 (by evm_ov)
  have rd38 := rd36.push1 ⟨32⟩ hd36 (by evm_ov)
  have rd39 := rd38.add hd38 (by evm_ov)
  have rd40 := rd39.calldataload hd39 (by evm_ov)
  have rd43 := rd40.push2 routine hd40 (by evm_ov)
  exact ⟨_, _, by
    simpa [calldataWord, show (⟨4⟩ : UInt256).toNat = 4 from by decide,
      show ((⟨32⟩ : UInt256) + ⟨4⟩).toNat = 36 from by decide,
      show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask from by decide, u256_land_comm]
      using rd43.jump hd43 hroutine (by evm_ov)⟩

/-! ## Shared address/address/uint256 external entry -/

/-- PC of the post-length-check decode block in Uniswap's optimized
address/address/uint256 wrappers. -/
@[reducible] def uniswapAddressAddressUint256ExternalDecodedPc (pc : UInt256) : UInt256 :=
  uniswapTwoAddressGetterDecodedPc pc

/-- Bytecode shape for Uniswap's optimized external address/address/uint256 wrappers.

The wrapper checks that three static ABI words are present, masks the first two address words,
leaves the `uint256` word raw, and jumps to a routine while preserving the return/continuation pc.
-/
@[reducible] def uniswapAddressAddressUint256ExternalEntryWf
    (pc ret routine : UInt256) : Prop :=
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
  let p22 := uniswapAddressAddressUint256ExternalDecodedPc pc
  let p23 := p22 + ⟨1⟩
  let p24 := p23 + ⟨1⟩
  let p26 := p24 + UInt256.ofNat 2
  let p28 := p26 + UInt256.ofNat 2
  let p30 := p28 + UInt256.ofNat 2
  let p31 := p30 + ⟨1⟩
  let p32 := p31 + ⟨1⟩
  let p33 := p32 + ⟨1⟩
  let p34 := p33 + ⟨1⟩
  let p35 := p34 + ⟨1⟩
  let p36 := p35 + ⟨1⟩
  let p37 := p36 + ⟨1⟩
  let p39 := p37 + UInt256.ofNat 2
  let p40 := p39 + ⟨1⟩
  let p41 := p40 + ⟨1⟩
  let p42 := p41 + ⟨1⟩
  let p43 := p42 + ⟨1⟩
  let p44 := p43 + ⟨1⟩
  let p45 := p44 + ⟨1⟩
  let p46 := p45 + ⟨1⟩
  let p48 := p46 + UInt256.ofNat 2
  let p49 := p48 + ⟨1⟩
  let p50 := p49 + ⟨1⟩
  let p53 := p50 + UInt256.ofNat 3
  decode UniswapV2Pair.uniswapV2PairBytecode pc = some (.JUMPDEST, .none)
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode p1 =
      some (.Push .PUSH2, some (ret, 2))
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode p4 =
      some (.Push .PUSH1, some (⟨4⟩, 1))
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode p6 = some (.DUP1, .none)
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode p7 = some (.CALLDATASIZE, .none)
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode p8 = some (.SUB, .none)
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode p9 =
      some (.Push .PUSH1, some (⟨96⟩, 1))
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode p11 = some (.DUP2, .none)
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode p12 = some (.LT, .none)
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode p13 = some (.ISZERO, .none)
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode p14 =
      some (.Push .PUSH2, some (p22, 2))
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode p17 = some (.JUMPI, .none)
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode p18 =
      some (.Push .PUSH1, some (⟨0⟩, 1))
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode p20 = some (.DUP1, .none)
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode p21 = some (.REVERT, .none)
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode p22 = some (.JUMPDEST, .none)
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode p23 = some (.POP, .none)
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode p24 =
      some (.Push .PUSH1, some (⟨1⟩, 1))
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode p26 =
      some (.Push .PUSH1, some (⟨1⟩, 1))
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode p28 =
      some (.Push .PUSH1, some (⟨160⟩, 1))
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode p30 = some (.SHL, .none)
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode p31 = some (.SUB, .none)
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode p32 = some (.DUP2, .none)
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode p33 = some (.CALLDATALOAD, .none)
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode p34 = some (.DUP2, .none)
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode p35 = some (.AND, .none)
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode p36 = some (.SWAP2, .none)
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode p37 =
      some (.Push .PUSH1, some (⟨32⟩, 1))
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode p39 = some (.DUP2, .none)
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode p40 = some (.ADD, .none)
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode p41 = some (.CALLDATALOAD, .none)
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode p42 = some (.SWAP1, .none)
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode p43 = some (.SWAP2, .none)
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode p44 = some (.AND, .none)
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode p45 = some (.SWAP1, .none)
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode p46 =
      some (.Push .PUSH1, some (⟨64⟩, 1))
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode p48 = some (.ADD, .none)
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode p49 = some (.CALLDATALOAD, .none)
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode p50 =
      some (.Push .PUSH2, some (routine, 2))
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode p53 = some (.JUMP, .none)

/-- Discharge a concrete Uniswap address/address/uint256 external entry bytecode-shape proof. -/
macro "uniswap_address_address_uint256_external_entry_wf" : term =>
  `(by
    unfold UniswapV2Pair.uniswapAddressAddressUint256ExternalEntryWf
    repeat' first | apply And.intro | native_decide)

-- GENERALIZES Reasoning.Reach.RD.uniswapTwoAddressGetterLenOk — same static calldata length
-- check, but for three ABI words and parameterized over a non-getter return pc and continuation.
-- LIBRARY CANDIDATE: Reasoning.Reach — first half of an optimizer-on solc
-- address/address/uint256 external wrapper, parameterized by bytecode, entry PC,
-- continuation PC, and target routine.
set_option maxHeartbeats 1000000 in
theorem RD.uniswapAddressAddressUint256ExternalLenOk {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256} {entry ret routine : UInt256}
    (hreach : ∃ k C, RD UniswapV2Pair.uniswapV2PairBytecode I g
      (Reasoning.Theory.initState cA gh bl σ σ₀ g A I) entry [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hwf : uniswapAddressAddressUint256ExternalEntryWf entry ret routine)
    (hdecoded : (D_J UniswapV2Pair.uniswapV2PairBytecode 0).contains
      (uniswapAddressAddressUint256ExternalDecodedPc entry) = true)
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size) :
    ∃ k C, RD UniswapV2Pair.uniswapV2PairBytecode I g
      (Reasoning.Theory.initState cA gh bl σ σ₀ g A I)
      (uniswapAddressAddressUint256ExternalDecodedPc entry)
      (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩ :: ⟨4⟩ :: ret :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rdEntry⟩ := hreach
  rcases hwf with
    ⟨hd0, hd1, hd4, hd6, hd7, hd8, hd9, hd11, hd12, hd13, hd14, hd17, _hd18,
      _hd20, _hd21, _hd22, _hd23, _hd24, _hd26, _hd28, _hd30, _hd31, _hd32,
      _hd33, _hd34, _hd35, _hd36, _hd37, _hd39, _hd40, _hd41, _hd42, _hd43,
      _hd44, _hd45, _hd46, _hd48, _hd49, _hd50, _hd53⟩
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨96⟩ = ⟨0⟩ :=
    UniswapV2Pair.uniswapDecodeLenCheckOk_4_96_lt hsz100 hsize
  have hjumpCond :
      UInt256.isZero (UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨96⟩) ≠
        ⟨0⟩ := by
    rw [hlt]
    decide
  have rd1 := rdEntry.jumpdest hd0 (by simp only [List.length_singleton]; omega)
  have rd4 := rd1.push2 ret hd1 (by evm_ov)
  have rd6 := rd4.push1 ⟨4⟩ hd4 (by evm_ov)
  have rd7 := rd6.dup1 hd6 (by evm_ov)
  have rd8 := rd7.calldatasize hd7 (by evm_ov)
  have rd9 := rd8.sub hd8 (by evm_ov)
  have rd11 := rd9.push1 ⟨96⟩ hd9 (by evm_ov)
  have rd12 := rd11.dup2 hd11 (by evm_ov)
  have rd13 := rd12.lt hd12 (by evm_ov)
  have rd14 := rd13.iszero hd13 (by evm_ov)
  have rd17 := rd14.push2 (uniswapAddressAddressUint256ExternalDecodedPc entry) hd14
    (by evm_ov)
  exact ⟨_, _, rd17.jumpiT hd17 hjumpCond hdecoded (by evm_ov)⟩

-- GENERALIZES Reasoning.Reach.RD.uniswapTwoAddressGetterMaskAndJump — masks two leading
-- address words and keeps the third static ABI word raw.
-- LIBRARY CANDIDATE: Reasoning.Reach — second half of an optimizer-on solc
-- address/address/uint256 external wrapper, parameterized by bytecode, entry PC,
-- continuation PC, and target routine.
set_option maxHeartbeats 1000000 in
theorem RD.uniswapAddressAddressUint256ExternalMaskAndJump {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {entry ret routine de : UInt256} {R : List UInt256}
    {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0
      (uniswapAddressAddressUint256ExternalDecodedPc entry) (de :: ⟨4⟩ :: ret :: R)
      solcFreePtrMem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hwf : uniswapAddressAddressUint256ExternalEntryWf entry ret routine)
    (hcanon0 : (calldataWord ee.calldata 4).toNat < EVM.addressModulus)
    (hcanon1 : (calldataWord ee.calldata 36).toNat < EVM.addressModulus)
    (hroutine : (D_J UniswapV2Pair.uniswapV2PairBytecode 0).contains routine = true)
    (hov : R.length + 7 ≤ 1024) :
    ∃ k' C', RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 routine
      (calldataWord ee.calldata 68 :: calldataWord ee.calldata 36 ::
        calldataWord ee.calldata 4 :: ret :: R)
      solcFreePtrMem (UInt256.ofNat 3) rdata (cA, σ) k' C' := by
  rcases hwf with
    ⟨_hd0, _hd1, _hd4, _hd6, _hd7, _hd8, _hd9, _hd11, _hd12, _hd13, _hd14,
      _hd17, _hd18, _hd20, _hd21, hd22, hd23, hd24, hd26, hd28, hd30, hd31,
      hd32, hd33, hd34, hd35, hd36, hd37, hd39, hd40, hd41, hd42, hd43, hd44,
      hd45, hd46, hd48, hd49, hd50, hd53⟩
  have hmask0 :
      UInt256.land (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩)
          (calldataWord ee.calldata 4) =
        calldataWord ee.calldata 4 := by
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide]
    exact solcAddrMask_clean_left hcanon0
  have hmask1 :
      UInt256.land (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩)
          (calldataWord ee.calldata 36) =
        calldataWord ee.calldata 36 := by
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide]
    exact solcAddrMask_clean_left hcanon1
  have rd23 := h.jumpdest hd22 (by evm_ov)
  have rd24 := rd23.pop hd23 (by evm_ov)
  have rd26 := rd24.push1 ⟨1⟩ hd24 (by evm_ov)
  have rd28 := rd26.push1 ⟨1⟩ hd26 (by evm_ov)
  have rd30 := rd28.push1 ⟨160⟩ hd28 (by evm_ov)
  have rd31 := rd30.shl hd30 (by evm_ov)
  have rd32 := rd31.sub hd31 (by evm_ov)
  have rd33 := rd32.dup2 hd32 (by evm_ov)
  have rd34 := rd33.calldataload hd33 (by evm_ov)
  have rd35 := rd34.dup2 hd34 (by evm_ov)
  have rd36 := rd35.and hd35 (by evm_ov)
  have rd37 := rd36.swap2 hd36 (by evm_ov)
  have rd39 := rd37.push1 ⟨32⟩ hd37 (by evm_ov)
  have rd40 := rd39.dup2 hd39 (by evm_ov)
  have rd41 := rd40.add hd40 (by evm_ov)
  have rd42 := rd41.calldataload hd41 (by evm_ov)
  have rd43 := rd42.swap1 hd42 (by evm_ov)
  have rd44 := rd43.swap2 hd43 (by evm_ov)
  have rd45 := rd44.and hd44 (by evm_ov)
  have rd46 := rd45.swap1 hd45 (by evm_ov)
  have rd48 := rd46.push1 ⟨64⟩ hd46 (by evm_ov)
  have rd49 := rd48.add hd48 (by evm_ov)
  have rd50 := rd49.calldataload hd49 (by evm_ov)
  have rd53 := rd50.push2 routine hd50 (by evm_ov)
  exact ⟨_, _, by
    simpa [calldataWord, show (⟨4⟩ : UInt256).toNat = 4 from by decide,
      show ((⟨4⟩ : UInt256) + ⟨32⟩).toNat = 36 from by decide,
      show ((⟨32⟩ : UInt256) + ⟨4⟩).toNat = 36 from by decide,
      show ((⟨64⟩ : UInt256) + ⟨4⟩).toNat = 68 from by decide, hmask0, hmask1]
      using rd53.jump hd53 hroutine (by evm_ov)⟩

/-! ## Shared checked-arithmetic routines -/

-- GENERALIZES Examples.ERC20.Transfer.erc20RoutineCheckedSub — same optimizer-on solc
-- SafeMath-style `sub` success tail, parameterized over memory, active words, return data, and
-- continuation stack for Uniswap's pc layout.
-- LIBRARY CANDIDATE: Reasoning.Reach — generic solc checked-sub success routine with dynamic
-- return pc; should be parameterized by bytecode, entry pc, success-tail pc, and overflow branch.
set_option maxHeartbeats 1000000 in
theorem RD.uniswapSafeMathSubSuccess {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {a b ret : UInt256} {R : List UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨6879⟩ (b :: a :: ret :: R)
      mem aw rdata acc k C)
    (hle : b.toNat ≤ a.toNat)
    (hret : (D_J UniswapV2Pair.uniswapV2PairBytecode 0).contains ret = true)
    (hov : R.length + 9 ≤ 1024) :
    ∃ k' C', RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ret
      (UInt256.sub a b :: R) mem aw rdata acc k' C' := by
  have hsubNat : (UInt256.sub a b).toNat = a.toNat - b.toNat := usub_toNat hle
  have hgt : UInt256.gt (UInt256.sub a b) a = ⟨0⟩ :=
    ugt_zero (by rw [hsubNat]; omega)
  have rd6886 := evm_run h with [jumpdest, dup1, dup3, sub, dup3, dup2]
  have rd6887₀ := evm_run rd6886 with [gt]
  have rd6887 := rd6887₀
  rw [hgt] at rd6887
  have rd6888₀ := evm_run rd6887 with [iszero]
  have rd6888 := rd6888₀
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd6888
  have rd2911 := evm_run rd6888 with [
    push2 ⟨2911⟩, jumpiT one_ne_zero_uint (by jump_dest)]
  exact ⟨_, _, evm_run rd2911 with [
    jumpdest, swap3, swap2, pop, pop, jump hret]⟩

-- GENERALIZES Examples.ERC20.Transfer.erc20RoutineCheckedAdd — same optimizer-on solc
-- SafeMath-style `add` success tail, parameterized over memory, active words, return data, and
-- continuation stack for Uniswap's pc layout.
-- LIBRARY CANDIDATE: Reasoning.Reach — generic solc checked-add success routine with dynamic
-- return pc; should be parameterized by bytecode, entry pc, success-tail pc, and overflow branch.
set_option maxHeartbeats 1000000 in
theorem RD.uniswapSafeMathAddSuccess {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {a b ret : UInt256} {R : List UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨8515⟩ (b :: a :: ret :: R)
      mem aw rdata acc k C)
    (hfit : a.toNat + b.toNat < UInt256.size)
    (hret : (D_J UniswapV2Pair.uniswapV2PairBytecode 0).contains ret = true)
    (hov : R.length + 9 ≤ 1024) :
    ∃ k' C', RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ret
      ((a + b) :: R) mem aw rdata acc k' C' := by
  have haddNat : (a + b).toNat = a.toNat + b.toNat := by
    rw [uadd_toNat, Nat.mod_eq_of_lt hfit]
  have hlt : UInt256.lt (a + b) a = ⟨0⟩ :=
    ult_zero (by rw [haddNat]; omega)
  have rd8521 := evm_run h with [jumpdest, dup1, dup3, add, dup3, dup2]
  have rd8522₀ := evm_run rd8521 with [lt]
  have rd8522 := rd8522₀
  rw [hlt] at rd8522
  have rd8523₀ := evm_run rd8522 with [iszero]
  have rd8523 := rd8523₀
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd8523
  have rd2911 := evm_run rd8523 with [
    push2 ⟨2911⟩, jumpiT one_ne_zero_uint (by jump_dest)]
  exact ⟨_, _, evm_run rd2911 with [
    jumpdest, swap3, swap2, pop, pop, jump hret]⟩

/-! ## Shared internal `_transfer` routine prefix -/

abbrev uniswapCodeOwnerStorageWord (ee : ExecutionEnv) (σ : AccountMap)
    (slot : UInt256) : UInt256 :=
  codeOwnerStorageWord ee σ slot

theorem uniswapCodeOwnerStorageWord_initState {cA gh bl σ σ₀ A I} {g : Sat256}
    (slot : UInt256) :
    Solm.EVM.storageLoad (initState cA gh bl σ σ₀ g A I) I.codeOwner slot =
      uniswapCodeOwnerStorageWord I σ slot := by
  exact codeOwnerStorageWord_initState slot

-- GENERALIZES Examples.UniswapV2Pair.Routines.RD.uniswapTransferInternalFromBalanceLoad —
-- parameterizes the initial 96-byte scratch memory instead of requiring `solcFreePtrMem`.
-- LIBRARY CANDIDATE: Reasoning.Reach — optimizer-on solc single-mapping load prefix that masks
-- an address key, writes `key || baseSlot` into scratch memory, hashes it, `SLOAD`s the slot, and
-- jumps to a checked-arithmetic routine with a dynamic continuation.
set_option maxHeartbeats 1000000 in
theorem RD.uniswapTransferInternalFromBalanceLoadMem {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {value toWord src ret : UInt256}
    {R : List UInt256} {mem rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨7510⟩
        (value :: toWord :: src :: ret :: R)
        mem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hmem : mem.size = 96)
    (hcanonSrc : src.toNat < EVM.addressModulus)
    (hov : R.length + 16 ≤ 1024) :
    ∃ k' C', RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨6879⟩
      (value :: uniswapCodeOwnerStorageWord ee σ (mapSlot src ⟨1⟩) ::
        ⟨7551⟩ :: value :: toWord :: src :: ret :: R)
      (twoWordHashMem src ⟨1⟩ mem)
      (UInt256.ofNat 3) rdata (cA, σ) k' C' := by
  have hmask : UInt256.land src solcAddrMask = src :=
    solcAddrMask_clean hcanonSrc
  have hmaskLiteral :
      UInt256.land src (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) =
        src := by
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide]
    exact hmask
  have hslot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((twoWordHashMem src ⟨1⟩ mem).readWithPadding 0 64))) =
        mapSlot src ⟨1⟩ := by
    rw [twoWordHashMem_read0_64 src ⟨1⟩ hmem]
    unfold mapSlot
    exact mappingSlot_single src ⟨1⟩
  have rd7521 := evm_run h with [
    jumpdest, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup4, and]
  rw [hmaskLiteral] at rd7521
  have rd7525 := evm_run rd7521 with [push1 ⟨0⟩, swap1, dup2]
  have rd7526 := rd7525.mstore 0 (wordAt0Mem src mem)
    (UInt256.ofNat 3) (by decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd7531 := evm_run rd7526 with [push1 ⟨1⟩, push1 ⟨32⟩]
  have rd7532 := rd7531.mstore 0 (twoWordHashMem src ⟨1⟩ mem)
    (UInt256.ofNat 3) (by decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd7535 := evm_run rd7532 with [push1 ⟨64⟩, swap1]
  have rd7536 := rd7535.keccak256 0 (mapSlot src ⟨1⟩) (UInt256.ofNat 3)
    (by decide) mem_cost hslot (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd7537⟩ := rd7536.sload (by decide)
    (by simp only [List.length_cons]; omega)
  have rd7551 := evm_run rd7537 with [
    push2 ⟨7551⟩, swap1, dup3, push4 ⟨0xffffffff⟩, push2 ⟨6879⟩, and]
  exact ⟨_, _, by
    simpa [uniswapCodeOwnerStorageWord,
      show UInt256.land (⟨6879⟩ : UInt256) ⟨0xffffffff⟩ = ⟨6879⟩ from by decide]
      using rd7551.jump (by decide) (by jump_dest) (by evm_ov)⟩

-- LIBRARY CANDIDATE: Reasoning.Reach — pristine-memory specialization of
-- `RD.uniswapTransferInternalFromBalanceLoadMem` for the common external `transfer` path.
set_option maxHeartbeats 1000000 in
theorem RD.uniswapTransferInternalFromBalanceLoad {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {value toWord src ret : UInt256}
    {R : List UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨7510⟩
        (value :: toWord :: src :: ret :: R)
        solcFreePtrMem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hcanonSrc : src.toNat < EVM.addressModulus)
    (hov : R.length + 16 ≤ 1024) :
    ∃ k' C', RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨6879⟩
      (value :: uniswapCodeOwnerStorageWord ee σ (mapSlot src ⟨1⟩) ::
        ⟨7551⟩ :: value :: toWord :: src :: ret :: R)
      (twoWordHashMem src ⟨1⟩ solcFreePtrMem)
      (UInt256.ofNat 3) rdata (cA, σ) k' C' := by
  simpa using RD.uniswapTransferInternalFromBalanceLoadMem
    (mem := solcFreePtrMem) h solcFreePtrMem_size hcanonSrc hov

-- GENERALIZES Examples.ERC20.Transfer.erc20TransferX_afterDebit — isolates the reusable private
-- transfer debit prefix from the contract-specific storage-write and event-log suffix.
-- GENERALIZES Examples.UniswapV2Pair.Routines.RD.uniswapTransferInternalAfterDebit —
-- parameterizes the initial 96-byte scratch memory instead of requiring `solcFreePtrMem`.
-- LIBRARY CANDIDATE: Reasoning.Reach — mapping-load plus checked-sub success prefix for
-- optimizer-on ERC20-like transfer routines, parameterized by base slot, routine PCs, and initial
-- scratch memory.
set_option maxHeartbeats 1000000 in
theorem RD.uniswapTransferInternalAfterDebitMem {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {value toWord src ret : UInt256}
    {R : List UInt256} {mem rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨7510⟩
        (value :: toWord :: src :: ret :: R)
        mem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hmem : mem.size = 96)
    (hcanonSrc : src.toNat < EVM.addressModulus)
    (hbalance :
      value.toNat ≤ (uniswapCodeOwnerStorageWord ee σ (mapSlot src ⟨1⟩)).toNat)
    (hov : R.length + 16 ≤ 1024) :
    ∃ k' C', RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨7551⟩
      (UInt256.sub (uniswapCodeOwnerStorageWord ee σ (mapSlot src ⟨1⟩)) value ::
        value :: toWord :: src :: ret :: R)
      (twoWordHashMem src ⟨1⟩ mem)
      (UInt256.ofNat 3) rdata (cA, σ) k' C' := by
  obtain ⟨_, _, rd6879⟩ := RD.uniswapTransferInternalFromBalanceLoadMem
    (value := value) (toWord := toWord) (src := src) (ret := ret) (R := R)
    h hmem hcanonSrc hov
  obtain ⟨_, _, rd7551⟩ := RD.uniswapSafeMathSubSuccess
    (a := uniswapCodeOwnerStorageWord ee σ (mapSlot src ⟨1⟩))
    (b := value) (ret := ⟨7551⟩)
    (R := value :: toWord :: src :: ret :: R)
    rd6879 hbalance (by jump_dest)
    (by simp only [List.length_cons]; omega)
  exact ⟨_, _, rd7551⟩

-- LIBRARY CANDIDATE: Reasoning.Reach — pristine-memory specialization of
-- `RD.uniswapTransferInternalAfterDebitMem` for the common external `transfer` path.
set_option maxHeartbeats 1000000 in
theorem RD.uniswapTransferInternalAfterDebit {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {value toWord src ret : UInt256}
    {R : List UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨7510⟩
        (value :: toWord :: src :: ret :: R)
        solcFreePtrMem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hcanonSrc : src.toNat < EVM.addressModulus)
    (hbalance :
      value.toNat ≤ (uniswapCodeOwnerStorageWord ee σ (mapSlot src ⟨1⟩)).toNat)
    (hov : R.length + 16 ≤ 1024) :
    ∃ k' C', RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨7551⟩
      (UInt256.sub (uniswapCodeOwnerStorageWord ee σ (mapSlot src ⟨1⟩)) value ::
        value :: toWord :: src :: ret :: R)
      (twoWordHashMem src ⟨1⟩ solcFreePtrMem)
      (UInt256.ofNat 3) rdata (cA, σ) k' C' := by
  simpa using RD.uniswapTransferInternalAfterDebitMem
    (mem := solcFreePtrMem) h solcFreePtrMem_size hcanonSrc hbalance hov

-- LIBRARY CANDIDATE: Reasoning.Memory — double mapping-hash scratch rewrite over an arbitrary
-- 96-byte scratch buffer, useful for solc routines that reload and then store the same mapping slot.
noncomputable abbrev uniswapTransferDebitHashMemOf (src : UInt256) (mem : ByteArray) :
    ByteArray :=
  twoWordHashMem src ⟨1⟩ (twoWordHashMem src ⟨1⟩ mem)

-- LIBRARY CANDIDATE: Reasoning.Memory — size preservation for the double mapping-hash scratch
-- rewrite above.
theorem uniswapTransferDebitHashMemOf_size (src : UInt256) {mem : ByteArray}
    (hmem : mem.size = 96) :
    (uniswapTransferDebitHashMemOf src mem).size = 96 := by
  unfold uniswapTransferDebitHashMemOf
  exact twoWordHashMem_size_96 src ⟨1⟩ (twoWordHashMem_size_96 src ⟨1⟩ hmem)

noncomputable abbrev uniswapTransferDebitHashMem (src : UInt256) : ByteArray :=
  uniswapTransferDebitHashMemOf src solcFreePtrMem

theorem uniswapTransferDebitHashMem_size (src : UInt256) :
    (uniswapTransferDebitHashMem src).size = 96 := by
  exact uniswapTransferDebitHashMemOf_size src solcFreePtrMem_size

-- GENERALIZES Examples.UniswapV2Pair.Routines.RD.uniswapTransferInternalStoreDebit —
-- parameterizes the pre-existing 96-byte scratch memory instead of requiring `solcFreePtrMem`.
-- LIBRARY CANDIDATE: Reasoning.Reach — optimizer-on solc single-mapping store prefix that
-- recomputes an address-keyed mapping slot in scratch memory and performs `SSTORE`, parameterized
-- by base slot, routine PCs, and initial scratch memory.
set_option maxHeartbeats 4000000 in
theorem RD.uniswapTransferInternalStoreDebitMem {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {debit value toWord src ret : UInt256}
    {R : List UInt256} {mem rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨7551⟩
        (debit :: value :: toWord :: src :: ret :: R)
        (twoWordHashMem src ⟨1⟩ mem) (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hmem : mem.size = 96)
    (hperm : ee.perm = true)
    (hcanonSrc : src.toNat < EVM.addressModulus)
    (hov : R.length + 16 ≤ 1024) :
    ∃ k' C', RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨7582⟩
      (⟨0⟩ :: solcAddrMask :: ⟨64⟩ :: value :: toWord :: src :: ret :: R)
      (uniswapTransferDebitHashMemOf src mem) (UInt256.ofNat 3) rdata
      (cA, sstoreAccountMap ee.codeOwner σ (mapSlot src ⟨1⟩) debit) k' C' := by
  have hmask : UInt256.land src solcAddrMask = src :=
    solcAddrMask_clean hcanonSrc
  have hmaskLiteral :
      UInt256.land src (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) =
        src := by
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide]
    exact hmask
  have hbaseSize : (twoWordHashMem src ⟨1⟩ mem).size = 96 :=
    twoWordHashMem_size_96 src ⟨1⟩ hmem
  have hslot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((uniswapTransferDebitHashMemOf src mem).readWithPadding 0 64))) =
        mapSlot src ⟨1⟩ := by
    unfold uniswapTransferDebitHashMemOf
    rw [twoWordHashMem_read0_64 src ⟨1⟩ hbaseSize]
    unfold mapSlot
    exact mappingSlot_single src ⟨1⟩
  have rd7563 := evm_run h with [
    jumpdest, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup1, dup6, and]
  rw [hmaskLiteral] at rd7563
  have rd7567 := evm_run rd7563 with [push1 ⟨0⟩, swap1, dup2]
  have rd7568 := rd7567.mstore 0
    (wordAt0Mem src (twoWordHashMem src ⟨1⟩ mem))
    (UInt256.ofNat 3) (by decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd7572 := evm_run rd7568 with [push1 ⟨1⟩, push1 ⟨32⟩]
  have rd7573 := rd7572.mstore 0 (uniswapTransferDebitHashMemOf src mem)
    (UInt256.ofNat 3) (by decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd7577 := evm_run rd7573 with [push1 ⟨64⟩, dup1, dup3]
  have rd7578 := rd7577.keccak256 0 (mapSlot src ⟨1⟩) (UInt256.ofNat 3)
    (by decide) mem_cost hslot (by native_decide) (by evm_ov)
  have rd7581 := evm_run rd7578 with [swap4, swap1, swap4]
  obtain ⟨_, _, rd7582⟩ := rd7581.sstore hperm (by decide)
    (by simp only [List.length_cons]; omega)
  exact ⟨_, _, by simpa [uniswapTransferDebitHashMemOf] using rd7582⟩

-- LIBRARY CANDIDATE: Reasoning.Reach — pristine-memory specialization of
-- `RD.uniswapTransferInternalStoreDebitMem` for the common external `transfer` path.
set_option maxHeartbeats 4000000 in
theorem RD.uniswapTransferInternalStoreDebit {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {debit value toWord src ret : UInt256}
    {R : List UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨7551⟩
        (debit :: value :: toWord :: src :: ret :: R)
        (twoWordHashMem src ⟨1⟩ solcFreePtrMem) (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hperm : ee.perm = true)
    (hcanonSrc : src.toNat < EVM.addressModulus)
    (hov : R.length + 16 ≤ 1024) :
    ∃ k' C', RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨7582⟩
      (⟨0⟩ :: solcAddrMask :: ⟨64⟩ :: value :: toWord :: src :: ret :: R)
      (uniswapTransferDebitHashMem src) (UInt256.ofNat 3) rdata
      (cA, sstoreAccountMap ee.codeOwner σ (mapSlot src ⟨1⟩) debit) k' C' := by
  simpa [uniswapTransferDebitHashMem] using RD.uniswapTransferInternalStoreDebitMem
    (mem := solcFreePtrMem) h solcFreePtrMem_size hperm hcanonSrc hov

-- LIBRARY CANDIDATE: Reasoning.Memory — recipient-key overwrite of an arbitrary 96-byte
-- transfer-debit mapping scratch buffer.
noncomputable abbrev uniswapTransferToHashMemOf (src toWord : UInt256) (mem : ByteArray) :
    ByteArray :=
  wordAt0Mem toWord (uniswapTransferDebitHashMemOf src mem)

-- LIBRARY CANDIDATE: Reasoning.Memory — size preservation for recipient-key overwrite over an
-- arbitrary 96-byte transfer-debit mapping scratch buffer.
theorem uniswapTransferToHashMemOf_size (src toWord : UInt256) {mem : ByteArray}
    (hmem : mem.size = 96) :
    (uniswapTransferToHashMemOf src toWord mem).size = 96 := by
  unfold uniswapTransferToHashMemOf
  exact wordAt0Mem_size_96 toWord (uniswapTransferDebitHashMemOf_size src hmem)

noncomputable abbrev uniswapTransferToHashMem (src toWord : UInt256) : ByteArray :=
  uniswapTransferToHashMemOf src toWord solcFreePtrMem

theorem uniswapTransferToHashMem_size (src toWord : UInt256) :
    (uniswapTransferToHashMem src toWord).size = 96 := by
  exact uniswapTransferToHashMemOf_size src toWord solcFreePtrMem_size

-- LIBRARY CANDIDATE: Reasoning.Memory — one-word overwrite of an existing mapping-hash scratch
-- buffer where the base-slot word at `0x20` is preserved.
-- GENERALIZES Examples.UniswapV2Pair.Routines.uniswapTransferToHashMem_read0_64 —
-- parameterizes the pre-existing 96-byte scratch memory.
set_option maxHeartbeats 1000000 in
theorem uniswapTransferToHashMemOf_read0_64 (src toWord : UInt256) {mem : ByteArray}
    (hmem : mem.size = 96) :
    (uniswapTransferToHashMemOf src toWord mem).readWithPadding 0 64 =
      UInt256.toByteArray toWord ++ UInt256.toByteArray ⟨1⟩ := by
  unfold uniswapTransferToHashMemOf wordAt0Mem
  rw [readWithPadding_eq_extract' _ 0 64 (by norm_num) (by norm_num) (by
    rw [writeWord_size_of_96 _ _ 0 (by
      unfold uniswapTransferDebitHashMemOf
      exact twoWordHashMem_size_96 src ⟨1⟩ (twoWordHashMem_size_96 src ⟨1⟩ hmem))
      (by norm_num)]
    omega)]
  have hleft :
      ((UInt256.toByteArray toWord).write 0
        (uniswapTransferDebitHashMemOf src mem) 0 32).extract 0 32 =
        UInt256.toByteArray toWord := by
    rw [← readWithPadding_eq_extract _ 0 (by
      rw [writeWord_size_of_96 _ _ 0 (by
        unfold uniswapTransferDebitHashMemOf
        exact twoWordHashMem_size_96 src ⟨1⟩ (twoWordHashMem_size_96 src ⟨1⟩ hmem))
        (by norm_num)]
      omega)]
    rw [write32_read_back _ _ _ (by rw [toByteArray_size]) (by
      unfold uniswapTransferDebitHashMemOf
      rw [twoWordHashMem_size_96 src ⟨1⟩
        (twoWordHashMem_size_96 src ⟨1⟩ hmem)]
      omega)]
    apply ByteArray.ext
    rw [ByteArray.data_extract]
    exact Array.extract_eq_self_of_le (by
      change (UInt256.toByteArray toWord).size ≤ 32
      rw [toByteArray_size])
  have hright :
      ((UInt256.toByteArray toWord).write 0
        (uniswapTransferDebitHashMemOf src mem) 0 32).extract 32 64 =
        UInt256.toByteArray ⟨1⟩ := by
    rw [← readWithPadding_eq_extract _ 32 (by
      rw [writeWord_size_of_96 _ _ 0 (by
        unfold uniswapTransferDebitHashMemOf
        exact twoWordHashMem_size_96 src ⟨1⟩ (twoWordHashMem_size_96 src ⟨1⟩ hmem))
        (by norm_num)]
      omega)]
    rw [write32_read_above _ _ 0 32 (by rw [toByteArray_size]) (by
      unfold uniswapTransferDebitHashMemOf
      rw [twoWordHashMem_size_96 src ⟨1⟩
        (twoWordHashMem_size_96 src ⟨1⟩ hmem)]
      omega) (by omega) (by
      unfold uniswapTransferDebitHashMemOf
      rw [twoWordHashMem_size_96 src ⟨1⟩
        (twoWordHashMem_size_96 src ⟨1⟩ hmem)]
      omega)]
    unfold uniswapTransferDebitHashMemOf
    rw [twoWordHashMem_read32 src ⟨1⟩
      (twoWordHashMem_size_96 src ⟨1⟩ hmem)]
  rw [show ((UInt256.toByteArray toWord).write 0
        (uniswapTransferDebitHashMemOf src mem) 0 32).extract 0 64 =
      ((UInt256.toByteArray toWord).write 0
        (uniswapTransferDebitHashMemOf src mem) 0 32).extract 0 32 ++
      ((UInt256.toByteArray toWord).write 0
        (uniswapTransferDebitHashMemOf src mem) 0 32).extract 32 64 by
      rw [ByteArray.extract_append_extract]
      norm_num]
  rw [hleft, hright]

theorem uniswapTransferToHashMem_read0_64 (src toWord : UInt256) :
    (uniswapTransferToHashMem src toWord).readWithPadding 0 64 =
      UInt256.toByteArray toWord ++ UInt256.toByteArray ⟨1⟩ := by
  exact uniswapTransferToHashMemOf_read0_64 src toWord solcFreePtrMem_size

theorem uniswapTransferToHashMemOf_slot (src toWord : UInt256) {mem : ByteArray}
    (hmem : mem.size = 96) :
    UInt256.ofNat
        (fromByteArrayBigEndian (ffi.KEC ((uniswapTransferToHashMemOf src toWord mem).readWithPadding
          0 64))) =
      mapSlot toWord ⟨1⟩ := by
  rw [uniswapTransferToHashMemOf_read0_64 src toWord hmem]
  unfold mapSlot
  exact mappingSlot_single toWord ⟨1⟩

theorem uniswapTransferToHashMem_slot (src toWord : UInt256) :
    UInt256.ofNat
        (fromByteArrayBigEndian (ffi.KEC ((uniswapTransferToHashMem src toWord).readWithPadding
          0 64))) =
      mapSlot toWord ⟨1⟩ := by
  exact uniswapTransferToHashMemOf_slot src toWord solcFreePtrMem_size

-- GENERALIZES Examples.UniswapV2Pair.Routines.RD.uniswapTransferInternalToBalanceLoad —
-- parameterizes the pre-existing 96-byte scratch memory.
-- LIBRARY CANDIDATE: Reasoning.Reach — optimizer-on solc single-mapping load prefix that
-- reuses an existing mapping scratch buffer by overwriting only the key word at `0x00`.
set_option maxHeartbeats 2000000 in
theorem RD.uniswapTransferInternalToBalanceLoadMem {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {value toWord src ret : UInt256}
    {R : List UInt256} {mem rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨7582⟩
      (⟨0⟩ :: solcAddrMask :: ⟨64⟩ :: value :: toWord :: src :: ret :: R)
      (uniswapTransferDebitHashMemOf src mem) (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hmem : mem.size = 96)
    (hcanonTo : toWord.toNat < EVM.addressModulus)
    (hov : R.length + 16 ≤ 1024) :
    ∃ k' C', RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨8515⟩
      (value :: uniswapCodeOwnerStorageWord ee σ (mapSlot toWord ⟨1⟩) ::
        ⟨7604⟩ :: value :: toWord :: src :: ret :: R)
      (uniswapTransferToHashMemOf src toWord mem) (UInt256.ofNat 3) rdata (cA, σ) k' C' := by
  have hmask : UInt256.land toWord solcAddrMask = toWord :=
    solcAddrMask_clean hcanonTo
  have rd7585 := evm_run h with [swap1, dup5, and]
  rw [hmask] at rd7585
  have rd7586 := evm_run rd7585 with [dup2]
  have rd7587 := rd7586.mstore 0 (uniswapTransferToHashMemOf src toWord mem)
    (UInt256.ofNat 3) (by decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd7588 := rd7587.keccak256 0 (mapSlot toWord ⟨1⟩) (UInt256.ofNat 3)
    (by decide) mem_cost (uniswapTransferToHashMemOf_slot src toWord hmem) (by native_decide)
    (by evm_ov)
  obtain ⟨_, _, rd7589⟩ := rd7588.sload (by decide)
    (by simp only [List.length_cons]; omega)
  have rd7603 := evm_run rd7589 with [
    push2 ⟨7604⟩, swap1, dup3, push4 ⟨0xffffffff⟩, push2 ⟨8515⟩, and]
  exact ⟨_, _, by
    simpa [uniswapCodeOwnerStorageWord,
      show UInt256.land (⟨8515⟩ : UInt256) ⟨0xffffffff⟩ = ⟨8515⟩ from by decide]
      using rd7603.jump (by decide) (by jump_dest) (by evm_ov)⟩

-- LIBRARY CANDIDATE: Reasoning.Reach — pristine-memory specialization of
-- `RD.uniswapTransferInternalToBalanceLoadMem` for the common external `transfer` path.
set_option maxHeartbeats 2000000 in
theorem RD.uniswapTransferInternalToBalanceLoad {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {value toWord src ret : UInt256}
    {R : List UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨7582⟩
      (⟨0⟩ :: solcAddrMask :: ⟨64⟩ :: value :: toWord :: src :: ret :: R)
      (uniswapTransferDebitHashMem src) (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hcanonTo : toWord.toNat < EVM.addressModulus)
    (hov : R.length + 16 ≤ 1024) :
    ∃ k' C', RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨8515⟩
      (value :: uniswapCodeOwnerStorageWord ee σ (mapSlot toWord ⟨1⟩) ::
        ⟨7604⟩ :: value :: toWord :: src :: ret :: R)
      (uniswapTransferToHashMem src toWord) (UInt256.ofNat 3) rdata (cA, σ) k' C' := by
  simpa [uniswapTransferDebitHashMem, uniswapTransferToHashMem] using
    RD.uniswapTransferInternalToBalanceLoadMem
      (mem := solcFreePtrMem) h solcFreePtrMem_size hcanonTo hov

-- GENERALIZES Examples.UniswapV2Pair.Routines.RD.uniswapTransferInternalAfterCreditCalc —
-- parameterizes the pre-existing 96-byte scratch memory.
-- LIBRARY CANDIDATE: Reasoning.Reach — mapping-load plus checked-add success prefix for
-- optimizer-on ERC20-like transfer routines, parameterized by base slot, routine PCs, and initial
-- scratch memory.
set_option maxHeartbeats 2000000 in
theorem RD.uniswapTransferInternalAfterCreditCalcMem {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {value toWord src ret : UInt256}
    {R : List UInt256} {mem rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨7582⟩
      (⟨0⟩ :: solcAddrMask :: ⟨64⟩ :: value :: toWord :: src :: ret :: R)
      (uniswapTransferDebitHashMemOf src mem) (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hmem : mem.size = 96)
    (hcanonTo : toWord.toNat < EVM.addressModulus)
    (hfit : (uniswapCodeOwnerStorageWord ee σ (mapSlot toWord ⟨1⟩)).toNat +
      value.toNat < UInt256.size)
    (hov : R.length + 16 ≤ 1024) :
    ∃ k' C', RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨7604⟩
      ((uniswapCodeOwnerStorageWord ee σ (mapSlot toWord ⟨1⟩) + value) ::
        value :: toWord :: src :: ret :: R)
      (uniswapTransferToHashMemOf src toWord mem) (UInt256.ofNat 3) rdata (cA, σ) k' C' := by
  obtain ⟨_, _, rd8515⟩ := RD.uniswapTransferInternalToBalanceLoadMem
    (value := value) (toWord := toWord) (src := src) (ret := ret) (R := R)
    h hmem hcanonTo hov
  obtain ⟨_, _, rd7604⟩ := RD.uniswapSafeMathAddSuccess
    (a := uniswapCodeOwnerStorageWord ee σ (mapSlot toWord ⟨1⟩)) (b := value)
    (ret := ⟨7604⟩) (R := value :: toWord :: src :: ret :: R)
    rd8515 hfit (by jump_dest) (by simp only [List.length_cons]; omega)
  exact ⟨_, _, rd7604⟩

-- LIBRARY CANDIDATE: Reasoning.Reach — pristine-memory specialization of
-- `RD.uniswapTransferInternalAfterCreditCalcMem` for the common external `transfer` path.
set_option maxHeartbeats 2000000 in
theorem RD.uniswapTransferInternalAfterCreditCalc {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {value toWord src ret : UInt256}
    {R : List UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨7582⟩
      (⟨0⟩ :: solcAddrMask :: ⟨64⟩ :: value :: toWord :: src :: ret :: R)
      (uniswapTransferDebitHashMem src) (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hcanonTo : toWord.toNat < EVM.addressModulus)
    (hfit : (uniswapCodeOwnerStorageWord ee σ (mapSlot toWord ⟨1⟩)).toNat +
      value.toNat < UInt256.size)
    (hov : R.length + 16 ≤ 1024) :
    ∃ k' C', RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨7604⟩
      ((uniswapCodeOwnerStorageWord ee σ (mapSlot toWord ⟨1⟩) + value) ::
        value :: toWord :: src :: ret :: R)
      (uniswapTransferToHashMem src toWord) (UInt256.ofNat 3) rdata (cA, σ) k' C' := by
  simpa [uniswapTransferDebitHashMem, uniswapTransferToHashMem] using
    RD.uniswapTransferInternalAfterCreditCalcMem
      (mem := solcFreePtrMem) h solcFreePtrMem_size hcanonTo hfit hov

noncomputable abbrev uniswapTransferCreditHashMem (src toWord : UInt256) : ByteArray :=
  twoWordHashMem toWord ⟨1⟩ (uniswapTransferToHashMem src toWord)

theorem uniswapTransferCreditHashMem_size (src toWord : UInt256) :
    (uniswapTransferCreditHashMem src toWord).size = 96 := by
  unfold uniswapTransferCreditHashMem
  exact twoWordHashMem_size_96 toWord ⟨1⟩ (uniswapTransferToHashMem_size src toWord)

theorem uniswapTransferCreditHashMem_slot (src toWord : UInt256) :
    UInt256.ofNat
        (fromByteArrayBigEndian (ffi.KEC ((uniswapTransferCreditHashMem src toWord).readWithPadding
          0 64))) =
      mapSlot toWord ⟨1⟩ := by
  unfold uniswapTransferCreditHashMem
  rw [twoWordHashMem_read0_64 toWord ⟨1⟩ (uniswapTransferToHashMem_size src toWord)]
  unfold mapSlot
  exact mappingSlot_single toWord ⟨1⟩

-- LIBRARY CANDIDATE: Reasoning.Reach — optimizer-on solc single-mapping store suffix that
-- rewrites an address-keyed mapping slot in scratch memory and performs `SSTORE`, preserving the
-- stack tail needed by an event-log suffix.
set_option maxHeartbeats 4000000 in
theorem RD.uniswapTransferInternalStoreCredit {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {newTo value toWord src ret : UInt256}
    {R : List UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨7604⟩
      (newTo :: value :: toWord :: src :: ret :: R)
      (uniswapTransferToHashMem src toWord) (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hperm : ee.perm = true)
    (hcanonTo : toWord.toNat < EVM.addressModulus)
    (hov : R.length + 16 ≤ 1024) :
    ∃ k' C', RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨7638⟩
      (⟨64⟩ :: toWord :: solcAddrMask :: ⟨32⟩ :: value :: toWord :: src :: ret :: R)
      (uniswapTransferCreditHashMem src toWord) (UInt256.ofNat 3) rdata
      (cA, sstoreAccountMap ee.codeOwner σ (mapSlot toWord ⟨1⟩) newTo) k' C' := by
  have hmask : UInt256.land toWord solcAddrMask = toWord :=
    solcAddrMask_clean hcanonTo
  have hmaskLiteral :
      UInt256.land toWord (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) =
        toWord := by
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide]
    exact hmask
  have rd7616 := evm_run h with [
    jumpdest, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup1, dup5, and]
  rw [hmaskLiteral] at rd7616
  have rd7620 := evm_run rd7616 with [push1 ⟨0⟩, dup2, dup2]
  have rd7621 := rd7620.mstore 0 (wordAt0Mem toWord (uniswapTransferToHashMem src toWord))
    (UInt256.ofNat 3) (by decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd7627 := evm_run rd7621 with [push1 ⟨1⟩, push1 ⟨32⟩, swap1, dup2]
  have rd7628 := rd7627.mstore 0 (uniswapTransferCreditHashMem src toWord)
    (UInt256.ofNat 3) (by decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd7633 := evm_run rd7628 with [push1 ⟨64⟩, swap2, dup3, swap1]
  have rd7634 := rd7633.keccak256 0 (mapSlot toWord ⟨1⟩) (UInt256.ofNat 3)
    (by decide) mem_cost (uniswapTransferCreditHashMem_slot src toWord) (by native_decide)
    (by evm_ov)
  have rd7637 := evm_run rd7634 with [swap5, swap1, swap5]
  obtain ⟨_, _, rd7638⟩ := rd7637.sstore hperm (by decide)
    (by simp only [List.length_cons]; omega)
  exact ⟨_, _, by simpa [uniswapTransferCreditHashMem] using rd7638⟩

def uniswapTransferTopic : UInt256 :=
  ⟨0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef⟩

-- LIBRARY CANDIDATE: Reasoning.Memory — scratch-memory free-pointer preservation for repeated
-- mapping-hash writes followed by an event data word at `0x80`.
theorem uniswapTransferDebitHashMem_read64 (src : UInt256) :
    (uniswapTransferDebitHashMem src).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold uniswapTransferDebitHashMem
  exact twoWordHashMem_read64 src ⟨1⟩
    (twoWordHashMem_size_96 src ⟨1⟩ solcFreePtrMem_size)
    (twoWordHashMem_read64 src ⟨1⟩ solcFreePtrMem_size solcFreePtrMem_read64)

theorem uniswapTransferToHashMem_read64 (src toWord : UInt256) :
    (uniswapTransferToHashMem src toWord).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold uniswapTransferToHashMem uniswapTransferToHashMemOf wordAt0Mem
  rw [write32_read_above _ _ 0 64 (by rw [toByteArray_size])
      (by rw [uniswapTransferDebitHashMem_size]; omega) (by omega)
      (by rw [uniswapTransferDebitHashMem_size])]
  exact uniswapTransferDebitHashMem_read64 src

theorem uniswapTransferCreditHashMem_read64 (src toWord : UInt256) :
    (uniswapTransferCreditHashMem src toWord).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold uniswapTransferCreditHashMem
  exact twoWordHashMem_read64 toWord ⟨1⟩ (uniswapTransferToHashMem_size src toWord)
    (uniswapTransferToHashMem_read64 src toWord)

theorem uniswapTransferCreditHashMem_mload64 (src toWord : UInt256) :
    (if (⟨64⟩ : UInt256).toNat ≥ (uniswapTransferCreditHashMem src toWord).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 3 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((uniswapTransferCreditHashMem src toWord).readWithPadding
          (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ :=
  mloadFreePtrValue (by rw [uniswapTransferCreditHashMem_size]; decide) (by decide)
    (uniswapTransferCreditHashMem_read64 src toWord)

noncomputable def uniswapTransferLogMem (src toWord value : UInt256) : ByteArray :=
  (UInt256.toByteArray value).write 0 (uniswapTransferCreditHashMem src toWord) 128 32

theorem uniswapTransferLogMem_size (src toWord value : UInt256) :
    (uniswapTransferLogMem src toWord value).size = 160 := by
  unfold uniswapTransferLogMem
  rw [toByteArray_write_eq _ _ _ (by rw [uniswapTransferCreditHashMem_size]; omega)
      (by rw [uniswapTransferCreditHashMem_size]; exact lt_usize _ (by norm_num)),
    ByteArray.size_append, ByteArray.size_append, uniswapTransferCreditHashMem_size,
    ByteArray_zeroes_size,
    show (USize.ofNat (128 - 96)).toNat = 32 from by
      exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num)),
    toByteArray_size]

theorem uniswapTransferLogMem_read64 (src toWord value : UInt256) :
    (uniswapTransferLogMem src toWord value).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold uniswapTransferLogMem
  rw [toByteArray_write_eq _ _ _ (by rw [uniswapTransferCreditHashMem_size]; omega)
      (by rw [uniswapTransferCreditHashMem_size]; exact lt_usize _ (by norm_num))]
  rw [readWithPadding_eq_extract _ 64 (by
      rw [ByteArray.size_append, ByteArray.size_append, uniswapTransferCreditHashMem_size,
        ByteArray_zeroes_size,
        show (USize.ofNat (128 - 96)).toNat = 32 from by
          exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num)),
        toByteArray_size]
      norm_num)]
  rw [extract_append_left _ _ _ _ (by
      rw [ByteArray.size_append, uniswapTransferCreditHashMem_size, ByteArray_zeroes_size,
        show (USize.ofNat (128 - 96)).toNat = 32 from by
          exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num))]
      omega)]
  rw [extract_append_left _ _ _ _ (by rw [uniswapTransferCreditHashMem_size]),
    ← readWithPadding_eq_extract _ 64 (by rw [uniswapTransferCreditHashMem_size]),
    uniswapTransferCreditHashMem_read64]

theorem uniswapTransferLogMem_mload64 (src toWord value : UInt256) :
    (if (⟨64⟩ : UInt256).toNat ≥ (uniswapTransferLogMem src toWord value).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 5 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((uniswapTransferLogMem src toWord value).readWithPadding
          (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ :=
  mloadFreePtrValue (by rw [uniswapTransferLogMem_size]; decide) (by decide)
    (uniswapTransferLogMem_read64 src toWord value)

theorem uniswapTransferLogMem_read128 (src toWord value : UInt256) :
    (uniswapTransferLogMem src toWord value).readWithPadding 128 32 =
      UInt256.toByteArray value := by
  unfold uniswapTransferLogMem
  rw [toByteArray_write_eq _ _ _ (by rw [uniswapTransferCreditHashMem_size]; omega)
      (by rw [uniswapTransferCreditHashMem_size]; exact lt_usize _ (by norm_num))]
  rw [readWithPadding_eq_extract _ 128 (by
      rw [ByteArray.size_append, ByteArray.size_append, uniswapTransferCreditHashMem_size,
        ByteArray_zeroes_size,
        show (USize.ofNat (128 - 96)).toNat = 32 from by
          exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num)),
        toByteArray_size])]
  rw [extract_append_right_window
      (uniswapTransferCreditHashMem src toWord ++
        ffi.ByteArray.zeroes
          (USize.ofNat (128 - (uniswapTransferCreditHashMem src toWord).size)))
      (UInt256.toByteArray value) 128 160 (by
        rw [ByteArray.size_append, uniswapTransferCreditHashMem_size, ByteArray_zeroes_size,
          show (USize.ofNat (128 - 96)).toNat = 32 from by
            exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num))])]
  rw [ByteArray.size_append, uniswapTransferCreditHashMem_size, ByteArray_zeroes_size,
    show (USize.ofNat (128 - 96)).toNat = 32 from by
      exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num))]
  norm_num
  apply ByteArray.ext
  rw [ByteArray.data_extract]
  exact Array.extract_eq_self_of_le (by
    change (UInt256.toByteArray value).size ≤ 32
    rw [toByteArray_size])

noncomputable def uniswapTransferReturnMem
    (src toWord logValue retValue : UInt256) : ByteArray :=
  (UInt256.toByteArray retValue).write 0
    (uniswapTransferLogMem src toWord logValue) 128 32

theorem uniswapTransferReturnMem_size (src toWord logValue retValue : UInt256) :
    (uniswapTransferReturnMem src toWord logValue retValue).size = 160 := by
  unfold uniswapTransferReturnMem
  rw [write32_eq _ _ _ (by rw [toByteArray_size])
      (by rw [uniswapTransferLogMem_size]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract, uniswapTransferLogMem_size,
    toByteArray_size]
  omega

theorem uniswapTransferReturnMem_read64 (src toWord logValue retValue : UInt256) :
    (uniswapTransferReturnMem src toWord logValue retValue).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold uniswapTransferReturnMem
  rw [write32_read_below _ _ 128 64 (by rw [toByteArray_size])
      (by rw [uniswapTransferLogMem_size]; omega) (by omega),
    uniswapTransferLogMem_read64]

theorem uniswapTransferReturnMem_mload64 (src toWord logValue retValue : UInt256) :
    (if (⟨64⟩ : UInt256).toNat ≥
          (uniswapTransferReturnMem src toWord logValue retValue).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 5 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((uniswapTransferReturnMem src toWord logValue retValue).readWithPadding
          (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ :=
  mloadFreePtrValue (by rw [uniswapTransferReturnMem_size]; decide) (by decide)
    (uniswapTransferReturnMem_read64 src toWord logValue retValue)

theorem uniswapTransferReturnMem_read128 (src toWord logValue retValue : UInt256) :
    (uniswapTransferReturnMem src toWord logValue retValue).readWithPadding 128 32 =
      UInt256.toByteArray retValue := by
  unfold uniswapTransferReturnMem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size])
      (by rw [uniswapTransferLogMem_size]; omega)]
  apply ByteArray.ext
  rw [ByteArray.data_extract]
  exact Array.extract_eq_self_of_le (by
    change (UInt256.toByteArray retValue).size ≤ 32
    rw [toByteArray_size])

-- LIBRARY CANDIDATE: Reasoning.Reach — optimizer-on ERC20-style `Transfer` event suffix for a
-- shared internal transfer routine, parameterized by source/recipient/value and dynamic return pc.
set_option maxHeartbeats 4000000 in
theorem RD.uniswapTransferInternalEmitAndJump {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {value toWord src ret : UInt256}
    {R : List UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨7638⟩
      (⟨64⟩ :: toWord :: solcAddrMask :: ⟨32⟩ :: value :: toWord :: src :: ret :: R)
      (uniswapTransferCreditHashMem src toWord) (UInt256.ofNat 3) rdata acc k C)
    (hperm : ee.perm = true)
    (hcanonSrc : src.toNat < EVM.addressModulus)
    (hret : (D_J UniswapV2Pair.uniswapV2PairBytecode 0).contains ret = true)
    (hov : R.length + 16 ≤ 1024) :
    ∃ k' C', RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ret R
      (uniswapTransferLogMem src toWord value) (UInt256.ofNat 5) rdata acc k' C' := by
  have hmask : UInt256.land src solcAddrMask = src :=
    solcAddrMask_clean hcanonSrc
  have rd7640 := evm_run h with [
    dup1,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost
      (uniswapTransferCreditHashMem_mload64 src toWord)
      (by decide) (by evm_ov)]
  have rd7642 := evm_run rd7640 with [dup6, dup2]
  have rd7643 := rd7642.mstore 6 (uniswapTransferLogMem src toWord value)
    (UInt256.ofNat 5) (by decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd7645 := evm_run rd7643 with [
    swap1,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) (by decide)
      mem_cost
      (uniswapTransferLogMem_mload64 src toWord value)
      (by decide) (by evm_ov),
    swap2, swap4, swap3, dup8, and]
  rw [hmask] at rd7645
  have rd7651 := evm_run rd7645 with [swap3]
  have rd7684₀ := rd7651.pushConst uniswapTransferTopic (width := 32) (op := .PUSH32)
    (by decide) (by decide) (by evm_ov)
  have rd7691 := evm_run rd7684₀ with [swap3, swap2, dup3, swap1, sub, add, swap1]
  have rd7692 := rd7691.log3 0 (UInt256.ofNat 5) (by decide) hperm mem_cost
    (by decide) (by simp only [List.length_cons]; omega)
  have rd7695 := evm_run rd7692 with [pop, pop, pop]
  exact ⟨_, _, rd7695.jump (by decide) hret (by evm_ov)⟩

-- LIBRARY CANDIDATE: Reasoning.Reach — small solc continuation that discards two routine
-- arguments, pushes boolean true, and jumps to a dynamic return wrapper.
set_option maxHeartbeats 1000000 in
theorem RD.uniswapInternalTransferReturnTrue {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {discard a b ret : UInt256}
    {R : List UInt256} {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨2907⟩
      (discard :: a :: b :: ret :: R) mem aw rdata acc k C)
    (hret : (D_J UniswapV2Pair.uniswapV2PairBytecode 0).contains ret = true)
    (hov : R.length + 5 ≤ 1024) :
    ∃ k' C', RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ret
      (⟨1⟩ :: R) mem aw rdata acc k' C' := by
  exact ⟨_, _, evm_run h with [
    jumpdest, pop, push1 ⟨1⟩, jumpdest, swap3, swap2, pop, pop, jump hret]⟩

/-! ## Shared internal `_approve` routine prefix -/

def uniswapApprovalTopic : UInt256 :=
  ⟨0x8c5be1e5ebec7d5bd14f71427d1e84f3dd0314c0f7b2291e5b200ac8c7c3b925⟩

-- LIBRARY CANDIDATE: Reasoning.Memory — one-word write-at-0x80 return/log memory over a
-- 96-byte scratch memory that preserves the solc free pointer at `0x40`.
noncomputable abbrev uniswapApproveHashMem (owner spender : UInt256) : ByteArray :=
  twoWordHashMem spender (mapSlot owner ⟨2⟩) (twoWordHashMem owner ⟨2⟩ solcFreePtrMem)

noncomputable def uniswapApproveLogMem (owner spender value : UInt256) : ByteArray :=
  (UInt256.toByteArray value).write 0 (uniswapApproveHashMem owner spender) 128 32

noncomputable def uniswapApproveReturnMem
    (owner spender logValue retValue : UInt256) : ByteArray :=
  (UInt256.toByteArray retValue).write 0
    (uniswapApproveLogMem owner spender logValue) 128 32

theorem uniswapApproveHashMem_size (owner spender : UInt256) :
    (uniswapApproveHashMem owner spender).size = 96 := by
  unfold uniswapApproveHashMem
  exact twoWordHashMem_size_96 spender (mapSlot owner ⟨2⟩)
    (twoWordHashMem_size_96 owner ⟨2⟩ solcFreePtrMem_size)

theorem uniswapApproveHashMem_read64 (owner spender : UInt256) :
    (uniswapApproveHashMem owner spender).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold uniswapApproveHashMem
  exact twoWordHashMem_read64 spender (mapSlot owner ⟨2⟩)
    (twoWordHashMem_size_96 owner ⟨2⟩ solcFreePtrMem_size)
    (twoWordHashMem_read64 owner ⟨2⟩ solcFreePtrMem_size solcFreePtrMem_read64)

theorem uniswapApproveHashMem_mload64 (owner spender : UInt256) :
    (if (⟨64⟩ : UInt256).toNat ≥ (uniswapApproveHashMem owner spender).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 3 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((uniswapApproveHashMem owner spender).readWithPadding
          (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ :=
  mloadFreePtrValue (by rw [uniswapApproveHashMem_size]; decide) (by decide)
    (uniswapApproveHashMem_read64 owner spender)

-- LIBRARY CANDIDATE: Reasoning.Reach — optimizer-on solc nested-mapping load plus
-- `uint256.max` branch, parameterized by base slot, branch PCs, and stack layout.
set_option maxHeartbeats 1000000 in
theorem RD.uniswapTransferFromAllowanceMaxBranch {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {value toWord src ret : UInt256}
    {R : List UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨2938⟩
      (value :: toWord :: src :: ret :: R)
      solcFreePtrMem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hcanonSrc : src.toNat < EVM.addressModulus)
    (hmax :
      (uniswapCodeOwnerStorageWord ee σ
        (mapSlot (uniswapSourceWord ee) (mapSlot src ⟨2⟩))).toNat =
        UInt256.size - 1)
    (hov : R.length + 16 ≤ 1024) :
    ∃ k' C', RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨3071⟩
      (⟨0⟩ :: value :: toWord :: src :: ret :: R)
      (uniswapApproveHashMem src (uniswapSourceWord ee))
      (UInt256.ofNat 3) rdata (cA, σ) k' C' := by
  let allowanceSlot := mapSlot (uniswapSourceWord ee) (mapSlot src ⟨2⟩)
  let allowanceWord := uniswapCodeOwnerStorageWord ee σ allowanceSlot
  have hmask : UInt256.land src solcAddrMask = src :=
    solcAddrMask_clean hcanonSrc
  have hmaskLiteral :
      UInt256.land src (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) =
        src := by
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide]
    exact hmask
  have hinner :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((twoWordHashMem src ⟨2⟩ solcFreePtrMem).readWithPadding 0 64))) =
        mapSlot src ⟨2⟩ := by
    rw [twoWordHashMem_read0_64 src ⟨2⟩ solcFreePtrMem_size]
    unfold mapSlot
    exact mappingSlot_single src ⟨2⟩
  have houter :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((uniswapApproveHashMem src (uniswapSourceWord ee)).readWithPadding 0 64))) =
        allowanceSlot := by
    unfold allowanceSlot uniswapApproveHashMem
    rw [twoWordHashMem_read0_64 (uniswapSourceWord ee) (mapSlot src ⟨2⟩)
      (twoWordHashMem_size_96 src ⟨2⟩ solcFreePtrMem_size)]
    unfold mapSlot
    exact mappingSlot_single (uniswapSourceWord ee) (mapSlot src ⟨2⟩)
  have hlnot0 : (UInt256.lnot (⟨0⟩ : UInt256)).toNat = UInt256.size - 1 := by
    unfold UInt256.lnot
    decide
  have hmax' : allowanceWord.toNat = UInt256.size - 1 := by
    simpa [allowanceWord, allowanceSlot] using hmax
  have hallowEq : allowanceWord = UInt256.lnot (⟨0⟩ : UInt256) := by
    apply u256_inj
    rw [hmax', hlnot0]
  have heq : UInt256.eq (UInt256.lnot (⟨0⟩ : UInt256)) allowanceWord = ⟨1⟩ := by
    rw [hallowEq]
    exact u256_eq_refl _
  have rd2949 := evm_run h with [
    jumpdest, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup4, and]
  rw [hmaskLiteral] at rd2949
  have rd2953 := evm_run rd2949 with [push1 ⟨0⟩, swap1, dup2]
  have rd2954 := rd2953.mstore 0 (wordAt0Mem src solcFreePtrMem)
    (UInt256.ofNat 3) (by decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd2961 := evm_run rd2954 with [push1 ⟨2⟩, push1 ⟨32⟩, swap1, dup2]
  have rd2962 := rd2961.mstore 0 (twoWordHashMem src ⟨2⟩ solcFreePtrMem)
    (UInt256.ofNat 3) (by decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd2966 := evm_run rd2962 with [push1 ⟨64⟩, dup1, dup4]
  have rd2967 := rd2966.keccak256 0 (mapSlot src ⟨2⟩) (UInt256.ofNat 3)
    (by decide) mem_cost hinner (by native_decide) (by evm_ov)
  have rd2969 := evm_run rd2967 with [caller, dup5]
  have rd2970 := rd2969.mstore 0
    (wordAt0Mem (uniswapSourceWord ee) (twoWordHashMem src ⟨2⟩ solcFreePtrMem))
    (UInt256.ofNat 3) (by decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd2972 := evm_run rd2970 with [swap1, swap2]
  have rd2973 := rd2972.mstore 0 (uniswapApproveHashMem src (uniswapSourceWord ee))
    (UInt256.ofNat 3) (by decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd2974 := evm_run rd2973 with [dup2]
  have rd2975₀ := rd2974.keccak256 0 allowanceSlot (UInt256.ofNat 3)
    (by decide) mem_cost houter (by native_decide) (by evm_ov)
  obtain ⟨k2975, C2975, rd2975₁⟩ := rd2975₀.sload (by decide)
    (by simp only [List.length_cons]; omega)
  have rd2975 : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨2975⟩
      (allowanceWord :: ⟨0⟩ :: value :: toWord :: src :: ret :: R)
      (uniswapApproveHashMem src (uniswapSourceWord ee))
      (UInt256.ofNat 3) rdata (cA, σ) k2975 C2975 := by
    simpa [allowanceWord, allowanceSlot, uniswapCodeOwnerStorageWord] using rd2975₁
  have rd2979 := evm_run rd2975 with [push1 ⟨0⟩, not, eq]
  rw [heq] at rd2979
  have rd2983 := evm_run rd2979 with [
    push2 ⟨3071⟩, jumpiT one_ne_zero_uint (by jump_dest)]
  exact ⟨_, _, by simpa using rd2983⟩

-- LIBRARY CANDIDATE: Reasoning.Reach — optimizer-on solc internal-call setup that pushes a
-- static continuation, duplicates three arguments, and jumps to a shared internal routine.
set_option maxHeartbeats 1000000 in
theorem RD.uniswapTransferFromMaxAllowanceToInternal {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {value toWord src ret discard : UInt256}
    {R : List UInt256} {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨3071⟩
      (discard :: value :: toWord :: src :: ret :: R) mem aw rdata acc k C)
    (hov : R.length + 10 ≤ 1024) :
    ∃ k' C', RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨7510⟩
      (value :: toWord :: src :: ⟨3082⟩ :: discard :: value :: toWord :: src :: ret :: R)
      mem aw rdata acc k' C' := by
  have rd7510 := evm_run h with [
    jumpdest, push2 ⟨3082⟩, dup5, dup5, dup5, push2 ⟨7510⟩]
  exact ⟨_, _, rd7510.jump (by decide) (by jump_dest) (by evm_ov)⟩

theorem uniswapApproveLogMem_size (owner spender value : UInt256) :
    (uniswapApproveLogMem owner spender value).size = 160 := by
  unfold uniswapApproveLogMem
  rw [toByteArray_write_eq _ _ _ (by rw [uniswapApproveHashMem_size]; omega)
      (by rw [uniswapApproveHashMem_size]; exact lt_usize _ (by norm_num)),
    ByteArray.size_append, ByteArray.size_append, uniswapApproveHashMem_size,
    ByteArray_zeroes_size,
    show (USize.ofNat (128 - 96)).toNat = 32 from by
      exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num)),
    toByteArray_size]

theorem uniswapApproveLogMem_read64 (owner spender value : UInt256) :
    (uniswapApproveLogMem owner spender value).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold uniswapApproveLogMem
  rw [toByteArray_write_eq _ _ _ (by rw [uniswapApproveHashMem_size]; omega)
      (by rw [uniswapApproveHashMem_size]; exact lt_usize _ (by norm_num))]
  rw [readWithPadding_eq_extract _ 64 (by
      rw [ByteArray.size_append, ByteArray.size_append, uniswapApproveHashMem_size,
        ByteArray_zeroes_size,
        show (USize.ofNat (128 - 96)).toNat = 32 from by
          exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num)),
        toByteArray_size]
      norm_num)]
  rw [extract_append_left _ _ _ _ (by
      rw [ByteArray.size_append, uniswapApproveHashMem_size, ByteArray_zeroes_size,
        show (USize.ofNat (128 - 96)).toNat = 32 from by
          exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num))]
      omega)]
  rw [extract_append_left _ _ _ _ (by rw [uniswapApproveHashMem_size]),
    ← readWithPadding_eq_extract _ 64 (by rw [uniswapApproveHashMem_size]),
    uniswapApproveHashMem_read64]

theorem uniswapApproveLogMem_mload64 (owner spender value : UInt256) :
    (if (⟨64⟩ : UInt256).toNat ≥ (uniswapApproveLogMem owner spender value).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 5 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((uniswapApproveLogMem owner spender value).readWithPadding
          (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ :=
  mloadFreePtrValue (by rw [uniswapApproveLogMem_size]; decide) (by decide)
    (uniswapApproveLogMem_read64 owner spender value)

theorem uniswapApproveLogMem_read128 (owner spender value : UInt256) :
    (uniswapApproveLogMem owner spender value).readWithPadding 128 32 =
      UInt256.toByteArray value := by
  unfold uniswapApproveLogMem
  rw [toByteArray_write_eq _ _ _ (by rw [uniswapApproveHashMem_size]; omega)
      (by rw [uniswapApproveHashMem_size]; exact lt_usize _ (by norm_num))]
  rw [readWithPadding_eq_extract _ 128 (by
      rw [ByteArray.size_append, ByteArray.size_append, uniswapApproveHashMem_size,
        ByteArray_zeroes_size,
        show (USize.ofNat (128 - 96)).toNat = 32 from by
          exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num)),
        toByteArray_size])]
  rw [extract_append_right_window
      (uniswapApproveHashMem owner spender ++
        ffi.ByteArray.zeroes
          (USize.ofNat (128 - (uniswapApproveHashMem owner spender).size)))
      (UInt256.toByteArray value) 128 160 (by
        rw [ByteArray.size_append, uniswapApproveHashMem_size, ByteArray_zeroes_size,
          show (USize.ofNat (128 - 96)).toNat = 32 from by
            exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num))])]
  rw [ByteArray.size_append, uniswapApproveHashMem_size, ByteArray_zeroes_size,
    show (USize.ofNat (128 - 96)).toNat = 32 from by
      exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num))]
  norm_num
  apply ByteArray.ext
  rw [ByteArray.data_extract]
  exact Array.extract_eq_self_of_le (by
    change (UInt256.toByteArray value).size ≤ 32
    rw [toByteArray_size])

theorem uniswapApproveReturnMem_size (owner spender logValue retValue : UInt256) :
    (uniswapApproveReturnMem owner spender logValue retValue).size = 160 := by
  unfold uniswapApproveReturnMem
  rw [write32_eq _ _ _ (by rw [toByteArray_size])
      (by rw [uniswapApproveLogMem_size]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract, uniswapApproveLogMem_size,
    toByteArray_size]
  omega

theorem uniswapApproveReturnMem_read64 (owner spender logValue retValue : UInt256) :
    (uniswapApproveReturnMem owner spender logValue retValue).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold uniswapApproveReturnMem
  rw [write32_read_below _ _ 128 64 (by rw [toByteArray_size])
      (by rw [uniswapApproveLogMem_size]; omega) (by omega),
    uniswapApproveLogMem_read64]

theorem uniswapApproveReturnMem_mload64 (owner spender logValue retValue : UInt256) :
    (if (⟨64⟩ : UInt256).toNat ≥
          (uniswapApproveReturnMem owner spender logValue retValue).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 5 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((uniswapApproveReturnMem owner spender logValue retValue).readWithPadding
          (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ :=
  mloadFreePtrValue (by rw [uniswapApproveReturnMem_size]; decide) (by decide)
    (uniswapApproveReturnMem_read64 owner spender logValue retValue)

theorem uniswapApproveReturnMem_read128 (owner spender logValue retValue : UInt256) :
    (uniswapApproveReturnMem owner spender logValue retValue).readWithPadding 128 32 =
      UInt256.toByteArray retValue := by
  unfold uniswapApproveReturnMem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size])
      (by rw [uniswapApproveLogMem_size]; omega)]
  apply ByteArray.ext
  rw [ByteArray.data_extract]
  exact Array.extract_eq_self_of_le (by
    change (UInt256.toByteArray retValue).size ≤ 32
    rw [toByteArray_size])

-- LIBRARY CANDIDATE: Reasoning.Reach — optimizer-on solc nested-mapping store prefix that masks
-- an address key, writes `key || baseSlot` into scratch memory, and hashes it.
set_option maxHeartbeats 1000000 in
theorem RD.uniswapApproveInternalInnerHash {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {value spender owner ret : UInt256} {R : List UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨7412⟩
        (value :: spender :: owner :: ret :: R)
        solcFreePtrMem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hcanonOwner : owner.toNat < EVM.addressModulus)
    (hov : R.length + 13 ≤ 1024) :
    ∃ k' C', RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨7441⟩
      (mapSlot owner ⟨2⟩ :: ⟨64⟩ :: ⟨32⟩ :: ⟨0⟩ :: owner :: solcAddrMask :: value ::
        spender :: owner :: ret :: R)
      (twoWordHashMem owner ⟨2⟩ solcFreePtrMem)
      (UInt256.ofNat 3) rdata (cA, σ) k' C' := by
  have hmask :
      UInt256.land (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) owner =
        owner := by
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide]
    exact solcAddrMask_clean_left hcanonOwner
  have hslot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((twoWordHashMem owner ⟨2⟩ solcFreePtrMem).readWithPadding 0 64))) =
        mapSlot owner ⟨2⟩ := by
    rw [twoWordHashMem_read0_64 owner ⟨2⟩ solcFreePtrMem_size]
    unfold mapSlot
    exact mappingSlot_single owner ⟨2⟩
  have rd7421 := evm_run h with [
    jumpdest, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, dup1, dup5, and]
  rw [u256_land_comm owner (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩),
    hmask] at rd7421
  have rd7424 := evm_run rd7421 with [push1 ⟨0⟩, dup2, dup2]
  have rd7429 := rd7424.mstore 0 (wordAt0Mem owner solcFreePtrMem) (UInt256.ofNat 3)
    (by decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd7435 := evm_run rd7429 with [push1 ⟨2⟩, push1 ⟨32⟩, swap1, dup2]
  have rd7436 := rd7435.mstore 0 (twoWordHashMem owner ⟨2⟩ solcFreePtrMem)
    (UInt256.ofNat 3) (by decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd7440 := evm_run rd7436 with [push1 ⟨64⟩, dup1, dup4]
  exact ⟨_, _, by
    simpa using rd7440.keccak256 0 (mapSlot owner ⟨2⟩) (UInt256.ofNat 3)
      (by decide) mem_cost hslot (by native_decide) (by evm_ov)⟩

-- LIBRARY CANDIDATE: Reasoning.Reach — optimizer-on solc nested-mapping store suffix from
-- the inner hash through the final storage slot hash and `SSTORE`.
set_option maxHeartbeats 1000000 in
theorem RD.uniswapApproveInternalStore {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {value spender owner ret : UInt256} {R : List UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨7441⟩
      (mapSlot owner ⟨2⟩ :: ⟨64⟩ :: ⟨32⟩ :: ⟨0⟩ :: owner :: solcAddrMask ::
        value :: spender :: owner :: ret :: R)
      (twoWordHashMem owner ⟨2⟩ solcFreePtrMem)
      (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hperm : ee.perm = true)
    (hcanonSpender : spender.toNat < EVM.addressModulus)
    (hov : R.length + 13 ≤ 1024) :
    ∃ k' C', RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨7457⟩
      (⟨32⟩ :: ⟨64⟩ :: owner :: spender :: value :: spender :: owner :: ret :: R)
      (twoWordHashMem spender (mapSlot owner ⟨2⟩)
        (twoWordHashMem owner ⟨2⟩ solcFreePtrMem))
      (UInt256.ofNat 3) rdata
      (cA, sstoreAccountMap ee.codeOwner σ (mapSlot spender (mapSlot owner ⟨2⟩)) value)
      k' C' := by
  have hmask :
      UInt256.land spender solcAddrMask = spender :=
    solcAddrMask_clean hcanonSpender
  have hslot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((twoWordHashMem spender (mapSlot owner ⟨2⟩)
            (twoWordHashMem owner ⟨2⟩ solcFreePtrMem)).readWithPadding 0 64))) =
        mapSlot spender (mapSlot owner ⟨2⟩) := by
    rw [twoWordHashMem_read0_64 spender (mapSlot owner ⟨2⟩)
      (twoWordHashMem_size_96 owner ⟨2⟩ solcFreePtrMem_size)]
    unfold mapSlot
    exact mappingSlot_single spender (mapSlot owner ⟨2⟩)
  have rd7444 := evm_run h with [swap5, dup8, and]
  rw [hmask] at rd7444
  have rd7446 := evm_run rd7444 with [dup1, dup5]
  have rd7447 := rd7446.mstore 0
    (wordAt0Mem spender (twoWordHashMem owner ⟨2⟩ solcFreePtrMem))
    (UInt256.ofNat 3) (by decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd7449 := evm_run rd7447 with [swap5, dup3]
  have rd7450 := rd7449.mstore 0
    (twoWordHashMem spender (mapSlot owner ⟨2⟩)
      (twoWordHashMem owner ⟨2⟩ solcFreePtrMem))
    (UInt256.ofNat 3) (by decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd7453 := evm_run rd7450 with [swap2, dup3, swap1]
  have rd7454 := rd7453.keccak256 0 (mapSlot spender (mapSlot owner ⟨2⟩))
    (UInt256.ofNat 3) (by decide) mem_cost hslot (by native_decide) (by evm_ov)
  have rd7456 := evm_run rd7454 with [dup6, swap1]
  obtain ⟨_, _, rd7457⟩ := rd7456.sstore hperm (by decide)
    (by simp only [List.length_cons]; omega)
  exact ⟨_, _, by simpa using rd7457⟩

-- LIBRARY CANDIDATE: Reasoning.Reach — optimizer-on solc event-log suffix for a storage-write
-- routine that logs one data word and jumps to a dynamic return pc.
set_option maxHeartbeats 1000000 in
theorem RD.uniswapApproveInternalEmitAndJump {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {value spender owner ret : UInt256} {R : List UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨7457⟩
      (⟨32⟩ :: ⟨64⟩ :: owner :: spender :: value :: spender :: owner :: ret :: R)
      (uniswapApproveHashMem owner spender) (UInt256.ofNat 3) rdata acc k C)
    (hperm : ee.perm = true)
    (hret : (D_J UniswapV2Pair.uniswapV2PairBytecode 0).contains ret = true)
    (hov : R.length + 11 ≤ 1024) :
    ∃ k' C', RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ret R
      (uniswapApproveLogMem owner spender value) (UInt256.ofNat 5) rdata acc k' C' := by
  have rd7459 := evm_run h with [
    dup2,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide)
      mem_cost
      (uniswapApproveHashMem_mload64 owner spender)
      (by decide) (by evm_ov)]
  have rd7461 := evm_run rd7459 with [dup6, dup2]
  have rd7462 := rd7461.mstore 6 (uniswapApproveLogMem owner spender value)
    (UInt256.ofNat 5) (by decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd7464 := evm_run rd7462 with [
    swap2,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) (by decide)
      mem_cost
      (uniswapApproveLogMem_mload64 owner spender value)
      (by decide) (by evm_ov)]
  have rd7497₀ := rd7464.pushConst uniswapApprovalTopic (width := 32) (op := .PUSH32)
    (by decide) (by decide) (by evm_ov)
  have rd7505 := evm_run rd7497₀ with [swap3, dup2, swap1, sub, swap1, swap2, add, swap1]
  have rd7506 := rd7505.log3 0 (UInt256.ofNat 5) (by decide) hperm mem_cost
    (by decide) (by simp only [List.length_cons]; omega)
  have rd7509 := evm_run rd7506 with [pop, pop, pop]
  exact ⟨_, _, rd7509.jump (by decide) hret (by evm_ov)⟩

-- LIBRARY CANDIDATE: Reasoning.Reach — generic optimizer-on solc bool-return wrapper from
-- arbitrary memory, parameterized by the post-MSTORE return memory.
theorem RD.uniswapReturnBool797FromMem {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {val : UInt256} {R : List UInt256} {mem memout rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨797⟩ (val :: R)
      mem (UInt256.ofNat 5) rdata acc k C)
    (hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 5 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32)))
        = ⟨128⟩)
    (hmemout :
      (UInt256.toByteArray (UInt256.isZero (UInt256.isZero val))).write 0 mem 128 32 =
        memout)
    (hmemoutLoad64 :
      (if (⟨64⟩ : UInt256).toNat ≥ memout.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 5 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (memout.readWithPadding (⟨64⟩ : UInt256).toNat 32)))
        = ⟨128⟩)
    (hread128 :
      memout.readWithPadding 128 32 =
        UInt256.toByteArray (UInt256.isZero (UInt256.isZero val)))
    (hov : R.length + 5 ≤ 1024) :
    RDret UniswapV2Pair.uniswapV2PairBytecode g s0 acc
      (UInt256.toByteArray (UInt256.isZero (UInt256.isZero val))) := by
  exact evm_run h with [
    jumpdest, push1 ⟨64⟩, dup1,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) (by decide)
      mem_cost
      hmload64
      (by decide) (by evm_ov),
    swap2, iszero, iszero, dup3,
    raw mstore 0 memout (UInt256.ofNat 5)
      (by decide) mem_cost
      (by rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide]; exact hmemout)
      (by decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) (by decide)
      mem_cost
      hmemoutLoad64
      (by decide) (by evm_ov),
    swap1, dup2, swap1, sub, push1 ⟨32⟩, add, swap1,
    raw ret 0 (UInt256.toByteArray (UInt256.isZero (UInt256.isZero val))) (by decide)
      mem_cost
      (by
        rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide,
          show ((⟨32⟩ : UInt256) + UInt256.sub (⟨128⟩ : UInt256) ⟨128⟩).toNat = 32
            from by decide]
        exact hread128)
      (by evm_ov) ]

end UniswapV2Pair
