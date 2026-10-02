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

set_option maxHeartbeats 1000000 in
theorem RD.uniswapTwoAddressExternalLenOk {σ σ₀ A I} {g : Sat256} {sel : UInt256}
    {entry ret routine : UInt256}
    (hreach : ∃ k C, RD UniswapV2Pair.uniswapV2PairBytecode I g
      (Reasoning.Theory.initState σ σ₀ g A I) entry [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C)
    (hwf : uniswapTwoAddressExternalEntryWf entry ret routine)
    (hdecoded : (D_J UniswapV2Pair.uniswapV2PairBytecode 0).contains
      (uniswapTwoAddressExternalDecodedPc entry) = true)
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size) :
    ∃ k C, RD UniswapV2Pair.uniswapV2PairBytecode I g
      (Reasoning.Theory.initState σ σ₀ g A I)
      (uniswapTwoAddressExternalDecodedPc entry)
      (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩ :: ⟨4⟩ :: ret :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C := by
  rcases hwf with
    ⟨hd0, hd1, hd4, hd6, hd7, hd8, hd9, hd11, hd12, hd13, hd14, hd17, _hd18,
      _hd20, _hd21, hd22, _hd23, _hd24, _hd26, _hd28, _hd30, _hd31, _hd32,
      _hd33, _hd34, _hd35, _hd36, _hd37, _hd39, _hd40, _hd41, _hd42, _hd45⟩
  exact RD.solcTwoAddressExternalLenOk hreach hd0 hd1 hd4 hd6 hd7 hd8 hd9 hd11 hd12
    hd13 hd14 hd17 hdecoded hsz68 hsize

set_option maxHeartbeats 1000000 in
theorem RD.uniswapTwoAddressExternalMaskAndJump {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {entry ret routine de : UInt256} {R : List UInt256} {rdata : ByteArray}
    {σ : AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0
      (uniswapTwoAddressExternalDecodedPc entry) (de :: ⟨4⟩ :: ret :: R)
      solcFreePtrMem (UInt256.ofNat 3) rdata σ k C)
    (hwf : uniswapTwoAddressExternalEntryWf entry ret routine)
    (hcanon0 : (calldataWord ee.calldata 4).toNat < EVM.addressModulus)
    (hcanon1 : (calldataWord ee.calldata 36).toNat < EVM.addressModulus)
    (hroutine : (D_J UniswapV2Pair.uniswapV2PairBytecode 0).contains routine = true)
    (hov : R.length + 7 ≤ 1024) :
    ∃ k' C', RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 routine
      (calldataWord ee.calldata 36 :: calldataWord ee.calldata 4 :: ret :: R)
      solcFreePtrMem (UInt256.ofNat 3) rdata σ k' C' := by
  rcases hwf with
    ⟨_hd0, _hd1, _hd4, _hd6, _hd7, _hd8, _hd9, _hd11, _hd12, _hd13, _hd14,
      _hd17, _hd18, _hd20, _hd21, hd22, hd23, hd24, hd26, hd28, hd30, hd31,
      hd32, hd33, hd34, hd35, hd36, hd37, hd39, hd40, hd41, hd42, hd45⟩
  exact RD.solcTwoAddressExternalMaskAndJump h hd22 hd23 hd24 hd26 hd28 hd30 hd31
    hd32 hd33 hd34 hd35 hd36 hd37 hd39 hd40 hd41 hd42 hd45 hcanon0 hcanon1 hroutine hov

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

set_option maxHeartbeats 1000000 in
theorem RD.addressUint256ExternalLenOk {σ σ₀ A I} {g : Sat256}
    {sel : UInt256} {entry ret routine : UInt256}
    (hreach : ∃ k C, RD UniswapV2Pair.uniswapV2PairBytecode I g
      (Reasoning.Theory.initState σ σ₀ g A I) entry [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C)
    (hwf : uniswapAddressUint256ExternalEntryWf entry ret routine)
    (hdecoded : (D_J UniswapV2Pair.uniswapV2PairBytecode 0).contains
      (uniswapAddressUint256ExternalDecodedPc entry) = true)
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size) :
    ∃ k C, RD UniswapV2Pair.uniswapV2PairBytecode I g
      (Reasoning.Theory.initState σ σ₀ g A I)
      (uniswapAddressUint256ExternalDecodedPc entry)
      (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩ :: ⟨4⟩ :: ret :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C := by
  rcases hwf with
    ⟨hd0, hd1, hd4, hd6, hd7, hd8, hd9, hd11, hd12, hd13, hd14, hd17, _hd18,
      _hd20, _hd21, hd22, _hd23, _hd24, _hd26, _hd28, _hd30, _hd31, _hd32,
      _hd33, _hd34, _hd35, _hd36, _hd38, _hd39, _hd40, _hd43⟩
  exact RD.solcTwoAddressExternalLenOk hreach hd0 hd1 hd4 hd6 hd7 hd8 hd9 hd11 hd12
    hd13 hd14 hd17 hdecoded hsz68 hsize

set_option maxHeartbeats 1000000 in
theorem RD.addressUint256ExternalMaskAndJump {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {entry ret routine de : UInt256} {R : List UInt256}
    {rdata : ByteArray} {σ : AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0
      (uniswapAddressUint256ExternalDecodedPc entry) (de :: ⟨4⟩ :: ret :: R)
      solcFreePtrMem (UInt256.ofNat 3) rdata σ k C)
    (hwf : uniswapAddressUint256ExternalEntryWf entry ret routine)
    (hcanon : (calldataWord ee.calldata 4).toNat < EVM.addressModulus)
    (hroutine : (D_J UniswapV2Pair.uniswapV2PairBytecode 0).contains routine = true)
    (hov : R.length + 6 ≤ 1024) :
    ∃ k' C', RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 routine
      (calldataWord ee.calldata 36 :: calldataWord ee.calldata 4 :: ret :: R)
      solcFreePtrMem (UInt256.ofNat 3) rdata σ k' C' := by
  rcases hwf with
    ⟨_hd0, _hd1, _hd4, _hd6, _hd7, _hd8, _hd9, _hd11, _hd12, _hd13, _hd14,
      _hd17, _hd18, _hd20, _hd21, hd22, hd23, hd24, hd26, hd28, hd30, hd31,
      hd32, hd33, hd34, hd35, hd36, hd38, hd39, hd40, hd43⟩
  exact RD.solcAddressUint256ExternalMaskAndJump h hd22 hd23 hd24 hd26 hd28 hd30
    hd31 hd32 hd33 hd34 hd35 hd36 hd38 hd39 hd40 hd43 hcanon hroutine hov

set_option maxHeartbeats 1000000 in
theorem RD.addressUint256ExternalMaskAndJumpMasked {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {entry ret routine de : UInt256} {R : List UInt256}
    {rdata : ByteArray} {σ : AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0
      (uniswapAddressUint256ExternalDecodedPc entry) (de :: ⟨4⟩ :: ret :: R)
      solcFreePtrMem (UInt256.ofNat 3) rdata σ k C)
    (hwf : uniswapAddressUint256ExternalEntryWf entry ret routine)
    (hroutine : (D_J UniswapV2Pair.uniswapV2PairBytecode 0).contains routine = true)
    (hov : R.length + 6 ≤ 1024) :
    ∃ k' C', RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 routine
      (calldataWord ee.calldata 36 :: UInt256.land solcAddrMask (calldataWord ee.calldata 4) ::
        ret :: R)
      solcFreePtrMem (UInt256.ofNat 3) rdata σ k' C' := by
  rcases hwf with
    ⟨_hd0, _hd1, _hd4, _hd6, _hd7, _hd8, _hd9, _hd11, _hd12, _hd13, _hd14,
      _hd17, _hd18, _hd20, _hd21, hd22, hd23, hd24, hd26, hd28, hd30, hd31,
      hd32, hd33, hd34, hd35, hd36, hd38, hd39, hd40, hd43⟩
  exact RD.solcAddressUint256ExternalMaskAndJumpMasked h hd22 hd23 hd24 hd26 hd28 hd30
    hd31 hd32 hd33 hd34 hd35 hd36 hd38 hd39 hd40 hd43 hroutine hov

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

set_option maxHeartbeats 1000000 in
theorem RD.addressAddressUint256ExternalLenOk {σ σ₀ A I} {g : Sat256}
    {sel : UInt256} {entry ret routine : UInt256}
    (hreach : ∃ k C, RD UniswapV2Pair.uniswapV2PairBytecode I g
      (Reasoning.Theory.initState σ σ₀ g A I) entry [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C)
    (hwf : uniswapAddressAddressUint256ExternalEntryWf entry ret routine)
    (hdecoded : (D_J UniswapV2Pair.uniswapV2PairBytecode 0).contains
      (uniswapAddressAddressUint256ExternalDecodedPc entry) = true)
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size) :
    ∃ k C, RD UniswapV2Pair.uniswapV2PairBytecode I g
      (Reasoning.Theory.initState σ σ₀ g A I)
      (uniswapAddressAddressUint256ExternalDecodedPc entry)
      (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩ :: ⟨4⟩ :: ret :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C := by
  rcases hwf with
    ⟨hd0, hd1, hd4, hd6, hd7, hd8, hd9, hd11, hd12, hd13, hd14, hd17, _hd18,
      _hd20, _hd21, _hd22, _hd23, _hd24, _hd26, _hd28, _hd30, _hd31, _hd32,
      _hd33, _hd34, _hd35, _hd36, _hd37, _hd39, _hd40, _hd41, _hd42, _hd43,
      _hd44, _hd45, _hd46, _hd48, _hd49, _hd50, _hd53⟩
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨96⟩ = ⟨0⟩ :=
    UniswapV2Pair.uniswapDecodeLenCheckOk_4_96_lt hsz100 hsize
  exact RD.solcExternalStaticArgsLenOk hreach hd0 hd1 hd4 hd6 hd7 hd8 hd9 hd11 hd12
    hd13 hd14 hd17 hdecoded hlt

set_option maxHeartbeats 1000000 in
theorem RD.addressAddressUint256ExternalMaskAndJump {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {entry ret routine de : UInt256} {R : List UInt256}
    {rdata : ByteArray} {σ : AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0
      (uniswapAddressAddressUint256ExternalDecodedPc entry) (de :: ⟨4⟩ :: ret :: R)
      solcFreePtrMem (UInt256.ofNat 3) rdata σ k C)
    (hwf : uniswapAddressAddressUint256ExternalEntryWf entry ret routine)
    (hcanon0 : (calldataWord ee.calldata 4).toNat < EVM.addressModulus)
    (hcanon1 : (calldataWord ee.calldata 36).toNat < EVM.addressModulus)
    (hroutine : (D_J UniswapV2Pair.uniswapV2PairBytecode 0).contains routine = true)
    (hov : R.length + 7 ≤ 1024) :
    ∃ k' C', RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 routine
      (calldataWord ee.calldata 68 :: calldataWord ee.calldata 36 ::
        calldataWord ee.calldata 4 :: ret :: R)
      solcFreePtrMem (UInt256.ofNat 3) rdata σ k' C' := by
  rcases hwf with
    ⟨_hd0, _hd1, _hd4, _hd6, _hd7, _hd8, _hd9, _hd11, _hd12, _hd13, _hd14,
      _hd17, _hd18, _hd20, _hd21, hd22, hd23, hd24, hd26, hd28, hd30, hd31,
      hd32, hd33, hd34, hd35, hd36, hd37, hd39, hd40, hd41, hd42, hd43, hd44,
      hd45, hd46, hd48, hd49, hd50, hd53⟩
  exact RD.solcAddressAddressUint256ExternalMaskAndJump h hd22 hd23 hd24 hd26 hd28
    hd30 hd31 hd32 hd33 hd34 hd35 hd36 hd37 hd39 hd40 hd41 hd42 hd43 hd44 hd45
    hd46 hd48 hd49 hd50 hd53 hcanon0 hcanon1 hroutine hov


end UniswapV2Pair
