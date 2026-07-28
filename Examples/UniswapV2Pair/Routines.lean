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
  rcases hwf with
    ⟨hd0, hd1, hd4, hd6, hd7, hd8, hd9, hd11, hd12, hd13, hd14, hd17, _hd18,
      _hd20, _hd21, hd22, _hd23, _hd24, _hd26, _hd28, _hd30, _hd31, _hd32,
      _hd33, _hd34, _hd35, _hd36, _hd37, _hd39, _hd40, _hd41, _hd42, _hd45⟩
  exact RD.solcTwoAddressExternalLenOk hreach hd0 hd1 hd4 hd6 hd7 hd8 hd9 hd11 hd12
    hd13 hd14 hd17 hdecoded hsz68 hsize

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
  rcases hwf with
    ⟨hd0, hd1, hd4, hd6, hd7, hd8, hd9, hd11, hd12, hd13, hd14, hd17, _hd18,
      _hd20, _hd21, hd22, _hd23, _hd24, _hd26, _hd28, _hd30, _hd31, _hd32,
      _hd33, _hd34, _hd35, _hd36, _hd38, _hd39, _hd40, _hd43⟩
  exact RD.solcTwoAddressExternalLenOk hreach hd0 hd1 hd4 hd6 hd7 hd8 hd9 hd11 hd12
    hd13 hd14 hd17 hdecoded hsz68 hsize

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
  exact RD.solcAddressUint256ExternalMaskAndJump h hd22 hd23 hd24 hd26 hd28 hd30
    hd31 hd32 hd33 hd34 hd35 hd36 hd38 hd39 hd40 hd43 hcanon hroutine hov

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
  exact RD.solcAddressAddressUint256ExternalMaskAndJump h hd22 hd23 hd24 hd26 hd28
    hd30 hd31 hd32 hd33 hd34 hd35 hd36 hd37 hd39 hd40 hd41 hd42 hd43 hd44 hd45
    hd46 hd48 hd49 hd50 hd53 hcanon0 hcanon1 hroutine hov

/-! ## Shared checked-arithmetic routines -/

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
  exact RD.solcCheckedSubSuccess (pc := ⟨6879⟩) (okPc := ⟨2911⟩) h
    (by
      unfold solcCheckedSubSuccessWf
      repeat' first | apply And.intro | native_decide)
    hle hret (by jump_dest) hov

set_option maxHeartbeats 1000000 in
theorem RD.uniswapSafeMathSubUnderflow_aw6_size164_shared {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {a b ret : UInt256} {R : List UInt256}
    {mem : ByteArray} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨6879⟩ (b :: a :: ret :: R)
      mem (UInt256.ofNat 6) rdata acc k C)
    (hlt : a.toNat < b.toNat)
    (hmem : mem.size = 164)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hov : R.length + 9 ≤ 1024) :
    RDrev UniswapV2Pair.uniswapV2PairBytecode g s0 := by
  have hsubNat : (UInt256.sub a b).toNat = UInt256.size + a.toNat - b.toNat :=
    usub_toNat_underflow hlt
  have hgt : UInt256.gt (UInt256.sub a b) a = ⟨1⟩ := by
    show UInt256.fromBool (decide (UInt256.sub a b > a)) = ⟨1⟩
    rw [decide_eq_true]
    · rfl
    · show (UInt256.sub a b).toNat > a.toNat
      rw [hsubNat]
      have hb : b.toNat < UInt256.size := b.val.isLt
      omega
  have rd6886 := evm_run h with [jumpdest, dup1, dup3, sub, dup3, dup2]
  have rd6887₀ := evm_run rd6886 with [gt]
  have rd6887 := rd6887₀
  rw [hgt] at rd6887
  have rd6888₀ := evm_run rd6887 with [iszero]
  have rd6888 := rd6888₀
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd6888
  have rd6891 := evm_run rd6888 with [
    push2 ⟨2911⟩, jumpiNT (by decide)]
  have rd6895 := evm_run rd6891 with [
    push1 ⟨64⟩, dup1,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 6) (by decide)
      mem_cost
      (mloadFreePtrValue (by rw [hmem]; decide) (by decide) hread64)
      (by decide) (by evm_ov)]
  have rd6899 := rd6895.pushConst (⟨4594637⟩ : UInt256) (width := 3) (op := .PUSH3)
    (by decide) (by decide) (by evm_ov)
  have rd6918 := evm_run rd6899 with [
    push1 ⟨229⟩, shl, dup2,
    raw mstore 0 (solcErrorStringMem0 mem) (UInt256.ofNat 6)
      (by decide) mem_cost
      (by rfl) (by decide) (by evm_ov),
    push1 ⟨32⟩, push1 ⟨4⟩, dup3, add,
    raw mstore 0 (solcErrorStringMem1 mem) (UInt256.ofNat 6)
      (by decide) mem_cost
      (by rfl) (by decide) (by evm_ov),
    push1 ⟨21⟩, push1 ⟨36⟩, dup3, add,
    raw mstore 3
      (solcErrorStringMem2 (⟨21⟩ : UInt256) mem)
      (UInt256.ofNat 7) (by decide) mem_cost
      (by rfl) (by decide) (by evm_ov)]
  have rd6940 := rd6918.pushConst
    (⟨146807710733670254765134916515197633279875231805303⟩ : UInt256)
    (width := 21) (op := .PUSH21) (by decide) (by decide) (by evm_ov)
  exact evm_run rd6940 with [
    push1 ⟨88⟩, shl, push1 ⟨68⟩, dup3, add,
    raw mstore 3
      (solcErrorStringMem3 (⟨21⟩ : UInt256)
        (UInt256.shiftLeft
          (⟨146807710733670254765134916515197633279875231805303⟩ : UInt256)
          ⟨88⟩) mem)
      (UInt256.ofNat 8) (by decide) mem_cost
      (by rfl) (by decide) (by evm_ov),
    swap1,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) (by decide)
      mem_cost
      (solcErrorStringMem3_mload64_of_size164 (⟨21⟩ : UInt256)
        (UInt256.shiftLeft
          (⟨146807710733670254765134916515197633279875231805303⟩ : UInt256)
          ⟨88⟩) hmem hread64)
      (by decide) (by evm_ov),
    swap1, dup2, swap1, sub, push1 ⟨100⟩, add, swap1,
    raw rev 0 (by decide) mem_cost (by evm_ov)]

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
  exact RD.solcCheckedAddSuccess (pc := ⟨8515⟩) (okPc := ⟨2911⟩) h
    (by
      unfold solcCheckedAddSuccessWf
      repeat' first | apply And.intro | native_decide)
    hfit hret (by jump_dest) hov

set_option maxHeartbeats 1000000 in
theorem RD.uniswapSafeMathMulSuccess {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {a b ret : UInt256} {R : List UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ⟨6780⟩ (b :: a :: ret :: R)
      mem aw rdata acc k C)
    (hfit : a.toNat * b.toNat < UInt256.size)
    (hret : (D_J UniswapV2Pair.uniswapV2PairBytecode 0).contains ret = true)
    (hov : R.length + 9 ≤ 1024) :
    ∃ k' C', RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ret
      (UInt256.mul a b :: R) mem aw rdata acc k' C' := by
  by_cases hb : b = ⟨0⟩
  · subst b
    have hmulZero : UInt256.mul a (⟨0⟩ : UInt256) = ⟨0⟩ := by
      apply u256_inj
      rw [u256_mul_toNat]
      simp
    have rd6807pre := evm_run h with [jumpdest, push1 ⟨0⟩, dup2, iszero, dup1,
      push2 ⟨6807⟩]
    rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd6807pre
    have rdRet := evm_run rd6807pre with [
      jumpiT one_ne_zero_uint (by jump_dest),
      jumpdest, push2 ⟨2911⟩, jumpiT one_ne_zero_uint (by jump_dest),
      jumpdest, swap3, swap2, pop, pop, jump hret]
    rw [hmulZero]
    exact ⟨_, _, rdRet⟩
  · have hmulDiv : UInt256.div (UInt256.mul a b) b = a := by
      apply u256_inj
      rw [udiv_toNat]
      have hmulNat : (UInt256.mul a b).toNat = a.toNat * b.toNat := by
        rw [u256_mul_toNat, Nat.mod_eq_of_lt hfit]
      rw [hmulNat]
      have hbNat : b.toNat ≠ 0 := by
        intro hbZero
        exact hb (uint256_toNat_eq_zero hbZero)
      simpa [Nat.mul_comm] using Nat.mul_div_right a.toNat (Nat.pos_of_ne_zero hbNat)
    have heq : UInt256.eq (UInt256.div (UInt256.mul a b) b) a = ⟨1⟩ := by
      rw [hmulDiv]
      exact uInt256_eq_self a
    have rd6804pre := evm_run h with [jumpdest, push1 ⟨0⟩, dup2, iszero, dup1,
      push2 ⟨6807⟩]
    rw [isZero_eq_zero_of_ne hb] at rd6804pre
    have rd6804 := evm_run rd6804pre with [
      jumpiNT (by native_decide), pop, pop, dup1, dup3, mul, dup3, dup3, dup3,
      dup2, push2 ⟨6804⟩, jumpiT hb (by jump_dest)]
    have rd6807 := evm_run rd6804 with [jumpdest, div, eq]
    rw [heq] at rd6807
    exact ⟨_, _, evm_run rd6807 with [
      jumpdest, push2 ⟨2911⟩, jumpiT one_ne_zero_uint (by jump_dest),
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
  simpa [uniswapCodeOwnerStorageWord, mapSlot, solcMappingSlot] using
    RD.solcSingleMappingLoadToRoutineMem
      (code := UniswapV2Pair.uniswapV2PairBytecode)
      (pc := ⟨7510⟩) (baseSlot := ⟨1⟩) (afterLoadPc := ⟨7551⟩)
      (routinePc := ⟨6879⟩) (value := value) (aux := toWord) (key := src)
      (ret := ret) (R := R) h
      (by
        unfold solcSingleMappingLoadToRoutineMemWf
        repeat' first | apply And.intro | native_decide)
      hmem hcanonSrc (by jump_dest) (by decide) hov

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
  simpa [uniswapCodeOwnerStorageWord, mapSlot, solcMappingSlot] using
    RD.solcSingleMappingLoadCheckedSubMem
      (code := UniswapV2Pair.uniswapV2PairBytecode)
      (pc := ⟨7510⟩) (baseSlot := ⟨1⟩) (afterLoadPc := ⟨7551⟩)
      (routinePc := ⟨6879⟩) (checkedOkPc := ⟨2911⟩)
      (value := value) (aux := toWord) (key := src) (ret := ret) (R := R) h
      (by
        unfold solcSingleMappingLoadToRoutineMemWf
        repeat' first | apply And.intro | native_decide)
      (by
        unfold solcCheckedSubSuccessWf
        repeat' first | apply And.intro | native_decide)
      hmem hcanonSrc hbalance (by jump_dest) (by decide) (by jump_dest) (by jump_dest) hov

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

noncomputable abbrev uniswapTransferDebitHashMemOf (src : UInt256) (mem : ByteArray) :
    ByteArray :=
  twoWordHashMem src ⟨1⟩ (twoWordHashMem src ⟨1⟩ mem)

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
  simpa [uniswapTransferDebitHashMemOf, mapSlot, solcMappingSlot,
    solcSingleMappingStoreDebitOutPc] using
    RD.solcSingleMappingStoreDebitMem
      (code := UniswapV2Pair.uniswapV2PairBytecode)
      (pc := ⟨7551⟩) (baseSlot := ⟨1⟩) (newValue := debit)
      (value := value) (aux := toWord) (key := src) (ret := ret) (R := R) h
      (by
        unfold solcSingleMappingStoreDebitMemWf
        repeat' first | apply And.intro | native_decide)
      hmem hperm hcanonSrc hov

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

noncomputable abbrev uniswapTransferToHashMemOf (src toWord : UInt256) (mem : ByteArray) :
    ByteArray :=
  wordAt0Mem toWord (uniswapTransferDebitHashMemOf src mem)

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
  simpa [uniswapCodeOwnerStorageWord, uniswapTransferToHashMemOf, mapSlot, solcMappingSlot] using
    RD.solcPreparedSingleMappingLoadToRoutineMem
      (code := UniswapV2Pair.uniswapV2PairBytecode)
      (pc := ⟨7582⟩) (baseSlot := ⟨1⟩) (afterLoadPc := ⟨7604⟩)
      (routinePc := ⟨8515⟩) (value := value) (key := toWord) (other := src)
      (ret := ret) (R := R) h
      (by
        unfold solcPreparedSingleMappingLoadToRoutineMemWf
        repeat' first | apply And.intro | native_decide)
      (uniswapTransferToHashMemOf_slot src toWord hmem)
      hcanonTo (by jump_dest) (by decide) hov

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
  simpa [uniswapCodeOwnerStorageWord, uniswapTransferToHashMemOf, mapSlot, solcMappingSlot] using
    RD.solcPreparedSingleMappingLoadCheckedAddMem
      (code := UniswapV2Pair.uniswapV2PairBytecode)
      (pc := ⟨7582⟩) (baseSlot := ⟨1⟩) (afterLoadPc := ⟨7604⟩)
      (routinePc := ⟨8515⟩) (checkedOkPc := ⟨2911⟩)
      (value := value) (key := toWord) (other := src) (ret := ret) (R := R) h
      (by
        unfold solcPreparedSingleMappingLoadToRoutineMemWf
        repeat' first | apply And.intro | native_decide)
      (by
        unfold solcCheckedAddSuccessWf
        repeat' first | apply And.intro | native_decide)
      (uniswapTransferToHashMemOf_slot src toWord hmem)
      hcanonTo hfit (by jump_dest) (by decide) (by jump_dest) (by jump_dest) hov

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
  simpa [solcSingleMappingStoreCreditOutPc, uniswapTransferCreditHashMem,
    uniswapTransferToHashMem, mapSlot, solcMappingSlot] using
    RD.solcSingleMappingStoreCreditMem
      (code := UniswapV2Pair.uniswapV2PairBytecode) (pc := ⟨7604⟩)
      (baseSlot := ⟨1⟩) (newValue := newTo) (value := value) (key := toWord)
      (aux := src) (ret := ret) (R := R) (mem := uniswapTransferToHashMem src toWord)
      h
      (by
        unfold solcSingleMappingStoreCreditMemWf
        repeat' first | apply And.intro | native_decide)
      (by
        simpa [uniswapTransferCreditHashMem, mapSlot, solcMappingSlot] using
          uniswapTransferCreditHashMem_slot src toWord)
      hperm hcanonTo hov

def uniswapTransferTopic : UInt256 :=
  ⟨0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef⟩

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
    toByteArray_size]

theorem uniswapTransferLogMem_read64 (src toWord value : UInt256) :
    (uniswapTransferLogMem src toWord value).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold uniswapTransferLogMem
  rw [toByteArray_write_eq _ _ _ (by rw [uniswapTransferCreditHashMem_size]; omega)
      (by rw [uniswapTransferCreditHashMem_size]; exact lt_usize _ (by norm_num))]
  rw [readWithPadding_eq_extract _ 64 (by
      rw [ByteArray.size_append, ByteArray.size_append, uniswapTransferCreditHashMem_size,
        ByteArray_zeroes_size, toByteArray_size]
      native_decide)]
  rw [extract_append_left _ _ _ _ (by
      rw [ByteArray.size_append, uniswapTransferCreditHashMem_size, ByteArray_zeroes_size]
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
        toByteArray_size])]
  rw [extract_append_right_window
      (uniswapTransferCreditHashMem src toWord ++
        ffi.ByteArray.zeroes ((128 - (uniswapTransferCreditHashMem src toWord).size)))
      (UInt256.toByteArray value) 128 (128 + 32) (by
        rw [ByteArray.size_append, uniswapTransferCreditHashMem_size, ByteArray_zeroes_size])]
  rw [ByteArray.size_append, uniswapTransferCreditHashMem_size, ByteArray_zeroes_size]
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
  simpa [uniswapTransferLogMem] using
    RD.solcMaskedTransferLog3AndJump
      (code := UniswapV2Pair.uniswapV2PairBytecode) (pc := ⟨7638⟩)
      (topic := uniswapTransferTopic) (value := value) (toWord := toWord)
      (src := src) (ret := ret) (R := R)
      (mem := uniswapTransferCreditHashMem src toWord) h
      (by
        unfold solcMaskedTransferLog3AndJumpWf
        repeat' first | apply And.intro | native_decide)
      (uniswapTransferCreditHashMem_mload64 src toWord)
      (by simpa [uniswapTransferLogMem] using uniswapTransferLogMem_mload64 src toWord value)
      hperm hcanonSrc hret hov

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
  exact RD.solcDiscard2ReturnTrue (pc := ⟨2907⟩) h
    (by
      unfold solcDiscard2ReturnTrueWf
      repeat' first | apply And.intro | native_decide)
    hret hov

/-! ## Shared internal `_approve` routine prefix -/

def uniswapApprovalTopic : UInt256 :=
  ⟨0x8c5be1e5ebec7d5bd14f71427d1e84f3dd0314c0f7b2291e5b200ac8c7c3b925⟩

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
  have hmax' :
      (solcSlotWord σ ee
        (solcMappingSlot (solcMappingSlot (⟨2⟩ : UInt256) src) (solcSourceWord ee))).toNat =
        UInt256.size - 1 := by
    simpa [uniswapCodeOwnerStorageWord, uniswapSourceWord, mapSlot, solcMappingSlot] using hmax
  obtain ⟨_, _, rd2975⟩ := RD.solcNestedMappingCallerLoad
    (code := UniswapV2Pair.uniswapV2PairBytecode) (pc := ⟨2938⟩)
    (baseSlot := ⟨2⟩) (value := value) (aux := toWord) (owner := src)
    (ret := ret) (R := R) (mem := solcFreePtrMem) h
    (by
      unfold solcNestedMappingCallerLoadWf
      repeat' first | apply And.intro | native_decide)
    solcFreePtrMem_size hcanonSrc hov
  obtain ⟨_, _, rd3071⟩ := RD.solcUintMaxEqBranchTrue
    (code := UniswapV2Pair.uniswapV2PairBytecode)
    (pc := solcNestedMappingCallerLoadOutPc (⟨2938⟩ : UInt256))
    (targetPc := ⟨3071⟩)
    (word :=
      solcSlotWord σ ee
        (solcMappingSlot (solcMappingSlot (⟨2⟩ : UInt256) src) (solcSourceWord ee)))
    (discard := ⟨0⟩) (R := value :: toWord :: src :: ret :: R)
    rd2975
    (by
      unfold solcUintMaxEqBranchWf solcNestedMappingCallerLoadOutPc
      repeat' first | apply And.intro | native_decide)
    hmax' (by jump_dest) (by simp only [List.length_cons]; omega)
  exact ⟨_, _, by
    simpa [solcNestedMappingCallerLoadOutPc, solcNestedMappingCallerHashMem,
      uniswapCodeOwnerStorageWord, uniswapApproveHashMem, uniswapSourceWord, mapSlot,
      solcMappingSlot] using rd3071⟩

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
  exact RD.solcInternalCallSetup3
    (pc := ⟨3071⟩) (contPc := ⟨3082⟩) (routinePc := ⟨7510⟩) h
    (by
      unfold solcInternalCallSetup3Wf
      repeat' first | apply And.intro | native_decide)
    (by jump_dest) hov

theorem uniswapApproveLogMem_size (owner spender value : UInt256) :
    (uniswapApproveLogMem owner spender value).size = 160 := by
  unfold uniswapApproveLogMem
  rw [toByteArray_write_eq _ _ _ (by rw [uniswapApproveHashMem_size]; omega)
      (by rw [uniswapApproveHashMem_size]; exact lt_usize _ (by norm_num)),
    ByteArray.size_append, ByteArray.size_append, uniswapApproveHashMem_size,
    ByteArray_zeroes_size,
    toByteArray_size]

theorem uniswapApproveLogMem_read64 (owner spender value : UInt256) :
    (uniswapApproveLogMem owner spender value).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold uniswapApproveLogMem
  rw [toByteArray_write_eq _ _ _ (by rw [uniswapApproveHashMem_size]; omega)
      (by rw [uniswapApproveHashMem_size]; exact lt_usize _ (by norm_num))]
  rw [readWithPadding_eq_extract _ 64 (by
      rw [ByteArray.size_append, ByteArray.size_append, uniswapApproveHashMem_size,
        ByteArray_zeroes_size, toByteArray_size]
      native_decide)]
  rw [extract_append_left _ _ _ _ (by
      rw [ByteArray.size_append, uniswapApproveHashMem_size, ByteArray_zeroes_size]
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
        toByteArray_size])]
  rw [extract_append_right_window
      (uniswapApproveHashMem owner spender ++
        ffi.ByteArray.zeroes ((128 - (uniswapApproveHashMem owner spender).size)))
      (UInt256.toByteArray value) 128 (128 + 32) (by
        rw [ByteArray.size_append, uniswapApproveHashMem_size, ByteArray_zeroes_size])]
  rw [ByteArray.size_append, uniswapApproveHashMem_size, ByteArray_zeroes_size]
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
  simpa [solcNestedMappingStoreInnerHashOutPc, mapSlot, solcMappingSlot] using
    RD.solcNestedMappingStoreInnerHash
      (code := UniswapV2Pair.uniswapV2PairBytecode) (pc := ⟨7412⟩)
      (baseSlot := ⟨2⟩) (value := value) (spender := spender)
      (owner := owner) (ret := ret) (R := R) (mem := solcFreePtrMem) h
      (by
        unfold solcNestedMappingStoreInnerHashWf
        repeat' first | apply And.intro | native_decide)
      solcFreePtrMem_size hcanonOwner hov

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
  simpa [solcNestedMappingStoreOuterSstoreOutPc, mapSlot, solcMappingSlot] using
    RD.solcNestedMappingStoreOuterSstore
      (code := UniswapV2Pair.uniswapV2PairBytecode) (pc := ⟨7441⟩)
      (innerSlot := mapSlot owner ⟨2⟩) (value := value) (spender := spender)
      (owner := owner) (ret := ret) (R := R)
      (mem := twoWordHashMem owner ⟨2⟩ solcFreePtrMem) h
      (by
        unfold solcNestedMappingStoreOuterSstoreWf
        repeat' first | apply And.intro | native_decide)
      (twoWordHashMem_size_96 owner ⟨2⟩ solcFreePtrMem_size)
      hperm hcanonSpender hov

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
  simpa [uniswapApproveLogMem] using
    RD.solcPlainLog3AndJump
      (code := UniswapV2Pair.uniswapV2PairBytecode) (pc := ⟨7457⟩)
      (topic := uniswapApprovalTopic) (value := value) (topic1 := owner)
      (topic2 := spender) (ret := ret) (R := R)
      (mem := uniswapApproveHashMem owner spender) h
      (by
        unfold solcPlainLog3AndJumpWf
        repeat' first | apply And.intro | native_decide)
      (uniswapApproveHashMem_mload64 owner spender)
      (by simpa [uniswapApproveLogMem] using uniswapApproveLogMem_mload64 owner spender value)
      hperm hret hov

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
  exact RD.solcReturnBoolFromMem h
    (by
      unfold solcReturnBoolFromMemWf
      repeat' first | apply And.intro | native_decide)
    hmload64
    hmemout
    hmemoutLoad64
    hread128
    hov

end UniswapV2Pair
