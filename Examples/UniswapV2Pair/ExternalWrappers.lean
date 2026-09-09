import Examples.UniswapV2Pair.Routines
import Examples.UniswapV2Pair.LegacyABI

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace UniswapV2Pair

/-! # Shared Uniswap V2 Pair external-wrapper branches -/

/-! ## Shared one-address external entry -/

/-- PC of the post-length-check decode block in Uniswap's optimized one-address external wrappers. -/
@[reducible] def uniswapOneAddressExternalDecodedPc (pc : UInt256) : UInt256 :=
  uniswapOneAddressGetterDecodedPc pc

/-- Bytecode shape for Uniswap's optimized external one-address wrappers.

The wrapper checks that one static ABI word is present, masks the address word, and jumps to a
routine while preserving the caller-supplied return/continuation pc.
-/
@[reducible] def uniswapOneAddressExternalEntryWf
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
  let p22 := uniswapOneAddressExternalDecodedPc pc
  let p23 := p22 + ⟨1⟩
  let p24 := p23 + ⟨1⟩
  let p25 := p24 + ⟨1⟩
  let p27 := p25 + UInt256.ofNat 2
  let p29 := p27 + UInt256.ofNat 2
  let p31 := p29 + UInt256.ofNat 2
  let p32 := p31 + ⟨1⟩
  let p33 := p32 + ⟨1⟩
  let p34 := p33 + ⟨1⟩
  let p37 := p34 + UInt256.ofNat 3
  decode UniswapV2Pair.uniswapV2PairBytecode pc = some (.JUMPDEST, .none)
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode p1 =
      some (.Push .PUSH2, some (ret, 2))
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode p4 =
      some (.Push .PUSH1, some (⟨4⟩, 1))
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode p6 = some (.DUP1, .none)
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode p7 = some (.CALLDATASIZE, .none)
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode p8 = some (.SUB, .none)
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode p9 =
      some (.Push .PUSH1, some (⟨32⟩, 1))
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
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode p24 = some (.CALLDATALOAD, .none)
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode p25 =
      some (.Push .PUSH1, some (⟨1⟩, 1))
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode p27 =
      some (.Push .PUSH1, some (⟨1⟩, 1))
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode p29 =
      some (.Push .PUSH1, some (⟨160⟩, 1))
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode p31 = some (.SHL, .none)
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode p32 = some (.SUB, .none)
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode p33 = some (.AND, .none)
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode p34 =
      some (.Push .PUSH2, some (routine, 2))
  ∧ decode UniswapV2Pair.uniswapV2PairBytecode p37 = some (.JUMP, .none)

/-- Discharge a concrete Uniswap one-address external entry bytecode-shape proof. -/
macro "uniswap_one_address_external_entry_wf" : term =>
  `(by
    unfold UniswapV2Pair.uniswapOneAddressExternalEntryWf
    repeat' first | apply And.intro | decide +native)

set_option maxHeartbeats 1000000 in
theorem RD.uniswapOneAddressExternalLenOk {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    {entry ret routine : UInt256}
    (hreach : ∃ k C, RD UniswapV2Pair.uniswapV2PairBytecode I g
      (Reasoning.Theory.initState cA gh bl σ σ₀ g A I) entry [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hwf : uniswapOneAddressExternalEntryWf entry ret routine)
    (hdecoded : (D_J UniswapV2Pair.uniswapV2PairBytecode 0).contains
      (uniswapOneAddressExternalDecodedPc entry) = true)
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size) :
    ∃ k C, RD UniswapV2Pair.uniswapV2PairBytecode I g
      (Reasoning.Theory.initState cA gh bl σ σ₀ g A I)
      (uniswapOneAddressExternalDecodedPc entry)
      (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩ :: ⟨4⟩ :: ret :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  rcases hwf with
    ⟨hd0, hd1, hd4, hd6, hd7, hd8, hd9, hd11, hd12, hd13, hd14, hd17, _hd18,
      _hd20, _hd21, hd22, _hd23, _hd24, _hd25, _hd27, _hd29, _hd31, _hd32,
      _hd33, _hd34, _hd37⟩
  exact RD.solcOneAddressExternalLenOk hreach hd0 hd1 hd4 hd6 hd7 hd8 hd9 hd11 hd12
    hd13 hd14 hd17 hdecoded hsz36 hsize

set_option maxHeartbeats 1000000 in
theorem RD.uniswapOneAddressExternalMaskAndJump {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {entry ret routine de : UInt256} {R : List UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0
      (uniswapOneAddressExternalDecodedPc entry) (de :: ⟨4⟩ :: ret :: R)
      solcFreePtrMem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hwf : uniswapOneAddressExternalEntryWf entry ret routine)
    (hcanon : (calldataWord ee.calldata 4).toNat < EVM.addressModulus)
    (hroutine : (D_J UniswapV2Pair.uniswapV2PairBytecode 0).contains routine = true)
    (hov : R.length + 5 ≤ 1024) :
    ∃ k' C', RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 routine
      (calldataWord ee.calldata 4 :: ret :: R)
      solcFreePtrMem (UInt256.ofNat 3) rdata (cA, σ) k' C' := by
  rcases hwf with
    ⟨_hd0, _hd1, _hd4, _hd6, _hd7, _hd8, _hd9, _hd11, _hd12, _hd13, _hd14,
      _hd17, _hd18, _hd20, _hd21, hd22, hd23, hd24, hd25, hd27, hd29, hd31,
      hd32, hd33, hd34, hd37⟩
  exact RD.solcOneAddressExternalMaskAndJump h hd22 hd23 hd24 hd25 hd27 hd29 hd31 hd32
    hd33 hd34 hd37 hcanon hroutine hov

set_option maxHeartbeats 1000000 in
theorem RD.uniswapOneAddressExternalMaskAndJumpMasked {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {entry ret routine de : UInt256} {R : List UInt256}
    {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0
      (uniswapOneAddressExternalDecodedPc entry) (de :: ⟨4⟩ :: ret :: R)
      solcFreePtrMem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hwf : uniswapOneAddressExternalEntryWf entry ret routine)
    (hroutine : (D_J UniswapV2Pair.uniswapV2PairBytecode 0).contains routine = true)
    (hov : R.length + 5 ≤ 1024) :
    ∃ k' C', RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 routine
      (UInt256.land solcAddrMask (calldataWord ee.calldata 4) :: ret :: R)
      solcFreePtrMem (UInt256.ofNat 3) rdata (cA, σ) k' C' := by
  rcases hwf with
    ⟨_hd0, _hd1, _hd4, _hd6, _hd7, _hd8, _hd9, _hd11, _hd12, _hd13, _hd14,
      _hd17, _hd18, _hd20, _hd21, hd22, hd23, hd24, hd25, hd27, hd29, hd31,
      hd32, hd33, hd34, hd37⟩
  exact RD.solcOneAddressExternalMaskAndJumpMasked h hd22 hd23 hd24 hd25 hd27 hd29 hd31
    hd32 hd33 hd34 hd37 hroutine hov

set_option maxHeartbeats 1000000 in
theorem RD.uniswapOneAddressExternalShort {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel entry ret routine : UInt256}
    (hreach : ∃ k C, RD UniswapV2Pair.uniswapV2PairBytecode I g
      (Reasoning.Theory.initState cA gh bl σ σ₀ g A I) entry [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hwf : uniswapOneAddressExternalEntryWf entry ret routine)
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 36) :
    RDrev UniswapV2Pair.uniswapV2PairBytecode g
      (Reasoning.Theory.initState cA gh bl σ σ₀ g A I) := by
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨1⟩ := by
    apply ult_one
    rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide,
      usub_ofNat_word_toNat (c := (⟨4⟩ : UInt256)) (by simpa using hsz4) hsize,
      show (⟨4⟩ : UInt256).toNat = 4 from by decide]
    omega
  rcases hwf with
    ⟨hd0, hd1, hd4, hd6, hd7, hd8, hd9, hd11, hd12, hd13, hd14, hd17, hd18,
      hd20, hd21, _hd22, _hd23, _hd24, _hd25, _hd27, _hd29, _hd31, _hd32,
      _hd33, _hd34, _hd37⟩
  exact RD.solcExternalStaticArgsShortReverts hreach hd0 hd1 hd4 hd6 hd7 hd8 hd9
    hd11 hd12 hd13 hd14 hd17 hd18 hd20 hd21 hlt

set_option maxHeartbeats 1000000 in
theorem RD.uniswapOneAddressGetterShort {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel entry routine : UInt256}
    (hreach : ∃ k C, RD UniswapV2Pair.uniswapV2PairBytecode I g
      (Reasoning.Theory.initState cA gh bl σ σ₀ g A I) entry [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hwf : uniswapOneAddressGetterEntryWf entry routine)
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 36) :
    RDrev UniswapV2Pair.uniswapV2PairBytecode g
      (Reasoning.Theory.initState cA gh bl σ σ₀ g A I) := by
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨1⟩ := by
    apply ult_one
    rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide,
      usub_ofNat_word_toNat (c := (⟨4⟩ : UInt256)) (by simpa using hsz4) hsize,
      show (⟨4⟩ : UInt256).toNat = 4 from by decide]
    omega
  rcases hwf with
    ⟨hd0, hd1, hd4, hd6, hd7, hd8, hd9, hd11, hd12, hd13, hd14, hd17, hd18,
      hd20, hd21, _hd22, _hd23, _hd24, _hd25, _hd27, _hd29, _hd31, _hd32,
      _hd33, _hd34, _hd37⟩
  exact RD.solcExternalStaticArgsShortReverts hreach hd0 hd1 hd4 hd6 hd7 hd8 hd9
    hd11 hd12 hd13 hd14 hd17 hd18 hd20 hd21 hlt

set_option maxHeartbeats 1000000 in
theorem RD.uniswapTwoAddressGetterShort {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel entry routine : UInt256}
    (hreach : ∃ k C, RD UniswapV2Pair.uniswapV2PairBytecode I g
      (Reasoning.Theory.initState cA gh bl σ σ₀ g A I) entry [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hwf : uniswapTwoAddressGetterEntryWf entry routine)
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 68) :
    RDrev UniswapV2Pair.uniswapV2PairBytecode g
      (Reasoning.Theory.initState cA gh bl σ σ₀ g A I) := by
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨1⟩ := by
    apply ult_one
    rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide,
      usub_ofNat_word_toNat (c := (⟨4⟩ : UInt256)) (by simpa using hsz4) hsize,
      show (⟨4⟩ : UInt256).toNat = 4 from by decide]
    omega
  rcases hwf with
    ⟨hd0, hd1, hd4, hd6, hd7, hd8, hd9, hd11, hd12, hd13, hd14, hd17, hd18,
      hd20, hd21, _hd22, _hd23, _hd24, _hd26, _hd28, _hd30, _hd31, _hd32,
      _hd33, _hd34, _hd35, _hd36, _hd37, _hd39, _hd40, _hd41, _hd42, _hd45⟩
  exact RD.solcExternalStaticArgsShortReverts hreach hd0 hd1 hd4 hd6 hd7 hd8 hd9
    hd11 hd12 hd13 hd14 hd17 hd18 hd20 hd21 hlt

set_option maxHeartbeats 1000000 in
theorem RD.uniswapTwoAddressExternalShort {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel entry ret routine : UInt256}
    (hreach : ∃ k C, RD UniswapV2Pair.uniswapV2PairBytecode I g
      (Reasoning.Theory.initState cA gh bl σ σ₀ g A I) entry [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hwf : uniswapTwoAddressExternalEntryWf entry ret routine)
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 68) :
    RDrev UniswapV2Pair.uniswapV2PairBytecode g
      (Reasoning.Theory.initState cA gh bl σ σ₀ g A I) := by
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨1⟩ := by
    apply ult_one
    rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide,
      usub_ofNat_word_toNat (c := (⟨4⟩ : UInt256)) (by simpa using hsz4) hsize,
      show (⟨4⟩ : UInt256).toNat = 4 from by decide]
    omega
  rcases hwf with
    ⟨hd0, hd1, hd4, hd6, hd7, hd8, hd9, hd11, hd12, hd13, hd14, hd17, hd18,
      hd20, hd21, _hd22, _hd23, _hd24, _hd26, _hd28, _hd30, _hd31, _hd32,
      _hd33, _hd34, _hd35, _hd36, _hd37, _hd39, _hd40, _hd41, _hd42, _hd45⟩
  exact RD.solcExternalStaticArgsShortReverts hreach hd0 hd1 hd4 hd6 hd7 hd8 hd9
    hd11 hd12 hd13 hd14 hd17 hd18 hd20 hd21 hlt

set_option maxHeartbeats 1000000 in
theorem RD.uniswapTwoAddressExternalMaskAndJumpMasked {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {entry ret routine de : UInt256} {R : List UInt256}
    {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0
      (uniswapTwoAddressExternalDecodedPc entry) (de :: ⟨4⟩ :: ret :: R)
      solcFreePtrMem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hwf : uniswapTwoAddressExternalEntryWf entry ret routine)
    (hroutine : (D_J UniswapV2Pair.uniswapV2PairBytecode 0).contains routine = true)
    (hov : R.length + 7 ≤ 1024) :
    ∃ k' C', RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 routine
      (UInt256.land solcAddrMask (calldataWord ee.calldata 36) ::
        UInt256.land solcAddrMask (calldataWord ee.calldata 4) :: ret :: R)
      solcFreePtrMem (UInt256.ofNat 3) rdata (cA, σ) k' C' := by
  rcases hwf with
    ⟨_hd0, _hd1, _hd4, _hd6, _hd7, _hd8, _hd9, _hd11, _hd12, _hd13, _hd14,
      _hd17, _hd18, _hd20, _hd21, hd22, hd23, hd24, hd26, hd28, hd30, hd31,
      hd32, hd33, hd34, hd35, hd36, hd37, hd39, hd40, hd41, hd42, hd45⟩
  exact RD.solcTwoAddressExternalMaskAndJumpMasked h hd22 hd23 hd24 hd26 hd28 hd30 hd31
    hd32 hd33 hd34 hd35 hd36 hd37 hd39 hd40 hd41 hd42 hd45 hroutine hov

set_option maxHeartbeats 1000000 in
theorem RD.addressUint256ExternalShort {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel entry ret routine : UInt256}
    (hreach : ∃ k C, RD UniswapV2Pair.uniswapV2PairBytecode I g
      (Reasoning.Theory.initState cA gh bl σ σ₀ g A I) entry [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hwf : uniswapAddressUint256ExternalEntryWf entry ret routine)
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 68) :
    RDrev UniswapV2Pair.uniswapV2PairBytecode g
      (Reasoning.Theory.initState cA gh bl σ σ₀ g A I) := by
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨1⟩ := by
    apply ult_one
    rw [show (⟨64⟩ : UInt256).toNat = 64 from by decide,
      usub_ofNat_word_toNat (c := (⟨4⟩ : UInt256)) (by simpa using hsz4) hsize,
      show (⟨4⟩ : UInt256).toNat = 4 from by decide]
    omega
  rcases hwf with
    ⟨hd0, hd1, hd4, hd6, hd7, hd8, hd9, hd11, hd12, hd13, hd14, hd17, hd18,
      hd20, hd21, _hd22, _hd23, _hd24, _hd26, _hd28, _hd30, _hd31, _hd32,
      _hd33, _hd34, _hd35, _hd36, _hd38, _hd39, _hd40, _hd43⟩
  exact RD.solcExternalStaticArgsShortReverts hreach hd0 hd1 hd4 hd6 hd7 hd8 hd9
    hd11 hd12 hd13 hd14 hd17 hd18 hd20 hd21 hlt

set_option maxHeartbeats 1000000 in
theorem RD.addressAddressUint256ExternalShort {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel entry ret routine : UInt256}
    (hreach : ∃ k C, RD UniswapV2Pair.uniswapV2PairBytecode I g
      (Reasoning.Theory.initState cA gh bl σ σ₀ g A I) entry [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hwf : uniswapAddressAddressUint256ExternalEntryWf entry ret routine)
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 100) :
    RDrev UniswapV2Pair.uniswapV2PairBytecode g
      (Reasoning.Theory.initState cA gh bl σ σ₀ g A I) := by
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨96⟩ = ⟨1⟩ := by
    apply ult_one
    rw [show (⟨96⟩ : UInt256).toNat = 96 from by decide,
      usub_ofNat_word_toNat (c := (⟨4⟩ : UInt256)) (by simpa using hsz4) hsize,
      show (⟨4⟩ : UInt256).toNat = 4 from by decide]
    omega
  rcases hwf with
    ⟨hd0, hd1, hd4, hd6, hd7, hd8, hd9, hd11, hd12, hd13, hd14, hd17, hd18,
      hd20, hd21, _hd22, _hd23, _hd24, _hd26, _hd28, _hd30, _hd31, _hd32,
      _hd33, _hd34, _hd35, _hd36, _hd37, _hd39, _hd40, _hd41, _hd42, _hd43,
      _hd44, _hd45, _hd46, _hd48, _hd49, _hd50, _hd53⟩
  exact RD.solcExternalStaticArgsShortReverts hreach hd0 hd1 hd4 hd6 hd7 hd8 hd9
    hd11 hd12 hd13 hd14 hd17 hd18 hd20 hd21 hlt

set_option maxHeartbeats 1000000 in
theorem RD.addressAddressUint256ExternalMaskAndJumpMasked {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {entry ret routine de : UInt256} {R : List UInt256}
    {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0
      (uniswapAddressAddressUint256ExternalDecodedPc entry) (de :: ⟨4⟩ :: ret :: R)
      solcFreePtrMem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hwf : uniswapAddressAddressUint256ExternalEntryWf entry ret routine)
    (hroutine : (D_J UniswapV2Pair.uniswapV2PairBytecode 0).contains routine = true)
    (hov : R.length + 7 ≤ 1024) :
    ∃ k' C', RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 routine
      (calldataWord ee.calldata 68 :: UInt256.land solcAddrMask (calldataWord ee.calldata 36) ::
        UInt256.land solcAddrMask (calldataWord ee.calldata 4) :: ret :: R)
      solcFreePtrMem (UInt256.ofNat 3) rdata (cA, σ) k' C' := by
  rcases hwf with
    ⟨_hd0, _hd1, _hd4, _hd6, _hd7, _hd8, _hd9, _hd11, _hd12, _hd13, _hd14,
      _hd17, _hd18, _hd20, _hd21, hd22, hd23, hd24, hd26, hd28, hd30, hd31,
      hd32, hd33, hd34, hd35, hd36, hd37, hd39, hd40, hd41, hd42, hd43, hd44,
      hd45, hd46, hd48, hd49, hd50, hd53⟩
  exact RD.solcAddressAddressUint256ExternalMaskAndJumpMasked h hd22 hd23 hd24 hd26
    hd28 hd30 hd31 hd32 hd33 hd34 hd35 hd36 hd37 hd39 hd40 hd41 hd42 hd43 hd44
    hd45 hd46 hd48 hd49 hd50 hd53 hroutine hov

end UniswapV2Pair
