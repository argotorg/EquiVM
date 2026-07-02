import Examples.UniswapV2Pair.Common

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace UniswapV2Pair

/-! # Shared Uniswap V2 Pair storage helpers -/

/-! ## Single-mapping scratch memory -/

noncomputable abbrev uniswapMappingBaseSlotMem (baseSlot : UInt256) : ByteArray :=
  solcMappingBaseSlotMem baseSlot

noncomputable abbrev uniswapMappingHashMem (baseSlot key : UInt256) : ByteArray :=
  solcMappingHashMem baseSlot key

theorem uniswapMappingBaseSlotMem_size (baseSlot : UInt256) :
    (uniswapMappingBaseSlotMem baseSlot).size = 96 := by
  exact solcMappingBaseSlotMem_size baseSlot

theorem uniswapMappingHashMem_size (baseSlot key : UInt256) :
    (uniswapMappingHashMem baseSlot key).size = 96 := by
  exact solcMappingHashMem_size baseSlot key

theorem uniswapMappingBaseSlotMem_read32 (baseSlot : UInt256) :
    (uniswapMappingBaseSlotMem baseSlot).readWithPadding 32 32 =
      UInt256.toByteArray baseSlot := by
  exact solcMappingBaseSlotMem_read32 baseSlot

theorem uniswapMappingBaseSlotMem_read64 (baseSlot : UInt256) :
    (uniswapMappingBaseSlotMem baseSlot).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  exact solcMappingBaseSlotMem_read64 baseSlot

theorem uniswapMappingHashMem_read0 (baseSlot key : UInt256) :
    (uniswapMappingHashMem baseSlot key).readWithPadding 0 32 =
      UInt256.toByteArray key := by
  exact solcMappingHashMem_read0 baseSlot key

theorem uniswapMappingHashMem_read32 (baseSlot key : UInt256) :
    (uniswapMappingHashMem baseSlot key).readWithPadding 32 32 =
      UInt256.toByteArray baseSlot := by
  exact solcMappingHashMem_read32 baseSlot key

theorem uniswapMappingHashMem_read64 (baseSlot key : UInt256) :
    (uniswapMappingHashMem baseSlot key).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  exact solcMappingHashMem_read64 baseSlot key

theorem uniswapMappingHashMem_mload64 (baseSlot key : UInt256) :
    (if (⟨64⟩ : UInt256).toNat ≥ (uniswapMappingHashMem baseSlot key).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 3 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((uniswapMappingHashMem baseSlot key).readWithPadding (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ := by
  exact solcMappingHashMem_mload64 baseSlot key

set_option maxHeartbeats 800000 in
theorem uniswapMappingHashMem_read0_64 (baseSlot key : UInt256) :
    (uniswapMappingHashMem baseSlot key).readWithPadding 0 64 =
      UInt256.toByteArray key ++ UInt256.toByteArray baseSlot := by
  exact solcMappingHashMem_read0_64 baseSlot key

theorem uniswapMappingKeccakSlot (baseSlot key : UInt256) :
    UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((uniswapMappingHashMem baseSlot key).readWithPadding 0 64)))
      = mapSlot key baseSlot := by
  simpa [mapSlot] using solcMappingKeccakSlot baseSlot key

/-! ## Return memory after a mapping getter -/

noncomputable abbrev uniswapMappingReturnMem (baseSlot key val : UInt256) : ByteArray :=
  solcScratchReturnMem (uniswapMappingHashMem baseSlot key) val

theorem uniswapMappingReturnMem_size (baseSlot key val : UInt256) :
    (uniswapMappingReturnMem baseSlot key val).size = 160 := by
  exact solcScratchReturnMem_size val (uniswapMappingHashMem_size baseSlot key)

theorem uniswapMappingReturnMem_read64 (baseSlot key val : UInt256) :
    (uniswapMappingReturnMem baseSlot key val).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  exact solcScratchReturnMem_read64 val (uniswapMappingHashMem_size baseSlot key)
    (uniswapMappingHashMem_read64 baseSlot key)

theorem uniswapMappingReturnMem_mload64 (baseSlot key val : UInt256) :
    (if (⟨64⟩ : UInt256).toNat ≥ (uniswapMappingReturnMem baseSlot key val).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 5 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((uniswapMappingReturnMem baseSlot key val).readWithPadding
          (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ := by
  exact solcScratchReturnMem_mload64 val (uniswapMappingHashMem_size baseSlot key)
    (uniswapMappingHashMem_read64 baseSlot key)

theorem uniswapMappingReturnMem_read128 (baseSlot key val : UInt256) :
    (uniswapMappingReturnMem baseSlot key val).readWithPadding 128 32 =
      UInt256.toByteArray val := by
  exact solcScratchReturnMem_read128 val (uniswapMappingHashMem_size baseSlot key)

/-! ## Nested-mapping scratch memory -/

noncomputable abbrev uniswapNestedMappingOuterBaseMem (baseSlot owner : UInt256) : ByteArray :=
  solcNestedMappingOuterBaseMem baseSlot owner

noncomputable abbrev uniswapNestedMappingHashMem
    (baseSlot owner spender : UInt256) : ByteArray :=
  solcNestedMappingHashMem baseSlot owner spender

theorem uniswapNestedMappingOuterBaseMem_size (baseSlot owner : UInt256) :
    (uniswapNestedMappingOuterBaseMem baseSlot owner).size = 96 := by
  exact solcNestedMappingOuterBaseMem_size baseSlot owner

theorem uniswapNestedMappingHashMem_size (baseSlot owner spender : UInt256) :
    (uniswapNestedMappingHashMem baseSlot owner spender).size = 96 := by
  exact solcNestedMappingHashMem_size baseSlot owner spender

theorem uniswapNestedMappingOuterBaseMem_read32 (baseSlot owner : UInt256) :
    (uniswapNestedMappingOuterBaseMem baseSlot owner).readWithPadding 32 32 =
      UInt256.toByteArray (mapSlot owner baseSlot) := by
  simpa [mapSlot, solcMappingSlot] using
    solcNestedMappingOuterBaseMem_read32 baseSlot owner

theorem uniswapNestedMappingOuterBaseMem_read64 (baseSlot owner : UInt256) :
    (uniswapNestedMappingOuterBaseMem baseSlot owner).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  exact solcNestedMappingOuterBaseMem_read64 baseSlot owner

theorem uniswapNestedMappingHashMem_read0 (baseSlot owner spender : UInt256) :
    (uniswapNestedMappingHashMem baseSlot owner spender).readWithPadding 0 32 =
      UInt256.toByteArray spender := by
  exact solcNestedMappingHashMem_read0 baseSlot owner spender

theorem uniswapNestedMappingHashMem_read32 (baseSlot owner spender : UInt256) :
    (uniswapNestedMappingHashMem baseSlot owner spender).readWithPadding 32 32 =
      UInt256.toByteArray (mapSlot owner baseSlot) := by
  simpa [mapSlot, solcMappingSlot] using
    solcNestedMappingHashMem_read32 baseSlot owner spender

theorem uniswapNestedMappingHashMem_read64 (baseSlot owner spender : UInt256) :
    (uniswapNestedMappingHashMem baseSlot owner spender).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  exact solcNestedMappingHashMem_read64 baseSlot owner spender

theorem uniswapNestedMappingHashMem_mload64 (baseSlot owner spender : UInt256) :
    (if (⟨64⟩ : UInt256).toNat ≥ (uniswapNestedMappingHashMem baseSlot owner spender).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 3 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((uniswapNestedMappingHashMem baseSlot owner spender).readWithPadding
          (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ := by
  exact solcNestedMappingHashMem_mload64 baseSlot owner spender

set_option maxHeartbeats 800000 in
theorem uniswapNestedMappingHashMem_read0_64 (baseSlot owner spender : UInt256) :
    (uniswapNestedMappingHashMem baseSlot owner spender).readWithPadding 0 64 =
      UInt256.toByteArray spender ++ UInt256.toByteArray (mapSlot owner baseSlot) := by
  simpa [mapSlot, solcMappingSlot] using
    solcNestedMappingHashMem_read0_64 baseSlot owner spender

theorem uniswapNestedMappingKeccakSlot (baseSlot owner spender : UInt256) :
    UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((uniswapNestedMappingHashMem baseSlot owner spender).readWithPadding 0 64)))
      = mapSlot spender (mapSlot owner baseSlot) := by
  simpa [mapSlot, solcMappingSlot] using
    solcNestedMappingKeccakSlot baseSlot owner spender

/-! ## Return memory after a nested-mapping getter -/

noncomputable abbrev uniswapNestedMappingReturnMem
    (baseSlot owner spender val : UInt256) : ByteArray :=
  solcScratchReturnMem (uniswapNestedMappingHashMem baseSlot owner spender) val

theorem uniswapNestedMappingReturnMem_size (baseSlot owner spender val : UInt256) :
    (uniswapNestedMappingReturnMem baseSlot owner spender val).size = 160 := by
  exact solcScratchReturnMem_size val
    (uniswapNestedMappingHashMem_size baseSlot owner spender)

theorem uniswapNestedMappingReturnMem_read64 (baseSlot owner spender val : UInt256) :
    (uniswapNestedMappingReturnMem baseSlot owner spender val).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  exact solcScratchReturnMem_read64 val
    (uniswapNestedMappingHashMem_size baseSlot owner spender)
    (uniswapNestedMappingHashMem_read64 baseSlot owner spender)

theorem uniswapNestedMappingReturnMem_mload64 (baseSlot owner spender val : UInt256) :
    (if (⟨64⟩ : UInt256).toNat ≥ (uniswapNestedMappingReturnMem baseSlot owner spender val).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 5 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((uniswapNestedMappingReturnMem baseSlot owner spender val).readWithPadding
          (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ := by
  exact solcScratchReturnMem_mload64 val
    (uniswapNestedMappingHashMem_size baseSlot owner spender)
    (uniswapNestedMappingHashMem_read64 baseSlot owner spender)

theorem uniswapNestedMappingReturnMem_read128 (baseSlot owner spender val : UInt256) :
    (uniswapNestedMappingReturnMem baseSlot owner spender val).readWithPadding 128 32 =
      UInt256.toByteArray val := by
  exact solcScratchReturnMem_read128 val
    (uniswapNestedMappingHashMem_size baseSlot owner spender)

end UniswapV2Pair

namespace Reasoning.Reach

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

/-! ## Shared single-mapping getter routine -/

/-- Bytecode shape for Uniswap's optimized single-mapping getter routines.

The routine stores the base slot at scratch offset `0x20`, stores the key at `0x00`, hashes the
64-byte preimage, loads storage, duplicates the dynamic return address, and jumps back.
-/
@[reducible] def uniswapSingleMappingGetterWf (pc baseSlot : UInt256) : Prop :=
  solcSingleMappingGetterWf UniswapV2Pair.uniswapV2PairBytecode pc baseSlot

/-- Discharge a concrete Uniswap single-mapping getter bytecode-shape proof. -/
macro "uniswap_single_mapping_getter_wf" : term =>
  `(by
    unfold Reasoning.Reach.uniswapSingleMappingGetterWf
      Reasoning.Reach.solcSingleMappingGetterWf
    repeat' first | apply And.intro | native_decide)

/-! ## Shared nested-mapping getter routine -/

/-- Bytecode shape for Uniswap's optimized nested-mapping getter routine.

The routine computes `keccak(owner, baseSlot)`, then `keccak(spender, innerSlot)`, loads storage,
duplicates the dynamic return address, and jumps back.
-/
@[reducible] def uniswapNestedMappingGetterWf (pc baseSlot : UInt256) : Prop :=
  solcNestedMappingGetterWf UniswapV2Pair.uniswapV2PairBytecode pc baseSlot

/-- PC of the `SLOAD` in Uniswap's optimized nested-mapping getter routine. -/
@[reducible] def uniswapNestedMappingGetterSloadPc (pc : UInt256) : UInt256 :=
  solcNestedMappingGetterSloadPc pc

/-- PC immediately after the first `KECCAK256` in Uniswap's nested-mapping getter routine. -/
@[reducible] def uniswapNestedMappingGetterAfterInnerHashPc (pc : UInt256) : UInt256 :=
  solcNestedMappingGetterAfterInnerHashPc pc

/-- Discharge a concrete Uniswap nested-mapping getter bytecode-shape proof. -/
macro "uniswap_nested_mapping_getter_wf" : term =>
  `(by
    unfold Reasoning.Reach.uniswapNestedMappingGetterWf
      Reasoning.Reach.solcNestedMappingGetterWf
    repeat' first | apply And.intro | native_decide)

/-! ## Shared one-address external getter entry -/

/-- PC of the post-length-check decode block in Uniswap's optimized one-address getter wrapper. -/
@[reducible] def uniswapOneAddressGetterDecodedPc (pc : UInt256) : UInt256 :=
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
  p21 + ⟨1⟩

/-- Bytecode shape for Uniswap's optimized external one-address getter wrappers.

The wrapper checks that at least one static ABI word is present, masks the address word, and jumps
to a mapping getter routine with return wrapper pc `861`.
-/
@[reducible] def uniswapOneAddressGetterEntryWf (pc routine : UInt256) : Prop :=
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
  let p22 := uniswapOneAddressGetterDecodedPc pc
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
      some (.Push .PUSH2, some (⟨861⟩, 2))
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

/-- Discharge a concrete Uniswap one-address getter entry bytecode-shape proof. -/
macro "uniswap_one_address_getter_entry_wf" : term =>
  `(by
    unfold Reasoning.Reach.uniswapOneAddressGetterEntryWf
    repeat' first | apply And.intro | native_decide)

set_option maxHeartbeats 1000000 in
theorem RD.uniswapOneAddressGetterLenOk {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    {entry routine : UInt256}
    (hreach : ∃ k C, RD UniswapV2Pair.uniswapV2PairBytecode I g
      (Reasoning.Theory.initState cA gh bl σ σ₀ g A I) entry [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hwf : uniswapOneAddressGetterEntryWf entry routine)
    (hdecoded : (D_J UniswapV2Pair.uniswapV2PairBytecode 0).contains
      (uniswapOneAddressGetterDecodedPc entry) = true)
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size) :
    ∃ k C, RD UniswapV2Pair.uniswapV2PairBytecode I g
      (Reasoning.Theory.initState cA gh bl σ σ₀ g A I)
      (uniswapOneAddressGetterDecodedPc entry)
      (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩ :: ⟨4⟩ :: ⟨861⟩ :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  rcases hwf with
    ⟨hd0, hd1, hd4, hd6, hd7, hd8, hd9, hd11, hd12, hd13, hd14, hd17, _hd18,
      _hd20, _hd21, hd22, _hd23, _hd24, _hd25, _hd27, _hd29, _hd31, _hd32, _hd33,
      _hd34, _hd37⟩
  exact RD.solcOneAddressExternalLenOk hreach hd0 hd1 hd4 hd6 hd7 hd8 hd9 hd11 hd12
    hd13 hd14 hd17 hdecoded hsz36 hsize

set_option maxHeartbeats 1000000 in
theorem RD.uniswapOneAddressGetterMaskAndJump {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {entry routine de : UInt256} {R : List UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0
      (uniswapOneAddressGetterDecodedPc entry) (de :: ⟨4⟩ :: ⟨861⟩ :: R)
      solcFreePtrMem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hwf : uniswapOneAddressGetterEntryWf entry routine)
    (hcanon : (calldataWord ee.calldata 4).toNat < EVM.addressModulus)
    (hroutine : (D_J UniswapV2Pair.uniswapV2PairBytecode 0).contains routine = true)
    (hov : R.length + 5 ≤ 1024) :
    ∃ k' C', RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 routine
      (calldataWord ee.calldata 4 :: ⟨861⟩ :: R)
      solcFreePtrMem (UInt256.ofNat 3) rdata (cA, σ) k' C' := by
  rcases hwf with
    ⟨_hd0, _hd1, _hd4, _hd6, _hd7, _hd8, _hd9, _hd11, _hd12, _hd13, _hd14, _hd17,
      _hd18, _hd20, _hd21, hd22, hd23, hd24, hd25, hd27, hd29, hd31, hd32, hd33,
      hd34, hd37⟩
  exact RD.solcOneAddressExternalMaskAndJump h hd22 hd23 hd24 hd25 hd27 hd29 hd31 hd32
    hd33 hd34 hd37 hcanon hroutine hov

set_option maxHeartbeats 1000000 in
theorem RD.uniswapOneAddressGetterMaskAndJumpMasked {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {entry routine de : UInt256} {R : List UInt256}
    {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0
      (uniswapOneAddressGetterDecodedPc entry) (de :: ⟨4⟩ :: ⟨861⟩ :: R)
      solcFreePtrMem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hwf : uniswapOneAddressGetterEntryWf entry routine)
    (hroutine : (D_J UniswapV2Pair.uniswapV2PairBytecode 0).contains routine = true)
    (hov : R.length + 5 ≤ 1024) :
    ∃ k' C', RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 routine
      (UInt256.land solcAddrMask (calldataWord ee.calldata 4) :: ⟨861⟩ :: R)
      solcFreePtrMem (UInt256.ofNat 3) rdata (cA, σ) k' C' := by
  rcases hwf with
    ⟨_hd0, _hd1, _hd4, _hd6, _hd7, _hd8, _hd9, _hd11, _hd12, _hd13, _hd14,
      _hd17, _hd18, _hd20, _hd21, hd22, hd23, hd24, hd25, hd27, hd29, hd31,
      hd32, hd33, hd34, hd37⟩
  exact RD.solcOneAddressExternalMaskAndJumpMasked h hd22 hd23 hd24 hd25 hd27 hd29 hd31
    hd32 hd33 hd34 hd37 hroutine hov

/-! ## Shared two-address external getter entry -/

/-- PC of the post-length-check decode block in Uniswap's optimized two-address getter wrapper. -/
@[reducible] def uniswapTwoAddressGetterDecodedPc (pc : UInt256) : UInt256 :=
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
  p21 + ⟨1⟩

/-- Bytecode shape for Uniswap's optimized external two-address getter wrapper.

The wrapper checks that two static ABI words are present, masks both address words, and jumps to a
nested-mapping getter routine with return wrapper pc `861`.
-/
@[reducible] def uniswapTwoAddressGetterEntryWf (pc routine : UInt256) : Prop :=
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
  let p22 := uniswapTwoAddressGetterDecodedPc pc
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
      some (.Push .PUSH2, some (⟨861⟩, 2))
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

/-- Discharge a concrete Uniswap two-address getter entry bytecode-shape proof. -/
macro "uniswap_two_address_getter_entry_wf" : term =>
  `(by
    unfold Reasoning.Reach.uniswapTwoAddressGetterEntryWf
    repeat' first | apply And.intro | native_decide)

set_option maxHeartbeats 1000000 in
theorem RD.uniswapTwoAddressGetterLenOk {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    {entry routine : UInt256}
    (hreach : ∃ k C, RD UniswapV2Pair.uniswapV2PairBytecode I g
      (Reasoning.Theory.initState cA gh bl σ σ₀ g A I) entry [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hwf : uniswapTwoAddressGetterEntryWf entry routine)
    (hdecoded : (D_J UniswapV2Pair.uniswapV2PairBytecode 0).contains
      (uniswapTwoAddressGetterDecodedPc entry) = true)
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size) :
    ∃ k C, RD UniswapV2Pair.uniswapV2PairBytecode I g
      (Reasoning.Theory.initState cA gh bl σ σ₀ g A I)
      (uniswapTwoAddressGetterDecodedPc entry)
      (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩ :: ⟨4⟩ :: ⟨861⟩ :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  rcases hwf with
    ⟨hd0, hd1, hd4, hd6, hd7, hd8, hd9, hd11, hd12, hd13, hd14, hd17, _hd18,
      _hd20, _hd21, hd22, _hd23, _hd24, _hd26, _hd28, _hd30, _hd31, _hd32,
      _hd33, _hd34, _hd35, _hd36, _hd37, _hd39, _hd40, _hd41, _hd42, _hd45⟩
  exact RD.solcTwoAddressExternalLenOk hreach hd0 hd1 hd4 hd6 hd7 hd8 hd9 hd11 hd12
    hd13 hd14 hd17 hdecoded hsz68 hsize

set_option maxHeartbeats 1000000 in
theorem RD.uniswapTwoAddressGetterMaskAndJump {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {entry routine de : UInt256} {R : List UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0
      (uniswapTwoAddressGetterDecodedPc entry) (de :: ⟨4⟩ :: ⟨861⟩ :: R)
      solcFreePtrMem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hwf : uniswapTwoAddressGetterEntryWf entry routine)
    (hcanonOwner : (calldataWord ee.calldata 4).toNat < EVM.addressModulus)
    (hcanonSpender : (calldataWord ee.calldata 36).toNat < EVM.addressModulus)
    (hroutine : (D_J UniswapV2Pair.uniswapV2PairBytecode 0).contains routine = true)
    (hov : R.length + 7 ≤ 1024) :
    ∃ k' C', RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 routine
      (calldataWord ee.calldata 36 :: calldataWord ee.calldata 4 :: ⟨861⟩ :: R)
      solcFreePtrMem (UInt256.ofNat 3) rdata (cA, σ) k' C' := by
  rcases hwf with
    ⟨_hd0, _hd1, _hd4, _hd6, _hd7, _hd8, _hd9, _hd11, _hd12, _hd13, _hd14,
      _hd17, _hd18, _hd20, _hd21, hd22, hd23, hd24, hd26, hd28, hd30, hd31,
      hd32, hd33, hd34, hd35, hd36, hd37, hd39, hd40, hd41, hd42, hd45⟩
  exact RD.solcTwoAddressExternalMaskAndJump h hd22 hd23 hd24 hd26 hd28 hd30 hd31
    hd32 hd33 hd34 hd35 hd36 hd37 hd39 hd40 hd41 hd42 hd45 hcanonOwner hcanonSpender
    hroutine hov

set_option maxHeartbeats 1000000 in
theorem RD.uniswapTwoAddressGetterMaskAndJumpMasked {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {entry routine de : UInt256} {R : List UInt256}
    {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0
      (uniswapTwoAddressGetterDecodedPc entry) (de :: ⟨4⟩ :: ⟨861⟩ :: R)
      solcFreePtrMem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hwf : uniswapTwoAddressGetterEntryWf entry routine)
    (hroutine : (D_J UniswapV2Pair.uniswapV2PairBytecode 0).contains routine = true)
    (hov : R.length + 7 ≤ 1024) :
    ∃ k' C', RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 routine
      (UInt256.land solcAddrMask (calldataWord ee.calldata 36) ::
        UInt256.land solcAddrMask (calldataWord ee.calldata 4) :: ⟨861⟩ :: R)
      solcFreePtrMem (UInt256.ofNat 3) rdata (cA, σ) k' C' := by
  rcases hwf with
    ⟨_hd0, _hd1, _hd4, _hd6, _hd7, _hd8, _hd9, _hd11, _hd12, _hd13, _hd14,
      _hd17, _hd18, _hd20, _hd21, hd22, hd23, hd24, hd26, hd28, hd30, hd31,
      hd32, hd33, hd34, hd35, hd36, hd37, hd39, hd40, hd41, hd42, hd45⟩
  exact RD.solcTwoAddressExternalMaskAndJumpMasked h hd22 hd23 hd24 hd26 hd28 hd30 hd31
    hd32 hd33 hd34 hd35 hd36 hd37 hd39 hd40 hd41 hd42 hd45 hroutine hov

theorem RD.uniswapSingleMappingGetter {g : Sat256} {s0 : State} {ee : ExecutionEnv} {k C : ℕ}
    {pc baseSlot key ret : UInt256} {R : List UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 pc (key :: ret :: R)
        solcFreePtrMem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hwf : uniswapSingleMappingGetterWf pc baseSlot)
    (hret : (D_J UniswapV2Pair.uniswapV2PairBytecode 0).contains ret = true)
    (hov : R.length + 4 ≤ 1024) :
    ∃ k' C', RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ret
      ((σ.find? ee.codeOwner |>.option ⟨0⟩
          (fun acc => acc.storage.findD (UniswapV2Pair.mapSlot key baseSlot) ⟨0⟩))
        :: ret :: R)
      (UniswapV2Pair.uniswapMappingHashMem baseSlot key)
      (UInt256.ofNat 3) rdata (cA, σ) k' C' := by
  simpa [solcSlotWord, UniswapV2Pair.uniswapMappingHashMem, UniswapV2Pair.mapSlot,
    solcMappingSlot] using RD.solcSingleMappingGetter h hwf hret hov

set_option maxHeartbeats 3000000 in
theorem RD.uniswapNestedMappingInnerHash {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ}
    {pc baseSlot owner spender ret : UInt256} {R : List UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 pc (spender :: owner :: ret :: R)
        solcFreePtrMem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hwf : uniswapNestedMappingGetterWf pc baseSlot)
    (hov : R.length + 7 ≤ 1024) :
    ∃ k' C', RD UniswapV2Pair.uniswapV2PairBytecode ee g s0
      (uniswapNestedMappingGetterAfterInnerHashPc pc)
      (UniswapV2Pair.mapSlot owner baseSlot :: ⟨64⟩ :: ⟨32⟩ :: spender :: ⟨0⟩ :: ret :: R)
      (UniswapV2Pair.uniswapMappingHashMem baseSlot owner)
      (UInt256.ofNat 3) rdata (cA, σ) k' C' := by
  simpa [uniswapNestedMappingGetterAfterInnerHashPc, UniswapV2Pair.uniswapMappingHashMem,
    UniswapV2Pair.mapSlot, solcMappingSlot] using
      RD.solcNestedMappingInnerHash h hwf hov

set_option maxHeartbeats 1000000 in
theorem RD.uniswapNestedMappingOuterHash {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ}
    {pc baseSlot owner spender ret : UInt256} {R : List UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0
      (uniswapNestedMappingGetterAfterInnerHashPc pc)
      (UniswapV2Pair.mapSlot owner baseSlot :: ⟨64⟩ :: ⟨32⟩ :: spender :: ⟨0⟩ :: ret :: R)
      (UniswapV2Pair.uniswapMappingHashMem baseSlot owner)
      (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hwf : uniswapNestedMappingGetterWf pc baseSlot)
    (hov : R.length + 7 ≤ 1024) :
    ∃ k' C', RD UniswapV2Pair.uniswapV2PairBytecode ee g s0
      (uniswapNestedMappingGetterSloadPc pc)
      (UniswapV2Pair.mapSlot spender (UniswapV2Pair.mapSlot owner baseSlot) :: ret :: R)
      (UniswapV2Pair.uniswapNestedMappingHashMem baseSlot owner spender)
      (UInt256.ofNat 3) rdata (cA, σ) k' C' := by
  simpa [uniswapNestedMappingGetterAfterInnerHashPc, uniswapNestedMappingGetterSloadPc,
    UniswapV2Pair.uniswapMappingHashMem, UniswapV2Pair.uniswapNestedMappingOuterBaseMem,
    UniswapV2Pair.uniswapNestedMappingHashMem, UniswapV2Pair.mapSlot, solcMappingSlot] using
      RD.solcNestedMappingOuterHash h hwf hov

theorem RD.uniswapNestedMappingLoadAndJump {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {pc baseSlot slot ret : UInt256} {R : List UInt256} {mem : ByteArray}
    {aw : UInt256} {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare}
    {σ : AccountMap}
    (h : RD UniswapV2Pair.uniswapV2PairBytecode ee g s0
      (uniswapNestedMappingGetterSloadPc pc) (slot :: ret :: R) mem aw rdata (cA, σ) k C)
    (hwf : uniswapNestedMappingGetterWf pc baseSlot)
    (hret : (D_J UniswapV2Pair.uniswapV2PairBytecode 0).contains ret = true)
    (hov : R.length + 3 ≤ 1024) :
    ∃ k' C', RD UniswapV2Pair.uniswapV2PairBytecode ee g s0 ret
      ((σ.find? ee.codeOwner |>.option ⟨0⟩
          (fun acc => acc.storage.findD slot ⟨0⟩)) :: ret :: R)
      mem aw rdata (cA, σ) k' C' := by
  simpa [solcSlotWord, uniswapNestedMappingGetterSloadPc] using
    RD.solcNestedMappingLoadAndJump h hwf hret hov

end Reasoning.Reach
