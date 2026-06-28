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
    repeat' first | apply And.intro | native_decide)

-- GENERALIZES Reasoning.Reach.RD.uniswapOneAddressGetterLenOk -
-- parameterizes the continuation pc instead of hardcoding Uniswap's one-word return wrapper at
-- pc 861.
-- LIBRARY CANDIDATE: Reasoning.Reach - first half of an optimizer-on solc one-address external
-- wrapper, parameterized by bytecode, entry PC, continuation PC, and target routine.
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
  obtain ⟨_, _, rdEntry⟩ := hreach
  rcases hwf with
    ⟨hd0, hd1, hd4, hd6, hd7, hd8, hd9, hd11, hd12, hd13, hd14, hd17, _hd18,
      _hd20, _hd21, hd22, _hd23, _hd24, _hd25, _hd27, _hd29, _hd31, _hd32,
      _hd33, _hd34, _hd37⟩
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨0⟩ :=
    UniswapV2Pair.uniswapDecodeLenCheckOk_4_32_lt hsz36 hsize
  have hjumpCond :
      UInt256.isZero (UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩) ≠
        ⟨0⟩ := by
    rw [hlt]
    decide
  have rd1 := rdEntry.jumpdest hd0 (by simp only [List.length_singleton]; omega)
  have rd4 := rd1.push2 ret hd1 (by evm_ov)
  have rd6 := rd4.push1 ⟨4⟩ hd4 (by evm_ov)
  have rd7 := rd6.dup1 hd6 (by evm_ov)
  have rd8 := rd7.calldatasize hd7 (by evm_ov)
  have rd9 := rd8.sub hd8 (by evm_ov)
  have rd11 := rd9.push1 ⟨32⟩ hd9 (by evm_ov)
  have rd12 := rd11.dup2 hd11 (by evm_ov)
  have rd13 := rd12.lt hd12 (by evm_ov)
  have rd14 := rd13.iszero hd13 (by evm_ov)
  have rd17 := rd14.push2 (uniswapOneAddressExternalDecodedPc entry) hd14 (by evm_ov)
  exact ⟨_, _, rd17.jumpiT hd17 hjumpCond hdecoded (by evm_ov)⟩

-- GENERALIZES Reasoning.Reach.RD.uniswapOneAddressGetterMaskAndJump -
-- parameterizes the continuation pc instead of hardcoding Uniswap's one-word return wrapper at
-- pc 861.
-- LIBRARY CANDIDATE: Reasoning.Reach - second half of an optimizer-on solc one-address external
-- wrapper, parameterized by bytecode, entry PC, continuation PC, and target routine.
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
  have hmask :
      UInt256.land (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩)
          (calldataWord ee.calldata 4) =
        calldataWord ee.calldata 4 := by
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide]
    exact solcAddrMask_clean_left hcanon
  have rd23 := h.jumpdest hd22 (by evm_ov)
  have rd24 := rd23.pop hd23 (by evm_ov)
  have rd25 := rd24.calldataload hd24 (by evm_ov)
  have rd27 := rd25.push1 ⟨1⟩ hd25 (by evm_ov)
  have rd29 := rd27.push1 ⟨1⟩ hd27 (by evm_ov)
  have rd31 := rd29.push1 ⟨160⟩ hd29 (by evm_ov)
  have rd32 := rd31.shl hd31 (by evm_ov)
  have rd33 := rd32.sub hd32 (by evm_ov)
  have rd34 := rd33.and hd33 (by evm_ov)
  have rd37 := rd34.push2 routine hd34 (by evm_ov)
  exact ⟨_, _, by
    simpa [calldataWord, show (⟨4⟩ : UInt256).toNat = 4 from by decide, hmask]
      using rd37.jump hd37 hroutine (by evm_ov)⟩

-- GENERALIZES Reasoning.Reach.RD.uniswapOneAddressGetterLenOk -
-- same optimized one-address ABI wrapper prefix, but with a parameterized continuation pc.
-- LIBRARY CANDIDATE: Reasoning.Reach - optimizer-on solc one-address external wrapper
-- short-calldata revert, parameterized by bytecode, entry PC, continuation PC, and target routine.
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
  obtain ⟨_, _, rdEntry⟩ := hreach
  rcases hwf with
    ⟨hd0, hd1, hd4, hd6, hd7, hd8, hd9, hd11, hd12, hd13, hd14, hd17, hd18,
      hd20, hd21, _hd22, _hd23, _hd24, _hd25, _hd27, _hd29, _hd31, _hd32,
      _hd33, _hd34, _hd37⟩
  have rd1 := rdEntry.jumpdest hd0 (by simp only [List.length_singleton]; omega)
  have rd4 := rd1.push2 ret hd1 (by evm_ov)
  have rd6 := rd4.push1 ⟨4⟩ hd4 (by evm_ov)
  have rd7 := rd6.dup1 hd6 (by evm_ov)
  have rd8 := rd7.calldatasize hd7 (by evm_ov)
  have rd9 := rd8.sub hd8 (by evm_ov)
  have rd11 := rd9.push1 ⟨32⟩ hd9 (by evm_ov)
  have rd12 := rd11.dup2 hd11 (by evm_ov)
  have rd13₀ := rd12.lt hd12 (by evm_ov)
  have rd13 := rd13₀
  rw [hlt] at rd13
  have rd14₀ := rd13.iszero hd13 (by evm_ov)
  have rd14 := rd14₀
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd14
  have rd17 := rd14.push2 (uniswapOneAddressExternalDecodedPc entry) hd14 (by evm_ov)
  have rd18 := rd17.jumpiNT hd17 (by decide : (⟨0⟩ : UInt256) = ⟨0⟩) (by evm_ov)
  have rd20 := rd18.push1 ⟨0⟩ hd18 (by evm_ov)
  have rd21 := rd20.dup1 hd20 (by evm_ov)
  exact rd21.rev 0 hd21 mem_cost (by evm_ov)

-- GENERALIZES Reasoning.Reach.RD.uniswapOneAddressGetterLenOk -
-- same optimized one-address getter wrapper prefix, but the failing short-calldata branch.
-- LIBRARY CANDIDATE: Reasoning.Reach - optimizer-on solc one-address getter wrapper
-- short-calldata revert, parameterized by bytecode, entry PC, and target routine.
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
  obtain ⟨_, _, rdEntry⟩ := hreach
  rcases hwf with
    ⟨hd0, hd1, hd4, hd6, hd7, hd8, hd9, hd11, hd12, hd13, hd14, hd17, hd18,
      hd20, hd21, _hd22, _hd23, _hd24, _hd25, _hd27, _hd29, _hd31, _hd32,
      _hd33, _hd34, _hd37⟩
  have rd1 := rdEntry.jumpdest hd0 (by simp only [List.length_singleton]; omega)
  have rd4 := rd1.push2 ⟨861⟩ hd1 (by evm_ov)
  have rd6 := rd4.push1 ⟨4⟩ hd4 (by evm_ov)
  have rd7 := rd6.dup1 hd6 (by evm_ov)
  have rd8 := rd7.calldatasize hd7 (by evm_ov)
  have rd9 := rd8.sub hd8 (by evm_ov)
  have rd11 := rd9.push1 ⟨32⟩ hd9 (by evm_ov)
  have rd12 := rd11.dup2 hd11 (by evm_ov)
  have rd13₀ := rd12.lt hd12 (by evm_ov)
  have rd13 := rd13₀
  rw [hlt] at rd13
  have rd14₀ := rd13.iszero hd13 (by evm_ov)
  have rd14 := rd14₀
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd14
  have rd17 := rd14.push2 (uniswapOneAddressGetterDecodedPc entry) hd14 (by evm_ov)
  have rd18 := rd17.jumpiNT hd17 (by decide : (⟨0⟩ : UInt256) = ⟨0⟩) (by evm_ov)
  have rd20 := rd18.push1 ⟨0⟩ hd18 (by evm_ov)
  have rd21 := rd20.dup1 hd20 (by evm_ov)
  exact rd21.rev 0 hd21 mem_cost (by evm_ov)

-- GENERALIZES Reasoning.Reach.RD.uniswapTwoAddressGetterLenOk -
-- same optimized two-address getter wrapper prefix, but the failing short-calldata branch.
-- LIBRARY CANDIDATE: Reasoning.Reach - optimizer-on solc two-address getter wrapper
-- short-calldata revert, parameterized by bytecode, entry PC, and target routine.
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
  obtain ⟨_, _, rdEntry⟩ := hreach
  rcases hwf with
    ⟨hd0, hd1, hd4, hd6, hd7, hd8, hd9, hd11, hd12, hd13, hd14, hd17, hd18,
      hd20, hd21, _hd22, _hd23, _hd24, _hd26, _hd28, _hd30, _hd31, _hd32,
      _hd33, _hd34, _hd35, _hd36, _hd37, _hd39, _hd40, _hd41, _hd42, _hd45⟩
  have rd1 := rdEntry.jumpdest hd0 (by simp only [List.length_singleton]; omega)
  have rd4 := rd1.push2 ⟨861⟩ hd1 (by evm_ov)
  have rd6 := rd4.push1 ⟨4⟩ hd4 (by evm_ov)
  have rd7 := rd6.dup1 hd6 (by evm_ov)
  have rd8 := rd7.calldatasize hd7 (by evm_ov)
  have rd9 := rd8.sub hd8 (by evm_ov)
  have rd11 := rd9.push1 ⟨64⟩ hd9 (by evm_ov)
  have rd12 := rd11.dup2 hd11 (by evm_ov)
  have rd13₀ := rd12.lt hd12 (by evm_ov)
  have rd13 := rd13₀
  rw [hlt] at rd13
  have rd14₀ := rd13.iszero hd13 (by evm_ov)
  have rd14 := rd14₀
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd14
  have rd17 := rd14.push2 (uniswapTwoAddressGetterDecodedPc entry) hd14 (by evm_ov)
  have rd18 := rd17.jumpiNT hd17 (by decide : (⟨0⟩ : UInt256) = ⟨0⟩) (by evm_ov)
  have rd20 := rd18.push1 ⟨0⟩ hd18 (by evm_ov)
  have rd21 := rd20.dup1 hd20 (by evm_ov)
  exact rd21.rev 0 hd21 mem_cost (by evm_ov)

-- GENERALIZES Examples.UniswapV2Pair.Routines.RD.uniswapTwoAddressExternalLenOk -
-- same optimized two-address external wrapper prefix, but the failing short-calldata branch.
-- LIBRARY CANDIDATE: Reasoning.Reach - optimizer-on solc two-address external wrapper
-- short-calldata revert, parameterized by bytecode, entry PC, continuation PC, and target routine.
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
  obtain ⟨_, _, rdEntry⟩ := hreach
  rcases hwf with
    ⟨hd0, hd1, hd4, hd6, hd7, hd8, hd9, hd11, hd12, hd13, hd14, hd17, hd18,
      hd20, hd21, _hd22, _hd23, _hd24, _hd26, _hd28, _hd30, _hd31, _hd32,
      _hd33, _hd34, _hd35, _hd36, _hd37, _hd39, _hd40, _hd41, _hd42, _hd45⟩
  have rd1 := rdEntry.jumpdest hd0 (by simp only [List.length_singleton]; omega)
  have rd4 := rd1.push2 ret hd1 (by evm_ov)
  have rd6 := rd4.push1 ⟨4⟩ hd4 (by evm_ov)
  have rd7 := rd6.dup1 hd6 (by evm_ov)
  have rd8 := rd7.calldatasize hd7 (by evm_ov)
  have rd9 := rd8.sub hd8 (by evm_ov)
  have rd11 := rd9.push1 ⟨64⟩ hd9 (by evm_ov)
  have rd12 := rd11.dup2 hd11 (by evm_ov)
  have rd13₀ := rd12.lt hd12 (by evm_ov)
  have rd13 := rd13₀
  rw [hlt] at rd13
  have rd14₀ := rd13.iszero hd13 (by evm_ov)
  have rd14 := rd14₀
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd14
  have rd17 := rd14.push2 (uniswapTwoAddressExternalDecodedPc entry) hd14 (by evm_ov)
  have rd18 := rd17.jumpiNT hd17 (by decide : (⟨0⟩ : UInt256) = ⟨0⟩) (by evm_ov)
  have rd20 := rd18.push1 ⟨0⟩ hd18 (by evm_ov)
  have rd21 := rd20.dup1 hd20 (by evm_ov)
  exact rd21.rev 0 hd21 mem_cost (by evm_ov)

-- GENERALIZES Reasoning.Reach.RD.uniswapTwoAddressGetterMaskAndJump -
-- parameterizes the return/continuation pc instead of hardcoding Uniswap's one-word return wrapper
-- at pc 861, and exposes both masked address words instead of requiring canonical calldata.
-- LIBRARY CANDIDATE: Reasoning.Reach - optimizer-on solc two-address external wrapper that
-- returns the low-160-bit masked address words.
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
      show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask from by decide, u256_land_comm]
      using rd45.jump hd45 hroutine (by evm_ov)⟩

-- GENERALIZES Examples.UniswapV2Pair.Routines.RD.uniswapAddressUint256ExternalLenOk -
-- same optimized address/uint256 external wrapper prefix, but the failing short-calldata branch.
-- LIBRARY CANDIDATE: Reasoning.Reach - optimizer-on solc address/uint256 external wrapper
-- short-calldata revert, parameterized by bytecode, entry PC, continuation PC, and target routine.
set_option maxHeartbeats 1000000 in
theorem RD.uniswapAddressUint256ExternalShort {cA gh bl σ σ₀ A I} {g : Sat256}
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
  obtain ⟨_, _, rdEntry⟩ := hreach
  rcases hwf with
    ⟨hd0, hd1, hd4, hd6, hd7, hd8, hd9, hd11, hd12, hd13, hd14, hd17, hd18,
      hd20, hd21, _hd22, _hd23, _hd24, _hd26, _hd28, _hd30, _hd31, _hd32,
      _hd33, _hd34, _hd35, _hd36, _hd38, _hd39, _hd40, _hd43⟩
  have rd1 := rdEntry.jumpdest hd0 (by simp only [List.length_singleton]; omega)
  have rd4 := rd1.push2 ret hd1 (by evm_ov)
  have rd6 := rd4.push1 ⟨4⟩ hd4 (by evm_ov)
  have rd7 := rd6.dup1 hd6 (by evm_ov)
  have rd8 := rd7.calldatasize hd7 (by evm_ov)
  have rd9 := rd8.sub hd8 (by evm_ov)
  have rd11 := rd9.push1 ⟨64⟩ hd9 (by evm_ov)
  have rd12 := rd11.dup2 hd11 (by evm_ov)
  have rd13₀ := rd12.lt hd12 (by evm_ov)
  have rd13 := rd13₀
  rw [hlt] at rd13
  have rd14₀ := rd13.iszero hd13 (by evm_ov)
  have rd14 := rd14₀
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd14
  have rd17 := rd14.push2 (uniswapAddressUint256ExternalDecodedPc entry) hd14 (by evm_ov)
  have rd18 := rd17.jumpiNT hd17 (by decide : (⟨0⟩ : UInt256) = ⟨0⟩) (by evm_ov)
  have rd20 := rd18.push1 ⟨0⟩ hd18 (by evm_ov)
  have rd21 := rd20.dup1 hd20 (by evm_ov)
  exact rd21.rev 0 hd21 mem_cost (by evm_ov)

-- GENERALIZES Examples.UniswapV2Pair.Routines.RD.uniswapAddressAddressUint256ExternalLenOk -
-- same optimized address/address/uint256 external wrapper prefix, but the failing short-calldata
-- branch.
-- LIBRARY CANDIDATE: Reasoning.Reach - optimizer-on solc address/address/uint256 external
-- wrapper short-calldata revert, parameterized by bytecode, entry PC, continuation PC, and
-- target routine.
set_option maxHeartbeats 1000000 in
theorem RD.uniswapAddressAddressUint256ExternalShort {cA gh bl σ σ₀ A I} {g : Sat256}
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
  obtain ⟨_, _, rdEntry⟩ := hreach
  rcases hwf with
    ⟨hd0, hd1, hd4, hd6, hd7, hd8, hd9, hd11, hd12, hd13, hd14, hd17, hd18,
      hd20, hd21, _hd22, _hd23, _hd24, _hd26, _hd28, _hd30, _hd31, _hd32,
      _hd33, _hd34, _hd35, _hd36, _hd37, _hd39, _hd40, _hd41, _hd42, _hd43,
      _hd44, _hd45, _hd46, _hd48, _hd49, _hd50, _hd53⟩
  have rd1 := rdEntry.jumpdest hd0 (by simp only [List.length_singleton]; omega)
  have rd4 := rd1.push2 ret hd1 (by evm_ov)
  have rd6 := rd4.push1 ⟨4⟩ hd4 (by evm_ov)
  have rd7 := rd6.dup1 hd6 (by evm_ov)
  have rd8 := rd7.calldatasize hd7 (by evm_ov)
  have rd9 := rd8.sub hd8 (by evm_ov)
  have rd11 := rd9.push1 ⟨96⟩ hd9 (by evm_ov)
  have rd12 := rd11.dup2 hd11 (by evm_ov)
  have rd13₀ := rd12.lt hd12 (by evm_ov)
  have rd13 := rd13₀
  rw [hlt] at rd13
  have rd14₀ := rd13.iszero hd13 (by evm_ov)
  have rd14 := rd14₀
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd14
  have rd17 := rd14.push2 (uniswapAddressAddressUint256ExternalDecodedPc entry) hd14
    (by evm_ov)
  have rd18 := rd17.jumpiNT hd17 (by decide : (⟨0⟩ : UInt256) = ⟨0⟩) (by evm_ov)
  have rd20 := rd18.push1 ⟨0⟩ hd18 (by evm_ov)
  have rd21 := rd20.dup1 hd20 (by evm_ov)
  exact rd21.rev 0 hd21 mem_cost (by evm_ov)

-- GENERALIZES Reasoning.Reach.RD.uniswapTwoAddressGetterMaskAndJump - keeps the third static ABI
-- word raw, and exposes both masked address words instead of requiring canonical calldata.
-- LIBRARY CANDIDATE: Reasoning.Reach - optimizer-on solc address/address/uint256 external
-- wrapper that returns the low-160-bit masked address words.
set_option maxHeartbeats 1000000 in
theorem RD.uniswapAddressAddressUint256ExternalMaskAndJumpMasked {g : Sat256} {s0 : State}
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
      show ((⟨64⟩ : UInt256) + ⟨4⟩).toNat = 68 from by decide,
      show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask from by decide, u256_land_comm]
      using rd53.jump hd53 hroutine (by evm_ov)⟩

end UniswapV2Pair
