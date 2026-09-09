import Benchmarks.Dss.Pot.Dispatch
import Benchmarks.Dss.Pot.Arith
import Reasoning.ExternalCall
import Reasoning.Initcode

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.Pot

/-! ## `vat.move(from, to, rad)` external-call calldata construction (shared by `join`/`exit`)

The optimized runtime builds the ABI calldata for `move(address,address,uint256)` at the free
memory pointer (`128`): selector at `128`, `from` at `132`, `to` at `164`, `rad` at `196`; the
100-byte window `[128, 228)` is exactly `potExternalABI.encode? "move" [from, to, rad]`.  Mirrors the
sibling `Jug` fold-call memory layout (`Benchmarks/Dss/Jug/DripBase.lean`). -/

abbrev potMoveSelectorWord : UInt256 := ⟨0xbb35783b⟩

abbrev potMoveSelectorShifted : UInt256 :=
  UInt256.shiftLeft potMoveSelectorWord ⟨224⟩

abbrev potMoveOutPtr : UInt256 := ⟨128⟩
abbrev potMoveInSize : UInt256 := ⟨100⟩
abbrev potMoveEndPtr : UInt256 := ⟨228⟩

noncomputable def potMoveSelectorMem (mem : ByteArray) : ByteArray :=
  potMoveSelectorShifted.toByteArray.write 0 mem potMoveOutPtr.toNat 32

noncomputable def potMoveFromMem (fromW : UInt256) (mem : ByteArray) : ByteArray :=
  fromW.toByteArray.write 0 (potMoveSelectorMem mem) (potMoveOutPtr + ⟨4⟩).toNat 32

noncomputable def potMoveToMem (fromW toW : UInt256) (mem : ByteArray) : ByteArray :=
  toW.toByteArray.write 0 (potMoveFromMem fromW mem) (potMoveOutPtr + ⟨36⟩).toNat 32

noncomputable def potMoveCalldataMem (fromW toW rad : UInt256) (mem : ByteArray) : ByteArray :=
  rad.toByteArray.write 0 (potMoveToMem fromW toW mem) (potMoveOutPtr + ⟨68⟩).toNat 32

/-! ### Sizes -/

theorem potMoveSelectorMem_size {mem : ByteArray} (hmem : mem.size = 96) :
    (potMoveSelectorMem mem).size = 160 := by
  unfold potMoveSelectorMem potMoveOutPtr
  exact toByteArray_write32_size_of_ge mem potMoveSelectorShifted 128 96 160 hmem
    (by omega) (by decide +native) (by omega)

theorem potMoveFromMem_size {fromW : UInt256} {mem : ByteArray} (hmem : mem.size = 96) :
    (potMoveFromMem fromW mem).size = 164 := by
  have hoff : (potMoveOutPtr + ⟨4⟩).toNat = 132 := by decide +native
  unfold potMoveFromMem
  rw [hoff]
  exact toByteArray_write32_size_of_le (potMoveSelectorMem mem) fromW 132 160 164
    (potMoveSelectorMem_size hmem) (by rw [potMoveSelectorMem_size hmem]; omega) (by omega)

theorem potMoveToMem_size {fromW toW : UInt256} {mem : ByteArray} (hmem : mem.size = 96) :
    (potMoveToMem fromW toW mem).size = 196 := by
  have hoff : (potMoveOutPtr + ⟨36⟩).toNat = 164 := by decide +native
  unfold potMoveToMem
  rw [hoff]
  exact toByteArray_write32_size_of_le (potMoveFromMem fromW mem) toW 164 164 196
    (potMoveFromMem_size hmem) (by rw [potMoveFromMem_size hmem]) (by omega)

theorem potMoveCalldataMem_size {fromW toW rad : UInt256} {mem : ByteArray} (hmem : mem.size = 96) :
    (potMoveCalldataMem fromW toW rad mem).size = 228 := by
  have hoff : (potMoveOutPtr + ⟨68⟩).toNat = 196 := by decide +native
  unfold potMoveCalldataMem
  rw [hoff]
  exact toByteArray_write32_size_of_le (potMoveToMem fromW toW mem) rad 196 196 228
    (potMoveToMem_size hmem) (by rw [potMoveToMem_size hmem]) (by omega)

/-! ### Free-pointer preservation (`readWithPadding 64 32 = ⟨128⟩`) -/

theorem potMoveSelectorMem_read64 {mem : ByteArray} (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (potMoveSelectorMem mem).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold potMoveSelectorMem potMoveOutPtr
  change (potMoveSelectorShifted.toByteArray.write 0 mem 128 32).readWithPadding 64 32 =
    UInt256.toByteArray ⟨128⟩
  rw [toByteArray_write_read_below_of_gap potMoveSelectorShifted mem 128 64
    (by omega) (by omega) (by rw [hmem]; decide +native)]
  exact hread64

theorem potMoveFromMem_read64 {fromW : UInt256} {mem : ByteArray} (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (potMoveFromMem fromW mem).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  have hoff : (potMoveOutPtr + ⟨4⟩).toNat = 132 := by decide +native
  unfold potMoveFromMem
  rw [hoff, write32_read_below _ _ 132 64 (by rw [toByteArray_size])
    (by rw [potMoveSelectorMem_size hmem]; omega) (by omega)]
  exact potMoveSelectorMem_read64 hmem hread64

theorem potMoveToMem_read64 {fromW toW : UInt256} {mem : ByteArray} (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (potMoveToMem fromW toW mem).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  have hoff : (potMoveOutPtr + ⟨36⟩).toNat = 164 := by decide +native
  unfold potMoveToMem
  rw [hoff, write32_read_below _ _ 164 64 (by rw [toByteArray_size])
    (by rw [potMoveFromMem_size hmem]) (by omega)]
  exact potMoveFromMem_read64 hmem hread64

theorem potMoveCalldataMem_read64 {fromW toW rad : UInt256} {mem : ByteArray} (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (potMoveCalldataMem fromW toW rad mem).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  have hoff : (potMoveOutPtr + ⟨68⟩).toNat = 196 := by decide +native
  unfold potMoveCalldataMem
  rw [hoff, write32_read_below _ _ 196 64 (by rw [toByteArray_size])
    (by rw [potMoveToMem_size hmem]) (by omega)]
  exact potMoveToMem_read64 hmem hread64

theorem potMoveCalldataMem_mload64 {fromW toW rad : UInt256} {mem : ByteArray} (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (if (⟨64⟩ : UInt256).toNat ≥ (potMoveCalldataMem fromW toW rad mem).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 8 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((potMoveCalldataMem fromW toW rad mem).readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
      ⟨128⟩ := by
  exact mloadFreePtrValue (by rw [potMoveCalldataMem_size hmem]; decide)
    (by decide) (potMoveCalldataMem_read64 hmem hread64)

/-! ### The 100-byte calldata window reads back as `selector ++ from ++ to ++ rad` -/

theorem potMoveCalldataMem_read128_100 {fromW toW rad : UInt256} {mem : ByteArray}
    (hmem : mem.size = 96) :
    (potMoveCalldataMem fromW toW rad mem).readWithPadding 128 100 =
      vatMoveSelector ++ fromW.toByteArray ++ toW.toByteArray ++ rad.toByteArray := by
  let final := potMoveCalldataMem fromW toW rad mem
  have hfinalSize : final.size = 228 := potMoveCalldataMem_size hmem
  have e132 : (potMoveOutPtr + ⟨4⟩).toNat = 132 := by decide +native
  have e164 : (potMoveOutPtr + ⟨36⟩).toNat = 164 := by decide +native
  have e196 : (potMoveOutPtr + ⟨68⟩).toNat = 196 := by decide +native
  have hselectorRead : final.readWithPadding 128 4 = vatMoveSelector := by
    show (potMoveCalldataMem fromW toW rad mem).readWithPadding 128 4 = vatMoveSelector
    unfold potMoveCalldataMem; rw [e196]
    rw [toByteArray_write_read_below_len_of_gap rad (potMoveToMem fromW toW mem) 196 128 4
      (by rw [potMoveToMem_size hmem]; omega) (by omega) (by omega) (by norm_num)
      (by rw [potMoveToMem_size hmem]; decide +native)]
    unfold potMoveToMem; rw [e164]
    rw [toByteArray_write_read_below_len_of_gap toW (potMoveFromMem fromW mem) 164 128 4
      (by rw [potMoveFromMem_size hmem]; omega) (by omega) (by omega) (by norm_num)
      (by rw [potMoveFromMem_size hmem]; decide +native)]
    unfold potMoveFromMem; rw [e132]
    rw [toByteArray_write_read_below_len_of_gap fromW (potMoveSelectorMem mem) 132 128 4
      (by rw [potMoveSelectorMem_size hmem]; omega) (by omega) (by omega) (by norm_num)
      (by rw [potMoveSelectorMem_size hmem]; decide +native)]
    unfold potMoveSelectorMem
    show (potMoveSelectorShifted.toByteArray.write 0 mem 128 32).readWithPadding 128 4 =
      vatMoveSelector
    have hw := toByteArray_write_read_window_of_gap potMoveSelectorShifted mem 128 0 4
      (by omega) (by omega) (by norm_num) (by rw [hmem]; decide +native)
    simp only [Nat.add_zero] at hw
    rw [hw]
    decide +native
  have hfromRead : final.readWithPadding 132 32 = fromW.toByteArray := by
    show (potMoveCalldataMem fromW toW rad mem).readWithPadding 132 32 = fromW.toByteArray
    unfold potMoveCalldataMem; rw [e196]
    rw [toByteArray_write_read_below_len_of_gap rad (potMoveToMem fromW toW mem) 196 132 32
      (by rw [potMoveToMem_size hmem]; omega) (by omega) (by omega) (by norm_num)
      (by rw [potMoveToMem_size hmem]; decide +native)]
    unfold potMoveToMem; rw [e164]
    rw [toByteArray_write_read_below_len_of_gap toW (potMoveFromMem fromW mem) 164 132 32
      (by rw [potMoveFromMem_size hmem]) (by omega) (by omega) (by norm_num)
      (by rw [potMoveFromMem_size hmem]; decide +native)]
    unfold potMoveFromMem; rw [e132]
    rw [toByteArray_write_read_back_of_gap fromW (potMoveSelectorMem mem) 132
      (by rw [potMoveSelectorMem_size hmem]; decide +native)]
  have htoRead : final.readWithPadding 164 32 = toW.toByteArray := by
    show (potMoveCalldataMem fromW toW rad mem).readWithPadding 164 32 = toW.toByteArray
    unfold potMoveCalldataMem; rw [e196]
    rw [toByteArray_write_read_below_len_of_gap rad (potMoveToMem fromW toW mem) 196 164 32
      (by rw [potMoveToMem_size hmem]) (by omega) (by omega) (by norm_num)
      (by rw [potMoveToMem_size hmem]; decide +native)]
    unfold potMoveToMem; rw [e164]
    rw [toByteArray_write_read_back_of_gap toW (potMoveFromMem fromW mem) 164
      (by rw [potMoveFromMem_size hmem]; decide +native)]
  have hradRead : final.readWithPadding 196 32 = rad.toByteArray := by
    show (potMoveCalldataMem fromW toW rad mem).readWithPadding 196 32 = rad.toByteArray
    unfold potMoveCalldataMem; rw [e196]
    rw [toByteArray_write_read_back_of_gap rad (potMoveToMem fromW toW mem) 196
      (by rw [potMoveToMem_size hmem]; decide +native)]
  rw [readWithPadding_eq_extract' final 128 100 (by norm_num) (by norm_num) (by rw [hfinalSize])]
  have hselectorExt : final.extract 128 132 = vatMoveSelector := by
    rw [← readWithPadding_eq_extract' final 128 4 (by norm_num) (by norm_num)
      (by rw [hfinalSize]; omega)]
    exact hselectorRead
  have hfromExt : final.extract 132 164 = fromW.toByteArray := by
    rw [← readWithPadding_eq_extract' final 132 32 (by norm_num) (by norm_num)
      (by rw [hfinalSize]; omega)]
    exact hfromRead
  have htoExt : final.extract 164 196 = toW.toByteArray := by
    rw [← readWithPadding_eq_extract' final 164 32 (by norm_num) (by norm_num)
      (by rw [hfinalSize]; omega)]
    exact htoRead
  have hradExt : final.extract 196 228 = rad.toByteArray := by
    rw [← readWithPadding_eq_extract' final 196 32 (by norm_num) (by norm_num)
      (by rw [hfinalSize])]
    exact hradRead
  have hsplit : final.extract 128 228 =
      final.extract 128 132 ++ final.extract 132 164 ++ final.extract 164 196 ++
        final.extract 196 228 := by
    rw [show final.extract 128 228 = final.extract 128 132 ++ final.extract 132 228 by
      rw [ByteArray.extract_append_extract]; norm_num]
    rw [show final.extract 132 228 = final.extract 132 164 ++ final.extract 164 228 by
      rw [ByteArray.extract_append_extract]; norm_num]
    rw [show final.extract 164 228 = final.extract 164 196 ++ final.extract 196 228 by
      rw [ByteArray.extract_append_extract]; norm_num]
    simp [ByteArray.append_assoc]
  rw [hsplit, hselectorExt, hfromExt, htoExt, hradExt]

theorem potMoveEncode_eq (fromA toA : AccountAddress) (fromW toW rad : UInt256) {mem : ByteArray}
    (hmem : mem.size = 96)
    (hfromWord : EVM.word ↑fromA = fromW)
    (htoWord : EVM.word ↑toA = toW) :
    config.externalABI.encode? "move"
        [.address fromA, .address toA, .int (Int.ofNat rad.toNat)] =
      some ((potMoveCalldataMem fromW toW rad mem).readWithPadding
        potMoveOutPtr.toNat potMoveInSize.toNat) := by
  change config.externalABI.encode? "move"
      [.address fromA, .address toA, .int (Int.ofNat rad.toNat)] =
    some ((potMoveCalldataMem fromW toW rad mem).readWithPadding 128 100)
  rw [potMoveCalldataMem_read128_100 hmem]
  have hradWord : EVM.word rad.toNat = rad := by
    show UInt256.ofNat rad.toNat = rad
    exact u256_ofNat_toNat rad
  have hradLt : rad.toNat < EVM.twoPow 256 := by
    change rad.val.val < EVM.twoPow 256
    exact rad.val.isLt
  have hfromLt : (fromA.val : ℕ) < EVM.twoPow 160 := by
    change fromA.val < EVM.twoPow 160
    have := fromA.isLt
    simp only [AccountAddress.size] at this
    change fromA.val < AccountAddress.size at this
    simpa [EVM.twoPow, AccountAddress.size] using this
  have htoLt : (toA.val : ℕ) < EVM.twoPow 160 := by
    change toA.val < EVM.twoPow 160
    have := toA.isLt
    simp only [AccountAddress.size] at this
    change toA.val < AccountAddress.size at this
    simpa [EVM.twoPow, AccountAddress.size] using this
  simp [config, potExternalABI, ABI.encodeCallWithSelector?, ABI.encodeABIValues?,
    ABI.encodeABIValuesFrom?, ABI.encodeABIValue?, ABI.encodeABIWord?, ABI.abiTupleHeadSize?,
    ABI.staticABIEncodedSize?, ABI.isDynamicABIType, addr, uint256, uint256Int,
    vatMoveSelector, selectorBytes, hfromWord, htoWord, hradWord, hradLt, hfromLt, htoLt,
    word_toBytesBE_toByteArray_eq_toByteArray]
  simp [ABI.zeroBytes, ByteArray.append_assoc]

/-! ## `join(uint256)` EVM-side words -/

abbrev joinWadWord (I : ExecutionEnv) : UInt256 := calldataWord I.calldata 4
abbrev joinCallerWord (I : ExecutionEnv) : UInt256 := UInt256.ofNat I.source.val
abbrev joinThisWord (I : ExecutionEnv) : UInt256 := UInt256.ofNat I.codeOwner.val
abbrev joinPieSlot (I : ExecutionEnv) : UInt256 := solcMappingSlot ⟨1⟩ (joinCallerWord I)
abbrev joinPie0 (σ : AccountMap) (I : ExecutionEnv) : UInt256 := solcSlotWord σ I (joinPieSlot I)
abbrev joinPie2 (σ : AccountMap) (I : ExecutionEnv) : UInt256 := solcSlotWord σ I ⟨2⟩
abbrev joinChi (σ : AccountMap) (I : ExecutionEnv) : UInt256 := solcSlotWord σ I ⟨4⟩
abbrev joinVatRaw (σ : AccountMap) (I : ExecutionEnv) : UInt256 := solcSlotWord σ I ⟨5⟩
abbrev joinVatMasked (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.land (joinVatRaw σ I) solcAddrMask
abbrev joinRhoWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 := solcSlotWord σ I ⟨7⟩
abbrev joinNowWord (I : ExecutionEnv) : UInt256 := UInt256.ofNat I.header.timestamp

/-- Scratch memory holding `keccak(caller ++ 1)` for the `pie[caller]` slot. -/
noncomputable abbrev joinPieHashMem (I : ExecutionEnv) : ByteArray :=
  twoWordHashMem (joinCallerWord I) ⟨1⟩ solcFreePtrMem

theorem joinPieHashMem_size (I : ExecutionEnv) : (joinPieHashMem I).size = 96 :=
  twoWordHashMem_size_96 (joinCallerWord I) ⟨1⟩ solcFreePtrMem_size

theorem joinPieHashMem_read64 (I : ExecutionEnv) :
    (joinPieHashMem I).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ :=
  twoWordHashMem_read64 (joinCallerWord I) ⟨1⟩ solcFreePtrMem_size solcFreePtrMem_read64

theorem joinPieSlot_keccak (I : ExecutionEnv) :
    UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((joinPieHashMem I).readWithPadding 0 64))) = joinPieSlot I :=
  twoWordHashMem_solcMappingSlot ⟨1⟩ (joinCallerWord I) solcFreePtrMem_size

theorem joinCallerWord_canonical (I : ExecutionEnv) :
    (joinCallerWord I).toNat < EVM.addressModulus := by
  show (UInt256.ofNat I.source.val).toNat < EVM.addressModulus
  rw [ulit_toNat' _ (lt_of_lt_of_le I.source.isLt (by decide))]
  exact lt_of_lt_of_le I.source.isLt (by decide)

/-! ## Shared checked-arithmetic routines (`_add @2278`, `_mul @2300`) -/

/-- `_add(a, b)` routine (`@2278`): stack `[a, b, ret, R]` → `[b + a, R]` at `ret`, no overflow. -/
theorem RD.potAddReturns {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {a b ret : UInt256} {R : List UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ}
    (h : RD potBytecode ee g s0 ⟨2278⟩ (a :: b :: ret :: R) mem aw rdata (cA, σ) k C)
    (hno : ¬ UInt256.size ≤ b.toNat + a.toNat)
    (hret : (D_J potBytecode 0).contains ret = true)
    (hov : R.length + 6 ≤ 1024) :
    ∃ k' C', RD potBytecode ee g s0 ret ((b + a) :: R) mem aw rdata (cA, σ) k' C' := by
  have hlt : UInt256.lt (b + a) b = ⟨0⟩ := by
    rw [u256_add_comm b a]; exact constructorCheckedAddNoOverflowLt b a hno
  have rdPre := evm_run h with [
    raw jumpdest (by decide +native) (by evm_ov),
    raw dup1 (by decide +native) (by evm_ov),
    raw dup3 (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov),
    raw dup3 (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw lt (by decide +native) (by evm_ov),
    raw iszero (by decide +native) (by evm_ov),
    raw push2 ⟨2294⟩ (by decide +native) (by evm_ov)]
  have rd2294 := rdPre.jumpiT (by decide +native) (by rw [hlt]; decide) (by jump_dest) (by evm_ov)
  have rdEnd := evm_run rd2294 with [
    raw jumpdest (by decide +native) (by evm_ov),
    raw swap3 (by decide +native) (by evm_ov),
    raw swap2 (by decide +native) (by evm_ov),
    raw pop (by decide +native) (by evm_ov),
    raw pop (by decide +native) (by evm_ov)]
  exact ⟨_, _, rdEnd.jump (by decide +native) hret (by evm_ov)⟩

/-- `_add(a, b)` routine (`@2278`): overflow (`size ≤ b + a`) reverts. -/
theorem RD.potAddReverts {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {a b ret : UInt256} {R : List UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ}
    (h : RD potBytecode ee g s0 ⟨2278⟩ (a :: b :: ret :: R) mem aw rdata (cA, σ) k C)
    (hover : UInt256.size ≤ b.toNat + a.toNat)
    (hov : R.length + 6 ≤ 1024) :
    RDrev potBytecode g s0 := by
  have hlt : UInt256.lt (b + a) b = ⟨1⟩ := by
    rw [u256_add_comm b a]; exact constructorCheckedAddOverflowLt b a hover
  have rdPre := evm_run h with [
    raw jumpdest (by decide +native) (by evm_ov),
    raw dup1 (by decide +native) (by evm_ov),
    raw dup3 (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov),
    raw dup3 (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw lt (by decide +native) (by evm_ov),
    raw iszero (by decide +native) (by evm_ov),
    raw push2 ⟨2294⟩ (by decide +native) (by evm_ov)]
  have rdRev := rdPre.jumpiNT (by decide +native) (by rw [hlt]; decide) (by evm_ov)
  exact RD.solcPush1Dup1Revert0 rdRev
    (by decide +native) (by decide +native) (by decide +native)
    (by simp only [List.length_cons, List.length_nil]; omega)

/-- SafeMath mul division-check succeeds when the product fits and `a ≠ 0`. -/
theorem potMulOkEqOne {a b : UInt256} (ha : a ≠ (⟨0⟩ : UInt256))
    (hfit : b.toNat * a.toNat < UInt256.size) :
    UInt256.eq (UInt256.div (UInt256.mul b a) a) b = ⟨1⟩ := by
  have haNe : a.toNat ≠ 0 := fun hz => ha (uint256_toNat_eq_zero hz)
  have hdiv : UInt256.div (UInt256.mul b a) a = b := by
    apply u256_inj
    rw [udiv_toNat, u256_mul_toNat, Nat.mod_eq_of_lt hfit]
    simpa [Nat.mul_comm] using Nat.mul_div_right b.toNat (Nat.pos_of_ne_zero haNe)
  rw [hdiv, u256_eq_refl]

/-- SafeMath mul division-check fails on overflow (`size ≤ b*a`, `a ≠ 0`). -/
theorem potMulOverflowEqZero {a b : UInt256} (ha : a ≠ (⟨0⟩ : UInt256))
    (hover : UInt256.size ≤ b.toNat * a.toNat) :
    UInt256.eq (UInt256.div (UInt256.mul b a) a) b = ⟨0⟩ := by
  apply u256_eq_of_ne
  intro hbad
  have hmod : (UInt256.mul b a).toNat = b.toNat * a.toNat % UInt256.size := u256_mul_toNat b a
  have hsizePos : 0 < UInt256.size := by decide
  have hlt : (UInt256.mul b a).toNat < b.toNat * a.toNat := by
    rw [hmod]; exact lt_of_lt_of_le (Nat.mod_lt _ hsizePos) hover
  have hdiv : (UInt256.mul b a).toNat / a.toNat = b.toNat := by
    have hh := congrArg UInt256.toNat hbad
    rwa [udiv_toNat] at hh
  have hge : b.toNat * a.toNat ≤ (UInt256.mul b a).toNat := by
    calc b.toNat * a.toNat = ((UInt256.mul b a).toNat / a.toNat) * a.toNat := by rw [hdiv]
      _ ≤ (UInt256.mul b a).toNat := Nat.div_mul_le_self _ _
  omega

/-- `_mul(a, b)` routine (`@2300`): stack `[a, b, ret, R]` → `[b * a, R]` at `ret`, product fits. -/
theorem RD.potMulReturns {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {a b ret : UInt256} {R : List UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ}
    (h : RD potBytecode ee g s0 ⟨2300⟩ (a :: b :: ret :: R) mem aw rdata (cA, σ) k C)
    (hfit : b.toNat * a.toNat < UInt256.size)
    (hret : (D_J potBytecode 0).contains ret = true)
    (hov : R.length + 9 ≤ 1024) :
    ∃ k' C', RD potBytecode ee g s0 ret ((UInt256.mul b a) :: R) mem aw rdata (cA, σ) k' C' := by
  have rd2294 : ∃ k' C', RD potBytecode ee g s0 ⟨2294⟩
      (UInt256.mul b a :: a :: b :: ret :: R) mem aw rdata (cA, σ) k' C' := by
    by_cases ha : a = (⟨0⟩ : UInt256)
    · subst ha
      have hmul0 : UInt256.mul b ⟨0⟩ = ⟨0⟩ := by
        apply u256_inj; simp [u256_mul_toNat]
      have rdPre := evm_run h with [
        raw jumpdest (by decide +native) (by evm_ov),
        raw push1 ⟨0⟩ (by decide +native) (by evm_ov),
        raw dup2 (by decide +native) (by evm_ov),
        raw iszero (by decide +native) (by evm_ov),
        raw dup1 (by decide +native) (by evm_ov),
        raw push2 ⟨2327⟩ (by decide +native) (by evm_ov)]
      have rd2327 := rdPre.jumpiT (by decide +native) (by decide) (by jump_dest) (by evm_ov)
      have rd2328 := rd2327.jumpdest (by decide +native) (by evm_ov)
      have rd2331 := rd2328.pushConst (⟨2294⟩ : UInt256) (width := 2) (op := .PUSH2)
        (by decide) (by decide +native) (by evm_ov)
      have rd := rd2331.jumpiT (by decide +native) (by decide) (by jump_dest) (by evm_ov)
      exact ⟨_, _, by rw [hmul0]; exact rd⟩
    · have hEqOne := potMulOkEqOne ha hfit
      have rdPre := evm_run h with [
        raw jumpdest (by decide +native) (by evm_ov),
        raw push1 ⟨0⟩ (by decide +native) (by evm_ov),
        raw dup2 (by decide +native) (by evm_ov),
        raw iszero (by decide +native) (by evm_ov),
        raw dup1 (by decide +native) (by evm_ov),
        raw push2 ⟨2327⟩ (by decide +native) (by evm_ov)]
      have rd2310 := rdPre.jumpiNT (by decide +native)
        (by rw [Reasoning.Theory.isZero_eq_zero_of_ne ha]) (by evm_ov)
      have rdPre2 := evm_run rd2310 with [
        raw pop (by decide +native) (by evm_ov),
        raw pop (by decide +native) (by evm_ov),
        raw dup1 (by decide +native) (by evm_ov),
        raw dup3 (by decide +native) (by evm_ov),
        raw mul (by decide +native) (by evm_ov),
        raw dup3 (by decide +native) (by evm_ov),
        raw dup3 (by decide +native) (by evm_ov),
        raw dup3 (by decide +native) (by evm_ov),
        raw dup2 (by decide +native) (by evm_ov),
        raw push2 ⟨2324⟩ (by decide +native) (by evm_ov)]
      have rd2324 := rdPre2.jumpiT (by decide +native)
        (by simpa using ha) (by jump_dest) (by evm_ov)
      have rdPre3 := evm_run rd2324 with [
        raw jumpdest (by decide +native) (by evm_ov),
        raw div (by decide +native) (by evm_ov),
        raw eq (by decide +native) (by evm_ov),
        raw jumpdest (by decide +native) (by evm_ov),
        raw push2 ⟨2294⟩ (by decide +native) (by evm_ov)]
      exact ⟨_, _, rdPre3.jumpiT (by decide +native) (by rw [hEqOne]; decide)
        (by jump_dest) (by evm_ov)⟩
  obtain ⟨_, _, rd⟩ := rd2294
  have rdEnd := evm_run rd with [
    raw jumpdest (by decide +native) (by evm_ov),
    raw swap3 (by decide +native) (by evm_ov),
    raw swap2 (by decide +native) (by evm_ov),
    raw pop (by decide +native) (by evm_ov),
    raw pop (by decide +native) (by evm_ov)]
  exact ⟨_, _, rdEnd.jump (by decide +native) hret (by evm_ov)⟩

/-- `_mul(a, b)` routine (`@2300`): overflow (`size ≤ b*a`) reverts. -/
theorem RD.potMulReverts {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {a b ret : UInt256} {R : List UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ}
    (h : RD potBytecode ee g s0 ⟨2300⟩ (a :: b :: ret :: R) mem aw rdata (cA, σ) k C)
    (hover : UInt256.size ≤ b.toNat * a.toNat)
    (hov : R.length + 9 ≤ 1024) :
    RDrev potBytecode g s0 := by
  have ha : a ≠ (⟨0⟩ : UInt256) := by
    intro haz; subst haz
    simp only [show (⟨0⟩ : UInt256).toNat = 0 from rfl, Nat.mul_zero] at hover
    exact absurd hover (by decide)
  have hEqZero := potMulOverflowEqZero ha hover
  have rdPre := evm_run h with [
    raw jumpdest (by decide +native) (by evm_ov),
    raw push1 ⟨0⟩ (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw iszero (by decide +native) (by evm_ov),
    raw dup1 (by decide +native) (by evm_ov),
    raw push2 ⟨2327⟩ (by decide +native) (by evm_ov)]
  have rd2310 := rdPre.jumpiNT (by decide +native)
    (by rw [Reasoning.Theory.isZero_eq_zero_of_ne ha]) (by evm_ov)
  have rdPre2 := evm_run rd2310 with [
    raw pop (by decide +native) (by evm_ov),
    raw pop (by decide +native) (by evm_ov),
    raw dup1 (by decide +native) (by evm_ov),
    raw dup3 (by decide +native) (by evm_ov),
    raw mul (by decide +native) (by evm_ov),
    raw dup3 (by decide +native) (by evm_ov),
    raw dup3 (by decide +native) (by evm_ov),
    raw dup3 (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw push2 ⟨2324⟩ (by decide +native) (by evm_ov)]
  have rd2324 := rdPre2.jumpiT (by decide +native)
    (by simpa using ha) (by jump_dest) (by evm_ov)
  have rdPre3 := evm_run rd2324 with [
    raw jumpdest (by decide +native) (by evm_ov),
    raw div (by decide +native) (by evm_ov),
    raw eq (by decide +native) (by evm_ov),
    raw jumpdest (by decide +native) (by evm_ov),
    raw push2 ⟨2294⟩ (by decide +native) (by evm_ov)]
  have rdRev := rdPre3.jumpiNT (by decide +native) (by rw [hEqZero]) (by evm_ov)
  exact RD.solcPush1Dup1Revert0 rdRev
    (by decide +native) (by decide +native) (by decide +native)
    (by simp only [List.length_cons, List.length_nil]; omega)

/-! ## `join(uint256)` EVM-side reachability -/

theorem potReachJoinBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = potBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (potSelBytes 9)) :
    ∃ k C, RD potBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨272⟩ [potSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  have hword : potSelWord I = ⟨0x049878f3⟩ :=
    potSelWord_eq_of_beq I hsz 0x04 0x98 0x78 0xf3 ⟨0x049878f3⟩
      (by decide +native) (by simpa [potSelBytes] using hsel)
  have hroot : UInt256.gt (armSelNat potBytecode potRootSplitPc) (potSelWord I) ≠ ⟨0⟩ := by
    rw [hword]; decide +native
  have h163 : UInt256.gt (armSelNat potBytecode potSplit163Pc) (potSelWord I) ≠ ⟨0⟩ := by
    rw [hword]; decide +native
  have heq0 : ∀ j, j < 0 →
      UInt256.eq (armSelNat potBytecode (nthArmPc potBytecode potG223FirstArmPc j))
        (potSelWord I) = ⟨0⟩ := by intro j hj; omega
  have htake :
      UInt256.eq (armSelNat potBytecode (nthArmPc potBytecode potG223FirstArmPc 0))
        (potSelWord I) ≠ ⟨0⟩ := by rw [hword]; decide +native
  exact potReachG223Body 0 (by omega) ⟨272⟩ hcode hwv hsz hsize hroot h163 heq0 htake
    (by jump_dest) (by decide +native)

/-- Entry `@272`: decode the single `uint256 wad` argument, jump to logic `@681`. -/
theorem potJoinX_decoded {cA σ I} {g : Sat256} {s0 : State} {sel : UInt256}
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD potBytecode I g s0 ⟨272⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD potBytecode I g s0 ⟨681⟩ [joinWadWord I, ⟨301⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨k, C, h⟩ := hreach
  have hsz4 : 4 ≤ I.calldata.size := by omega
  have hlt : UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨0⟩ := by
    apply ult_zero
    rw [usub_ofNat_word_toNat (by simpa using hsz4) hsize]
    change 32 ≤ I.calldata.size - 4
    omega
  have rdPre := evm_run h with [
    raw jumpdest (by decide +native) (by evm_ov),
    raw push2 ⟨301⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨4⟩ (by decide +native) (by evm_ov),
    raw dup1 (by decide +native) (by evm_ov),
    raw calldatasize (by decide +native) (by evm_ov),
    raw sub (by decide +native) (by evm_ov),
    raw push1 ⟨32⟩ (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw lt (by decide +native) (by evm_ov),
    raw iszero (by decide +native) (by evm_ov),
    raw push2 ⟨294⟩ (by decide +native) (by evm_ov)]
  have rdJd := rdPre.jumpiT (by decide +native) (by rw [hlt]; decide) (by jump_dest) (by evm_ov)
  have rdLoad := evm_run rdJd with [
    raw jumpdest (by decide +native) (by evm_ov),
    raw pop (by decide +native) (by evm_ov),
    raw calldataload (by decide +native) (by evm_ov),
    raw push2 ⟨681⟩ (by decide +native) (by evm_ov)]
  have rd681 := rdLoad.jump (by decide +native) (by jump_dest) (by evm_ov)
  exact ⟨_, _, by simpa [joinWadWord, calldataWord] using rd681⟩

/-- Entry `@272`: short calldata (`< 36` bytes) reverts before decoding. -/
theorem potJoinX_shortReverts {cA σ I} {g : Sat256} {s0 : State} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 36)
    (hreach : ∃ k C, RD potBytecode I g s0 ⟨272⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev potBytecode g s0 := by
  obtain ⟨k, C, h⟩ := hreach
  have hlt : UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨1⟩ := by
    apply ult_one
    rw [usub_ofNat_word_toNat (by simpa using hsz4) hsize]
    change I.calldata.size - 4 < 32
    omega
  have rdPre := evm_run h with [
    raw jumpdest (by decide +native) (by evm_ov),
    raw push2 ⟨301⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨4⟩ (by decide +native) (by evm_ov),
    raw dup1 (by decide +native) (by evm_ov),
    raw calldatasize (by decide +native) (by evm_ov),
    raw sub (by decide +native) (by evm_ov),
    raw push1 ⟨32⟩ (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw lt (by decide +native) (by evm_ov),
    raw iszero (by decide +native) (by evm_ov),
    raw push2 ⟨294⟩ (by decide +native) (by evm_ov)]
  have rdRev := rdPre.jumpiNT (by decide +native) (by rw [hlt]; decide) (by evm_ov)
  exact RD.solcPush1Dup1Revert0 rdRev
    (by decide +native) (by decide +native) (by decide +native)
    (by simp only [List.length_cons, List.length_nil]; omega)

/-! ## `join(uint256)` — `now == rho` guard -/

/-- Logic `@681`: `require now == rho`, then jump to `@757`. -/
theorem potJoinX_rhoOk {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ} {sel : UInt256}
    (hrho : joinNowWord I = joinRhoWord σ I)
    (h : RD potBytecode I g s0 ⟨681⟩ [joinWadWord I, ⟨301⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD potBytecode I g s0 ⟨757⟩ [joinWadWord I, ⟨301⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have rd682 := h.jumpdest (by decide +native) (by evm_ov)
  have rd684 := rd682.push1 ⟨7⟩ (by decide +native) (by evm_ov)
  obtain ⟨_, _, rd685⟩ := rd684.sload (by decide +native) (by evm_ov)
  have rd686 := rd685.timestamp (by decide +native) (by evm_ov)
  have rd687 := rd686.eq (by decide +native) (by evm_ov)
  have hcond : UInt256.eq (joinNowWord I) (joinRhoWord σ I) ≠ ⟨0⟩ := by
    rw [hrho, u256_eq_refl]; decide
  have rd690 := rd687.pushConst (⟨757⟩ : UInt256) (width := 2) (op := .PUSH2)
    (by decide) (by decide +native) (by evm_ov)
  exact ⟨_, _, rd690.jumpiT (by decide +native) hcond (by jump_dest) (by evm_ov)⟩

/-- Logic `@681`: `now ≠ rho` reverts with `"Pot/rho-not-updated"`. -/
theorem potJoinX_rhoReverts {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ} {sel : UInt256}
    (hrho : joinNowWord I ≠ joinRhoWord σ I)
    (h : RD potBytecode I g s0 ⟨681⟩ [joinWadWord I, ⟨301⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev potBytecode g s0 := by
  have rd682 := h.jumpdest (by decide +native) (by evm_ov)
  have rd684 := rd682.push1 ⟨7⟩ (by decide +native) (by evm_ov)
  obtain ⟨_, _, rd685⟩ := rd684.sload (by decide +native) (by evm_ov)
  have rd686 := rd685.timestamp (by decide +native) (by evm_ov)
  have rd687 := rd686.eq (by decide +native) (by evm_ov)
  have hcond : UInt256.eq (joinNowWord I) (joinRhoWord σ I) = ⟨0⟩ :=
    u256_eq_of_ne hrho
  have rd690 := rd687.pushConst (⟨757⟩ : UInt256) (width := 2) (op := .PUSH2)
    (by decide) (by decide +native) (by evm_ov)
  have rd692 := rd690.jumpiNT (by decide +native) hcond (by evm_ov)
  exact RD.solcErrorStringRevertTail
    (pc := ⟨691⟩) (len := ⟨19⟩)
    (rawWord := ⟨0x141bdd0bdc9a1bcb5b9bdd0b5d5c19185d1959⟩)
    (shift := ⟨106⟩)
    (word := UInt256.shiftLeft (⟨0x141bdd0bdc9a1bcb5b9bdd0b5d5c19185d1959⟩ : UInt256) ⟨106⟩)
    (op := .PUSH19) (width := 19)
    rd692
    (by unfold solcErrorStringRevertTailWf; repeat' first | apply And.intro | decide +native)
    (by decide)
    rfl
    solcFreePtrMem_size solcFreePtrMem_read64
    (by simp only [List.length_cons, List.length_nil]; omega)

/-! ## `join(uint256)` — `pie[caller] += wad`, `Pie += wad` -/

/-- Scratch memory after the second `keccak(caller ++ 1)` (the `pie[caller]` store). -/
noncomputable abbrev joinPieStoreHashMem (I : ExecutionEnv) : ByteArray :=
  twoWordHashMem (joinCallerWord I) ⟨1⟩ (joinPieHashMem I)

/-- Logic `@757 → @800`: load `pie[caller]`, `_add wad`, store back. -/
theorem potJoinX_pieStore {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ} {sel : UInt256}
    (hperm : I.perm = true)
    (hno : ¬ UInt256.size ≤ (joinPie0 σ I).toNat + (joinWadWord I).toNat)
    (h : RD potBytecode I g s0 ⟨757⟩ [joinWadWord I, ⟨301⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD potBytecode I g s0 ⟨800⟩ [joinWadWord I, ⟨301⟩, sel]
      (joinPieStoreHashMem I) (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ (joinPieSlot I) (joinPie0 σ I + joinWadWord I)) k' C' := by
  have rdPre1 := evm_run h with [
    raw jumpdest (by decide +native) (by evm_ov),
    raw caller (by decide +native) (by evm_ov),
    raw push1 ⟨0⟩ (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov)]
  have rd764 := rdPre1.mstore 0 (wordAt0Mem (joinCallerWord I) solcFreePtrMem)
    (UInt256.ofNat 3) (by decide +native) mem_cost (by rfl) (by decide +native) (by evm_ov)
  have rdPre2 := evm_run rd764 with [
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨32⟩ (by decide +native) (by evm_ov)]
  have rd769 := rdPre2.mstore 0 (joinPieHashMem I)
    (UInt256.ofNat 3) (by decide +native) mem_cost (by rfl) (by decide +native) (by evm_ov)
  have rdPre3 := evm_run rd769 with [
    raw push1 ⟨64⟩ (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov)]
  have rd773 := rdPre3.keccak256 0 (joinPieSlot I)
    (UInt256.ofNat 3) (by decide +native) mem_cost (joinPieSlot_keccak I)
    (by decide +native) (by evm_ov)
  obtain ⟨_, _, rd773v⟩ := rd773.sload (by decide +native) (by evm_ov)
  have rdPre4 := evm_run rd773v with [
    raw push2 ⟨783⟩ (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw dup3 (by decide +native) (by evm_ov),
    raw push2 ⟨2278⟩ (by decide +native) (by evm_ov)]
  have rd2278 := rdPre4.jump (by decide +native) (by jump_dest) (by evm_ov)
  obtain ⟨_, _, rd783⟩ := RD.potAddReturns rd2278 hno (by jump_dest)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdPre5 := evm_run rd783 with [
    raw jumpdest (by decide +native) (by evm_ov),
    raw caller (by decide +native) (by evm_ov),
    raw push1 ⟨0⟩ (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov)]
  have rd790 := rdPre5.mstore 0 (wordAt0Mem (joinCallerWord I) (joinPieHashMem I))
    (UInt256.ofNat 3) (by decide +native) mem_cost (by rfl) (by decide +native) (by evm_ov)
  have rdPre6 := evm_run rd790 with [
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨32⟩ (by decide +native) (by evm_ov)]
  have rd795 := rdPre6.mstore 0 (joinPieStoreHashMem I)
    (UInt256.ofNat 3) (by decide +native) mem_cost (by rfl) (by decide +native) (by evm_ov)
  have rdPre7 := evm_run rd795 with [
    raw push1 ⟨64⟩ (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov)]
  have rd799 := rdPre7.keccak256 0 (joinPieSlot I)
    (UInt256.ofNat 3) (by decide +native) mem_cost
    (twoWordHashMem_solcMappingSlot ⟨1⟩ (joinCallerWord I) (joinPieHashMem_size I))
    (by decide +native) (by evm_ov)
  obtain ⟨_, _, rd800⟩ := rd799.sstore hperm (by decide +native)
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact ⟨_, _, by simpa [joinPie0] using rd800⟩

/-- Logic `@800 → @816`: load `Pie` (slot 2), `_add wad`, store back. -/
theorem potJoinX_PieStore {cA σ' I} {g : Sat256} {s0 : State} {k C : ℕ} {sel : UInt256}
    {mem : ByteArray}
    (hperm : I.perm = true)
    (hno : ¬ UInt256.size ≤ (solcSlotWord σ' I ⟨2⟩).toNat + (joinWadWord I).toNat)
    (h : RD potBytecode I g s0 ⟨800⟩ [joinWadWord I, ⟨301⟩, sel]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ') k C) :
    ∃ k' C', RD potBytecode I g s0 ⟨816⟩ [joinWadWord I, ⟨301⟩, sel]
      mem (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ' ⟨2⟩ (solcSlotWord σ' I ⟨2⟩ + joinWadWord I)) k' C' := by
  have rd802 := h.push1 ⟨2⟩ (by decide +native) (by evm_ov)
  obtain ⟨_, _, rd803⟩ := rd802.sload (by decide +native) (by evm_ov)
  have rdPre := evm_run rd803 with [
    raw push2 ⟨812⟩ (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw dup3 (by decide +native) (by evm_ov),
    raw push2 ⟨2278⟩ (by decide +native) (by evm_ov)]
  have rd2278 := rdPre.jump (by decide +native) (by jump_dest) (by evm_ov)
  obtain ⟨_, _, rd812⟩ := RD.potAddReturns rd2278 hno (by jump_dest)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd813 := rd812.jumpdest (by decide +native) (by evm_ov)
  have rd815 := rd813.push1 ⟨2⟩ (by decide +native) (by evm_ov)
  obtain ⟨_, _, rd816⟩ := rd815.sstore hperm (by decide +native)
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact ⟨_, _, by simpa using rd816⟩

/-- Logic `@816 → @853`: load `vat`/`chi`, `_mul chi wad`; product fits. -/
theorem potJoinX_mulReady {cA σ'' I} {g : Sat256} {s0 : State} {k C : ℕ} {sel : UInt256}
    {mem : ByteArray}
    (hfit : (joinChi σ'' I).toNat * (joinWadWord I).toNat < UInt256.size)
    (h : RD potBytecode I g s0 ⟨816⟩ [joinWadWord I, ⟨301⟩, sel]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ'') k C) :
    ∃ k' C', RD potBytecode I g s0 ⟨853⟩
      [UInt256.mul (joinChi σ'' I) (joinWadWord I), joinThisWord I, joinCallerWord I,
        potMoveSelectorWord, joinVatMasked σ'' I, joinWadWord I, ⟨301⟩, sel]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ'') k' C' := by
  have hmask : UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask := by
    decide
  have rd818 := h.push1 ⟨5⟩ (by decide +native) (by evm_ov)
  obtain ⟨_, _, rd819⟩ := rd818.sload (by decide +native) (by evm_ov)
  have rd821 := rd819.push1 ⟨4⟩ (by decide +native) (by evm_ov)
  obtain ⟨_, _, rd822⟩ := rd821.sload (by decide +native) (by evm_ov)
  have rdPre := evm_run rd822 with [
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨160⟩ (by decide +native) (by evm_ov),
    raw shl (by decide +native) (by evm_ov),
    raw sub (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw swap2 (by decide +native) (by evm_ov),
    raw and (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw push4 potMoveSelectorWord (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw caller (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov)]
  have rd843 := rdPre.address (by decide +native) (by evm_ov)
  have rdPre2 := evm_run rd843 with [
    raw swap1 (by decide +native) (by evm_ov),
    raw push2 ⟨853⟩ (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw dup7 (by decide +native) (by evm_ov),
    raw push2 ⟨2300⟩ (by decide +native) (by evm_ov)]
  have rd2300 := rdPre2.jump (by decide +native) (by jump_dest) (by evm_ov)
  obtain ⟨_, _, rd853⟩ := RD.potMulReturns rd2300 hfit (by jump_dest)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have hgoalVat : joinVatMasked σ'' I =
      UInt256.land (joinVatRaw σ'' I)
        (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) := by
    rw [joinVatMasked, hmask]
  rw [hgoalVat]
  exact ⟨_, _, rd853⟩

/-! ## `join(uint256)` — build `move` calldata + extcodesize guard -/

theorem joinThisWord_canonical (I : ExecutionEnv) :
    (joinThisWord I).toNat < EVM.addressModulus := by
  show (UInt256.ofNat I.codeOwner.val).toNat < EVM.addressModulus
  rw [ulit_toNat' _ (lt_of_lt_of_le I.codeOwner.isLt (by decide))]
  exact lt_of_lt_of_le I.codeOwner.isLt (by decide)

set_option maxHeartbeats 1000000 in
/-- Logic 853 to 927: build the move(from,to,rad) calldata in memory, reach the CALL
EXTCODESIZE guard. -/
theorem potJoinX_callGuard {cA σ'' I} {g : Sat256} {s0 : State} {k C : ℕ} {sel : UInt256}
    {mem : ByteArray} (hmemSize : mem.size = 96)
    (hmemRead64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (h : RD potBytecode I g s0 ⟨853⟩
      [UInt256.mul (joinChi σ'' I) (joinWadWord I), joinThisWord I, joinCallerWord I,
        potMoveSelectorWord, joinVatMasked σ'' I, joinWadWord I, ⟨301⟩, sel]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ'') k C) :
    ∃ k' C', RD potBytecode I g s0 ⟨927⟩
      (joinVatMasked σ'' I :: joinVatMasked σ'' I :: ⟨0⟩ :: ⟨128⟩ :: ⟨100⟩ :: ⟨128⟩ :: ⟨0⟩ ::
        ⟨228⟩ :: potMoveSelectorWord :: joinVatMasked σ'' I :: joinWadWord I :: ⟨301⟩ :: sel :: [])
      (potMoveCalldataMem (joinCallerWord I) (joinThisWord I)
        (UInt256.mul (joinChi σ'' I) (joinWadWord I)) mem)
      (UInt256.ofNat 8) ByteArray.empty (cA, σ'') k' C' := by
  set rad := UInt256.mul (joinChi σ'' I) (joinWadWord I) with hrad
  have hmask : UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask := by decide
  have hselShift : UInt256.shiftLeft
      (UInt256.land (⟨4294967295⟩ : UInt256) potMoveSelectorWord) ⟨224⟩ =
      potMoveSelectorShifted := by decide +native
  have hcallerClean : UInt256.land
      (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) (joinCallerWord I) =
      joinCallerWord I := by rw [hmask]; exact solcAddrMask_clean_left (joinCallerWord_canonical I)
  have hthisClean : UInt256.land
      (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩) (joinThisWord I) =
      joinThisWord I := by rw [hmask]; exact solcAddrMask_clean_left (joinThisWord_canonical I)
  have hmload0 :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 3 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) = ⟨128⟩ :=
    mloadFreePtrValue (by rw [hmemSize]; decide) (by decide) hmemRead64
  have rd854 := h.jumpdest (by decide +native) (by evm_ov)
  have rd856 := rd854.push1 ⟨64⟩ (by decide +native) (by evm_ov)
  have rd857 := rd856.mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide +native)
    mem_cost hmload0 (by decide) (by evm_ov)
  have rdSel := evm_run rd857 with [
    raw dup5 (by decide +native) (by evm_ov),
    raw push4 ⟨4294967295⟩ (by decide +native) (by evm_ov),
    raw and (by decide +native) (by evm_ov),
    raw push1 ⟨224⟩ (by decide +native) (by evm_ov),
    raw shl (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov)]
  have rd869 := rdSel.mstore 6 (potMoveSelectorMem mem) (UInt256.ofNat 5)
    (by decide +native) mem_cost (by rw [hselShift]; rfl) (by decide) (by evm_ov)
  have rdFrom := evm_run rd869 with [
    raw push1 ⟨4⟩ (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov),
    raw dup1 (by decide +native) (by evm_ov),
    raw dup5 (by decide +native) (by evm_ov),
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨160⟩ (by decide +native) (by evm_ov),
    raw shl (by decide +native) (by evm_ov),
    raw sub (by decide +native) (by evm_ov),
    raw and (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov)]
  have rd885 := rdFrom.mstore 3 (potMoveFromMem (joinCallerWord I) mem)
    (UInt256.ofNat 6) (by decide +native) mem_cost (by rw [hcallerClean]; rfl)
    (by decide +native) (by evm_ov)
  have rdTo := evm_run rd885 with [
    raw push1 ⟨32⟩ (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov),
    raw dup4 (by decide +native) (by evm_ov),
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨160⟩ (by decide +native) (by evm_ov),
    raw shl (by decide +native) (by evm_ov),
    raw sub (by decide +native) (by evm_ov),
    raw and (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov)]
  have rd900 := rdTo.mstore 3 (potMoveToMem (joinCallerWord I) (joinThisWord I) mem)
    (UInt256.ofNat 7) (by decide +native) mem_cost (by rw [hthisClean]; rfl)
    (by decide +native) (by evm_ov)
  have rdCd := evm_run rd900 with [
    raw push1 ⟨32⟩ (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov),
    raw dup3 (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov)]
  have rd906 := rdCd.mstore 3 (potMoveCalldataMem (joinCallerWord I) (joinThisWord I) rad mem)
    (UInt256.ofNat 8) (by decide +native) mem_cost (by rfl) (by decide +native) (by evm_ov)
  have hmload1 :
      (if (⟨64⟩ : UInt256).toNat ≥
            (potMoveCalldataMem (joinCallerWord I) (joinThisWord I) rad mem).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 8 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          ((potMoveCalldataMem (joinCallerWord I) (joinThisWord I) rad mem).readWithPadding
            (⟨64⟩ : UInt256).toNat 32))) = ⟨128⟩ :=
    potMoveCalldataMem_mload64 hmemSize hmemRead64
  have rdEnd := evm_run rd906 with [
    raw push1 ⟨32⟩ (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov),
    raw swap4 (by decide +native) (by evm_ov),
    raw pop (by decide +native) (by evm_ov),
    raw pop (by decide +native) (by evm_ov),
    raw pop (by decide +native) (by evm_ov),
    raw pop (by decide +native) (by evm_ov),
    raw push1 ⟨0⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨64⟩ (by decide +native) (by evm_ov)]
  have rd919 := rdEnd.mload 0 ⟨128⟩ (UInt256.ofNat 8) (by decide +native)
    mem_cost hmload1 (by decide) (by evm_ov)
  have rd927 := evm_run rd919 with [
    raw dup1 (by decide +native) (by evm_ov),
    raw dup4 (by decide +native) (by evm_ov),
    raw sub (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw push1 ⟨0⟩ (by decide +native) (by evm_ov),
    raw dup8 (by decide +native) (by evm_ov),
    raw dup1 (by decide +native) (by evm_ov)]
  exact ⟨_, _, by simpa using rd927⟩

/-! ### `join(uint256)` calldata decode -/

private theorem decodeJoinUint256_ok {cd : ByteArray} {x : Solm.Ident}
    (hsz36 : 36 ≤ cd.size) :
    decodeCalldataWithMode DecodeMode.legacySolc05 [x] [abiUInt256] cd =
      some ((∅ : Solm.Store).insert x (.int (Int.ofNat (calldataWord cd 4).toNat))) := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  have htake4 : ((cd.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]; omega
  have hword4 : ABI.bytesToWord ((cd.toList.drop 4).take 32) = calldataWord cd 4 :=
    decode_word_at_eq cd 4 (by omega) (by norm_num)
  rw [decodeCalldataWithMode_legacyScalarWords_eq (names := [x]) (types := [abiUInt256]) (cd := cd)
    (by decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  simp only [decodeScalarWordsWithMode?]
  rw [decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05)
    (bytes := cd.toList.drop 4) (start := 0) htake4]
  change decodeCalldata.insertValues [x]
      [.int (Int.ofNat (ABI.bytesToWord ((cd.toList.drop 4).take 32)).toNat)] ∅ =
    some ((∅ : Solm.Store).insert x (.int (Int.ofNat (calldataWord cd 4).toNat)))
  rw [hword4]
  simp [decodeCalldata.insertValues]

private theorem decodeJoinUint256_none_short {cd : ByteArray} {x : Solm.Ident}
    (hsz4 : 4 ≤ cd.size) (hshort : cd.size < 36) :
    decodeCalldataWithMode DecodeMode.legacySolc05 [x] [abiUInt256] cd = none := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  rw [decodeCalldataWithMode_legacyScalarWords_eq (names := [x]) (types := [abiUInt256]) (cd := cd)
    (by decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  simp only [decodeScalarWordsWithMode?]
  have htake0n : ¬ ((cd.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]; omega
  rw [decodeScalarWordWithMode_uint256_none_short (mode := DecodeMode.legacySolc05) (start := 0)
    (by simpa using htake0n)]
  simp only [Option.bind, bind]

theorem potDecode_join_ok {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (joinTransition.params.map Param.name)
      (transitionSignature joinTransition).paramTypes I.calldata =
        some ((∅ : Store).insert "wad" (.int (Int.ofNat (joinWadWord I).toNat))) := by
  show decodeCalldataWithMode DecodeMode.legacySolc05 ["wad"] [abiUInt256] I.calldata = _
  simpa [joinWadWord] using decodeJoinUint256_ok (cd := I.calldata) (x := "wad") hsz36

theorem potDecode_join_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36) :
    decodeCalldataWithMode config.abiDecodeMode (joinTransition.params.map Param.name)
      (transitionSignature joinTransition).paramTypes I.calldata = none := by
  show decodeCalldataWithMode DecodeMode.legacySolc05 ["wad"] [abiUInt256] I.calldata = _
  exact decodeJoinUint256_none_short (cd := I.calldata) (x := "wad") hsz4 hshort

/-! ### `join(uint256)` — fire the `vat.move` CALL and thread the outcome -/

/-- Logic 927 → 943: `extcodesize(vat) ≠ 0` ⇒ fire the `move` CALL, exposing the opaque `Θ`-link
    and the post-`CALL` cursor (memory unchanged, `retSize = 0`). -/
theorem potJoinX_postCall {cA σ'' I} {g : Sat256} {s0 : State} {k C : ℕ} {sel : UInt256}
    {mem : ByteArray} (hmemSize : mem.size = 96)
    (hdepth : I.depth.val < 1024)
    (hcodeSize : Reasoning.Theory.extCodeSizeWord σ'' (joinVatMasked σ'' I) ≠ ⟨0⟩)
    (h : RD potBytecode I g s0 ⟨927⟩
      (joinVatMasked σ'' I :: joinVatMasked σ'' I :: ⟨0⟩ :: ⟨128⟩ :: ⟨100⟩ :: ⟨128⟩ :: ⟨0⟩ ::
        ⟨228⟩ :: potMoveSelectorWord :: joinVatMasked σ'' I :: joinWadWord I :: ⟨301⟩ :: sel :: [])
      (potMoveCalldataMem (joinCallerWord I) (joinThisWord I)
        (UInt256.mul (joinChi σ'' I) (joinWadWord I)) mem)
      (UInt256.ofNat 8) ByteArray.empty (cA, σ'') k C) :
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap) (z : Bool) (o : ByteArray)
      (A_in : Substate) (callGas : UInt256) (mem' : ByteArray) (aw' : UInt256) (k' C' : ℕ),
      (∃ (g'' : UInt256) (A' : Substate),
        (cA', σ', g'', A', z, o) = Ethereum.EVM.Θ I.blobVersionedHashes cA s0.genesisBlockHeader
          s0.blocks σ'' s0.σ₀ A_in
          (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner)) I.sender
          (AccountAddress.ofUInt256 (joinVatMasked σ'' I))
          (toExecute σ'' (AccountAddress.ofUInt256 (joinVatMasked σ'' I)))
          callGas (UInt256.ofNat I.gasPrice) ⟨0⟩ ⟨0⟩
          ((potMoveCalldataMem (joinCallerWord I) (joinThisWord I)
            (UInt256.mul (joinChi σ'' I) (joinWadWord I)) mem).readWithPadding 128 100)
          (I.depth + 1) I.header I.perm)
      ∧ RD potBytecode I g s0 ⟨943⟩
          ((if z then ⟨1⟩ else ⟨0⟩) :: ⟨228⟩ :: potMoveSelectorWord :: joinVatMasked σ'' I ::
            joinWadWord I :: ⟨301⟩ :: sel :: [])
          mem' aw' o (cA', σ') k' C'
      ∧ o.size < UInt256.size := by
  obtain ⟨gasWord, k1, C1, rd942⟩ :=
    RD.solcExtcodesizeGuardOkGas (pc := ⟨927⟩) (okPc := ⟨939⟩) h hcodeSize
      (by decide +native) (by decide +native) (by decide +native) (by decide +native)
      (by decide +native) (by decide +native) (by jump_dest) (by decide +native)
      (by decide +native) (by decide +native) (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨cA', σ', z, o, A_in, callGas, k', C', hΘ, rd943raw, hosz⟩ :=
    RD.call (target := joinVatMasked σ'' I) rd942 (by decide +native) hdepth (by evm_ov)
  exact ⟨cA', σ', z, o, A_in, callGas, _, _, k', C', hΘ, rd943raw, hosz⟩

/-- Post-`CALL` success tail (`z = true`): pop the frame and `STOP`, returning empty data. -/
theorem potJoinX_successTail {cA' σ' I} {g : Sat256} {s0 : State} {k C : ℕ} {sel : UInt256}
    {mem : ByteArray} {aw : UInt256} {o : ByteArray}
    (h : RD potBytecode I g s0 ⟨943⟩
      (⟨1⟩ :: ⟨228⟩ :: potMoveSelectorWord :: joinVatMasked σ' I ::
        joinWadWord I :: ⟨301⟩ :: sel :: [])
      mem aw o (cA', σ') k C) :
    RDret potBytecode g s0 (cA', σ') ByteArray.empty := by
  obtain ⟨k1, C1, rd961⟩ :=
    RD.solcCallSuccessGuardOk (pc := ⟨943⟩) (okPc := ⟨959⟩) h (by decide)
      (by decide +native) (by decide +native) (by decide +native) (by decide +native)
      (by decide +native) (by jump_dest) (by decide +native) (by decide +native)
      (by simp only [List.length_cons, List.length_nil]; omega)
  have rd301 := evm_run rd961 with [
    raw pop (by decide +native) (by evm_ov),
    raw pop (by decide +native) (by evm_ov),
    raw pop (by decide +native) (by evm_ov),
    raw pop (by decide +native) (by evm_ov),
    raw jump (by decide +native) (by jump_dest) (by evm_ov)]
  have rd302 := rd301.jumpdest (by decide +native) (by evm_ov)
  exact RD.stop rd302 (by decide +native) (by simp only [List.length_cons, List.length_nil]; omega)

/-- Post-`CALL` failure tail (`z = false`): the solc success guard bubbles the revert. -/
theorem potJoinX_failTail {cA' σ' I} {g : Sat256} {s0 : State} {k C : ℕ} {sel : UInt256}
    {mem : ByteArray} {aw : UInt256} {o : ByteArray}
    (hosz : o.size < UInt256.size)
    (h : RD potBytecode I g s0 ⟨943⟩
      (⟨0⟩ :: ⟨228⟩ :: potMoveSelectorWord :: joinVatMasked σ' I ::
        joinWadWord I :: ⟨301⟩ :: sel :: [])
      mem aw o (cA', σ') k C) :
    RDrev potBytecode g s0 := by
  exact RD.solcCallSuccessGuardMissing (pc := ⟨943⟩) (okPc := ⟨959⟩) h rfl
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native) hosz
    (by simp only [List.length_cons, List.length_nil]; omega)

/-- Post-`CALL` success tail with an arbitrary leftover `vat` word (the `POP`s discard it): the
    stack-`vat` value need not match the (post-`CALL`) returned account map. -/
theorem potJoinX_successTailGen {cA' σ' I} {g : Sat256} {s0 : State} {k C : ℕ} {sel vw : UInt256}
    {mem : ByteArray} {aw : UInt256} {o : ByteArray}
    (h : RD potBytecode I g s0 ⟨943⟩
      (⟨1⟩ :: ⟨228⟩ :: potMoveSelectorWord :: vw :: joinWadWord I :: ⟨301⟩ :: sel :: [])
      mem aw o (cA', σ') k C) :
    RDret potBytecode g s0 (cA', σ') ByteArray.empty := by
  obtain ⟨k1, C1, rd961⟩ :=
    RD.solcCallSuccessGuardOk (pc := ⟨943⟩) (okPc := ⟨959⟩) h (by decide)
      (by decide +native) (by decide +native) (by decide +native) (by decide +native)
      (by decide +native) (by jump_dest) (by decide +native) (by decide +native)
      (by simp only [List.length_cons, List.length_nil]; omega)
  have rd301 := evm_run rd961 with [
    raw pop (by decide +native) (by evm_ov),
    raw pop (by decide +native) (by evm_ov),
    raw pop (by decide +native) (by evm_ov),
    raw pop (by decide +native) (by evm_ov),
    raw jump (by decide +native) (by jump_dest) (by evm_ov)]
  have rd302 := rd301.jumpdest (by decide +native) (by evm_ov)
  exact RD.stop rd302 (by decide +native) (by simp only [List.length_cons, List.length_nil]; omega)

/-- Post-`CALL` failure tail with an arbitrary leftover `vat` word. -/
theorem potJoinX_failTailGen {cA' σ' I} {g : Sat256} {s0 : State} {k C : ℕ} {sel vw : UInt256}
    {mem : ByteArray} {aw : UInt256} {o : ByteArray}
    (hosz : o.size < UInt256.size)
    (h : RD potBytecode I g s0 ⟨943⟩
      (⟨0⟩ :: ⟨228⟩ :: potMoveSelectorWord :: vw :: joinWadWord I :: ⟨301⟩ :: sel :: [])
      mem aw o (cA', σ') k C) :
    RDrev potBytecode g s0 := by
  exact RD.solcCallSuccessGuardMissing (pc := ⟨943⟩) (okPc := ⟨959⟩) h rfl
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native) hosz
    (by simp only [List.length_cons, List.length_nil]; omega)

/-- Logic 927: `extcodesize(vat) = 0` ⇒ the checked external call reverts. -/
theorem potJoinX_ecsZero {cA σ'' I} {g : Sat256} {s0 : State} {k C : ℕ} {sel : UInt256}
    {mem : ByteArray}
    (hcodeSize : Reasoning.Theory.extCodeSizeWord σ'' (joinVatMasked σ'' I) = ⟨0⟩)
    (h : RD potBytecode I g s0 ⟨927⟩
      (joinVatMasked σ'' I :: joinVatMasked σ'' I :: ⟨0⟩ :: ⟨128⟩ :: ⟨100⟩ :: ⟨128⟩ :: ⟨0⟩ ::
        ⟨228⟩ :: potMoveSelectorWord :: joinVatMasked σ'' I :: joinWadWord I :: ⟨301⟩ :: sel :: [])
      mem (UInt256.ofNat 8) ByteArray.empty (cA, σ'') k C) :
    RDrev potBytecode g s0 := by
  exact RD.solcExtcodesizeGuardMissing (pc := ⟨927⟩) (okPc := ⟨939⟩) h hcodeSize
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by simp only [List.length_cons, List.length_nil]; omega)

/-! ### `join(uint256)` — checked-arithmetic overflow reverts (EVM side) -/

/-- Logic `@757`: `pie[caller] + wad` overflows ⇒ the `_add` check reverts. -/
theorem potJoinX_pieOverflowReverts {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ} {sel : UInt256}
    (hover : UInt256.size ≤ (joinPie0 σ I).toNat + (joinWadWord I).toNat)
    (h : RD potBytecode I g s0 ⟨757⟩ [joinWadWord I, ⟨301⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev potBytecode g s0 := by
  have rdPre1 := evm_run h with [
    raw jumpdest (by decide +native) (by evm_ov),
    raw caller (by decide +native) (by evm_ov),
    raw push1 ⟨0⟩ (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov)]
  have rd764 := rdPre1.mstore 0 (wordAt0Mem (joinCallerWord I) solcFreePtrMem)
    (UInt256.ofNat 3) (by decide +native) mem_cost (by rfl) (by decide +native) (by evm_ov)
  have rdPre2 := evm_run rd764 with [
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨32⟩ (by decide +native) (by evm_ov)]
  have rd769 := rdPre2.mstore 0 (joinPieHashMem I)
    (UInt256.ofNat 3) (by decide +native) mem_cost (by rfl) (by decide +native) (by evm_ov)
  have rdPre3 := evm_run rd769 with [
    raw push1 ⟨64⟩ (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov)]
  have rd773 := rdPre3.keccak256 0 (joinPieSlot I)
    (UInt256.ofNat 3) (by decide +native) mem_cost (joinPieSlot_keccak I)
    (by decide +native) (by evm_ov)
  obtain ⟨_, _, rd773v⟩ := rd773.sload (by decide +native) (by evm_ov)
  have rdPre4 := evm_run rd773v with [
    raw push2 ⟨783⟩ (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw dup3 (by decide +native) (by evm_ov),
    raw push2 ⟨2278⟩ (by decide +native) (by evm_ov)]
  have rd2278 := rdPre4.jump (by decide +native) (by jump_dest) (by evm_ov)
  exact RD.potAddReverts rd2278 hover
    (by simp only [List.length_cons, List.length_nil]; omega)

/-- Logic `@800`: `Pie + wad` overflows ⇒ the `_add` check reverts. -/
theorem potJoinX_PieOverflowReverts {cA σ' I} {g : Sat256} {s0 : State} {k C : ℕ} {sel : UInt256}
    {mem : ByteArray}
    (hover : UInt256.size ≤ (solcSlotWord σ' I ⟨2⟩).toNat + (joinWadWord I).toNat)
    (h : RD potBytecode I g s0 ⟨800⟩ [joinWadWord I, ⟨301⟩, sel]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ') k C) :
    RDrev potBytecode g s0 := by
  have rd802 := h.push1 ⟨2⟩ (by decide +native) (by evm_ov)
  obtain ⟨_, _, rd803⟩ := rd802.sload (by decide +native) (by evm_ov)
  have rdPre := evm_run rd803 with [
    raw push2 ⟨812⟩ (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw dup3 (by decide +native) (by evm_ov),
    raw push2 ⟨2278⟩ (by decide +native) (by evm_ov)]
  have rd2278 := rdPre.jump (by decide +native) (by jump_dest) (by evm_ov)
  exact RD.potAddReverts rd2278 hover
    (by simp only [List.length_cons, List.length_nil]; omega)

/-- Logic `@816`: `chi * wad` overflows ⇒ the `_mul` check reverts. -/
theorem potJoinX_mulOverflowReverts {cA σ'' I} {g : Sat256} {s0 : State} {k C : ℕ} {sel : UInt256}
    {mem : ByteArray}
    (hover : UInt256.size ≤ (joinChi σ'' I).toNat * (joinWadWord I).toNat)
    (h : RD potBytecode I g s0 ⟨816⟩ [joinWadWord I, ⟨301⟩, sel]
      mem (UInt256.ofNat 3) ByteArray.empty (cA, σ'') k C) :
    RDrev potBytecode g s0 := by
  have rd818 := h.push1 ⟨5⟩ (by decide +native) (by evm_ov)
  obtain ⟨_, _, rd819⟩ := rd818.sload (by decide +native) (by evm_ov)
  have rd821 := rd819.push1 ⟨4⟩ (by decide +native) (by evm_ov)
  obtain ⟨_, _, rd822⟩ := rd821.sload (by decide +native) (by evm_ov)
  have rdPre := evm_run rd822 with [
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨160⟩ (by decide +native) (by evm_ov),
    raw shl (by decide +native) (by evm_ov),
    raw sub (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw swap2 (by decide +native) (by evm_ov),
    raw and (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw push4 potMoveSelectorWord (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw caller (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov)]
  have rd843 := rdPre.address (by decide +native) (by evm_ov)
  have rdPre2 := evm_run rd843 with [
    raw swap1 (by decide +native) (by evm_ov),
    raw push2 ⟨853⟩ (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw dup7 (by decide +native) (by evm_ov),
    raw push2 ⟨2300⟩ (by decide +native) (by evm_ov)]
  have rd2300 := rdPre2.jump (by decide +native) (by jump_dest) (by evm_ov)
  exact RD.potMulReverts rd2300 hover
    (by simp only [List.length_cons, List.length_nil]; omega)

/-! ### `join(uint256)` — Solm-side storage reads / writes / guards -/

theorem evalExpr_joinChiOf {evm : EVM.State} {locals : Store}
    (hbase : locals.get? "chi" = none) :
    evalExpr? config { contract := contract, locals := locals } evm (.storage chiRef) =
      .ok (.int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨4⟩).toNat)) :=
  evalExpr_storage_scalar_value (slot := chiRef)
    (er := ({ base := "chi", steps := [] } : EvaledStorageRef))
    (t := .int uint256Int) (loc := wordLoc ⟨4⟩)
    hbase
    (by simp [chiRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind])
    (by simp [storageTypeAt?, contract, storageDecls, uint256St])
    (by rfl)
    (potStorageLocLoad_uint256 evm ⟨4⟩)

theorem evalExpr_joinPieScalarOf {evm : EVM.State} {locals : Store}
    (hbase : locals.get? "Pie" = none) :
    evalExpr? config { contract := contract, locals := locals } evm (.storage PieRef) =
      .ok (.int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩).toNat)) :=
  evalExpr_storage_scalar_value (slot := PieRef)
    (er := ({ base := "Pie", steps := [] } : EvaledStorageRef))
    (t := .int uint256Int) (loc := wordLoc ⟨2⟩)
    hbase
    (by simp [PieRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind])
    (by simp [storageTypeAt?, contract, storageDecls, uint256St])
    (by rfl)
    (potStorageLocLoad_uint256 evm ⟨2⟩)

theorem evalExpr_joinRhoOf {evm : EVM.State} {locals : Store}
    (hbase : locals.get? "rho" = none) :
    evalExpr? config { contract := contract, locals := locals } evm (.storage rhoRef) =
      .ok (.int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨7⟩).toNat)) :=
  evalExpr_storage_scalar_value (slot := rhoRef)
    (er := ({ base := "rho", steps := [] } : EvaledStorageRef))
    (t := .int uint256Int) (loc := wordLoc ⟨7⟩)
    hbase
    (by simp [rhoRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind])
    (by simp [storageTypeAt?, contract, storageDecls, uint256St])
    (by rfl)
    (potStorageLocLoad_uint256 evm ⟨7⟩)

theorem evalExpr_joinVatOf {evm : EVM.State} {locals : Store}
    (hbase : locals.get? "vat" = none) :
    evalExpr? config { contract := contract, locals := locals } evm (.storage vatRef) =
      .ok (.address (AccountAddress.ofNat
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨5⟩)
          solcAddrMask).toNat)) :=
  evalExpr_storage_scalar_value (slot := vatRef)
    (er := ({ base := "vat", steps := [] } : EvaledStorageRef))
    (t := .address) (loc := addrLoc ⟨5⟩)
    hbase
    (by simp [vatRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind])
    (by simp [storageTypeAt?, contract, storageDecls, addrSt])
    (by rfl)
    (potStorageLocLoad_address_offset0 evm ⟨5⟩)

theorem evalStorageRef_joinPie (evm : EVM.State) {locals : Store} :
    evalStorageRef config { contract := contract, locals := locals } evm (pieRef sender) =
      .ok ({ base := "pie",
             steps := [.mindex (.address evm.executionEnv.source)] } : EvaledStorageRef) := by
  simp [pieRef, sender, evalStorageRef, evalStorageRefSteps, evalStorageRefStep,
    evalExpr?, envValue, valueToKey?, EvalResult.ofOption, EvalResult.bind, pure, bind]

theorem evalExpr_joinPieMapOf {evm : EVM.State} {locals : Store}
    (hbase : locals.get? "pie" = none) :
    evalExpr? config { contract := contract, locals := locals } evm (.storage (pieRef sender)) =
      .ok (.int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (pieSlot (.address evm.executionEnv.source))).toNat)) :=
  evalExpr_storage_scalar_value (slot := pieRef sender)
    (er := ({ base := "pie",
              steps := [.mindex (.address evm.executionEnv.source)] } : EvaledStorageRef))
    (t := .int uint256Int) (loc := wordLoc (pieSlot (.address evm.executionEnv.source)))
    hbase
    (evalStorageRef_joinPie evm)
    (by simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, uint256St])
    (by rfl)
    (potStorageLocLoad_uint256 evm (pieSlot (.address evm.executionEnv.source)))

theorem joinAssignPieMap (evm : EVM.State) {locals : Store} (v : UInt256)
    (hbase : locals.get? "pie" = none) :
    assignStorageRef? config { contract := contract, locals := locals } evm
        .storage (pieRef sender) (.int (Int.ofNat v.toNat)) =
      .ok ({ contract := contract, locals := locals },
        Solm.EVM.storageStore evm evm.executionEnv.codeOwner
          (pieSlot (.address evm.executionEnv.source)) v) := by
  apply assignStorageRef_storage_scalar (ty := uint256St)
    (loc := wordLoc (pieSlot (.address evm.executionEnv.source)))
    hbase (evalStorageRef_joinPie evm)
    (by simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, uint256St]) (by rfl)
  exact potStorageLocStore_uint256 evm (pieSlot (.address evm.executionEnv.source)) v

theorem joinAssignPieScalar (evm : EVM.State) {locals : Store} (v : UInt256)
    (hbase : locals.get? "Pie" = none) :
    assignStorageRef? config { contract := contract, locals := locals } evm
        .storage PieRef (.int (Int.ofNat v.toNat)) =
      .ok ({ contract := contract, locals := locals },
        Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨2⟩ v) := by
  apply assignStorageRef_storage_scalar (ty := uint256St) (loc := wordLoc ⟨2⟩)
    (er := ({ base := "Pie", steps := [] } : EvaledStorageRef))
    hbase
    (by simp [PieRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind])
    (by simp [storageTypeAt?, contract, storageDecls, uint256St]) (by rfl)
  exact potStorageLocStore_uint256 evm ⟨2⟩ v

theorem evalExpr_joinExtCodeGuard_true {evm : EVM.State} {locals : Store}
    {receiver : Expr} {target : AccountAddress}
    (hreceiver :
      evalExpr? config { contract := contract, locals := locals } evm receiver =
        .ok (.address target))
    (hcode :
      0 < (UInt256.ofNat ((evm.lookupAccount target).option 0 (fun acc => acc.code.size))).toNat) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.binary .gt (.extCodeSize receiver) (.intLit 0)) = .ok (.bool true) := by
  simp [evalExpr?, EvalResult.bind, bind, hreceiver, evalBinaryOp?, EVM.Word.ofNat, hcode]

theorem evalExpr_joinExtCodeGuard_false {evm : EVM.State} {locals : Store}
    {receiver : Expr} {target : AccountAddress}
    (hreceiver :
      evalExpr? config { contract := contract, locals := locals } evm receiver =
        .ok (.address target))
    (hcode :
      (UInt256.ofNat ((evm.lookupAccount target).option 0 (fun acc => acc.code.size))).toNat = 0) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.binary .gt (.extCodeSize receiver) (.intLit 0)) = .ok (.bool false) := by
  simp [evalExpr?, EvalResult.bind, bind, hreceiver, evalBinaryOp?, EVM.Word.ofNat, hcode]

/-- The Solm mapping slot for `pie[msg.sender]` equals the EVM keccak slot. -/
theorem joinPieSlot_eq (I : ExecutionEnv) :
    pieSlot (.address I.source) = joinPieSlot I := by
  show mapSlot (keyValueToWord (.address I.source)) ⟨1⟩ = solcMappingSlot ⟨1⟩ (joinCallerWord I)
  rw [keyValueToWord_address]; rfl

/-! ### `join(uint256)` — Solm-side read/store bridges -/

/-- Bridge the Solm `storageLoad` at `I.codeOwner` to the EVM-side `solcSlotWord`. -/
theorem joinStorageLoad_eq (evm : EVM.State) (I : ExecutionEnv) (slot : UInt256) :
    Solm.EVM.storageLoad evm I.codeOwner slot = solcSlotWord evm.accountMap I slot := by
  simp [solcSlotWord, Solm.EVM.storageLoad, State.lookupAccount, Ethereum.Account.lookupStorage]

/-- The Solm `vat.move` target address is the EVM masked `vat` word (given read agreement). -/
theorem joinVatTarget_eq (σ'' : AccountMap) (I : ExecutionEnv) (v : UInt256)
    (hveq : joinVatRaw σ'' I = v) :
    EVM.address (AccountAddress.ofNat (UInt256.land v solcAddrMask).toNat)
      = AccountAddress.ofUInt256 (joinVatMasked σ'' I) := by
  rw [joinVatMasked, hveq]
  apply Fin.ext
  show (UInt256.land v solcAddrMask).toNat % EVM.addressModulus % AccountAddress.size
      = (UInt256.land v solcAddrMask).val % AccountAddress.size % AccountAddress.size
  rw [show EVM.addressModulus = AccountAddress.size from by decide]
  rfl

/-- Read `Pie` (slot 2) in `I.codeOwner`-normalized form. -/
theorem joinReadPieScalar {evm : EVM.State} {locals : Store} {I : ExecutionEnv}
    (hco : evm.executionEnv.codeOwner = I.codeOwner) (hbase : locals.get? "Pie" = none) :
    evalExpr? config { contract := contract, locals := locals } evm (.storage PieRef)
      = .ok (.int (Int.ofNat (Solm.EVM.storageLoad evm I.codeOwner ⟨2⟩).toNat)) := by
  have h := evalExpr_joinPieScalarOf (evm := evm) (locals := locals) hbase
  rw [hco] at h; exact h

/-- Read `chi` (slot 4) in `I.codeOwner`-normalized form. -/
theorem joinReadChi {evm : EVM.State} {locals : Store} {I : ExecutionEnv}
    (hco : evm.executionEnv.codeOwner = I.codeOwner) (hbase : locals.get? "chi" = none) :
    evalExpr? config { contract := contract, locals := locals } evm (.storage chiRef)
      = .ok (.int (Int.ofNat (Solm.EVM.storageLoad evm I.codeOwner ⟨4⟩).toNat)) := by
  have h := evalExpr_joinChiOf (evm := evm) (locals := locals) hbase
  rw [hco] at h; exact h

/-- Read `vat` (slot 5, masked to an address) in `I.codeOwner`-normalized form. -/
theorem joinReadVat {evm : EVM.State} {locals : Store} {I : ExecutionEnv}
    (hco : evm.executionEnv.codeOwner = I.codeOwner) (hbase : locals.get? "vat" = none) :
    evalExpr? config { contract := contract, locals := locals } evm (.storage vatRef)
      = .ok (.address (AccountAddress.ofNat
        (UInt256.land (Solm.EVM.storageLoad evm I.codeOwner ⟨5⟩) solcAddrMask).toNat)) := by
  have h := evalExpr_joinVatOf (evm := evm) (locals := locals) hbase
  rw [hco] at h; exact h

/-- Read `pie[caller]` (mapping slot) in `I.codeOwner`/`I.source`-normalized form. -/
theorem joinReadPieMap {evm : EVM.State} {locals : Store} {I : ExecutionEnv}
    (hco : evm.executionEnv.codeOwner = I.codeOwner)
    (hsrc : evm.executionEnv.source = I.source) (hbase : locals.get? "pie" = none) :
    evalExpr? config { contract := contract, locals := locals } evm (.storage (pieRef sender))
      = .ok (.int (Int.ofNat
        (Solm.EVM.storageLoad evm I.codeOwner (pieSlot (.address I.source))).toNat)) := by
  have h := evalExpr_joinPieMapOf (evm := evm) (locals := locals) hbase
  rw [hco, hsrc] at h; exact h

set_option maxHeartbeats 1000000 in
/-- Logic 927 → revert at the call-depth limit (`I.depth = 1024`): the `move` CALL never fires,
    returns `0`, and the solc success guard bubbles the revert. -/
theorem potJoinX_depthLimitReverts {cA σ'' I} {g : Sat256} {s0 : State} {k C : ℕ} {sel : UInt256}
    {mem : ByteArray}
    (hdepth : I.depth = 1024)
    (hcodeSize : Reasoning.Theory.extCodeSizeWord σ'' (joinVatMasked σ'' I) ≠ ⟨0⟩)
    (h : RD potBytecode I g s0 ⟨927⟩
      (joinVatMasked σ'' I :: joinVatMasked σ'' I :: ⟨0⟩ :: ⟨128⟩ :: ⟨100⟩ :: ⟨128⟩ :: ⟨0⟩ ::
        ⟨228⟩ :: potMoveSelectorWord :: joinVatMasked σ'' I :: joinWadWord I :: ⟨301⟩ :: sel :: [])
      (potMoveCalldataMem (joinCallerWord I) (joinThisWord I)
        (UInt256.mul (joinChi σ'' I) (joinWadWord I)) mem)
      (UInt256.ofNat 8) ByteArray.empty (cA, σ'') k C) :
    RDrev potBytecode g s0 := by
  obtain ⟨gasWord, k1, C1, rd942⟩ :=
    RD.solcExtcodesizeGuardOkGas (pc := ⟨927⟩) (okPc := ⟨939⟩) h hcodeSize
      (by decide +native) (by decide +native) (by decide +native) (by decide +native)
      (by decide +native) (by decide +native) (by jump_dest) (by decide +native)
      (by decide +native) (by decide +native) (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨k', C', rd943⟩ :=
    RD.callDepthLimit rd942 (by decide +native) hdepth
      (by simp only [List.length_cons, List.length_nil]; omega)
  exact potJoinX_failTail (by simp only [ByteArray.empty, ByteArray.size]; decide) rd943

/-! ### `join(uint256)` — Solm-side statement drivers (shared prefix) -/

set_option maxHeartbeats 1000000 in
/-- Runs the Solm body prefix through the `pie[caller] += wad` store (statements 0–4),
    leaving the tail obligation from the post-`pie`-store frame/state. -/
theorem potJoinSolmDriverPie {cA gh bl σ_solm σ₀ A I} {g : Sat256} {result : ExecResult}
    (hwv : I.weiValue = ⟨0⟩)
    (hrho : joinNowWord I
      = Solm.EVM.storageLoad (initState cA gh bl σ_solm σ₀ g A I) I.codeOwner ⟨7⟩)
    (hpieFit : (Solm.EVM.storageLoad (initState cA gh bl σ_solm σ₀ g A I) I.codeOwner
        (pieSlot (.address I.source))).toNat + (joinWadWord I).toNat < UInt256.size)
    (htail : ExecBlock config
        { contract := contract,
          locals := ((∅ : Store).insert "wad" (.int (Int.ofNat (joinWadWord I).toNat))).insert
            "pieNew" (.int (Int.ofNat ((Solm.EVM.storageLoad (initState cA gh bl σ_solm σ₀ g A I)
              I.codeOwner (pieSlot (.address I.source))) + joinWadWord I).toNat)) }
        (Solm.EVM.storageStore (initState cA gh bl σ_solm σ₀ g A I) I.codeOwner
          (pieSlot (.address I.source))
          ((Solm.EVM.storageLoad (initState cA gh bl σ_solm σ₀ g A I) I.codeOwner
            (pieSlot (.address I.source))) + joinWadWord I))
        [ .letDecl "PieNew" (some uint256) (add256 (.storage PieRef) (.var "wad")),
          .require (.binary .ge (.var "PieNew") (.storage PieRef)),
          .assign .storage PieRef (.var "PieNew"),
          .internalCall "_mul" [.storage chiRef, .var "wad"] "rad",
          .require (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)),
          .externalCall (.storage vatRef) "move" (.intLit 0) [sender, .env .this, .var "rad"]
            "_moveRet" ]
        result) :
    ExecBlock config
      { contract := contract,
        locals := (∅ : Store).insert "wad" (.int (Int.ofNat (joinWadWord I).toNat)) }
      (initState cA gh bl σ_solm σ₀ g A I) joinTransition.body result := by
  have hpieValNat : ((Solm.EVM.storageLoad (initState cA gh bl σ_solm σ₀ g A I) I.codeOwner
      (pieSlot (.address I.source))) + joinWadWord I).toNat
      = (Solm.EVM.storageLoad (initState cA gh bl σ_solm σ₀ g A I) I.codeOwner
          (pieSlot (.address I.source))).toNat + (joinWadWord I).toNat := by
    rw [uadd_toNat, Nat.mod_eq_of_lt hpieFit]
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue
    (evalExpr_eq_int_true (a := Int.ofNat (joinNowWord I).toNat)
      (b := Int.ofNat (Solm.EVM.storageLoad (initState cA gh bl σ_solm σ₀ g A I)
        I.codeOwner ⟨7⟩).toNat)
      (by simp only [evalExpr?, envValue, joinNowWord, pure]; rfl)
      (evalExpr_joinRhoOf (by simp)) (by rw [hrho]))) ?_
  refine ExecBlock.consNormal (ExecStmt.letDecl
    (evalExpr_add256_ok
      (a := Solm.EVM.storageLoad (initState cA gh bl σ_solm σ₀ g A I) I.codeOwner
        (pieSlot (.address I.source)))
      (b := joinWadWord I)
      (sum := (Solm.EVM.storageLoad (initState cA gh bl σ_solm σ₀ g A I) I.codeOwner
        (pieSlot (.address I.source))) + joinWadWord I)
      (evalExpr_joinPieMapOf (by simp))
      (evalExpr_varUInt256 (by simp)) rfl hpieFit)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue
    (evalExpr_ge_uint256_true
      (a := (Solm.EVM.storageLoad (initState cA gh bl σ_solm σ₀ g A I) I.codeOwner
        (pieSlot (.address I.source))) + joinWadWord I)
      (b := Solm.EVM.storageLoad (initState cA gh bl σ_solm σ₀ g A I) I.codeOwner
        (pieSlot (.address I.source)))
      (evalExpr_varUInt256 (by simp))
      (evalExpr_joinPieMapOf (by simp)) (by rw [hpieValNat]; omega))) ?_
  refine ExecBlock.consNormal (ExecStmt.assign
    (value := .int (Int.ofNat ((Solm.EVM.storageLoad (initState cA gh bl σ_solm σ₀ g A I)
      I.codeOwner (pieSlot (.address I.source))) + joinWadWord I).toNat))
    (evalExpr_varUInt256 (by simp))
    (joinAssignPieMap (initState cA gh bl σ_solm σ₀ g A I)
      ((Solm.EVM.storageLoad (initState cA gh bl σ_solm σ₀ g A I) I.codeOwner
        (pieSlot (.address I.source))) + joinWadWord I) (by simp))) ?_
  exact htail

set_option maxHeartbeats 1000000 in
/-- Runs statements 5–7 (`Pie += wad` store), from the post-`pie`-store frame/state. -/
theorem potJoinSolmMulSeg {cA gh bl σ_solm σ₀ A I} {g : Sat256} {result : ExecResult}
    {PIEV : UInt256} {pnV : Value}
    (hPieFit : (Solm.EVM.storageLoad
        (Solm.EVM.storageStore (initState cA gh bl σ_solm σ₀ g A I) I.codeOwner
          (pieSlot (.address I.source)) PIEV) I.codeOwner ⟨2⟩).toNat
        + (joinWadWord I).toNat < UInt256.size)
    (htail : ExecBlock config
        { contract := contract,
          locals := ((((∅ : Store).insert "wad" (.int (Int.ofNat (joinWadWord I).toNat))).insert
            "pieNew" pnV).insert "PieNew" (.int (Int.ofNat ((Solm.EVM.storageLoad
              (Solm.EVM.storageStore (initState cA gh bl σ_solm σ₀ g A I) I.codeOwner
                (pieSlot (.address I.source)) PIEV) I.codeOwner ⟨2⟩) + joinWadWord I).toNat))) }
        (Solm.EVM.storageStore (Solm.EVM.storageStore (initState cA gh bl σ_solm σ₀ g A I) I.codeOwner
          (pieSlot (.address I.source)) PIEV) I.codeOwner ⟨2⟩
          ((Solm.EVM.storageLoad (Solm.EVM.storageStore (initState cA gh bl σ_solm σ₀ g A I)
            I.codeOwner (pieSlot (.address I.source)) PIEV) I.codeOwner ⟨2⟩) + joinWadWord I))
        [ .internalCall "_mul" [.storage chiRef, .var "wad"] "rad",
          .require (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)),
          .externalCall (.storage vatRef) "move" (.intLit 0) [sender, .env .this, .var "rad"]
            "_moveRet" ]
        result) :
    ExecBlock config
      { contract := contract,
        locals := (((∅ : Store).insert "wad" (.int (Int.ofNat (joinWadWord I).toNat))).insert
          "pieNew" pnV) }
      (Solm.EVM.storageStore (initState cA gh bl σ_solm σ₀ g A I) I.codeOwner
        (pieSlot (.address I.source)) PIEV)
      [ .letDecl "PieNew" (some uint256) (add256 (.storage PieRef) (.var "wad")),
        .require (.binary .ge (.var "PieNew") (.storage PieRef)),
        .assign .storage PieRef (.var "PieNew"),
        .internalCall "_mul" [.storage chiRef, .var "wad"] "rad",
        .require (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)),
        .externalCall (.storage vatRef) "move" (.intLit 0) [sender, .env .this, .var "rad"]
          "_moveRet" ]
      result := by
  have hco0 : (initState cA gh bl σ_solm σ₀ g A I).executionEnv.codeOwner = I.codeOwner := rfl
  have he1co : (Solm.EVM.storageStore (initState cA gh bl σ_solm σ₀ g A I) I.codeOwner
      (pieSlot (.address I.source)) PIEV).executionEnv.codeOwner = I.codeOwner := by
    rw [storageStore_executionEnv]; exact hco0
  have hPieValNat : ((Solm.EVM.storageLoad (Solm.EVM.storageStore (initState cA gh bl σ_solm σ₀ g A I)
      I.codeOwner (pieSlot (.address I.source)) PIEV) I.codeOwner ⟨2⟩) + joinWadWord I).toNat
      = (Solm.EVM.storageLoad (Solm.EVM.storageStore (initState cA gh bl σ_solm σ₀ g A I)
          I.codeOwner (pieSlot (.address I.source)) PIEV) I.codeOwner ⟨2⟩).toNat
          + (joinWadWord I).toNat := by
    rw [uadd_toNat, Nat.mod_eq_of_lt hPieFit]
  refine ExecBlock.consNormal (ExecStmt.letDecl
    (evalExpr_add256_ok
      (a := Solm.EVM.storageLoad (Solm.EVM.storageStore (initState cA gh bl σ_solm σ₀ g A I)
        I.codeOwner (pieSlot (.address I.source)) PIEV) I.codeOwner ⟨2⟩)
      (b := joinWadWord I)
      (sum := (Solm.EVM.storageLoad (Solm.EVM.storageStore (initState cA gh bl σ_solm σ₀ g A I)
        I.codeOwner (pieSlot (.address I.source)) PIEV) I.codeOwner ⟨2⟩) + joinWadWord I)
      (joinReadPieScalar he1co (by simp))
      (evalExpr_varUInt256 (by rw [store_get_ne _ _ (by decide), store_get_self])) rfl hPieFit)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue
    (evalExpr_ge_uint256_true
      (a := (Solm.EVM.storageLoad (Solm.EVM.storageStore (initState cA gh bl σ_solm σ₀ g A I)
        I.codeOwner (pieSlot (.address I.source)) PIEV) I.codeOwner ⟨2⟩) + joinWadWord I)
      (b := Solm.EVM.storageLoad (Solm.EVM.storageStore (initState cA gh bl σ_solm σ₀ g A I)
        I.codeOwner (pieSlot (.address I.source)) PIEV) I.codeOwner ⟨2⟩)
      (evalExpr_varUInt256 (by simp)) (joinReadPieScalar he1co (by simp))
      (by rw [hPieValNat]; omega))) ?_
  refine ExecBlock.consNormal (ExecStmt.assign
    (value := .int (Int.ofNat ((Solm.EVM.storageLoad (Solm.EVM.storageStore
      (initState cA gh bl σ_solm σ₀ g A I) I.codeOwner (pieSlot (.address I.source)) PIEV)
      I.codeOwner ⟨2⟩) + joinWadWord I).toNat))
    (evalExpr_varUInt256 (by simp))
    (joinAssignPieScalar _ _ (by simp))) ?_
  rw [he1co]
  exact htail

/-! ### `join(uint256)` — `storageStore` field preservation -/

theorem storageStore_σ₀ (evm : EVM.State) (addr : AccountAddress) (slot val : UInt256) :
    (Solm.EVM.storageStore evm addr slot val).σ₀ = evm.σ₀ := by
  simp only [Solm.EVM.storageStore, State.lookupAccount]
  cases evm.accountMap.find? addr <;> simp [Option.option, State.setAccount, Account.updateStorage]

theorem storageStore_genesis (evm : EVM.State) (addr : AccountAddress) (slot val : UInt256) :
    (Solm.EVM.storageStore evm addr slot val).genesisBlockHeader = evm.genesisBlockHeader := by
  simp only [Solm.EVM.storageStore, State.lookupAccount]
  cases evm.accountMap.find? addr <;> simp [Option.option, State.setAccount, Account.updateStorage]

theorem storageStore_blocks (evm : EVM.State) (addr : AccountAddress) (slot val : UInt256) :
    (Solm.EVM.storageStore evm addr slot val).blocks = evm.blocks := by
  simp only [Solm.EVM.storageStore, State.lookupAccount]
  cases evm.accountMap.find? addr <;> simp [Option.option, State.setAccount, Account.updateStorage]

theorem storageStore_substate (evm : EVM.State) (addr : AccountAddress) (slot val : UInt256) :
    (Solm.EVM.storageStore evm addr slot val).substate = evm.substate := by
  simp only [Solm.EVM.storageStore, State.lookupAccount]
  cases evm.accountMap.find? addr <;> simp [Option.option, State.setAccount, Account.updateStorage]

/-! ### `join(uint256)` — the pre-`CALL` account-map coincidence -/

set_option maxHeartbeats 1000000 in
/-- The EVM post-store state `σ''` (`pie[caller] += wad`, `Pie += wad`) is account-map equivalent
    to the Solm post-store state, given `accountMapEquiv σ_evm σ_solm`. -/
theorem joinPreCallAccounts {cA gh bl σ_evm σ_solm σ₀ A I} {g : Sat256}
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    accountMapEquiv
      (sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner σ_evm (joinPieSlot I) (joinPie0 σ_evm I + joinWadWord I))
        ⟨2⟩ (solcSlotWord (sstoreAccountMap I.codeOwner σ_evm (joinPieSlot I)
          (joinPie0 σ_evm I + joinWadWord I)) I ⟨2⟩ + joinWadWord I))
      (Solm.EVM.storageStore (Solm.EVM.storageStore (initState cA gh bl σ_solm σ₀ g A I) I.codeOwner
        (pieSlot (.address I.source))
        (Solm.EVM.storageLoad (initState cA gh bl σ_solm σ₀ g A I) I.codeOwner
          (pieSlot (.address I.source)) + joinWadWord I)) I.codeOwner ⟨2⟩
        (Solm.EVM.storageLoad (Solm.EVM.storageStore (initState cA gh bl σ_solm σ₀ g A I) I.codeOwner
          (pieSlot (.address I.source))
          (Solm.EVM.storageLoad (initState cA gh bl σ_solm σ₀ g A I) I.codeOwner
            (pieSlot (.address I.source)) + joinWadWord I)) I.codeOwner ⟨2⟩
          + joinWadWord I)).accountMap := by
  have hslot : pieSlot (.address I.source) = joinPieSlot I := joinPieSlot_eq I
  have hpieAgree : solcSlotWord σ_evm I (joinPieSlot I) = solcSlotWord σ_solm I (joinPieSlot I) :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner (joinPieSlot I) ⟨0⟩
  have hpieRead : Solm.EVM.storageLoad (initState cA gh bl σ_solm σ₀ g A I) I.codeOwner
      (pieSlot (.address I.source)) = joinPie0 σ_evm I := by
    rw [joinStorageLoad_eq, hslot]
    show solcSlotWord σ_solm I (joinPieSlot I) = solcSlotWord σ_evm I (joinPieSlot I)
    exact hpieAgree.symm
  rw [storageStore_accountMap, storageStore_accountMap, hpieRead, hslot]
  have hPieEquiv : accountMapEquiv
      (sstoreAccountMap I.codeOwner σ_evm (joinPieSlot I) (joinPie0 σ_evm I + joinWadWord I))
      (sstoreAccountMap I.codeOwner σ_solm (joinPieSlot I) (joinPie0 σ_evm I + joinWadWord I)) :=
    accountMapEquiv_sstoreAccountMap I.codeOwner (joinPieSlot I)
      (joinPie0 σ_evm I + joinWadWord I) hAccounts
  have hPieRead : Solm.EVM.storageLoad
      (Solm.EVM.storageStore (initState cA gh bl σ_solm σ₀ g A I) I.codeOwner (joinPieSlot I)
        (joinPie0 σ_evm I + joinWadWord I)) I.codeOwner ⟨2⟩
      = solcSlotWord (sstoreAccountMap I.codeOwner σ_evm (joinPieSlot I)
          (joinPie0 σ_evm I + joinWadWord I)) I ⟨2⟩ := by
    rw [joinStorageLoad_eq, storageStore_accountMap]
    show solcSlotWord (sstoreAccountMap I.codeOwner σ_solm (joinPieSlot I) _) I ⟨2⟩ = _
    exact (accountMapEquiv_storage_findD hPieEquiv I.codeOwner ⟨2⟩ ⟨0⟩).symm
  rw [hPieRead]
  exact accountMapEquiv_sstoreAccountMap_two I.codeOwner I.codeOwner (joinPieSlot I)
    (joinPie0 σ_evm I + joinWadWord I) ⟨2⟩
    (solcSlotWord (sstoreAccountMap I.codeOwner σ_evm (joinPieSlot I)
      (joinPie0 σ_evm I + joinWadWord I)) I ⟨2⟩ + joinWadWord I) hAccounts

/-! ### `join(uint256)` — `_mul` internal call + `vat.move` external call (Solm side) -/

set_option maxHeartbeats 1000000 in
/-- The `_mul(chi, wad)` internal call, binding `rad := chi * wad` (product fits). -/
theorem joinMulStmt {evm2 : EVM.State} {I : ExecutionEnv} {c wad : UInt256} {L : Store}
    (hco : evm2.executionEnv.codeOwner = I.codeOwner)
    (hc : Solm.EVM.storageLoad evm2 I.codeOwner ⟨4⟩ = c)
    (hwadget : L.get? "wad" = some (.int (Int.ofNat wad.toNat)))
    (hbaseChi : L.get? "chi" = none) (hfit : c.toNat * wad.toNat < UInt256.size) :
    ExecStmt config { contract := contract, locals := L } evm2
      (.internalCall "_mul" [.storage chiRef, .var "wad"] "rad")
      (.ok
        { contract := contract, locals := L.insert "rad" (.int (Int.ofNat (c * wad).toNat)) }
        evm2) := by
  have hargs : evalExprs? config { contract := contract, locals := L } evm2
      [.storage chiRef, .var "wad"] = .ok [.int (Int.ofNat c.toNat), .int (Int.ofNat wad.toNat)] := by
    have hchi := joinReadChi (I := I) hco hbaseChi
    rw [hc] at hchi
    simp only [evalExprs?, evalExpr?, hchi, EvalResult.bind, bind, pure, EvalResult.ofOption, hwadget]
  have hmul := internalCallFunctionReturn (cfg := config)
    (caller := { contract := contract, locals := L }) (evm := evm2) (calleeEvm := evm2)
    (name := "_mul") (retVar := "rad") (args := [.storage chiRef, .var "wad"])
    (argVals := [.int (Int.ofNat c.toNat), .int (Int.ofNat wad.toNat)])
    (callee := mulFunction) (locals := uintBinaryLocals c wad)
    (calleeSolm := { contract := contract, locals := uintBinaryLocalsZ c wad (c * wad) })
    (value := some [.int (Int.ofNat (c * wad).toNat)])
    hargs rfl rfl (execMulFunctionReturn evm2 rfl hfit)
  have hres : resumeAfterInternalCall { contract := contract, locals := L } "rad"
      (some [.int (Int.ofNat (c * wad).toNat)])
      = { contract := contract, locals := L.insert "rad" (.int (Int.ofNat (c * wad).toNat)) } := rfl
  rwa [hres] at hmul

set_option maxHeartbeats 1000000 in
/-- The `_mul(chi, wad)` internal call reverts on overflow. -/
theorem joinMulStmtRevert {evm2 : EVM.State} {I : ExecutionEnv} {c wad : UInt256} {L : Store}
    (hco : evm2.executionEnv.codeOwner = I.codeOwner)
    (hc : Solm.EVM.storageLoad evm2 I.codeOwner ⟨4⟩ = c)
    (hwadget : L.get? "wad" = some (.int (Int.ofNat wad.toNat)))
    (hbaseChi : L.get? "chi" = none) (hover : UInt256.size ≤ c.toNat * wad.toNat) :
    ExecStmt config { contract := contract, locals := L } evm2
      (.internalCall "_mul" [.storage chiRef, .var "wad"] "rad") .reverted := by
  have hargs : evalExprs? config { contract := contract, locals := L } evm2
      [.storage chiRef, .var "wad"] = .ok [.int (Int.ofNat c.toNat), .int (Int.ofNat wad.toNat)] := by
    have hchi := joinReadChi (I := I) hco hbaseChi
    rw [hc] at hchi
    simp only [evalExprs?, evalExpr?, hchi, EvalResult.bind, bind, pure, EvalResult.ofOption, hwadget]
  exact internalCallFunctionRevert (cfg := config)
    (caller := { contract := contract, locals := L }) (evm := evm2)
    (name := "_mul") (retVar := "rad") (args := [.storage chiRef, .var "wad"])
    (argVals := [.int (Int.ofNat c.toNat), .int (Int.ofNat wad.toNat)])
    (callee := mulFunction) (locals := uintBinaryLocals c wad)
    hargs rfl rfl (execMulFunctionRevert evm2 hover)

/-- The Solm frame after the whole `join` body: `rad` and `_moveRet` bound. -/
abbrev joinPostFrame (L : Store) (r : UInt256) : Frame :=
  { contract := contract,
    locals := (L.insert "rad" (.int (Int.ofNat r.toNat))).insert "_moveRet" .unit }

set_option maxHeartbeats 1000000 in
/-- Statements 8–10 on the success path (`z = true`): `_mul`, `extcodesize` guard, `vat.move`. -/
theorem joinTailSuccess {evm2 evm' : EVM.State} {I : ExecutionEnv} {c wad : UInt256}
    {L : Store} {o : ByteArray} {vtgt : AccountAddress}
    (hco : evm2.executionEnv.codeOwner = I.codeOwner)
    (hsrc : evm2.executionEnv.source = I.source)
    (hc : Solm.EVM.storageLoad evm2 I.codeOwner ⟨4⟩ = c)
    (hwadget : L.get? "wad" = some (.int (Int.ofNat wad.toNat)))
    (hbaseChi : L.get? "chi" = none) (hbaseVat : L.get? "vat" = none)
    (hfit : c.toNat * wad.toNat < UInt256.size)
    (hvtgt : AccountAddress.ofNat
      (UInt256.land (Solm.EVM.storageLoad evm2 I.codeOwner ⟨5⟩) solcAddrMask).toNat = vtgt)
    (hextcode : 0 < (UInt256.ofNat ((evm2.lookupAccount vtgt).option 0
      (fun acc => acc.code.size))).toNat)
    (hcall : typedCallViaEVM config evm2 (EVM.address vtgt) "move" 0
      [.address I.source, .address I.codeOwner, .int (Int.ofNat (c * wad).toNat)]
      (true, evm', o) true) :
    ExecBlock config { contract := contract, locals := L } evm2
      [ .internalCall "_mul" [.storage chiRef, .var "wad"] "rad",
        .require (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)),
        .externalCall (.storage vatRef) "move" (.intLit 0) [sender, .env .this, .var "rad"]
          "_moveRet" ]
      (.ok (joinPostFrame L (c * wad)) evm') := by
  refine ExecBlock.consNormal (joinMulStmt hco hc hwadget hbaseChi hfit) ?_
  have hvat : evalExpr? config
      { contract := contract, locals := L.insert "rad" (.int (Int.ofNat (c * wad).toNat)) }
      evm2 (.storage vatRef) = .ok (.address vtgt) := by
    rw [← hvtgt]; exact joinReadVat (I := I) hco (by rw [store_get_ne _ _ (by decide)]; exact hbaseVat)
  have hcallArgs : evalExprs? config
      { contract := contract, locals := L.insert "rad" (.int (Int.ofNat (c * wad).toNat)) }
      evm2 [sender, .env .this, .var "rad"]
      = .ok [.address I.source, .address I.codeOwner, .int (Int.ofNat (c * wad).toNat)] := by
    simp only [sender, evalExprs?, evalExpr?, envValue, EvalResult.bind, bind, pure,
      EvalResult.ofOption, store_get_self, hco, hsrc]
  refine ExecBlock.consNormal (ExecStmt.requireTrue
    (evalExpr_joinExtCodeGuard_true hvat hextcode)) ?_
  exact ExecBlock.consNormal (ExecStmt.externalCallSuccess (sendVal := 0) (out := o) hvat
    (by simp only [evalExpr?]; rfl) hcallArgs hcall (by rfl)) ExecBlock.nil

set_option maxHeartbeats 1000000 in
/-- Statements 8–10 on the failed-sub-call path (`z = false`): the `vat.move` CALL reverts. -/
theorem joinTailFail {evm2 evm' : EVM.State} {I : ExecutionEnv} {c wad : UInt256}
    {L : Store} {o : ByteArray} {vtgt : AccountAddress}
    (hco : evm2.executionEnv.codeOwner = I.codeOwner)
    (hsrc : evm2.executionEnv.source = I.source)
    (hc : Solm.EVM.storageLoad evm2 I.codeOwner ⟨4⟩ = c)
    (hwadget : L.get? "wad" = some (.int (Int.ofNat wad.toNat)))
    (hbaseChi : L.get? "chi" = none) (hbaseVat : L.get? "vat" = none)
    (hfit : c.toNat * wad.toNat < UInt256.size)
    (hvtgt : AccountAddress.ofNat
      (UInt256.land (Solm.EVM.storageLoad evm2 I.codeOwner ⟨5⟩) solcAddrMask).toNat = vtgt)
    (hextcode : 0 < (UInt256.ofNat ((evm2.lookupAccount vtgt).option 0
      (fun acc => acc.code.size))).toNat)
    (hcall : typedCallViaEVM config evm2 (EVM.address vtgt) "move" 0
      [.address I.source, .address I.codeOwner, .int (Int.ofNat (c * wad).toNat)]
      (false, evm', o) true) :
    ExecBlock config { contract := contract, locals := L } evm2
      [ .internalCall "_mul" [.storage chiRef, .var "wad"] "rad",
        .require (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)),
        .externalCall (.storage vatRef) "move" (.intLit 0) [sender, .env .this, .var "rad"]
          "_moveRet" ]
      .reverted := by
  refine ExecBlock.consNormal (joinMulStmt hco hc hwadget hbaseChi hfit) ?_
  have hvat : evalExpr? config
      { contract := contract, locals := L.insert "rad" (.int (Int.ofNat (c * wad).toNat)) }
      evm2 (.storage vatRef) = .ok (.address vtgt) := by
    rw [← hvtgt]; exact joinReadVat (I := I) hco (by rw [store_get_ne _ _ (by decide)]; exact hbaseVat)
  have hcallArgs : evalExprs? config
      { contract := contract, locals := L.insert "rad" (.int (Int.ofNat (c * wad).toNat)) }
      evm2 [sender, .env .this, .var "rad"]
      = .ok [.address I.source, .address I.codeOwner, .int (Int.ofNat (c * wad).toNat)] := by
    simp only [sender, evalExprs?, evalExpr?, envValue, EvalResult.bind, bind, pure,
      EvalResult.ofOption, store_get_self, hco, hsrc]
  refine ExecBlock.consNormal (ExecStmt.requireTrue
    (evalExpr_joinExtCodeGuard_true hvat hextcode)) ?_
  exact ExecBlock.consRevert (ExecStmt.externalCallFailure (sendVal := 0) (out := o) hvat
    (by simp only [evalExpr?]; rfl) hcallArgs hcall)

set_option maxHeartbeats 1000000 in
/-- Statements 8–9 when `extcodesize(vat) = 0`: `_mul`, then the `extcodesize` guard reverts. -/
theorem joinTailEcs {evm2 : EVM.State} {I : ExecutionEnv} {c wad : UInt256}
    {L : Store} {vtgt : AccountAddress}
    (hco : evm2.executionEnv.codeOwner = I.codeOwner)
    (hc : Solm.EVM.storageLoad evm2 I.codeOwner ⟨4⟩ = c)
    (hwadget : L.get? "wad" = some (.int (Int.ofNat wad.toNat)))
    (hbaseChi : L.get? "chi" = none) (hbaseVat : L.get? "vat" = none)
    (hfit : c.toNat * wad.toNat < UInt256.size)
    (hvtgt : AccountAddress.ofNat
      (UInt256.land (Solm.EVM.storageLoad evm2 I.codeOwner ⟨5⟩) solcAddrMask).toNat = vtgt)
    (hextcode : (UInt256.ofNat ((evm2.lookupAccount vtgt).option 0
      (fun acc => acc.code.size))).toNat = 0) :
    ExecBlock config { contract := contract, locals := L } evm2
      [ .internalCall "_mul" [.storage chiRef, .var "wad"] "rad",
        .require (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)),
        .externalCall (.storage vatRef) "move" (.intLit 0) [sender, .env .this, .var "rad"]
          "_moveRet" ]
      .reverted := by
  refine ExecBlock.consNormal (joinMulStmt hco hc hwadget hbaseChi hfit) ?_
  have hvat : evalExpr? config
      { contract := contract, locals := L.insert "rad" (.int (Int.ofNat (c * wad).toNat)) }
      evm2 (.storage vatRef) = .ok (.address vtgt) := by
    rw [← hvtgt]; exact joinReadVat (I := I) hco (by rw [store_get_ne _ _ (by decide)]; exact hbaseVat)
  exact ExecBlock.consRevert (ExecStmt.requireFalse (evalExpr_joinExtCodeGuard_false hvat hextcode))

/-! ### `join(uint256)` — the `vat.move` external-call bridge -/

set_option maxHeartbeats 1600000 in
/-- Transport the bytecode `Θ`-link of the `vat.move` `CALL` to a Solm-side `typedCallViaEVM`
    over the equivalent post-store state, threading `accountMapEquiv` on the outcome. -/
theorem potJoinCallBridge {cA gh bl σ₀ A I} {g : Sat256}
    {σ'' : AccountMap} {evm2_solm : EVM.State} {mem : ByteArray}
    {cA' : Batteries.RBSet AccountAddress compare} {σ_final : AccountMap} {z : Bool}
    {o : ByteArray} {A_in A' : Substate} {callGas g'' : UInt256}
    (hmem : mem.size = 96)
    (hEnv : evm2_solm.executionEnv = I) (hσ0 : evm2_solm.σ₀ = σ₀)
    (hCreated : evm2_solm.createdAccounts = cA) (hGenesis : evm2_solm.genesisBlockHeader = gh)
    (hBlocks : evm2_solm.blocks = bl) (hSubstate : evm2_solm.substate = A)
    (hAccountsPre : accountMapEquiv σ'' evm2_solm.accountMap)
    (hdepth : I.depth ≠ 1024)
    (hΘ : (cA', σ_final, g'', A', z, o) =
        Ethereum.EVM.Θ I.blobVersionedHashes cA gh bl σ'' σ₀ A_in
          (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner)) I.sender
          (AccountAddress.ofUInt256 (joinVatMasked σ'' I))
          (toExecute σ'' (AccountAddress.ofUInt256 (joinVatMasked σ'' I)))
          callGas (UInt256.ofNat I.gasPrice) ⟨0⟩ ⟨0⟩
          ((potMoveCalldataMem (joinCallerWord I) (joinThisWord I)
            (UInt256.mul (joinChi σ'' I) (joinWadWord I)) mem).readWithPadding 128 100)
          (I.depth + 1) I.header I.perm) :
    ∃ (σ'_solm : AccountMap) (A'_solm : Substate),
      typedCallViaEVM config evm2_solm
        (EVM.address (AccountAddress.ofNat
          (UInt256.land (Solm.EVM.storageLoad evm2_solm I.codeOwner ⟨5⟩) solcAddrMask).toNat))
        "move" 0
        [.address I.source, .address I.codeOwner,
          .int (Int.ofNat (UInt256.mul (Solm.EVM.storageLoad evm2_solm I.codeOwner ⟨4⟩)
            (joinWadWord I)).toNat)]
        (z, { evm2_solm with accountMap := σ'_solm, substate := A'_solm, createdAccounts := cA' }, o)
        I.perm ∧ accountMapEquiv σ_final σ'_solm := by
  have hChi : joinChi σ'' I = Solm.EVM.storageLoad evm2_solm I.codeOwner ⟨4⟩ := by
    rw [joinStorageLoad_eq]; exact accountMapEquiv_storage_findD hAccountsPre I.codeOwner ⟨4⟩ ⟨0⟩
  have hVat : joinVatRaw σ'' I = Solm.EVM.storageLoad evm2_solm I.codeOwner ⟨5⟩ := by
    rw [joinStorageLoad_eq]; exact accountMapEquiv_storage_findD hAccountsPre I.codeOwner ⟨5⟩ ⟨0⟩
  refine typedCallViaEVM_callMade_accountMapEquiv
    (cfg := config) (evm_evm := initState cA gh bl σ'' σ₀ g A I) (evm_solm := evm2_solm)
    (tgt := EVM.address (AccountAddress.ofNat
      (UInt256.land (Solm.EVM.storageLoad evm2_solm I.codeOwner ⟨5⟩) solcAddrMask).toNat))
    (targetWord := joinVatMasked σ'' I) (name := "move")
    (args := [.address I.source, .address I.codeOwner,
      .int (Int.ofNat (UInt256.mul (Solm.EVM.storageLoad evm2_solm I.codeOwner ⟨4⟩)
        (joinWadWord I)).toNat)])
    (mem := potMoveCalldataMem (joinCallerWord I) (joinThisWord I)
      (UInt256.mul (joinChi σ'' I) (joinWadWord I)) mem)
    (inOff := ⟨128⟩) (inSize := ⟨100⟩) (callPerm := I.perm) (callGas := callGas)
    (hdepth := hdepth)
    (htgt := by rw [← hVat]; exact joinVatTarget_eq σ'' I (joinVatRaw σ'' I) rfl)
    (hcd := by
      rw [← hChi]
      exact potMoveEncode_eq I.source I.codeOwner (joinCallerWord I) (joinThisWord I)
        (UInt256.mul (joinChi σ'' I) (joinWadWord I)) hmem rfl rfl)
    (hΘ := by simpa using hΘ)
    (hAccounts := by simpa using hAccountsPre)
    (hOriginalAccounts := hσ0.symm) (hCreated := hCreated) (hGenesis := hGenesis)
    (hBlocks := hBlocks) (hSubstate := hSubstate) (hEnv := hEnv)

/-! ### `join(uint256)` — `extcodesize(vat)` agreement -/

/-- `AccountAddress.ofUInt256` and `ofNat ∘ toNat` coincide. -/
theorem addrOfUInt256_eq_ofNat (w : UInt256) :
    AccountAddress.ofUInt256 w = AccountAddress.ofNat w.toNat := by
  unfold AccountAddress.ofUInt256 AccountAddress.ofNat
  apply Fin.ext
  simp only [Fin.ofNat]
  have hv : (↑w.val : ℕ) = w.toNat := rfl
  rw [hv, Nat.mod_mod_of_dvd _ (dvd_refl _)]

/-- The EVM `extcodesize(vat)` word equals the Solm-side code-size read (given read agreement). -/
theorem joinExtCodeAgree (σ'' : AccountMap) (evm2 : EVM.State) (I : ExecutionEnv)
    (hAcc : accountMapEquiv σ'' evm2.accountMap)
    (hvat : joinVatRaw σ'' I = Solm.EVM.storageLoad evm2 I.codeOwner ⟨5⟩) :
    extCodeSizeWord σ'' (joinVatMasked σ'' I)
      = UInt256.ofNat ((evm2.lookupAccount (AccountAddress.ofNat
          (UInt256.land (Solm.EVM.storageLoad evm2 I.codeOwner ⟨5⟩) solcAddrMask).toNat)).option 0
          (fun acc => acc.code.size)) := by
  rw [extCodeSizeWord_accountMapEquiv hAcc]
  have htgt : AccountAddress.ofUInt256 (joinVatMasked σ'' I)
      = AccountAddress.ofNat
        (UInt256.land (Solm.EVM.storageLoad evm2 I.codeOwner ⟨5⟩) solcAddrMask).toNat := by
    rw [joinVatMasked, hvat, addrOfUInt256_eq_ofNat]
  rw [extCodeSizeWord, htgt]
  simp only [State.lookupAccount]
  cases evm2.accountMap.find? (AccountAddress.ofNat
    (UInt256.land (Solm.EVM.storageLoad evm2 I.codeOwner ⟨5⟩) solcAddrMask).toNat) <;> rfl

/-- `extcodesize(vat) ≠ 0` ⇒ the Solm code-size read is positive. -/
theorem joinExtCodeNe (σ'' : AccountMap) (evm2 : EVM.State) (I : ExecutionEnv)
    (hAcc : accountMapEquiv σ'' evm2.accountMap)
    (hvat : joinVatRaw σ'' I = Solm.EVM.storageLoad evm2 I.codeOwner ⟨5⟩)
    (hne : extCodeSizeWord σ'' (joinVatMasked σ'' I) ≠ ⟨0⟩) :
    0 < (UInt256.ofNat ((evm2.lookupAccount (AccountAddress.ofNat
          (UInt256.land (Solm.EVM.storageLoad evm2 I.codeOwner ⟨5⟩) solcAddrMask).toNat)).option 0
          (fun acc => acc.code.size))).toNat := by
  rw [← joinExtCodeAgree σ'' evm2 I hAcc hvat]
  rcases Nat.eq_zero_or_pos (extCodeSizeWord σ'' (joinVatMasked σ'' I)).toNat with h | h
  · exact absurd (u256_inj (by rw [h]; rfl)) hne
  · exact h

/-- `extcodesize(vat) = 0` ⇒ the Solm code-size read is zero. -/
theorem joinExtCodeEq (σ'' : AccountMap) (evm2 : EVM.State) (I : ExecutionEnv)
    (hAcc : accountMapEquiv σ'' evm2.accountMap)
    (hvat : joinVatRaw σ'' I = Solm.EVM.storageLoad evm2 I.codeOwner ⟨5⟩)
    (heq : extCodeSizeWord σ'' (joinVatMasked σ'' I) = ⟨0⟩) :
    (UInt256.ofNat ((evm2.lookupAccount (AccountAddress.ofNat
          (UInt256.land (Solm.EVM.storageLoad evm2 I.codeOwner ⟨5⟩) solcAddrMask).toNat)).option 0
          (fun acc => acc.code.size))).toNat = 0 := by
  rw [← joinExtCodeAgree σ'' evm2 I hAcc hvat, heq]; rfl

/-! ### `join(uint256)` — early-revert Solm bodies -/

set_option maxHeartbeats 1000000 in
/-- `now ≠ rho`: the body reverts at the `rho` `require`. -/
theorem potJoinSolmRevertRho {cA gh bl σ_solm σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩)
    (hrhoNe : joinNowWord I
      ≠ Solm.EVM.storageLoad (initState cA gh bl σ_solm σ₀ g A I) I.codeOwner ⟨7⟩) :
    ExecTransitionBody config contract (initState cA gh bl σ_solm σ₀ g A I)
      ((∅ : Store).insert "wad" (.int (Int.ofNat (joinWadWord I).toNat)))
      joinTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consRevert (ExecStmt.requireFalse
    (evalExpr_eq_int_false (a := Int.ofNat (joinNowWord I).toNat)
      (b := Int.ofNat (Solm.EVM.storageLoad (initState cA gh bl σ_solm σ₀ g A I)
        I.codeOwner ⟨7⟩).toNat)
      (by simp only [evalExpr?, envValue, joinNowWord, pure]; rfl)
      (evalExpr_joinRhoOf (by simp)) ?_))
  intro heq
  exact hrhoNe (u256_inj (Int.ofNat.inj heq))

set_option maxHeartbeats 1000000 in
/-- `pie[caller] + wad` overflows: the body reverts at the `pieNew` `letDecl`. -/
theorem potJoinSolmRevertPie {cA gh bl σ_solm σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩)
    (hrho : joinNowWord I = Solm.EVM.storageLoad (initState cA gh bl σ_solm σ₀ g A I) I.codeOwner ⟨7⟩)
    (hover : UInt256.size ≤ (Solm.EVM.storageLoad (initState cA gh bl σ_solm σ₀ g A I) I.codeOwner
      (pieSlot (.address I.source))).toNat + (joinWadWord I).toNat) :
    ExecTransitionBody config contract (initState cA gh bl σ_solm σ₀ g A I)
      ((∅ : Store).insert "wad" (.int (Int.ofNat (joinWadWord I).toNat)))
      joinTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue
    (evalExpr_eq_int_true (a := Int.ofNat (joinNowWord I).toNat)
      (b := Int.ofNat (Solm.EVM.storageLoad (initState cA gh bl σ_solm σ₀ g A I)
        I.codeOwner ⟨7⟩).toNat)
      (by simp only [evalExpr?, envValue, joinNowWord, pure]; rfl)
      (evalExpr_joinRhoOf (by simp)) (by rw [hrho]))) ?_
  exact ExecBlock.consRevert (ExecStmt.letDeclRevert
    (evalExpr_add256_revert
      (a := Solm.EVM.storageLoad (initState cA gh bl σ_solm σ₀ g A I) I.codeOwner
        (pieSlot (.address I.source)))
      (b := joinWadWord I)
      (evalExpr_joinPieMapOf (by simp)) (evalExpr_varUInt256 (by simp)) hover))

set_option maxHeartbeats 1000000 in
/-- `Pie + wad` overflows: the body reverts at the `PieNew` `letDecl` (after `pie` is stored). -/
theorem potJoinSolmRevertPie2 {cA gh bl σ_solm σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩)
    (hrho : joinNowWord I = Solm.EVM.storageLoad (initState cA gh bl σ_solm σ₀ g A I) I.codeOwner ⟨7⟩)
    (hpieFit : (Solm.EVM.storageLoad (initState cA gh bl σ_solm σ₀ g A I) I.codeOwner
        (pieSlot (.address I.source))).toNat + (joinWadWord I).toNat < UInt256.size)
    (hover : UInt256.size ≤ (Solm.EVM.storageLoad
        (Solm.EVM.storageStore (initState cA gh bl σ_solm σ₀ g A I) I.codeOwner
          (pieSlot (.address I.source))
          ((Solm.EVM.storageLoad (initState cA gh bl σ_solm σ₀ g A I) I.codeOwner
            (pieSlot (.address I.source))) + joinWadWord I)) I.codeOwner ⟨2⟩).toNat
        + (joinWadWord I).toNat) :
    ExecTransitionBody config contract (initState cA gh bl σ_solm σ₀ g A I)
      ((∅ : Store).insert "wad" (.int (Int.ofNat (joinWadWord I).toNat)))
      joinTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  refine potJoinSolmDriverPie hwv hrho hpieFit ?_
  have he1co : (Solm.EVM.storageStore (initState cA gh bl σ_solm σ₀ g A I) I.codeOwner
      (pieSlot (.address I.source))
      ((Solm.EVM.storageLoad (initState cA gh bl σ_solm σ₀ g A I) I.codeOwner
        (pieSlot (.address I.source))) + joinWadWord I)).executionEnv.codeOwner = I.codeOwner := by
    rw [storageStore_executionEnv]; rfl
  exact ExecBlock.consRevert (ExecStmt.letDeclRevert
    (evalExpr_add256_revert
      (a := Solm.EVM.storageLoad (Solm.EVM.storageStore (initState cA gh bl σ_solm σ₀ g A I)
        I.codeOwner (pieSlot (.address I.source))
        ((Solm.EVM.storageLoad (initState cA gh bl σ_solm σ₀ g A I) I.codeOwner
          (pieSlot (.address I.source))) + joinWadWord I)) I.codeOwner ⟨2⟩)
      (b := joinWadWord I)
      (joinReadPieScalar he1co (by simp))
      (evalExpr_varUInt256 (by rw [store_get_ne _ _ (by decide), store_get_self])) hover))

/-! ### `join(uint256)` — post-store state abbreviations + `evm2` read bridges -/

/-- EVM post-`pie`-store account map. -/
noncomputable abbrev joinSigma' (σ_evm : AccountMap) (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap I.codeOwner σ_evm (joinPieSlot I) (joinPie0 σ_evm I + joinWadWord I)

/-- EVM post-`Pie`-store account map. -/
noncomputable abbrev joinSigma'' (σ_evm : AccountMap) (I : ExecutionEnv) : AccountMap :=
  sstoreAccountMap I.codeOwner (joinSigma' σ_evm I) ⟨2⟩
    (solcSlotWord (joinSigma' σ_evm I) I ⟨2⟩ + joinWadWord I)

/-- Solm post-`pie`-store state. -/
noncomputable abbrev joinSolmEvm1 (cA : Batteries.RBSet AccountAddress compare)
    (gh : BlockHeader) (bl : ProcessedBlocks) (σ_solm σ₀ : AccountMap) (g : Sat256) (A : Substate)
    (I : ExecutionEnv) : EVM.State :=
  Solm.EVM.storageStore (initState cA gh bl σ_solm σ₀ g A I) I.codeOwner (pieSlot (.address I.source))
    (Solm.EVM.storageLoad (initState cA gh bl σ_solm σ₀ g A I) I.codeOwner
      (pieSlot (.address I.source)) + joinWadWord I)

/-- Solm post-`Pie`-store state. -/
noncomputable abbrev joinSolmEvm2 (cA : Batteries.RBSet AccountAddress compare)
    (gh : BlockHeader) (bl : ProcessedBlocks) (σ_solm σ₀ : AccountMap) (g : Sat256) (A : Substate)
    (I : ExecutionEnv) : EVM.State :=
  Solm.EVM.storageStore (joinSolmEvm1 cA gh bl σ_solm σ₀ g A I) I.codeOwner ⟨2⟩
    (Solm.EVM.storageLoad (joinSolmEvm1 cA gh bl σ_solm σ₀ g A I) I.codeOwner ⟨2⟩ + joinWadWord I)

theorem joinSolmEvm2_codeOwner {cA gh bl σ_solm σ₀ A I} {g : Sat256} :
    (joinSolmEvm2 cA gh bl σ_solm σ₀ g A I).executionEnv.codeOwner = I.codeOwner := by
  rw [joinSolmEvm2, storageStore_executionEnv, joinSolmEvm1, storageStore_executionEnv]; rfl

theorem joinSolmEvm2_source {cA gh bl σ_solm σ₀ A I} {g : Sat256} :
    (joinSolmEvm2 cA gh bl σ_solm σ₀ g A I).executionEnv.source = I.source := by
  rw [joinSolmEvm2, storageStore_executionEnv, joinSolmEvm1, storageStore_executionEnv]; rfl

theorem joinSolmEvm2_env {cA gh bl σ_solm σ₀ A I} {g : Sat256} :
    (joinSolmEvm2 cA gh bl σ_solm σ₀ g A I).executionEnv = I := by
  rw [joinSolmEvm2, storageStore_executionEnv, joinSolmEvm1, storageStore_executionEnv]; rfl

theorem joinSolmEvm2_σ₀ {cA gh bl σ_solm σ₀ A I} {g : Sat256} :
    (joinSolmEvm2 cA gh bl σ_solm σ₀ g A I).σ₀ = σ₀ := by
  rw [joinSolmEvm2, storageStore_σ₀, joinSolmEvm1, storageStore_σ₀]; rfl

theorem joinSolmEvm2_created {cA gh bl σ_solm σ₀ A I} {g : Sat256} :
    (joinSolmEvm2 cA gh bl σ_solm σ₀ g A I).createdAccounts = cA := by
  rw [joinSolmEvm2, storageStore_createdAccounts, joinSolmEvm1, storageStore_createdAccounts]; rfl

theorem joinSolmEvm2_genesis {cA gh bl σ_solm σ₀ A I} {g : Sat256} :
    (joinSolmEvm2 cA gh bl σ_solm σ₀ g A I).genesisBlockHeader = gh := by
  rw [joinSolmEvm2, storageStore_genesis, joinSolmEvm1, storageStore_genesis]; rfl

theorem joinSolmEvm2_blocks {cA gh bl σ_solm σ₀ A I} {g : Sat256} :
    (joinSolmEvm2 cA gh bl σ_solm σ₀ g A I).blocks = bl := by
  rw [joinSolmEvm2, storageStore_blocks, joinSolmEvm1, storageStore_blocks]; rfl

theorem joinSolmEvm2_substate {cA gh bl σ_solm σ₀ A I} {g : Sat256} :
    (joinSolmEvm2 cA gh bl σ_solm σ₀ g A I).substate = A := by
  rw [joinSolmEvm2, storageStore_substate, joinSolmEvm1, storageStore_substate]; rfl

/-- The pre-`CALL` account-map coincidence in abbreviation form. -/
theorem joinAccPre {cA gh bl σ_evm σ_solm σ₀ A I} {g : Sat256}
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    accountMapEquiv (joinSigma'' σ_evm I) (joinSolmEvm2 cA gh bl σ_solm σ₀ g A I).accountMap :=
  joinPreCallAccounts hAccounts

theorem joinChiReadB {cA gh bl σ_evm σ_solm σ₀ A I} {g : Sat256}
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    Solm.EVM.storageLoad (joinSolmEvm2 cA gh bl σ_solm σ₀ g A I) I.codeOwner ⟨4⟩
      = joinChi (joinSigma'' σ_evm I) I := by
  rw [joinStorageLoad_eq]
  exact (accountMapEquiv_storage_findD (joinAccPre hAccounts) I.codeOwner ⟨4⟩ ⟨0⟩).symm

theorem joinVatReadB {cA gh bl σ_evm σ_solm σ₀ A I} {g : Sat256}
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    joinVatRaw (joinSigma'' σ_evm I) I
      = Solm.EVM.storageLoad (joinSolmEvm2 cA gh bl σ_solm σ₀ g A I) I.codeOwner ⟨5⟩ := by
  rw [joinStorageLoad_eq]
  exact accountMapEquiv_storage_findD (joinAccPre hAccounts) I.codeOwner ⟨5⟩ ⟨0⟩

/-! ## `join(uint256)` -/

set_option maxHeartbeats 4000000 in
/-- `join(uint256)` external: `pie[snd] += wad; Pie += wad; vat.move(snd, this, chi*wad)`. -/
theorem potJoinBody {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = potBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (potSelBytes 9))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (potSelBytes 9) rfl hsel
  have hdispatch : dispatchMsg contract I.calldata = some joinTransition := potDispatchJoin hsel
  have hreach := potReachJoinBody (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
    (A := A) (I := I) (g := Sat256.ofUInt256 g) hcode hwv hsz4 hsize hsel
  -- Solm-side rho / pie reads bridged to the EVM words.
  have hrhoB : Solm.EVM.storageLoad (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
      I.codeOwner ⟨7⟩ = joinRhoWord σ_evm I := by
    rw [joinStorageLoad_eq]
    exact (accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨7⟩ ⟨0⟩).symm
  have hpieB : Solm.EVM.storageLoad (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
      I.codeOwner (pieSlot (.address I.source)) = joinPie0 σ_evm I := by
    rw [joinStorageLoad_eq, joinPieSlot_eq]
    exact (accountMapEquiv_storage_findD hAccounts I.codeOwner (joinPieSlot I) ⟨0⟩).symm
  by_cases hsz36 : 36 ≤ I.calldata.size
  · obtain ⟨_, _, rd681⟩ := potJoinX_decoded hsz36 hsize hreach
    by_cases hrho : joinNowWord I = joinRhoWord σ_evm I
    · obtain ⟨_, _, rd757⟩ := potJoinX_rhoOk hrho rd681
      by_cases hpieOvf : UInt256.size ≤ (joinPie0 σ_evm I).toNat + (joinWadWord I).toNat
      · exact (potJoinX_pieOverflowReverts hpieOvf rd757).reEquivExecutionRevert hcode hdispatch
          (potDecode_join_ok hsz36)
          (potJoinSolmRevertPie hwv (hrho.trans hrhoB.symm) (by rw [hpieB]; exact hpieOvf))
      · obtain ⟨_, _, rd800⟩ := potJoinX_pieStore _hperm hpieOvf rd757
        have hPie1B : Solm.EVM.storageLoad (Solm.EVM.storageStore
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I.codeOwner
            (pieSlot (.address I.source))
            ((Solm.EVM.storageLoad (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I.codeOwner
              (pieSlot (.address I.source))) + joinWadWord I)) I.codeOwner ⟨2⟩
            = solcSlotWord (sstoreAccountMap I.codeOwner σ_evm (joinPieSlot I)
              (joinPie0 σ_evm I + joinWadWord I)) I ⟨2⟩ := by
          rw [joinStorageLoad_eq, storageStore_accountMap, hpieB, joinPieSlot_eq]
          exact (accountMapEquiv_storage_findD (accountMapEquiv_sstoreAccountMap I.codeOwner
            (joinPieSlot I) (joinPie0 σ_evm I + joinWadWord I) hAccounts) I.codeOwner ⟨2⟩ ⟨0⟩).symm
        by_cases hPieOvf : UInt256.size ≤ (solcSlotWord (sstoreAccountMap I.codeOwner σ_evm
            (joinPieSlot I) (joinPie0 σ_evm I + joinWadWord I)) I ⟨2⟩).toNat + (joinWadWord I).toNat
        · exact (potJoinX_PieOverflowReverts hPieOvf rd800).reEquivExecutionRevert hcode hdispatch
            (potDecode_join_ok hsz36)
            (potJoinSolmRevertPie2 hwv (hrho.trans hrhoB.symm) (by rw [hpieB]; exact not_le.mp hpieOvf)
              (by rw [hPie1B]; exact hPieOvf))
        · obtain ⟨_, _, rd816⟩ := potJoinX_PieStore _hperm hPieOvf rd800
          by_cases hMulOvf : UInt256.size ≤ (joinChi (sstoreAccountMap I.codeOwner
              (sstoreAccountMap I.codeOwner σ_evm (joinPieSlot I) (joinPie0 σ_evm I + joinWadWord I))
              ⟨2⟩ (solcSlotWord (sstoreAccountMap I.codeOwner σ_evm (joinPieSlot I)
                (joinPie0 σ_evm I + joinWadWord I)) I ⟨2⟩ + joinWadWord I)) I).toNat
              * (joinWadWord I).toNat
          · exact (potJoinX_mulOverflowReverts hMulOvf rd816).reEquivExecutionRevert hcode hdispatch
              (potDecode_join_ok hsz36)
              (ExecFuncBody.execBlockRevert (potJoinSolmDriverPie hwv (hrho.trans hrhoB.symm)
                (by rw [hpieB]; exact not_le.mp hpieOvf)
                (potJoinSolmMulSeg (by rw [hPie1B]; exact not_le.mp hPieOvf)
                  (ExecBlock.consRevert (joinMulStmtRevert joinSolmEvm2_codeOwner
                    (joinChiReadB hAccounts)
                    (by rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
                      store_get_self])
                    (by simp) hMulOvf)))))
          · obtain ⟨_, _, rd853⟩ := potJoinX_mulReady (not_le.mp hMulOvf) rd816
            have hmemSz : (joinPieStoreHashMem I).size = 96 :=
              twoWordHashMem_size_96 (joinCallerWord I) ⟨1⟩ (joinPieHashMem_size I)
            have hmemR64 : (joinPieStoreHashMem I).readWithPadding 64 32
                = UInt256.toByteArray ⟨128⟩ :=
              twoWordHashMem_read64 (joinCallerWord I) ⟨1⟩ (joinPieHashMem_size I)
                (joinPieHashMem_read64 I)
            obtain ⟨_, _, rd927⟩ := potJoinX_callGuard hmemSz hmemR64 rd853
            by_cases hEcs : extCodeSizeWord (joinSigma'' σ_evm I)
                (joinVatMasked (joinSigma'' σ_evm I) I) = ⟨0⟩
            · -- extcodesize(vat) = 0 ⇒ both revert at the `extcodesize` guard
              refine (potJoinX_ecsZero hEcs rd927).reEquivExecutionRevert hcode hdispatch
                (potDecode_join_ok hsz36)
                (ExecFuncBody.execBlockRevert (potJoinSolmDriverPie hwv (hrho.trans hrhoB.symm)
                  (by rw [hpieB]; exact not_le.mp hpieOvf)
                  (potJoinSolmMulSeg (by rw [hPie1B]; exact not_le.mp hPieOvf)
                    (joinTailEcs joinSolmEvm2_codeOwner rfl
                      (by rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
                        store_get_self])
                      (by simp) (by simp)
                      (by rw [joinChiReadB hAccounts]; exact not_le.mp hMulOvf) rfl
                      (joinExtCodeEq (joinSigma'' σ_evm I) (joinSolmEvm2 cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I (joinAccPre hAccounts)
                        (joinVatReadB hAccounts) hEcs)))))
            · by_cases hdepth : I.depth = 1024
              · -- call-depth limit ⇒ both revert (call never made)
                refine (potJoinX_depthLimitReverts hdepth hEcs rd927).reEquivExecutionRevert hcode
                  hdispatch (potDecode_join_ok hsz36)
                  (ExecFuncBody.execBlockRevert (potJoinSolmDriverPie hwv (hrho.trans hrhoB.symm)
                    (by rw [hpieB]; exact not_le.mp hpieOvf)
                    (potJoinSolmMulSeg (by rw [hPie1B]; exact not_le.mp hPieOvf)
                      (joinTailFail joinSolmEvm2_codeOwner joinSolmEvm2_source rfl
                        (by rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
                          store_get_self])
                        (by simp) (by simp)
                        (by rw [joinChiReadB hAccounts]; exact not_le.mp hMulOvf) rfl
                        (joinExtCodeNe (joinSigma'' σ_evm I) (joinSolmEvm2 cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I (joinAccPre hAccounts)
                          (joinVatReadB hAccounts) hEcs)
                        (callNotMade_depthLimit
                          (potMoveEncode_eq I.source I.codeOwner (joinCallerWord I) (joinThisWord I)
                            (UInt256.mul (Solm.EVM.storageLoad
                              (joinSolmEvm2 cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I.codeOwner
                              ⟨4⟩) (joinWadWord I)) hmemSz rfl rfl)
                          (by rw [joinSolmEvm2_env]; exact hdepth))))))
              · -- fire the `vat.move` CALL
                have hdepthLt : I.depth.val < 1024 :=
                  lt_of_le_of_ne (Nat.le_of_lt_succ I.depth.isLt) (fun h => hdepth (Fin.ext h))
                obtain ⟨cA', σ_final, z, o, A_in, callGas, mem', aw', k', C', ⟨g'', A', hΘ⟩,
                  rd943, hosz⟩ := potJoinX_postCall hmemSz hdepthLt hEcs rd927
                obtain ⟨σ'_solm, A'_solm, hcall, hAcc'⟩ :=
                  potJoinCallBridge (g := Sat256.ofUInt256 g) (σ'' := joinSigma'' σ_evm I)
                    (evm2_solm := joinSolmEvm2 cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
                    hmemSz joinSolmEvm2_env joinSolmEvm2_σ₀ joinSolmEvm2_created
                    joinSolmEvm2_genesis joinSolmEvm2_blocks joinSolmEvm2_substate
                    (joinAccPre hAccounts) hdepth hΘ
                cases z
                · -- CALL returned 0 ⇒ both revert
                  simp only [Bool.false_eq_true, if_false] at rd943
                  refine (potJoinX_failTailGen hosz rd943).reEquivExecutionRevert hcode hdispatch
                    (potDecode_join_ok hsz36)
                    (ExecFuncBody.execBlockRevert (potJoinSolmDriverPie hwv (hrho.trans hrhoB.symm)
                      (by rw [hpieB]; exact not_le.mp hpieOvf)
                      (potJoinSolmMulSeg (by rw [hPie1B]; exact not_le.mp hPieOvf)
                        (joinTailFail joinSolmEvm2_codeOwner joinSolmEvm2_source rfl
                          (by rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
                            store_get_self])
                          (by simp) (by simp)
                          (by rw [joinChiReadB hAccounts]; exact not_le.mp hMulOvf) rfl
                          (joinExtCodeNe (joinSigma'' σ_evm I) (joinSolmEvm2 cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I (joinAccPre hAccounts)
                            (joinVatReadB hAccounts) hEcs)
                          (_hperm ▸ hcall)))))
                · -- CALL succeeded ⇒ both return (void)
                  simp only [if_true] at rd943
                  refine (potJoinX_successTailGen rd943).reEquivExecutionGenAccountMapEquiv hcode
                    hdispatch (potDecode_join_ok hsz36)
                    (ExecFuncBody.execBlockOK (potJoinSolmDriverPie hwv (hrho.trans hrhoB.symm)
                      (by rw [hpieB]; exact not_le.mp hpieOvf)
                      (potJoinSolmMulSeg (by rw [hPie1B]; exact not_le.mp hPieOvf)
                        (joinTailSuccess joinSolmEvm2_codeOwner joinSolmEvm2_source rfl
                          (by rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
                            store_get_self])
                          (by simp) (by simp)
                          (by rw [joinChiReadB hAccounts]; exact not_le.mp hMulOvf) rfl
                          (joinExtCodeNe (joinSigma'' σ_evm I) (joinSolmEvm2 cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I (joinAccPre hAccounts)
                            (joinVatReadB hAccounts) hEcs)
                          (_hperm ▸ hcall)))))
                    rfl hAcc'
                    (returnEquiv.fallthrough (o := ByteArray.empty) (r := none) (t := [])
                      (dvs := []) rfl (by decide +native) (by decide +native))
    · exact (potJoinX_rhoReverts hrho rd681).reEquivExecutionRevert hcode hdispatch
        (potDecode_join_ok hsz36)
        (potJoinSolmRevertRho hwv (fun h => hrho (by rw [h, hrhoB])))
  · exact (potJoinX_shortReverts hsz4 hsize (by omega) hreach).reEquivDecodingFailed hcode hdispatch
      (potDecode_join_none_short hsz4 (by omega))

end Benchmarks.Dss.Pot
