import Benchmarks.Dss.Vow.Trusted
import Reasoning.ABI
import Reasoning.Dispatch
import Reasoning.Memory
import Reasoning.Refinement
import Reasoning.Reach
import Reasoning.Solc
import Reasoning.Storage
import Reasoning.SolmBody
import Mathlib.Tactic.IntervalCases

/-!
# MakerDAO/Sky DSS Vow shared proof foundation

This file contains contract-wide selector, dispatch-failure, and global revert facts used by the
top-level runtime proof and the per-function body proofs.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.Vow

/-- The 4-byte selector word computed by `CALLDATALOAD(0); SHR 224`. -/
abbrev vowSelWord (I : ExecutionEnv) : UInt256 :=
  UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩

/-- The 4-byte selector of `I`'s calldata equals `sel`. -/
abbrev selIs (I : ExecutionEnv) (sel : ByteArray) : Prop :=
  (sel == I.calldata.extract 0 4) = true

/-- Function selectors in `contract.transitions` order. -/
def vowSelBytes : ℕ → ByteArray
  | 0 => ⟨#[0x2a, 0x1d, 0x2b, 0x3c]⟩  -- Ash()
  | 1 => ⟨#[0xd0, 0xad, 0xc3, 0x5f]⟩  -- Sin()
  | 2 => ⟨#[0x68, 0x11, 0x0b, 0x2f]⟩  -- bump()
  | 3 => ⟨#[0x69, 0x24, 0x50, 0x09]⟩  -- cage()
  | 4 => ⟨#[0x9c, 0x52, 0xa7, 0xf1]⟩  -- deny(address)
  | 5 => ⟨#[0xe4, 0x33, 0x05, 0x45]⟩  -- dump()
  | 6 => ⟨#[0x69, 0x7e, 0xfb, 0x78]⟩  -- fess(uint256)
  | 7 => ⟨#[0x29, 0xae, 0x81, 0x14]⟩  -- file(bytes32,uint256)
  | 8 => ⟨#[0xd4, 0xe8, 0xbe, 0x83]⟩  -- file(bytes32,address)
  | 9 => ⟨#[0x0e, 0x01, 0x19, 0x8b]⟩  -- flap()
  | 10 => ⟨#[0x5c, 0xa0, 0xd7, 0x23]⟩ -- flapper()
  | 11 => ⟨#[0xd7, 0xee, 0x67, 0x4b]⟩ -- flog(uint256)
  | 12 => ⟨#[0xbb, 0xbb, 0x0d, 0x7b]⟩ -- flop()
  | 13 => ⟨#[0x40, 0x81, 0xd7, 0x3a]⟩ -- flopper()
  | 14 => ⟨#[0xf3, 0x7a, 0xc6, 0x1c]⟩ -- heal(uint256)
  | 15 => ⟨#[0x1b, 0x8e, 0x8c, 0xfa]⟩ -- hump()
  | 16 => ⟨#[0x25, 0x06, 0x85, 0x5a]⟩ -- kiss(uint256)
  | 17 => ⟨#[0x95, 0x7a, 0xa5, 0x8c]⟩ -- live()
  | 18 => ⟨#[0x65, 0xfa, 0xe3, 0x5e]⟩ -- rely(address)
  | 19 => ⟨#[0xcb, 0x5c, 0xc1, 0x09]⟩ -- sin(uint256)
  | 20 => ⟨#[0xc3, 0x49, 0xd3, 0x62]⟩ -- sump()
  | 21 => ⟨#[0x36, 0x56, 0x9e, 0x77]⟩ -- vat()
  | 22 => ⟨#[0x64, 0xbd, 0x70, 0x13]⟩ -- wait()
  | _ => ⟨#[0xbf, 0x35, 0x3d, 0xbb]⟩  -- wards(address)

/-! ## Dispatcher constants and prefix reachability -/

abbrev vowRootSplitPc : UInt256 := ⟨32⟩
abbrev vowHighSplitPc : UInt256 := ⟨43⟩
abbrev vowHighHighFirstArmPc : UInt256 := ⟨54⟩
abbrev vowHighLowJumpdestPc : UInt256 := ⟨124⟩
abbrev vowHighLowFirstArmPc : UInt256 := ⟨125⟩
abbrev vowLowJumpdestPc : UInt256 := ⟨195⟩
abbrev vowLowSplitPc : UInt256 := ⟨196⟩
abbrev vowLowHighFirstArmPc : UInt256 := ⟨207⟩
abbrev vowLowLowJumpdestPc : UInt256 := ⟨277⟩
abbrev vowLowLowFirstArmPc : UInt256 := ⟨278⟩
abbrev vowDispatchBodyPc : UInt256 := ⟨18⟩
abbrev vowSelectorLoadPc : UInt256 := ⟨26⟩
abbrev vowDispatchRevertPc : UInt256 := ⟨344⟩

def vowLowLowSelBytes : ℕ → ByteArray
  | 0 => ⟨#[0x0e, 0x01, 0x19, 0x8b]⟩ -- flap()
  | 1 => ⟨#[0x1b, 0x8e, 0x8c, 0xfa]⟩ -- hump()
  | 2 => ⟨#[0x25, 0x06, 0x85, 0x5a]⟩ -- kiss(uint256)
  | 3 => ⟨#[0x29, 0xae, 0x81, 0x14]⟩ -- file(bytes32,uint256)
  | 4 => ⟨#[0x2a, 0x1d, 0x2b, 0x3c]⟩ -- Ash()
  | _ => ⟨#[0x36, 0x56, 0x9e, 0x77]⟩  -- vat()

def vowLowHighSelBytes : ℕ → ByteArray
  | 0 => ⟨#[0x40, 0x81, 0xd7, 0x3a]⟩ -- flopper()
  | 1 => ⟨#[0x5c, 0xa0, 0xd7, 0x23]⟩ -- flapper()
  | 2 => ⟨#[0x64, 0xbd, 0x70, 0x13]⟩ -- wait()
  | 3 => ⟨#[0x65, 0xfa, 0xe3, 0x5e]⟩ -- rely(address)
  | 4 => ⟨#[0x68, 0x11, 0x0b, 0x2f]⟩ -- bump()
  | _ => ⟨#[0x69, 0x24, 0x50, 0x09]⟩  -- cage()

def vowHighLowSelBytes : ℕ → ByteArray
  | 0 => ⟨#[0x69, 0x7e, 0xfb, 0x78]⟩ -- fess(uint256)
  | 1 => ⟨#[0x95, 0x7a, 0xa5, 0x8c]⟩ -- live()
  | 2 => ⟨#[0x9c, 0x52, 0xa7, 0xf1]⟩ -- deny(address)
  | 3 => ⟨#[0xbb, 0xbb, 0x0d, 0x7b]⟩ -- flop()
  | 4 => ⟨#[0xbf, 0x35, 0x3d, 0xbb]⟩ -- wards(address)
  | _ => ⟨#[0xc3, 0x49, 0xd3, 0x62]⟩  -- sump()

def vowHighHighSelBytes : ℕ → ByteArray
  | 0 => ⟨#[0xcb, 0x5c, 0xc1, 0x09]⟩ -- sin(uint256)
  | 1 => ⟨#[0xd0, 0xad, 0xc3, 0x5f]⟩ -- Sin()
  | 2 => ⟨#[0xd4, 0xe8, 0xbe, 0x83]⟩ -- file(bytes32,address)
  | 3 => ⟨#[0xd7, 0xee, 0x67, 0x4b]⟩ -- flog(uint256)
  | 4 => ⟨#[0xe4, 0x33, 0x05, 0x45]⟩ -- dump()
  | _ => ⟨#[0xf3, 0x7a, 0xc6, 0x1c]⟩  -- heal(uint256)

def vowSlotWord (slot : UInt256) (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  solcSlotWord σ I slot

abbrev vowAddressReturnWord (slot : UInt256) (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.land (vowSlotWord slot σ I) solcAddrMask

theorem vowStorageLocLoad_address_offset0 (evm : EVM.State) (slot : UInt256) :
    storageLocLoad evm (addrLoc slot) =
      .address (AccountAddress.ofNat
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)
          solcAddrMask).toNat) := by
  simpa [addrLoc, addressOffset0Loc] using storageLocLoad_address_offset0 evm slot

theorem vowStorageLocLoad_uint256 (evm : EVM.State) (slot : UInt256) :
    storageLocLoad evm (wordLoc slot) =
      .int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot).toNat) := by
  simpa [wordLoc, uint256Loc] using storageLocLoad_uint256 evm slot

theorem decodeCalldata_legacyUInt256_ok {cd : ByteArray} {x : Solm.Ident}
    (hsz36 : 36 ≤ cd.size) :
    decodeCalldataWithMode DecodeMode.legacySolc05 [x] [abiUInt256] cd =
      some ((∅ : Solm.Store).insert x (.int (Int.ofNat (calldataWord cd 4).toNat))) := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have htake4 : ((cd.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have hword4 : ABI.bytesToWord ((cd.toList.drop 4).take 32) = calldataWord cd 4 :=
    decode_word_at_eq cd 4 (by omega) (by norm_num)
  rw [decodeCalldataWithMode_legacyScalarWords_eq (names := [x]) (types := [abiUInt256])
    (cd := cd) (by decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  simp only [decodeScalarWordsWithMode?]
  rw [decodeScalarWordWithMode_uint256_ok (mode := DecodeMode.legacySolc05)
    (bytes := cd.toList.drop 4) (start := 0) htake4]
  change decodeCalldata.insertValues [x]
      [.int (Int.ofNat (ABI.bytesToWord ((cd.toList.drop 4).take 32)).toNat)] ∅ =
    some ((∅ : Solm.Store).insert x (.int (Int.ofNat (calldataWord cd 4).toNat)))
  rw [hword4]
  simp [decodeCalldata.insertValues]

theorem decodeCalldata_legacyUInt256_none_short {cd : ByteArray} {x : Solm.Ident}
    (hsz4 : 4 ≤ cd.size) (hshort : cd.size < 36) :
    decodeCalldataWithMode DecodeMode.legacySolc05 [x] [abiUInt256] cd = none := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  rw [decodeCalldataWithMode_legacyScalarWords_eq (names := [x]) (types := [abiUInt256])
    (cd := cd) (by decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  simp only [decodeScalarWordsWithMode?]
  have htake0n : ¬ ((cd.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  rw [decodeScalarWordWithMode_uint256_none_short (mode := DecodeMode.legacySolc05)
    (start := 0) (by simpa using htake0n)]
  simp only [Option.bind, bind]

-- LIBRARY CANDIDATE: generalizes `Reasoning.Solc.RD.solcCheckedAddStringRevert` for
-- solc checked-add routines whose failure path is a bare `revert(0, 0)`.
@[reducible] def solcCheckedAddEmptyRevertWf
    (code : ByteArray) (pc okPc : UInt256) : Prop :=
  solcCheckedAddSuccessWf code pc okPc
  ∧ decode code (solcCheckedArithmeticRevertPc pc) =
      some (.Push .PUSH1, some (⟨0⟩, 1))
  ∧ decode code (solcCheckedArithmeticRevertPc pc + UInt256.ofNat 2) =
      some (.DUP1, .none)
  ∧ decode code (solcCheckedArithmeticRevertPc pc + UInt256.ofNat 2 + ⟨1⟩) =
      some (.REVERT, .none)

set_option maxHeartbeats 1000000 in
theorem RD.solcCheckedAddEmptyRevert {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {pc okPc a b ret : UInt256} {R : List UInt256}
    {mem : ByteArray} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD code ee g s0 pc (b :: a :: ret :: R) mem (UInt256.ofNat 3) rdata acc k C)
    (hwf : solcCheckedAddEmptyRevertWf code pc okPc)
    (hover : UInt256.size ≤ a.toNat + b.toNat)
    (hov : R.length + 9 ≤ 1024) :
    RDrev code g s0 := by
  rcases hwf with ⟨hadd, hdRev0, hdRev2, hdRev3⟩
  rcases hadd with
    ⟨hd0, hd1, hd2, hd3, hd4, hd5, hd6, hd7, hd8, hd11, _, _, _, _, _, _⟩
  have hsum_lt2 : a.toNat + b.toNat < 2 * UInt256.size := by
    have ha : a.toNat < UInt256.size := a.val.isLt
    have hb : b.toNat < UInt256.size := b.val.isLt
    omega
  have hmod : (a.toNat + b.toNat) % UInt256.size =
      a.toNat + b.toNat - UInt256.size := by
    rw [Nat.mod_eq_sub_mod hover]
    exact Nat.mod_eq_of_lt (by omega)
  have haddNat : (a + b).toNat = a.toNat + b.toNat - UInt256.size := by
    rw [uadd_toNat, hmod]
  have hlt : UInt256.lt (a + b) a = ⟨1⟩ := by
    apply ult_one
    rw [haddNat]
    have hb : b.toNat < UInt256.size := b.val.isLt
    omega
  have rd6 := evm_run h with [
    raw jumpdest hd0 (by evm_ov),
    raw dup1 hd1 (by evm_ov),
    raw dup3 hd2 (by evm_ov),
    raw add hd3 (by evm_ov),
    raw dup3 hd4 (by evm_ov),
    raw dup2 hd5 (by evm_ov)]
  have rd7₀ := evm_run rd6 with [raw lt hd6 (by evm_ov)]
  have rd7 := rd7₀
  rw [hlt] at rd7
  have rd8₀ := evm_run rd7 with [raw iszero hd7 (by evm_ov)]
  have rd8 := rd8₀
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd8
  have rdPush := evm_run rd8 with [raw push2 okPc hd8 (by evm_ov)]
  have rdTail₀ := rdPush.jumpiNT hd11 (by decide) (by simp only [List.length_cons]; omega)
  have rdTail := by
    simpa [solcCheckedArithmeticRevertPc] using rdTail₀
  exact evm_run rdTail with [
    raw push1 ⟨0⟩ hdRev0 (by evm_ov),
    raw dup1 hdRev2 (by evm_ov),
    raw rev 0 hdRev3 mem_cost (by evm_ov)]

theorem RD.solcCheckedAddEmptyRevertAnyWords {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {pc okPc a b ret : UInt256} {R : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD code ee g s0 pc (b :: a :: ret :: R) mem aw rdata acc k C)
    (hwf : solcCheckedAddEmptyRevertWf code pc okPc)
    (hover : UInt256.size ≤ a.toNat + b.toNat)
    (hov : R.length + 9 ≤ 1024) :
    RDrev code g s0 := by
  rcases hwf with ⟨hadd, hdRev0, hdRev2, hdRev3⟩
  rcases hadd with
    ⟨hd0, hd1, hd2, hd3, hd4, hd5, hd6, hd7, hd8, hd11, _, _, _, _, _, _⟩
  have hsum_lt2 : a.toNat + b.toNat < 2 * UInt256.size := by
    have ha : a.toNat < UInt256.size := a.val.isLt
    have hb : b.toNat < UInt256.size := b.val.isLt
    omega
  have hmod : (a.toNat + b.toNat) % UInt256.size =
      a.toNat + b.toNat - UInt256.size := by
    rw [Nat.mod_eq_sub_mod hover]
    exact Nat.mod_eq_of_lt (by omega)
  have haddNat : (a + b).toNat = a.toNat + b.toNat - UInt256.size := by
    rw [uadd_toNat, hmod]
  have hlt : UInt256.lt (a + b) a = ⟨1⟩ := by
    apply ult_one
    rw [haddNat]
    have hb : b.toNat < UInt256.size := b.val.isLt
    omega
  have rd6 := evm_run h with [
    raw jumpdest hd0 (by evm_ov),
    raw dup1 hd1 (by evm_ov),
    raw dup3 hd2 (by evm_ov),
    raw add hd3 (by evm_ov),
    raw dup3 hd4 (by evm_ov),
    raw dup2 hd5 (by evm_ov)]
  have rd7₀ := evm_run rd6 with [raw lt hd6 (by evm_ov)]
  have rd7 := rd7₀
  rw [hlt] at rd7
  have rd8₀ := evm_run rd7 with [raw iszero hd7 (by evm_ov)]
  have rd8 := rd8₀
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd8
  have rdPush := evm_run rd8 with [raw push2 okPc hd8 (by evm_ov)]
  have rdTail₀ := rdPush.jumpiNT hd11 (by decide) (by simp only [List.length_cons]; omega)
  have rdTail := by
    simpa [solcCheckedArithmeticRevertPc] using rdTail₀
  have rdRev := evm_run rdTail with [
    raw push1 ⟨0⟩ hdRev0 (by evm_ov),
    raw dup1 hdRev2 (by evm_ov)]
  exact RD.rev 0 rdRev hdRev3 (fun s _ hstk => memExpRevert0 s hstk) (by evm_ov)

-- LIBRARY CANDIDATE: checked-sub variant of `RD.solcCheckedAddEmptyRevert`.
@[reducible] def solcCheckedSubEmptyRevertWf
    (code : ByteArray) (pc okPc : UInt256) : Prop :=
  solcCheckedSubSuccessWf code pc okPc
  ∧ decode code (solcCheckedArithmeticRevertPc pc) =
      some (.Push .PUSH1, some (⟨0⟩, 1))
  ∧ decode code (solcCheckedArithmeticRevertPc pc + UInt256.ofNat 2) =
      some (.DUP1, .none)
  ∧ decode code (solcCheckedArithmeticRevertPc pc + UInt256.ofNat 2 + ⟨1⟩) =
      some (.REVERT, .none)

set_option maxHeartbeats 1000000 in
theorem RD.solcCheckedSubEmptyRevert {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {pc okPc a b ret : UInt256} {R : List UInt256}
    {mem : ByteArray} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD code ee g s0 pc (b :: a :: ret :: R) mem (UInt256.ofNat 3) rdata acc k C)
    (hwf : solcCheckedSubEmptyRevertWf code pc okPc)
    (hlt : a.toNat < b.toNat)
    (hov : R.length + 9 ≤ 1024) :
    RDrev code g s0 := by
  rcases hwf with ⟨hsub, hdRev0, hdRev2, hdRev3⟩
  rcases hsub with
    ⟨hd0, hd1, hd2, hd3, hd4, hd5, hd6, hd7, hd8, hd11, _, _, _, _, _, _⟩
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
  have rd6 := evm_run h with [
    raw jumpdest hd0 (by evm_ov),
    raw dup1 hd1 (by evm_ov),
    raw dup3 hd2 (by evm_ov),
    raw sub hd3 (by evm_ov),
    raw dup3 hd4 (by evm_ov),
    raw dup2 hd5 (by evm_ov)]
  have rd7₀ := evm_run rd6 with [raw gt hd6 (by evm_ov)]
  have rd7 := rd7₀
  rw [hgt] at rd7
  have rd8₀ := evm_run rd7 with [raw iszero hd7 (by evm_ov)]
  have rd8 := rd8₀
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd8
  have rdPush := evm_run rd8 with [raw push2 okPc hd8 (by evm_ov)]
  have rdTail₀ := rdPush.jumpiNT hd11 (by decide) (by simp only [List.length_cons]; omega)
  have rdTail := by
    simpa [solcCheckedArithmeticRevertPc] using rdTail₀
  exact evm_run rdTail with [
    raw push1 ⟨0⟩ hdRev0 (by evm_ov),
    raw dup1 hdRev2 (by evm_ov),
    raw rev 0 hdRev3 mem_cost (by evm_ov)]

theorem vowSelWord_eq_of_beq (I : ExecutionEnv) (hsz : 4 ≤ I.calldata.size)
    (c0 c1 c2 c3 : UInt8) (sel : UInt256)
    (hsel : (fromBytesBigEndian [c0, c1, c2, c3] : ℕ) = sel.toNat)
    (hmatch : ((⟨#[c0, c1, c2, c3]⟩ : ByteArray) == I.calldata.extract 0 4) = true) :
    vowSelWord I = sel := by
  simpa [vowSelWord, solcSelectorWord] using
    solcSelectorWord_eq_of_beq I hsz c0 c1 c2 c3 sel hsel hmatch

theorem vowRootSplitWellFormed :
    selectorSplitWellFormed vowBytecode vowRootSplitPc := by
  dsimp [selectorSplitWellFormed]
  repeat' first | apply And.intro | native_decide

theorem vowHighSplitWellFormed :
    selectorSplitWellFormed vowBytecode vowHighSplitPc := by
  dsimp [selectorSplitWellFormed]
  repeat' first | apply And.intro | native_decide

theorem vowLowSplitWellFormed :
    selectorSplitWellFormed vowBytecode vowLowSplitPc := by
  dsimp [selectorSplitWellFormed]
  repeat' first | apply And.intro | native_decide

set_option maxHeartbeats 1000000 in
theorem vowLowLowArmsWellFormed :
    ∀ j, j ≤ 5 → armWellFormed vowBytecode
      (nthArmPc vowBytecode vowLowLowFirstArmPc j) := by
  intro j hj
  interval_cases j <;>
    (dsimp [armWellFormed]
     repeat' first | apply And.intro | native_decide)

set_option maxHeartbeats 1000000 in
theorem vowLowHighArmsWellFormed :
    ∀ j, j ≤ 5 → armWellFormed vowBytecode
      (nthArmPc vowBytecode vowLowHighFirstArmPc j) := by
  intro j hj
  interval_cases j <;>
    (dsimp [armWellFormed]
     repeat' first | apply And.intro | native_decide)

set_option maxHeartbeats 1000000 in
theorem vowHighLowArmsWellFormed :
    ∀ j, j ≤ 5 → armWellFormed vowBytecode
      (nthArmPc vowBytecode vowHighLowFirstArmPc j) := by
  intro j hj
  interval_cases j <;>
    (dsimp [armWellFormed]
     repeat' first | apply And.intro | native_decide)

set_option maxHeartbeats 1000000 in
theorem vowHighHighArmsWellFormed :
    ∀ j, j ≤ 5 → armWellFormed vowBytecode
      (nthArmPc vowBytecode vowHighHighFirstArmPc j) := by
  intro j hj
  interval_cases j <;>
    (dsimp [armWellFormed]
     repeat' first | apply And.intro | native_decide)

theorem vowLowLowArmEq (I : ExecutionEnv) (hsz : 4 ≤ I.calldata.size)
    (j : ℕ) (hj : j < 6) :
    UInt256.eq
        (armSelNat vowBytecode (nthArmPc vowBytecode vowLowLowFirstArmPc j))
        (vowSelWord I) =
      if (vowLowLowSelBytes j == I.calldata.extract 0 4) then ⟨1⟩ else ⟨0⟩ := by
  interval_cases j <;> exact evmSelectorDecode hsz _ _ _ _ _ (by native_decide)

theorem vowLowHighArmEq (I : ExecutionEnv) (hsz : 4 ≤ I.calldata.size)
    (j : ℕ) (hj : j < 6) :
    UInt256.eq
        (armSelNat vowBytecode (nthArmPc vowBytecode vowLowHighFirstArmPc j))
        (vowSelWord I) =
      if (vowLowHighSelBytes j == I.calldata.extract 0 4) then ⟨1⟩ else ⟨0⟩ := by
  interval_cases j <;> exact evmSelectorDecode hsz _ _ _ _ _ (by native_decide)

theorem vowHighLowArmEq (I : ExecutionEnv) (hsz : 4 ≤ I.calldata.size)
    (j : ℕ) (hj : j < 6) :
    UInt256.eq
        (armSelNat vowBytecode (nthArmPc vowBytecode vowHighLowFirstArmPc j))
        (vowSelWord I) =
      if (vowHighLowSelBytes j == I.calldata.extract 0 4) then ⟨1⟩ else ⟨0⟩ := by
  interval_cases j <;> exact evmSelectorDecode hsz _ _ _ _ _ (by native_decide)

theorem vowHighHighArmEq (I : ExecutionEnv) (hsz : 4 ≤ I.calldata.size)
    (j : ℕ) (hj : j < 6) :
    UInt256.eq
        (armSelNat vowBytecode (nthArmPc vowBytecode vowHighHighFirstArmPc j))
        (vowSelWord I) =
      if (vowHighHighSelBytes j == I.calldata.extract 0 4) then ⟨1⟩ else ⟨0⟩ := by
  interval_cases j <;> exact evmSelectorDecode hsz _ _ _ _ _ (by native_decide)

theorem vowReachRootSplit {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = vowBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size) :
    ∃ k C, RD vowBytecode I g (initState cA gh bl σ σ₀ g A I)
        vowRootSplitPc [vowSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
  simpa [vowRootSplitPc, vowSelWord] using
    solcLegacyDispatchReachSelector (cA := cA) (gh := gh) (bl := bl) (σ := σ)
      (σ₀ := σ₀) (A := A) (g := g) (code := vowBytecode)
      (bodyPc := vowDispatchBodyPc) (loadPc := vowSelectorLoadPc)
      (firstPc := vowRootSplitPc) (guardTgt := (⟨16⟩ : UInt256))
      (revertTgt := vowDispatchRevertPc) (guardWidth := 2) (revertWidth := 2)
      (guardOp := .PUSH2) (revertOp := .PUSH2)
      hcode hwv hsz hsize
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by jump_dest) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)

theorem vowReachLowSplit {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = vowBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot : UInt256.gt (armSelNat vowBytecode vowRootSplitPc) (vowSelWord I) ≠ ⟨0⟩) :
    ∃ k C, RD vowBytecode I g (initState cA gh bl σ σ₀ g A I)
        vowLowSplitPc [vowSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
  obtain ⟨k32, C32, h32⟩ :=
    vowReachRootSplit (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize
  have h195 : RD vowBytecode I g (initState cA gh bl σ σ₀ g A I)
      (armTgt vowBytecode vowRootSplitPc) [vowSelWord I] solcFreePtrMem
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) (k32 + 5) (C32 + 22) :=
    RD.selectorSplitTakenAuto h32 vowRootSplitWellFormed hroot (by jump_dest) (by simp)
  have h196 : RD vowBytecode I g (initState cA gh bl σ σ₀ g A I)
      vowLowSplitPc [vowSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k32 + 5 + 1) (C32 + 22 + 1) := by
    simpa [vowLowSplitPc, vowLowJumpdestPc, vowRootSplitPc, armTgt, pushAt]
      using h195.jumpdest (by native_decide) (by simp)
  exact ⟨_, _, h196⟩

theorem vowReachHighSplit {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = vowBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot : UInt256.gt (armSelNat vowBytecode vowRootSplitPc) (vowSelWord I) = ⟨0⟩) :
    ∃ k C, RD vowBytecode I g (initState cA gh bl σ σ₀ g A I)
        vowHighSplitPc [vowSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
  obtain ⟨k32, C32, h32⟩ :=
    vowReachRootSplit (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize
  have h43 : RD vowBytecode I g (initState cA gh bl σ σ₀ g A I)
      vowHighSplitPc [vowSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k32 + 5) (C32 + 22) := by
    simpa [vowHighSplitPc, vowRootSplitPc, selArmNextPc, armTgtWidth,
      selArmJumpiPc, selArmPushTgtPc, selArmEqPc, selArmPush4Pc] using
      RD.selectorSplitNotTakenAuto h32 vowRootSplitWellFormed hroot (by simp)
  exact ⟨_, _, h43⟩

theorem vowReachLowLowFirstArm {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = vowBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot : UInt256.gt (armSelNat vowBytecode vowRootSplitPc) (vowSelWord I) ≠ ⟨0⟩)
    (hlow : UInt256.gt (armSelNat vowBytecode vowLowSplitPc) (vowSelWord I) ≠ ⟨0⟩) :
    ∃ k C, RD vowBytecode I g (initState cA gh bl σ σ₀ g A I)
        vowLowLowFirstArmPc [vowSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
  obtain ⟨k196, C196, h196⟩ :=
    vowReachLowSplit (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot
  have h277 : RD vowBytecode I g (initState cA gh bl σ σ₀ g A I)
      (armTgt vowBytecode vowLowSplitPc) [vowSelWord I] solcFreePtrMem
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) (k196 + 5) (C196 + 22) :=
    RD.selectorSplitTakenAuto h196 vowLowSplitWellFormed hlow (by jump_dest) (by simp)
  have h278 : RD vowBytecode I g (initState cA gh bl σ σ₀ g A I)
      vowLowLowFirstArmPc [vowSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k196 + 5 + 1) (C196 + 22 + 1) := by
    simpa [vowLowLowFirstArmPc, vowLowLowJumpdestPc, vowLowSplitPc, armTgt, pushAt]
      using h277.jumpdest (by native_decide) (by simp)
  exact ⟨_, _, h278⟩

theorem vowReachLowHighFirstArm {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = vowBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot : UInt256.gt (armSelNat vowBytecode vowRootSplitPc) (vowSelWord I) ≠ ⟨0⟩)
    (hlow : UInt256.gt (armSelNat vowBytecode vowLowSplitPc) (vowSelWord I) = ⟨0⟩) :
    ∃ k C, RD vowBytecode I g (initState cA gh bl σ σ₀ g A I)
        vowLowHighFirstArmPc [vowSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
  obtain ⟨k196, C196, h196⟩ :=
    vowReachLowSplit (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot
  have h207 : RD vowBytecode I g (initState cA gh bl σ σ₀ g A I)
      vowLowHighFirstArmPc [vowSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k196 + 5) (C196 + 22) := by
    simpa [vowLowHighFirstArmPc, vowLowSplitPc, selArmNextPc, armTgtWidth,
      selArmJumpiPc, selArmPushTgtPc, selArmEqPc, selArmPush4Pc] using
      RD.selectorSplitNotTakenAuto h196 vowLowSplitWellFormed hlow (by simp)
  exact ⟨_, _, h207⟩

theorem vowReachHighLowFirstArm {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = vowBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot : UInt256.gt (armSelNat vowBytecode vowRootSplitPc) (vowSelWord I) = ⟨0⟩)
    (hhigh : UInt256.gt (armSelNat vowBytecode vowHighSplitPc) (vowSelWord I) ≠ ⟨0⟩) :
    ∃ k C, RD vowBytecode I g (initState cA gh bl σ σ₀ g A I)
        vowHighLowFirstArmPc [vowSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
  obtain ⟨k43, C43, h43⟩ :=
    vowReachHighSplit (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot
  have h124 : RD vowBytecode I g (initState cA gh bl σ σ₀ g A I)
      (armTgt vowBytecode vowHighSplitPc) [vowSelWord I] solcFreePtrMem
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) (k43 + 5) (C43 + 22) :=
    RD.selectorSplitTakenAuto h43 vowHighSplitWellFormed hhigh (by jump_dest) (by simp)
  have h125 : RD vowBytecode I g (initState cA gh bl σ σ₀ g A I)
      vowHighLowFirstArmPc [vowSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k43 + 5 + 1) (C43 + 22 + 1) := by
    simpa [vowHighLowFirstArmPc, vowHighLowJumpdestPc, vowHighSplitPc, armTgt, pushAt]
      using h124.jumpdest (by native_decide) (by simp)
  exact ⟨_, _, h125⟩

theorem vowReachHighHighFirstArm {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = vowBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot : UInt256.gt (armSelNat vowBytecode vowRootSplitPc) (vowSelWord I) = ⟨0⟩)
    (hhigh : UInt256.gt (armSelNat vowBytecode vowHighSplitPc) (vowSelWord I) = ⟨0⟩) :
    ∃ k C, RD vowBytecode I g (initState cA gh bl σ σ₀ g A I)
        vowHighHighFirstArmPc [vowSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
  obtain ⟨k43, C43, h43⟩ :=
    vowReachHighSplit (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot
  have h54 : RD vowBytecode I g (initState cA gh bl σ σ₀ g A I)
      vowHighHighFirstArmPc [vowSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k43 + 5) (C43 + 22) := by
    simpa [vowHighHighFirstArmPc, vowHighSplitPc, selArmNextPc, armTgtWidth,
      selArmJumpiPc, selArmPushTgtPc, selArmEqPc, selArmPush4Pc] using
      RD.selectorSplitNotTakenAuto h43 vowHighSplitWellFormed hhigh (by simp)
  exact ⟨_, _, h54⟩

theorem vowReachLowLowBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (i : ℕ) (hi : i ≤ 5) (bodyPC : UInt256)
    (hcode : I.code = vowBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot : UInt256.gt (armSelNat vowBytecode vowRootSplitPc) (vowSelWord I) ≠ ⟨0⟩)
    (hlow : UInt256.gt (armSelNat vowBytecode vowLowSplitPc) (vowSelWord I) ≠ ⟨0⟩)
    (heq0 : ∀ j, j < i →
      UInt256.eq (armSelNat vowBytecode (nthArmPc vowBytecode vowLowLowFirstArmPc j))
        (vowSelWord I) = ⟨0⟩)
    (htake :
      UInt256.eq (armSelNat vowBytecode (nthArmPc vowBytecode vowLowLowFirstArmPc i))
        (vowSelWord I) ≠ ⟨0⟩)
    (hjd : (D_J vowBytecode 0).contains bodyPC = true)
    (hbody : armTgt vowBytecode (nthArmPc vowBytecode vowLowLowFirstArmPc i) = bodyPC) :
    ∃ k C, RD vowBytecode I g (initState cA gh bl σ σ₀ g A I)
        bodyPC [vowSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  obtain ⟨_, _, hfirst⟩ :=
    vowReachLowLowFirstArm (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot hlow
  exact RD.dispatchTo bodyPC i hfirst
    (fun j hj => vowLowLowArmsWellFormed j (le_trans hj hi))
    heq0 htake (by simpa [hbody] using hjd) hbody (by simp)

theorem vowReachLowHighBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (i : ℕ) (hi : i ≤ 5) (bodyPC : UInt256)
    (hcode : I.code = vowBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot : UInt256.gt (armSelNat vowBytecode vowRootSplitPc) (vowSelWord I) ≠ ⟨0⟩)
    (hlow : UInt256.gt (armSelNat vowBytecode vowLowSplitPc) (vowSelWord I) = ⟨0⟩)
    (heq0 : ∀ j, j < i →
      UInt256.eq (armSelNat vowBytecode (nthArmPc vowBytecode vowLowHighFirstArmPc j))
        (vowSelWord I) = ⟨0⟩)
    (htake :
      UInt256.eq (armSelNat vowBytecode (nthArmPc vowBytecode vowLowHighFirstArmPc i))
        (vowSelWord I) ≠ ⟨0⟩)
    (hjd : (D_J vowBytecode 0).contains bodyPC = true)
    (hbody : armTgt vowBytecode (nthArmPc vowBytecode vowLowHighFirstArmPc i) = bodyPC) :
    ∃ k C, RD vowBytecode I g (initState cA gh bl σ σ₀ g A I)
        bodyPC [vowSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  obtain ⟨_, _, hfirst⟩ :=
    vowReachLowHighFirstArm (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot hlow
  exact RD.dispatchTo bodyPC i hfirst
    (fun j hj => vowLowHighArmsWellFormed j (le_trans hj hi))
    heq0 htake (by simpa [hbody] using hjd) hbody (by simp)

theorem vowReachHighLowBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (i : ℕ) (hi : i ≤ 5) (bodyPC : UInt256)
    (hcode : I.code = vowBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot : UInt256.gt (armSelNat vowBytecode vowRootSplitPc) (vowSelWord I) = ⟨0⟩)
    (hhigh : UInt256.gt (armSelNat vowBytecode vowHighSplitPc) (vowSelWord I) ≠ ⟨0⟩)
    (heq0 : ∀ j, j < i →
      UInt256.eq (armSelNat vowBytecode (nthArmPc vowBytecode vowHighLowFirstArmPc j))
        (vowSelWord I) = ⟨0⟩)
    (htake :
      UInt256.eq (armSelNat vowBytecode (nthArmPc vowBytecode vowHighLowFirstArmPc i))
        (vowSelWord I) ≠ ⟨0⟩)
    (hjd : (D_J vowBytecode 0).contains bodyPC = true)
    (hbody : armTgt vowBytecode (nthArmPc vowBytecode vowHighLowFirstArmPc i) = bodyPC) :
    ∃ k C, RD vowBytecode I g (initState cA gh bl σ σ₀ g A I)
        bodyPC [vowSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  obtain ⟨_, _, hfirst⟩ :=
    vowReachHighLowFirstArm (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot hhigh
  exact RD.dispatchTo bodyPC i hfirst
    (fun j hj => vowHighLowArmsWellFormed j (le_trans hj hi))
    heq0 htake (by simpa [hbody] using hjd) hbody (by simp)

theorem vowReachHighHighBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (i : ℕ) (hi : i ≤ 5) (bodyPC : UInt256)
    (hcode : I.code = vowBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot : UInt256.gt (armSelNat vowBytecode vowRootSplitPc) (vowSelWord I) = ⟨0⟩)
    (hhigh : UInt256.gt (armSelNat vowBytecode vowHighSplitPc) (vowSelWord I) = ⟨0⟩)
    (heq0 : ∀ j, j < i →
      UInt256.eq (armSelNat vowBytecode (nthArmPc vowBytecode vowHighHighFirstArmPc j))
        (vowSelWord I) = ⟨0⟩)
    (htake :
      UInt256.eq (armSelNat vowBytecode (nthArmPc vowBytecode vowHighHighFirstArmPc i))
        (vowSelWord I) ≠ ⟨0⟩)
    (hjd : (D_J vowBytecode 0).contains bodyPC = true)
    (hbody : armTgt vowBytecode (nthArmPc vowBytecode vowHighHighFirstArmPc i) = bodyPC) :
    ∃ k C, RD vowBytecode I g (initState cA gh bl σ σ₀ g A I)
        bodyPC [vowSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  obtain ⟨_, _, hfirst⟩ :=
    vowReachHighHighFirstArm (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot hhigh
  exact RD.dispatchTo bodyPC i hfirst
    (fun j hj => vowHighHighArmsWellFormed j (le_trans hj hi))
    heq0 htake (by simpa [hbody] using hjd) hbody (by simp)

theorem vowJumpToNoMatchRevert {cA gh bl σ σ₀ A I} {g : Sat256} {pc : UInt256}
    {k C : ℕ}
    (h : RD vowBytecode I g (initState cA gh bl σ σ₀ g A I) pc
      [vowSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hpush : decode vowBytecode pc = some (.Push .PUSH2, some (vowDispatchRevertPc, 2)))
    (hjump : decode vowBytecode (pc + UInt256.ofNat 3) = some (.JUMP, .none)) :
    RDrev vowBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have h344 := h.push2 vowDispatchRevertPc hpush (by simp only [List.length_singleton]; omega)
    |>.jump hjump (by jump_dest) (by simp only [List.length_singleton]; omega)
    |>.jumpdest (by native_decide) (by simp only [List.length_singleton]; omega)
  exact RD.uniswapPush1Dup1Revert0 h344 (by native_decide) (by native_decide)
    (by native_decide) (by simp only [List.length_singleton]; omega)

theorem vowLowLowNoMatchRevert {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ}
    (h : RD vowBytecode I g (initState cA gh bl σ σ₀ g A I) vowLowLowFirstArmPc
      [vowSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (heq0 : ∀ j, j < 6 →
      UInt256.eq (armSelNat vowBytecode (nthArmPc vowBytecode vowLowLowFirstArmPc j))
        (vowSelWord I) = ⟨0⟩) :
    RDrev vowBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have h344 := h
    |>.selectorArmNotTakenAuto (vowLowLowArmsWellFormed 0 (by omega))
        (heq0 0 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (vowLowLowArmsWellFormed 1 (by omega))
        (heq0 1 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (vowLowLowArmsWellFormed 2 (by omega))
        (heq0 2 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (vowLowLowArmsWellFormed 3 (by omega))
        (heq0 3 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (vowLowLowArmsWellFormed 4 (by omega))
        (heq0 4 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (vowLowLowArmsWellFormed 5 (by omega))
        (heq0 5 (by omega)) (by simp)
    |>.jumpdest (by native_decide) (by simp only [List.length_singleton]; omega)
  exact RD.uniswapPush1Dup1Revert0 h344 (by native_decide) (by native_decide)
    (by native_decide) (by simp only [List.length_singleton]; omega)

theorem vowLowHighNoMatchRevert {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ}
    (h : RD vowBytecode I g (initState cA gh bl σ σ₀ g A I) vowLowHighFirstArmPc
      [vowSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (heq0 : ∀ j, j < 6 →
      UInt256.eq (armSelNat vowBytecode (nthArmPc vowBytecode vowLowHighFirstArmPc j))
        (vowSelWord I) = ⟨0⟩) :
    RDrev vowBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have h273 := h
    |>.selectorArmNotTakenAuto (vowLowHighArmsWellFormed 0 (by omega))
        (heq0 0 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (vowLowHighArmsWellFormed 1 (by omega))
        (heq0 1 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (vowLowHighArmsWellFormed 2 (by omega))
        (heq0 2 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (vowLowHighArmsWellFormed 3 (by omega))
        (heq0 3 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (vowLowHighArmsWellFormed 4 (by omega))
        (heq0 4 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (vowLowHighArmsWellFormed 5 (by omega))
        (heq0 5 (by omega)) (by simp)
  exact vowJumpToNoMatchRevert h273 (by native_decide) (by native_decide)

theorem vowHighLowNoMatchRevert {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ}
    (h : RD vowBytecode I g (initState cA gh bl σ σ₀ g A I) vowHighLowFirstArmPc
      [vowSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (heq0 : ∀ j, j < 6 →
      UInt256.eq (armSelNat vowBytecode (nthArmPc vowBytecode vowHighLowFirstArmPc j))
        (vowSelWord I) = ⟨0⟩) :
    RDrev vowBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have h191 := h
    |>.selectorArmNotTakenAuto (vowHighLowArmsWellFormed 0 (by omega))
        (heq0 0 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (vowHighLowArmsWellFormed 1 (by omega))
        (heq0 1 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (vowHighLowArmsWellFormed 2 (by omega))
        (heq0 2 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (vowHighLowArmsWellFormed 3 (by omega))
        (heq0 3 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (vowHighLowArmsWellFormed 4 (by omega))
        (heq0 4 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (vowHighLowArmsWellFormed 5 (by omega))
        (heq0 5 (by omega)) (by simp)
  exact vowJumpToNoMatchRevert h191 (by native_decide) (by native_decide)

theorem vowHighHighNoMatchRevert {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ}
    (h : RD vowBytecode I g (initState cA gh bl σ σ₀ g A I) vowHighHighFirstArmPc
      [vowSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (heq0 : ∀ j, j < 6 →
      UInt256.eq (armSelNat vowBytecode (nthArmPc vowBytecode vowHighHighFirstArmPc j))
        (vowSelWord I) = ⟨0⟩) :
    RDrev vowBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have h120 := h
    |>.selectorArmNotTakenAuto (vowHighHighArmsWellFormed 0 (by omega))
        (heq0 0 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (vowHighHighArmsWellFormed 1 (by omega))
        (heq0 1 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (vowHighHighArmsWellFormed 2 (by omega))
        (heq0 2 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (vowHighHighArmsWellFormed 3 (by omega))
        (heq0 3 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (vowHighHighArmsWellFormed 4 (by omega))
        (heq0 4 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (vowHighHighArmsWellFormed 5 (by omega))
        (heq0 5 (by omega)) (by simp)
  exact vowJumpToNoMatchRevert h120 (by native_decide) (by native_decide)

theorem vowX_noMatch {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = vowBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hnm : ∀ i, i < 24 → (vowSelBytes i == I.calldata.extract 0 4) = false) :
    RDrev vowBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have heqLowLow : ∀ j, j < 6 →
      UInt256.eq
        (armSelNat vowBytecode (nthArmPc vowBytecode vowLowLowFirstArmPc j))
        (vowSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j
    · rw [vowLowLowArmEq I hsz 0 (by omega)]
      have hfalse : (vowLowLowSelBytes 0 == I.calldata.extract 0 4) = false := by
        simpa [vowLowLowSelBytes, vowSelBytes] using hnm 9 (by omega)
      rw [hfalse]; rfl
    · rw [vowLowLowArmEq I hsz 1 (by omega)]
      have hfalse : (vowLowLowSelBytes 1 == I.calldata.extract 0 4) = false := by
        simpa [vowLowLowSelBytes, vowSelBytes] using hnm 15 (by omega)
      rw [hfalse]; rfl
    · rw [vowLowLowArmEq I hsz 2 (by omega)]
      have hfalse : (vowLowLowSelBytes 2 == I.calldata.extract 0 4) = false := by
        simpa [vowLowLowSelBytes, vowSelBytes] using hnm 16 (by omega)
      rw [hfalse]; rfl
    · rw [vowLowLowArmEq I hsz 3 (by omega)]
      have hfalse : (vowLowLowSelBytes 3 == I.calldata.extract 0 4) = false := by
        simpa [vowLowLowSelBytes, vowSelBytes] using hnm 7 (by omega)
      rw [hfalse]; rfl
    · rw [vowLowLowArmEq I hsz 4 (by omega)]
      have hfalse : (vowLowLowSelBytes 4 == I.calldata.extract 0 4) = false := by
        simpa [vowLowLowSelBytes, vowSelBytes] using hnm 0 (by omega)
      rw [hfalse]; rfl
    · rw [vowLowLowArmEq I hsz 5 (by omega)]
      have hfalse : (vowLowLowSelBytes 5 == I.calldata.extract 0 4) = false := by
        simpa [vowLowLowSelBytes, vowSelBytes] using hnm 21 (by omega)
      rw [hfalse]; rfl
  have heqLowHigh : ∀ j, j < 6 →
      UInt256.eq
        (armSelNat vowBytecode (nthArmPc vowBytecode vowLowHighFirstArmPc j))
        (vowSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j
    · rw [vowLowHighArmEq I hsz 0 (by omega)]
      have hfalse : (vowLowHighSelBytes 0 == I.calldata.extract 0 4) = false := by
        simpa [vowLowHighSelBytes, vowSelBytes] using hnm 13 (by omega)
      rw [hfalse]; rfl
    · rw [vowLowHighArmEq I hsz 1 (by omega)]
      have hfalse : (vowLowHighSelBytes 1 == I.calldata.extract 0 4) = false := by
        simpa [vowLowHighSelBytes, vowSelBytes] using hnm 10 (by omega)
      rw [hfalse]; rfl
    · rw [vowLowHighArmEq I hsz 2 (by omega)]
      have hfalse : (vowLowHighSelBytes 2 == I.calldata.extract 0 4) = false := by
        simpa [vowLowHighSelBytes, vowSelBytes] using hnm 22 (by omega)
      rw [hfalse]; rfl
    · rw [vowLowHighArmEq I hsz 3 (by omega)]
      have hfalse : (vowLowHighSelBytes 3 == I.calldata.extract 0 4) = false := by
        simpa [vowLowHighSelBytes, vowSelBytes] using hnm 18 (by omega)
      rw [hfalse]; rfl
    · rw [vowLowHighArmEq I hsz 4 (by omega)]
      have hfalse : (vowLowHighSelBytes 4 == I.calldata.extract 0 4) = false := by
        simpa [vowLowHighSelBytes, vowSelBytes] using hnm 2 (by omega)
      rw [hfalse]; rfl
    · rw [vowLowHighArmEq I hsz 5 (by omega)]
      have hfalse : (vowLowHighSelBytes 5 == I.calldata.extract 0 4) = false := by
        simpa [vowLowHighSelBytes, vowSelBytes] using hnm 3 (by omega)
      rw [hfalse]; rfl
  have heqHighLow : ∀ j, j < 6 →
      UInt256.eq
        (armSelNat vowBytecode (nthArmPc vowBytecode vowHighLowFirstArmPc j))
        (vowSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j
    · rw [vowHighLowArmEq I hsz 0 (by omega)]
      have hfalse : (vowHighLowSelBytes 0 == I.calldata.extract 0 4) = false := by
        simpa [vowHighLowSelBytes, vowSelBytes] using hnm 6 (by omega)
      rw [hfalse]; rfl
    · rw [vowHighLowArmEq I hsz 1 (by omega)]
      have hfalse : (vowHighLowSelBytes 1 == I.calldata.extract 0 4) = false := by
        simpa [vowHighLowSelBytes, vowSelBytes] using hnm 17 (by omega)
      rw [hfalse]; rfl
    · rw [vowHighLowArmEq I hsz 2 (by omega)]
      have hfalse : (vowHighLowSelBytes 2 == I.calldata.extract 0 4) = false := by
        simpa [vowHighLowSelBytes, vowSelBytes] using hnm 4 (by omega)
      rw [hfalse]; rfl
    · rw [vowHighLowArmEq I hsz 3 (by omega)]
      have hfalse : (vowHighLowSelBytes 3 == I.calldata.extract 0 4) = false := by
        simpa [vowHighLowSelBytes, vowSelBytes] using hnm 12 (by omega)
      rw [hfalse]; rfl
    · rw [vowHighLowArmEq I hsz 4 (by omega)]
      have hfalse : (vowHighLowSelBytes 4 == I.calldata.extract 0 4) = false := by
        simpa [vowHighLowSelBytes, vowSelBytes] using hnm 23 (by omega)
      rw [hfalse]; rfl
    · rw [vowHighLowArmEq I hsz 5 (by omega)]
      have hfalse : (vowHighLowSelBytes 5 == I.calldata.extract 0 4) = false := by
        simpa [vowHighLowSelBytes, vowSelBytes] using hnm 20 (by omega)
      rw [hfalse]; rfl
  have heqHighHigh : ∀ j, j < 6 →
      UInt256.eq
        (armSelNat vowBytecode (nthArmPc vowBytecode vowHighHighFirstArmPc j))
        (vowSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j
    · rw [vowHighHighArmEq I hsz 0 (by omega)]
      have hfalse : (vowHighHighSelBytes 0 == I.calldata.extract 0 4) = false := by
        simpa [vowHighHighSelBytes, vowSelBytes] using hnm 19 (by omega)
      rw [hfalse]; rfl
    · rw [vowHighHighArmEq I hsz 1 (by omega)]
      have hfalse : (vowHighHighSelBytes 1 == I.calldata.extract 0 4) = false := by
        simpa [vowHighHighSelBytes, vowSelBytes] using hnm 1 (by omega)
      rw [hfalse]; rfl
    · rw [vowHighHighArmEq I hsz 2 (by omega)]
      have hfalse : (vowHighHighSelBytes 2 == I.calldata.extract 0 4) = false := by
        simpa [vowHighHighSelBytes, vowSelBytes] using hnm 8 (by omega)
      rw [hfalse]; rfl
    · rw [vowHighHighArmEq I hsz 3 (by omega)]
      have hfalse : (vowHighHighSelBytes 3 == I.calldata.extract 0 4) = false := by
        simpa [vowHighHighSelBytes, vowSelBytes] using hnm 11 (by omega)
      rw [hfalse]; rfl
    · rw [vowHighHighArmEq I hsz 4 (by omega)]
      have hfalse : (vowHighHighSelBytes 4 == I.calldata.extract 0 4) = false := by
        simpa [vowHighHighSelBytes, vowSelBytes] using hnm 5 (by omega)
      rw [hfalse]; rfl
    · rw [vowHighHighArmEq I hsz 5 (by omega)]
      have hfalse : (vowHighHighSelBytes 5 == I.calldata.extract 0 4) = false := by
        simpa [vowHighHighSelBytes, vowSelBytes] using hnm 14 (by omega)
      rw [hfalse]; rfl
  by_cases hroot : UInt256.gt (armSelNat vowBytecode vowRootSplitPc) (vowSelWord I) ≠ ⟨0⟩
  · by_cases hlow : UInt256.gt (armSelNat vowBytecode vowLowSplitPc) (vowSelWord I) ≠ ⟨0⟩
    · obtain ⟨_, _, hfirst⟩ :=
        vowReachLowLowFirstArm (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
          (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot hlow
      exact vowLowLowNoMatchRevert hfirst heqLowLow
    · have hlow0 : UInt256.gt (armSelNat vowBytecode vowLowSplitPc) (vowSelWord I) = ⟨0⟩ := by
        by_contra hne
        exact hlow hne
      obtain ⟨_, _, hfirst⟩ :=
        vowReachLowHighFirstArm (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
          (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot hlow0
      exact vowLowHighNoMatchRevert hfirst heqLowHigh
  · have hroot0 : UInt256.gt (armSelNat vowBytecode vowRootSplitPc) (vowSelWord I) = ⟨0⟩ := by
      by_contra hne
      exact hroot hne
    by_cases hhigh : UInt256.gt (armSelNat vowBytecode vowHighSplitPc) (vowSelWord I) ≠ ⟨0⟩
    · obtain ⟨_, _, hfirst⟩ :=
        vowReachHighLowFirstArm (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
          (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot0 hhigh
      exact vowHighLowNoMatchRevert hfirst heqHighLow
    · have hhigh0 :
          UInt256.gt (armSelNat vowBytecode vowHighSplitPc) (vowSelWord I) = ⟨0⟩ := by
        by_contra hne
        exact hhigh hne
      obtain ⟨_, _, hfirst⟩ :=
        vowReachHighHighFirstArm (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
          (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot0 hhigh0
      exact vowHighHighNoMatchRevert hfirst heqHighHigh

/-! ## Simple storage getter cores -/

theorem vowAddressGetterBodyReturns (evm : EVM.State) (locals : Store)
    {ref : StorageRef} {er : EvaledStorageRef} {slot : UInt256}
    (h : evm.executionEnv.weiValue = ⟨0⟩)
    (hbase : locals.get? ref.base = none)
    (her : evalStorageRef config { contract := contract, locals := locals } evm ref = .ok er)
    (hty : storageTypeAt? contract.storage er = some (.elem .address))
    (hloc : config.storage.layout er = fun _ => some (addrLoc slot)) :
    ExecTransitionBody config contract evm locals (nonpayable ++ [ .return [(.storage ref)] ])
      (.returned { contract := contract, locals := locals } evm
        (some [(.address (AccountAddress.ofNat
          (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)
            solcAddrMask).toNat))])) := by
  simpa [nonpayable] using
    nonpayableReturnExprBodyReturns (cfg := config) (contract := contract) h (by
      rw [evalExpr_storage_scalar (hbase := hbase) (her := her) (hty := hty) (hloc := hloc)]
      exact congrArg EvalResult.ok (vowStorageLocLoad_address_offset0 evm slot))

theorem vowUint256GetterBodyReturns (evm : EVM.State) (locals : Store)
    {ref : StorageRef} {er : EvaledStorageRef} {slot : UInt256}
    (h : evm.executionEnv.weiValue = ⟨0⟩)
    (hbase : locals.get? ref.base = none)
    (her : evalStorageRef config { contract := contract, locals := locals } evm ref = .ok er)
    (hty : storageTypeAt? contract.storage er = some (.elem (.int uint256Int)))
    (hloc : config.storage.layout er = fun _ => some (wordLoc slot)) :
    ExecTransitionBody config contract evm locals (nonpayable ++ [ .return [(.storage ref)] ])
      (.returned { contract := contract, locals := locals } evm
        (some [(.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot).toNat))])) := by
  simpa [nonpayable] using
    nonpayableReturnExprBodyReturns (cfg := config) (contract := contract) h (by
      rw [evalExpr_storage_scalar (hbase := hbase) (her := her) (hty := hty) (hloc := hloc)]
      exact congrArg EvalResult.ok (vowStorageLocLoad_uint256 evm slot))

theorem vowAddressGetterBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    {transition : TransitionDecl} {entry routine slot : UInt256}
    (hcode : I.code = vowBytecode)
    (hdispatch : dispatchMsg contract I.calldata = some transition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (transition.params.map Param.name)
        (transitionSignature transition).paramTypes I.calldata = some ∅)
    (hreach : ∃ k C, RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) entry [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hentry : solcGetterEntryWf vowBytecode entry ⟨465⟩ routine)
    (hgetter : solcAddressSlotGetterWf vowBytecode routine slot)
    (hroutine : (D_J vowBytecode 0).contains routine = true)
    (hreturn : transition.returnType = [addr])
    (hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅ transition.body
        (.returned { contract := contract, locals := ∅ }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.address (AccountAddress.ofNat
            (vowAddressReturnWord slot σ_solm I).toNat))]))) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hword : vowSlotWord slot σ_evm I = vowSlotWord slot σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner slot ⟨0⟩
  have hval :
      some [Value.address (AccountAddress.ofNat (vowAddressReturnWord slot σ_solm I).toNat)] =
        some [Value.address (AccountAddress.ofNat (vowAddressReturnWord slot σ_evm I).toNat)] := by
    have hslot : vowSlotWord slot σ_solm I = vowSlotWord slot σ_evm I := hword.symm
    simp [vowAddressReturnWord, hslot]
  have henc :
      returnEquiv (UInt256.toByteArray (vowAddressReturnWord slot σ_evm I))
        (some [(.address (AccountAddress.ofNat (vowAddressReturnWord slot σ_evm I).toNat))])
        transition.returnType := by
    rw [hreturn]
    simpa [vowAddressReturnWord] using
      (returnEquiv_of_encode
        (solcAddressReturnEncoding (addrTy := addr) rfl (vowSlotWord slot σ_evm I)))
  have hret := RD.solcAddressGetterExternal (code := vowBytecode) (g := Sat256.ofUInt256 g)
    (returnPc := ⟨465⟩) (entry := entry) (routine := routine) (slot := slot)
    hreach hentry hgetter hroutine (by jump_dest)
    (by
      unfold solcReturnAddressFromMemWf
      repeat' first | apply And.intro | native_decide)
  have hret' :
      RDret vowBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) (cA, σ_evm)
        (UInt256.toByteArray (vowAddressReturnWord slot σ_evm I)) := by
    simpa [vowAddressReturnWord, vowSlotWord] using hret
  exact hret'.reEquivExecutionTransport hcode hdispatch hdecode hbody hval hAccounts henc

theorem vowUint256GetterBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    {transition : TransitionDecl} {entry routine slot : UInt256}
    (hcode : I.code = vowBytecode)
    (hdispatch : dispatchMsg contract I.calldata = some transition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (transition.params.map Param.name)
        (transitionSignature transition).paramTypes I.calldata = some ∅)
    (hreach : ∃ k C, RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) entry [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hentry : solcGetterEntryWf vowBytecode entry ⟨357⟩ routine)
    (hgetter : solcWordSlotGetterWf vowBytecode routine slot)
    (hroutine : (D_J vowBytecode 0).contains routine = true)
    (hreturn : transition.returnType = [uint256])
    (hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅ transition.body
        (.returned { contract := contract, locals := ∅ }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.int (Int.ofNat (vowSlotWord slot σ_solm I).toNat))]))) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hword : vowSlotWord slot σ_evm I = vowSlotWord slot σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner slot ⟨0⟩
  have hval :
      some [Value.int (Int.ofNat (vowSlotWord slot σ_solm I).toNat)] =
        some [Value.int (Int.ofNat (vowSlotWord slot σ_evm I).toNat)] := by
    rw [hword]
  have henc :
      returnEquiv (UInt256.toByteArray (vowSlotWord slot σ_evm I))
        (some [(.int (Int.ofNat (vowSlotWord slot σ_evm I).toNat))])
        transition.returnType := by
    rw [hreturn]
    exact returnEquiv_of_encode
      (by simpa [uint256] using uint256ReturnEncoding (vowSlotWord slot σ_evm I))
  have hret := RD.solcWordGetterExternal (code := vowBytecode) (g := Sat256.ofUInt256 g)
    (returnPc := ⟨357⟩) (entry := entry) (routine := routine) (slot := slot)
    hreach hentry hgetter hroutine (by jump_dest)
    (by
      unfold solcReturnWordFromMemWf
      repeat' first | apply And.intro | native_decide)
  have hret' :
      RDret vowBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) (cA, σ_evm)
        (UInt256.toByteArray (vowSlotWord slot σ_evm I)) := by
    simpa [vowSlotWord] using hret
  exact hret'.reEquivExecutionTransport hcode hdispatch hdecode hbody hval hAccounts henc

theorem vowDispatch_none_short {cd : ByteArray} (h : cd.size < 4) :
    dispatchMsg contract cd = none := by
  rw [dispatchMsg_eq_dispatchList contract cd (by rfl)]
  change dispatchList
    [AshTransition, SinTransition, bumpTransition, cageTransition, denyTransition,
      dumpTransition, fessTransition, fileUintTransition, fileAddressTransition,
      flapTransition, flapperTransition, flogTransition, flopTransition,
      flopperTransition, healTransition, humpTransition, kissTransition, liveTransition,
      relyTransition, sinTransition, sumpTransition, vatTransition, waitTransition,
      wardsTransition] cd = none
  exact dispatchList_none_short _ (by
    intro t ht
    simp at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      simp [selectorOf, AshSelectorBytes, SinSelectorBytes, bumpSelectorBytes,
        cageSelectorBytes, denySelectorBytes, dumpSelectorBytes, fessSelectorBytes,
        fileUintSelectorBytes, fileAddressSelectorBytes, flapSelectorBytes,
        flapperSelectorBytes, flogSelectorBytes, flopSelectorBytes, flopperSelectorBytes,
        healSelectorBytes, humpSelectorBytes, kissSelectorBytes, liveSelectorBytes,
        relySelectorBytes, sinSelectorBytes, sumpSelectorBytes, vatSelectorBytes,
        waitSelectorBytes, wardsSelectorBytes]
      native_decide) h

theorem vowDispatch_none_nomatch {cd : ByteArray}
    (hnm : ∀ i, i < 24 → (vowSelBytes i == cd.extract 0 4) = false) :
    dispatchMsg contract cd = none := by
  apply dispatchMsg_none_of_all_ne (hfallback := by rfl)
  intro t ht
  simp [contract, transitions] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [selectorOf, AshSelectorBytes]
    simpa [vowSelBytes] using hnm 0 (by omega)
  · rw [selectorOf, SinSelectorBytes]
    simpa [vowSelBytes] using hnm 1 (by omega)
  · rw [selectorOf, bumpSelectorBytes]
    simpa [vowSelBytes] using hnm 2 (by omega)
  · rw [selectorOf, cageSelectorBytes]
    simpa [vowSelBytes] using hnm 3 (by omega)
  · rw [selectorOf, denySelectorBytes]
    simpa [vowSelBytes] using hnm 4 (by omega)
  · rw [selectorOf, dumpSelectorBytes]
    simpa [vowSelBytes] using hnm 5 (by omega)
  · rw [selectorOf, fessSelectorBytes]
    simpa [vowSelBytes] using hnm 6 (by omega)
  · rw [selectorOf, fileUintSelectorBytes]
    simpa [vowSelBytes] using hnm 7 (by omega)
  · rw [selectorOf, fileAddressSelectorBytes]
    simpa [vowSelBytes] using hnm 8 (by omega)
  · rw [selectorOf, flapSelectorBytes]
    simpa [vowSelBytes] using hnm 9 (by omega)
  · rw [selectorOf, flapperSelectorBytes]
    simpa [vowSelBytes] using hnm 10 (by omega)
  · rw [selectorOf, flogSelectorBytes]
    simpa [vowSelBytes] using hnm 11 (by omega)
  · rw [selectorOf, flopSelectorBytes]
    simpa [vowSelBytes] using hnm 12 (by omega)
  · rw [selectorOf, flopperSelectorBytes]
    simpa [vowSelBytes] using hnm 13 (by omega)
  · rw [selectorOf, healSelectorBytes]
    simpa [vowSelBytes] using hnm 14 (by omega)
  · rw [selectorOf, humpSelectorBytes]
    simpa [vowSelBytes] using hnm 15 (by omega)
  · rw [selectorOf, kissSelectorBytes]
    simpa [vowSelBytes] using hnm 16 (by omega)
  · rw [selectorOf, liveSelectorBytes]
    simpa [vowSelBytes] using hnm 17 (by omega)
  · rw [selectorOf, relySelectorBytes]
    simpa [vowSelBytes] using hnm 18 (by omega)
  · rw [selectorOf, sinSelectorBytes]
    simpa [vowSelBytes] using hnm 19 (by omega)
  · rw [selectorOf, sumpSelectorBytes]
    simpa [vowSelBytes] using hnm 20 (by omega)
  · rw [selectorOf, vatSelectorBytes]
    simpa [vowSelBytes] using hnm 21 (by omega)
  · rw [selectorOf, waitSelectorBytes]
    simpa [vowSelBytes] using hnm 22 (by omega)
  · rw [selectorOf, wardsSelectorBytes]
    simpa [vowSelBytes] using hnm 23 (by omega)

theorem vowBodyReverts_nonPayable (t : TransitionDecl) (ht : t ∈ contract.transitions)
    (evm : EVM.State) (locals : Store) (h : evm.executionEnv.weiValue ≠ ⟨0⟩) :
    ExecTransitionBody config contract evm locals t.body .reverted := by
  simp [contract, transitions] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact bodyReverts_nonPayable h

theorem vowX_callvalue_ne {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = vowBytecode) (hwv : I.weiValue ≠ ⟨0⟩) :
    RDrev vowBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have h0 := solcGuardPrologueRD (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (g := g) hcode
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have h12 := h0.push2 ⟨16⟩ (by native_decide) (by simp only [List.length]; omega)
    |>.jumpiNT (by native_decide) (isZero_eq_zero_of_ne hwv)
      (by simp only [List.length]; omega)
  exact RD.uniswapPush1Dup1Revert0 h12 (by native_decide) (by native_decide)
    (by native_decide) (by simp only [List.length]; omega)

theorem vowX_short {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = vowBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : I.calldata.size < 4) :
    RDrev vowBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have h0 := solcGuardPrologueRD (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (g := g) hcode (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  obtain ⟨_, _, h1⟩ := solcGuardCallvalueZero
    (ctgt := solcGuardTgt vowBytecode)
    (opC := solcGuardTgtOp vowBytecode)
    (wC := solcGuardTgtWidth vowBytecode) h0 hwv
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by jump_dest)
  have h344 := h1.push1 ⟨4⟩ (by native_decide) (by simp only [List.length]; omega)
    |>.calldatasize (by native_decide) (by simp only [List.length]; omega)
    |>.lt (by native_decide) (by simp only [List.length]; omega)
    |>.push2 ⟨344⟩ (by native_decide) (by simp only [List.length]; omega)
    |>.jumpiT (by native_decide) (lt_four_ne_zero_of_lt hsz) (by jump_dest)
      (by simp only [List.length]; omega)
    |>.jumpdest (by native_decide) (by simp only [List.length]; omega)
  exact RD.uniswapPush1Dup1Revert0 h344 (by native_decide) (by native_decide)
    (by native_decide) (by simp only [List.length]; omega)

end Benchmarks.Dss.Vow
