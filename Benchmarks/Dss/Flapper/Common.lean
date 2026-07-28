import Benchmarks.Dss.Flapper.Bytecode
import Reasoning.ABI
import Reasoning.Theory
import Reasoning.Stepping
import Reasoning.Reach
import Reasoning.Solc
import Reasoning.Storage
import Reasoning.Dispatch
import Reasoning.SolmBody
import Mathlib.Tactic.IntervalCases

/-!
# MakerDAO/Sky DSS Flapper shared proof foundation

Contract-wide selector notation and constants for the optimized Flapper runtime.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.Flapper

/-- The 4-byte selector word computed by `CALLDATALOAD(0); SHR 224`. -/
abbrev flapperSelWord (I : ExecutionEnv) : UInt256 :=
  UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩

/-- The 4-byte selector of `I`'s calldata equals `sel`. -/
abbrev selIs (I : ExecutionEnv) (sel : ByteArray) : Prop :=
  (sel == I.calldata.extract 0 4) = true

/-- Function selectors in `contract.transitions` order. -/
def flapperSelBytes : ℕ → ByteArray
  | 0 => ⟨#[0x7d, 0x78, 0x0d, 0x82]⟩  -- beg()
  | 1 => ⟨#[0x44, 0x23, 0xc5, 0xf1]⟩  -- bids(uint256)
  | 2 => ⟨#[0xa2, 0xf9, 0x1a, 0xf2]⟩  -- cage(uint256)
  | 3 => ⟨#[0xc9, 0x59, 0xc4, 0x2b]⟩  -- deal(uint256)
  | 4 => ⟨#[0x9c, 0x52, 0xa7, 0xf1]⟩  -- deny(address)
  | 5 => ⟨#[0x29, 0xae, 0x81, 0x14]⟩  -- file(bytes32,uint256)
  | 6 => ⟨#[0xd9, 0xc5, 0x5c, 0xe1]⟩  -- fill()
  | 7 => ⟨#[0x7b, 0xd2, 0xbe, 0xa7]⟩  -- gem()
  | 8 => ⟨#[0xca, 0x40, 0xc4, 0x19]⟩  -- kick(uint256,uint256)
  | 9 => ⟨#[0xcf, 0xdd, 0x33, 0x02]⟩  -- kicks()
  | 10 => ⟨#[0x26, 0xd2, 0xad, 0xdc]⟩ -- lid()
  | 11 => ⟨#[0x95, 0x7a, 0xa5, 0x8c]⟩ -- live()
  | 12 => ⟨#[0x65, 0xfa, 0xe3, 0x5e]⟩ -- rely(address)
  | 13 => ⟨#[0xcf, 0xc4, 0xaf, 0x55]⟩ -- tau()
  | 14 => ⟨#[0x4b, 0x43, 0xed, 0x12]⟩ -- tend(uint256,uint256,uint256)
  | 15 => ⟨#[0xfc, 0x7b, 0x6a, 0xee]⟩ -- tick(uint256)
  | 16 => ⟨#[0x4e, 0x8b, 0x1d, 0xd5]⟩ -- ttl()
  | 17 => ⟨#[0x36, 0x56, 0x9e, 0x77]⟩ -- vat()
  | 18 => ⟨#[0xbf, 0x35, 0x3d, 0xbb]⟩ -- wards(address)
  | _ => ⟨#[0x26, 0xe0, 0x27, 0xf1]⟩  -- yank(uint256)

def flapperSlotWord (slot : UInt256) (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  solcSlotWord σ I slot

abbrev flapperAddressReturnWord (slot : UInt256) (σ : AccountMap) (I : ExecutionEnv) :
    UInt256 :=
  UInt256.land (flapperSlotWord slot σ I) solcAddrMask

abbrev flapperUint48Mask : UInt256 :=
  ⟨0xffffffffffff⟩

def flapperUint48Offset0Word (slot : UInt256) (σ : AccountMap) (I : ExecutionEnv) :
    UInt256 :=
  UInt256.land (flapperSlotWord slot σ I) flapperUint48Mask

def flapperUint48Offset6Word (slot : UInt256) (σ : AccountMap) (I : ExecutionEnv) :
    UInt256 :=
  UInt256.land flapperUint48Mask
    (UInt256.div (flapperSlotWord slot σ I) (UInt256.ofNat (256 ^ 6)))

def flapperUint48Offset20Word (slot : UInt256) (σ : AccountMap) (I : ExecutionEnv) :
    UInt256 :=
  UInt256.land flapperUint48Mask
    (UInt256.div (flapperSlotWord slot σ I) (UInt256.ofNat (256 ^ 20)))

def flapperUint48Offset26Word (slot : UInt256) (σ : AccountMap) (I : ExecutionEnv) :
    UInt256 :=
  UInt256.land flapperUint48Mask
    (UInt256.div (flapperSlotWord slot σ I) (UInt256.ofNat (256 ^ 26)))

theorem flapperUint48Masked_lt (w : UInt256) :
    (UInt256.land w flapperUint48Mask).toNat < EVM.twoPow 48 := by
  show Nat.land w.toNat flapperUint48Mask.toNat % UInt256.size < EVM.twoPow 48
  have hle := nat_land_le_right w.toNat flapperUint48Mask.toNat
  have hltSize : Nat.land w.toNat flapperUint48Mask.toNat < UInt256.size :=
    lt_of_le_of_lt hle (by native_decide)
  rw [Nat.mod_eq_of_lt hltSize]
  exact lt_of_le_of_lt hle (by native_decide)

theorem flapperUint48Mask_clean_of_canonical {w : UInt256}
    (h : w.toNat < EVM.twoPow 48) :
    UInt256.land w flapperUint48Mask = w := by
  apply u256_inj
  change Nat.land w.toNat (2 ^ 48 - 1) % UInt256.size = w.toNat
  have h' : w.toNat < 2 ^ 48 := by
    simpa [EVM.twoPow] using h
  rw [nat_land_mask_eq_mod]
  rw [Nat.mod_eq_of_lt h']
  exact Nat.mod_eq_of_lt (lt_trans h (by native_decide))

theorem flapperUint48Mask_clean (w : UInt256) :
    UInt256.land (UInt256.land w flapperUint48Mask) flapperUint48Mask =
      UInt256.land w flapperUint48Mask :=
  flapperUint48Mask_clean_of_canonical (flapperUint48Masked_lt w)

theorem uint48ReturnEncoding (v : UInt256) (h48 : v.toNat < EVM.twoPow 48) :
    encodeReturnValue? (.elem (.int (.uint ⟨48, by decide⟩))) (.int (Int.ofNat v.toNat)) =
      some (UInt256.toByteArray v) := by
  have hword : EVM.word v.toNat = v := by
    show UInt256.ofNat v.toNat = v
    exact u256_ofNat_toNat v
  refine scalarReturnEncoding (t := (.int (.uint ⟨48, by decide⟩))) (w := v) rfl ?_ ?_
  · simp only [abiTupleHeadSize?, staticABIEncodedSize?, isDynamicABIType, bind, Option.bind]
    decide
  · simp [encodeABIValue?, encodeABIWord?, hword, h48]

theorem flapperStorageLocLoad_address_offset0 (evm : EVM.State) (slot : UInt256) :
    storageLocLoad evm (addrLoc slot) =
      .address (AccountAddress.ofNat
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)
          solcAddrMask).toNat) := by
  simpa [addrLoc, addressOffset0Loc] using storageLocLoad_address_offset0 evm slot

theorem flapperStorageLocLoad_uint256 (evm : EVM.State) (slot : UInt256) :
    storageLocLoad evm (wordLoc slot) =
      .int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot).toNat) := by
  simpa [wordLoc, uint256Loc] using storageLocLoad_uint256 evm slot

theorem flapperStorageLocLoad_uint48_offset0 (evm : EVM.State) (slot : UInt256) :
    storageLocLoad evm (uint48Loc slot ⟨0, by decide⟩ (by decide)) =
      .int (Int.ofNat (UInt256.land
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)
        flapperUint48Mask).toNat) := by
  simpa [uint48Loc, flapperUint48Mask] using
    storageLocLoad_uint_offset0 evm slot ⟨6, by decide⟩ ⟨48, by decide⟩
      (hbound := by decide) (by decide)

theorem flapperStorageLocLoad_uint48_offset6 (evm : EVM.State) (slot : UInt256) :
    storageLocLoad evm (uint48Loc slot ⟨6, by decide⟩ (by decide)) =
      .int (Int.ofNat (UInt256.land
        (UInt256.div (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)
          (UInt256.ofNat (256 ^ 6)))
        flapperUint48Mask).toNat) := by
  simpa [uint48Loc, flapperUint48Mask] using
    storageLocLoad_uint_offset evm slot ⟨6, by decide⟩ ⟨6, by decide⟩ ⟨48, by decide⟩
      (hbound := by decide) (by decide) (by decide)

theorem flapperStorageLocLoad_uint48_offset20 (evm : EVM.State) (slot : UInt256) :
    storageLocLoad evm (uint48Loc slot ⟨20, by decide⟩ (by decide)) =
      .int (Int.ofNat (UInt256.land
        (UInt256.div (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)
          (UInt256.ofNat (256 ^ 20)))
        flapperUint48Mask).toNat) := by
  simpa [uint48Loc, flapperUint48Mask] using
    storageLocLoad_uint_offset evm slot ⟨20, by decide⟩ ⟨6, by decide⟩ ⟨48, by decide⟩
      (hbound := by decide) (by decide) (by decide)

theorem flapperStorageLocLoad_uint48_offset26 (evm : EVM.State) (slot : UInt256) :
    storageLocLoad evm (uint48Loc slot ⟨26, by decide⟩ (by decide)) =
      .int (Int.ofNat (UInt256.land
        (UInt256.div (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)
          (UInt256.ofNat (256 ^ 26)))
        flapperUint48Mask).toNat) := by
  simpa [uint48Loc, flapperUint48Mask] using
    storageLocLoad_uint_offset evm slot ⟨26, by decide⟩ ⟨6, by decide⟩ ⟨48, by decide⟩
      (hbound := by decide) (by decide) (by decide)

theorem flapperAddressGetterBodyReturns (evm : EVM.State) (locals : Store)
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
      exact congrArg EvalResult.ok (flapperStorageLocLoad_address_offset0 evm slot))

theorem flapperUint48GetterBodyReturns_offset0 (evm : EVM.State) (locals : Store)
    {ref : StorageRef} {er : EvaledStorageRef} {slot : UInt256}
    (h : evm.executionEnv.weiValue = ⟨0⟩)
    (hbase : locals.get? ref.base = none)
    (her : evalStorageRef config { contract := contract, locals := locals } evm ref = .ok er)
    (hty : storageTypeAt? contract.storage er = some (.elem (.int uint48Int)))
    (hloc :
      config.storage.layout er =
        fun _ => some (uint48Loc slot ⟨0, by decide⟩ (by decide))) :
    ExecTransitionBody config contract evm locals (nonpayable ++ [ .return [(.storage ref)] ])
      (.returned { contract := contract, locals := locals } evm
        (some [(.int (Int.ofNat
          (flapperUint48Offset0Word slot evm.accountMap evm.executionEnv).toNat))])) := by
  simpa [nonpayable, flapperUint48Offset0Word, flapperSlotWord] using
    nonpayableReturnExprBodyReturns (cfg := config) (contract := contract) h (by
      rw [evalExpr_storage_scalar (hbase := hbase) (her := her) (hty := hty) (hloc := hloc)]
      exact congrArg EvalResult.ok (flapperStorageLocLoad_uint48_offset0 evm slot))

theorem flapperUint48GetterBodyReturns_offset6 (evm : EVM.State) (locals : Store)
    {ref : StorageRef} {er : EvaledStorageRef} {slot : UInt256}
    (h : evm.executionEnv.weiValue = ⟨0⟩)
    (hbase : locals.get? ref.base = none)
    (her : evalStorageRef config { contract := contract, locals := locals } evm ref = .ok er)
    (hty : storageTypeAt? contract.storage er = some (.elem (.int uint48Int)))
    (hloc :
      config.storage.layout er =
        fun _ => some (uint48Loc slot ⟨6, by decide⟩ (by decide))) :
    ExecTransitionBody config contract evm locals (nonpayable ++ [ .return [(.storage ref)] ])
      (.returned { contract := contract, locals := locals } evm
        (some [(.int (Int.ofNat
          (flapperUint48Offset6Word slot evm.accountMap evm.executionEnv).toNat))])) := by
  simpa [nonpayable, flapperUint48Offset6Word, flapperSlotWord] using
    nonpayableReturnExprBodyReturns (cfg := config) (contract := contract) h (by
      rw [evalExpr_storage_scalar (hbase := hbase) (her := her) (hty := hty) (hloc := hloc)]
      have hload :
          storageLocLoad evm (uint48Loc slot ⟨6, by decide⟩ (by decide)) =
            .int (Int.ofNat (UInt256.land flapperUint48Mask
              (UInt256.div (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)
                (UInt256.ofNat (256 ^ 6)))).toNat) := by
        rw [flapperStorageLocLoad_uint48_offset6]
        rw [u256_land_comm
          (UInt256.div (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)
            (UInt256.ofNat (256 ^ 6)))
          flapperUint48Mask]
      exact congrArg EvalResult.ok hload)

theorem flapperUint256GetterBodyReturns (evm : EVM.State) (locals : Store)
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
      exact congrArg EvalResult.ok (flapperStorageLocLoad_uint256 evm slot))

theorem flapperUint256GetterBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    {transition : TransitionDecl} {entry returnPc routine slot : UInt256}
    (hcode : I.code = flapperBytecode)
    (hdispatch : dispatchMsg contract I.calldata = some transition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (transition.params.map Param.name)
        (transitionSignature transition).paramTypes I.calldata = some ∅)
    (hreach : ∃ k C, RD flapperBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) entry [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hentry : solcGetterEntryWf flapperBytecode entry returnPc routine)
    (hgetter : solcWordSlotGetterWf flapperBytecode routine slot)
    (hroutine : (D_J flapperBytecode 0).contains routine = true)
    (hreturnJd : (D_J flapperBytecode 0).contains returnPc = true)
    (hretmem : solcReturnWordFromMemWf flapperBytecode returnPc)
    (hreturn : transition.returnType = [uint256])
    (hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅ transition.body
        (.returned { contract := contract, locals := ∅ }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.int (Int.ofNat (flapperSlotWord slot σ_solm I).toNat))]))) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hword : flapperSlotWord slot σ_evm I = flapperSlotWord slot σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner slot ⟨0⟩
  have hval :
      some [Value.int (Int.ofNat (flapperSlotWord slot σ_solm I).toNat)] =
        some [Value.int (Int.ofNat (flapperSlotWord slot σ_evm I).toNat)] := by
    rw [hword]
  have henc :
      returnEquiv (UInt256.toByteArray (flapperSlotWord slot σ_evm I))
        (some [(.int (Int.ofNat (flapperSlotWord slot σ_evm I).toNat))])
        transition.returnType := by
      rw [hreturn]
      exact returnEquiv_of_encode
        (by simpa [uint256] using uint256ReturnEncoding (flapperSlotWord slot σ_evm I))
  have hret := RD.solcWordGetterExternal (code := flapperBytecode) (g := Sat256.ofUInt256 g)
    (returnPc := returnPc) (entry := entry) (routine := routine) (slot := slot)
    hreach hentry hgetter hroutine hreturnJd hretmem
  have hret' :
      RDret flapperBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) (cA, σ_evm)
        (UInt256.toByteArray (flapperSlotWord slot σ_evm I)) := by
    simpa [flapperSlotWord] using hret
  exact hret'.reEquivExecutionTransport hcode hdispatch hdecode hbody hval hAccounts henc

@[reducible] def flapperUint48Offset0SlotGetterWf
    (code : ByteArray) (pc slot : UInt256) : Prop :=
  let p1 := pc + ⟨1⟩
  let p3 := p1 + UInt256.ofNat 2
  let p4 := p3 + ⟨1⟩
  let p11 := p4 + UInt256.ofNat 7
  let p12 := p11 + ⟨1⟩
  let p13 := p12 + ⟨1⟩
  decode code pc = some (.JUMPDEST, .none)
  ∧ decode code p1 = some (.Push .PUSH1, some (slot, 1))
  ∧ decode code p3 = some (.SLOAD, .none)
  ∧ decode code p4 = some (.Push .PUSH6, some (flapperUint48Mask, 6))
  ∧ decode code p11 = some (.AND, .none)
  ∧ decode code p12 = some (.DUP2, .none)
  ∧ decode code p13 = some (.JUMP, .none)

@[reducible] def flapperUint48Offset6SlotGetterWf
    (code : ByteArray) (pc slot : UInt256) : Prop :=
  let p1 := pc + ⟨1⟩
  let p3 := p1 + UInt256.ofNat 2
  let p4 := p3 + ⟨1⟩
  let p6 := p4 + UInt256.ofNat 2
  let p8 := p6 + UInt256.ofNat 2
  let p9 := p8 + ⟨1⟩
  let p10 := p9 + ⟨1⟩
  let p11 := p10 + ⟨1⟩
  let p18 := p11 + UInt256.ofNat 7
  let p19 := p18 + ⟨1⟩
  let p20 := p19 + ⟨1⟩
  decode code pc = some (.JUMPDEST, .none)
  ∧ decode code p1 = some (.Push .PUSH1, some (slot, 1))
  ∧ decode code p3 = some (.SLOAD, .none)
  ∧ decode code p4 = some (.Push .PUSH1, some (⟨1⟩, 1))
  ∧ decode code p6 = some (.Push .PUSH1, some (⟨48⟩, 1))
  ∧ decode code p8 = some (.SHL, .none)
  ∧ decode code p9 = some (.SWAP1, .none)
  ∧ decode code p10 = some (.DIV, .none)
  ∧ decode code p11 = some (.Push .PUSH6, some (flapperUint48Mask, 6))
  ∧ decode code p18 = some (.AND, .none)
  ∧ decode code p19 = some (.DUP2, .none)
  ∧ decode code p20 = some (.JUMP, .none)

theorem RD.flapperUint48Offset0SlotGetter {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {pc slot ret : UInt256} {R : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD code ee g s0 pc (ret :: R) mem aw rdata (cA, σ) k C)
    (hwf : flapperUint48Offset0SlotGetterWf code pc slot)
    (hret : (D_J code 0).contains ret = true)
    (hov : R.length + 4 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ret
      (UInt256.land (solcSlotWord σ ee slot) flapperUint48Mask :: ret :: R) mem aw rdata
      (cA, σ) k' C' := by
  rcases hwf with ⟨hd0, hd1, hd3, hd4, hd11, hd12, hd13⟩
  have rd1 := h.jumpdest hd0 (by simp only [List.length_cons]; omega)
  have rd3 := rd1.push1 slot hd1 (by simp only [List.length_cons]; omega)
  obtain ⟨_, _, rd4⟩ := rd3.sload hd3 (by simp only [List.length_cons]; omega)
  have rd11 := rd4.pushConst flapperUint48Mask (width := 6) (op := .PUSH6)
    (by decide) hd4 (by simp only [List.length_cons]; omega)
  have rd12 := rd11.and hd11 (by simp only [List.length_cons]; omega)
  have rd13 := rd12.dup2 hd12 (by omega)
  have rdRet := rd13.jump hd13 hret (by simp only [List.length_cons]; omega)
  exact ⟨_, _, by simpa [u256_land_comm flapperUint48Mask (solcSlotWord σ ee slot)] using rdRet⟩

theorem RD.flapperUint48Offset6SlotGetter {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {pc slot ret : UInt256} {R : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD code ee g s0 pc (ret :: R) mem aw rdata (cA, σ) k C)
    (hwf : flapperUint48Offset6SlotGetterWf code pc slot)
    (hret : (D_J code 0).contains ret = true)
    (hov : R.length + 7 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ret
      (UInt256.land flapperUint48Mask
        (UInt256.div (solcSlotWord σ ee slot) (UInt256.ofNat (256 ^ 6))) :: ret :: R)
      mem aw rdata (cA, σ) k' C' := by
  rcases hwf with
    ⟨hd0, hd1, hd3, hd4, hd6, hd8, hd9, hd10, hd11, hd18, hd19, hd20⟩
  have rd1 := h.jumpdest hd0 (by simp only [List.length_cons]; omega)
  have rd3 := rd1.push1 slot hd1 (by simp only [List.length_cons]; omega)
  obtain ⟨_, _, rd4⟩ := rd3.sload hd3 (by simp only [List.length_cons]; omega)
  have rd6 := rd4.push1 ⟨1⟩ hd4 (by simp only [List.length_cons]; omega)
  have rd8 := rd6.push1 ⟨48⟩ hd6 (by simp only [List.length_cons]; omega)
  have rd9 := rd8.shl hd8 (by simp only [List.length_cons]; omega)
  have rd10 := rd9.swap1 hd9 (by simp only [List.length_cons]; omega)
  have rd11 := rd10.div hd10 (by simp only [List.length_cons]; omega)
  have rd18 := rd11.pushConst flapperUint48Mask (width := 6) (op := .PUSH6)
    (by decide) hd11 (by simp only [List.length_cons]; omega)
  have rd19 := rd18.and hd18 (by simp only [List.length_cons]; omega)
  have rd20 := rd19.dup2 hd19 (by omega)
  have rdRet := rd20.jump hd20 hret (by simp only [List.length_cons]; omega)
  have hshift :
      UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨48⟩ = UInt256.ofNat (256 ^ 6) := by
    native_decide
  exact ⟨_, _, by simpa [hshift, solcSlotWord] using rdRet⟩

@[reducible] def flapperReturnUint48FromMemWf (code : ByteArray) (pc : UInt256) : Prop :=
  decode code pc = some (.JUMPDEST, .none)
  ∧ decode code (pc + ⟨1⟩) = some (.Push .PUSH1, some (⟨64⟩, 1))
  ∧ decode code (pc + ⟨1⟩ + UInt256.ofNat 2) = some (.DUP1, .none)
  ∧ decode code (pc + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩) = some (.MLOAD, .none)
  ∧ decode code (pc + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩) =
      some (.Push .PUSH6, some (flapperUint48Mask, 6))
  ∧ decode code (pc + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 7) =
      some (.SWAP1, .none)
  ∧ decode code
      (pc + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 7 + ⟨1⟩) =
      some (.SWAP3, .none)
  ∧ decode code
      (pc + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 7 + ⟨1⟩ +
        ⟨1⟩) =
      some (.AND, .none)
  ∧ decode code
      (pc + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 7 + ⟨1⟩ +
        ⟨1⟩ + ⟨1⟩) =
      some (.DUP3, .none)
  ∧ decode code
      (pc + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 7 + ⟨1⟩ +
        ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
      some (.MSTORE, .none)
  ∧ decode code
      (pc + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 7 + ⟨1⟩ +
        ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
      some (.MLOAD, .none)
  ∧ decode code
      (pc + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 7 + ⟨1⟩ +
        ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
      some (.SWAP1, .none)
  ∧ decode code
      (pc + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 7 + ⟨1⟩ +
        ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
      some (.DUP2, .none)
  ∧ decode code
      (pc + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 7 + ⟨1⟩ +
        ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
      some (.SWAP1, .none)
  ∧ decode code
      (pc + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 7 + ⟨1⟩ +
        ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
      some (.SUB, .none)
  ∧ decode code
      (pc + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 7 + ⟨1⟩ +
        ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
      some (.Push .PUSH1, some (⟨32⟩, 1))
  ∧ decode code
      (pc + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 7 + ⟨1⟩ +
        ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
        UInt256.ofNat 2) =
      some (.ADD, .none)
  ∧ decode code
      (pc + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 7 + ⟨1⟩ +
        ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
        UInt256.ofNat 2 + ⟨1⟩) =
      some (.SWAP1, .none)
  ∧ decode code
      (pc + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 7 + ⟨1⟩ +
        ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
        UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩) =
      some (.RETURN, .none)

theorem RD.flapperReturnUint48FromMem {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {pc val ret : UInt256} {R : List UInt256}
    {mem memout rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD code ee g s0 pc (val :: ret :: R) mem (UInt256.ofNat 3) rdata acc k C)
    (hwf : flapperReturnUint48FromMemWf code pc)
    (hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 3 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32)))
        = ⟨128⟩)
    (hmemout :
      (UInt256.toByteArray (UInt256.land val flapperUint48Mask)).write 0 mem 128 32 =
        memout)
    (hmemoutLoad64 :
      (if (⟨64⟩ : UInt256).toNat ≥ memout.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 5 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (memout.readWithPadding (⟨64⟩ : UInt256).toNat 32)))
        = ⟨128⟩)
    (hread128 :
      memout.readWithPadding 128 32 =
        UInt256.toByteArray (UInt256.land val flapperUint48Mask))
    (hov : R.length + 9 ≤ 1024) :
    RDret code g s0 acc (UInt256.toByteArray (UInt256.land val flapperUint48Mask)) := by
  rcases hwf with
    ⟨hd0, hd1, hd3, hd4, hd5, hd12, hd13, hd14, hd15, hd16, hd17, hd18, hd19,
      hd20, hd21, hd22, hd24, hd25, hd26⟩
  have rd4 := evm_run h with [
    raw jumpdest hd0 (by evm_ov),
    raw push1 ⟨64⟩ hd1 (by evm_ov),
    raw dup1 hd3 (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) hd4 mem_cost hmload64 (by decide)
      (by evm_ov)]
  have rd12 := rd4.pushConst flapperUint48Mask (width := 6) (op := .PUSH6)
    (by decide) hd5 (by evm_ov)
  have rd16 := evm_run rd12 with [
    raw swap1 hd12 (by evm_ov),
    raw swap3 hd13 (by evm_ov),
    raw and hd14 (by evm_ov),
    raw dup3 hd15 (by evm_ov)]
  have rd17 := rd16.mstore 6 memout (UInt256.ofNat 5) hd16 mem_cost
    (by
      rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide]
      exact hmemout)
    (by decide) (by evm_ov)
  exact evm_run rd17 with [
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) hd17 mem_cost hmemoutLoad64 (by decide)
      (by evm_ov),
    raw swap1 hd18 (by evm_ov),
    raw dup2 hd19 (by evm_ov),
    raw swap1 hd20 (by evm_ov),
    raw sub hd21 (by evm_ov),
    raw push1 ⟨32⟩ hd22 (by evm_ov),
    raw add hd24 (by evm_ov),
    raw swap1 hd25 (by evm_ov),
    raw ret 0 (UInt256.toByteArray (UInt256.land val flapperUint48Mask)) hd26 mem_cost
      (by
        rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide,
          show ((⟨32⟩ : UInt256) + UInt256.sub (⟨128⟩ : UInt256) ⟨128⟩).toNat = 32
            from by decide]
        exact hread128)
      (by evm_ov)]

theorem RD.flapperUint48Offset0GetterExternal {code : ByteArray} {cA gh bl σ σ₀ A I}
    {g : Sat256} {sel entry returnPc routine slot : UInt256}
    (hreach : ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I) entry [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hentry : solcGetterEntryWf code entry returnPc routine)
    (hgetter : flapperUint48Offset0SlotGetterWf code routine slot)
    (hroutine : (D_J code 0).contains routine = true)
    (hreturnJd : (D_J code 0).contains returnPc = true)
    (hreturn : flapperReturnUint48FromMemWf code returnPc) :
    RDret code g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (flapperUint48Offset0Word slot σ I)) := by
  obtain ⟨_, _, rdRoutine⟩ := RD.solcGetterThunk hreach hentry hroutine
  obtain ⟨_, _, rdReturn⟩ :=
    RD.flapperUint48Offset0SlotGetter (R := [sel]) rdRoutine hgetter hreturnJd
      (by simp only [List.length_singleton]; omega)
  have hret := RD.flapperReturnUint48FromMem rdReturn hreturn
    solcFreePtrMem_mload64
    (by rfl)
    (solcReturnMem_mload64
      (UInt256.land (flapperUint48Offset0Word slot σ I) flapperUint48Mask))
    (solcReturnMem_read128
      (UInt256.land (flapperUint48Offset0Word slot σ I) flapperUint48Mask))
    (by simp only [List.length_singleton]; omega)
  have hclean' :
      UInt256.land (UInt256.land (solcSlotWord σ I slot) flapperUint48Mask)
          flapperUint48Mask =
        UInt256.land (solcSlotWord σ I slot) flapperUint48Mask :=
    flapperUint48Mask_clean (solcSlotWord σ I slot)
  simpa [flapperUint48Offset0Word, flapperSlotWord, hclean'] using hret

theorem RD.flapperUint48Offset6GetterExternal {code : ByteArray} {cA gh bl σ σ₀ A I}
    {g : Sat256} {sel entry returnPc routine slot : UInt256}
    (hreach : ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I) entry [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hentry : solcGetterEntryWf code entry returnPc routine)
    (hgetter : flapperUint48Offset6SlotGetterWf code routine slot)
    (hroutine : (D_J code 0).contains routine = true)
    (hreturnJd : (D_J code 0).contains returnPc = true)
    (hreturn : flapperReturnUint48FromMemWf code returnPc) :
    RDret code g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (flapperUint48Offset6Word slot σ I)) := by
  obtain ⟨_, _, rdRoutine⟩ := RD.solcGetterThunk hreach hentry hroutine
  obtain ⟨_, _, rdReturn⟩ :=
    RD.flapperUint48Offset6SlotGetter (R := [sel]) rdRoutine hgetter hreturnJd
      (by simp only [List.length_singleton]; omega)
  have hret := RD.flapperReturnUint48FromMem rdReturn hreturn
    solcFreePtrMem_mload64
    (by rfl)
    (solcReturnMem_mload64
      (UInt256.land (flapperUint48Offset6Word slot σ I) flapperUint48Mask))
    (solcReturnMem_read128
      (UInt256.land (flapperUint48Offset6Word slot σ I) flapperUint48Mask))
    (by simp only [List.length_singleton]; omega)
  have hclean' :
      UInt256.land (UInt256.land flapperUint48Mask
          (UInt256.div (solcSlotWord σ I slot) (UInt256.ofNat (256 ^ 6))))
          flapperUint48Mask =
        UInt256.land flapperUint48Mask
          (UInt256.div (solcSlotWord σ I slot) (UInt256.ofNat (256 ^ 6))) := by
    rw [u256_land_comm flapperUint48Mask
      (UInt256.div (solcSlotWord σ I slot) (UInt256.ofNat (256 ^ 6)))]
    exact flapperUint48Mask_clean
      (UInt256.div (solcSlotWord σ I slot) (UInt256.ofNat (256 ^ 6)))
  rw [hclean'] at hret
  simpa [flapperUint48Offset6Word, flapperSlotWord] using hret

theorem flapperUint48Offset0GetterBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    {transition : TransitionDecl} {entry returnPc routine slot : UInt256}
    (hcode : I.code = flapperBytecode)
    (hdispatch : dispatchMsg contract I.calldata = some transition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (transition.params.map Param.name)
        (transitionSignature transition).paramTypes I.calldata = some ∅)
    (hreach : ∃ k C, RD flapperBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) entry [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hentry : solcGetterEntryWf flapperBytecode entry returnPc routine)
    (hgetter : flapperUint48Offset0SlotGetterWf flapperBytecode routine slot)
    (hroutine : (D_J flapperBytecode 0).contains routine = true)
    (hreturnJd : (D_J flapperBytecode 0).contains returnPc = true)
    (hretmem : flapperReturnUint48FromMemWf flapperBytecode returnPc)
    (hreturn : transition.returnType = [uint48])
    (hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅ transition.body
        (.returned { contract := contract, locals := ∅ }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.int
            (Int.ofNat (flapperUint48Offset0Word slot σ_solm I).toNat))]))) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hslot : flapperSlotWord slot σ_evm I = flapperSlotWord slot σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner slot ⟨0⟩
  have hslot' : solcSlotWord σ_solm I slot = solcSlotWord σ_evm I slot := by
    simpa [flapperSlotWord] using hslot.symm
  have hword :
      flapperUint48Offset0Word slot σ_solm I = flapperUint48Offset0Word slot σ_evm I := by
    simp [flapperUint48Offset0Word, flapperSlotWord, hslot']
  have hval :
      some [Value.int (Int.ofNat (flapperUint48Offset0Word slot σ_solm I).toNat)] =
        some [Value.int (Int.ofNat (flapperUint48Offset0Word slot σ_evm I).toNat)] := by
    rw [hword]
  have henc :
      returnEquiv (UInt256.toByteArray (flapperUint48Offset0Word slot σ_evm I))
        (some [(.int (Int.ofNat (flapperUint48Offset0Word slot σ_evm I).toNat))])
        transition.returnType := by
    rw [hreturn]
    exact returnEquiv_of_encode
      (by
        simpa [uint48] using
          uint48ReturnEncoding (flapperUint48Offset0Word slot σ_evm I)
            (flapperUint48Masked_lt (flapperSlotWord slot σ_evm I)))
  have hret := RD.flapperUint48Offset0GetterExternal (code := flapperBytecode)
    (g := Sat256.ofUInt256 g) (returnPc := returnPc) (entry := entry)
    (routine := routine) (slot := slot) hreach hentry hgetter hroutine hreturnJd hretmem
  exact hret.reEquivExecutionTransport hcode hdispatch hdecode hbody hval hAccounts henc

theorem flapperUint48Offset6GetterBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    {transition : TransitionDecl} {entry returnPc routine slot : UInt256}
    (hcode : I.code = flapperBytecode)
    (hdispatch : dispatchMsg contract I.calldata = some transition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (transition.params.map Param.name)
        (transitionSignature transition).paramTypes I.calldata = some ∅)
    (hreach : ∃ k C, RD flapperBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) entry [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hentry : solcGetterEntryWf flapperBytecode entry returnPc routine)
    (hgetter : flapperUint48Offset6SlotGetterWf flapperBytecode routine slot)
    (hroutine : (D_J flapperBytecode 0).contains routine = true)
    (hreturnJd : (D_J flapperBytecode 0).contains returnPc = true)
    (hretmem : flapperReturnUint48FromMemWf flapperBytecode returnPc)
    (hreturn : transition.returnType = [uint48])
    (hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅ transition.body
        (.returned { contract := contract, locals := ∅ }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.int
            (Int.ofNat (flapperUint48Offset6Word slot σ_solm I).toNat))]))) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hslot : flapperSlotWord slot σ_evm I = flapperSlotWord slot σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner slot ⟨0⟩
  have hslot' : solcSlotWord σ_solm I slot = solcSlotWord σ_evm I slot := by
    simpa [flapperSlotWord] using hslot.symm
  have hword :
      flapperUint48Offset6Word slot σ_solm I = flapperUint48Offset6Word slot σ_evm I := by
    simp [flapperUint48Offset6Word, flapperSlotWord, hslot']
  have hval :
      some [Value.int (Int.ofNat (flapperUint48Offset6Word slot σ_solm I).toNat)] =
        some [Value.int (Int.ofNat (flapperUint48Offset6Word slot σ_evm I).toNat)] := by
    rw [hword]
  have henc :
      returnEquiv (UInt256.toByteArray (flapperUint48Offset6Word slot σ_evm I))
        (some [(.int (Int.ofNat (flapperUint48Offset6Word slot σ_evm I).toNat))])
        transition.returnType := by
    have hlt :
        (flapperUint48Offset6Word slot σ_evm I).toNat < EVM.twoPow 48 := by
      rw [flapperUint48Offset6Word]
      rw [u256_land_comm flapperUint48Mask
        (UInt256.div (flapperSlotWord slot σ_evm I) (UInt256.ofNat (256 ^ 6)))]
      exact flapperUint48Masked_lt
        (UInt256.div (flapperSlotWord slot σ_evm I) (UInt256.ofNat (256 ^ 6)))
    rw [hreturn]
    exact returnEquiv_of_encode
      (by
        simpa [uint48] using
          uint48ReturnEncoding (flapperUint48Offset6Word slot σ_evm I) hlt)
  have hret := RD.flapperUint48Offset6GetterExternal (code := flapperBytecode)
    (g := Sat256.ofUInt256 g) (returnPc := returnPc) (entry := entry)
    (routine := routine) (slot := slot) hreach hentry hgetter hroutine hreturnJd hretmem
  exact hret.reEquivExecutionTransport hcode hdispatch hdecode hbody hval hAccounts henc

theorem flapperAddressGetterBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    {transition : TransitionDecl} {entry returnPc routine slot : UInt256}
    (hcode : I.code = flapperBytecode)
    (hdispatch : dispatchMsg contract I.calldata = some transition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (transition.params.map Param.name)
        (transitionSignature transition).paramTypes I.calldata = some ∅)
    (hreach : ∃ k C, RD flapperBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) entry [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hentry : solcGetterEntryWf flapperBytecode entry returnPc routine)
    (hgetter : solcAddressSlotGetterWf flapperBytecode routine slot)
    (hroutine : (D_J flapperBytecode 0).contains routine = true)
    (hreturnJd : (D_J flapperBytecode 0).contains returnPc = true)
    (hretmem : solcReturnAddressFromMemWf flapperBytecode returnPc)
    (hreturn : transition.returnType = [addr])
    (hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅ transition.body
        (.returned { contract := contract, locals := ∅ }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.address (AccountAddress.ofNat
            (flapperAddressReturnWord slot σ_solm I).toNat))]))) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hword : flapperSlotWord slot σ_evm I = flapperSlotWord slot σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner slot ⟨0⟩
  have hval :
      some [Value.address (AccountAddress.ofNat (flapperAddressReturnWord slot σ_solm I).toNat)] =
        some [Value.address (AccountAddress.ofNat (flapperAddressReturnWord slot σ_evm I).toNat)] := by
    have hslot : flapperSlotWord slot σ_solm I = flapperSlotWord slot σ_evm I := hword.symm
    simp [flapperAddressReturnWord, hslot]
  have henc :
      returnEquiv (UInt256.toByteArray (flapperAddressReturnWord slot σ_evm I))
        (some [(.address (AccountAddress.ofNat (flapperAddressReturnWord slot σ_evm I).toNat))])
        transition.returnType := by
    rw [hreturn]
    simpa [flapperAddressReturnWord] using
      (returnEquiv_of_encode
        (solcAddressReturnEncoding (addrTy := addr) rfl (flapperSlotWord slot σ_evm I)))
  have hret := RD.solcAddressGetterExternal (code := flapperBytecode) (g := Sat256.ofUInt256 g)
    (returnPc := returnPc) (entry := entry) (routine := routine) (slot := slot)
    hreach hentry hgetter hroutine hreturnJd hretmem
  have hret' :
      RDret flapperBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) (cA, σ_evm)
        (UInt256.toByteArray (flapperAddressReturnWord slot σ_evm I)) := by
    simpa [flapperAddressReturnWord, flapperSlotWord] using hret
  exact hret'.reEquivExecutionTransport hcode hdispatch hdecode hbody hval hAccounts henc

@[reducible] def solcZeroSlotMappingGetterWf (code : ByteArray) (pc : UInt256) : Prop :=
  let p1 := pc + ⟨1⟩
  let p3 := p1 + UInt256.ofNat 2
  let p5 := p3 + UInt256.ofNat 2
  let p6 := p5 + ⟨1⟩
  let p7 := p6 + ⟨1⟩
  let p8 := p7 + ⟨1⟩
  let p9 := p8 + ⟨1⟩
  let p10 := p9 + ⟨1⟩
  let p11 := p10 + ⟨1⟩
  let p13 := p11 + UInt256.ofNat 2
  let p14 := p13 + ⟨1⟩
  let p15 := p14 + ⟨1⟩
  let p16 := p15 + ⟨1⟩
  let p17 := p16 + ⟨1⟩
  decode code pc = some (.JUMPDEST, .none)
  ∧ decode code p1 = some (.Push .PUSH1, some (⟨0⟩, 1))
  ∧ decode code p3 = some (.Push .PUSH1, some (⟨32⟩, 1))
  ∧ decode code p5 = some (.DUP2, .none)
  ∧ decode code p6 = some (.SWAP1, .none)
  ∧ decode code p7 = some (.MSTORE, .none)
  ∧ decode code p8 = some (.SWAP1, .none)
  ∧ decode code p9 = some (.DUP2, .none)
  ∧ decode code p10 = some (.MSTORE, .none)
  ∧ decode code p11 = some (.Push .PUSH1, some (⟨64⟩, 1))
  ∧ decode code p13 = some (.SWAP1, .none)
  ∧ decode code p14 = some (.KECCAK256, .none)
  ∧ decode code p15 = some (.SLOAD, .none)
  ∧ decode code p16 = some (.DUP2, .none)
  ∧ decode code p17 = some (.JUMP, .none)

theorem RD.solcZeroSlotMappingGetter {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {pc key ret : UInt256} {R : List UInt256}
    {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD code ee g s0 pc (key :: ret :: R)
        solcFreePtrMem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hwf : solcZeroSlotMappingGetterWf code pc)
    (hret : (D_J code 0).contains ret = true)
    (hov : R.length + 5 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ret
      (solcSlotWord σ ee (solcMappingSlot ⟨0⟩ key) :: ret :: R)
      (solcMappingHashMem ⟨0⟩ key) (UInt256.ofNat 3) rdata (cA, σ) k' C' := by
  rcases hwf with
    ⟨hd0, hd1, hd3, hd5, hd6, hd7, hd8, hd9, hd10, hd11, hd13, hd14, hd15,
      hd16, hd17⟩
  have rd1 := h.jumpdest hd0 (by simp only [List.length_cons]; omega)
  have rd3 := rd1.push1 ⟨0⟩ hd1 (by evm_ov)
  have rd5 := rd3.push1 ⟨32⟩ hd3 (by evm_ov)
  have rd6 := rd5.dup2 hd5 (by evm_ov)
  have rd7 := rd6.swap1 hd6 (by evm_ov)
  have rd8 := rd7.mstore 0 (solcMappingBaseSlotMem ⟨0⟩)
    (UInt256.ofNat 3) hd7 mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd9 := rd8.swap1 hd8 (by evm_ov)
  have rd10 := rd9.dup2 hd9 (by evm_ov)
  have rd11 := rd10.mstore 0 (solcMappingHashMem ⟨0⟩ key)
    (UInt256.ofNat 3) hd10 mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd13 := rd11.push1 ⟨64⟩ hd11 (by evm_ov)
  have rd14 := rd13.swap1 hd13 (by evm_ov)
  have hslot := solcMappingKeccakSlot ⟨0⟩ key
  have rd15 := rd14.keccak256 0 (solcMappingSlot ⟨0⟩ key)
    (UInt256.ofNat 3) hd14 mem_cost
    (by simpa [show (⟨0⟩ : UInt256).toNat = 0 from by decide,
      show (⟨64⟩ : UInt256).toNat = 64 from by decide] using hslot)
    (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd16⟩ := rd15.sload hd15 (by evm_ov)
  have rd17 := rd16.dup2 hd16 (by evm_ov)
  exact ⟨_, _, rd17.jump hd17 hret (by evm_ov)⟩

end Benchmarks.Dss.Flapper
