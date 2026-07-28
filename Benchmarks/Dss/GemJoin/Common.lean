import Benchmarks.Dss.GemJoin.Bytecode
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
# Shared MakerDAO/Sky DSS GemJoin proof helpers

Contract-wide selector notation and constants for the optimized runtime.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.GemJoin

/-- The 4-byte selector word computed by `CALLDATALOAD(0); SHR 224`. -/
abbrev gemJoinSelWord (I : ExecutionEnv) : UInt256 :=
  UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩

/-- The 4-byte selector of `I`'s calldata equals `sel`. -/
abbrev selIs (I : ExecutionEnv) (sel : ByteArray) : Prop :=
  (sel == I.calldata.extract 0 4) = true

/-- Function selectors in `contract.transitions` order. -/
def gemJoinSelBytes : ℕ → ByteArray
  | 0 => ⟨#[0x69, 0x24, 0x50, 0x09]⟩ -- cage()
  | 1 => ⟨#[0xb3, 0xbc, 0xfa, 0x82]⟩ -- dec()
  | 2 => ⟨#[0x9c, 0x52, 0xa7, 0xf1]⟩ -- deny(address)
  | 3 => ⟨#[0xef, 0x69, 0x3b, 0xed]⟩ -- exit(address,uint256)
  | 4 => ⟨#[0x7b, 0xd2, 0xbe, 0xa7]⟩ -- gem()
  | 5 => ⟨#[0xc5, 0xce, 0x28, 0x1e]⟩ -- ilk()
  | 6 => ⟨#[0x3b, 0x4d, 0xa6, 0x9f]⟩ -- join(address,uint256)
  | 7 => ⟨#[0x95, 0x7a, 0xa5, 0x8c]⟩ -- live()
  | 8 => ⟨#[0x65, 0xfa, 0xe3, 0x5e]⟩ -- rely(address)
  | 9 => ⟨#[0x36, 0x56, 0x9e, 0x77]⟩ -- vat()
  | _ => ⟨#[0xbf, 0x35, 0x3d, 0xbb]⟩ -- wards(address)

def gemJoinSlotWord (slot : UInt256) (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  solcSlotWord σ I slot

abbrev gemJoinAddressReturnWord (slot : UInt256) (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.land (gemJoinSlotWord slot σ I) solcAddrMask

theorem gemJoinStorageLocLoad_address_offset0 (evm : EVM.State) (slot : UInt256) :
    storageLocLoad evm (addrLoc slot) =
      .address (AccountAddress.ofNat
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)
          solcAddrMask).toNat) := by
  simpa [addrLoc, addressOffset0Loc] using storageLocLoad_address_offset0 evm slot

theorem gemJoinStorageLocLoad_uint256 (evm : EVM.State) (slot : UInt256) :
    storageLocLoad evm (wordLoc slot) =
      .int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot).toNat) := by
  simpa [wordLoc, uint256Loc] using storageLocLoad_uint256 evm slot

theorem gemJoinStorageLocLoad_bytes32 (evm : EVM.State) (slot : UInt256) :
    storageLocLoad evm (bytes32Loc slot) =
      .fixedBytes bytes32Width
        (EVM.Word.toBytesBE (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)) := by
  simpa [bytes32Loc, Reasoning.Theory.bytes32Loc, bytes32Width] using
    Reasoning.Theory.storageLocLoad_bytes32 evm slot

/-! ## Auth helpers -/

abbrev relySourceWord (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat I.source.val

abbrev relyAuthKey (I : ExecutionEnv) : KeyValue :=
  .address I.source

def relyAuthStorageSlot (I : ExecutionEnv) : UInt256 :=
  wardsSlot (relyAuthKey I)

def relyAuthWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  gemJoinSlotWord (relyAuthStorageSlot I) σ I

abbrev relyAuthEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "wards", steps := [.mindex (relyAuthKey I)] }

theorem relyAuthStorageSlot_eq_mapSlot_source (I : ExecutionEnv) :
    relyAuthStorageSlot I = mapSlot (relySourceWord I) ⟨0⟩ := by
  unfold relyAuthStorageSlot wardsSlot relyAuthKey relySourceWord
  rw [keyValueToWord_address]

theorem uint256_toNat_eq_one {a : UInt256} (h : a.toNat = 1) : a = ⟨1⟩ := by
  apply u256_inj
  simpa using h

theorem evalStorageRef_auth_of_wards_none (evm : EVM.State) (I : ExecutionEnv)
    (locals : Store)
    (_hwards : locals.get? "wards" = none)
    (hsrc : evm.executionEnv.source = I.source) :
    evalStorageRef config { contract := contract, locals := locals } evm
      (wardsRef sender) = .ok (relyAuthEvaledRef I) := by
  simp [evalStorageRef, evalStorageRefStep, wardsRef, sender, envValue, relyAuthEvaledRef,
    relyAuthKey, hsrc, valueToKey?, EvalResult.bind, EvalResult.ofOption, bind, pure,
    evalExpr?]

theorem evalExpr_auth_true_of_wards_none (evm : EVM.State) (I : ExecutionEnv)
    (locals : Store)
    (hwards : locals.get? "wards" = none)
    (hsrc : evm.executionEnv.source = I.source)
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (relyAuthStorageSlot I) = ⟨1⟩) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) = .ok (.bool true) := by
  have hstorage :
      evalExpr? config { contract := contract, locals := locals } evm
        (.storage (wardsRef sender)) = .ok (.int 1) := by
    rw [evalExpr_storage_scalar_value
      (cfg := config)
      (solm := { contract := contract, locals := locals })
      (slot := wardsRef sender)
      (er := relyAuthEvaledRef I)
      (t := .int uint256Int)
      (loc := wordLoc (relyAuthStorageSlot I))
      (value := .int 1)
      (hbase := by simpa [wardsRef] using hwards)
      (her := evalStorageRef_auth_of_wards_none evm I locals hwards hsrc)
      (hty := by simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, uint256St])
      (hloc := by rfl)
      (hload := by
        simpa [hload] using gemJoinStorageLocLoad_uint256 evm (relyAuthStorageSlot I))]
  simp only [evalExpr?, hstorage, EvalResult.bind, bind, pure]
  rfl

theorem evalExpr_auth_false_of_wards_none (evm : EVM.State) (I : ExecutionEnv)
    (locals : Store)
    (hwards : locals.get? "wards" = none)
    (hsrc : evm.executionEnv.source = I.source)
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (relyAuthStorageSlot I) ≠ ⟨1⟩) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) = .ok (.bool false) := by
  have hstorage :
      evalExpr? config { contract := contract, locals := locals } evm
        (.storage (wardsRef sender)) =
          .ok (.int (Int.ofNat
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
              (relyAuthStorageSlot I)).toNat)) := by
    exact evalExpr_storage_scalar_value
      (cfg := config)
      (solm := { contract := contract, locals := locals })
      (slot := wardsRef sender)
      (er := relyAuthEvaledRef I)
      (t := .int uint256Int)
      (loc := wordLoc (relyAuthStorageSlot I))
      (hbase := by simpa [wardsRef] using hwards)
      (her := evalStorageRef_auth_of_wards_none evm I locals hwards hsrc)
      (hty := by simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, uint256St])
      (hloc := by rfl)
      (hload := by exact gemJoinStorageLocLoad_uint256 evm (relyAuthStorageSlot I))
  have hne :
      Value.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
            (relyAuthStorageSlot I)).toNat) ≠ Value.int 1 := by
    intro hbad
    rw [Value.int.injEq] at hbad
    apply hload
    exact uint256_toNat_eq_one (Int.ofNat.inj hbad)
  have hbeq :
      (Value.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
            (relyAuthStorageSlot I)).toNat) == Value.int 1) = false := by
    exact beq_eq_false_iff_ne.mpr hne
  simp only [evalExpr?, hstorage, EvalResult.bind, bind, pure]
  change evalBinaryOp? BinaryOp.eq
      (Value.int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (relyAuthStorageSlot I)).toNat))
      (Value.int 1) = .ok (.bool false)
  simp only [evalBinaryOp?]
  rw [hbeq]

noncomputable abbrev relyAuthHashMem (I : ExecutionEnv) : ByteArray :=
  twoWordHashMem (relySourceWord I) ⟨0⟩ solcFreePtrMem

theorem relyAuthHashMem_size (I : ExecutionEnv) :
    (relyAuthHashMem I).size = 96 := by
  exact twoWordHashMem_size_96 (relySourceWord I) ⟨0⟩ solcFreePtrMem_size

theorem relyAuthHashMem_read64 (I : ExecutionEnv) :
    (relyAuthHashMem I).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  exact twoWordHashMem_read64 (relySourceWord I) ⟨0⟩ solcFreePtrMem_size
    solcFreePtrMem_read64

/-! ## LOG2 reach helper -/

def stLog2 (s : State) (a b c d : UInt256) (t : List UInt256) : State :=
  { s with
    substate.logSeries := s.substate.logSeries.push
      ⟨s.executionEnv.codeOwner, #[c, d], s.machineState.memory.readWithPadding a.toNat b.toNat⟩
    machineState.stack := t
    machineState.activeWords :=
      UInt256.ofNat (MachineState.M s.machineState.activeWords.toNat a.toNat b.toNat)
    machineState.gasAvailable :=
      (s.machineState.gasAvailable.subNat (memoryExpansionCost s .LOG2)).subNat
        (GasConstants.Glog + GasConstants.Glogdata * b.toNat + 2 * GasConstants.Glogtopic)
    machineState.pc := s.machineState.pc + ⟨1⟩
    machineState.execLength := s.machineState.execLength + 1 }

theorem log2_xstep {s : State} {code : ByteArray} {pcv a b c d : UInt256}
    {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.LOG2, .none)) (hperm : s.executionEnv.perm = true)
    (hstk : s.machineState.stack = a :: b :: c :: d :: t) (hov : t.length ≤ 1024) :
    Xstep (D_J code 0) s =
      (if s.machineState.gasAvailable.toNat < memoryExpansionCost s .LOG2 +
            (GasConstants.Glog + GasConstants.Glogdata * b.toNat + 2 * GasConstants.Glogtopic)
       then .error .OutOfGass else .ok (stLog2 s a b c d t, .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.LOG2, .none) := by
    rw [hcode, hpc]; exact hdec
  rw [← hcode, step_log2 s hd, hstk]
  have hov' : ¬ ((a :: b :: c :: d :: t).length - 4 + 0 > 1024) := by
    simp only [List.length_cons]; omega
  have hpermF : (¬ s.executionEnv.perm = true) = False := eq_false (by simp [hperm])
  simp only [collapse_two_stage, if_neg hov', hpermF, if_false, stLog2]

theorem RD.log2 {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {pc : UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b c d : UInt256} {t : List UInt256} (mcost : ℕ) (awout : UInt256)
    (h : RD code ee g s0 pc (a :: b :: c :: d :: t) mem aw rdata acc k C)
    (hdec : decode code pc = some (.LOG2, .none)) (hperm : ee.perm = true)
    (hmc : ∀ s : State, s.machineState.activeWords = aw →
        s.machineState.stack = a :: b :: c :: d :: t →
        memoryExpansionCost s .LOG2 = mcost)
    (hawout : UInt256.ofNat (MachineState.M aw.toNat a.toNat b.toNat) = awout)
    (hov : t.length ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩) t mem awout rdata acc (k + 1)
      (C + (mcost + (GasConstants.Glog + GasConstants.Glogdata * b.toNat
        + 2 * GasConstants.Glogtopic))) := by
  unfold RD at h ⊢
  rcases h with hoog | ⟨s, hX, hcode, hpc, hstk, hgas, hk, hC, hmem, haw, hrdata, hacc,
      hee, hworld⟩
  · exact Or.inl hoog
  · have hmcS : memoryExpansionCost s .LOG2 = mcost := hmc s haw hstk
    have hperms : s.executionEnv.perm = true := by rw [hee]; exact hperm
    have st := log2_xstep hcode hpc hdec hperms hstk hov
    rw [hmcS] at st
    by_cases gg : g.toNat < C + (mcost
        + (GasConstants.Glog + GasConstants.Glogdata * b.toNat + 2 * GasConstants.Glogtopic))
    · exact Or.inl (hX.trans (stepOOG hgas st hk hC (by omega)))
    · refine Or.inr ⟨stLog2 s a b c d t,
        hX.trans (stepContinue hgas st hk (Nat.not_lt.mp gg)), ?_, ?_, ?_, ?_,
          (by have : 1 ≤ GasConstants.Glog := (by decide); omega), by omega,
          ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [stLog2]; exact hcode
      · simp only [stLog2]; rw [hpc]
      · simp only [stLog2]
      · simp only [stLog2, hmcS]
        rw [hgas, Sat256.subNat_sub_add_of_sub_sub, Sat256.subNat_sub_add_of_sub_sub]
      · simp only [stLog2]; exact hmem
      · simp only [stLog2]; rw [haw, hawout]
      · simp only [stLog2]; exact hrdata
      · simp only [stLog2]; exact hacc
      · simp only [stLog2]; exact hee
      · simp only [stLog2]; exact hworld

/-! ## Inline `Error(string)` revert tail -/

@[reducible] def gemJoinInlineErrorStringRevertTailWf
    (code : ByteArray) (pc len word : UInt256) : Prop :=
  let p2 := pc + UInt256.ofNat 2
  let p3 := p2 + ⟨1⟩
  let p4 := p3 + ⟨1⟩
  let p8 := p4 + UInt256.ofNat 4
  let p10 := p8 + UInt256.ofNat 2
  let p11 := p10 + ⟨1⟩
  let p12 := p11 + ⟨1⟩
  let p13 := p12 + ⟨1⟩
  let p15 := p13 + UInt256.ofNat 2
  let p17 := p15 + UInt256.ofNat 2
  let p18 := p17 + ⟨1⟩
  let p19 := p18 + ⟨1⟩
  let p20 := p19 + ⟨1⟩
  let p22 := p20 + UInt256.ofNat 2
  let p24 := p22 + UInt256.ofNat 2
  let p25 := p24 + ⟨1⟩
  let p26 := p25 + ⟨1⟩
  let p27 := p26 + ⟨1⟩
  let p60 := p27 + UInt256.ofNat 33
  let p62 := p60 + UInt256.ofNat 2
  let p63 := p62 + ⟨1⟩
  let p64 := p63 + ⟨1⟩
  let p65 := p64 + ⟨1⟩
  let p66 := p65 + ⟨1⟩
  let p67 := p66 + ⟨1⟩
  let p68 := p67 + ⟨1⟩
  let p69 := p68 + ⟨1⟩
  let p70 := p69 + ⟨1⟩
  let p71 := p70 + ⟨1⟩
  let p73 := p71 + UInt256.ofNat 2
  let p74 := p73 + ⟨1⟩
  let p75 := p74 + ⟨1⟩
  decode code pc = some (.Push .PUSH1, some (⟨64⟩, 1))
  ∧ decode code p2 = some (.DUP1, .none)
  ∧ decode code p3 = some (.MLOAD, .none)
  ∧ decode code p4 = some (.Push .PUSH3, some (⟨4594637⟩, 3))
  ∧ decode code p8 = some (.Push .PUSH1, some (⟨229⟩, 1))
  ∧ decode code p10 = some (.SHL, .none)
  ∧ decode code p11 = some (.DUP2, .none)
  ∧ decode code p12 = some (.MSTORE, .none)
  ∧ decode code p13 = some (.Push .PUSH1, some (⟨32⟩, 1))
  ∧ decode code p15 = some (.Push .PUSH1, some (⟨4⟩, 1))
  ∧ decode code p17 = some (.DUP3, .none)
  ∧ decode code p18 = some (.ADD, .none)
  ∧ decode code p19 = some (.MSTORE, .none)
  ∧ decode code p20 = some (.Push .PUSH1, some (len, 1))
  ∧ decode code p22 = some (.Push .PUSH1, some (⟨36⟩, 1))
  ∧ decode code p24 = some (.DUP3, .none)
  ∧ decode code p25 = some (.ADD, .none)
  ∧ decode code p26 = some (.MSTORE, .none)
  ∧ decode code p27 = some (.Push .PUSH32, some (word, 32))
  ∧ decode code p60 = some (.Push .PUSH1, some (⟨68⟩, 1))
  ∧ decode code p62 = some (.DUP3, .none)
  ∧ decode code p63 = some (.ADD, .none)
  ∧ decode code p64 = some (.MSTORE, .none)
  ∧ decode code p65 = some (.SWAP1, .none)
  ∧ decode code p66 = some (.MLOAD, .none)
  ∧ decode code p67 = some (.SWAP1, .none)
  ∧ decode code p68 = some (.DUP2, .none)
  ∧ decode code p69 = some (.SWAP1, .none)
  ∧ decode code p70 = some (.SUB, .none)
  ∧ decode code p71 = some (.Push .PUSH1, some (⟨100⟩, 1))
  ∧ decode code p73 = some (.ADD, .none)
  ∧ decode code p74 = some (.SWAP1, .none)
  ∧ decode code p75 = some (.REVERT, .none)

set_option maxHeartbeats 1000000 in
theorem RD.gemJoinInlineErrorStringRevertTail {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {pc : UInt256}
    {len word : UInt256} {stk : List UInt256} {mem rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD code ee g s0 pc stk mem (UInt256.ofNat 3) rdata acc k C)
    (hwf : gemJoinInlineErrorStringRevertTailWf code pc len word)
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hov : stk.length + 5 ≤ 1024) :
    RDrev code g s0 := by
  rcases hwf with
    ⟨hd0, hd2, hd3, hd4, hd8, hd10, hd11, hd12, hd13, hd15, hd17, hd18,
      hd19, hd20, hd22, hd24, hd25, hd26, hd27, hd60, hd62, hd63, hd64,
      hd65, hd66, hd67, hd68, hd69, hd70, hd71, hd73, hd74, hd75⟩
  have rdMload := evm_run h with [
    raw push1 ⟨64⟩ hd0 (by evm_ov),
    raw dup1 hd2 (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) hd3
      mem_cost
      (mloadFreePtrValue (by rw [hmem]; decide) (by decide) hread64)
      (by decide) (by evm_ov)]
  have rdSelectorRaw := rdMload.pushConst (⟨4594637⟩ : UInt256)
    (width := 3) (op := .PUSH3) (by decide) hd4
    (by simp only [List.length_cons]; omega)
  have rdPrefix := evm_run rdSelectorRaw with [
    raw push1 ⟨229⟩ hd8 (by evm_ov),
    raw shl hd10 (by evm_ov),
    raw dup2 hd11 (by evm_ov),
    raw mstore 6 (solcErrorStringMem0 mem) (UInt256.ofNat 5)
      hd12 mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨32⟩ hd13 (by evm_ov),
    raw push1 ⟨4⟩ hd15 (by evm_ov),
    raw dup3 hd17 (by evm_ov),
    raw add hd18 (by evm_ov),
    raw mstore 3 (solcErrorStringMem1 mem) (UInt256.ofNat 6)
      hd19 mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 len hd20 (by evm_ov),
    raw push1 ⟨36⟩ hd22 (by evm_ov),
    raw dup3 hd24 (by evm_ov),
    raw add hd25 (by evm_ov),
    raw mstore 3 (solcErrorStringMem2 len mem)
      (UInt256.ofNat 7) hd26 mem_cost (by rfl) (by decide) (by evm_ov)]
  have rdWord := rdPrefix.pushConst word (width := 32) (op := .PUSH32)
    (by decide) hd27 (by simp only [List.length_cons]; omega)
  exact evm_run rdWord with [
    raw push1 ⟨68⟩ hd60 (by evm_ov),
    raw dup3 hd62 (by evm_ov),
    raw add hd63 (by evm_ov),
    raw mstore 3 (solcErrorStringMem3 len word mem)
      (UInt256.ofNat 8) hd64 mem_cost (by rfl) (by decide) (by evm_ov),
    raw swap1 hd65 (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) hd66
      mem_cost
      (solcErrorStringMem3_mload64 len word hmem hread64)
      (by decide) (by evm_ov),
    raw swap1 hd67 (by evm_ov),
    raw dup2 hd68 (by evm_ov),
    raw swap1 hd69 (by evm_ov),
    raw sub hd70 (by evm_ov),
    raw push1 ⟨100⟩ hd71 (by evm_ov),
    raw add hd73 (by evm_ov),
    raw swap1 hd74 (by evm_ov),
    raw rev 0 hd75 mem_cost (by evm_ov)]

theorem gemJoinAddressGetterBodyReturns (evm : EVM.State) (locals : Store)
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
      exact congrArg EvalResult.ok (gemJoinStorageLocLoad_address_offset0 evm slot))

theorem gemJoinUint256GetterBodyReturns (evm : EVM.State) (locals : Store)
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
      exact congrArg EvalResult.ok (gemJoinStorageLocLoad_uint256 evm slot))

theorem gemJoinBytes32GetterBodyReturns (evm : EVM.State) (locals : Store)
    {ref : StorageRef} {er : EvaledStorageRef} {slot : UInt256}
    (h : evm.executionEnv.weiValue = ⟨0⟩)
    (hbase : locals.get? ref.base = none)
    (her : evalStorageRef config { contract := contract, locals := locals } evm ref = .ok er)
    (hty : storageTypeAt? contract.storage er = some (.elem (.bytes bytes32Width)))
    (hloc : config.storage.layout er = fun _ => some (bytes32Loc slot)) :
    ExecTransitionBody config contract evm locals (nonpayable ++ [ .return [(.storage ref)] ])
      (.returned { contract := contract, locals := locals } evm
        (some [(.fixedBytes bytes32Width
          (EVM.Word.toBytesBE (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)))])) := by
  simpa [nonpayable] using
    nonpayableReturnExprBodyReturns (cfg := config) (contract := contract) h (by
      rw [evalExpr_storage_scalar (hbase := hbase) (her := her) (hty := hty) (hloc := hloc)]
      exact congrArg EvalResult.ok (gemJoinStorageLocLoad_bytes32 evm slot))

theorem gemJoinAddressGetterBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    {transition : TransitionDecl} {entry returnPc routine slot : UInt256}
    (hcode : I.code = gemJoinBytecode)
    (hdispatch : dispatchMsg contract I.calldata = some transition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (transition.params.map Param.name)
        (transitionSignature transition).paramTypes I.calldata = some ∅)
    (hreach : ∃ k C, RD gemJoinBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) entry [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hentry : solcGetterEntryWf gemJoinBytecode entry returnPc routine)
    (hgetter : solcAddressSlotGetterWf gemJoinBytecode routine slot)
    (hroutine : (D_J gemJoinBytecode 0).contains routine = true)
    (hreturnJd : (D_J gemJoinBytecode 0).contains returnPc = true)
    (hretmem : solcReturnAddressFromMemWf gemJoinBytecode returnPc)
    (hreturn : transition.returnType = [addr])
    (hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅ transition.body
        (.returned { contract := contract, locals := ∅ }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.address (AccountAddress.ofNat
            (gemJoinAddressReturnWord slot σ_solm I).toNat))]))) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hword : gemJoinSlotWord slot σ_evm I = gemJoinSlotWord slot σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner slot ⟨0⟩
  have hval :
      some [Value.address (AccountAddress.ofNat (gemJoinAddressReturnWord slot σ_solm I).toNat)] =
        some [Value.address (AccountAddress.ofNat (gemJoinAddressReturnWord slot σ_evm I).toNat)] := by
    have hslot : gemJoinSlotWord slot σ_solm I = gemJoinSlotWord slot σ_evm I := hword.symm
    simp [gemJoinAddressReturnWord, hslot]
  have henc :
      returnEquiv (UInt256.toByteArray (gemJoinAddressReturnWord slot σ_evm I))
        (some [(.address (AccountAddress.ofNat (gemJoinAddressReturnWord slot σ_evm I).toNat))])
        transition.returnType := by
    rw [hreturn]
    simpa [gemJoinAddressReturnWord] using
      (returnEquiv_of_encode
        (solcAddressReturnEncoding (addrTy := addr) rfl (gemJoinSlotWord slot σ_evm I)))
  have hret := RD.solcAddressGetterExternal (code := gemJoinBytecode)
    (g := Sat256.ofUInt256 g) (returnPc := returnPc) (entry := entry) (routine := routine)
    (slot := slot) hreach hentry hgetter hroutine hreturnJd hretmem
  have hret' :
      RDret gemJoinBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) (cA, σ_evm)
        (UInt256.toByteArray (gemJoinAddressReturnWord slot σ_evm I)) := by
    simpa [gemJoinAddressReturnWord, gemJoinSlotWord] using hret
  exact hret'.reEquivExecutionTransport hcode hdispatch hdecode hbody hval hAccounts henc

theorem gemJoinUint256GetterBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    {transition : TransitionDecl} {entry returnPc routine slot : UInt256}
    (hcode : I.code = gemJoinBytecode)
    (hdispatch : dispatchMsg contract I.calldata = some transition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (transition.params.map Param.name)
        (transitionSignature transition).paramTypes I.calldata = some ∅)
    (hreach : ∃ k C, RD gemJoinBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) entry [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hentry : solcGetterEntryWf gemJoinBytecode entry returnPc routine)
    (hgetter : solcWordSlotGetterWf gemJoinBytecode routine slot)
    (hroutine : (D_J gemJoinBytecode 0).contains routine = true)
    (hreturnJd : (D_J gemJoinBytecode 0).contains returnPc = true)
    (hretmem : solcReturnWordFromMemWf gemJoinBytecode returnPc)
    (hreturn : transition.returnType = [uint256])
    (hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅ transition.body
        (.returned { contract := contract, locals := ∅ }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.int (Int.ofNat (gemJoinSlotWord slot σ_solm I).toNat))]))) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hword : gemJoinSlotWord slot σ_evm I = gemJoinSlotWord slot σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner slot ⟨0⟩
  have hval :
      some [Value.int (Int.ofNat (gemJoinSlotWord slot σ_solm I).toNat)] =
        some [Value.int (Int.ofNat (gemJoinSlotWord slot σ_evm I).toNat)] := by
    rw [hword]
  have henc :
      returnEquiv (UInt256.toByteArray (gemJoinSlotWord slot σ_evm I))
        (some [(.int (Int.ofNat (gemJoinSlotWord slot σ_evm I).toNat))])
        transition.returnType := by
    rw [hreturn]
    exact returnEquiv_of_encode
      (by simpa [uint256] using uint256ReturnEncoding (gemJoinSlotWord slot σ_evm I))
  have hret := RD.solcWordGetterExternal (code := gemJoinBytecode)
    (g := Sat256.ofUInt256 g) (returnPc := returnPc) (entry := entry) (routine := routine)
    (slot := slot) hreach hentry hgetter hroutine hreturnJd hretmem
  have hret' :
      RDret gemJoinBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) (cA, σ_evm)
        (UInt256.toByteArray (gemJoinSlotWord slot σ_evm I)) := by
    simpa [gemJoinSlotWord] using hret
  exact hret'.reEquivExecutionTransport hcode hdispatch hdecode hbody hval hAccounts henc

theorem gemJoinBytes32GetterBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    {transition : TransitionDecl} {entry returnPc routine slot : UInt256}
    (hcode : I.code = gemJoinBytecode)
    (hdispatch : dispatchMsg contract I.calldata = some transition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (transition.params.map Param.name)
        (transitionSignature transition).paramTypes I.calldata = some ∅)
    (hreach : ∃ k C, RD gemJoinBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) entry [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hentry : solcGetterEntryWf gemJoinBytecode entry returnPc routine)
    (hgetter : solcWordSlotGetterWf gemJoinBytecode routine slot)
    (hroutine : (D_J gemJoinBytecode 0).contains routine = true)
    (hreturnJd : (D_J gemJoinBytecode 0).contains returnPc = true)
    (hretmem : solcReturnWordFromMemWf gemJoinBytecode returnPc)
    (hreturn : transition.returnType = [bytes32])
    (hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅ transition.body
        (.returned { contract := contract, locals := ∅ }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.fixedBytes bytes32Width
            (EVM.Word.toBytesBE (gemJoinSlotWord slot σ_solm I)))]))) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hword : gemJoinSlotWord slot σ_evm I = gemJoinSlotWord slot σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner slot ⟨0⟩
  have hval :
      some [Value.fixedBytes bytes32Width (EVM.Word.toBytesBE (gemJoinSlotWord slot σ_solm I))] =
        some [Value.fixedBytes bytes32Width (EVM.Word.toBytesBE (gemJoinSlotWord slot σ_evm I))] := by
    rw [hword]
  have henc :
      returnEquiv (UInt256.toByteArray (gemJoinSlotWord slot σ_evm I))
        (some [(.fixedBytes bytes32Width (EVM.Word.toBytesBE (gemJoinSlotWord slot σ_evm I)))])
        transition.returnType := by
    rw [hreturn]
    exact returnEquiv_of_encode
      (by simpa [bytes32, bytes32Width] using bytes32ReturnEncoding (gemJoinSlotWord slot σ_evm I))
  have hret := RD.solcWordGetterExternal (code := gemJoinBytecode)
    (g := Sat256.ofUInt256 g) (returnPc := returnPc) (entry := entry) (routine := routine)
    (slot := slot) hreach hentry hgetter hroutine hreturnJd hretmem
  have hret' :
      RDret gemJoinBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) (cA, σ_evm)
        (UInt256.toByteArray (gemJoinSlotWord slot σ_evm I)) := by
    simpa [gemJoinSlotWord] using hret
  exact hret'.reEquivExecutionTransport hcode hdispatch hdecode hbody hval hAccounts henc

@[reducible] def gemJoinZeroSlotMappingGetterWf (code : ByteArray) (pc : UInt256) : Prop :=
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

theorem RD.gemJoinZeroSlotMappingGetter {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {pc key ret : UInt256} {R : List UInt256}
    {rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD code ee g s0 pc (key :: ret :: R)
        solcFreePtrMem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hwf : gemJoinZeroSlotMappingGetterWf code pc)
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

end Benchmarks.Dss.GemJoin
