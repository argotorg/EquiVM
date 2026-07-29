import Benchmarks.Dss.Cure.Trusted
import Reasoning.ABI
import Reasoning.Stepping
import Reasoning.Reach
import Reasoning.Solc
import Reasoning.Memory
import Reasoning.Storage
import Reasoning.Dispatch
import Reasoning.SolmBody
import Mathlib.Tactic.IntervalCases

/-!
# MakerDAO/Sky DSS Cure shared proof foundation

Contract-wide selector notation and top-level revert/no-dispatch placeholders for the optimized
Cure runtime.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.Cure

/-- The 4-byte selector word computed by `CALLDATALOAD(0); SHR 224`. -/
abbrev cureSelWord (I : ExecutionEnv) : UInt256 :=
  UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩

/-- The 4-byte selector of `I`'s calldata equals `sel`. -/
abbrev selIs (I : ExecutionEnv) (sel : ByteArray) : Prop :=
  (sel == I.calldata.extract 0 4) = true

/-- Function selectors in `contract.transitions` order. -/
def cureSelBytes : ℕ → ByteArray
  | 0 => ⟨#[0x09, 0x61, 0x56, 0x62]⟩  -- amt(address)
  | 1 => ⟨#[0x69, 0x24, 0x50, 0x09]⟩  -- cage()
  | 2 => ⟨#[0x9c, 0x52, 0xa7, 0xf1]⟩  -- deny(address)
  | 3 => ⟨#[0x91, 0xf2, 0x70, 0x0a]⟩  -- drop(address)
  | 4 => ⟨#[0x29, 0xae, 0x81, 0x14]⟩  -- file(bytes32,uint256)
  | 5 => ⟨#[0x49, 0x3a, 0xa4, 0xc7]⟩  -- lCount()
  | 6 => ⟨#[0x3c, 0x27, 0x8b, 0xd5]⟩  -- lift(address)
  | 7 => ⟨#[0x0f, 0x56, 0x0c, 0xd7]⟩  -- list()
  | 8 => ⟨#[0x95, 0x7a, 0xa5, 0x8c]⟩  -- live()
  | 9 => ⟨#[0x2f, 0x40, 0xe7, 0x34]⟩  -- load(address)
  | 10 => ⟨#[0xff, 0xa9, 0xca, 0x9f]⟩ -- loaded(address)
  | 11 => ⟨#[0x93, 0xd0, 0x28, 0x1c]⟩ -- pos(address)
  | 12 => ⟨#[0x65, 0xfa, 0xe3, 0x5e]⟩ -- rely(address)
  | 13 => ⟨#[0x95, 0x4a, 0xb4, 0xb2]⟩ -- say()
  | 14 => ⟨#[0xf3, 0x81, 0x27, 0x3f]⟩ -- srcs(uint256)
  | 15 => ⟨#[0x53, 0xf9, 0xa8, 0x73]⟩ -- tCount()
  | 16 => ⟨#[0x53, 0xd7, 0x00, 0xe5]⟩ -- tell()
  | 17 => ⟨#[0x64, 0xbd, 0x70, 0x13]⟩ -- wait()
  | 18 => ⟨#[0xbf, 0x35, 0x3d, 0xbb]⟩ -- wards(address)
  | _ => ⟨#[0xe2, 0xb0, 0xca, 0xef]⟩  -- when()

/-- No calldata shorter than four bytes can dispatch to a Cure function. -/
theorem cureDispatch_none_short {cd : ByteArray} (h : cd.size < 4) :
    dispatchMsg contract cd = none := by
  rw [dispatchMsg_eq_dispatchList contract cd (by rfl)]
  change dispatchList transitions cd = none
  exact dispatchList_none_short _ (by
    intro t ht
    simp [transitions] at ht
    rcases ht with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [selectorOf, cureAmtSelectorBytes]; rfl
    · rw [selectorOf, cureCageSelectorBytes]; rfl
    · rw [selectorOf, cureDenySelectorBytes]; rfl
    · rw [selectorOf, cureDropSelectorBytes]; rfl
    · rw [selectorOf, cureFileSelectorBytes]; rfl
    · rw [selectorOf, cureLCountSelectorBytes]; rfl
    · rw [selectorOf, cureLiftSelectorBytes]; rfl
    · rw [selectorOf, cureListSelectorBytes]; rfl
    · rw [selectorOf, cureLiveSelectorBytes]; rfl
    · rw [selectorOf, cureLoadSelectorBytes]; rfl
    · rw [selectorOf, cureLoadedSelectorBytes]; rfl
    · rw [selectorOf, curePosSelectorBytes]; rfl
    · rw [selectorOf, cureRelySelectorBytes]; rfl
    · rw [selectorOf, cureSaySelectorBytes]; rfl
    · rw [selectorOf, cureSrcsSelectorBytes]; rfl
    · rw [selectorOf, cureTCountSelectorBytes]; rfl
    · rw [selectorOf, cureTellSelectorBytes]; rfl
    · rw [selectorOf, cureWaitSelectorBytes]; rfl
    · rw [selectorOf, cureWardsSelectorBytes]; rfl
    · rw [selectorOf, cureWhenSelectorBytes]; rfl) h

/-- If all Cure selectors miss, `dispatchMsg` returns `none`. -/
theorem cureDispatch_none_nomatch {cd : ByteArray}
    (hnm : ∀ i, i < 20 → (cureSelBytes i == cd.extract 0 4) = false) :
    dispatchMsg contract cd = none := by
  apply dispatchMsg_none_of_all_ne (hfallback := by rfl)
  intro t ht
  simp [contract, transitions] at ht
  rcases ht with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [selectorOf, cureAmtSelectorBytes]; simpa [cureSelBytes] using hnm 0 (by omega)
  · rw [selectorOf, cureCageSelectorBytes]; simpa [cureSelBytes] using hnm 1 (by omega)
  · rw [selectorOf, cureDenySelectorBytes]; simpa [cureSelBytes] using hnm 2 (by omega)
  · rw [selectorOf, cureDropSelectorBytes]; simpa [cureSelBytes] using hnm 3 (by omega)
  · rw [selectorOf, cureFileSelectorBytes]; simpa [cureSelBytes] using hnm 4 (by omega)
  · rw [selectorOf, cureLCountSelectorBytes]; simpa [cureSelBytes] using hnm 5 (by omega)
  · rw [selectorOf, cureLiftSelectorBytes]; simpa [cureSelBytes] using hnm 6 (by omega)
  · rw [selectorOf, cureListSelectorBytes]; simpa [cureSelBytes] using hnm 7 (by omega)
  · rw [selectorOf, cureLiveSelectorBytes]; simpa [cureSelBytes] using hnm 8 (by omega)
  · rw [selectorOf, cureLoadSelectorBytes]; simpa [cureSelBytes] using hnm 9 (by omega)
  · rw [selectorOf, cureLoadedSelectorBytes]; simpa [cureSelBytes] using hnm 10 (by omega)
  · rw [selectorOf, curePosSelectorBytes]; simpa [cureSelBytes] using hnm 11 (by omega)
  · rw [selectorOf, cureRelySelectorBytes]; simpa [cureSelBytes] using hnm 12 (by omega)
  · rw [selectorOf, cureSaySelectorBytes]; simpa [cureSelBytes] using hnm 13 (by omega)
  · rw [selectorOf, cureSrcsSelectorBytes]; simpa [cureSelBytes] using hnm 14 (by omega)
  · rw [selectorOf, cureTCountSelectorBytes]; simpa [cureSelBytes] using hnm 15 (by omega)
  · rw [selectorOf, cureTellSelectorBytes]; simpa [cureSelBytes] using hnm 16 (by omega)
  · rw [selectorOf, cureWaitSelectorBytes]; simpa [cureSelBytes] using hnm 17 (by omega)
  · rw [selectorOf, cureWardsSelectorBytes]; simpa [cureSelBytes] using hnm 18 (by omega)
  · rw [selectorOf, cureWhenSelectorBytes]; simpa [cureSelBytes] using hnm 19 (by omega)

def cureSlotWord (slot : UInt256) (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  solcSlotWord σ I slot

/-- Storage well-formedness for the generated `srcs` dynamic-array getter and source index map.

The bound rules out overflow in the Solidity return routine's pointer/length arithmetic and keeps
the final ABI return object within the byte-addressed memory model used by `ByteArray`.
It accounts for a 128-byte array base, 32-byte length word, 64-byte ABI prefix, and two
`32 * len` byte spans.

This intentionally does not assume relationships between mapping slots and array length slots:
aliasing storage states are handled in the per-function proofs. -/
def cureStorageWF (σ : AccountMap) (I : ExecutionEnv) : Prop :=
  224 + 64 * (cureSlotWord ⟨2⟩ σ I).toNat < 2 ^ 64

theorem cureStorageWF_returnBound {σ : AccountMap} {I : ExecutionEnv}
    (hwf : cureStorageWF σ I) :
    224 + 64 * (cureSlotWord ⟨2⟩ σ I).toNat < 2 ^ 64 :=
  hwf

theorem cureStorageWF_accountMapEquiv {σ τ : AccountMap} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ τ) :
    cureStorageWF σ I ↔ cureStorageWF τ I := by
  have hword : cureSlotWord ⟨2⟩ σ I = cureSlotWord ⟨2⟩ τ I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨2⟩ ⟨0⟩
  constructor
  · intro h
    simpa [cureStorageWF, ← hword] using h
  · intro h
    simpa [cureStorageWF, hword] using h

theorem cureStorageWF_of_accountMapEquiv {σ τ : AccountMap} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ τ) (hwf : cureStorageWF σ I) :
    cureStorageWF τ I :=
  (cureStorageWF_accountMapEquiv hAccounts).mp hwf

theorem cureStorageLocLoad_uint256 (evm : EVM.State) (slot : UInt256) :
    storageLocLoad evm (wordLoc slot) =
      .int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot).toNat) := by
  simpa [wordLoc, uint256Loc] using storageLocLoad_uint256 evm slot

theorem cureUint256GetterBodyReturns (evm : EVM.State) (locals : Store)
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
      exact congrArg EvalResult.ok (cureStorageLocLoad_uint256 evm slot))

theorem cureUint256GetterBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    {transition : TransitionDecl} {entry returnPc routine slot : UInt256}
    (hcode : I.code = cureBytecode)
    (hdispatch : dispatchMsg contract I.calldata = some transition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (transition.params.map Param.name)
        (transitionSignature transition).paramTypes I.calldata = some ∅)
    (hreach : ∃ k C, RD cureBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) entry [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hentry : solcGetterEntryWf cureBytecode entry returnPc routine)
    (hgetter : solcWordSlotGetterWf cureBytecode routine slot)
    (hroutine : (D_J cureBytecode 0).contains routine = true)
    (hreturnJd : (D_J cureBytecode 0).contains returnPc = true)
    (hretmem : solcReturnWordFromMemWf cureBytecode returnPc)
    (hreturn : transition.returnType = [uint256])
    (hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅ transition.body
        (.returned { contract := contract, locals := ∅ }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.int (Int.ofNat (cureSlotWord slot σ_solm I).toNat))]))) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hword : cureSlotWord slot σ_evm I = cureSlotWord slot σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner slot ⟨0⟩
  have hval :
      some [Value.int (Int.ofNat (cureSlotWord slot σ_solm I).toNat)] =
        some [Value.int (Int.ofNat (cureSlotWord slot σ_evm I).toNat)] := by
    rw [hword]
  have henc :
      returnEquiv (UInt256.toByteArray (cureSlotWord slot σ_evm I))
        (some [(.int (Int.ofNat (cureSlotWord slot σ_evm I).toNat))])
        transition.returnType := by
    rw [hreturn]
    exact returnEquiv_of_encode
      (by simpa [uint256] using uint256ReturnEncoding (cureSlotWord slot σ_evm I))
  have hret := RD.solcWordGetterExternal (code := cureBytecode) (g := Sat256.ofUInt256 g)
    (returnPc := returnPc) (entry := entry) (routine := routine) (slot := slot)
    hreach hentry hgetter hroutine hreturnJd hretmem
  have hret' :
      RDret cureBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) (cA, σ_evm)
        (UInt256.toByteArray (cureSlotWord slot σ_evm I)) := by
    simpa [cureSlotWord] using hret
  exact hret'.reEquivExecutionTransport hcode hdispatch hdecode hbody hval hAccounts henc

-- LIBRARY CANDIDATE: variant of the solc word-slot getter that swaps the return pc before jumping.
@[reducible] def solcWordSlotGetterSwapJumpWf
    (code : ByteArray) (pc slot : UInt256) : Prop :=
  let p1 := pc + ⟨1⟩
  let p3 := p1 + UInt256.ofNat 2
  let p4 := p3 + ⟨1⟩
  let p5 := p4 + ⟨1⟩
  decode code pc = some (.JUMPDEST, .none)
  ∧ decode code p1 = some (.Push .PUSH1, some (slot, 1))
  ∧ decode code p3 = some (.SLOAD, .none)
  ∧ decode code p4 = some (.SWAP1, .none)
  ∧ decode code p5 = some (.JUMP, .none)

theorem RD.solcWordSlotGetterSwapJump {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {pc slot ret : UInt256} {R : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD code ee g s0 pc (ret :: R) mem aw rdata (cA, σ) k C)
    (hwf : solcWordSlotGetterSwapJumpWf code pc slot)
    (hret : (D_J code 0).contains ret = true)
    (hov : R.length + 3 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ret
      ((σ.find? ee.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD slot ⟨0⟩)) :: R)
      mem aw rdata (cA, σ) k' C' := by
  rcases hwf with ⟨hd0, hd1, hd2, hd3, hd4⟩
  have rd1 := h.jumpdest hd0 (by simp only [List.length_cons]; omega)
  have rd3 := rd1.push1 slot hd1 (by simp only [List.length_cons]; omega)
  obtain ⟨_, _, rd4⟩ := rd3.sload hd2 (by simp only [List.length_cons]; omega)
  have rd5 := rd4.swap1 hd3 (by omega)
  have rdRet := rd5.jump hd4 hret (by simp only [List.length_cons]; omega)
  exact ⟨_, _, rdRet⟩

-- LIBRARY CANDIDATE: generic solc getter for a mapping stored at slot zero.
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

/-- Every Cure transition body reverts when the non-payable guard sees non-zero callvalue. -/
theorem cureBodyReverts_nonPayable (t : TransitionDecl) (ht : t ∈ contract.transitions)
    (evm : EVM.State) (locals : Store) (h : evm.executionEnv.weiValue ≠ ⟨0⟩) :
    ExecTransitionBody config contract evm locals t.body .reverted := by
  simp [contract, transitions] at ht
  rcases ht with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact bodyReverts_nonPayable h

-- GENERALIZES Reasoning.Solc.solcGuardCallvalueNonzeroRevert — supports legacy
-- `PUSH1 0; DUP1; REVERT` revert stubs emitted before `PUSH0` was available.
theorem solcGuardCallvalueNonzeroRevertLegacy {cA gh bl σ σ₀ A I} {g : Sat256}
    {code : ByteArray} {ctgt : UInt256} {wC : ℕ} {opC : Operation.POp} {k0 C0 : ℕ}
    (h : RD code I g (initState cA gh bl σ σ₀ g A I) ⟨8⟩
          [UInt256.isZero I.weiValue, I.weiValue] solcFreePtrMem (UInt256.ofNat 3)
          ByteArray.empty (cA, σ) k0 C0)
    (hwv : I.weiValue ≠ ⟨0⟩) (hopC : opC ≠ .PUSH0)
    (hpushC : decode code ⟨8⟩ = some (.Push opC, some (ctgt, wC)))
    (hjumpi : decode code (⟨8⟩ + UInt256.ofNat wC.succ) = some (.JUMPI, .none))
    (hr0 : decode code (⟨8⟩ + UInt256.ofNat wC.succ + ⟨1⟩) =
      some (.Push .PUSH1, some (⟨0⟩, 1)))
    (hr1 : decode code (⟨8⟩ + UInt256.ofNat wC.succ + ⟨1⟩ + UInt256.ofNat 2) =
      some (.DUP1, .none))
    (hr2 : decode code (⟨8⟩ + UInt256.ofNat wC.succ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩) =
      some (.REVERT, .none)) :
    RDrev code g (initState cA gh bl σ σ₀ g A I) :=
  (h.pushConst ctgt hopC hpushC (by simp only [List.length]; omega)
    |>.jumpiNT hjumpi (isZero_eq_zero_of_ne hwv)
      (by simp only [List.length]; omega))
    |>.solcPush1Dup1Revert0 hr0 hr1 hr2 (by simp only [List.length]; omega)

/-- Legacy solc short-calldata revert for `PUSH1 0; DUP1; REVERT` stubs. -/
theorem solcCalldataShortRevertLegacy {cA gh bl σ σ₀ A I} {g : Sat256}
    {code : ByteArray} {bodyPc rtgt : UInt256} {wR : ℕ} {opR : Operation.POp} {k0 C0 : ℕ}
    (h : RD code I g (initState cA gh bl σ σ₀ g A I) bodyPc [] solcFreePtrMem
          (UInt256.ofNat 3) ByteArray.empty (cA, σ) k0 C0)
    (hsz : I.calldata.size < 4)
    (hd_p4 : decode code bodyPc = some (.Push .PUSH1, some (⟨4⟩, 1)))
    (hd_cds : decode code (bodyPc + UInt256.ofNat 2) = some (.CALLDATASIZE, .none))
    (hd_lt : decode code (bodyPc + UInt256.ofNat 2 + ⟨1⟩) = some (.LT, .none))
    (hopR : opR ≠ .PUSH0)
    (hd_pR : decode code (bodyPc + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩) =
      some (.Push opR, some (rtgt, wR)))
    (hd_ji :
      decode code (bodyPc + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat wR.succ) =
        some (.JUMPI, .none))
    (hd_jd : decode code rtgt = some (.JUMPDEST, .none))
    (hjd : (D_J code 0).contains rtgt = true)
    (hr0 : decode code (rtgt + ⟨1⟩) = some (.Push .PUSH1, some (⟨0⟩, 1)))
    (hr1 : decode code (rtgt + ⟨1⟩ + UInt256.ofNat 2) = some (.DUP1, .none))
    (hr2 : decode code (rtgt + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩) = some (.REVERT, .none)) :
    RDrev code g (initState cA gh bl σ σ₀ g A I) :=
  (h.push1 ⟨4⟩ hd_p4 (by simp only [List.length]; omega)
    |>.calldatasize hd_cds (by simp only [List.length]; omega)
    |>.lt hd_lt (by simp only [List.length]; omega)
    |>.pushConst rtgt hopR hd_pR (by simp only [List.length]; omega)
    |>.jumpiT hd_ji (lt_four_ne_zero_of_lt hsz) hjd (by simp only [List.length]; omega)
    |>.jumpdest hd_jd (by simp only [List.length]; omega))
    |>.solcPush1Dup1Revert0 hr0 hr1 hr2 (by simp only [List.length]; omega)

/-- `callvalue ≠ 0` makes the global solc non-payable guard revert before dispatch. -/
theorem cureX_callvalue_ne {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = cureBytecode) (hwv : I.weiValue ≠ ⟨0⟩) :
    RDrev cureBytecode g (initState cA gh bl σ σ₀ g A I) := by
  exact solcGuardCallvalueNonzeroRevertLegacy
    (ctgt := solcGuardTgt cureBytecode) (opC := solcGuardTgtOp cureBytecode)
    (wC := solcGuardTgtWidth cureBytecode)
    (solcGuardPrologueRD hcode (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide))
    hwv (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)

/-- EVM calldata-size guard reverts when calldata is shorter than a selector. -/
theorem cureX_short {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = cureBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : I.calldata.size < 4) :
    RDrev cureBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have h0 := solcGuardPrologueRD (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (g := g) hcode (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  obtain ⟨_, _, h1⟩ := solcGuardCallvalueZero
    (ctgt := solcGuardTgt cureBytecode) (opC := solcGuardTgtOp cureBytecode)
    (wC := solcGuardTgtWidth cureBytecode) h0 hwv
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by jump_dest)
  exact solcCalldataShortRevertLegacy
    (bodyPc := solcDispatchBodyPc cureBytecode)
    (rtgt := solcCalldataRevertTgt cureBytecode)
    (opR := solcCalldataRevertTgtOp cureBytecode)
    (wR := solcCalldataRevertTgtWidth cureBytecode)
    h1 hsz (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by jump_dest) (by native_decide) (by native_decide) (by native_decide)

/-! ## Runtime dispatcher reachability -/

abbrev cureRootSplitPc : UInt256 := ⟨32⟩
abbrev cureMidSplitPc : UInt256 := ⟨43⟩
abbrev cureHighUpperFirstArmPc : UInt256 := ⟨54⟩
abbrev cureLowJumpdestPc : UInt256 := ⟨173⟩
abbrev cureLowSplitPc : UInt256 := ⟨174⟩
abbrev cureLowUpperFirstArmPc : UInt256 := ⟨185⟩
abbrev cureLowLowerJumpdestPc : UInt256 := ⟨244⟩
abbrev cureLowLowerFirstArmPc : UInt256 := ⟨245⟩
abbrev cureMidLowJumpdestPc : UInt256 := ⟨113⟩
abbrev cureMidLowFirstArmPc : UInt256 := ⟨114⟩
abbrev cureDispatchRevertPc : UInt256 := ⟨300⟩

theorem cureRootSplitWellFormed :
    selectorSplitWellFormed cureBytecode cureRootSplitPc := by
  dsimp [selectorSplitWellFormed]
  repeat' first | apply And.intro | native_decide

theorem cureMidSplitWellFormed :
    selectorSplitWellFormed cureBytecode cureMidSplitPc := by
  dsimp [selectorSplitWellFormed]
  repeat' first | apply And.intro | native_decide

theorem cureLowSplitWellFormed :
    selectorSplitWellFormed cureBytecode cureLowSplitPc := by
  dsimp [selectorSplitWellFormed]
  repeat' first | apply And.intro | native_decide

set_option maxHeartbeats 1000000 in
theorem cureMidLowArmsWellFormed :
    ∀ j, j ≤ 4 → armWellFormed cureBytecode
      (nthArmPc cureBytecode cureMidLowFirstArmPc j) := by
  intro j hj
  interval_cases j <;>
    (dsimp [armWellFormed]
     repeat' first | apply And.intro | native_decide)

set_option maxHeartbeats 1000000 in
theorem cureHighUpperArmsWellFormed :
    ∀ j, j ≤ 4 → armWellFormed cureBytecode
      (nthArmPc cureBytecode cureHighUpperFirstArmPc j) := by
  intro j hj
  interval_cases j <;>
    (dsimp [armWellFormed]
     repeat' first | apply And.intro | native_decide)

set_option maxHeartbeats 1000000 in
theorem cureLowUpperArmsWellFormed :
    ∀ j, j ≤ 4 → armWellFormed cureBytecode
      (nthArmPc cureBytecode cureLowUpperFirstArmPc j) := by
  intro j hj
  interval_cases j <;>
    (dsimp [armWellFormed]
     repeat' first | apply And.intro | native_decide)

set_option maxHeartbeats 1000000 in
theorem cureLowLowerArmsWellFormed :
    ∀ j, j ≤ 4 → armWellFormed cureBytecode
      (nthArmPc cureBytecode cureLowLowerFirstArmPc j) := by
  intro j hj
  interval_cases j <;>
    (dsimp [armWellFormed]
     repeat' first | apply And.intro | native_decide)

theorem cureSelWord_eq_of_beq (I : ExecutionEnv) (hsz : 4 ≤ I.calldata.size)
    (c0 c1 c2 c3 : UInt8) (sel : UInt256)
    (hsel : (fromBytesBigEndian [c0, c1, c2, c3] : ℕ) = sel.toNat)
    (hmatch : ((⟨#[c0, c1, c2, c3]⟩ : ByteArray) == I.calldata.extract 0 4) = true) :
    cureSelWord I = sel := by
  simpa [cureSelWord, solcSelectorWord] using
    solcSelectorWord_eq_of_beq I hsz c0 c1 c2 c3 sel hsel hmatch

theorem cureReachRootSplit {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = cureBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size) :
    ∃ k C, RD cureBytecode I g (initState cA gh bl σ σ₀ g A I) cureRootSplitPc
      [cureSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have h0 := solcGuardPrologueRD (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (g := g) hcode (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  obtain ⟨_, _, h1⟩ := solcGuardCallvalueZero
    (ctgt := solcGuardTgt cureBytecode) (opC := solcGuardTgtOp cureBytecode)
    (wC := solcGuardTgtWidth cureBytecode) h0 hwv
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by jump_dest)
  obtain ⟨_, _, hload⟩ := solcCalldataOk
    (bodyPc := solcDispatchBodyPc cureBytecode)
    (selLoadTgt := solcCalldataRevertTgt cureBytecode)
    (opR := solcCalldataRevertTgtOp cureBytecode)
    (wR := solcCalldataRevertTgtWidth cureBytecode)
    h1 hsz hsize (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  obtain ⟨k, C, hsplit⟩ := solcLegacySelectorLoad hload
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by simp only [List.length]; omega)
  exact ⟨k, C, by simpa [cureRootSplitPc, cureSelWord] using hsplit⟩

theorem cureReachMidSplit {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = cureBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot : UInt256.gt (armSelNat cureBytecode cureRootSplitPc) (cureSelWord I) = ⟨0⟩) :
    ∃ k C, RD cureBytecode I g (initState cA gh bl σ σ₀ g A I) cureMidSplitPc
      [cureSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, h32⟩ := cureReachRootSplit (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hwv hsz hsize
  exact ⟨_, _, by
    simpa [cureMidSplitPc, cureRootSplitPc, selArmNextPc, armTgtWidth] using
      RD.selectorSplitNotTakenAuto h32 cureRootSplitWellFormed hroot (by simp)⟩

theorem cureReachLowSplit {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = cureBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot : UInt256.gt (armSelNat cureBytecode cureRootSplitPc) (cureSelWord I) ≠ ⟨0⟩) :
    ∃ k C, RD cureBytecode I g (initState cA gh bl σ σ₀ g A I) cureLowSplitPc
      [cureSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, h32⟩ := cureReachRootSplit (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hwv hsz hsize
  have h173 := RD.selectorSplitTakenAuto h32 cureRootSplitWellFormed hroot (by jump_dest) (by simp)
  exact ⟨_, _, by
    simpa [cureLowSplitPc, cureLowJumpdestPc, cureRootSplitPc, armTgt, pushAt] using
      h173.jumpdest (by native_decide) (by simp only [List.length]; omega)⟩

theorem cureReachMidLowFirstArm {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = cureBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot : UInt256.gt (armSelNat cureBytecode cureRootSplitPc) (cureSelWord I) = ⟨0⟩)
    (hmid : UInt256.gt (armSelNat cureBytecode cureMidSplitPc) (cureSelWord I) ≠ ⟨0⟩) :
    ∃ k C, RD cureBytecode I g (initState cA gh bl σ σ₀ g A I) cureMidLowFirstArmPc
      [cureSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, h43⟩ := cureReachMidSplit (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot
  have h113 := RD.selectorSplitTakenAuto h43 cureMidSplitWellFormed hmid
    (by jump_dest) (by simp)
  exact ⟨_, _, by
    simpa [cureMidLowFirstArmPc, cureMidLowJumpdestPc, cureMidSplitPc, armTgt, pushAt] using
      h113.jumpdest (by native_decide) (by simp only [List.length]; omega)⟩

theorem cureReachHighUpperFirstArm {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = cureBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot : UInt256.gt (armSelNat cureBytecode cureRootSplitPc) (cureSelWord I) = ⟨0⟩)
    (hmid : UInt256.gt (armSelNat cureBytecode cureMidSplitPc) (cureSelWord I) = ⟨0⟩) :
    ∃ k C, RD cureBytecode I g (initState cA gh bl σ σ₀ g A I) cureHighUpperFirstArmPc
      [cureSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, h43⟩ := cureReachMidSplit (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot
  exact ⟨_, _, by
    simpa [cureHighUpperFirstArmPc, cureMidSplitPc, selArmNextPc, armTgtWidth] using
      RD.selectorSplitNotTakenAuto h43 cureMidSplitWellFormed hmid (by simp)⟩

theorem cureReachLowUpperFirstArm {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = cureBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot : UInt256.gt (armSelNat cureBytecode cureRootSplitPc) (cureSelWord I) ≠ ⟨0⟩)
    (hlow : UInt256.gt (armSelNat cureBytecode cureLowSplitPc) (cureSelWord I) = ⟨0⟩) :
    ∃ k C, RD cureBytecode I g (initState cA gh bl σ σ₀ g A I) cureLowUpperFirstArmPc
      [cureSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, h173⟩ := cureReachLowSplit (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot
  exact ⟨_, _, by
    simpa [cureLowUpperFirstArmPc, cureLowSplitPc, selArmNextPc, armTgtWidth] using
      RD.selectorSplitNotTakenAuto h173 cureLowSplitWellFormed hlow (by simp)⟩

theorem cureReachLowLowerFirstArm {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = cureBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hroot : UInt256.gt (armSelNat cureBytecode cureRootSplitPc) (cureSelWord I) ≠ ⟨0⟩)
    (hlow : UInt256.gt (armSelNat cureBytecode cureLowSplitPc) (cureSelWord I) ≠ ⟨0⟩) :
    ∃ k C, RD cureBytecode I g (initState cA gh bl σ σ₀ g A I) cureLowLowerFirstArmPc
      [cureSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, h173⟩ := cureReachLowSplit (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot
  have h244 := RD.selectorSplitTakenAuto h173 cureLowSplitWellFormed hlow
    (by jump_dest) (by simp)
  exact ⟨_, _, by
    simpa [cureLowLowerFirstArmPc, cureLowLowerJumpdestPc, cureLowSplitPc, armTgt, pushAt] using
      h244.jumpdest (by native_decide) (by simp only [List.length]; omega)⟩

theorem cureReachAmtBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = cureBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (cureSelBytes 0)) :
    ∃ k C, RD cureBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨305⟩
      [cureSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hsw : cureSelWord I = ⟨0x09615662⟩ :=
    cureSelWord_eq_of_beq I hsz 0x09 0x61 0x56 0x62 ⟨0x09615662⟩
      (by native_decide) (by simpa [cureSelBytes] using hsel)
  obtain ⟨_, _, h245⟩ := cureReachLowLowerFirstArm (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hwv hsz hsize
    (by rw [hsw]; native_decide) (by rw [hsw]; native_decide)
  exact RD.dispatchTo ⟨305⟩ 0 h245 (fun j hj => cureLowLowerArmsWellFormed j (by omega))
    (fun j hj => by omega)
    (by rw [hsw]; native_decide) (by jump_dest) (by native_decide) (by simp)

theorem cureReachListBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = cureBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (cureSelBytes 7)) :
    ∃ k C, RD cureBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨361⟩
      [cureSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hsw : cureSelWord I = ⟨0x0f560cd7⟩ :=
    cureSelWord_eq_of_beq I hsz 0x0f 0x56 0x0c 0xd7 ⟨0x0f560cd7⟩
      (by native_decide) (by simpa [cureSelBytes] using hsel)
  obtain ⟨_, _, h245⟩ := cureReachLowLowerFirstArm (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hwv hsz hsize
    (by rw [hsw]; native_decide) (by rw [hsw]; native_decide)
  exact RD.dispatchTo ⟨361⟩ 1 h245 (fun j hj => cureLowLowerArmsWellFormed j (by omega))
    (fun j hj => by interval_cases j; rw [hsw]; native_decide)
    (by rw [hsw]; native_decide) (by jump_dest) (by native_decide) (by simp)

theorem cureReachLoadBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = cureBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (cureSelBytes 9)) :
    ∃ k C, RD cureBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨486⟩
      [cureSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hsw : cureSelWord I = ⟨0x2f40e734⟩ :=
    cureSelWord_eq_of_beq I hsz 0x2f 0x40 0xe7 0x34 ⟨0x2f40e734⟩
      (by native_decide) (by simpa [cureSelBytes] using hsel)
  obtain ⟨_, _, h245⟩ := cureReachLowLowerFirstArm (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hwv hsz hsize
    (by rw [hsw]; native_decide) (by rw [hsw]; native_decide)
  exact RD.dispatchTo ⟨486⟩ 3 h245 (fun j hj => cureLowLowerArmsWellFormed j (by omega))
    (fun j hj => by
      interval_cases j
      · rw [hsw]; native_decide
      · rw [hsw]; native_decide
      · rw [hsw]; native_decide)
    (by rw [hsw]; native_decide) (by jump_dest) (by native_decide) (by simp)

theorem cureReachLiveBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = cureBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (cureSelBytes 8)) :
    ∃ k C, RD cureBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨724⟩
      [cureSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hsw : cureSelWord I = ⟨0x957aa58c⟩ :=
    cureSelWord_eq_of_beq I hsz 0x95 0x7a 0xa5 0x8c ⟨0x957aa58c⟩
      (by native_decide) (by simpa [cureSelBytes] using hsel)
  obtain ⟨_, _, h114⟩ := cureReachMidLowFirstArm (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hwv hsz hsize
    (by rw [hsw]; native_decide) (by rw [hsw]; native_decide)
  exact RD.dispatchTo ⟨724⟩ 4 h114 (fun j hj => cureMidLowArmsWellFormed j (by omega))
    (fun j hj => by interval_cases j <;> · rw [hsw]; native_decide)
    (by rw [hsw]; native_decide) (by jump_dest) (by native_decide) (by simp)

theorem cureReachDropBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = cureBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (cureSelBytes 3)) :
    ∃ k C, RD cureBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨640⟩
      [cureSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hsw : cureSelWord I = ⟨0x91f2700a⟩ :=
    cureSelWord_eq_of_beq I hsz 0x91 0xf2 0x70 0x0a ⟨0x91f2700a⟩
      (by native_decide) (by simpa [cureSelBytes] using hsel)
  obtain ⟨_, _, h114⟩ := cureReachMidLowFirstArm (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hwv hsz hsize
    (by rw [hsw]; native_decide) (by rw [hsw]; native_decide)
  exact RD.dispatchTo ⟨640⟩ 1 h114 (fun j hj => cureMidLowArmsWellFormed j (by omega))
    (fun j hj => by interval_cases j; rw [hsw]; native_decide)
    (by rw [hsw]; native_decide) (by jump_dest) (by native_decide) (by simp)

theorem cureReachSayBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = cureBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (cureSelBytes 13)) :
    ∃ k C, RD cureBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨716⟩
      [cureSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hsw : cureSelWord I = ⟨0x954ab4b2⟩ :=
    cureSelWord_eq_of_beq I hsz 0x95 0x4a 0xb4 0xb2 ⟨0x954ab4b2⟩
      (by native_decide) (by simpa [cureSelBytes] using hsel)
  obtain ⟨_, _, h114⟩ := cureReachMidLowFirstArm (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hwv hsz hsize
    (by rw [hsw]; native_decide) (by rw [hsw]; native_decide)
  exact RD.dispatchTo ⟨716⟩ 3 h114 (fun j hj => cureMidLowArmsWellFormed j (by omega))
    (fun j hj => by interval_cases j <;> · rw [hsw]; native_decide)
    (by rw [hsw]; native_decide) (by jump_dest) (by native_decide) (by simp)

theorem cureReachLCountBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = cureBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (cureSelBytes 5)) :
    ∃ k C, RD cureBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨562⟩
      [cureSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hsw : cureSelWord I = ⟨0x493aa4c7⟩ :=
    cureSelWord_eq_of_beq I hsz 0x49 0x3a 0xa4 0xc7 ⟨0x493aa4c7⟩
      (by native_decide) (by simpa [cureSelBytes] using hsel)
  obtain ⟨_, _, h185⟩ := cureReachLowUpperFirstArm (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hwv hsz hsize
    (by rw [hsw]; native_decide) (by rw [hsw]; native_decide)
  exact RD.dispatchTo ⟨562⟩ 0 h185 (fun j hj => cureLowUpperArmsWellFormed j (by omega))
    (fun j hj => by omega)
    (by rw [hsw]; native_decide) (by jump_dest) (by native_decide) (by simp)

theorem cureReachTCountBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = cureBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (cureSelBytes 15)) :
    ∃ k C, RD cureBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨578⟩
      [cureSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hsw : cureSelWord I = ⟨0x53f9a873⟩ :=
    cureSelWord_eq_of_beq I hsz 0x53 0xf9 0xa8 0x73 ⟨0x53f9a873⟩
      (by native_decide) (by simpa [cureSelBytes] using hsel)
  obtain ⟨_, _, h185⟩ := cureReachLowUpperFirstArm (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hwv hsz hsize
    (by rw [hsw]; native_decide) (by rw [hsw]; native_decide)
  exact RD.dispatchTo ⟨578⟩ 2 h185 (fun j hj => cureLowUpperArmsWellFormed j (by omega))
    (fun j hj => by interval_cases j <;> · rw [hsw]; native_decide)
    (by rw [hsw]; native_decide) (by jump_dest) (by native_decide) (by simp)

theorem cureReachWaitBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = cureBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (cureSelBytes 17)) :
    ∃ k C, RD cureBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨586⟩
      [cureSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hsw : cureSelWord I = ⟨0x64bd7013⟩ :=
    cureSelWord_eq_of_beq I hsz 0x64 0xbd 0x70 0x13 ⟨0x64bd7013⟩
      (by native_decide) (by simpa [cureSelBytes] using hsel)
  obtain ⟨_, _, h185⟩ := cureReachLowUpperFirstArm (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hwv hsz hsize
    (by rw [hsw]; native_decide) (by rw [hsw]; native_decide)
  exact RD.dispatchTo ⟨586⟩ 3 h185 (fun j hj => cureLowUpperArmsWellFormed j (by omega))
    (fun j hj => by interval_cases j <;> · rw [hsw]; native_decide)
    (by rw [hsw]; native_decide) (by jump_dest) (by native_decide) (by simp)

theorem cureReachWhenBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = cureBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (cureSelBytes 19)) :
    ∃ k C, RD cureBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨808⟩
      [cureSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hsw : cureSelWord I = ⟨0xe2b0caef⟩ :=
    cureSelWord_eq_of_beq I hsz 0xe2 0xb0 0xca 0xef ⟨0xe2b0caef⟩
      (by native_decide) (by simpa [cureSelBytes] using hsel)
  obtain ⟨_, _, h54⟩ := cureReachHighUpperFirstArm (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hwv hsz hsize
    (by rw [hsw]; native_decide) (by rw [hsw]; native_decide)
  exact RD.dispatchTo ⟨808⟩ 2 h54 (fun j hj => cureHighUpperArmsWellFormed j (by omega))
    (fun j hj => by interval_cases j <;> · rw [hsw]; native_decide)
    (by rw [hsw]; native_decide) (by jump_dest) (by native_decide) (by simp)

theorem cureReachWardsBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = cureBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (cureSelBytes 18)) :
    ∃ k C, RD cureBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨770⟩
      [cureSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hsw : cureSelWord I = ⟨0xbf353dbb⟩ :=
    cureSelWord_eq_of_beq I hsz 0xbf 0x35 0x3d 0xbb ⟨0xbf353dbb⟩
      (by native_decide) (by simpa [cureSelBytes] using hsel)
  obtain ⟨_, _, h54⟩ := cureReachHighUpperFirstArm (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hwv hsz hsize
    (by rw [hsw]; native_decide) (by rw [hsw]; native_decide)
  exact RD.dispatchTo ⟨770⟩ 1 h54 (fun j hj => cureHighUpperArmsWellFormed j (by omega))
    (fun j hj => by
      interval_cases j
      · rw [hsw]; native_decide)
    (by rw [hsw]; native_decide) (by jump_dest) (by native_decide) (by simp)

theorem cureReachPosBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = cureBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (cureSelBytes 11)) :
    ∃ k C, RD cureBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨678⟩
      [cureSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hsw : cureSelWord I = ⟨0x93d0281c⟩ :=
    cureSelWord_eq_of_beq I hsz 0x93 0xd0 0x28 0x1c ⟨0x93d0281c⟩
      (by native_decide) (by simpa [cureSelBytes] using hsel)
  obtain ⟨_, _, h114⟩ := cureReachMidLowFirstArm (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hwv hsz hsize
    (by rw [hsw]; native_decide) (by rw [hsw]; native_decide)
  exact RD.dispatchTo ⟨678⟩ 2 h114 (fun j hj => cureMidLowArmsWellFormed j (by omega))
    (fun j hj => by interval_cases j <;> · rw [hsw]; native_decide)
    (by rw [hsw]; native_decide) (by jump_dest) (by native_decide) (by simp)

theorem cureReachLoadedBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = cureBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (cureSelBytes 10)) :
    ∃ k C, RD cureBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨873⟩
      [cureSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hsw : cureSelWord I = ⟨0xffa9ca9f⟩ :=
    cureSelWord_eq_of_beq I hsz 0xff 0xa9 0xca 0x9f ⟨0xffa9ca9f⟩
      (by native_decide) (by simpa [cureSelBytes] using hsel)
  obtain ⟨_, _, h54⟩ := cureReachHighUpperFirstArm (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hwv hsz hsize
    (by rw [hsw]; native_decide) (by rw [hsw]; native_decide)
  exact RD.dispatchTo ⟨873⟩ 4 h54 (fun j hj => cureHighUpperArmsWellFormed j (by omega))
    (fun j hj => by interval_cases j <;> · rw [hsw]; native_decide)
    (by rw [hsw]; native_decide) (by jump_dest) (by native_decide) (by simp)

theorem cureJumpToNoMatchRevert {cA gh bl σ σ₀ A I} {g : Sat256} {pc : UInt256}
    {k C : ℕ}
    (h : RD cureBytecode I g (initState cA gh bl σ σ₀ g A I) pc
      [cureSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hpush : decode cureBytecode pc = some (.Push .PUSH2, some (cureDispatchRevertPc, 2)))
    (hjump : decode cureBytecode (pc + UInt256.ofNat 3) = some (.JUMP, .none)) :
    RDrev cureBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have h300 := h.push2 cureDispatchRevertPc hpush (by simp only [List.length_singleton]; omega)
    |>.jump hjump (by jump_dest) (by simp only [List.length_singleton]; omega)
    |>.jumpdest (by native_decide) (by simp only [List.length_singleton]; omega)
  exact RD.solcPush1Dup1Revert0 h300 (by native_decide) (by native_decide)
    (by native_decide) (by simp only [List.length_singleton]; omega)

theorem cureLowLowerNoMatchRevert {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ}
    (h : RD cureBytecode I g (initState cA gh bl σ σ₀ g A I) cureLowLowerFirstArmPc
      [cureSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (heq0 : ∀ j, j < 5 →
      UInt256.eq (armSelNat cureBytecode (nthArmPc cureBytecode cureLowLowerFirstArmPc j))
        (cureSelWord I) = ⟨0⟩) :
    RDrev cureBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have h300 := h
    |>.selectorArmNotTakenAuto (cureLowLowerArmsWellFormed 0 (by omega))
        (heq0 0 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (cureLowLowerArmsWellFormed 1 (by omega))
        (heq0 1 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (cureLowLowerArmsWellFormed 2 (by omega))
        (heq0 2 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (cureLowLowerArmsWellFormed 3 (by omega))
        (heq0 3 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (cureLowLowerArmsWellFormed 4 (by omega))
        (heq0 4 (by omega)) (by simp)
    |>.jumpdest (by native_decide) (by simp only [List.length_singleton]; omega)
  exact RD.solcPush1Dup1Revert0 h300 (by native_decide) (by native_decide)
    (by native_decide) (by simp only [List.length_singleton]; omega)

theorem cureLowUpperNoMatchRevert {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ}
    (h : RD cureBytecode I g (initState cA gh bl σ σ₀ g A I) cureLowUpperFirstArmPc
      [cureSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (heq0 : ∀ j, j < 5 →
      UInt256.eq (armSelNat cureBytecode (nthArmPc cureBytecode cureLowUpperFirstArmPc j))
        (cureSelWord I) = ⟨0⟩) :
    RDrev cureBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have h240 := h
    |>.selectorArmNotTakenAuto (cureLowUpperArmsWellFormed 0 (by omega))
        (heq0 0 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (cureLowUpperArmsWellFormed 1 (by omega))
        (heq0 1 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (cureLowUpperArmsWellFormed 2 (by omega))
        (heq0 2 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (cureLowUpperArmsWellFormed 3 (by omega))
        (heq0 3 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (cureLowUpperArmsWellFormed 4 (by omega))
        (heq0 4 (by omega)) (by simp)
  exact cureJumpToNoMatchRevert h240 (by native_decide) (by native_decide)

theorem cureMidLowNoMatchRevert {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ}
    (h : RD cureBytecode I g (initState cA gh bl σ σ₀ g A I) cureMidLowFirstArmPc
      [cureSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (heq0 : ∀ j, j < 5 →
      UInt256.eq (armSelNat cureBytecode (nthArmPc cureBytecode cureMidLowFirstArmPc j))
        (cureSelWord I) = ⟨0⟩) :
    RDrev cureBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have h169 := h
    |>.selectorArmNotTakenAuto (cureMidLowArmsWellFormed 0 (by omega))
        (heq0 0 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (cureMidLowArmsWellFormed 1 (by omega))
        (heq0 1 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (cureMidLowArmsWellFormed 2 (by omega))
        (heq0 2 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (cureMidLowArmsWellFormed 3 (by omega))
        (heq0 3 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (cureMidLowArmsWellFormed 4 (by omega))
        (heq0 4 (by omega)) (by simp)
  exact cureJumpToNoMatchRevert h169 (by native_decide) (by native_decide)

theorem cureHighUpperNoMatchRevert {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ}
    (h : RD cureBytecode I g (initState cA gh bl σ σ₀ g A I) cureHighUpperFirstArmPc
      [cureSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (heq0 : ∀ j, j < 5 →
      UInt256.eq (armSelNat cureBytecode (nthArmPc cureBytecode cureHighUpperFirstArmPc j))
        (cureSelWord I) = ⟨0⟩) :
    RDrev cureBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have h109 := h
    |>.selectorArmNotTakenAuto (cureHighUpperArmsWellFormed 0 (by omega))
        (heq0 0 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (cureHighUpperArmsWellFormed 1 (by omega))
        (heq0 1 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (cureHighUpperArmsWellFormed 2 (by omega))
        (heq0 2 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (cureHighUpperArmsWellFormed 3 (by omega))
        (heq0 3 (by omega)) (by simp)
    |>.selectorArmNotTakenAuto (cureHighUpperArmsWellFormed 4 (by omega))
        (heq0 4 (by omega)) (by simp)
  exact cureJumpToNoMatchRevert h109 (by native_decide) (by native_decide)

theorem cureNonPayable {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = cureBytecode) (hwv : I.weiValue ≠ ⟨0⟩)
    (_hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  exact (cureX_callvalue_ne (g := Sat256.ofUInt256 g) hcode hwv).reEquivElim hcode
    fun _ _ hrev => by
      by_cases hdisp : dispatchMsg contract I.calldata = none
      · exact reEquiv_noDispatch hdisp hrev
      · obtain ⟨t, ht⟩ := Option.ne_none_iff_exists'.mp hdisp
        have htmem : t ∈ contract.transitions := by
          rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl)] at ht
          exact dispatchList_some_mem ht
        by_cases hdec : decodeCalldataWithMode config.abiDecodeMode (t.params.map Param.name)
            (transitionSignature t).paramTypes I.calldata = none
        · exact reEquiv_decodingFailed ht hdec hrev
        · obtain ⟨callargs, hca⟩ := Option.ne_none_iff_exists'.mp hdec
          exact reEquiv_execution ht hca
            (cureBodyReverts_nonPayable t htmem
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
              callargs (by simp only [initState]; exact hwv))
            (by rw [hrev]; exact execResultsEquiv.revert rfl rfl)

/-- With enough calldata for a selector but no selector match, Cure's dispatcher reverts. -/
theorem cureX_noMatch {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = cureBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hnm : ∀ i, i < 20 → (cureSelBytes i == I.calldata.extract 0 4) = false) :
    RDrev cureBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hselectorNoMatch (i : ℕ) (hi : i < 20) (c0 c1 c2 c3 : UInt8) (sel : UInt256)
      (hsel : (fromBytesBigEndian [c0, c1, c2, c3] : ℕ) = sel.toNat)
      (hbytes : cureSelBytes i = (⟨#[c0, c1, c2, c3]⟩ : ByteArray)) :
      UInt256.eq sel (cureSelWord I) = ⟨0⟩ := by
    dsimp [cureSelWord]
    rw [evmSelectorDecode hsz c0 c1 c2 c3 sel hsel]
    have hno := hnm i hi
    rw [hbytes] at hno
    simp [hno]
  have heqLowLower : ∀ j, j < 5 →
      UInt256.eq
        (armSelNat cureBytecode (nthArmPc cureBytecode cureLowLowerFirstArmPc j))
        (cureSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j
    · exact hselectorNoMatch 0 (by omega) 0x09 0x61 0x56 0x62 _ (by native_decide) rfl
    · exact hselectorNoMatch 7 (by omega) 0x0f 0x56 0x0c 0xd7 _ (by native_decide) rfl
    · exact hselectorNoMatch 4 (by omega) 0x29 0xae 0x81 0x14 _ (by native_decide) rfl
    · exact hselectorNoMatch 9 (by omega) 0x2f 0x40 0xe7 0x34 _ (by native_decide) rfl
    · exact hselectorNoMatch 6 (by omega) 0x3c 0x27 0x8b 0xd5 _ (by native_decide) rfl
  have heqLowUpper : ∀ j, j < 5 →
      UInt256.eq
        (armSelNat cureBytecode (nthArmPc cureBytecode cureLowUpperFirstArmPc j))
        (cureSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j
    · exact hselectorNoMatch 5 (by omega) 0x49 0x3a 0xa4 0xc7 _ (by native_decide) rfl
    · exact hselectorNoMatch 16 (by omega) 0x53 0xd7 0x00 0xe5 _ (by native_decide) rfl
    · exact hselectorNoMatch 15 (by omega) 0x53 0xf9 0xa8 0x73 _ (by native_decide) rfl
    · exact hselectorNoMatch 17 (by omega) 0x64 0xbd 0x70 0x13 _ (by native_decide) rfl
    · exact hselectorNoMatch 12 (by omega) 0x65 0xfa 0xe3 0x5e _ (by native_decide) rfl
  have heqMidLow : ∀ j, j < 5 →
      UInt256.eq
        (armSelNat cureBytecode (nthArmPc cureBytecode cureMidLowFirstArmPc j))
        (cureSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j
    · exact hselectorNoMatch 1 (by omega) 0x69 0x24 0x50 0x09 _ (by native_decide) rfl
    · exact hselectorNoMatch 3 (by omega) 0x91 0xf2 0x70 0x0a _ (by native_decide) rfl
    · exact hselectorNoMatch 11 (by omega) 0x93 0xd0 0x28 0x1c _ (by native_decide) rfl
    · exact hselectorNoMatch 13 (by omega) 0x95 0x4a 0xb4 0xb2 _ (by native_decide) rfl
    · exact hselectorNoMatch 8 (by omega) 0x95 0x7a 0xa5 0x8c _ (by native_decide) rfl
  have heqHighUpper : ∀ j, j < 5 →
      UInt256.eq
        (armSelNat cureBytecode (nthArmPc cureBytecode cureHighUpperFirstArmPc j))
        (cureSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j
    · exact hselectorNoMatch 2 (by omega) 0x9c 0x52 0xa7 0xf1 _ (by native_decide) rfl
    · exact hselectorNoMatch 18 (by omega) 0xbf 0x35 0x3d 0xbb _ (by native_decide) rfl
    · exact hselectorNoMatch 19 (by omega) 0xe2 0xb0 0xca 0xef _ (by native_decide) rfl
    · exact hselectorNoMatch 14 (by omega) 0xf3 0x81 0x27 0x3f _ (by native_decide) rfl
    · exact hselectorNoMatch 10 (by omega) 0xff 0xa9 0xca 0x9f _ (by native_decide) rfl
  by_cases hroot : UInt256.gt (armSelNat cureBytecode cureRootSplitPc) (cureSelWord I) = ⟨0⟩
  · by_cases hmid : UInt256.gt (armSelNat cureBytecode cureMidSplitPc) (cureSelWord I) = ⟨0⟩
    · obtain ⟨_, _, hfirst⟩ := cureReachHighUpperFirstArm (cA := cA) (gh := gh)
        (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
        hcode hwv hsz hsize hroot hmid
      exact cureHighUpperNoMatchRevert hfirst heqHighUpper
    · obtain ⟨_, _, hfirst⟩ := cureReachMidLowFirstArm (cA := cA) (gh := gh)
        (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
        hcode hwv hsz hsize hroot hmid
      exact cureMidLowNoMatchRevert hfirst heqMidLow
  · by_cases hlow : UInt256.gt (armSelNat cureBytecode cureLowSplitPc) (cureSelWord I) = ⟨0⟩
    · obtain ⟨_, _, hfirst⟩ := cureReachLowUpperFirstArm (cA := cA) (gh := gh)
        (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
        hcode hwv hsz hsize hroot hlow
      exact cureLowUpperNoMatchRevert hfirst heqLowUpper
    · obtain ⟨_, _, hfirst⟩ := cureReachLowLowerFirstArm (cA := cA) (gh := gh)
        (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
        hcode hwv hsz hsize hroot hlow
      exact cureLowLowerNoMatchRevert hfirst heqLowLower

theorem cureNoDispatch {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = cureBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hnm : ∀ i, i < 20 → (cureSelBytes i == I.calldata.extract 0 4) = false)
    (_hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  by_cases hsz : 4 ≤ I.calldata.size
  · exact (cureX_noMatch (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hnm)
      |>.reEquivNoDispatch hcode (cureDispatch_none_nomatch hnm)
  · have hshort : I.calldata.size < 4 := by omega
    exact (cureX_short (g := Sat256.ofUInt256 g) hcode hwv hshort)
      |>.reEquivNoDispatch hcode (cureDispatch_none_short hshort)

theorem cureNoSelectorMatches {I : ExecutionEnv}
    (hamt : ¬ selIs I (cureSelBytes 0))
    (hcage : ¬ selIs I (cureSelBytes 1))
    (hdeny : ¬ selIs I (cureSelBytes 2))
    (hdrop : ¬ selIs I (cureSelBytes 3))
    (hfile : ¬ selIs I (cureSelBytes 4))
    (hlCount : ¬ selIs I (cureSelBytes 5))
    (hlift : ¬ selIs I (cureSelBytes 6))
    (hlist : ¬ selIs I (cureSelBytes 7))
    (hlive : ¬ selIs I (cureSelBytes 8))
    (hload : ¬ selIs I (cureSelBytes 9))
    (hloaded : ¬ selIs I (cureSelBytes 10))
    (hpos : ¬ selIs I (cureSelBytes 11))
    (hrely : ¬ selIs I (cureSelBytes 12))
    (hsay : ¬ selIs I (cureSelBytes 13))
    (hsrcs : ¬ selIs I (cureSelBytes 14))
    (htCount : ¬ selIs I (cureSelBytes 15))
    (htell : ¬ selIs I (cureSelBytes 16))
    (hwait : ¬ selIs I (cureSelBytes 17))
    (hwards : ¬ selIs I (cureSelBytes 18))
    (hwhen : ¬ selIs I (cureSelBytes 19)) :
    ∀ i, i < 20 → (cureSelBytes i == I.calldata.extract 0 4) = false := by
  intro i hi
  interval_cases i
  · simpa [selIs, cureSelBytes] using hamt
  · simpa [selIs, cureSelBytes] using hcage
  · simpa [selIs, cureSelBytes] using hdeny
  · simpa [selIs, cureSelBytes] using hdrop
  · simpa [selIs, cureSelBytes] using hfile
  · simpa [selIs, cureSelBytes] using hlCount
  · simpa [selIs, cureSelBytes] using hlift
  · simpa [selIs, cureSelBytes] using hlist
  · simpa [selIs, cureSelBytes] using hlive
  · simpa [selIs, cureSelBytes] using hload
  · simpa [selIs, cureSelBytes] using hloaded
  · simpa [selIs, cureSelBytes] using hpos
  · simpa [selIs, cureSelBytes] using hrely
  · simpa [selIs, cureSelBytes] using hsay
  · simpa [selIs, cureSelBytes] using hsrcs
  · simpa [selIs, cureSelBytes] using htCount
  · simpa [selIs, cureSelBytes] using htell
  · simpa [selIs, cureSelBytes] using hwait
  · simpa [selIs, cureSelBytes] using hwards
  · simpa [selIs, cureSelBytes] using hwhen

end Benchmarks.Dss.Cure
