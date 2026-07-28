import Benchmarks.Dss.LinearDecrease.Bytecode
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
# MakerDAO/Sky DSS LinearDecrease shared proof foundation

Contract-wide selector notation and constants for the optimized runtime.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.LinearDecrease

/-- The 4-byte selector word computed by `CALLDATALOAD(0); SHR 224`. -/
abbrev stairstepSelWord (I : ExecutionEnv) : UInt256 :=
  UInt256.shiftRight (uInt256OfByteArray (I.calldata.readBytes 0 32)) ⟨224⟩

/-- The 4-byte selector of `I`'s calldata equals `sel`. -/
abbrev selIs (I : ExecutionEnv) (sel : ByteArray) : Prop :=
  (sel == I.calldata.extract 0 4) = true

/-- Function selectors in `contract.transitions` order. -/
def stairstepSelBytes : ℕ → ByteArray
  | 0 => ⟨#[0x9c, 0x52, 0xa7, 0xf1]⟩ -- deny(address)
  | 1 => ⟨#[0x29, 0xae, 0x81, 0x14]⟩ -- file(bytes32,uint256)
  | 2 => ⟨#[0x48, 0x7a, 0x23, 0x95]⟩ -- price(uint256,uint256)
  | 3 => ⟨#[0x65, 0xfa, 0xe3, 0x5e]⟩ -- rely(address)
  | 4 => ⟨#[0xcf, 0xc4, 0xaf, 0x55]⟩ -- tau()
  | _ => ⟨#[0xbf, 0x35, 0x3d, 0xbb]⟩ -- wards(address)

def stairstepSlotWord (slot : UInt256) (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  solcSlotWord σ I slot

theorem stairstepStorageLocLoad_uint256 (evm : EVM.State) (slot : UInt256) :
    storageLocLoad evm (wordLoc slot) =
      .int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot).toNat) := by
  simpa [wordLoc, uint256Loc] using storageLocLoad_uint256 evm slot

theorem stairstepStorageLocStore_uint256 (evm : EVM.State) (slot val : UInt256) :
    storageLocStore evm (wordLoc slot) (.int (Int.ofNat val.toNat)) =
      some (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot val) := by
  simpa [wordLoc, uint256Loc] using storageLocStore_uint256 evm slot val

theorem stairstepUint256GetterBodyReturns (evm : EVM.State) (locals : Store)
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
      exact congrArg EvalResult.ok (stairstepStorageLocLoad_uint256 evm slot))

theorem stairstepUint256GetterBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    {transition : TransitionDecl} {entry returnPc routine slot : UInt256}
    (hcode : I.code = linearDecreaseBytecode)
    (hdispatch : dispatchMsg contract I.calldata = some transition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (transition.params.map Param.name)
        (transitionSignature transition).paramTypes I.calldata = some ∅)
    (hreach : ∃ k C, RD linearDecreaseBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) entry [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hentry : solcGetterEntryWf linearDecreaseBytecode entry returnPc routine)
    (hgetter : solcWordSlotGetterWf linearDecreaseBytecode routine slot)
    (hroutine : (D_J linearDecreaseBytecode 0).contains routine = true)
    (hreturnJd : (D_J linearDecreaseBytecode 0).contains returnPc = true)
    (hretmem : solcReturnWordFromMemWf linearDecreaseBytecode returnPc)
    (hreturn : transition.returnType = [uint256])
    (hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) ∅ transition.body
        (.returned { contract := contract, locals := ∅ }
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (some [(.int (Int.ofNat (stairstepSlotWord slot σ_solm I).toNat))]))) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hword : stairstepSlotWord slot σ_evm I = stairstepSlotWord slot σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner slot ⟨0⟩
  have hval :
      some [Value.int (Int.ofNat (stairstepSlotWord slot σ_solm I).toNat)] =
        some [Value.int (Int.ofNat (stairstepSlotWord slot σ_evm I).toNat)] := by
    rw [hword]
  have henc :
      returnEquiv (UInt256.toByteArray (stairstepSlotWord slot σ_evm I))
        (some [(.int (Int.ofNat (stairstepSlotWord slot σ_evm I).toNat))])
        transition.returnType := by
    rw [hreturn]
    exact returnEquiv_of_encode
      (by simpa [uint256] using uint256ReturnEncoding (stairstepSlotWord slot σ_evm I))
  have hret := RD.solcWordGetterExternal
    (code := linearDecreaseBytecode) (g := Sat256.ofUInt256 g)
    (returnPc := returnPc) (entry := entry) (routine := routine) (slot := slot)
    hreach hentry hgetter hroutine hreturnJd hretmem
  have hret' :
      RDret linearDecreaseBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) (cA, σ_evm)
        (UInt256.toByteArray (stairstepSlotWord slot σ_evm I)) := by
    simpa [stairstepSlotWord] using hret
  exact hret'.reEquivExecutionTransport hcode hdispatch hdecode hbody hval hAccounts henc

-- GENERALIZES Benchmarks.Dss.Jug.solcZeroSlotMappingGetterWf — move to Reasoning by
-- parameterizing over the bytecode and mapping base slot.
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

-- GENERALIZES Benchmarks.Dss.Jug.RD.solcZeroSlotMappingGetter — move to Reasoning with
-- `solcZeroSlotMappingGetterWf`.
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

-- LIBRARY CANDIDATE: move to `Reasoning.Reach` beside terminal `RDret`/`RDrev` helpers.
theorem RD.invalidError {code : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {pc : UInt256} {stk : List UInt256} {mem : ByteArray}
    {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (h : RD code ee g s0 pc stk mem aw rdata acc k C)
    (hdec : decode code pc = some (.INVALID, .none)) :
    X (g.toNat + 1) (D_J code 0) s0 = .error .OutOfGass ∨
      X (g.toNat + 1) (D_J code 0) s0 = .error .InvalidInstruction := by
  rcases RD.conclude h with hoog | ⟨k', C', s', hX, hcode, hpc, _hstk, _hgas, hk, hC,
    _hmem, _haw, _hrdata, _hacc⟩
  · exact Or.inl hoog
  · have hdec' : decode s'.executionEnv.code s'.machineState.pc = some (.INVALID, .none) := by
      rw [hcode, hpc]
      exact hdec
    have hstep : Xstep (D_J code 0) s' = .error .InvalidInstruction := by
      have hstep' := Ethereum.EVM.step_invalid s' hdec'
      simpa [hcode] using hstep'
    have hfuel : g.toNat + 1 - k' = (g.toNat + 1 - (k' + 1)) + 1 := by
      omega
    exact Or.inr (by
      rw [hX, hfuel]
      exact Ethereum.EVM.Xstep_X_X_except _ s' _ _ hstep)

/-! ### LOG2

The reasoning library has LOG1/LOG3/LOG4 combinators; this contract emits two-topic auth logs.
-/

-- LIBRARY CANDIDATE: move to `Reasoning.Reach` beside `RD.log1`, `RD.log3`, and `RD.log4`.
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

-- LIBRARY CANDIDATE: move to `Reasoning.Stepping` with `stLog2`.
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

-- LIBRARY CANDIDATE: move to `Reasoning.Reach` beside `RD.log1`, `RD.log3`, and `RD.log4`.
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

/-! ### CODECOPY-backed `Error(string)` revert tail

This optimized artifact keeps the long auth error string in the deployed code and copies it
into the ABI error payload with `CODECOPY`.
-/

-- LIBRARY CANDIDATE: move beside `solcErrorStringMem3_read64`.
theorem solcErrorStringMem2_read64 (len : UInt256) {mem : ByteArray}
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (solcErrorStringMem2 len mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold solcErrorStringMem2
  rw [toByteArray_write_read_below_of_gap len _ 164 64
      (by rw [solcErrorStringMem1_size hmem]; omega) (by omega)
      (by rw [solcErrorStringMem1_size hmem]; exact lt_usize _ (by norm_num))]
  unfold solcErrorStringMem1
  rw [toByteArray_write_read_below_of_gap (⟨32⟩ : UInt256) _ 132 64
      (by rw [solcErrorStringMem0_size hmem]; omega) (by omega)
      (by rw [solcErrorStringMem0_size hmem]; exact lt_usize _ (by norm_num))]
  unfold solcErrorStringMem0
  rw [toByteArray_write_read_below_of_gap solcErrorStringSelector _ 128 64
      (by omega) (by omega) (by rw [hmem]; exact lt_usize _ (by norm_num))]
  exact hread64

@[reducible] def stairstepInlineErrorStringRevertTailWf
    (pc len word : UInt256) : Prop :=
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
  decode linearDecreaseBytecode pc = some (.Push .PUSH1, some (⟨64⟩, 1))
  ∧ decode linearDecreaseBytecode p2 = some (.DUP1, .none)
  ∧ decode linearDecreaseBytecode p3 = some (.MLOAD, .none)
  ∧ decode linearDecreaseBytecode p4 =
      some (.Push .PUSH3, some (⟨4594637⟩, 3))
  ∧ decode linearDecreaseBytecode p8 =
      some (.Push .PUSH1, some (⟨229⟩, 1))
  ∧ decode linearDecreaseBytecode p10 = some (.SHL, .none)
  ∧ decode linearDecreaseBytecode p11 = some (.DUP2, .none)
  ∧ decode linearDecreaseBytecode p12 = some (.MSTORE, .none)
  ∧ decode linearDecreaseBytecode p13 =
      some (.Push .PUSH1, some (⟨32⟩, 1))
  ∧ decode linearDecreaseBytecode p15 =
      some (.Push .PUSH1, some (⟨4⟩, 1))
  ∧ decode linearDecreaseBytecode p17 = some (.DUP3, .none)
  ∧ decode linearDecreaseBytecode p18 = some (.ADD, .none)
  ∧ decode linearDecreaseBytecode p19 = some (.MSTORE, .none)
  ∧ decode linearDecreaseBytecode p20 =
      some (.Push .PUSH1, some (len, 1))
  ∧ decode linearDecreaseBytecode p22 =
      some (.Push .PUSH1, some (⟨36⟩, 1))
  ∧ decode linearDecreaseBytecode p24 = some (.DUP3, .none)
  ∧ decode linearDecreaseBytecode p25 = some (.ADD, .none)
  ∧ decode linearDecreaseBytecode p26 = some (.MSTORE, .none)
  ∧ decode linearDecreaseBytecode p27 =
      some (.Push .PUSH32, some (word, 32))
  ∧ decode linearDecreaseBytecode p60 =
      some (.Push .PUSH1, some (⟨68⟩, 1))
  ∧ decode linearDecreaseBytecode p62 = some (.DUP3, .none)
  ∧ decode linearDecreaseBytecode p63 = some (.ADD, .none)
  ∧ decode linearDecreaseBytecode p64 = some (.MSTORE, .none)
  ∧ decode linearDecreaseBytecode p65 = some (.SWAP1, .none)
  ∧ decode linearDecreaseBytecode p66 = some (.MLOAD, .none)
  ∧ decode linearDecreaseBytecode p67 = some (.SWAP1, .none)
  ∧ decode linearDecreaseBytecode p68 = some (.DUP2, .none)
  ∧ decode linearDecreaseBytecode p69 = some (.SWAP1, .none)
  ∧ decode linearDecreaseBytecode p70 = some (.SUB, .none)
  ∧ decode linearDecreaseBytecode p71 =
      some (.Push .PUSH1, some (⟨100⟩, 1))
  ∧ decode linearDecreaseBytecode p73 = some (.ADD, .none)
  ∧ decode linearDecreaseBytecode p74 = some (.SWAP1, .none)
  ∧ decode linearDecreaseBytecode p75 = some (.REVERT, .none)

set_option maxHeartbeats 1000000 in
theorem RD.stairstepInlineErrorStringRevertTail {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {pc : UInt256}
    {len word : UInt256} {stk : List UInt256} {mem rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD linearDecreaseBytecode ee g s0 pc stk mem
        (UInt256.ofNat 3) rdata acc k C)
    (hwf : stairstepInlineErrorStringRevertTailWf pc len word)
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hov : stk.length + 5 ≤ 1024) :
    RDrev linearDecreaseBytecode g s0 := by
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

/-! The same tail, parameterized by the string window in the deployed code. -/

noncomputable def stairstepCodecopyErrorMem (offset len : UInt256)
    (mem : ByteArray) : ByteArray :=
  linearDecreaseBytecode.write offset.toNat
    (solcErrorStringMem2 len mem) 196 len.toNat

theorem stairstepCodecopyErrorMem_size {mem : ByteArray} (offset len : UInt256)
    (hmem : mem.size = 96) (hlen : len.toNat ≠ 0)
    (hsrc : offset.toNat + len.toNat ≤ linearDecreaseBytecode.size) :
    (stairstepCodecopyErrorMem offset len mem).size = 196 + len.toNat := by
  unfold stairstepCodecopyErrorMem
  rw [show 196 = (solcErrorStringMem2 len mem).size by
    rw [solcErrorStringMem2_size len hmem]]
  rw [write_end_size_from linearDecreaseBytecode
    (solcErrorStringMem2 len mem) offset.toNat len.toNat hlen hsrc]

theorem stairstepCodecopyErrorMem_read64 {mem : ByteArray} (offset len : UInt256)
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hlen : len.toNat ≠ 0)
    (hsrc : offset.toNat + len.toNat ≤ linearDecreaseBytecode.size) :
    (stairstepCodecopyErrorMem offset len mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold stairstepCodecopyErrorMem
  rw [show 196 = (solcErrorStringMem2 len mem).size by
    rw [solcErrorStringMem2_size len hmem]]
  rw [write_read_below_end_from linearDecreaseBytecode
    (solcErrorStringMem2 len mem) offset.toNat len.toNat 64 hlen hsrc
    (by rw [solcErrorStringMem2_size len hmem]; omega)]
  exact solcErrorStringMem2_read64 len hmem hread64

theorem stairstepCodecopyErrorMem_mload64 {mem : ByteArray} (offset len : UInt256)
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hlen : len.toNat ≠ 0)
    (hsrc : offset.toNat + len.toNat ≤ linearDecreaseBytecode.size) :
    (if (⟨64⟩ : UInt256).toNat ≥ (stairstepCodecopyErrorMem offset len mem).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 8 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((stairstepCodecopyErrorMem offset len mem).readWithPadding
          (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ :=
  mloadFreePtrValue
    (by
      rw [stairstepCodecopyErrorMem_size offset len hmem hlen hsrc]
      omega)
    (by decide)
    (stairstepCodecopyErrorMem_read64 offset len hmem hread64 hlen hsrc)

@[reducible] def stairstepCodecopyRevertTailWf
    (pc offset len : UInt256) : Prop :=
  let p2 := pc + UInt256.ofNat 2
  let p3 := p2 + ⟨1⟩
  let p7 := p3 + UInt256.ofNat 4
  let p9 := p7 + UInt256.ofNat 2
  let p10 := p9 + ⟨1⟩
  let p11 := p10 + ⟨1⟩
  let p12 := p11 + ⟨1⟩
  let p14 := p12 + UInt256.ofNat 2
  let p15 := p14 + ⟨1⟩
  let p16 := p15 + ⟨1⟩
  let p17 := p16 + ⟨1⟩
  let p19 := p17 + UInt256.ofNat 2
  let p20 := p19 + ⟨1⟩
  let p21 := p20 + ⟨1⟩
  let p22 := p21 + ⟨1⟩
  let p23 := p22 + ⟨1⟩
  let p24 := p23 + ⟨1⟩
  let p25 := p24 + ⟨1⟩
  let p27 := p25 + UInt256.ofNat 2
  let p28 := p27 + ⟨1⟩
  let p29 := p28 + ⟨1⟩
  let p31 := p29 + UInt256.ofNat 2
  let p32 := p31 + ⟨1⟩
  let p33 := p32 + ⟨1⟩
  let p36 := p33 + UInt256.ofNat 3
  let p38 := p36 + UInt256.ofNat 2
  let p39 := p38 + ⟨1⟩
  let p40 := p39 + ⟨1⟩
  let p42 := p40 + UInt256.ofNat 2
  let p43 := p42 + ⟨1⟩
  let p44 := p43 + ⟨1⟩
  let p45 := p44 + ⟨1⟩
  let p46 := p45 + ⟨1⟩
  let p48 := p46 + UInt256.ofNat 2
  let p49 := p48 + ⟨1⟩
  let p50 := p49 + ⟨1⟩
  let p51 := p50 + ⟨1⟩
  let p52 := p51 + ⟨1⟩
  let p53 := p52 + ⟨1⟩
  decode linearDecreaseBytecode pc = some (.Push .PUSH1, some (⟨64⟩, 1))
  ∧ decode linearDecreaseBytecode p2 = some (.MLOAD, .none)
  ∧ decode linearDecreaseBytecode p3 =
      some (.Push .PUSH3, some (⟨4594637⟩, 3))
  ∧ decode linearDecreaseBytecode p7 =
      some (.Push .PUSH1, some (⟨229⟩, 1))
  ∧ decode linearDecreaseBytecode p9 = some (.SHL, .none)
  ∧ decode linearDecreaseBytecode p10 = some (.DUP2, .none)
  ∧ decode linearDecreaseBytecode p11 = some (.MSTORE, .none)
  ∧ decode linearDecreaseBytecode p12 =
      some (.Push .PUSH1, some (⟨4⟩, 1))
  ∧ decode linearDecreaseBytecode p14 = some (.ADD, .none)
  ∧ decode linearDecreaseBytecode p15 = some (.DUP1, .none)
  ∧ decode linearDecreaseBytecode p16 = some (.DUP1, .none)
  ∧ decode linearDecreaseBytecode p17 =
      some (.Push .PUSH1, some (⟨32⟩, 1))
  ∧ decode linearDecreaseBytecode p19 = some (.ADD, .none)
  ∧ decode linearDecreaseBytecode p20 = some (.DUP3, .none)
  ∧ decode linearDecreaseBytecode p21 = some (.DUP2, .none)
  ∧ decode linearDecreaseBytecode p22 = some (.SUB, .none)
  ∧ decode linearDecreaseBytecode p23 = some (.DUP3, .none)
  ∧ decode linearDecreaseBytecode p24 = some (.MSTORE, .none)
  ∧ decode linearDecreaseBytecode p25 =
      some (.Push .PUSH1, some (len, 1))
  ∧ decode linearDecreaseBytecode p27 = some (.DUP2, .none)
  ∧ decode linearDecreaseBytecode p28 = some (.MSTORE, .none)
  ∧ decode linearDecreaseBytecode p29 =
      some (.Push .PUSH1, some (⟨32⟩, 1))
  ∧ decode linearDecreaseBytecode p31 = some (.ADD, .none)
  ∧ decode linearDecreaseBytecode p32 = some (.DUP1, .none)
  ∧ decode linearDecreaseBytecode p33 =
      some (.Push .PUSH2, some (offset, 2))
  ∧ decode linearDecreaseBytecode p36 =
      some (.Push .PUSH1, some (len, 1))
  ∧ decode linearDecreaseBytecode p38 = some (.SWAP2, .none)
  ∧ decode linearDecreaseBytecode p39 = some (.CODECOPY, .none)
  ∧ decode linearDecreaseBytecode p40 =
      some (.Push .PUSH1, some (⟨64⟩, 1))
  ∧ decode linearDecreaseBytecode p42 = some (.ADD, .none)
  ∧ decode linearDecreaseBytecode p43 = some (.SWAP2, .none)
  ∧ decode linearDecreaseBytecode p44 = some (.POP, .none)
  ∧ decode linearDecreaseBytecode p45 = some (.POP, .none)
  ∧ decode linearDecreaseBytecode p46 =
      some (.Push .PUSH1, some (⟨64⟩, 1))
  ∧ decode linearDecreaseBytecode p48 = some (.MLOAD, .none)
  ∧ decode linearDecreaseBytecode p49 = some (.DUP1, .none)
  ∧ decode linearDecreaseBytecode p50 = some (.SWAP2, .none)
  ∧ decode linearDecreaseBytecode p51 = some (.SUB, .none)
  ∧ decode linearDecreaseBytecode p52 = some (.SWAP1, .none)
  ∧ decode linearDecreaseBytecode p53 = some (.REVERT, .none)

set_option maxHeartbeats 1000000 in
theorem RD.stairstepCodecopyRevertTail {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {pc : UInt256}
    {stk : List UInt256} {mem rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (offset len : UInt256)
    (h : RD linearDecreaseBytecode ee g s0 pc stk mem
        (UInt256.ofNat 3) rdata acc k C)
    (hwf : stairstepCodecopyRevertTailWf pc offset len)
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hlen : len.toNat ≠ 0)
    (hsrc : offset.toNat + len.toNat ≤ linearDecreaseBytecode.size)
    (hmcost :
      Cₘ (UInt256.ofNat
          (MachineState.M (UInt256.ofNat 7).toNat 196 len.toNat)) -
        Cₘ (UInt256.ofNat 7) = 3)
    (hawout :
      UInt256.ofNat (MachineState.M (UInt256.ofNat 7).toNat 196 len.toNat) =
        UInt256.ofNat 8)
    (hov : stk.length + 6 ≤ 1024) :
    RDrev linearDecreaseBytecode g s0 := by
  rcases hwf with
    ⟨hd0, hd2, hd3, hd7, hd9, hd10, hd11, hd12, hd14, hd15, hd16, hd17, hd19,
      hd20, hd21, hd22, hd23, hd24, hd25, hd27, hd28, hd29, hd31, hd32, hd33,
      hd36, hd38, hd39, hd40, hd42, hd43, hd44, hd45, hd46, hd48, hd49, hd50,
      hd51, hd52, hd53⟩
  have rdMload := evm_run h with [
    raw push1 ⟨64⟩ hd0 (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) hd2
      mem_cost
      (mloadFreePtrValue (by rw [hmem]; decide) (by decide) hread64)
      (by decide) (by evm_ov)]
  have rdSelectorRaw := rdMload.pushConst (⟨4594637⟩ : UInt256)
    (width := 3) (op := .PUSH3) (by decide) hd3
    (by simp only [List.length_cons]; omega)
  have rdPrefix0 := evm_run rdSelectorRaw with [
    raw push1 ⟨229⟩ hd7 (by evm_ov),
    raw shl hd9 (by evm_ov),
    raw dup2 hd10 (by evm_ov),
    raw mstore 6 (solcErrorStringMem0 mem) (UInt256.ofNat 5)
      hd11 mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨4⟩ hd12 (by evm_ov),
    raw add hd14 (by evm_ov),
    raw dup1 hd15 (by evm_ov),
    raw dup1 hd16 (by evm_ov),
    raw push1 ⟨32⟩ hd17 (by evm_ov),
    raw add hd19 (by evm_ov),
    raw dup3 hd20 (by evm_ov),
    raw dup2 hd21 (by evm_ov),
    raw sub hd22 (by evm_ov),
    raw dup3 hd23 (by evm_ov),
    raw mstore 3 (solcErrorStringMem1 mem) (UInt256.ofNat 6)
      hd24 mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 len hd25 (by evm_ov),
    raw dup2 hd27 (by evm_ov),
    raw mstore 3 (solcErrorStringMem2 len mem)
      (UInt256.ofNat 7) hd28 mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨32⟩ hd29 (by evm_ov),
    raw add hd31 (by evm_ov),
    raw dup1 hd32 (by evm_ov)]
  have hcopy :
      linearDecreaseBytecode.write offset.toNat
          (solcErrorStringMem2 len mem) 196 len.toNat =
        stairstepCodecopyErrorMem offset len mem := by
    rfl
  have rdCopy := evm_run rdPrefix0 with [
    raw push2 offset hd33 (by simp only [List.length_cons]; omega),
    raw push1 len hd36 (by simp only [List.length_cons]; omega),
    raw swap2 hd38 (by simp only [List.length_cons]; omega),
    raw codecopy 3 (stairstepCodecopyErrorMem offset len mem) (UInt256.ofNat 8)
      hd39
      (fun s haws hstks => by
        simp only [memoryExpansionCost, memoryExpansionCost.μᵢ', haws, hstks,
          List.getElem!_cons_zero, List.getElem!_cons_succ]
        simpa [show
          ({ val := 32 } + ({ val := 32 } + ({ val := 4 } + { val := 128 })) : UInt256).toNat =
            196 by native_decide] using hmcost)
      hcopy
      (by
        simpa [show
          ({ val := 32 } + ({ val := 32 } + ({ val := 4 } + { val := 128 })) : UInt256).toNat =
            196 by native_decide] using hawout)
      (by evm_ov)]
  exact evm_run rdCopy with [
    raw push1 ⟨64⟩ hd40 (by evm_ov),
    raw add hd42 (by evm_ov),
    raw swap2 hd43 (by evm_ov),
    raw pop hd44 (by evm_ov),
    raw pop hd45 (by evm_ov),
    raw push1 ⟨64⟩ hd46 (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) hd48
      mem_cost
      (stairstepCodecopyErrorMem_mload64 offset len hmem hread64 hlen hsrc)
      (by decide) (by evm_ov),
    raw dup1 hd49 (by evm_ov),
    raw swap2 hd50 (by evm_ov),
    raw sub hd51 (by evm_ov),
    raw swap1 hd52 (by evm_ov),
    raw rev 3 hd53 mem_cost (by evm_ov)]

end Benchmarks.Dss.LinearDecrease
