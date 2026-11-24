import Benchmarks.Safe.ViaIR.Dispatch
import Benchmarks.Safe.ViaIR.ModuleStorage
import Benchmarks.Safe.ViaIR.Authorization
import Benchmarks.Safe.ViaIR.IRLengthCheck
import Benchmarks.Safe.ViaIR.Blocks.Runtime_011
import Benchmarks.Safe.ViaIR.Blocks.Runtime_028
import Benchmarks.Safe.ViaIR.Blocks.Runtime_044

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.ViaIR.RuntimeBlocks

namespace Benchmarks.Safe.ViaIR

set_option maxRecDepth 100000

variable {σ σ₀ : AccountMap} {g : UInt256} {A : Substate} {I : ExecutionEnv}

def enableModuleArgs (key : UInt256) : Store :=
  (∅ : Store).insert "module" (.address (AccountAddress.ofNat key.toNat))

def enableModuleFrame (key : UInt256) : Frame :=
  { contract := contract, locals := enableModuleArgs key }

def enableModuleState (evm : EVM.State) (key : UInt256) : EVM.State :=
  writeModuleLink (writeModuleLink evm key (moduleLink evm ⟨1⟩)) ⟨1⟩ key

theorem safeEvalModule (evm : EVM.State) (key : UInt256) :
    evalExpr? config (enableModuleFrame key) evm (.var "module") =
      .ok (.address (AccountAddress.ofNat key.toNat)) := by
  simp [evalExpr?, enableModuleFrame, enableModuleArgs, EvalResult.ofOption]

theorem safeEnableModuleGuard (evm : EVM.State) (key : UInt256)
    (hcanon : key.toNat < EVM.addressModulus) :
    evalExpr? config (enableModuleFrame key) evm
      (andE (neE (.var "module") zeroAddr) (neE (.var "module") sentinelAddr)) =
      .ok (.bool (decide (key ≠ ⟨0⟩ ∧ key ≠ ⟨1⟩))) :=
  evalAddressMembership hcanon hcanon (safeEvalModule evm key) (safeEvalModule evm key)

theorem safeEnableModuleEmptyGuard (evm : EVM.State) (key : UInt256)
    (hcanon : key.toNat < EVM.addressModulus) :
    evalExpr? config (enableModuleFrame key) evm
      (eqE (.storage (modulesRef (.var "module"))) zeroAddr) =
      .ok (.bool (decide (moduleLink evm key = ⟨0⟩))) :=
  evalAddressZero (solcAddrMask_result_canonical _)
    (safeEvalModuleLink evm _ _ key (by simp [enableModuleArgs]) hcanon (safeEvalModule evm key))

theorem safeEnableModuleSource (evm : EVM.State) (key : UInt256)
    (hcanon : key.toNat < EVM.addressModulus)
    (hvalue : evm.executionEnv.weiValue = ⟨0⟩)
    (hauth : evm.executionEnv.source = evm.executionEnv.codeOwner)
    (hgood : key ≠ ⟨0⟩ ∧ key ≠ ⟨1⟩) (hempty : moduleLink evm key = ⟨0⟩)
    (hperm : evm.executionEnv.perm = true) :
    ExecTransitionBody fork config contract evm (enableModuleArgs key) enablemoduleTransition.body
      (.returned (enableModuleFrame key) (enableModuleState evm key) none) := by
  have hbase : (enableModuleArgs key)["modules"]? = none := by simp [enableModuleArgs]
  have hsent := safeEvalModuleLink evm _ sentinelAddr ⟨1⟩ hbase (by decide)
    (safeEvalModuleSentinel evm _)
  have hfirst := safeAssignModuleLink evm _ (.var "module") key (moduleLink evm ⟨1⟩)
    hbase hcanon (solcAddrMask_result_canonical _) (safeEvalModule evm key)
  have hsecond := safeAssignModuleLink (writeModuleLink evm key (moduleLink evm ⟨1⟩))
    _ sentinelAddr ⟨1⟩ key hbase (by decide) hcanon (safeEvalModuleSentinel _ _)
  refine .execBlockOK (.consNormal (.requireTrue (evalCallvalueEq_true hvalue))
    (.consNormal (.requireTrue (by simpa [hauth] using safeEvalAuthorized evm _))
      (.consNormal (.requireTrue (by simpa [hgood] using safeEnableModuleGuard evm key hcanon))
        (.consNormal (.requireTrue (by
          simpa [hempty] using safeEnableModuleEmptyGuard evm key hcanon))
          (.consNormal (.assign (hperm := Or.inr hperm) hsent hfirst)
            (.consNormal (.assign (hperm := Or.inr (by simpa only [writeModuleLink, storageStore_executionEnv] using hperm)) (safeEvalModule _ key) hsecond)
              (.consNormal (.emit (hperm := by simpa only [writeModuleLink, storageStore_executionEnv] using hperm) (evalExprs?_singleton (safeEvalModule _ key))) .nil)))))))

theorem safeEnableModuleSourceStatic (evm : EVM.State) (key : UInt256)
    (hcanon : key.toNat < EVM.addressModulus)
    (hvalue : evm.executionEnv.weiValue = ⟨0⟩)
    (hauth : evm.executionEnv.source = evm.executionEnv.codeOwner)
    (hgood : key ≠ ⟨0⟩ ∧ key ≠ ⟨1⟩) (hempty : moduleLink evm key = ⟨0⟩)
    (hperm : evm.executionEnv.perm = false) :
    ExecTransitionBody fork config contract evm (enableModuleArgs key) enablemoduleTransition.body
      .staticViolation := by
  have hbase : (enableModuleArgs key)["modules"]? = none := by simp [enableModuleArgs]
  have hsent := safeEvalModuleLink evm _ sentinelAddr ⟨1⟩ hbase (by decide)
    (safeEvalModuleSentinel evm _)
  have hfirst := safeAssignModuleLink evm _ (.var "module") key (moduleLink evm ⟨1⟩)
    hbase hcanon (solcAddrMask_result_canonical _) (safeEvalModule evm key)
  exact .execBlockStatic (.consNormal (.requireTrue (evalCallvalueEq_true hvalue))
    (.consNormal (.requireTrue (by simpa [hauth] using safeEvalAuthorized evm _))
      (.consNormal (.requireTrue (by simpa [hgood] using safeEnableModuleGuard evm key hcanon))
        (.consNormal (.requireTrue (by
          simpa [hempty] using safeEnableModuleEmptyGuard evm key hcanon))
          (.consStatic (.assignStatic hsent hfirst hperm))))))

theorem safeEnableModuleSourceInvalid (evm : EVM.State) (key : UInt256)
    (hcanon : key.toNat < EVM.addressModulus)
    (hvalue : evm.executionEnv.weiValue = ⟨0⟩)
    (hauth : evm.executionEnv.source = evm.executionEnv.codeOwner)
    (hgood : ¬ (key ≠ ⟨0⟩ ∧ key ≠ ⟨1⟩)) :
    ExecTransitionBody fork config contract evm (enableModuleArgs key) enablemoduleTransition.body
      .reverted :=
  .execBlockRevert (.consNormal (.requireTrue (evalCallvalueEq_true hvalue))
    (.consNormal (.requireTrue (by simpa [hauth] using safeEvalAuthorized evm _))
      (.consRevert (.requireFalse (by simpa [hgood] using safeEnableModuleGuard evm key hcanon)))))

theorem safeEnableModuleSourceExisting (evm : EVM.State) (key : UInt256)
    (hcanon : key.toNat < EVM.addressModulus)
    (hvalue : evm.executionEnv.weiValue = ⟨0⟩)
    (hauth : evm.executionEnv.source = evm.executionEnv.codeOwner)
    (hgood : key ≠ ⟨0⟩ ∧ key ≠ ⟨1⟩) (hempty : moduleLink evm key ≠ ⟨0⟩) :
    ExecTransitionBody fork config contract evm (enableModuleArgs key) enablemoduleTransition.body
      .reverted :=
  .execBlockRevert (.consNormal (.requireTrue (evalCallvalueEq_true hvalue))
    (.consNormal (.requireTrue (by simpa [hauth] using safeEvalAuthorized evm _))
      (.consNormal (.requireTrue (by simpa [hgood] using safeEnableModuleGuard evm key hcanon))
        (.consRevert (.requireFalse
          (by simpa [hempty] using safeEnableModuleEmptyGuard evm key hcanon))))))

theorem safeEnableModuleUnauthorized (evm : EVM.State) (locals : Store)
    (hvalue : evm.executionEnv.weiValue = ⟨0⟩)
    (hauth : evm.executionEnv.source ≠ evm.executionEnv.codeOwner) :
    ExecTransitionBody fork config contract evm locals enablemoduleTransition.body .reverted :=
  .execBlockRevert (nonpayableSecondRequireReverts hvalue
    (by simpa [hauth] using safeEvalAuthorized evm _))

def enableModuleAccounts (σ : AccountMap) (I : ExecutionEnv) (key : UInt256) : AccountMap :=
  let σ' := sstoreAccountMap I.codeOwner σ (mapSlot key ⟨1⟩)
    (setAddressOffset0Word (solcSlotWordAt (mapSlot key ⟨1⟩) σ I)
      (UInt256.land (solcSlotWordAt (mapSlot ⟨1⟩ ⟨1⟩) σ I) solcAddrMask))
  sstoreAccountMap I.codeOwner σ' (mapSlot ⟨1⟩ ⟨1⟩)
    (setAddressOffset0Word (solcSlotWordAt (mapSlot ⟨1⟩ ⟨1⟩) σ' I) key)

theorem safeEnableModuleAccounts (evm : EVM.State) (key : UInt256) :
    (enableModuleState evm key).accountMap =
      enableModuleAccounts evm.accountMap evm.executionEnv key := by
  simp only [enableModuleState, writeModuleLink, moduleLink, storageStore_executionEnv,
    storageLoad_eq_solcSlotWord, storageStore_accountMap]
  rfl

theorem safeEnableModuleTrace {I g s0 σ k C aw mem rdata} {key : UInt256} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨5868⟩ (key :: R) mem aw rdata σ k C)
    (hov : R.length + 13 ≤ 1024) (hmem : mem.size = 96)
    (hcanon : key.toNat < EVM.addressModulus) (hperm : I.perm = true) :
    RDret fork safeBytecode g s0 (enableModuleAccounts σ I key) ByteArray.empty := by
  have hret := safeRuntime_block_5868 (by omega) hperm h
  simp only [safeAddressMask] at hret
  have hhash := keyAfterSlotHash key ⟨1⟩ hmem
  change keccakWord ⟨0⟩ (UInt256.ofNat 64)
    (key.toByteArray.write 0 ((UInt256.ofNat 1).toByteArray.write 0 mem
      (UInt256.ofNat 32).toNat 32) (⟨0⟩ : UInt256).toNat 32) = mapSlot key ⟨1⟩ at hhash
  rw [hhash, ← safeModuleSentinelSlot] at hret
  have hfirst (old next : UInt256) :
      UInt256.lor (UInt256.land (UInt256.lnot solcAddrMask) old)
        (UInt256.land next solcAddrMask) =
      setAddressOffset0Word old (UInt256.land next solcAddrMask) := by
    rw [setAddressOffset0Word, maskTwice, u256_land_comm (UInt256.lnot solcAddrMask) old]
  have hsecond (old : UInt256) :
      UInt256.lor key (UInt256.land old (UInt256.lnot solcAddrMask)) =
      setAddressOffset0Word old key := by
    rw [setAddressOffset0Word, solcAddrMask_clean hcanon, u256_lor_comm]
  simp only [hfirst, hsecond] at hret
  exact hret

theorem safeEnableModuleTraceStatic {I g s0 σ k C aw mem rdata} {key : UInt256} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨5868⟩ (key :: R) mem aw rdata σ k C)
    (hov : R.length + 12 ≤ 1024) (hperm : I.perm = false) :
    RDstatic fork safeBytecode g s0 := by
  have hslot := evm_run h with [push1 ⟨1⟩, push1 ⟨32⟩, dup2, swap1, genMstore]
  have hsent := hslot.pushConst
    (UInt256.ofNat 92458281274488595289803937127152923398167637295201432141969818930235769911599)
    (width := 32) (op := .PUSH32) (by decide) (by native_decide) (by simp; omega)
  have hdup := evm_run hsent with [dup1]
  obtain ⟨_, _, hload⟩ := RD.sload hdup (by native_decide) (by simp; omega)
  have hhash := evm_run hload with
    [push0, dup5, dup2, genMstore, push1 ⟨64⟩, dup2, genKeccak256, dup1]
  obtain ⟨_, _, hload2⟩ := RD.sload hhash (by native_decide) (by simp; omega)
  have hstore := evm_run hload2 with [push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub,
    swap1, swap4, and, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, not,
    swap4, dup5, and, or, swap1]
  exact hstore.sstoreStatic hperm (by native_decide) (by simp; omega)

theorem safeEnableModuleReachCheck {I g s0 σ k C aw mem rdata}
    {key : UInt256} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨5818⟩ (key :: R) mem aw rdata σ k C)
    (hov : R.length + 4 ≤ 1024) (hcanon : key.toNat < EVM.addressModulus)
    (hgood : key ≠ ⟨0⟩ ∧ key ≠ ⟨1⟩) :
    ∃ k' C', RD fork safeBytecode I g s0 ⟨5841⟩ (key :: R) mem aw rdata σ k' C' := by
  have h6038 := safeRuntime_block_5818_taken hov
    (by
      rw [safeAddressMask, solcAddrMask_clean_left hcanon, isZero_eq_zero_of_ne hgood.1]
      decide) (by jump_dest) h
  simp only [safeRuntime_block_5818_taken_stack, safeAddressMask,
    solcAddrMask_clean_left hcanon] at h6038
  have h5836 := safeRuntime_block_6038 (by omega) (by jump_dest) h6038
  have heq : UInt256.eq key (UInt256.ofNat 1) = ⟨0⟩ :=
    uInt256_eq_zero_of_ne (fun he ↦ hgood.2 (uInt256_eq_one_eq he))
  simp only [safeRuntime_block_6038_stack, heq] at h5836
  exact ⟨_, _, safeRuntime_block_5836_fallthrough (by simp; omega) rfl h5836⟩

theorem safeEnableModuleReject {I g s0 σ k C aw mem rdata} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨5836⟩ (⟨1⟩ :: R) mem aw rdata σ k C)
    (hov : R.length + 6 ≤ 1024) : RDrev fork safeBytecode g s0 := by
  have h2231 := safeRuntime_block_5836_taken (by omega) (by decide) (by jump_dest) h
  have h9592 := safeRuntime_block_2231
    (by simp [safeRuntime_block_5836_taken_stack]; omega) (by jump_dest) h2231
  exact safeRuntime_block_9592 (by simp [safeRuntime_block_5836_taken_stack]; omega) h9592

theorem safeEnableModuleTraceInvalid {I g s0 σ k C aw mem rdata}
    {key : UInt256} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨5818⟩ (key :: R) mem aw rdata σ k C)
    (hov : R.length + 7 ≤ 1024) (hcanon : key.toNat < EVM.addressModulus)
    (hgood : ¬ (key ≠ ⟨0⟩ ∧ key ≠ ⟨1⟩)) : RDrev fork safeBytecode g s0 := by
  by_cases hz : key = ⟨0⟩
  · have h5836 := safeRuntime_block_5818_fallthrough (by omega)
      (by rw [safeAddressMask, solcAddrMask_clean_left hcanon, hz]; decide) h
    simp only [safeRuntime_block_5818_fallthrough_stack, safeAddressMask,
      solcAddrMask_clean_left hcanon, hz,
      show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ by rfl] at h5836
    exact safeEnableModuleReject h5836 (by simp; omega)
  · have hone : key = ⟨1⟩ := by tauto
    have h6038 := safeRuntime_block_5818_taken (by omega)
      (by rw [safeAddressMask, solcAddrMask_clean_left hcanon, hone]; decide) (by jump_dest) h
    simp only [safeRuntime_block_5818_taken_stack, safeAddressMask,
      solcAddrMask_clean_left hcanon] at h6038
    have h5836 := safeRuntime_block_6038 (by omega) (by jump_dest) h6038
    simp only [safeRuntime_block_6038_stack, hone,
      show UInt256.eq (⟨1⟩ : UInt256) (UInt256.ofNat 1) = ⟨1⟩ by decide] at h5836
    exact safeEnableModuleReject h5836 (by simp; omega)

theorem safeEnableModuleCheckWord (σ : AccountMap) (I : ExecutionEnv) (key : UInt256)
    (hcanon : key.toNat < EVM.addressModulus) :
    UInt256.land
      (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))
      (solcSlotWordAt (keccakWord ⟨0⟩ (UInt256.ofNat 64)
        (safeRuntime_block_5841_taken_memory (mem := solcFreePtrMem) (x0 := key))) σ I) =
    UInt256.land (solcSlotWordAt (mapSlot key ⟨1⟩) σ I) solcAddrMask := by
  simp only [safeRuntime_block_5841_taken_memory, safeAddressMask, solcAddrMask_clean_left hcanon]
  change UInt256.land solcAddrMask (solcSlotWordAt (keccakWord ⟨0⟩ (UInt256.ofNat 64)
    (twoWordHashMem key ⟨1⟩ solcFreePtrMem)) σ I) = _
  rw [twoWordHashMemMapSlot key ⟨1⟩ solcFreePtrMem_size, u256_land_comm]

theorem safeEnableModuleTraceExisting {I g s0 σ k C aw mem rdata} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨5993⟩ R mem aw rdata σ k C)
    (hov : R.length + 6 ≤ 1024) : RDrev fork safeBytecode g s0 := by
  exact safeRuntime_block_5993 (by omega) h

theorem safeEnablemoduleBodyCore
    (hcode : I.code = safeBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hdispatch : selectorDispatchMsg contract I.calldata = some enablemoduleTransition) :
    runtimeRefinementFor fork config contract σ σ₀ g A I := by
  obtain ⟨hlong, hword⟩ := selectorDispatchFacts 0x61 0x0b 0x59 0x25 ⟨0x610b5925⟩
    hdispatch enablemoduleSelectorBytes (by decide)
  obtain ⟨k, C, h5785⟩ := safeReachEntry (fork := fork) (σ := σ) (σ₀ := σ₀) (A := A)
    (g := Sat256.ofUInt256 g) ⟨0x610b5925⟩ 9 ⟨5785⟩ hcode hsize hlong hword
    (by native_decide)
  have hlenWord := safeIRArgumentSizeSub hlong hsize
  by_cases hvalue : I.weiValue = ⟨0⟩
  · have h5791 := safeRuntime_block_5785_fallthrough (by simp) hvalue h5785
    by_cases hbig : I.calldata.size < 2 ^ 255 + 4
    · by_cases hlen : 36 ≤ I.calldata.size
      · have h5803 := safeRuntime_block_5791_fallthrough (by simp)
          (by rw [hlenWord]; exact solcDecodeLenCheckOk_4_32 hlen hbig hsize) h5791
        have h6952 := safeRuntime_block_5803 (by simp) (by jump_dest) h5803
        by_cases hcanon : (calldataWord I.calldata 4).toNat < EVM.addressModulus
        · obtain ⟨_, _, h5810⟩ := safeDecodeAddress h6952
            (by simp [safeRuntime_block_5803_stack]) hcanon (by jump_dest)
          have h9325 := safeRuntime_block_5810 (by simp) (by jump_dest) h5810
          have hdec : config.externalABI.decodeCalldata?
              (enablemoduleTransition.params.map Param.name)
              (transitionSignature enablemoduleTransition).paramTypes I.calldata =
              some (enableModuleArgs (calldataWord I.calldata 4)) :=
            decodeCalldata_address_ok hlen hbig hcanon
          by_cases hauth : I.source = I.codeOwner
          · obtain ⟨_, _, h5818⟩ := safeAuthorizedTrace h9325 (by simp) hauth (by jump_dest)
            change RD fork safeBytecode I (.ofUInt256 g) (initState σ σ₀ (.ofUInt256 g) A I) ⟨5818⟩
              [calldataWord I.calldata 4, selWord I, ⟨0⟩] _ _ _ σ _ _ at h5818
            by_cases hgood : calldataWord I.calldata 4 ≠ ⟨0⟩ ∧ calldataWord I.calldata 4 ≠ ⟨1⟩
            · obtain ⟨_, _, h5841⟩ := safeEnableModuleReachCheck h5818 (by simp) hcanon hgood
              have hword := safeEnableModuleCheckWord σ I (calldataWord I.calldata 4) hcanon
              dsimp only [safeRuntime_block_5841_taken_memory, solcSlotWordAt] at hword
              have hmodule : moduleLink (initState σ σ₀ (.ofUInt256 g) A I)
                  (calldataWord I.calldata 4) =
                  UInt256.land (solcSlotWordAt (mapSlot (calldataWord I.calldata 4) ⟨1⟩) σ I)
                    solcAddrMask := by
                rw [moduleLink, storageLoad_initState_ofUInt256_solcSlotWordAt]
              by_cases hempty : UInt256.land
                  (solcSlotWordAt (mapSlot (calldataWord I.calldata 4) ⟨1⟩) σ I) solcAddrMask = ⟨0⟩
              · have hempty' := hmodule.trans hempty
                obtain ⟨_, _, h5868⟩ := safeRuntime_block_5841_fallthrough (by simp)
                  (hword.trans hempty) h5841
                cases hperm : I.perm with
                | false =>
                    have hstatic := safeEnableModuleTraceStatic h5868 (by simp) hperm
                    have hbody := safeEnableModuleSourceStatic (fork := fork) (initState σ σ₀ (.ofUInt256 g) A I)
                      (calldataWord I.calldata 4) hcanon hvalue hauth hgood hempty' hperm
                    exact RDstatic.reEquivElim hcode hstatic fun hΞ ↦
                      reEquivSelectorExecution hdispatch hdec hbody (.staticHalt hΞ rfl)
                | true =>
                    have hmem : (safeRuntime_block_5841_taken_memory
                        (mem := solcFreePtrMem) (x0 := calldataWord I.calldata 4)).size = 96 := by
                      simp only [safeRuntime_block_5841_taken_memory, safeAddressMask,
                        solcAddrMask_clean_left hcanon]
                      exact twoWordHashMem_size_96 _ _ solcFreePtrMem_size
                    have hret := safeEnableModuleTrace h5868 (by simp) hmem hcanon hperm
                    have hbody := safeEnableModuleSource (fork := fork) (hperm := by assumption) (initState σ σ₀ (.ofUInt256 g) A I)
                      (calldataWord I.calldata 4) hcanon hvalue hauth hgood hempty'
                    refine reEquivReturnElim hcode hret fun _ _ hsuccess ↦ ?_
                    exact reEquivSelectorExecution hdispatch hdec hbody
                      (.success hsuccess rfl (safeEnableModuleAccounts (initState σ σ₀ (.ofUInt256
                        g) A I)
                        (calldataWord I.calldata 4)).symm
                        (.abi (.fallthrough rfl rfl encodeReturnValues_nil)))
              · obtain ⟨_, _, h5993⟩ := safeRuntime_block_5841_taken (by simp)
                  (fun hz ↦ hempty (hword.symm.trans hz)) (by jump_dest) h5841
                have hrev := safeEnableModuleTraceExisting h5993 (by simp)
                have hbody := safeEnableModuleSourceExisting (fork := fork) (initState σ σ₀ (.ofUInt256 g) A I)
                  (calldataWord I.calldata 4) hcanon hvalue hauth hgood (by rwa [hmodule])
                exact RDrev.reEquivElim hcode hrev fun _ _ hΞ ↦
                  reEquivSelectorExecution hdispatch hdec hbody (.revert hΞ rfl)
            · have hrev := safeEnableModuleTraceInvalid h5818 (by simp) hcanon hgood
              have hbody := safeEnableModuleSourceInvalid (fork := fork) (initState σ σ₀ (.ofUInt256 g) A I)
                (calldataWord I.calldata 4) hcanon hvalue hauth hgood
              exact RDrev.reEquivElim hcode hrev fun _ _ hΞ ↦
                reEquivSelectorExecution hdispatch hdec hbody (.revert hΞ rfl)
          · have hrev := safeUnauthorizedTrace h9325 (by simp [safeRuntime_block_5810_stack]) hauth
            exact reEquivSelectorRevert hcode hdispatch hrev fun locals ↦
              safeEnableModuleUnauthorized _ locals hvalue hauth
        · have hrev := safeDecodeAddressNoncanon h6952
            (by simp [safeRuntime_block_5803_stack]) hcanon
          exact reEquivSelectorDecodingFailed (cfg := config) hcode hdispatch
            (decodeCalldata_address_none_noncanon hlen hbig hcanon) hrev
      · have h111 := safeRuntime_block_5791_taken (by simp)
          (by
            rw [hlenWord]
            change UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ ≠ ⟨0⟩
            rw [solcDecodeLenCheckShort_4_32 hlong (by omega) hsize]
            decide) (by jump_dest) h5791
        have hrev := safeRuntime_block_111 (by simp) h111
        exact reEquivSelectorDecodingFailed (cfg := config) hcode hdispatch
          (decodeCalldata_address_none_short hlong (by omega)) hrev
    · have h111 := safeRuntime_block_5791_taken (by simp)
        (by
          rw [hlenWord]
          change UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ ≠ ⟨0⟩
          rw [solcDecodeLenCheckHuge_4_32 (by omega) hsize]
          decide) (by jump_dest) h5791
      have hrev := safeRuntime_block_111 (by simp) h111
      exact reEquivSelectorDecodingFailed (cfg := config) hcode hdispatch
        (decodeCalldata_address_none_huge (by omega)) hrev
  · have h111 := safeRuntime_block_5785_taken (by simp) hvalue (by jump_dest) h5785
    have hrev := safeRuntime_block_111 (by simp) h111
    exact reEquivSelectorRevert hcode hdispatch hrev fun _ ↦ bodyReverts_nonPayable hvalue

/-- Refinement obligation for `enableModule` (`enablemoduleTransition`). -/
theorem safeEnablemoduleRefines
    (hcode : I.code = safeBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hdispatch : selectorDispatchMsg contract I.calldata = some enablemoduleTransition) :
    runtimeRefinementFor fork config contract σ σ₀ g A I := by
  exact safeEnablemoduleBodyCore hcode hsize hdispatch

end Benchmarks.Safe.ViaIR
