import Benchmarks.Safe.Dispatch
import Benchmarks.Safe.ModuleStorage
import Benchmarks.Safe.Blocks.Runtime_006
import Benchmarks.Safe.Blocks.Runtime_008
import Benchmarks.Safe.Blocks.Runtime_018
import Benchmarks.Safe.Blocks.Runtime_019

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open safeRuntimeBlocks

namespace Benchmarks.Safe

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
    (hgood : key ≠ ⟨0⟩ ∧ key ≠ ⟨1⟩) (hempty : moduleLink evm key = ⟨0⟩) :
    ExecTransitionBody config contract evm (enableModuleArgs key) enablemoduleTransition.body
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
          (.consNormal (.assign hsent hfirst)
            (.consNormal (.assign (safeEvalModule _ key) hsecond)
              (.consNormal (.emit (evalExprs?_singleton (safeEvalModule _ key))) .nil)))))))

theorem safeEnableModuleSourceStatic (evm : EVM.State) (key : UInt256)
    (hcanon : key.toNat < EVM.addressModulus)
    (hvalue : evm.executionEnv.weiValue = ⟨0⟩)
    (hauth : evm.executionEnv.source = evm.executionEnv.codeOwner)
    (hgood : key ≠ ⟨0⟩ ∧ key ≠ ⟨1⟩) (hempty : moduleLink evm key = ⟨0⟩)
    (hperm : evm.executionEnv.perm = false) :
    ExecTransitionBody config contract evm (enableModuleArgs key) enablemoduleTransition.body
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
    ExecTransitionBody config contract evm (enableModuleArgs key) enablemoduleTransition.body
      .reverted :=
  .execBlockRevert (.consNormal (.requireTrue (evalCallvalueEq_true hvalue))
    (.consNormal (.requireTrue (by simpa [hauth] using safeEvalAuthorized evm _))
      (.consRevert (.requireFalse (by simpa [hgood] using safeEnableModuleGuard evm key hcanon)))))

theorem safeEnableModuleSourceExisting (evm : EVM.State) (key : UInt256)
    (hcanon : key.toNat < EVM.addressModulus)
    (hvalue : evm.executionEnv.weiValue = ⟨0⟩)
    (hauth : evm.executionEnv.source = evm.executionEnv.codeOwner)
    (hgood : key ≠ ⟨0⟩ ∧ key ≠ ⟨1⟩) (hempty : moduleLink evm key ≠ ⟨0⟩) :
    ExecTransitionBody config contract evm (enableModuleArgs key) enablemoduleTransition.body
      .reverted :=
  .execBlockRevert (.consNormal (.requireTrue (evalCallvalueEq_true hvalue))
    (.consNormal (.requireTrue (by simpa [hauth] using safeEvalAuthorized evm _))
      (.consNormal (.requireTrue (by simpa [hgood] using safeEnableModuleGuard evm key hcanon))
        (.consRevert (.requireFalse
          (by simpa [hempty] using safeEnableModuleEmptyGuard evm key hcanon))))))

theorem safeEnableModuleUnauthorized (evm : EVM.State) (locals : Store)
    (hvalue : evm.executionEnv.weiValue = ⟨0⟩)
    (hauth : evm.executionEnv.source ≠ evm.executionEnv.codeOwner) :
    ExecTransitionBody config contract evm locals enablemoduleTransition.body .reverted :=
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
    (h : RD safeBytecode I g s0 ⟨3277⟩ (key :: ⟨664⟩ :: R) mem aw rdata σ k C)
    (hov : R.length + 13 ≤ 1024) (hmem : mem.size = 96)
    (hcanon : key.toNat < EVM.addressModulus) (hperm : I.perm = true) :
    RDret safeBytecode g s0 (enableModuleAccounts σ I key) ByteArray.empty := by
  obtain ⟨_, _, h3414⟩ := safeRuntime_block_3277 (by simp; omega) hperm h
  have h664 := safeRuntime_block_3414 (by simp [safeRuntime_block_3277_stack]; omega)
    (by jump_dest) h3414
  have hret := safeRuntime_block_664 (by simp [safeRuntime_block_3414_stack]; omega) h664
  simp only [safeAddressMask, solcAddrMask_clean_left hcanon] at hret
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
      UInt256.lor key (UInt256.land (UInt256.lnot solcAddrMask) old) =
      setAddressOffset0Word old key := by
    rw [← solcAddrMask_clean hcanon, setAddressOffset0Word_bytecode, solcAddrMask_clean hcanon]
  simp only [hfirst, hsecond] at hret
  exact hret

theorem safeEnableModuleTraceStatic {I g s0 σ k C aw mem rdata} {key : UInt256} {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨3277⟩ (key :: R) mem aw rdata σ k C)
    (hov : R.length + 12 ≤ 1024) (hperm : I.perm = false) :
    RDstatic safeBytecode g s0 := by
  have hslot := evm_run h with [jumpdest, push1 ⟨1⟩, push1 ⟨32⟩, dup2, swap1, genMstore]
  have hsent := hslot.pushConst
    (UInt256.ofNat 92458281274488595289803937127152923398167637295201432141969818930235769911599)
    (width := 32) (op := .PUSH32) (by decide) (by native_decide) (by simp; omega)
  have hdup := evm_run hsent with [dup1]
  obtain ⟨_, _, hload⟩ := RD.sload hdup (by native_decide) (by simp; omega)
  have hhash := evm_run hload with [push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub,
    dup5, dup2, and, push0, dup2, dup2, genMstore, push1 ⟨64⟩, dup1, dup3, genKeccak256, dup1]
  obtain ⟨_, _, hload2⟩ := RD.sload hhash (by native_decide) (by simp; omega)
  have hstore := evm_run hload2 with [swap5, swap1, swap6, and, push1 ⟨1⟩, push1 ⟨1⟩,
    push1 ⟨160⟩, shl, sub, not, swap5, dup6, and, or, swap1, swap5]
  exact hstore.sstoreStatic hperm (by native_decide) (by simp; omega)

theorem safeEnableModuleReachCheck {I g s0 σ k C aw mem rdata}
    {key : UInt256} {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨3176⟩ (key :: R) mem aw rdata σ k C)
    (hov : R.length + 4 ≤ 1024) (hcanon : key.toNat < EVM.addressModulus)
    (hgood : key ≠ ⟨0⟩ ∧ key ≠ ⟨1⟩) :
    ∃ k' C', RD safeBytecode I g s0 ⟨3229⟩ (key :: R) mem aw rdata σ k' C' := by
  have h3193 := safeRuntime_block_3176_fallthrough hov
    (by rw [safeAddressMask, solcAddrMask_clean hcanon]; exact isZero_eq_zero_of_ne hgood.1) h
  have h3207 := safeRuntime_block_3193 hov h3193
  have heq : UInt256.eq (UInt256.ofNat 1) key = ⟨0⟩ :=
    uInt256_eq_zero_of_ne (fun he ↦ hgood.2 (uInt256_eq_one_eq he).symm)
  simp only [safeRuntime_block_3193_stack, safeAddressMask, solcAddrMask_clean hcanon, heq] at h3207
  exact ⟨_, _, safeRuntime_block_3207_taken (by simp; omega) (by decide) (by jump_dest) h3207⟩

theorem safeEnableModuleReject {I g s0 σ k C aw mem rdata} {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨3207⟩ (⟨1⟩ :: R) mem aw rdata σ k C)
    (hov : R.length + 6 ≤ 1024) : RDrev safeBytecode g s0 := by
  have h3213 := safeRuntime_block_3207_fallthrough (by omega) (by decide) h
  change RD safeBytecode I g s0 ⟨3213⟩ R mem aw rdata σ _ _ at h3213
  have h6898 := safeRuntime_block_3213 (by omega) (by jump_dest) h3213
  exact safeRuntime_block_6898 (by simp [safeRuntime_block_3213_stack]; omega) h6898

theorem safeEnableModuleTraceInvalid {I g s0 σ k C aw mem rdata}
    {key : UInt256} {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨3176⟩ (key :: R) mem aw rdata σ k C)
    (hov : R.length + 7 ≤ 1024) (hcanon : key.toNat < EVM.addressModulus)
    (hgood : ¬ (key ≠ ⟨0⟩ ∧ key ≠ ⟨1⟩)) : RDrev safeBytecode g s0 := by
  by_cases hz : key = ⟨0⟩
  · have h3207 := safeRuntime_block_3176_taken (by omega)
      (by rw [safeAddressMask, solcAddrMask_clean hcanon, hz]; decide) (by jump_dest) h
    simp only [safeRuntime_block_3176_taken_stack, safeAddressMask,
      solcAddrMask_clean hcanon, hz, show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ by rfl] at h3207
    exact safeEnableModuleReject h3207 (by simp; omega)
  · have hone : key = ⟨1⟩ := by tauto
    have h3193 := safeRuntime_block_3176_fallthrough (by omega)
      (by rw [safeAddressMask, solcAddrMask_clean hcanon]; exact isZero_eq_zero_of_ne hz) h
    have h3207 := safeRuntime_block_3193 (by omega) h3193
    simp only [safeRuntime_block_3193_stack, safeAddressMask, solcAddrMask_clean hcanon,
      hone, show UInt256.eq (UInt256.ofNat 1) ⟨1⟩ = ⟨1⟩ by decide] at h3207
    exact safeEnableModuleReject h3207 (by simp; omega)

theorem safeEnableModuleCheckWord (σ : AccountMap) (I : ExecutionEnv) (key : UInt256)
    (hcanon : key.toNat < EVM.addressModulus) :
    UInt256.land (solcSlotWordAt (keccakWord ⟨0⟩ (UInt256.ofNat 64)
      (safeRuntime_block_3229_taken_memory (mem := solcFreePtrMem) (x0 := key))) σ I)
      (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) =
    UInt256.land (solcSlotWordAt (mapSlot key ⟨1⟩) σ I) solcAddrMask := by
  simp only [safeRuntime_block_3229_taken_memory, safeAddressMask, solcAddrMask_clean_left hcanon]
  change UInt256.land (solcSlotWordAt (keccakWord ⟨0⟩ (UInt256.ofNat 64)
    (twoWordHashMem key ⟨1⟩ solcFreePtrMem)) σ I) solcAddrMask = _
  rw [twoWordHashMemMapSlot key ⟨1⟩ solcFreePtrMem_size]

theorem safeEnableModuleTraceExisting {I g s0 σ k C aw mem rdata} {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨3261⟩ R mem aw rdata σ k C)
    (hov : R.length + 6 ≤ 1024) : RDrev safeBytecode g s0 := by
  have h6898 := safeRuntime_block_3261 (by omega) (by jump_dest) h
  exact safeRuntime_block_6898 (by simp [safeRuntime_block_3261_stack]; omega) h6898

theorem safeEnablemoduleBodyCore
    (hcode : I.code = safeBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hdispatch : selectorDispatchMsg contract I.calldata = some enablemoduleTransition) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  obtain ⟨hlong, hword⟩ := selectorDispatchFacts 0x61 0x0b 0x59 0x25 ⟨0x610b5925⟩
    hdispatch enablemoduleSelectorBytes (by decide)
  obtain ⟨k, C, h988⟩ := safeReachEntry (σ := σ) (σ₀ := σ₀) (A := A)
    (g := Sat256.ofUInt256 g) ⟨0x610b5925⟩ 2 ⟨988⟩ hcode hsize hlong hword
    (by native_decide)
  by_cases hvalue : I.weiValue = ⟨0⟩
  · have h999 := safeRuntime_block_988_taken (by simp)
      (by rw [hvalue]; decide) (by jump_dest) h988
    have h9591 := safeRuntime_block_999 (by simp) (by jump_dest) h999
    by_cases hbig : I.calldata.size < 2 ^ 255 + 4
    · by_cases hlen : 36 ≤ I.calldata.size
      · have hcheck := solcDecodeLenCheckOk_4_32 hlen hbig hsize
        by_cases hcanon : (calldataWord I.calldata 4).toNat < EVM.addressModulus
        · obtain ⟨_, _, h1014⟩ := safeDecodeAddress h9591 (by simp) hcheck hcanon (by jump_dest)
          have h3168 := safeRuntime_block_1014 (by simp) (by jump_dest) h1014
          have h6757 := safeRuntime_block_3168 (by simp) (by jump_dest) h3168
          have hdec : decodeCalldataWithMode config.abiDecodeMode
              (enablemoduleTransition.params.map Param.name)
              (transitionSignature enablemoduleTransition).paramTypes I.calldata =
              some (enableModuleArgs (calldataWord I.calldata 4)) :=
            decodeCalldata_address_ok hlen hbig hcanon
          by_cases hauth : I.source = I.codeOwner
          · obtain ⟨_, _, h3176⟩ := safeAuthorizedTrace h6757 (by simp) hauth (by jump_dest)
            change RD safeBytecode I (.ofUInt256 g) (initState σ σ₀ (.ofUInt256 g) A I) ⟨3176⟩
              [calldataWord I.calldata 4, ⟨664⟩, selWord I] _ _ _ σ _ _ at h3176
            by_cases hgood : calldataWord I.calldata 4 ≠ ⟨0⟩ ∧ calldataWord I.calldata 4 ≠ ⟨1⟩
            · obtain ⟨_, _, h3229⟩ := safeEnableModuleReachCheck h3176 (by simp) hcanon hgood
              have hword := safeEnableModuleCheckWord σ I (calldataWord I.calldata 4) hcanon
              simp only [safeRuntime_block_3229_taken_memory] at hword
              have hmodule : moduleLink (initState σ σ₀ (.ofUInt256 g) A I)
                  (calldataWord I.calldata 4) =
                  UInt256.land (solcSlotWordAt (mapSlot (calldataWord I.calldata 4) ⟨1⟩) σ I)
                    solcAddrMask := by
                rw [moduleLink, storageLoad_initState_ofUInt256_solcSlotWordAt]
              by_cases hempty : UInt256.land
                  (solcSlotWordAt (mapSlot (calldataWord I.calldata 4) ⟨1⟩) σ I) solcAddrMask = ⟨0⟩
              · have hempty' := hmodule.trans hempty
                obtain ⟨_, _, h3277⟩ := safeRuntime_block_3229_taken (by simp)
                  (by
                    have hz := congrArg UInt256.isZero (hword.trans hempty)
                    intro hn
                    exact (by decide : UInt256.isZero (⟨0⟩ : UInt256) ≠ UInt256.ofNat 0)
                      (hz.symm.trans hn)) (by jump_dest) h3229
                cases hperm : I.perm with
                | false =>
                    have hstatic := safeEnableModuleTraceStatic h3277 (by simp) hperm
                    have hbody := safeEnableModuleSourceStatic (initState σ σ₀ (.ofUInt256 g) A I)
                      (calldataWord I.calldata 4) hcanon hvalue hauth hgood hempty' hperm
                    exact RDstatic.reEquivElim hcode hstatic fun hΞ ↦
                      reEquivSelectorExecution hdispatch hdec hbody (.staticHalt hΞ rfl)
                | true =>
                    have hmem : (safeRuntime_block_3229_taken_memory
                        (mem := solcFreePtrMem) (x0 := calldataWord I.calldata 4)).size = 96 := by
                      simp only [safeRuntime_block_3229_taken_memory, safeAddressMask,
                        solcAddrMask_clean_left hcanon]
                      exact twoWordHashMem_size_96 _ _ solcFreePtrMem_size
                    have hret := safeEnableModuleTrace h3277 (by simp) hmem hcanon hperm
                    have hbody := safeEnableModuleSource (initState σ σ₀ (.ofUInt256 g) A I)
                      (calldataWord I.calldata 4) hcanon hvalue hauth hgood hempty'
                    refine reEquivReturnElim hcode hret fun _ _ hsuccess ↦ ?_
                    exact reEquivSelectorExecution hdispatch hdec hbody
                      (.success hsuccess rfl (safeEnableModuleAccounts (initState σ σ₀ (.ofUInt256
                        g) A I)
                        (calldataWord I.calldata 4)).symm
                        (.abi (.fallthrough rfl rfl encodeReturnValues_nil)))
              · obtain ⟨_, _, h3261⟩ := safeRuntime_block_3229_fallthrough (by simp)
                  (isZero_eq_zero_of_ne (fun hz ↦ hempty (hword.symm.trans hz))) h3229
                have hrev := safeEnableModuleTraceExisting h3261 (by simp)
                have hbody := safeEnableModuleSourceExisting (initState σ σ₀ (.ofUInt256 g) A I)
                  (calldataWord I.calldata 4) hcanon hvalue hauth hgood (by rwa [hmodule])
                exact RDrev.reEquivElim hcode hrev fun _ _ hΞ ↦
                  reEquivSelectorExecution hdispatch hdec hbody (.revert hΞ rfl)
            · have hrev := safeEnableModuleTraceInvalid h3176 (by simp) hcanon hgood
              have hbody := safeEnableModuleSourceInvalid (initState σ σ₀ (.ofUInt256 g) A I)
                (calldataWord I.calldata 4) hcanon hvalue hauth hgood
              exact RDrev.reEquivElim hcode hrev fun _ _ hΞ ↦
                reEquivSelectorExecution hdispatch hdec hbody (.revert hΞ rfl)
          · have hrev := safeUnauthorizedTrace h6757 (by simp [safeRuntime_block_3168_stack]) hauth
            exact reEquivSelectorRevert hcode hdispatch hrev fun locals ↦
              safeEnableModuleUnauthorized _ locals hvalue hauth
        · have hrev := safeDecodeAddressNoncanon h9591 (by simp) hcheck hcanon
          exact reEquivSelectorDecodingFailed (cfg := config) hcode hdispatch
            (decodeCalldata_address_none_noncanon hlen hbig hcanon) hrev
      · have hrev := safeDecodeAddressRevert h9591 (by simp)
          (solcDecodeLenCheckShort_4_32 hlong (by omega) hsize)
        exact reEquivSelectorDecodingFailed (cfg := config) hcode hdispatch
          (decodeCalldata_address_none_short hlong (by omega)) hrev
    · have hrev := safeDecodeAddressRevert h9591 (by simp)
        (solcDecodeLenCheckHuge_4_32 (by omega) hsize)
      exact reEquivSelectorDecodingFailed (cfg := config) hcode hdispatch
        (decodeCalldata_address_none_huge (by omega)) hrev
  · have h996 := safeRuntime_block_988_fallthrough (by simp)
      (isZero_eq_zero_of_ne hvalue) h988
    have hrev := safeRuntime_block_996 (by simp [safeRuntime_block_988_fallthrough_stack]) h996
    exact reEquivSelectorRevert hcode hdispatch hrev fun _ ↦ bodyReverts_nonPayable hvalue

/-- Refinement obligation for `enableModule` (`enablemoduleTransition`). -/
theorem safeEnablemoduleRefines
    (hcode : I.code = safeBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hdispatch : selectorDispatchMsg contract I.calldata = some enablemoduleTransition) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  exact safeEnablemoduleBodyCore hcode hsize hdispatch

end Benchmarks.Safe
