import Benchmarks.Safe.Dispatch
import Benchmarks.Safe.ModuleStorage
import Benchmarks.Safe.PairDecoders
import Benchmarks.Safe.Blocks.Runtime_006
import Benchmarks.Safe.Blocks.Runtime_011
import Benchmarks.Safe.Blocks.Runtime_026
import Benchmarks.Safe.Blocks.Runtime_027

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

open safeRuntimeBlocks

namespace Benchmarks.Safe

set_option maxRecDepth 100000

variable {σ σ₀ : AccountMap} {g : UInt256} {A : Substate} {I : ExecutionEnv}

def disableModuleArgs (prev key : UInt256) : Store :=
  ((∅ : Store).insert "prevModule" (.address (AccountAddress.ofNat prev.toNat))).insert
    "module" (.address (AccountAddress.ofNat key.toNat))

def disableModuleFrame (prev key : UInt256) : Frame :=
  { contract := contract, locals := disableModuleArgs prev key }

def disableModuleState (evm : EVM.State) (prev key : UInt256) : EVM.State :=
  writeModuleLink (writeModuleLink evm prev (moduleLink evm key)) key ⟨0⟩

theorem safeEvalDisableModule (evm : EVM.State) (prev key : UInt256) :
    evalExpr? config (disableModuleFrame prev key) evm (.var "module") =
      .ok (.address (AccountAddress.ofNat key.toNat)) := by
  simp [evalExpr?, disableModuleFrame, disableModuleArgs, EvalResult.ofOption]

theorem safeEvalPrevModule (evm : EVM.State) (prev key : UInt256) :
    evalExpr? config (disableModuleFrame prev key) evm (.var "prevModule") =
      .ok (.address (AccountAddress.ofNat prev.toNat)) := by
  simp [evalExpr?, disableModuleFrame, disableModuleArgs, EvalResult.ofOption,
    Std.HashMap.getElem_insert]

theorem safeDisableModuleGuard (evm : EVM.State) (prev key : UInt256)
    (hcanon : key.toNat < EVM.addressModulus) :
    evalExpr? config (disableModuleFrame prev key) evm
      (andE (neE (.var "module") zeroAddr) (neE (.var "module") sentinelAddr)) =
      .ok (.bool (decide (key ≠ ⟨0⟩ ∧ key ≠ ⟨1⟩))) :=
  evalAddressMembership hcanon hcanon (safeEvalDisableModule evm prev key)
    (safeEvalDisableModule evm prev key)

theorem safeDisableModuleLinkGuard (evm : EVM.State) (prev key : UInt256)
    (hprev : prev.toNat < EVM.addressModulus) (hkey : key.toNat < EVM.addressModulus) :
    evalExpr? config (disableModuleFrame prev key) evm
      (eqE (.storage (modulesRef (.var "prevModule"))) (.var "module")) =
      .ok (.bool (decide (moduleLink evm prev = key))) :=
  evalAddressEq (solcAddrMask_result_canonical _) hkey
    (safeEvalModuleLink evm _ _ prev (by simp [disableModuleArgs, Std.HashMap.getElem_insert])
      hprev (safeEvalPrevModule evm prev key)) (safeEvalDisableModule evm prev key)

theorem safeDisableModuleSource (evm : EVM.State) (prev key : UInt256)
    (hprev : prev.toNat < EVM.addressModulus) (hkey : key.toNat < EVM.addressModulus)
    (hvalue : evm.executionEnv.weiValue = ⟨0⟩)
    (hauth : evm.executionEnv.source = evm.executionEnv.codeOwner)
    (hgood : key ≠ ⟨0⟩ ∧ key ≠ ⟨1⟩) (hlink : moduleLink evm prev = key) :
    ExecTransitionBody config contract evm (disableModuleArgs prev key) disablemoduleTransition.body
      (.returned (disableModuleFrame prev key) (disableModuleState evm prev key) none) := by
  have hbase : (disableModuleArgs prev key)["modules"]? = none := by
    simp [disableModuleArgs, Std.HashMap.getElem_insert]
  have hnext := safeEvalModuleLink evm _ (.var "module") key hbase hkey
    (safeEvalDisableModule evm prev key)
  have hfirst := safeAssignModuleLink evm _ (.var "prevModule") prev (moduleLink evm key)
    hbase hprev (solcAddrMask_result_canonical _) (safeEvalPrevModule evm prev key)
  have hsecond := safeAssignModuleLink (writeModuleLink evm prev (moduleLink evm key))
    _ (.var "module") key ⟨0⟩ hbase hkey (by decide) (safeEvalDisableModule _ prev key)
  have hzero : evalExpr? config (disableModuleFrame prev key)
      (writeModuleLink evm prev (moduleLink evm key)) zeroAddr =
      .ok (.address (AccountAddress.ofNat (⟨0⟩ : UInt256).toNat)) := by
    simp [zeroAddr, addrSt, evalExpr?, castValue?, EvalResult.bind, EvalResult.ofOption, bind, pure]
  exact .execBlockOK (.consNormal (.requireTrue (evalCallvalueEq_true hvalue))
    (.consNormal (.requireTrue (by simpa [hauth] using safeEvalAuthorized evm _))
      (.consNormal (.requireTrue (by simpa [hgood] using safeDisableModuleGuard evm prev key hkey))
        (.consNormal (.requireTrue
          (by simpa [hlink] using safeDisableModuleLinkGuard evm prev key hprev hkey))
          (.consNormal (.assign hnext hfirst) (.consNormal (.assign hzero hsecond)
            (.consNormal (.emit (evalExprs?_singleton (safeEvalDisableModule _ prev key)))
              .nil)))))))

theorem safeDisableModuleSourceStatic (evm : EVM.State) (prev key : UInt256)
    (hprev : prev.toNat < EVM.addressModulus) (hkey : key.toNat < EVM.addressModulus)
    (hvalue : evm.executionEnv.weiValue = ⟨0⟩)
    (hauth : evm.executionEnv.source = evm.executionEnv.codeOwner)
    (hgood : key ≠ ⟨0⟩ ∧ key ≠ ⟨1⟩) (hlink : moduleLink evm prev = key)
    (hperm : evm.executionEnv.perm = false) :
    ExecTransitionBody config contract evm (disableModuleArgs prev key) disablemoduleTransition.body
      .staticViolation := by
  have hbase : (disableModuleArgs prev key)["modules"]? = none := by
    simp [disableModuleArgs, Std.HashMap.getElem_insert]
  have hnext := safeEvalModuleLink evm _ (.var "module") key hbase hkey
    (safeEvalDisableModule evm prev key)
  have hfirst := safeAssignModuleLink evm _ (.var "prevModule") prev (moduleLink evm key)
    hbase hprev (solcAddrMask_result_canonical _) (safeEvalPrevModule evm prev key)
  exact .execBlockStatic (.consNormal (.requireTrue (evalCallvalueEq_true hvalue))
    (.consNormal (.requireTrue (by simpa [hauth] using safeEvalAuthorized evm _))
      (.consNormal (.requireTrue (by simpa [hgood] using safeDisableModuleGuard evm prev key hkey))
        (.consNormal (.requireTrue
          (by simpa [hlink] using safeDisableModuleLinkGuard evm prev key hprev hkey))
          (.consStatic (.assignStatic hnext hfirst hperm))))))

theorem safeDisableModuleSourceInvalid (evm : EVM.State) (prev key : UInt256)
    (hkey : key.toNat < EVM.addressModulus)
    (hvalue : evm.executionEnv.weiValue = ⟨0⟩)
    (hauth : evm.executionEnv.source = evm.executionEnv.codeOwner)
    (hgood : ¬ (key ≠ ⟨0⟩ ∧ key ≠ ⟨1⟩)) :
    ExecTransitionBody config contract evm (disableModuleArgs prev key) disablemoduleTransition.body
      .reverted :=
  .execBlockRevert (.consNormal (.requireTrue (evalCallvalueEq_true hvalue))
    (.consNormal (.requireTrue (by simpa [hauth] using safeEvalAuthorized evm _))
      (.consRevert (.requireFalse
        (by simpa [hgood] using safeDisableModuleGuard evm prev key hkey)))))

theorem safeDisableModuleSourceUnlinked (evm : EVM.State) (prev key : UInt256)
    (hprev : prev.toNat < EVM.addressModulus) (hkey : key.toNat < EVM.addressModulus)
    (hvalue : evm.executionEnv.weiValue = ⟨0⟩)
    (hauth : evm.executionEnv.source = evm.executionEnv.codeOwner)
    (hgood : key ≠ ⟨0⟩ ∧ key ≠ ⟨1⟩) (hlink : moduleLink evm prev ≠ key) :
    ExecTransitionBody config contract evm (disableModuleArgs prev key) disablemoduleTransition.body
      .reverted :=
  .execBlockRevert (.consNormal (.requireTrue (evalCallvalueEq_true hvalue))
    (.consNormal (.requireTrue (by simpa [hauth] using safeEvalAuthorized evm _))
      (.consNormal (.requireTrue (by simpa [hgood] using safeDisableModuleGuard evm prev key hkey))
        (.consRevert (.requireFalse
          (by simpa [hlink] using safeDisableModuleLinkGuard evm prev key hprev hkey))))))

theorem safeDisableModuleUnauthorized (evm : EVM.State) (locals : Store)
    (hvalue : evm.executionEnv.weiValue = ⟨0⟩)
    (hauth : evm.executionEnv.source ≠ evm.executionEnv.codeOwner) :
    ExecTransitionBody config contract evm locals disablemoduleTransition.body .reverted :=
  .execBlockRevert (nonpayableSecondRequireReverts hvalue
    (by simpa [hauth] using safeEvalAuthorized evm _))

theorem safeDisableModuleReachCheck {I g s0 σ k C aw mem rdata}
    {key : UInt256} {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨5532⟩ (key :: R) mem aw rdata σ k C)
    (hov : R.length + 4 ≤ 1024) (hcanon : key.toNat < EVM.addressModulus)
    (hgood : key ≠ ⟨0⟩ ∧ key ≠ ⟨1⟩) :
    ∃ k' C', RD safeBytecode I g s0 ⟨5585⟩ (key :: R) mem aw rdata σ k' C' := by
  have h5549 := safeRuntime_block_5532_fallthrough hov
    (by rw [safeAddressMask, solcAddrMask_clean hcanon]; exact isZero_eq_zero_of_ne hgood.1) h
  have h5563 := safeRuntime_block_5549 hov h5549
  have heq : UInt256.eq (UInt256.ofNat 1) key = ⟨0⟩ :=
    uInt256_eq_zero_of_ne (fun he ↦ hgood.2 (uInt256_eq_one_eq he).symm)
  simp only [safeRuntime_block_5549_stack, safeAddressMask, solcAddrMask_clean hcanon, heq] at h5563
  exact ⟨_, _, safeRuntime_block_5563_taken (by simp; omega) (by decide) (by jump_dest) h5563⟩

theorem safeDisableModuleReject {I g s0 σ k C aw mem rdata} {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨5563⟩ (⟨1⟩ :: R) mem aw rdata σ k C)
    (hov : R.length + 6 ≤ 1024) : RDrev safeBytecode g s0 := by
  have h5569 := safeRuntime_block_5563_fallthrough (by omega) (by decide) h
  change RD safeBytecode I g s0 ⟨5569⟩ R mem aw rdata σ _ _ at h5569
  have h6898 := safeRuntime_block_5569 (by omega) (by jump_dest) h5569
  exact safeRuntime_block_6898 (by simp [safeRuntime_block_5569_stack]; omega) h6898

theorem safeDisableModuleTraceInvalid {I g s0 σ k C aw mem rdata}
    {key : UInt256} {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨5532⟩ (key :: R) mem aw rdata σ k C)
    (hov : R.length + 7 ≤ 1024) (hcanon : key.toNat < EVM.addressModulus)
    (hgood : ¬ (key ≠ ⟨0⟩ ∧ key ≠ ⟨1⟩)) : RDrev safeBytecode g s0 := by
  by_cases hz : key = ⟨0⟩
  · have h5563 := safeRuntime_block_5532_taken (by omega)
      (by rw [safeAddressMask, solcAddrMask_clean hcanon, hz]; decide) (by jump_dest) h
    simp only [safeRuntime_block_5532_taken_stack, safeAddressMask,
      solcAddrMask_clean hcanon, hz, show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ by rfl] at h5563
    exact safeDisableModuleReject h5563 (by simp; omega)
  · have hone : key = ⟨1⟩ := by tauto
    have h5549 := safeRuntime_block_5532_fallthrough (by omega)
      (by rw [safeAddressMask, solcAddrMask_clean hcanon]; exact isZero_eq_zero_of_ne hz) h
    have h5563 := safeRuntime_block_5549 (by omega) h5549
    simp only [safeRuntime_block_5549_stack, safeAddressMask, solcAddrMask_clean hcanon,
      hone, show UInt256.eq (UInt256.ofNat 1) ⟨1⟩ = ⟨1⟩ by decide] at h5563
    exact safeDisableModuleReject h5563 (by simp; omega)

def disableModuleAccounts (σ : AccountMap) (I : ExecutionEnv) (prev key : UInt256) : AccountMap :=
  let σ' := sstoreAccountMap I.codeOwner σ (mapSlot prev ⟨1⟩)
    (setAddressOffset0Word (solcSlotWordAt (mapSlot prev ⟨1⟩) σ I)
      (UInt256.land (solcSlotWordAt (mapSlot key ⟨1⟩) σ I) solcAddrMask))
  sstoreAccountMap I.codeOwner σ' (mapSlot key ⟨1⟩)
    (setAddressOffset0Word (solcSlotWordAt (mapSlot key ⟨1⟩) σ' I) ⟨0⟩)

theorem safeDisableModuleAccounts (evm : EVM.State) (prev key : UInt256) :
    (disableModuleState evm prev key).accountMap =
      disableModuleAccounts evm.accountMap evm.executionEnv prev key := by
  simp only [disableModuleState, writeModuleLink, moduleLink, storageStore_executionEnv,
    storageLoad_eq_solcSlotWord, storageStore_accountMap]
  rfl

theorem safeDisableModuleTrace {I g s0 σ k C aw mem rdata} {prev key : UInt256} {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨5637⟩ (key :: prev :: ⟨664⟩ :: R) mem aw rdata σ k C)
    (hov : R.length + 13 ≤ 1024) (hmem : mem.size = 96)
    (hprev : prev.toNat < EVM.addressModulus) (hkey : key.toNat < EVM.addressModulus)
    (hperm : I.perm = true) :
    RDret safeBytecode g s0 (disableModuleAccounts σ I prev key) ByteArray.empty := by
  obtain ⟨_, _, h5710⟩ := safeRuntime_block_5637 (by simp; omega) hperm h
  have h664 := safeRuntime_block_5710 (by omega) hperm (by jump_dest) h5710
  have hret := safeRuntime_block_664 (by simp [safeRuntime_block_5710_stack]; omega) h664
  simp only [safeAddressMask, solcAddrMask_clean_left hprev, solcAddrMask_clean_left hkey] at hret
  have hkeyhash := twoWordHashMemMapSlot key (UInt256.ofNat 1) hmem
  change keccakWord ⟨0⟩ (UInt256.ofNat 64)
    ((UInt256.ofNat 1).toByteArray.write 0
      (key.toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32) =
      mapSlot key ⟨1⟩ at hkeyhash
  have hprevhash := keyAfterSlotHash prev (UInt256.ofNat 1) (wordAt0Mem_size_96 key hmem)
  change keccakWord ⟨0⟩ (UInt256.ofNat 64)
    (prev.toByteArray.write 0 ((UInt256.ofNat 1).toByteArray.write 0
      (key.toByteArray.write 0 mem (⟨0⟩ : UInt256).toNat 32) (UInt256.ofNat 32).toNat 32)
      (⟨0⟩ : UInt256).toNat 32) = mapSlot prev ⟨1⟩ at hprevhash
  rw [hkeyhash, hprevhash] at hret
  have hfirst (old next : UInt256) :
      UInt256.lor (UInt256.land (UInt256.lnot solcAddrMask) old)
        (UInt256.land solcAddrMask next) =
      setAddressOffset0Word old (UInt256.land next solcAddrMask) := by
    rw [setAddressOffset0Word, maskTwice, u256_land_comm (UInt256.lnot solcAddrMask) old,
      u256_land_comm solcAddrMask next]
  have hsecond (old : UInt256) : UInt256.land (UInt256.lnot solcAddrMask) old =
      setAddressOffset0Word old ⟨0⟩ := by
    rw [setAddressOffset0Word, u256_land_zero_left, u256_lor_zero, u256_land_comm]
  simp only [hfirst] at hret
  change RDret safeBytecode g s0 (sstoreAccountMap I.codeOwner
    (sstoreAccountMap I.codeOwner σ (mapSlot prev ⟨1⟩)
      (setAddressOffset0Word (solcSlotWordAt (mapSlot prev ⟨1⟩) σ I)
        (UInt256.land (solcSlotWordAt (mapSlot key ⟨1⟩) σ I) solcAddrMask))) (mapSlot key ⟨1⟩)
      (UInt256.land (UInt256.lnot solcAddrMask) _)) ByteArray.empty at hret
  rw [hsecond] at hret
  exact hret

theorem safeDisableModuleTraceStatic {I g s0 σ k C aw mem rdata}
    {prev key : UInt256} {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨5637⟩ (key :: prev :: R) mem aw rdata σ k C)
    (hov : R.length + 12 ≤ 1024) (hperm : I.perm = false) :
    RDstatic safeBytecode g s0 := by
  have hhash := evm_run h with [jumpdest, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub,
    dup2, dup2, and, push0, dup2, dup2, genMstore, push1 ⟨1⟩, push1 ⟨32⟩, genMstore,
    push1 ⟨64⟩, dup1, dup3, genKeccak256, dup1]
  obtain ⟨_, _, hnext⟩ := RD.sload hhash (by native_decide) (by simp; omega)
  have hprevhash := evm_run hnext with [dup8, dup7, and, dup5, genMstore, dup3, dup5,
    genKeccak256, dup1]
  obtain ⟨_, _, hload⟩ := RD.sload hprevhash (by native_decide) (by simp; omega)
  have hstore := evm_run hload with [swap2, swap1, swap7, and, push1 ⟨1⟩, push1 ⟨1⟩,
    push1 ⟨160⟩, shl, sub, not, swap2, dup3, and, or, swap1, swap6]
  exact hstore.sstoreStatic hperm (by native_decide) (by simp; omega)

theorem safeDisableModuleCheckWord (σ : AccountMap) (I : ExecutionEnv) (prev key : UInt256)
    (hprev : prev.toNat < EVM.addressModulus) (hkey : key.toNat < EVM.addressModulus) :
    UInt256.eq (UInt256.land key
      (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)))
      (UInt256.land
        (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))
        (solcSlotWordAt (keccakWord ⟨0⟩ (UInt256.ofNat 64)
          (safeRuntime_block_5585_taken_memory (mem := solcFreePtrMem) (x1 := prev))) σ I)) =
      UInt256.eq key (UInt256.land (solcSlotWordAt (mapSlot prev ⟨1⟩) σ I) solcAddrMask) := by
  simp only [safeRuntime_block_5585_taken_memory, safeAddressMask,
    solcAddrMask_clean_left hprev, solcAddrMask_clean hkey]
  change UInt256.eq key (UInt256.land solcAddrMask (solcSlotWordAt
    (keccakWord ⟨0⟩ (UInt256.ofNat 64) (twoWordHashMem prev ⟨1⟩ solcFreePtrMem)) σ I)) = _
  rw [twoWordHashMemMapSlot prev ⟨1⟩ solcFreePtrMem_size, u256_land_comm solcAddrMask]

theorem safeDisableModuleTraceUnlinked {I g s0 σ k C aw mem rdata} {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨5621⟩ R mem aw rdata σ k C)
    (hov : R.length + 6 ≤ 1024) : RDrev safeBytecode g s0 := by
  have h6898 := safeRuntime_block_5621 (by omega) (by jump_dest) h
  exact safeRuntime_block_6898 (by simp; omega) h6898

theorem safeDisablemoduleBodyCore
    (hcode : I.code = safeBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hdispatch : selectorDispatchMsg contract I.calldata = some disablemoduleTransition) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  obtain ⟨hlong, hword⟩ := selectorDispatchFacts 0xe0 0x09 0xcf 0xde ⟨0xe009cfde⟩
    hdispatch disablemoduleSelectorBytes (by decide)
  obtain ⟨k, C, h1377⟩ := safeReachEntry (σ := σ) (σ₀ := σ₀) (A := A)
    (g := Sat256.ofUInt256 g) ⟨0xe009cfde⟩ 2 ⟨1377⟩ hcode hsize hlong hword
    (by native_decide)
  by_cases hvalue : I.weiValue = ⟨0⟩
  · have h1388 := safeRuntime_block_1377_taken (by simp)
      (by rw [hvalue]; decide) (by jump_dest) h1377
    have h10868 := safeRuntime_block_1388 (by simp) (by jump_dest) h1388
    by_cases hbig : I.calldata.size < 2 ^ 255 + 4
    · by_cases hlen : 68 ≤ I.calldata.size
      · have hcheck := solcDecodeLenCheckOk_4_64 hlen hbig hsize
        by_cases hc0 : (calldataWord I.calldata 4).toNat < EVM.addressModulus
        · by_cases hc1 : (calldataWord I.calldata 36).toNat < EVM.addressModulus
          · obtain ⟨_, _, h1403⟩ := safeDecodeAddressPair h10868 (by simp)
              hcheck hc0 hc1 (by jump_dest)
            have h5524 := safeRuntime_block_1403 (by simp) (by jump_dest) h1403
            have h6757 := safeRuntime_block_5524 (by simp) (by jump_dest) h5524
            have hdec : decodeCalldataWithMode config.abiDecodeMode
                (disablemoduleTransition.params.map Param.name)
                (transitionSignature disablemoduleTransition).paramTypes I.calldata =
                some (disableModuleArgs (calldataWord I.calldata 4) (calldataWord I.calldata 36)) :=
              decodeCalldata_address_address_ok hlen hbig hc0 hc1
            by_cases hauth : I.source = I.codeOwner
            · obtain ⟨_, _, h5532⟩ := safeAuthorizedTrace h6757 (by simp) hauth (by jump_dest)
              change RD safeBytecode I (.ofUInt256 g) (initState σ σ₀ (.ofUInt256 g) A I) ⟨5532⟩
                [calldataWord I.calldata 36, calldataWord I.calldata 4, ⟨664⟩, selWord I]
                _ _ _ σ _ _ at h5532
              by_cases hgood : calldataWord I.calldata 36 ≠ ⟨0⟩ ∧ calldataWord I.calldata 36 ≠ ⟨1⟩
              · obtain ⟨_, _, h5585⟩ := safeDisableModuleReachCheck h5532 (by simp) hc1 hgood
                have hword := safeDisableModuleCheckWord σ I
                  (calldataWord I.calldata 4) (calldataWord I.calldata 36) hc0 hc1
                simp only [safeRuntime_block_5585_taken_memory] at hword
                have hmodule : moduleLink (initState σ σ₀ (.ofUInt256 g) A I)
                    (calldataWord I.calldata 4) =
                    UInt256.land (solcSlotWordAt (mapSlot (calldataWord I.calldata 4) ⟨1⟩) σ I)
                      solcAddrMask := by
                  rw [moduleLink, storageLoad_initState_ofUInt256_solcSlotWordAt]
                by_cases hlink : UInt256.land
                    (solcSlotWordAt (mapSlot (calldataWord I.calldata 4) ⟨1⟩) σ I) solcAddrMask =
                    calldataWord I.calldata 36
                · have hlink' := hmodule.trans hlink
                  obtain ⟨_, _, h5637⟩ := safeRuntime_block_5585_taken (by simp)
                    (by
                      have hone := hword.trans (by rw [hlink, uInt256_eq_self])
                      intro hz
                      exact (by decide : (⟨1⟩ : UInt256) ≠ UInt256.ofNat 0) (hone.symm.trans hz))
                    (by jump_dest) h5585
                  cases hperm : I.perm with
                  | false =>
                      have hstatic := safeDisableModuleTraceStatic h5637 (by simp) hperm
                      have hbody := safeDisableModuleSourceStatic (initState σ σ₀ (.ofUInt256 g) A
                        I)
                        (calldataWord I.calldata 4) (calldataWord I.calldata 36)
                        hc0 hc1 hvalue hauth hgood hlink' hperm
                      exact RDstatic.reEquivElim hcode hstatic fun hΞ ↦
                        reEquivSelectorExecution hdispatch hdec hbody (.staticHalt hΞ rfl)
                  | true =>
                      have hmem : (safeRuntime_block_5585_taken_memory
                          (mem := solcFreePtrMem) (x1 := calldataWord I.calldata 4)).size = 96 := by
                        simp only [safeRuntime_block_5585_taken_memory, safeAddressMask,
                          solcAddrMask_clean_left hc0]
                        exact twoWordHashMem_size_96 _ _ solcFreePtrMem_size
                      have hret := safeDisableModuleTrace h5637 (by simp) hmem hc0 hc1 hperm
                      have hbody := safeDisableModuleSource (initState σ σ₀ (.ofUInt256 g) A I)
                        (calldataWord I.calldata 4) (calldataWord I.calldata 36)
                        hc0 hc1 hvalue hauth hgood hlink'
                      refine reEquivReturnElim hcode hret fun _ _ hsuccess ↦ ?_
                      exact reEquivSelectorExecution hdispatch hdec hbody
                        (.success hsuccess rfl
                          (safeDisableModuleAccounts (initState σ σ₀ (.ofUInt256 g) A I)
                            (calldataWord I.calldata 4) (calldataWord I.calldata 36)).symm
                          (.abi (.fallthrough rfl rfl encodeReturnValues_nil)))
                · obtain ⟨_, _, h5621⟩ := safeRuntime_block_5585_fallthrough (by simp)
                    (hword.trans (uInt256_eq_zero_of_ne
                      (fun he ↦ hlink (uInt256_eq_one_eq he).symm))) h5585
                  have hrev := safeDisableModuleTraceUnlinked h5621 (by simp)
                  have hbody := safeDisableModuleSourceUnlinked (initState σ σ₀ (.ofUInt256 g) A I)
                    (calldataWord I.calldata 4) (calldataWord I.calldata 36)
                    hc0 hc1 hvalue hauth hgood (by rwa [hmodule])
                  exact RDrev.reEquivElim hcode hrev fun _ _ hΞ ↦
                    reEquivSelectorExecution hdispatch hdec hbody (.revert hΞ rfl)
              · have hrev := safeDisableModuleTraceInvalid h5532 (by simp) hc1 hgood
                have hbody := safeDisableModuleSourceInvalid (initState σ σ₀ (.ofUInt256 g) A I)
                  (calldataWord I.calldata 4) (calldataWord I.calldata 36) hc1 hvalue hauth hgood
                exact RDrev.reEquivElim hcode hrev fun _ _ hΞ ↦
                  reEquivSelectorExecution hdispatch hdec hbody (.revert hΞ rfl)
            · have hrev := safeUnauthorizedTrace h6757
                (by simp [safeRuntime_block_5524_stack]) hauth
              exact reEquivSelectorRevert hcode hdispatch hrev fun locals ↦
                safeDisableModuleUnauthorized _ locals hvalue hauth
          · have hrev := safeDecodeAddressPairNoncanon1 h10868 (by simp) hcheck hc0 hc1
            exact reEquivSelectorDecodingFailed (cfg := config) hcode hdispatch
              (decodeCalldata_address_address_none_noncanon1 hlen hbig hc0 hc1) hrev
        · have hrev := safeDecodeAddressPairNoncanon0 h10868 (by simp) hcheck hc0
          exact reEquivSelectorDecodingFailed (cfg := config) hcode hdispatch
            (decodeCalldata_address_address_none_noncanon0 hlen hbig hc0) hrev
      · have hrev := safeDecodeAddressPairRevert h10868 (by simp)
          (solcDecodeLenCheckShort_4_64 hlong (by omega) hsize)
        exact reEquivSelectorDecodingFailed (cfg := config) hcode hdispatch
          (decodeCalldata_address_address_none_short hlong (by omega)) hrev
    · have hrev := safeDecodeAddressPairRevert h10868 (by simp)
        (solcDecodeLenCheckHuge_4_64 (by omega) hsize)
      exact reEquivSelectorDecodingFailed (cfg := config) hcode hdispatch
        (decodeCalldata_address_address_none_huge (by omega)) hrev
  · have h1385 := safeRuntime_block_1377_fallthrough (by simp)
      (isZero_eq_zero_of_ne hvalue) h1377
    have hrev := safeRuntime_block_1385 (by simp [safeRuntime_block_1377_fallthrough_stack]) h1385
    exact reEquivSelectorRevert hcode hdispatch hrev fun _ ↦ bodyReverts_nonPayable hvalue

/-- Refinement obligation for `disableModule` (`disablemoduleTransition`). -/
theorem safeDisablemoduleRefines
    (hcode : I.code = safeBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hdispatch : selectorDispatchMsg contract I.calldata = some disablemoduleTransition) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  exact safeDisablemoduleBodyCore hcode hsize hdispatch

end Benchmarks.Safe
