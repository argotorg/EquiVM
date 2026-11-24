import Benchmarks.Safe.ViaIR.Dispatch
import Benchmarks.Safe.ViaIR.ModuleStorage
import Benchmarks.Safe.ViaIR.Authorization
import Benchmarks.Safe.ViaIR.IRLengthCheck
import Benchmarks.Safe.ViaIR.PairDecoders
import Benchmarks.Safe.ViaIR.Blocks.Runtime_004
import Benchmarks.Safe.ViaIR.Blocks.Runtime_011
import Benchmarks.Safe.ViaIR.Blocks.Runtime_044

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

open Benchmarks.Safe.ViaIR.RuntimeBlocks

namespace Benchmarks.Safe.ViaIR

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
    (hgood : key ≠ ⟨0⟩ ∧ key ≠ ⟨1⟩) (hlink : moduleLink evm prev = key)
    (hperm : evm.executionEnv.perm = true) :
    ExecTransitionBody fork config contract evm (disableModuleArgs prev key) disablemoduleTransition.body
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
          (.consNormal (.assign (hperm := Or.inr hperm) hnext hfirst) (.consNormal (.assign (hperm := Or.inr (by simpa only [writeModuleLink, storageStore_executionEnv] using hperm)) hzero hsecond)
            (.consNormal (.emit (hperm := by simpa only [writeModuleLink, storageStore_executionEnv] using hperm) (evalExprs?_singleton (safeEvalDisableModule _ prev key)))
              .nil)))))))

theorem safeDisableModuleSourceStatic (evm : EVM.State) (prev key : UInt256)
    (hprev : prev.toNat < EVM.addressModulus) (hkey : key.toNat < EVM.addressModulus)
    (hvalue : evm.executionEnv.weiValue = ⟨0⟩)
    (hauth : evm.executionEnv.source = evm.executionEnv.codeOwner)
    (hgood : key ≠ ⟨0⟩ ∧ key ≠ ⟨1⟩) (hlink : moduleLink evm prev = key)
    (hperm : evm.executionEnv.perm = false) :
    ExecTransitionBody fork config contract evm (disableModuleArgs prev key) disablemoduleTransition.body
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
    ExecTransitionBody fork config contract evm (disableModuleArgs prev key) disablemoduleTransition.body
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
    ExecTransitionBody fork config contract evm (disableModuleArgs prev key) disablemoduleTransition.body
      .reverted :=
  .execBlockRevert (.consNormal (.requireTrue (evalCallvalueEq_true hvalue))
    (.consNormal (.requireTrue (by simpa [hauth] using safeEvalAuthorized evm _))
      (.consNormal (.requireTrue (by simpa [hgood] using safeDisableModuleGuard evm prev key hkey))
        (.consRevert (.requireFalse
          (by simpa [hlink] using safeDisableModuleLinkGuard evm prev key hprev hkey))))))

theorem safeDisableModuleUnauthorized (evm : EVM.State) (locals : Store)
    (hvalue : evm.executionEnv.weiValue = ⟨0⟩)
    (hauth : evm.executionEnv.source ≠ evm.executionEnv.codeOwner) :
    ExecTransitionBody fork config contract evm locals disablemoduleTransition.body .reverted :=
  .execBlockRevert (nonpayableSecondRequireReverts hvalue
    (by simpa [hauth] using safeEvalAuthorized evm _))

theorem safeDisableModuleReachCheck {I g s0 σ k C aw mem rdata}
    {prev key : UInt256} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨2022⟩ (key :: prev :: R) mem aw rdata σ k C)
    (hov : R.length + 5 ≤ 1024) (hcanon : key.toNat < EVM.addressModulus)
    (hgood : key ≠ ⟨0⟩ ∧ key ≠ ⟨1⟩) :
    ∃ k' C', RD fork safeBytecode I g s0 ⟨2046⟩ (prev :: key :: R) mem aw rdata σ k' C' := by
  have h2236 := safeRuntime_block_2022_taken hov
    (by
      rw [safeAddressMask, solcAddrMask_clean_left hcanon, isZero_eq_zero_of_ne hgood.1]
      decide) (by jump_dest) h
  simp only [safeRuntime_block_2022_taken_stack, safeAddressMask,
    solcAddrMask_clean_left hcanon] at h2236
  have h2041 := safeRuntime_block_2236 (by omega) (by jump_dest) h2236
  have heq : UInt256.eq key (UInt256.ofNat 1) = ⟨0⟩ :=
    uInt256_eq_zero_of_ne (fun he ↦ hgood.2 (uInt256_eq_one_eq he))
  simp only [safeRuntime_block_2236_stack, heq] at h2041
  exact ⟨_, _, safeRuntime_block_2041_fallthrough (by simp; omega) rfl h2041⟩

theorem safeDisableModuleReject {I g s0 σ k C aw mem rdata} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨2041⟩ (⟨1⟩ :: R) mem aw rdata σ k C)
    (hov : R.length + 4 ≤ 1024) : RDrev fork safeBytecode g s0 := by
  have h2231 := safeRuntime_block_2041_taken (by omega) (by decide) (by jump_dest) h
  have h9592 := safeRuntime_block_2231
    (by simp [safeRuntime_block_2041_taken_stack]; omega) (by jump_dest) h2231
  exact safeRuntime_block_9592 (by simp [safeRuntime_block_2041_taken_stack]; omega) h9592

theorem safeDisableModuleTraceInvalid {I g s0 σ k C aw mem rdata}
    {prev key : UInt256} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨2022⟩ (key :: prev :: R) mem aw rdata σ k C)
    (hov : R.length + 7 ≤ 1024) (hcanon : key.toNat < EVM.addressModulus)
    (hgood : ¬ (key ≠ ⟨0⟩ ∧ key ≠ ⟨1⟩)) : RDrev fork safeBytecode g s0 := by
  by_cases hz : key = ⟨0⟩
  · have h2041 := safeRuntime_block_2022_fallthrough (by omega)
      (by rw [safeAddressMask, solcAddrMask_clean_left hcanon, hz]; decide) h
    simp only [safeRuntime_block_2022_fallthrough_stack, safeAddressMask,
      solcAddrMask_clean_left hcanon, hz,
      show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ by rfl] at h2041
    exact safeDisableModuleReject h2041 (by simp; omega)
  · have hone : key = ⟨1⟩ := by tauto
    have h2236 := safeRuntime_block_2022_taken (by omega)
      (by rw [safeAddressMask, solcAddrMask_clean_left hcanon, hone]; decide) (by jump_dest) h
    simp only [safeRuntime_block_2022_taken_stack, safeAddressMask,
      solcAddrMask_clean_left hcanon] at h2236
    have h2041 := safeRuntime_block_2236 (by omega) (by jump_dest) h2236
    simp only [safeRuntime_block_2236_stack, hone,
      show UInt256.eq (⟨1⟩ : UInt256) (UInt256.ofNat 1) = ⟨1⟩ by decide] at h2041
    exact safeDisableModuleReject h2041 (by simp; omega)

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
    (h : RD fork safeBytecode I g s0 ⟨2080⟩ (prev :: key :: ⟨0⟩ :: R) mem aw rdata σ k C)
    (hov : R.length + 13 ≤ 1024) (hmem : mem.size = 96)
    (hprev : prev.toNat < EVM.addressModulus) (hkey : key.toNat < EVM.addressModulus)
    (hperm : I.perm = true) :
    RDret fork safeBytecode g s0 (disableModuleAccounts σ I prev key) ByteArray.empty := by
  obtain ⟨_, _, h2185⟩ := safeRuntime_block_2080 (by omega) hperm h
  have hret := safeRuntime_block_2185 (by omega) h2185
  simp only [safeAddressMask, show (⟨0⟩ : UInt256).toNat = 0 from rfl,
    show (UInt256.ofNat 32).toNat = 32 from rfl, byteArray_readWithPadding_zero] at hret
  have hkeyhash := twoWordHashMemMapSlot key (UInt256.ofNat 1) hmem
  have hprevhash := twoWordHashMemMapSlot prev (UInt256.ofNat 1)
    (twoWordHashMem_size_96 key (UInt256.ofNat 1) hmem)
  have hclearhash := twoWordHashMemMapSlot key (UInt256.ofNat 1)
    (twoWordHashMem_size_96 prev (UInt256.ofNat 1)
      (twoWordHashMem_size_96 key (UInt256.ofNat 1) hmem))
  dsimp only [twoWordHashMem, wordAt32Mem, wordAt0Mem] at hkeyhash hprevhash hclearhash
  rw [hkeyhash, hprevhash, hclearhash] at hret
  have hfirst (old next : UInt256) :
      UInt256.lor (UInt256.land (UInt256.lnot solcAddrMask) old)
        (UInt256.land next solcAddrMask) =
      setAddressOffset0Word old (UInt256.land next solcAddrMask) := by
    rw [setAddressOffset0Word, maskTwice, u256_land_comm (UInt256.lnot solcAddrMask) old]
  have hsecond (old : UInt256) : UInt256.land (UInt256.lnot solcAddrMask) old =
      setAddressOffset0Word old ⟨0⟩ := by
    rw [setAddressOffset0Word, u256_land_zero_left, u256_lor_zero, u256_land_comm]
  simp only [hfirst] at hret
  change RDret fork safeBytecode g s0 (sstoreAccountMap I.codeOwner
    (sstoreAccountMap I.codeOwner σ (mapSlot prev ⟨1⟩)
      (setAddressOffset0Word (solcSlotWordAt (mapSlot prev ⟨1⟩) σ I)
        (UInt256.land (solcSlotWordAt (mapSlot key ⟨1⟩) σ I) solcAddrMask))) (mapSlot key ⟨1⟩)
      (UInt256.land (UInt256.lnot solcAddrMask) _)) ByteArray.empty at hret
  rw [hsecond] at hret
  exact hret

theorem safeDisableModuleTraceStatic {I g s0 σ k C aw mem rdata}
    {prev key : UInt256} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨2080⟩ (prev :: key :: ⟨0⟩ :: R) mem aw rdata σ k C)
    (hov : R.length + 12 ≤ 1024) (hperm : I.perm = false) :
    RDstatic fork safeBytecode g s0 := by
  have hhash := evm_run h with [dup2, dup4, genMstore, push1 ⟨1⟩, push1 ⟨32⟩,
    dup2, dup2, genMstore, push1 ⟨64⟩, dup1, dup7, genKeccak256]
  obtain ⟨_, _, hnext⟩ := RD.sload hhash (by native_decide) (by simp; omega)
  have hprevhash := evm_run hnext with
    [swap4, dup7, genMstore, dup3, dup3, genMstore, dup1, dup7, genKeccak256, dup1]
  obtain ⟨_, _, hload⟩ := RD.sload hprevhash (by native_decide) (by simp; omega)
  have hstore := evm_run hload with [push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub,
    swap1, swap6, and, push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub, not,
    swap6, dup7, and, or, swap1]
  exact hstore.sstoreStatic hperm (by native_decide) (by simp; omega)

theorem safeDisableModuleCheckWord (σ : AccountMap) (I : ExecutionEnv) (prev key : UInt256)
    (hprev : prev.toNat < EVM.addressModulus) (hkey : key.toNat < EVM.addressModulus) :
    UInt256.sub (UInt256.land
      (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))
      (solcSlotWordAt (keccakWord ⟨0⟩ (UInt256.ofNat 64)
        (safeRuntime_block_2046_taken_memory
          (mem := solcFreePtrMem) (x0 := prev) (x2 := ⟨0⟩))) σ I)) key =
      UInt256.sub (UInt256.land (solcSlotWordAt (mapSlot prev ⟨1⟩) σ I) solcAddrMask) key := by
  simp only [safeRuntime_block_2046_taken_memory, safeAddressMask,
    solcAddrMask_clean_left hprev]
  change UInt256.sub (UInt256.land solcAddrMask (solcSlotWordAt
    (keccakWord ⟨0⟩ (UInt256.ofNat 64) (twoWordHashMem prev ⟨1⟩ solcFreePtrMem)) σ I)) key = _
  rw [twoWordHashMemMapSlot prev ⟨1⟩ solcFreePtrMem_size, u256_land_comm solcAddrMask]

theorem safeDisableModuleTraceUnlinked {I g s0 σ k C aw mem rdata} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨2186⟩ R mem aw rdata σ k C)
    (hov : R.length + 6 ≤ 1024) : RDrev fork safeBytecode g s0 := by
  exact safeRuntime_block_2186 (by omega) h

theorem safeDisablemoduleBodyCore
    (hcode : I.code = safeBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hdispatch : selectorDispatchMsg contract I.calldata = some disablemoduleTransition) :
    runtimeRefinementFor fork config contract σ σ₀ g A I := by
  obtain ⟨hlong, hword⟩ := selectorDispatchFacts 0xe0 0x09 0xcf 0xde ⟨0xe009cfde⟩
    hdispatch disablemoduleSelectorBytes (by decide)
  obtain ⟨k, C, h1980⟩ := safeReachEntry (fork := fork) (σ := σ) (σ₀ := σ₀) (A := A)
    (g := Sat256.ofUInt256 g) ⟨0xe009cfde⟩ 21 ⟨1980⟩ hcode hsize hlong hword
    (by native_decide)
  have hlenWord := safeIRArgumentSizeSub hlong hsize
  by_cases hvalue : I.weiValue = ⟨0⟩
  · have h1987 := safeRuntime_block_1980_fallthrough (by simp) hvalue h1980
    simp only [safeRuntime_block_1980_fallthrough_stack] at h1987
    by_cases hbig : I.calldata.size < 2 ^ 255 + 4
    · by_cases hlen : 68 ≤ I.calldata.size
      · have h1999 := safeRuntime_block_1987_fallthrough (by simp)
          (by rw [hlenWord]; exact solcDecodeLenCheckOk_4_64 hlen hbig hsize) h1987
        by_cases hc0 : (calldataWord I.calldata 4).toNat < EVM.addressModulus
        · by_cases hc1 : (calldataWord I.calldata 36).toNat < EVM.addressModulus
          · obtain ⟨_, _, h2014⟩ := safeDecodeAddressPair h1999 (by simp) hc0 hc1
            have h9325 := safeRuntime_block_2014 (by simp) (by jump_dest) h2014
            have hdec : config.externalABI.decodeCalldata?
                (disablemoduleTransition.params.map Param.name)
                (transitionSignature disablemoduleTransition).paramTypes I.calldata =
                some (disableModuleArgs (calldataWord I.calldata 4) (calldataWord I.calldata 36)) :=
              decodeCalldata_address_address_ok hlen hbig hc0 hc1
            by_cases hauth : I.source = I.codeOwner
            · obtain ⟨_, _, h2022⟩ := safeAuthorizedTrace h9325 (by simp) hauth (by jump_dest)
              change RD fork safeBytecode I (.ofUInt256 g) (initState σ σ₀ (.ofUInt256 g) A I) ⟨2022⟩
                [calldataWord I.calldata 36, calldataWord I.calldata 4, ⟨0⟩]
                _ _ _ σ _ _ at h2022
              by_cases hgood : calldataWord I.calldata 36 ≠ ⟨0⟩ ∧ calldataWord I.calldata 36 ≠ ⟨1⟩
              · obtain ⟨_, _, h2046⟩ := safeDisableModuleReachCheck h2022 (by simp) hc1 hgood
                have hword := safeDisableModuleCheckWord σ I
                  (calldataWord I.calldata 4) (calldataWord I.calldata 36) hc0 hc1
                dsimp only [safeRuntime_block_2046_taken_memory, solcSlotWordAt] at hword
                have hmodule : moduleLink (initState σ σ₀ (.ofUInt256 g) A I)
                    (calldataWord I.calldata 4) =
                    UInt256.land (solcSlotWordAt (mapSlot (calldataWord I.calldata 4) ⟨1⟩) σ I)
                      solcAddrMask := by
                  rw [moduleLink, storageLoad_initState_ofUInt256_solcSlotWordAt]
                by_cases hlink : UInt256.land
                    (solcSlotWordAt (mapSlot (calldataWord I.calldata 4) ⟨1⟩) σ I) solcAddrMask =
                    calldataWord I.calldata 36
                · have hlink' := hmodule.trans hlink
                  obtain ⟨_, _, h2080⟩ := safeRuntime_block_2046_fallthrough (by simp)
                    (hword.trans (u256_sub_eq_zero_iff_eq.mpr hlink)) h2046
                  simp only [safeRuntime_block_2046_fallthrough_stack, safeAddressMask,
                    solcAddrMask_clean_left hc0] at h2080
                  cases hperm : I.perm with
                  | false =>
                      have hstatic := safeDisableModuleTraceStatic h2080 (by simp) hperm
                      have hbody := safeDisableModuleSourceStatic (fork := fork) (initState σ σ₀ (.ofUInt256 g) A
                        I)
                        (calldataWord I.calldata 4) (calldataWord I.calldata 36)
                        hc0 hc1 hvalue hauth hgood hlink' hperm
                      exact RDstatic.reEquivElim hcode hstatic fun hΞ ↦
                        reEquivSelectorExecution hdispatch hdec hbody (.staticHalt hΞ rfl)
                  | true =>
                      have hmem : (safeRuntime_block_2046_fallthrough_memory
                          (mem := solcFreePtrMem) (x0 := calldataWord I.calldata 4)
                          (x2 := ⟨0⟩)).size = 96 := by
                        simp only [safeRuntime_block_2046_fallthrough_memory, safeAddressMask,
                          solcAddrMask_clean_left hc0]
                        exact twoWordHashMem_size_96 _ _ solcFreePtrMem_size
                      have hret := safeDisableModuleTrace h2080 (by simp) hmem hc0 hc1 hperm
                      have hbody := safeDisableModuleSource (fork := fork) (hperm := by assumption) (initState σ σ₀ (.ofUInt256 g) A I)
                        (calldataWord I.calldata 4) (calldataWord I.calldata 36)
                        hc0 hc1 hvalue hauth hgood hlink'
                      refine reEquivReturnElim hcode hret fun _ _ hsuccess ↦ ?_
                      exact reEquivSelectorExecution hdispatch hdec hbody
                        (.success hsuccess rfl
                          (safeDisableModuleAccounts (initState σ σ₀ (.ofUInt256 g) A I)
                            (calldataWord I.calldata 4) (calldataWord I.calldata 36)).symm
                          (.abi (.fallthrough rfl rfl encodeReturnValues_nil)))
                · obtain ⟨_, _, h2186⟩ := safeRuntime_block_2046_taken (by simp)
                    (by rw [hword]; exact u256_sub_ne_zero_of_ne hlink) (by jump_dest) h2046
                  have hrev := safeDisableModuleTraceUnlinked h2186
                    (by simp [safeRuntime_block_2046_taken_stack])
                  have hbody := safeDisableModuleSourceUnlinked (fork := fork) (initState σ σ₀ (.ofUInt256 g) A I)
                    (calldataWord I.calldata 4) (calldataWord I.calldata 36)
                    hc0 hc1 hvalue hauth hgood (by rwa [hmodule])
                  exact RDrev.reEquivElim hcode hrev fun _ _ hΞ ↦
                    reEquivSelectorExecution hdispatch hdec hbody (.revert hΞ rfl)
              · have hrev := safeDisableModuleTraceInvalid h2022 (by simp) hc1 hgood
                have hbody := safeDisableModuleSourceInvalid (fork := fork) (initState σ σ₀ (.ofUInt256 g) A I)
                  (calldataWord I.calldata 4) (calldataWord I.calldata 36) hc1 hvalue hauth hgood
                exact RDrev.reEquivElim hcode hrev fun _ _ hΞ ↦
                  reEquivSelectorExecution hdispatch hdec hbody (.revert hΞ rfl)
            · have hrev := safeUnauthorizedTrace h9325
                (by simp [safeRuntime_block_2014_stack]) hauth
              exact reEquivSelectorRevert hcode hdispatch hrev fun locals ↦
                safeDisableModuleUnauthorized _ locals hvalue hauth
          · have hrev := safeDecodeAddressPairNoncanon1 h1999 (by simp) hc0 hc1
            exact reEquivSelectorDecodingFailed (cfg := config) hcode hdispatch
              (decodeCalldata_address_address_none_noncanon1 hlen hbig hc0 hc1) hrev
        · have hrev := safeDecodeAddressPairNoncanon0 h1999 (by simp) hc0
          exact reEquivSelectorDecodingFailed (cfg := config) hcode hdispatch
            (decodeCalldata_address_address_none_noncanon0 hlen hbig hc0) hrev
      · have h589 := safeRuntime_block_1987_taken (by simp)
          (by
            rw [hlenWord]
            change UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ ≠ ⟨0⟩
            rw [solcDecodeLenCheckShort_4_64 hlong (by omega) hsize]
            decide) (by jump_dest) h1987
        have hrev := safeRuntime_block_589 (by simp) h589
        exact reEquivSelectorDecodingFailed (cfg := config) hcode hdispatch
          (decodeCalldata_address_address_none_short hlong (by omega)) hrev
    · have h589 := safeRuntime_block_1987_taken (by simp)
        (by
          rw [hlenWord]
          change UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ ≠ ⟨0⟩
          rw [solcDecodeLenCheckHuge_4_64 (by omega) hsize]
          decide) (by jump_dest) h1987
      have hrev := safeRuntime_block_589 (by simp) h589
      exact reEquivSelectorDecodingFailed (cfg := config) hcode hdispatch
        (decodeCalldata_address_address_none_huge (by omega)) hrev
  · have h589 := safeRuntime_block_1980_taken (by simp) hvalue (by jump_dest) h1980
    have hrev := safeRuntime_block_589 (by simp) h589
    exact reEquivSelectorRevert hcode hdispatch hrev fun _ ↦ bodyReverts_nonPayable hvalue

/-- Refinement obligation for `disableModule` (`disablemoduleTransition`). -/
theorem safeDisablemoduleRefines
    (hcode : I.code = safeBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hdispatch : selectorDispatchMsg contract I.calldata = some disablemoduleTransition) :
    runtimeRefinementFor fork config contract σ σ₀ g A I := by
  exact safeDisablemoduleBodyCore hcode hsize hdispatch

end Benchmarks.Safe.ViaIR
