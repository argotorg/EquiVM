import Benchmarks.Safe.Membership
import Benchmarks.Safe.Authorization
import Reasoning.WordArithmetic

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe

def moduleLink (evm : EVM.State) (key : UInt256) : UInt256 :=
  UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (mapSlot key ⟨1⟩))
    solcAddrMask

def moduleLinkAt (σ : AccountMap) (I : ExecutionEnv) (key : UInt256) : UInt256 :=
  UInt256.land (solcSlotWordAt (mapSlot key ⟨1⟩) σ I) solcAddrMask

theorem moduleLink_eq_at (evm : EVM.State) (key : UInt256) :
    moduleLink evm key = moduleLinkAt evm.accountMap evm.executionEnv key := by
  simp only [moduleLink, moduleLinkAt, storageLoad_eq_solcSlotWord]
  rfl

def writeModuleLink (evm : EVM.State) (key value : UInt256) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner (mapSlot key ⟨1⟩)
    (setAddressOffset0Word
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (mapSlot key ⟨1⟩)) value)

theorem safeEvalModuleLink (evm : EVM.State) (locals : Store) (expr : Expr) (key : UInt256)
    (hbase : locals["modules"]? = none)
    (hcanon : key.toNat < EVM.addressModulus)
    (heval : evalExpr? config { contract := contract, locals := locals } evm expr =
      .ok (.address (AccountAddress.ofNat key.toNat))) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.storage (modulesRef expr)) = .ok (.address (AccountAddress.ofNat (moduleLink evm
        key).toNat)) := by
  apply evalExpr_storage_scalar_value (er := { base := "modules", steps :=
      [.mindex (.address (AccountAddress.ofNat key.toNat))] })
    (loc := addressOffset0Loc (mapSlot key ⟨1⟩))
  · exact hbase
  · simp [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, modulesRef,
      heval, valueToKey?, EvalResult.bind, EvalResult.ofOption, bind, pure]
  · rfl
  · rfl
  · change some (StorageAddr.leaf (addrLoc (mapSlot
      (keyValueToWord (.address (AccountAddress.ofNat key.toNat))) ⟨1⟩))) = _
    rw [keyValueToWord_address_of_canonical key hcanon]
    rfl
  · exact storageLocLoad_address_offset0 evm (mapSlot key ⟨1⟩)

theorem safeAssignModuleLink (evm : EVM.State) (locals : Store)
    (expr : Expr) (key value : UInt256)
    (hbase : locals["modules"]? = none)
    (hkey : key.toNat < EVM.addressModulus) (hvalue : value.toNat < EVM.addressModulus)
    (heval : evalExpr? config { contract := contract, locals := locals } evm expr =
      .ok (.address (AccountAddress.ofNat key.toNat))) :
    assignStorageRef? config { contract := contract, locals := locals } evm .storage
      (modulesRef expr) (.address (AccountAddress.ofNat value.toNat)) =
      .ok ({ contract := contract, locals := locals }, writeModuleLink evm key value) := by
  apply assignStorageRef_storage_scalar_value (er := { base := "modules", steps :=
      [.mindex (.address (AccountAddress.ofNat key.toNat))] })
    (loc := addressOffset0Loc (mapSlot key ⟨1⟩))
  · exact hbase
  · simp [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, modulesRef,
      heval, valueToKey?, EvalResult.bind, EvalResult.ofOption, bind, pure]
  · rfl
  · rfl
  · change some (StorageAddr.leaf (addrLoc (mapSlot
      (keyValueToWord (.address (AccountAddress.ofNat key.toNat))) ⟨1⟩))) = _
    rw [keyValueToWord_address_of_canonical key hkey]
    rfl
  · exact .inl ⟨_, rfl⟩
  · exact storageLocStore_address_offset0 evm (mapSlot key ⟨1⟩) value hvalue

-- LIBRARY CANDIDATE: equality to the zero address after canonical address evaluation.
theorem evalAddressZero {cfg : Config} {frame : Frame} {evm : EVM.State}
    {expr : Expr} {w : UInt256} (hcanon : w.toNat < EVM.addressModulus)
    (heval : evalExpr? cfg frame evm expr = .ok (.address (AccountAddress.ofNat w.toNat))) :
    evalExpr? cfg frame evm (eqE expr zeroAddr) = .ok (.bool (decide (w = ⟨0⟩))) := by
  rw [eqE, evalExpr_binary_nonshort (by decide) (by decide), heval]
  simp [zeroAddr, addrSt, evalExpr?, castValue?, evalBinaryOp?,
    EvalResult.bind, EvalResult.ofOption, bind, pure]
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, Value.address.injEq, decide_eq_true_eq,
    canonicalAddress_eq_zero_iff w hcanon]

theorem safeModuleSentinelSlot : mapSlot ⟨1⟩ ⟨1⟩ =
    UInt256.ofNat 92458281274488595289803937127152923398167637295201432141969818930235769911599 :=
      by
  native_decide

-- LIBRARY CANDIDATE: mapping hashing with the slot written before the key.
theorem keyAfterSlotHash (key slot : UInt256) {mem : ByteArray} (hmem : mem.size = 96) :
    keccakWord ⟨0⟩ (UInt256.ofNat 64) (wordAt0Mem key (wordAt32Mem slot mem)) =
      mapSlot key slot := by
  change UInt256.ofNat (fromByteArrayBigEndian
    (KEC ((wordAt0Mem key (wordAt32Mem slot mem)).readWithPadding 0 64))) =
      solcMappingSlot slot key
  apply wordAt0Mem_solcMappingSlot_of_read32 key slot (wordAt32Mem_size_96 slot hmem)
  exact toByteArray_write32_read_back mem slot 32 (by omega)

-- LIBRARY CANDIDATE: compare two canonically evaluated addresses by their EVM words.
theorem evalAddressEq {cfg : Config} {frame : Frame} {evm : EVM.State}
    {lhs rhs : Expr} {a b : UInt256}
    (ha : a.toNat < EVM.addressModulus) (hb : b.toNat < EVM.addressModulus)
    (hl : evalExpr? cfg frame evm lhs = .ok (.address (AccountAddress.ofNat a.toNat)))
    (hr : evalExpr? cfg frame evm rhs = .ok (.address (AccountAddress.ofNat b.toNat))) :
    evalExpr? cfg frame evm (eqE lhs rhs) = .ok (.bool (decide (a = b))) := by
  have heq : AccountAddress.ofNat a.toNat = AccountAddress.ofNat b.toNat ↔ a = b := by
    simpa only [accountAddress_ofUInt256_eq_ofNat_toNat] using
      accountAddress_ofUInt256_eq_iff_of_canonical ha hb
  rw [eqE, evalExpr_binary_nonshort (by decide) (by decide), hl, hr]
  simp [evalBinaryOp?, EvalResult.bind, bind, pure]
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, Value.address.injEq, decide_eq_true_eq, heq]

-- LIBRARY CANDIDATE: compare canonical address expressions for inequality.
theorem evalAddressNe {cfg : Config} {frame : Frame} {evm : EVM.State}
    {lhs rhs : Expr} {a b : UInt256}
    (ha : a.toNat < EVM.addressModulus) (hb : b.toNat < EVM.addressModulus)
    (hl : evalExpr? cfg frame evm lhs = .ok (.address (AccountAddress.ofNat a.toNat)))
    (hr : evalExpr? cfg frame evm rhs = .ok (.address (AccountAddress.ofNat b.toNat))) :
    evalExpr? cfg frame evm (neE lhs rhs) = .ok (.bool (decide (a ≠ b))) := by
  have heq : AccountAddress.ofNat a.toNat = AccountAddress.ofNat b.toNat ↔ a = b := by
    simpa only [accountAddress_ofUInt256_eq_ofNat_toNat] using
      accountAddress_ofUInt256_eq_iff_of_canonical ha hb
  rw [neE, evalExpr_binary_nonshort (by decide) (by decide), hl, hr]
  simp [evalBinaryOpNeAddress, EvalResult.bind, bind, pure]
  apply Bool.eq_iff_iff.mpr
  simpa only [beq_iff_eq, Value.address.injEq, decide_eq_true_eq] using heq

theorem safeEvalModuleSentinel (evm : EVM.State) (locals : Store) :
    evalExpr? config { contract := contract, locals := locals } evm sentinelAddr =
      .ok (.address (AccountAddress.ofNat (⟨1⟩ : UInt256).toNat)) := by
  simp [sentinelAddr, addrSt, evalExpr?, castValue?, EvalResult.bind, EvalResult.ofOption, bind,
    pure]
  rfl

end Benchmarks.Safe
