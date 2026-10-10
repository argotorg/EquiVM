import Benchmarks.UniswapV4PoolManager.Values
import Reasoning.TransientStorage

/-! PoolManager storage reads, using the concrete Solidity layout. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.UniswapV4PoolManager

set_option maxRecDepth 2000000

theorem addressScalarRead {f : Frame} {evm : EVM.State} {name : Ident} {slot : UInt256}
    (hf : f.contract = contract) (hbase : f.locals.get? name = none)
    (hty : storageTypeAt? contract.storage {base := name} = some (.elem .address))
    (hloc : config.storageBackend.locate? {base := name} = some (.leaf (addressOffset0Loc slot))) :
    evalExpr? config f evm (.storage {base := name}) =
      .ok (.address (AccountAddress.ofNat
        (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) solcAddrMask).toNat)) := by
  apply evalExpr_storage_scalar_value hbase
    (er := {base := name}) (loc := addressOffset0Loc slot) (t := .address)
    (hbackend := rfl) (hloc := hloc)
  · simp only [evalStorageRef, evalStorageRefSteps, pure, bind, EvalResult.bind]
  · rw [hf]; exact hty
  · exact storageLocLoad_address_offset0 _ _

theorem addressScalarWrite {f : Frame} {evm : EVM.State} {name : Ident} {slot : UInt256}
    (value : UInt256) (hf : f.contract = contract) (hc : value.toNat < EVM.addressModulus)
    (hbase : f.locals.get? name = none)
    (hty : storageTypeAt? contract.storage {base := name} = some (.elem .address))
    (hloc : config.storageBackend.locate? {base := name} = some (.leaf (addressOffset0Loc slot))) :
    assignStorageRef? config f evm .storage {base := name}
      (.address (AccountAddress.ofNat value.toNat)) =
      .ok (f, Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot
        (setAddressOffset0Word (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) value)) := by
  apply assignStorageRef_storage_scalar_value (slot := {base := name}) hbase
    (er := {base := name}) (hbackend := rfl) (hloc := hloc) (hleaf := Or.inl ⟨_, rfl⟩)
  · simp only [evalStorageRef, evalStorageRefSteps, pure, bind, EvalResult.bind]
  · rw [hf]; exact hty
  · exact storageLocStore_address_offset0 _ _ _ hc

/-- Both address getters load the low 160 bits of their physical slot. -/
theorem addressGetterBodyReturns (evm : EVM.State) (locals imms : Store)
    (name : Ident) (slot : UInt256)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < calldataLimit)
    (hname : ("__calldata" == name) = false)
    (hbase : locals.get? name = none)
    (hty : storageTypeAt? contract.storage {base := name} = some (.elem .address))
    (hloc : config.storageBackend.locate? {base := name} =
      some (.leaf (addressOffset0Loc slot))) :
    ExecTransitionBody config contract evm locals
      (nonpayableCalldataPrefix ++ [.return [.storage {base := name}]])
      (.returned (calldataFrame contract locals imms evm) evm
        (some [.address (AccountAddress.ofNat
          (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)
            solcAddrMask).toNat)])) imms := by
  apply guardedReturnBody hwv hhi
  exact addressScalarRead rfl ((store_get_ne locals _ hname).trans hbase) hty hloc

theorem rawSlots_loc (slot : UInt256) :
    config.storageBackend.locate?
      {base := "rawSlots", steps := [.aindex (.int (Int.ofNat slot.toNat))]} =
      some (.leaf (uint256Loc slot)) := by
  simp only [config, storageBackend, solidityStorageBackend, keyValueToWord_uint256,
    Nat.div_one, Nat.mod_one, Nat.zero_mul,
    u256_ofNat_toNat, u256_zero_add]
  rfl

theorem rawSlots_arrayType : storageTypeAt? contract.storage {base := "rawSlots"} =
    some (.array (.elem (.int (.uint ⟨256, by decide⟩))) UInt256.size) := by decide +kernel

theorem rawSlots_type (slot : UInt256) :
    storageTypeAt? contract.storage
      {base := "rawSlots", steps := [.aindex (.int (Int.ofNat slot.toNat))]} =
      some (.elem (.int (.uint ⟨256, by decide⟩))) := rfl

-- LIBRARY CANDIDATE: evaluation of a one-dimensional static array reference.
theorem evalStaticArrayRef {cfg : Config} {f : Frame} {evm : EVM.State}
    {base : Ident} {index : Expr} {i : Int} {ty : StorageType} {n : Nat}
    (htype : storageTypeAt? f.contract.storage {base := base} = some (.array ty n))
    (he : evalExpr? cfg f evm index = .ok (.int i)) (hbounds : 0 ≤ i ∧ i < (n : Int)) :
    evalStorageRef cfg f evm {base := base, steps := [.aindex index]} =
      .ok {base := base, steps := [.aindex (.int i)]} := by
  simp only [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, he, valueToKey?,
    bind, EvalResult.bind, pure, EvalResult.ofOption, arrayIndexInBounds?, htype,
    if_pos hbounds]

theorem rawSlots_ref {f : Frame} {evm : EVM.State} {index : Expr} {slot : UInt256}
    (hf : f.contract = contract)
    (he : evalExpr? config f evm index = .ok (.int (Int.ofNat slot.toNat))) :
    evalStorageRef config f evm {base := "rawSlots", steps := [.aindex index]} =
      .ok {base := "rawSlots", steps := [.aindex (.int (Int.ofNat slot.toNat))]} :=
  evalStaticArrayRef (by rw [hf]; exact rawSlots_arrayType) he
    ⟨Int.natCast_nonneg _, Int.ofNat_lt.mpr slot.val.isLt⟩

theorem rawSlots_read {f : Frame} {evm : EVM.State} {index : Expr} {slot : UInt256}
    (hf : f.contract = contract) (hbase : f.locals.get? "rawSlots" = none)
    (he : evalExpr? config f evm index = .ok (.int (Int.ofNat slot.toNat))) :
    evalExpr? config f evm (.storage {base := "rawSlots", steps := [.aindex index]}) =
      .ok (.int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot).toNat)) := by
  apply evalExpr_storage_scalar_value hbase (rawSlots_ref hf he)
    (hbackend := rfl) (hloc := rawSlots_loc slot)
  · rw [hf]; exact rawSlots_type slot
  · exact storageLocLoad_uint256 evm slot

theorem rawTransient_loc (slot : UInt256) :
    config.transientBackend.locate?
      {base := "rawTransient", steps := [.aindex (.int (Int.ofNat slot.toNat))]} =
      some (.leaf (uint256Loc slot)) := by
  simp only [config, solidityTransientStorageBackend, keyValueToWord_uint256,
    Nat.div_one, Nat.mod_one, Nat.zero_mul, u256_ofNat_toNat, u256_zero_add]
  rfl

theorem rawTransient_arrayType : storageTypeAt? contract.transient {base := "rawTransient"} =
    some (.array (.elem (.int (.uint ⟨256, by decide⟩))) UInt256.size) := by decide +kernel

theorem rawTransient_type (slot : UInt256) :
    storageTypeAt? contract.transient
      {base := "rawTransient", steps := [.aindex (.int (Int.ofNat slot.toNat))]} =
      some (.elem (.int (.uint ⟨256, by decide⟩))) := rfl

-- LIBRARY CANDIDATE: evaluation of a one-dimensional transient static array reference.
theorem evalStaticTransientArrayRef {cfg : Config} {f : Frame} {evm : EVM.State}
    {base : Ident} {index : Expr} {i : Int} {ty : StorageType} {n : Nat}
    (htype : storageTypeAt? f.contract.transient {base := base} = some (.array ty n))
    (he : evalExpr? cfg f evm index = .ok (.int i)) (hbounds : 0 ≤ i ∧ i < (n : Int)) :
    evalTransientStorageRef cfg f evm {base := base, steps := [.aindex index]} =
      .ok {base := base, steps := [.aindex (.int i)]} := by
  simp only [evalTransientStorageRef, evalTransientStorageRefSteps, evalTransientStorageRefStep,
    he, valueToKey?, bind, EvalResult.bind, pure, EvalResult.ofOption, arrayIndexInBounds?,
    htype, if_pos hbounds]

theorem rawTransient_ref {f : Frame} {evm : EVM.State} {index : Expr} {slot : UInt256}
    (hf : f.contract = contract)
    (he : evalExpr? config f evm index = .ok (.int (Int.ofNat slot.toNat))) :
    evalTransientStorageRef config f evm {base := "rawTransient", steps := [.aindex index]} =
      .ok {base := "rawTransient", steps := [.aindex (.int (Int.ofNat slot.toNat))]} :=
  evalStaticTransientArrayRef (by rw [hf]; exact rawTransient_arrayType) he
    ⟨Int.natCast_nonneg _, Int.ofNat_lt.mpr slot.val.isLt⟩

theorem rawTransient_read {f : Frame} {evm : EVM.State} {index : Expr} {slot : UInt256}
    (hf : f.contract = contract)
    (he : evalExpr? config f evm index = .ok (.int (Int.ofNat slot.toNat))) :
    evalExpr? config f evm (.transient {base := "rawTransient", steps := [.aindex index]}) =
      .ok (.int (Int.ofNat (Solm.EVM.transientLoad evm evm.executionEnv.codeOwner slot).toNat)) := by
  apply evalExpr_transient_scalar_value (rawTransient_ref hf he)
    (hbackend := rfl) (hloc := rawTransient_loc slot)
  · rw [hf]; exact rawTransient_type slot
  · exact transientLocLoad_uint256 evm slot

def mappingSlotWord (key base : UInt256) : UInt256 :=
  uInt256OfByteArray (KEC (key.toByteArray ++ base.toByteArray))

-- LIBRARY CANDIDATE: general word, mapping reference, or scratch-memory fact.
theorem evalMappingRef {cfg : Config} {f : Frame} {evm : EVM.State}
    {base : Ident} {index : Expr} {value : Value} {key : KeyValue}
    (he : evalExpr? cfg f evm index = .ok value) (hk : valueToKey? value = some key) :
    evalStorageRef cfg f evm {base := base, steps := [.mindex index]} =
      .ok {base := base, steps := [.mindex key]} := by
  simp only [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, he, hk,
    bind, EvalResult.bind, pure, EvalResult.ofOption]

theorem protocolFeesAccrued_loc (w : UInt256) (hcanon : w.toNat < EVM.addressModulus) :
    config.storageBackend.locate?
      {base := "protocolFeesAccrued", steps := [.mindex (.address (AccountAddress.ofNat w.toNat))]} =
      some (.leaf (uint256Loc (mappingSlotWord w ⟨1⟩))) := by
  simp only [config, storageBackend, solidityStorageBackend, keyValueToWord_address_of_canonical w hcanon]
  rfl

theorem protocolFeesAccrued_type (a : AccountAddress) :
    storageTypeAt? contract.storage {base := "protocolFeesAccrued", steps := [.mindex (.address a)]} =
      some (.elem (.int (.uint ⟨256, by decide⟩))) := rfl

-- LIBRARY CANDIDATE: general word, mapping reference, or scratch-memory fact.
theorem evalMappingRef2 {cfg : Config} {f : Frame} {evm : EVM.State}
    {base : Ident} {e0 e1 : Expr} {v0 v1 : Value} {k0 k1 : KeyValue}
    (h0 : evalExpr? cfg f evm e0 = .ok v0) (hk0 : valueToKey? v0 = some k0)
    (h1 : evalExpr? cfg f evm e1 = .ok v1) (hk1 : valueToKey? v1 = some k1) :
    evalStorageRef cfg f evm {base := base, steps := [.mindex e0, .mindex e1]} =
      .ok {base := base, steps := [.mindex k0, .mindex k1]} := by
  simp only [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, h0, hk0, h1, hk1,
    bind, EvalResult.bind, pure, EvalResult.ofOption]

theorem balanceOf_loc (w id : UInt256) (hcanon : w.toNat < EVM.addressModulus) :
    config.storageBackend.locate?
      {base := "balanceOf", steps := [.mindex (.address (AccountAddress.ofNat w.toNat)),
        .mindex (.int (Int.ofNat id.toNat))]} =
      some (.leaf (uint256Loc (mappingSlotWord id (mappingSlotWord w ⟨4⟩)))) := by
  simp only [config, storageBackend, solidityStorageBackend,
    keyValueToWord_address_of_canonical w hcanon, keyValueToWord_uint256]
  rfl

theorem balanceOf_type (a : AccountAddress) (id : Int) :
    storageTypeAt? contract.storage
      {base := "balanceOf", steps := [.mindex (.address a), .mindex (.int id)]} =
      some (.elem (.int (.uint ⟨256, by decide⟩))) := rfl

theorem isOperator_loc (a b : UInt256)
    (hca : a.toNat < EVM.addressModulus) (hcb : b.toNat < EVM.addressModulus) :
    config.storageBackend.locate?
      {base := "isOperator", steps := [.mindex (.address (AccountAddress.ofNat a.toNat)),
        .mindex (.address (AccountAddress.ofNat b.toNat))]} =
      some (.leaf (boolOffset0Loc (mappingSlotWord b (mappingSlotWord a ⟨3⟩)))) := by
  simp only [config, storageBackend, solidityStorageBackend,
    keyValueToWord_address_of_canonical a hca, keyValueToWord_address_of_canonical b hcb]
  rfl

theorem isOperator_type (a b : AccountAddress) :
    storageTypeAt? contract.storage
      {base := "isOperator", steps := [.mindex (.address a), .mindex (.address b)]} =
      some (.elem .bool) := rfl

-- LIBRARY CANDIDATE: evaluation of a three-key mapping reference.
theorem evalMappingRef3 {cfg : Config} {f : Frame} {evm : EVM.State}
    {base : Ident} {e0 e1 e2 : Expr} {v0 v1 v2 : Value} {k0 k1 k2 : KeyValue}
    (h0 : evalExpr? cfg f evm e0 = .ok v0) (hk0 : valueToKey? v0 = some k0)
    (h1 : evalExpr? cfg f evm e1 = .ok v1) (hk1 : valueToKey? v1 = some k1)
    (h2 : evalExpr? cfg f evm e2 = .ok v2) (hk2 : valueToKey? v2 = some k2) :
    evalStorageRef cfg f evm {base := base, steps := [.mindex e0, .mindex e1, .mindex e2]} =
      .ok {base := base, steps := [.mindex k0, .mindex k1, .mindex k2]} := by
  simp only [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, h0, hk0, h1, hk1, h2, hk2,
    bind, EvalResult.bind, pure, EvalResult.ofOption]

theorem allowance_loc (a b id : UInt256)
    (hca : a.toNat < EVM.addressModulus) (hcb : b.toNat < EVM.addressModulus) :
    config.storageBackend.locate?
      {base := "allowance", steps := [.mindex (.address (AccountAddress.ofNat a.toNat)),
        .mindex (.address (AccountAddress.ofNat b.toNat)), .mindex (.int (Int.ofNat id.toNat))]} =
      some (.leaf (uint256Loc (mappingSlotWord id (mappingSlotWord b (mappingSlotWord a ⟨5⟩))))) := by
  simp only [config, storageBackend, solidityStorageBackend, keyValueToWord_uint256,
    keyValueToWord_address_of_canonical a hca, keyValueToWord_address_of_canonical b hcb]
  rfl

theorem allowance_type (a b : AccountAddress) (id : Int) :
    storageTypeAt? contract.storage
      {base := "allowance", steps := [.mindex (.address a), .mindex (.address b), .mindex (.int id)]} =
      some (.elem (.int (.uint ⟨256, by decide⟩))) := rfl

theorem allowanceWrite {f : Frame} {evm : EVM.State} {e0 e1 e2 : Expr}
    (a b id amount : UInt256) (hf : f.contract = contract)
    (hca : a.toNat < EVM.addressModulus) (hcb : b.toNat < EVM.addressModulus)
    (hbase : f.locals.get? "allowance" = none)
    (h0 : evalExpr? config f evm e0 = .ok (.address (AccountAddress.ofNat a.toNat)))
    (h1 : evalExpr? config f evm e1 = .ok (.address (AccountAddress.ofNat b.toNat)))
    (h2 : evalExpr? config f evm e2 = .ok (.int (Int.ofNat id.toNat))) :
    assignStorageRef? config f evm .storage
      {base := "allowance", steps := [.mindex e0, .mindex e1, .mindex e2]}
      (.int (Int.ofNat amount.toNat)) =
      .ok (f, Solm.EVM.storageStore evm evm.executionEnv.codeOwner
        (mappingSlotWord id (mappingSlotWord b (mappingSlotWord a ⟨5⟩))) amount) := by
  apply assignStorageRef_storage_scalar
    (slot := {base := "allowance", steps := [.mindex e0, .mindex e1, .mindex e2]})
    hbase (evalMappingRef3 h0 rfl h1 rfl h2 rfl)
    (hbackend := rfl) (hloc := allowance_loc a b id hca hcb) (hleaf := Or.inl ⟨_, rfl⟩)
  · rw [hf]; exact allowance_type _ _ _
  · exact storageLocStore_uint256 _ _ _

theorem isOperatorWrite {f : Frame} {evm : EVM.State} {e0 e1 : Expr}
    (a b approved : UInt256) (hf : f.contract = contract)
    (hca : a.toNat < EVM.addressModulus) (hcb : b.toNat < EVM.addressModulus)
    (hbase : f.locals.get? "isOperator" = none)
    (h0 : evalExpr? config f evm e0 = .ok (.address (AccountAddress.ofNat a.toNat)))
    (h1 : evalExpr? config f evm e1 = .ok (.address (AccountAddress.ofNat b.toNat))) :
    assignStorageRef? config f evm .storage
      {base := "isOperator", steps := [.mindex e0, .mindex e1]}
      (wordToElem .bool approved) =
      .ok (f, Solm.EVM.storageStore evm evm.executionEnv.codeOwner
        (mappingSlotWord b (mappingSlotWord a ⟨3⟩))
        (setBoolOffset0Word (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
          (mappingSlotWord b (mappingSlotWord a ⟨3⟩))) approved)) := by
  apply assignStorageRef_storage_scalar_value
    (slot := {base := "isOperator", steps := [.mindex e0, .mindex e1]})
    hbase (evalMappingRef2 h0 rfl h1 rfl)
    (hbackend := rfl) (hloc := isOperator_loc a b hca hcb) (hleaf := Or.inl ⟨_, rfl⟩)
  · rw [hf]; exact isOperator_type _ _
  · exact storageLocStore_bool_word_offset0 _ _ _

def balanceSlot (owner id : UInt256) : UInt256 := mappingSlotWord id (mappingSlotWord owner ⟨4⟩)

def balanceWord (evm : EVM.State) (owner id : UInt256) : UInt256 :=
  Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (balanceSlot owner id)

def balancePost (evm : EVM.State) (owner id value : UInt256) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner (balanceSlot owner id) value

theorem balancePost_env (evm : EVM.State) (owner id value : UInt256) :
    (balancePost evm owner id value).executionEnv = evm.executionEnv :=
  storageStore_executionEnv _ _ _ _

theorem balanceOfRead {f : Frame} {evm : EVM.State} {e0 e1 : Expr}
    (owner id : UInt256) (hf : f.contract = contract)
    (hc : owner.toNat < EVM.addressModulus) (hbase : f.locals.get? "balanceOf" = none)
    (h0 : evalExpr? config f evm e0 = .ok (.address (AccountAddress.ofNat owner.toNat)))
    (h1 : evalExpr? config f evm e1 = .ok (.int (Int.ofNat id.toNat))) :
    evalExpr? config f evm (.storage {base := "balanceOf", steps := [.mindex e0, .mindex e1]}) =
      .ok (.int (Int.ofNat (balanceWord evm owner id).toNat)) := by
  apply evalExpr_storage_scalar_value hbase (evalMappingRef2 (base := "balanceOf") h0 rfl h1 rfl)
    (hbackend := rfl) (hloc := balanceOf_loc owner id hc)
  · rw [hf]; exact balanceOf_type _ _
  · exact storageLocLoad_uint256 _ _

theorem balanceOfWrite {f : Frame} {evm : EVM.State} {e0 e1 : Expr}
    (owner id value : UInt256) (hf : f.contract = contract)
    (hc : owner.toNat < EVM.addressModulus) (hbase : f.locals.get? "balanceOf" = none)
    (h0 : evalExpr? config f evm e0 = .ok (.address (AccountAddress.ofNat owner.toNat)))
    (h1 : evalExpr? config f evm e1 = .ok (.int (Int.ofNat id.toNat))) :
    assignStorageRef? config f evm .storage {base := "balanceOf", steps := [.mindex e0, .mindex e1]}
      (.int (Int.ofNat value.toNat)) = .ok (f, balancePost evm owner id value) := by
  apply assignStorageRef_storage_scalar
    (slot := {base := "balanceOf", steps := [.mindex e0, .mindex e1]})
    hbase (evalMappingRef2 h0 rfl h1 rfl)
    (hbackend := rfl) (hloc := balanceOf_loc owner id hc) (hleaf := Or.inl ⟨_, rfl⟩)
  · rw [hf]; exact balanceOf_type _ _
  · exact storageLocStore_uint256 _ _ _

def operatorWord (evm : EVM.State) (owner operator : UInt256) : UInt256 :=
  UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
    (mappingSlotWord operator (mappingSlotWord owner ⟨3⟩))) ⟨255⟩

theorem isOperatorRead {f : Frame} {evm : EVM.State} {e0 e1 : Expr}
    (owner operator : UInt256) (hf : f.contract = contract)
    (hca : owner.toNat < EVM.addressModulus) (hcb : operator.toNat < EVM.addressModulus)
    (hbase : f.locals.get? "isOperator" = none)
    (h0 : evalExpr? config f evm e0 = .ok (.address (AccountAddress.ofNat owner.toNat)))
    (h1 : evalExpr? config f evm e1 = .ok (.address (AccountAddress.ofNat operator.toNat))) :
    evalExpr? config f evm (.storage {base := "isOperator", steps := [.mindex e0, .mindex e1]}) =
      .ok (wordToElem .bool (operatorWord evm owner operator)) := by
  apply evalExpr_storage_scalar_value hbase (evalMappingRef2 (base := "isOperator") h0 rfl h1 rfl)
    (hbackend := rfl) (hloc := isOperator_loc owner operator hca hcb)
  · rw [hf]; exact isOperator_type _ _
  · exact storageLocLoad_bool_offset0 _ _

def allowanceSlot (owner spender id : UInt256) : UInt256 :=
  mappingSlotWord id (mappingSlotWord spender (mappingSlotWord owner ⟨5⟩))

def allowanceWord (evm : EVM.State) (owner spender id : UInt256) : UInt256 :=
  Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (allowanceSlot owner spender id)

theorem allowanceRead {f : Frame} {evm : EVM.State} {e0 e1 e2 : Expr}
    (owner spender id : UInt256) (hf : f.contract = contract)
    (hca : owner.toNat < EVM.addressModulus) (hcb : spender.toNat < EVM.addressModulus)
    (hbase : f.locals.get? "allowance" = none)
    (h0 : evalExpr? config f evm e0 = .ok (.address (AccountAddress.ofNat owner.toNat)))
    (h1 : evalExpr? config f evm e1 = .ok (.address (AccountAddress.ofNat spender.toNat)))
    (h2 : evalExpr? config f evm e2 = .ok (.int (Int.ofNat id.toNat))) :
    evalExpr? config f evm (.storage {base := "allowance", steps := [.mindex e0, .mindex e1, .mindex e2]}) =
      .ok (.int (Int.ofNat (allowanceWord evm owner spender id).toNat)) := by
  apply evalExpr_storage_scalar_value hbase (evalMappingRef3 (base := "allowance") h0 rfl h1 rfl h2 rfl)
    (hbackend := rfl) (hloc := allowance_loc owner spender id hca hcb)
  · rw [hf]; exact allowance_type _ _ _
  · exact storageLocLoad_uint256 _ _

end Benchmarks.UniswapV4PoolManager
