import Benchmarks.Morpho.MetaMorphoV1_1.Storage
import Reasoning.PackedStorage

/-! Storage updates and static-call handling shared by administrative functions. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MetaMorphoV1_1

-- LIBRARY CANDIDATE: falling through a function with no return values produces empty returndata.
theorem voidReturnEquiv : returnEquiv ByteArray.empty none [] := by
  refine returnEquiv.fallthrough rfl rfl ?_
  simp [encodeReturnValues?, encodeABIValues?, abiTupleHeadSize?, encodeABIValuesFrom?]
  rfl

theorem assignStorage_curator (evm : EVM.State) (locals imms : Store) (w : UInt256)
    (hbase : locals.get? "curator" = none) (hcanon : w.toNat < EVM.addressModulus) :
    assignStorageRef? config { contract := contract, locals := locals, immutables := imms }
      evm .storage ⟨"curator", []⟩ (.address (AccountAddress.ofNat w.toNat)) =
      .ok ({ contract := contract, locals := locals, immutables := imms },
        Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨10⟩
          (setAddressOffset0Word (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨10⟩) w)) :=
  assignStorageRef_storage_scalar_value (er := ⟨"curator", []⟩) (ty := .elem .address)
    hbase (by simp [evalStorageRef, evalStorageRefSteps, bind, pure, EvalResult.bind])
    rfl rfl rfl (Or.inl ⟨_, rfl⟩) (storageLocStore_address_offset0 evm ⟨10⟩ w hcanon)

theorem assignStorage_owner (evm : EVM.State) (locals imms : Store) (w : UInt256)
    (hbase : locals.get? "_owner" = none) (hcanon : w.toNat < EVM.addressModulus) :
    assignStorageRef? config { contract := contract, locals := locals, immutables := imms }
      evm .storage ⟨"_owner", []⟩ (.address (AccountAddress.ofNat w.toNat)) =
      .ok ({ contract := contract, locals := locals, immutables := imms },
        Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨8⟩
          (setAddressOffset0Word (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩) w)) :=
  assignStorageRef_storage_scalar_value (er := ⟨"_owner", []⟩) (ty := .elem .address)
    hbase (by simp [evalStorageRef, evalStorageRefSteps, bind, pure, EvalResult.bind])
    rfl rfl rfl (Or.inl ⟨_, rfl⟩) (storageLocStore_address_offset0 evm ⟨8⟩ w hcanon)

theorem assignStorage_pendingOwner (evm : EVM.State) (locals imms : Store) (w : UInt256)
    (hbase : locals.get? "_pendingOwner" = none) (hcanon : w.toNat < EVM.addressModulus) :
    assignStorageRef? config { contract := contract, locals := locals, immutables := imms }
      evm .storage ⟨"_pendingOwner", []⟩ (.address (AccountAddress.ofNat w.toNat)) =
      .ok ({ contract := contract, locals := locals, immutables := imms },
        Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨9⟩
          (setAddressOffset0Word (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨9⟩) w)) :=
  assignStorageRef_storage_scalar_value (er := ⟨"_pendingOwner", []⟩) (ty := .elem .address)
    hbase (by simp [evalStorageRef, evalStorageRefSteps, bind, pure, EvalResult.bind])
    rfl rfl rfl (Or.inl ⟨_, rfl⟩) (storageLocStore_address_offset0 evm ⟨9⟩ w hcanon)

theorem assignStorage_skimRecipient (evm : EVM.State) (locals imms : Store) (w : UInt256)
    (hbase : locals.get? "skimRecipient" = none) (hcanon : w.toNat < EVM.addressModulus) :
    assignStorageRef? config { contract := contract, locals := locals, immutables := imms }
      evm .storage ⟨"skimRecipient", []⟩ (.address (AccountAddress.ofNat w.toNat)) =
      .ok ({ contract := contract, locals := locals, immutables := imms },
        Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨19⟩
          (setAddressOffset0Word (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨19⟩) w)) :=
  assignStorageRef_storage_scalar_value (er := ⟨"skimRecipient", []⟩) (ty := .elem .address)
    hbase (by simp [evalStorageRef, evalStorageRefSteps, bind, pure, EvalResult.bind])
    rfl rfl rfl (Or.inl ⟨_, rfl⟩) (storageLocStore_address_offset0 evm ⟨19⟩ w hcanon)

-- LIBRARY CANDIDATE: delete a low address through the Solidity storage backend.
theorem deleteStorage_address_offset0 {cfg : Config} {layout : StorageLayout}
    {solm : Frame} {evm : EVM.State} {ref : StorageRef} {er : EvaledStorageRef}
    {slot : UInt256}
    (hcfg : cfg.storageBackend = solidityStorageBackend layout)
    (hresolve : resolveStorageRef? cfg solm evm ref = .ok (er, .elem .address))
    (hloc : layout er = some (.leaf (addressOffset0Loc slot))) :
    deleteStorage? cfg solm evm ref =
      .ok (Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot
        (setAddressOffset0Word
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot) ⟨0⟩)) := by
  simp only [deleteStorage?, usesTransientStorage_of_resolveStorageRef hresolve,
    Bool.false_eq_true, ↓reduceIte, hresolve, EvalResult.bind, bind]
  rw [hcfg]
  exact clearStorage_addr_zero hloc

theorem deleteStorage_pendingOwner (evm : EVM.State) (locals imms : Store)
    (hbase : locals.get? "_pendingOwner" = none) :
    deleteStorage? config { contract := contract, locals := locals, immutables := imms }
      evm ⟨"_pendingOwner", []⟩ =
      .ok (Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨9⟩
        (setAddressOffset0Word (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨9⟩) ⟨0⟩)) := by
  exact deleteStorage_address_offset0 (er := ⟨"_pendingOwner", []⟩) rfl
    (resolveStorageRef?_ok hbase
      (by simp [evalStorageRef, evalStorageRefSteps, bind, pure, EvalResult.bind]) rfl) rfl

-- LIBRARY CANDIDATE: the solc low-address merge immediately preceding SSTORE.
def packedAddressStoreWf (code : ByteArray) (pc slot : UInt256) : Prop :=
  let p2 := pc + ⟨2⟩
  let p4 := p2 + ⟨2⟩
  let p6 := p4 + ⟨2⟩
  let p7 := p6 + ⟨1⟩
  let p8 := p7 + ⟨1⟩
  let p9 := p8 + ⟨1⟩
  let p10 := p9 + ⟨1⟩
  let p11 := p10 + ⟨1⟩
  let p12 := p11 + ⟨1⟩
  let p14 := p12 + ⟨2⟩
  decode code pc = some (.Push .PUSH1, some (⟨1⟩, 1)) ∧
  decode code p2 = some (.Push .PUSH1, some (⟨1⟩, 1)) ∧
  decode code p4 = some (.Push .PUSH1, some (⟨160⟩, 1)) ∧
  decode code p6 = some (.SHL, none) ∧
  decode code p7 = some (.SUB, none) ∧
  decode code p8 = some (.NOT, none) ∧
  decode code p9 = some (.AND, none) ∧
  decode code p10 = some (.DUP2, none) ∧
  decode code p11 = some (.OR, none) ∧
  decode code p12 = some (.Push .PUSH1, some (slot, 1)) ∧
  decode code p14 = some (.SSTORE, none)

-- LIBRARY CANDIDATE: a packed address assignment halts at its first SSTORE in static mode.
theorem packedAddressStoreStatic {code : ByteArray} {I : ExecutionEnv} {g : Sat256}
    {s0 : State} {pc slot old addr : UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024) (hperm : I.perm = false)
    (hwf : packedAddressStoreWf code pc slot)
    (rd : RD code I g s0 pc (old :: addr :: R) mem aw rdata σ k C) :
    RDstatic code g s0 := by
  rcases hwf with ⟨hd0, hd2, hd4, hd6, hd7, hd8, hd9, hd10, hd11, hd12, hd14⟩
  have r2 := rd.push1 ⟨1⟩ hd0 (by evm_ov)
  have r4 := r2.push1 ⟨1⟩ hd2 (by evm_ov)
  have r6 := r4.push1 ⟨160⟩ hd4 (by evm_ov)
  have r7 := r6.shl hd6 (by evm_ov)
  have r8 := r7.sub hd7 (by evm_ov)
  have r9 := r8.not hd8 (by evm_ov)
  have r10 := r9.and hd9 (by evm_ov)
  have r11 := r10.dup2 hd10 (by evm_ov)
  have r12 := r11.or hd11 (by evm_ov)
  have r14 := r12.push1 slot hd12 (by evm_ov)
  exact r14.sstoreStatic hperm hd14 (by evm_ov)

-- LIBRARY CANDIDATE: the solc prefix clearing a packed low address.
def clearAddressStoreWf (code : ByteArray) (pc slot : UInt256) : Prop :=
  let p2 := pc + ⟨2⟩
  let p3 := p2 + ⟨1⟩
  let p4 := p3 + ⟨1⟩
  let p6 := p4 + ⟨2⟩
  let p8 := p6 + ⟨2⟩
  let p10 := p8 + ⟨2⟩
  let p11 := p10 + ⟨1⟩
  let p12 := p11 + ⟨1⟩
  let p13 := p12 + ⟨1⟩
  let p14 := p13 + ⟨1⟩
  let p15 := p14 + ⟨1⟩
  let p16 := p15 + ⟨1⟩
  let p17 := p16 + ⟨1⟩
  let p18 := p17 + ⟨1⟩
  decode code pc = some (.Push .PUSH1, some (slot, 1)) ∧
  decode code p2 = some (.DUP1, none) ∧
  decode code p3 = some (.SLOAD, none) ∧
  decode code p4 = some (.Push .PUSH1, some (⟨1⟩, 1)) ∧
  decode code p6 = some (.Push .PUSH1, some (⟨1⟩, 1)) ∧
  decode code p8 = some (.Push .PUSH1, some (⟨160⟩, 1)) ∧
  decode code p10 = some (.SHL, none) ∧
  decode code p11 = some (.SUB, none) ∧
  decode code p12 = some (.NOT, none) ∧
  decode code p13 = some (.SWAP1, none) ∧
  decode code p14 = some (.DUP2, none) ∧
  decode code p15 = some (.AND, none) ∧
  decode code p16 = some (.SWAP1, none) ∧
  decode code p17 = some (.SWAP2, none) ∧
  decode code p18 = some (.SSTORE, none)

-- LIBRARY CANDIDATE: a packed-address delete stops at SSTORE under STATICCALL.
theorem clearAddressStoreStatic {code : ByteArray} {I : ExecutionEnv} {g : Sat256}
    {s0 : State} {pc slot : UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024) (hperm : I.perm = false)
    (hwf : clearAddressStoreWf code pc slot)
    (rd : RD code I g s0 pc R mem aw rdata σ k C) : RDstatic code g s0 := by
  rcases hwf with
    ⟨hd0, hd2, hd3, hd4, hd6, hd8, hd10, hd11, hd12, hd13, hd14, hd15, hd16, hd17, hd18⟩
  have r1 := rd.push1 slot hd0 (by evm_ov)
  have r2 := r1.dup1 hd2 (by evm_ov)
  obtain ⟨_, _, r3⟩ := RD.sload r2 hd3 (by evm_ov)
  have r4 := r3.push1 ⟨1⟩ hd4 (by evm_ov)
  have r5 := r4.push1 ⟨1⟩ hd6 (by evm_ov)
  have r6 := r5.push1 ⟨160⟩ hd8 (by evm_ov)
  have r7 := r6.shl hd10 (by evm_ov)
  have r8 := r7.sub hd11 (by evm_ov)
  have r9 := r8.not hd12 (by evm_ov)
  have r10 := r9.swap1 hd13 (by evm_ov)
  have r11 := r10.dup2 hd14 (by evm_ov)
  have r12 := r11.and hd15 (by evm_ov)
  have r13 := r12.swap1 hd16 (by evm_ov)
  have r14 := r13.swap2 hd17 (by evm_ov)
  exact r14.sstoreStatic hperm hd18 (by evm_ov)

end Benchmarks.Morpho.MetaMorphoV1_1
