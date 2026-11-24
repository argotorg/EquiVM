import Benchmarks.CurveVault.AllowanceStorage
import Benchmarks.CurveVault.Memory
import Benchmarks.CurveVault.RuntimeBlocks_030
import Reasoning.ExternalCall

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch
namespace Benchmarks.CurveVault

abbrev vaultApproveFunction : FunctionDecl := contract.functions[33]!

def vaultApproveLocals (owner spender : AccountAddress) (value : UInt256) : Store :=
  (((∅ : Store).insert "_value" (.int (Int.ofNat value.toNat))).insert
    "_spender" (.address spender)).insert "_owner" (.address owner)

theorem vaultApproveSource (evm : State) (owner spender : AccountAddress) (value : UInt256)
    (hperm : evm.executionEnv.perm = true) :
    ExecFuncBody fork config {contract := contract, locals := vaultApproveLocals owner spender value}
      evm vaultApproveFunction.body
      (.returned {contract := contract, locals := vaultApproveLocals owner spender value}
        (Stele.EVM.storageStore evm evm.executionEnv.codeOwner (vaultAllowanceSlot owner spender) value) none) := by
  let locals := vaultApproveLocals owner spender value
  have ha (s : State) : evalExpr? config {contract := contract, locals := locals} s (.var "_owner") =
      .ok (.address owner) := by simp [evalExpr?, EvalResult.ofOption, locals, vaultApproveLocals]
  have hb (s : State) : evalExpr? config {contract := contract, locals := locals} s (.var "_spender") =
      .ok (.address spender) := by
    simp only [evalExpr?, locals, vaultApproveLocals, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
    rfl
  have hv (s : State) : evalExpr? config {contract := contract, locals := locals} s (.var "_value") =
      .ok (.int (Int.ofNat value.toNat)) := by
    simp only [evalExpr?, locals, vaultApproveLocals, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
    rfl
  apply ExecFuncBody.execBlockOK
  apply ExecBlock.consNormal (ExecStmt.assign (fork := fork) (hperm := Or.inr hperm) (hv evm)
    (vaultAllowanceAssign evm locals (.var "_owner") (.var "_spender") owner spender value
      (by simp [locals, vaultApproveLocals]) (ha evm) (hb evm)))
  refine ExecBlock.consNormal (ExecStmt.emit (fork := fork) (hperm := by simpa only [storageStore_executionEnv] using hperm) (vals := [.address owner, .address spender, .int (Int.ofNat value.toNat)]) ?_) ExecBlock.nil
  change evalExprs? config {contract := contract, locals := locals} _
    [.var "_owner", .var "_spender", .var "_value"] = _
  simp only [evalExprs?, ha, hb, hv, EvalResult.bind, pure, bind]

def vaultApproveHashMemory (mem : ByteArray) (owner spender : UInt256) : ByteArray :=
  wordAt0Mem (vyperMappingSlot ⟨12⟩ (.address (AccountAddress.ofNat owner.toNat)))
    (wordAt32Mem spender (wordAt0Mem ⟨12⟩ (wordAt32Mem owner mem)))

def vaultApproveMemory (mem : ByteArray) (owner spender value : UInt256) : ByteArray :=
  value.toByteArray.write 0 (vaultApproveHashMemory mem owner spender) 160 32

theorem vaultApproveMemory_frame (mem : ByteArray) (owner spender value : UInt256) :
    WordMemoryRange mem (vaultApproveMemory mem owner spender value) 192 UInt256.size := by
  have hgap (d : Nat) (hd : d < 1024) (m : ByteArray) : d - m.size < USize.size :=
    lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize d (by omega))
  exact (wordMemoryRange_vyperHash mem ⟨12⟩ owner 192 UInt256.size (by omega)).trans
    ((wordMemoryRange_vyperHash _ _ spender 192 UInt256.size (by omega)).trans
      (wordMemoryRange_write _ value 160 192 UInt256.size (hgap _ (by omega) _) (Or.inr (by omega))))

theorem vaultApproveRoutine {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {owner spender value returnPc : UInt256} {R : List UInt256}
    (hs : SourceState s0 I σ evm) (hsize : 160 ≤ mem.size)
    (hmo : memLoad (UInt256.ofNat 64) mem = owner)
    (hms : memLoad (UInt256.ofNat 96) mem = spender)
    (hmv : memLoad (UInt256.ofNat 128) mem = value)
    (hcanon0 : owner.toNat < EVM.addressModulus) (hcanon1 : spender.toNat < EVM.addressModulus)
    (hperm : I.perm = true) (hstack : R.length + 6 ≤ 1024)
    (hvalid : (D_J vaultBytecode 0).contains returnPc = true)
    (h : RD fork vaultBytecode I g s0 (UInt256.ofNat 7939) (returnPc :: R) mem aw rdata σ k C) :
    ∃ (evm' : State) (σ' : AccountMap) (aw' : UInt256) (k' C' : Nat),
      ExecFuncBody fork config {contract := contract, locals := (vaultApproveLocals
        (AccountAddress.ofNat owner.toNat) (AccountAddress.ofNat spender.toNat) value)}
        evm vaultApproveFunction.body
        (.returned {contract := contract, locals := (vaultApproveLocals
          (AccountAddress.ofNat owner.toNat) (AccountAddress.ofNat spender.toNat) value)} evm' none) ∧
      SourceState s0 I σ' evm' ∧
      RD fork vaultBytecode I g s0 returnPc R (vaultApproveMemory mem owner spender value) aw' rdata σ' k' C' := by
  let hashMem0 := wordAt0Mem ⟨12⟩ (wordAt32Mem owner mem)
  have hsize0 : hashMem0.size = mem.size := vyperHashMem_size _ _ _ (by omega)
  have hms0 : memLoad (UInt256.ofNat 96) hashMem0 = spender := by
    rw [memLoad_vyperHashMem _ _ _ _ (by omega) (by omega) (by decide +kernel), hms]
  have hhash0 := vyperHashMem_address ⟨12⟩ owner mem (by omega) hcanon0
  have hhash1 := vyperHashMem_address
    (vyperMappingSlot ⟨12⟩ (.address (AccountAddress.ofNat owner.toNat))) spender hashMem0
    (by rw [hsize0]; omega) hcanon1
  have hmv1 : memLoad (UInt256.ofNat 128) (vaultApproveHashMemory mem owner spender) = value := by
    unfold vaultApproveHashMemory
    rw [memLoad_vyperHashMem _ _ _ _ (by omega) (by rw [hsize0]; omega) (by decide +kernel),
      memLoad_vyperHashMem _ _ _ _ (by omega) (by omega) (by decide +kernel), hmv]
  have hmem : vaultBlocks.vault_block_7939_memory (mem := mem) = vaultApproveMemory mem owner spender value := by
    change (memLoad (UInt256.ofNat 128)
      (wordAt0Mem (keccakWord ⟨0⟩ (UInt256.ofNat 64)
        (wordAt0Mem ⟨12⟩ (wordAt32Mem (memLoad (UInt256.ofNat 64) mem) mem)))
        (wordAt32Mem (memLoad (UInt256.ofNat 96)
          (wordAt0Mem ⟨12⟩ (wordAt32Mem (memLoad (UInt256.ofNat 64) mem) mem)))
          (wordAt0Mem ⟨12⟩ (wordAt32Mem (memLoad (UInt256.ofNat 64) mem) mem))))).toByteArray.write 0 _ 160 32 = _
    rw [hmo, hms0, hhash0]
    change (memLoad (UInt256.ofNat 128) (vaultApproveHashMemory mem owner spender)).toByteArray.write 0 _ 160 32 = _
    rw [hmv1]
    change value.toByteArray.write 0
      (wordAt0Mem (keccakWord ⟨0⟩ (UInt256.ofNat 64) hashMem0)
        (wordAt32Mem (memLoad (UInt256.ofNat 96) hashMem0) hashMem0)) 160 32 = _
    rw [hhash0, hms0]
    rfl
  obtain ⟨aw', k', C', rd⟩ := vaultBlocks.vault_block_7939_packed hstack hperm hvalid h
  change RD fork vaultBytecode I g s0 returnPc R (vaultBlocks.vault_block_7939_memory (mem := mem)) aw' rdata
    (sstoreAccountMap I.codeOwner σ
      (keccakWord ⟨0⟩ (UInt256.ofNat 64)
        (wordAt0Mem (keccakWord ⟨0⟩ (UInt256.ofNat 64)
          (wordAt0Mem ⟨12⟩ (wordAt32Mem (memLoad (UInt256.ofNat 64) mem) mem)))
          (wordAt32Mem (memLoad (UInt256.ofNat 96)
            (wordAt0Mem ⟨12⟩ (wordAt32Mem (memLoad (UInt256.ofNat 64) mem) mem)))
            (wordAt0Mem ⟨12⟩ (wordAt32Mem (memLoad (UInt256.ofNat 64) mem) mem)))))
      (memLoad (UInt256.ofNat 128) mem)) k' C' at rd
  rw [hmem, hmo, hms0, hhash0, hhash1, hmv] at rd
  refine ⟨_, _, aw', k', C', vaultApproveSource (hperm := by simpa only [hs.env] using hperm) evm _ _ value, ?_, rd⟩
  rw [hs.env]
  exact hs.storageWrite _ _

end Benchmarks.CurveVault
