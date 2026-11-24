import Benchmarks.CurveVault.DebitMemory
import Benchmarks.CurveVault.DebitTail
import Benchmarks.CurveVault.ControllerCache
import Benchmarks.CurveVault.SupplyForward

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch
namespace Benchmarks.CurveVault

theorem vaultDebitBurn (isWithdraw : Bool) {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {receiver owner assets shares : UInt256} {R : List UInt256} {locals : Store}
    (hs : SourceState s0 I σ evm) (hsize : 704 ≤ mem.size)
    (hr : locals.get? "_receiver" = some (.address (AccountAddress.ofNat receiver.toNat)))
    (ho : locals.get? "_owner" = some (.address (AccountAddress.ofNat owner.toNat)))
    (hbc : locals.get? "_controller" = none) (hb : locals.get? "_borrowed_token" = none)
    (ha : locals.get? (vaultDebitAssetsName isWithdraw) = some (.int (Int.ofNat assets.toNat)))
    (hv : locals.get? (vaultDebitSharesName isWithdraw) = some (.int (Int.ofNat shares.toNat)))
    (hmr : memLoad (UInt256.ofNat 576) mem = receiver)
    (hmo : memLoad (UInt256.ofNat 608) mem = owner)
    (hmv : memLoad (UInt256.ofNat 672) mem = vaultDebitResult isWithdraw assets shares)
    (hinput : calldataWord I.calldata 4 = vaultDebitInput isWithdraw assets shares)
    (hrcanon : receiver.toNat < EVM.addressModulus) (hocanon : owner.toNat < EVM.addressModulus)
    (hperm : I.perm = true) (hstack : R.length + 9 ≤ 1024)
    (h : RD fork vaultBytecode I g s0 (UInt256.ofNat (if isWithdraw then 4549 else 5453)) R mem aw rdata σ k C) :
    (∃ (evm' : State) (σ' : AccountMap) (locals' : Store),
      ExecBlock fork config {contract := contract, locals := locals} evm ((vaultDebitFunction isWithdraw).body.drop 4)
        (.returned {contract := contract, locals := locals'} evm'
          (some [.int (Int.ofNat (vaultDebitResult isWithdraw assets shares).toNat)])) ∧
      SourceState s0 I σ' evm' ∧
      RDret fork vaultBytecode g s0 (tstoreAccountMap I.codeOwner σ' ⟨0⟩ ⟨0⟩)
        (vaultDebitResult isWithdraw assets shares).toByteArray) ∨
    (ExecBlock fork config {contract := contract, locals := locals} evm ((vaultDebitFunction isWithdraw).body.drop 4)
      .reverted ∧ RDrev fork vaultBytecode g s0) := by
  let beforeBody := if isWithdraw then vaultControllerCacheBody else []
  let afterBody := if isWithdraw then [] else vaultControllerCacheBody
  let locals0 := if isWithdraw then vaultControllerCacheLocals locals (codeOwnerStorageWord I σ ⟨3⟩) else locals
  have hbody : (vaultDebitFunction isWithdraw).body.drop 4 = beforeBody ++
      [.internalCall "_burn" [.var "_owner", .var (vaultDebitSharesName isWithdraw)] "__c3"] ++
      afterBody ++ (vaultDebitFunction isWithdraw).body.drop 7 := by cases isWithdraw <;> rfl
  have hbefore : ExecBlock fork config {contract := contract, locals := locals} evm beforeBody
      (.ok {contract := contract, locals := locals0} evm) := by
    cases isWithdraw
    · exact ExecBlock.nil
    · exact vaultControllerCache hs hbc
  have hget0 (name : Ident) (hw : ("controller_word" == name) = false) (hc : ("controller" == name) = false) :
      locals0.get? name = locals.get? name := by
    cases isWithdraw
    · rfl
    · exact vaultControllerCacheLocals_get _ _ _ hw hc
  obtain ⟨aw0, k0, C0, rdBurn⟩ := vaultDebitBurnSetup isWithdraw hsize hmo hmv hinput (by omega) h
  let mem0 := vaultDebitBurnMemory isWithdraw I σ mem
  obtain ⟨hargsSize, howner, hshares⟩ := vaultSupplyArguments_reads mem0 owner shares
  have hargs : evalExprs? config {contract := contract, locals := locals0} evm
      [.var "_owner", .var (vaultDebitSharesName isWithdraw)] =
      .ok [.address (AccountAddress.ofNat owner.toNat), .int (Int.ofNat shares.toNat)] := by
    have ho0 := (hget0 "_owner" (by decide +kernel) (by decide +kernel)).trans ho
    have hv0 := (hget0 (vaultDebitSharesName isWithdraw) (by cases isWithdraw <;> decide +kernel)
      (by cases isWithdraw <;> decide +kernel)).trans hv
    simp only [evalExprs?, evalExpr?, ho0, hv0, EvalResult.ofOption, EvalResult.bind, bind, pure]
  rcases vaultSupplyForward false (retVar := "__c3") hs hargsSize howner hshares hocanon hargs
    hperm (by omega) (by cases isWithdraw <;> native_decide) rdBurn with
      ⟨evm1, σ1, aw1, k1, C1, hburn, hs1, rdHook⟩ | ⟨hburn, hrev⟩
  swap
  · refine Or.inr ⟨?_, hrev⟩
    rw [hbody, List.append_assoc, List.append_assoc]
    exact execBlock_append hbefore (ExecBlock.consRevert hburn)
  let controller := if isWithdraw then codeOwnerStorageWord I σ ⟨3⟩ else codeOwnerStorageWord I σ1 ⟨3⟩
  let locals1 := locals0.insert "__c3" .unit
  let locals2 := if isWithdraw then locals1 else vaultControllerCacheLocals locals1 controller
  have hafter : ExecBlock fork config {contract := contract, locals := locals1} evm1 afterBody
      (.ok {contract := contract, locals := locals2} evm1) := by
    cases isWithdraw
    · apply vaultControllerCache hs1
      rw [store_get_ne _ _ (by decide +kernel)]
      exact hbc
    · exact ExecBlock.nil
  have hget2 (name : Ident) (hw : ("controller_word" == name) = false)
      (hc : ("controller" == name) = false) (hcall : ("__c3" == name) = false) :
      locals2.get? name = locals.get? name := by
    cases isWithdraw
    · exact (vaultControllerCacheLocals_get _ _ _ hw hc).trans (store_get_ne _ _ hcall)
    · exact (store_get_ne _ _ hcall).trans (vaultControllerCacheLocals_get _ _ _ hw hc)
  have hc : locals2.get? "controller" = some (.address (AccountAddress.ofUInt256 controller)) := by
    cases isWithdraw <;> simp only [locals2, locals1, locals0, controller, vaultControllerCacheLocals,
      Bool.false_eq_true, if_true, if_false, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] <;> rfl
  have hw : locals2.get? "controller_word" = some (.int (Int.ofNat controller.toNat)) := by
    cases isWithdraw <;> simp only [locals2, locals1, locals0, controller, vaultControllerCacheLocals,
      Bool.false_eq_true, if_true, if_false, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] <;> rfl
  let mem1 := vaultSupplyMemory (vaultSupplyArguments mem0 owner shares) owner shares
  have hf0 := vaultDebitBurnMemory_frame isWithdraw I σ mem
  have hf1 : WordMemoryRange mem0 mem1 160 UInt256.size :=
    ((vaultSupplyArguments_frame mem0 owner shares).mono (by omega) (le_refl _)).trans
      (vaultSupplyMemory_frame _ owner shares)
  have hframe : WordMemoryRange mem mem1 160 704 :=
    (hf0.mono (by omega) (le_refl _)).trans (hf1.mono (le_refl _) (by decide +kernel))
  have hcached : memLoad (UInt256.ofNat 704) (vaultHookCachedMemory (vaultDebitFlow isWithdraw) I σ1 mem1) = controller := by
    cases isWithdraw
    · exact memLoad_write_back _ _ 704 (by decide +kernel)
        (lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 704 (by omega)))
    · change memLoad (UInt256.ofNat 704) mem1 = codeOwnerStorageWord I σ ⟨3⟩
      rw [hf1.load 704 (by omega) (by decide +kernel)
        (toByteArray_write_size_ge_off_add32 _ _ 704
          (lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 704 (by omega)))) (by decide +kernel)]
      exact memLoad_write_back _ _ 704 (by decide +kernel)
        (lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 704 (by omega)))
  have hcachedSize : 736 ≤ (vaultHookCachedMemory (vaultDebitFlow isWithdraw) I σ1 mem1).size := by
    cases isWithdraw
    · exact toByteArray_write_size_ge_off_add32 _ _ 704
        (lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 704 (by omega)))
    · exact le_trans (toByteArray_write_size_ge_off_add32 _ _ 704
        (lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 704 (by omega)))) hf1.size
  rcases vaultDebitTail isWithdraw (locals := locals2) hs1 (le_trans hsize hframe.size)
    ((hget2 "_receiver" (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans hr)
    ((hget2 "_owner" (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans ho) hc hw
    ((hget2 "_borrowed_token" (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans hb)
    ((hget2 _ (by cases isWithdraw <;> decide +kernel) (by cases isWithdraw <;> decide +kernel)
      (by cases isWithdraw <;> decide +kernel)).trans ha)
    ((hget2 _ (by cases isWithdraw <;> decide +kernel) (by cases isWithdraw <;> decide +kernel)
      (by cases isWithdraw <;> decide +kernel)).trans hv)
    ((hframe.load 576 (by omega) (by omega) (by omega) (by decide +kernel)).trans hmr)
    hcached hcachedSize ((hframe.load 672 (by omega) (by omega) hsize (by decide +kernel)).trans hmv)
    hinput hrcanon hperm hstack rdHook with
    ⟨evm2, σ2, locals3, htail, hs2, hret⟩ | ⟨htail, hrev⟩
  · refine Or.inl ⟨evm2, σ2, locals3, ?_, hs2, hret⟩
    rw [hbody]
    exact execBlock_append (execBlock_append
      (execBlock_append hbefore (ExecBlock.consNormal hburn ExecBlock.nil)) hafter) htail
  · refine Or.inr ⟨?_, hrev⟩
    rw [hbody]
    exact execBlock_append (execBlock_append
      (execBlock_append hbefore (ExecBlock.consNormal hburn ExecBlock.nil)) hafter) htail

end Benchmarks.CurveVault
