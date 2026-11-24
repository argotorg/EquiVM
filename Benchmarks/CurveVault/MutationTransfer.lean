import Benchmarks.CurveVault.HookCalls
import Benchmarks.CurveVault.TokenCallSource
import Benchmarks.CurveVault.TokenForward

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch
namespace Benchmarks.CurveVault

def vaultMutationTransferBody (flow : VaultFlow) (argName : Ident) : List Stmt :=
  [.require (.binary .gt (.extCodeSize (.var "controller")) (.intLit 0)),
    .externalCall (.var "controller") flow.hookName (.intLit 0) [.var argName] "__ignored_transfer",
    .internalCall "tkn_transfer_from" (vaultTokenCallArgs flow (.var argName)) "__ignored_transfer"]

def vaultMutationCallLocals (locals : Store) : Store :=
  (locals.insert "__ignored_transfer" .unit).insert "__ignored_transfer" .unit

theorem vaultMutationCallLocals_get (locals : Store) (name : Ident)
    (hname : ("__ignored_transfer" == name) = false) :
    (vaultMutationCallLocals locals).get? name = locals.get? name :=
  store_get_ne2 locals _ _ hname hname

theorem vaultMutationTransfer (flow : VaultFlow) {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {receiver controller amount : UInt256} {R : List UInt256} {locals : Store} {argName : Ident}
    (hs : SourceState s0 I σ evm) (hsize : 704 ≤ mem.size)
    (hr : locals.get? "_receiver" = some (.address (AccountAddress.ofNat receiver.toNat)))
    (hc : locals.get? "controller" = some (.address (AccountAddress.ofUInt256 controller)))
    (hw : locals.get? "controller_word" = some (.int (Int.ofNat controller.toNat)))
    (hb : locals.get? "_borrowed_token" = none)
    (ha : locals.get? argName = some (.int (Int.ofNat amount.toNat)))
    (hname : ("__ignored_transfer" == argName) = false)
    (hmr : memLoad (UInt256.ofNat 576) mem = receiver)
    (hmc : memLoad (UInt256.ofNat flow.controllerOffset) (vaultHookCachedMemory flow I σ mem) = controller)
    (hcachedSize : flow.controllerOffset + 32 ≤ (vaultHookCachedMemory flow I σ mem).size)
    (hma : vaultHookAmount flow I mem = amount)
    (hcanon : receiver.toNat < EVM.addressModulus) (hperm : I.perm = true)
    (hstack : R.length + 9 ≤ 1024)
    (h : RD fork vaultBytecode I g s0 (UInt256.ofNat flow.hookEntry) R mem aw rdata σ k C) :
    (∃ (evm' : State) (σ' : AccountMap) (mem' out : ByteArray) (aw' : UInt256) (k' C' : Nat),
      ExecBlock fork config {contract := contract, locals := locals} evm (vaultMutationTransferBody flow argName)
        (.ok {contract := contract, locals := vaultMutationCallLocals locals} evm') ∧
      SourceState s0 I σ' evm' ∧ 736 ≤ mem'.size ∧
      WordMemoryRange (vaultHookCachedMemory flow I σ mem) mem' 352 flow.callOffset ∧
      RD fork vaultBytecode I g s0 (UInt256.ofNat flow.tokenNext) R mem' aw' out σ' k' C') ∨
    (ExecBlock fork config {contract := contract, locals := locals} evm (vaultMutationTransferBody flow argName)
      .reverted ∧ RDrev fork vaultBytecode g s0) := by
  have heval := evalExpr_varUInt256 (cfg := config) (contract := contract) (evm := evm) ha
  rcases vaultHookCall flow (retVar := "__ignored_transfer") hs hsize hc heval hmc hma (by omega) h with
    ⟨evm1, σ1, out1, aw1, k1, C1, hhook, hs1, rdSetup⟩ | ⟨hhook, hrev⟩
  swap
  · exact Or.inr ⟨execBlock_reverted_append hhook, hrev⟩
  let mem1 := vaultHookCallMemory flow I σ mem amount
  have hframe0 := vaultHookCallMemory_frame flow I σ mem amount
  have hframe1 := vaultHookCallMemory_cachedFrame flow I σ mem amount
  have hsize1 : 736 ≤ mem1.size := by
    have hs1 := toByteArray_write_size_ge_off_add32 amount
      (flow.hookSelector.toByteArray.write 0 (vaultHookCachedMemory flow I σ mem) flow.callOffset 32)
      (flow.callOffset + 32)
      (lt_of_le_of_lt (Nat.sub_le _ _) (by cases flow <;> exact lt_usize _ (by decide +kernel)))
    have hoff : 704 ≤ flow.callOffset := by cases flow <;> decide +kernel
    change flow.callOffset + 32 + 32 ≤ mem1.size at hs1
    omega
  have hc1 : memLoad (UInt256.ofNat flow.controllerOffset) mem1 = controller :=
    (hframe1.load _ (by cases flow <;> decide +kernel) (by cases flow <;> decide +kernel)
      hcachedSize (by cases flow <;> decide +kernel)).trans hmc
  have hr1 : memLoad (UInt256.ofNat 576) mem1 = receiver :=
    (hframe0.load 576 (by omega) (by omega) (by omega) (by decide +kernel)).trans hmr
  have ha1 : vaultHookAmount flow I mem1 = amount := by
    cases flow with
    | deposit | withdraw => exact hma
    | mint | redeem =>
      exact (hframe0.load 672 (by omega) (by omega) hsize (by decide +kernel)).trans hma
  obtain ⟨aw2, k2, C2, rdToken⟩ := vaultTokenSetup flow hsize1 hc1 hr1 ha1 (by omega) rdSetup
  have hargs := vaultTokenCallArgs_eval flow hs1 (locals.insert "__ignored_transfer" .unit)
    controller receiver amount (.var argName)
    (by rw [store_get_ne _ _ (by decide +kernel), hb])
    (by rw [store_get_ne _ _ (by decide +kernel), hw])
    (by rw [store_get_ne _ _ (by decide +kernel), hr]) hcanon
    (evalExpr_varUInt256 (by rw [store_get_ne _ _ hname, ha]))
  obtain ⟨hargsSize, htoken, hsender, hrecipient, hamount⟩ := vaultTokenArguments_reads mem1
    (codeOwnerStorageWord I σ1 ⟨0⟩) (vaultTokenFlowSender flow I controller)
    (vaultTokenFlowRecipient flow controller receiver) amount
  rcases vaultTokenForward (retVar := "__ignored_transfer") hs1 hargsSize htoken hsender hrecipient hamount
    hargs hperm hstack (by cases flow <;> native_decide) rdToken with
    ⟨evm2, σ2, mem2, out2, aw3, k3, C3, htokenCall, hs2, htokenFrame, rdNext⟩ | ⟨htokenCall, hrev⟩
  swap
  · exact Or.inr ⟨execBlock_append hhook (ExecBlock.consRevert htokenCall), hrev⟩
  have hargsFrame := vaultTokenArguments_frame mem1 (codeOwnerStorageWord I σ1 ⟨0⟩)
    (vaultTokenFlowSender flow I controller) (vaultTokenFlowRecipient flow controller receiver) amount
  refine Or.inl ⟨evm2, σ2, mem2, out2, aw3, k3, C3,
    execBlock_append hhook (ExecBlock.consNormal htokenCall ExecBlock.nil), hs2,
    le_trans hsize1 (le_trans hargsFrame.size htokenFrame.size), ?_, rdNext⟩
  exact ((hframe1.mono (by omega) (le_refl _)).trans
    (hargsFrame.mono (by omega) (by cases flow <;> decide +kernel))).trans
    (htokenFrame.mono (le_refl _) (by cases flow <;> decide +kernel))

end Benchmarks.CurveVault
