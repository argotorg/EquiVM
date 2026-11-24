import Benchmarks.CurveVault.DepositAfterAssets
import Benchmarks.CurveVault.MintAfterAssets
import Benchmarks.CurveVault.ControllerCache
import Benchmarks.CurveVault.CreditLocals
import Benchmarks.CurveVault.TotalAssetsInternal

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch
namespace Benchmarks.CurveVault

def vaultCreditBlockOutcome (fork : Ethereum.Fork) (isDeposit : Bool) (dropN : Nat) (s0 evm : State) (I : ExecutionEnv)
    (g : Sat256) (locals : Store) : Prop :=
  (∃ (evm' : State) (σ' : AccountMap) (locals' : Store) (value : UInt256),
    ExecBlock fork config {contract := contract, locals := locals} evm ((vaultCreditFunction isDeposit).body.drop dropN)
      (.returned {contract := contract, locals := locals'} evm' (some [.int (Int.ofNat value.toNat)])) ∧
    SourceState s0 I σ' evm' ∧
    RDret fork vaultBytecode g s0 (tstoreAccountMap I.codeOwner σ' ⟨0⟩ ⟨0⟩) value.toByteArray) ∨
  (ExecBlock fork config {contract := contract, locals := locals} evm ((vaultCreditFunction isDeposit).body.drop dropN)
    .reverted ∧ RDrev fork vaultBytecode g s0)

theorem vaultCreditAfterController (isDeposit : Bool) {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {receiver : UInt256} {R : List UInt256}
    (hs : SourceState s0 I σ evm) (hsize : 640 ≤ mem.size)
    (hmr : memLoad (UInt256.ofNat 576) mem = receiver)
    (hmc : memLoad (UInt256.ofNat 608) mem = codeOwnerStorageWord I σ ⟨3⟩)
    (hcanon : receiver.toNat < EVM.addressModulus) (hperm : I.perm = true)
    (hstack : R.length + 14 ≤ 1024)
    (h : RD fork vaultBytecode I g s0 (UInt256.ofNat 6772)
      (UInt256.ofNat 672 :: UInt256.ofNat (if isDeposit then 2190 else 3320) :: R) mem aw rdata σ k C) :
    vaultCreditBlockOutcome fork isDeposit (if isDeposit then 0 else 1) s0 evm I g
      (vaultCreditLocals isDeposit (AccountAddress.ofNat receiver.toNat) (calldataWord I.calldata 4)) := by
  let controller := codeOwnerStorageWord I σ ⟨3⟩
  let locals := vaultCreditLocals isDeposit (AccountAddress.ofNat receiver.toNat) (calldataWord I.calldata 4)
  let locals0 := vaultControllerCacheLocals locals controller
  have hcache := vaultControllerCache (fork := fork) (locals := locals) hs (by cases isDeposit <;> simp [locals, vaultCreditLocals])
  have hbody : (vaultCreditFunction isDeposit).body.drop (if isDeposit then 0 else 1) = vaultControllerCacheBody ++
      [.internalCall "_total_assets" [] "total_assets"] ++
        (vaultCreditFunction isDeposit).body.drop (if isDeposit then 3 else 4) := by cases isDeposit <;> rfl
  have hgap (m : ByteArray) : 672 - m.size < USize.size :=
    lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 672 (by omega))
  rcases vaultTotalAssetsRoutine hs (by omega) (by cases isDeposit <;> native_decide) h with
    ⟨evm1, σ1, calleeLocals, a, b, c, aw1, out, k1, C1, hcallee, hs1, rdNext⟩ | ⟨hcallee, hrev⟩
  swap
  · refine Or.inr ⟨?_, hrev⟩
    rw [hbody, List.append_assoc]
    exact execBlock_append hcache (ExecBlock.consRevert (internalCallFunctionRevert
      (callee := vaultTotalAssetsFunction) (argVals := []) (by simp [evalExprs?, pure]) rfl rfl hcallee))
  let total := UInt256.sub (a + b) c
  let scratch := vaultTotalAssetsScratch mem a b c
  let returned := total.toByteArray.write 0 scratch 672 32
  let locals1 := locals0.insert "total_assets" (.int (Int.ofNat total.toNat))
  have hcall := internalCallFunctionReturn (caller := {contract := contract, locals := locals0})
    (callee := vaultTotalAssetsFunction) (name := "_total_assets") (args := []) (retVar := "total_assets") (argVals := [])
    (by simp [evalExprs?, pure]) rfl rfl hcallee
  have hf := vaultTotalAssetsScratch_frame mem a b c (by omega)
  have hframe : WordMemoryRange mem returned 224 672 :=
    (show WordMemoryRange mem scratch 224 672 from
      ⟨Nat.le_of_eq hf.1.symm, fun off hlo _ hin hoff => hf.2 off hlo hin hoff⟩).trans
      (wordMemoryRange_write scratch total 672 224 672 (hgap _) (Or.inl (by omega)))
  have hsize1 : 704 ≤ returned.size := toByteArray_write_size_ge_off_add32 _ _ 672 (hgap _)
  have hrmem : memLoad (UInt256.ofNat 576) returned = receiver :=
    (hframe.load 576 (by omega) (by omega) (by omega) (by decide +kernel)).trans hmr
  have hcmem : memLoad (UInt256.ofNat 608) returned = controller :=
    (hframe.load 608 (by omega) (by omega) hsize (by decide +kernel)).trans hmc
  have htmem : memLoad (UInt256.ofNat 672) returned = total :=
    memLoad_write_back _ _ 672 (by decide +kernel) (hgap _)
  have hr : locals1.get? "_receiver" = some (.address (AccountAddress.ofNat receiver.toNat)) := by
    cases isDeposit <;> simp only [locals1, locals0, vaultControllerCacheLocals, locals, vaultCreditLocals,
      Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] <;> rfl
  have hc : locals1.get? "controller" = some (.address (AccountAddress.ofUInt256 controller)) := by
    simp only [locals1, locals0, vaultControllerCacheLocals, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
    rfl
  have hw : locals1.get? "controller_word" = some (.int (Int.ofNat controller.toNat)) := by
    simp only [locals1, locals0, vaultControllerCacheLocals, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
    rfl
  have hb : locals1.get? "_borrowed_token" = none := by
    cases isDeposit <;> simp [locals1, locals0, vaultControllerCacheLocals, locals, vaultCreditLocals]
  have hmax : locals1.get? "maxSupply" = none := by
    cases isDeposit <;> simp [locals1, locals0, vaultControllerCacheLocals, locals, vaultCreditLocals]
  have hv : locals1.get? (if isDeposit then "_assets" else "_shares") =
      some (.int (Int.ofNat (calldataWord I.calldata 4).toNat)) := by
    cases isDeposit <;> simp only [locals1, locals0, vaultControllerCacheLocals, locals, vaultCreditLocals,
      Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] <;> rfl
  have ht : locals1.get? "total_assets" = some (.int (Int.ofNat total.toNat)) := store_get_self _ _ _
  have hcontinuation : vaultCreditBlockOutcome fork isDeposit (if isDeposit then 3 else 4) s0 evm1 I g locals1 := by
    cases isDeposit
    · exact vaultMintAfterAssets hs1 hsize1 hr hc hw hb hmax hv ht hrmem hcmem htmem hcanon hperm hstack rdNext
    · exact vaultDepositAfterAssets hs1 hsize1 hr hc hw hb hmax hv ht hrmem hcmem htmem hcanon hperm hstack rdNext
  rcases hcontinuation with ⟨evm2, σ2, locals2, value, hrest, hs2, hret⟩ | ⟨hrest, hrev⟩
  · refine Or.inl ⟨evm2, σ2, locals2, value, ?_, hs2, hret⟩
    rw [hbody, List.append_assoc]
    exact execBlock_append hcache (ExecBlock.consNormal hcall hrest)
  · refine Or.inr ⟨?_, hrev⟩
    rw [hbody, List.append_assoc]
    exact execBlock_append hcache (ExecBlock.consNormal hcall hrest)

end Benchmarks.CurveVault
