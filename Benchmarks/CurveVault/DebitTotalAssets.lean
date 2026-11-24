import Benchmarks.CurveVault.WithdrawAfterAssets
import Benchmarks.CurveVault.RedeemAfterAssets
import Benchmarks.CurveVault.TotalAssetsInternal

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch
namespace Benchmarks.CurveVault

def vaultDebitLocals (isWithdraw : Bool) (receiver owner : AccountAddress) (input : UInt256) : Store :=
  (((∅ : Store).insert "_owner" (.address owner)).insert "_receiver" (.address receiver)).insert
    (if isWithdraw then "_assets" else "_shares") (.int (Int.ofNat input.toNat))

def vaultDebitBlockOutcome (fork : Ethereum.Fork) (isWithdraw : Bool) (dropN : Nat) (s0 evm : State) (I : ExecutionEnv)
    (g : Sat256) (locals : Store) : Prop :=
  (∃ (evm' : State) (σ' : AccountMap) (locals' : Store) (value : UInt256),
    ExecBlock fork config {contract := contract, locals := locals} evm ((vaultDebitFunction isWithdraw).body.drop dropN)
      (.returned {contract := contract, locals := locals'} evm' (some [.int (Int.ofNat value.toNat)])) ∧
    SourceState s0 I σ' evm' ∧
    RDret fork vaultBytecode g s0 (tstoreAccountMap I.codeOwner σ' ⟨0⟩ ⟨0⟩) value.toByteArray) ∨
  (ExecBlock fork config {contract := contract, locals := locals} evm ((vaultDebitFunction isWithdraw).body.drop dropN)
    .reverted ∧ RDrev fork vaultBytecode g s0)

theorem vaultDebitTotalAssets (isWithdraw : Bool) {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {receiver owner : UInt256} {R : List UInt256} {locals : Store}
    (hs : SourceState s0 I σ evm) (hsize : 640 ≤ mem.size)
    (hr : locals.get? "_receiver" = some (.address (AccountAddress.ofNat receiver.toNat)))
    (ho : locals.get? "_owner" = some (.address (AccountAddress.ofNat owner.toNat)))
    (hbc : locals.get? "_controller" = none) (hb : locals.get? "_borrowed_token" = none)
    (hallow : locals.get? "allowance" = none)
    (hi : locals.get? (if isWithdraw then "_assets" else "_shares") =
      some (.int (Int.ofNat (calldataWord I.calldata 4).toNat)))
    (hmr : memLoad (UInt256.ofNat 576) mem = receiver)
    (hmo : memLoad (UInt256.ofNat 608) mem = owner)
    (hrcanon : receiver.toNat < EVM.addressModulus) (hocanon : owner.toNat < EVM.addressModulus)
    (hperm : I.perm = true) (hstack : R.length + 14 ≤ 1024)
    (h : RD fork vaultBytecode I g s0 (UInt256.ofNat 6772)
      (UInt256.ofNat 672 :: UInt256.ofNat (if isWithdraw then 4202 else 5232) :: R) mem aw rdata σ k C) :
    vaultDebitBlockOutcome fork isWithdraw (if isWithdraw then 0 else 1) s0 evm I g locals := by
  have hbody : (vaultDebitFunction isWithdraw).body.drop (if isWithdraw then 0 else 1) =
      .internalCall "_total_assets" [] "total_assets" ::
        (vaultDebitFunction isWithdraw).body.drop (if isWithdraw then 1 else 2) := by cases isWithdraw <;> rfl
  rcases vaultTotalAssetsRoutine hs (by omega) (by cases isWithdraw <;> native_decide) h with
    ⟨evm1, σ1, calleeLocals, a, b, c, aw1, out, k1, C1, hcallee, hs1, rdNext⟩ | ⟨hcallee, hrev⟩
  swap
  · refine Or.inr ⟨?_, hrev⟩
    rw [hbody]
    exact ExecBlock.consRevert (internalCallFunctionRevert (callee := vaultTotalAssetsFunction)
      (argVals := []) (by simp [evalExprs?, pure]) rfl rfl hcallee)
  let total := UInt256.sub (a + b) c
  let scratch := vaultTotalAssetsScratch mem a b c
  let returned := total.toByteArray.write 0 scratch 672 32
  let locals1 := locals.insert "total_assets" (.int (Int.ofNat total.toNat))
  have hcall := internalCallFunctionReturn (caller := {contract := contract, locals := locals})
    (callee := vaultTotalAssetsFunction) (name := "_total_assets") (args := []) (retVar := "total_assets") (argVals := [])
    (by simp [evalExprs?, pure]) rfl rfl hcallee
  have hf := vaultTotalAssetsScratch_frame mem a b c (by omega)
  have hgap : 672 - scratch.size < USize.size :=
    lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 672 (by omega))
  have hframe : WordMemoryRange mem returned 224 672 :=
    (show WordMemoryRange mem scratch 224 672 from
      ⟨Nat.le_of_eq hf.1.symm, fun off hlo _ hin hoff => hf.2 off hlo hin hoff⟩).trans
      (wordMemoryRange_write scratch total 672 224 672 hgap (Or.inl (by omega)))
  have hsize1 : 704 ≤ returned.size := toByteArray_write_size_ge_off_add32 _ _ 672 hgap
  have hrmem := (hframe.load 576 (by omega) (by omega) (by omega) (by decide +kernel)).trans hmr
  have homem := (hframe.load 608 (by omega) (by omega) hsize (by decide +kernel)).trans hmo
  have htmem : memLoad (UInt256.ofNat 672) returned = total :=
    memLoad_write_back _ _ 672 (by decide +kernel) hgap
  have hr1 : locals1.get? "_receiver" = some (.address (AccountAddress.ofNat receiver.toNat)) := by
    rw [store_get_ne _ _ (by decide +kernel), hr]
  have ho1 : locals1.get? "_owner" = some (.address (AccountAddress.ofNat owner.toNat)) := by
    rw [store_get_ne _ _ (by decide +kernel), ho]
  have hbc1 : locals1.get? "_controller" = none := by rw [store_get_ne _ _ (by decide +kernel), hbc]
  have hb1 : locals1.get? "_borrowed_token" = none := by rw [store_get_ne _ _ (by decide +kernel), hb]
  have hallow1 : locals1.get? "allowance" = none := by rw [store_get_ne _ _ (by decide +kernel), hallow]
  have hi1 : locals1.get? (if isWithdraw then "_assets" else "_shares") =
      some (.int (Int.ofNat (calldataWord I.calldata 4).toNat)) := by
    rw [store_get_ne _ _ (by cases isWithdraw <;> decide +kernel), hi]
  have ht1 : locals1.get? "total_assets" = some (.int (Int.ofNat total.toNat)) := store_get_self _ _ _
  have hrest : vaultDebitBlockOutcome fork isWithdraw (if isWithdraw then 1 else 2) s0 evm1 I g locals1 := by
    cases isWithdraw
    · exact vaultRedeemAfterAssets hs1 hsize1 hr1 ho1 hbc1 hb1 hi1 ht1 hrmem homem htmem
        hrcanon hocanon hperm hstack rdNext
    · exact vaultWithdrawAfterAssets hs1 hsize1 hr1 ho1 hbc1 hb1 hallow1 hi1 ht1 hrmem homem htmem
        hrcanon hocanon hperm hstack rdNext
  rcases hrest with ⟨evm2, σ2, locals2, value, hrest, hs2, hret⟩ | ⟨hrest, hrev⟩
  · refine Or.inl ⟨evm2, σ2, locals2, value, ?_, hs2, hret⟩
    rw [hbody]
    exact ExecBlock.consNormal hcall hrest
  · refine Or.inr ⟨?_, hrev⟩
    rw [hbody]
    exact ExecBlock.consNormal hcall hrest

end Benchmarks.CurveVault
