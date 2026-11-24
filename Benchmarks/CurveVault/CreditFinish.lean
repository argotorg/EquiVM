import Benchmarks.CurveVault.CreditSource
import Benchmarks.CurveVault.SupplyForward
import Benchmarks.CurveVault.SaveRateCalls
import Benchmarks.CurveVault.MutationReturn

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch
namespace Benchmarks.CurveVault

theorem vaultCreditFinish (isDeposit : Bool) {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {receiver controller assets shares : UInt256} {R : List UInt256} {locals : Store}
    (hs : SourceState s0 I σ evm) (hsize : 704 ≤ mem.size)
    (hr : locals.get? "_receiver" = some (.address (AccountAddress.ofNat receiver.toNat)))
    (hc : locals.get? "controller" = some (.address (AccountAddress.ofUInt256 controller)))
    (ha : locals.get? (vaultCreditAssetsName isDeposit) = some (.int (Int.ofNat assets.toNat)))
    (hv : locals.get? (vaultCreditSharesName isDeposit) = some (.int (Int.ofNat shares.toNat)))
    (hmr : memLoad (UInt256.ofNat 576) mem = receiver)
    (hmc : memLoad (UInt256.ofNat 608) mem = controller)
    (hmv : memLoad (UInt256.ofNat 672) mem = vaultCreditResult isDeposit assets shares)
    (hinput : calldataWord I.calldata 4 = vaultCreditInput isDeposit assets shares)
    (hcanon : receiver.toNat < EVM.addressModulus) (hperm : I.perm = true)
    (hstack : R.length + 8 ≤ 1024)
    (h : RD fork vaultBytecode I g s0 (UInt256.ofNat (vaultCreditFlow isDeposit).tokenNext) R mem aw rdata σ k C) :
    (∃ (evm' : State) (σ' : AccountMap) (locals' : Store),
      ExecBlock fork config {contract := contract, locals := locals} evm (vaultCreditFinishBody isDeposit)
        (.returned {contract := contract, locals := locals'} evm'
          (some [.int (Int.ofNat (vaultCreditResult isDeposit assets shares).toNat)])) ∧
      SourceState s0 I σ' evm' ∧
      RDret fork vaultBytecode g s0 (tstoreAccountMap I.codeOwner σ' ⟨0⟩ ⟨0⟩)
        (vaultCreditResult isDeposit assets shares).toByteArray) ∨
    (ExecBlock fork config {contract := contract, locals := locals} evm (vaultCreditFinishBody isDeposit)
      .reverted ∧ RDrev fork vaultBytecode g s0) := by
  obtain ⟨aw0, k0, C0, rdMint⟩ := vaultCreditMintSetup isDeposit hsize hmr hmv hinput (by omega) h
  obtain ⟨hargsSize, howner, hshares⟩ := vaultSupplyArguments_reads mem receiver shares
  have hargs : evalExprs? config {contract := contract, locals := locals} evm
      [.var "_receiver", .var (vaultCreditSharesName isDeposit)] =
      .ok [.address (AccountAddress.ofNat receiver.toNat), .int (Int.ofNat shares.toNat)] := by
    simp only [evalExprs?, evalExpr?, hr, hv, EvalResult.ofOption, EvalResult.bind, bind, pure]
  rcases vaultSupplyForward true (retVar := "__c2") hs hargsSize howner hshares hcanon hargs
    hperm (by omega) (by cases isDeposit <;> native_decide) rdMint with
      ⟨evm1, σ1, aw1, k1, C1, hmint, hs1, rdSave⟩ | ⟨hmint, hrev⟩
  swap
  · exact Or.inr ⟨ExecBlock.consRevert hmint, hrev⟩
  let mem1 := vaultSupplyMemory (vaultSupplyArguments mem receiver shares) receiver shares
  have hframe : WordMemoryRange mem mem1 160 UInt256.size :=
    ((vaultSupplyArguments_frame mem receiver shares).mono (by omega) (le_refl _)).trans
      (vaultSupplyMemory_frame _ receiver shares)
  have hsize1 : 704 ≤ mem1.size := le_trans hsize hframe.size
  have hc1 : (locals.insert "__c2" .unit).get? "controller" =
      some (.address (AccountAddress.ofUInt256 controller)) := by
    rw [store_get_ne _ _ (by decide +kernel), hc]
  have hmc1 : memLoad (UInt256.ofNat (vaultCreditFlow isDeposit).controllerOffset) mem1 = controller := by
    have hoff : (vaultCreditFlow isDeposit).controllerOffset = 608 := by cases isDeposit <;> rfl
    rw [hoff, hframe.load 608 (by omega) (by decide +kernel) (by omega) (by decide +kernel), hmc]
  rcases vaultSaveRateCall (vaultCreditFlow isDeposit) (retVar := "__c3") hs1 hc1 hmc1 hstack rdSave with
    ⟨evm2, σ2, out, aw2, k2, C2, hsave, hs2, rdReturn⟩ | ⟨hsave, hrev⟩
  swap
  · exact Or.inr ⟨ExecBlock.consNormal hmint (execBlock_reverted_append hsave), hrev⟩
  let mem2 := vaultSaveRateMemory (vaultCreditFlow isDeposit) mem1
  have hsaveFrame : WordMemoryRange mem1 mem2 0 704 := by
    have hoff : (vaultCreditFlow isDeposit).callOffset = 704 := by cases isDeposit <;> rfl
    dsimp only [mem2, vaultSaveRateMemory]
    rw [hoff]
    exact wordMemoryRange_write _ _ 704 0 704
      (lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 704 (by omega))) (Or.inl (by omega))
  have hvalue : memLoad (UInt256.ofNat 672) mem2 = vaultCreditResult isDeposit assets shares := by
    rw [hsaveFrame.load 672 (by omega) (by omega) hsize1 (by decide +kernel),
      hframe.load 672 (by omega) (by decide +kernel) hsize (by decide +kernel), hmv]
  have hret := vaultMutationReturn (vaultCreditFlow isDeposit) (le_trans hsize1 hsaveFrame.size)
    hvalue hperm (by omega) rdReturn
  refine Or.inl ⟨evm2, σ2, (locals.insert "__c2" .unit).insert "__c3" .unit, ?_, hs2, hret⟩
  apply ExecBlock.consNormal hmint
  apply execBlock_append hsave
  apply vaultCreditReturnSource (hperm := by assumption) isDeposit hs2
  · rw [store_get_ne2 _ _ _ (by decide +kernel) (by decide +kernel), hr]
  · rw [store_get_ne2 _ _ _ (by cases isDeposit <;> decide +kernel)
      (by cases isDeposit <;> decide +kernel), ha]
  · rw [store_get_ne2 _ _ _ (by cases isDeposit <;> decide +kernel)
      (by cases isDeposit <;> decide +kernel), hv]

end Benchmarks.CurveVault
