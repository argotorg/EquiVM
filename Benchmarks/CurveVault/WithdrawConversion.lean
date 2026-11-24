import Benchmarks.CurveVault.WithdrawAfterConversion
import Benchmarks.CurveVault.MutationConversion

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch
namespace Benchmarks.CurveVault

theorem vaultWithdrawConversion {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {receiver owner total : UInt256} {R : List UInt256} {locals : Store}
    (hs : SourceState s0 I σ evm) (hsize : 672 ≤ mem.size)
    (hr : locals.get? "_receiver" = some (.address (AccountAddress.ofNat receiver.toNat)))
    (ho : locals.get? "_owner" = some (.address (AccountAddress.ofNat owner.toNat)))
    (hbc : locals.get? "_controller" = none) (hb : locals.get? "_borrowed_token" = none)
    (hallow : locals.get? "allowance" = none)
    (ha : locals.get? "_assets" = some (.int (Int.ofNat (calldataWord I.calldata 4).toNat)))
    (ht : locals.get? "total_assets" = some (.int (Int.ofNat total.toNat)))
    (hmr : memLoad (UInt256.ofNat 576) mem = receiver)
    (hmo : memLoad (UInt256.ofNat 608) mem = owner)
    (hmt : memLoad (UInt256.ofNat 640) mem = total)
    (hrcanon : receiver.toNat < EVM.addressModulus) (hocanon : owner.toNat < EVM.addressModulus)
    (hperm : I.perm = true) (hstack : R.length + 14 ≤ 1024)
    (h : RD fork vaultBytecode I g s0 (UInt256.ofNat 4381) R mem aw rdata σ k C) :
    (∃ (evm' : State) (σ' : AccountMap) (locals' : Store) (shares : UInt256),
      ExecBlock fork config {contract := contract, locals := locals} evm ((vaultDebitFunction true).body.drop 2)
        (.returned {contract := contract, locals := locals'} evm' (some [.int (Int.ofNat shares.toNat)])) ∧
      SourceState s0 I σ' evm' ∧
      RDret fork vaultBytecode g s0 (tstoreAccountMap I.codeOwner σ' ⟨0⟩ ⟨0⟩) shares.toByteArray) ∨
    (ExecBlock fork config {contract := contract, locals := locals} evm ((vaultDebitFunction true).body.drop 2)
      .reverted ∧ RDrev fork vaultBytecode g s0) := by
  have hargs : evalExprs? config {contract := contract, locals := locals} evm
      [.var "_assets", .boolLit false, .var "total_assets"] =
      .ok [.int (Int.ofNat (calldataWord I.calldata 4).toNat), .bool false, .int (Int.ofNat total.toNat)] := by
    simp only [evalExprs?, evalExpr?, ha, ht, EvalResult.ofOption, EvalResult.bind, bind, pure]
  rcases vaultMutationConversion .withdraw (retVar := "shares") hs hsize hmt hargs hstack h with
    ⟨evm1, σ1, mem1, shares, aw1, out, k1, C1, hcall, hs1, hframe, hsize1, hread, rdNext⟩ | ⟨hcall, hrev⟩
  swap
  · exact Or.inr ⟨ExecBlock.consRevert hcall, hrev⟩
  change WordMemoryRange mem mem1 576 672 at hframe
  let locals1 := locals.insert "shares" (.int (Int.ofNat shares.toNat))
  rcases vaultWithdrawAfterConversion (locals := locals1) hs1 hsize1
    (by rw [store_get_ne _ _ (by decide +kernel), hr])
    (by rw [store_get_ne _ _ (by decide +kernel), ho])
    (by rw [store_get_ne _ _ (by decide +kernel), hbc])
    (by rw [store_get_ne _ _ (by decide +kernel), hb])
    (by rw [store_get_ne _ _ (by decide +kernel), hallow])
    (by rw [store_get_ne _ _ (by decide +kernel), ha]) (store_get_self _ _ _)
    ((hframe.load 576 (by omega) (by omega) (by omega) (by decide +kernel)).trans hmr)
    ((hframe.load 608 (by omega) (by omega) (by omega) (by decide +kernel)).trans hmo)
    hread hrcanon hocanon hperm (by omega) rdNext with
    ⟨evm2, σ2, locals2, hrest, hs2, hret⟩ | ⟨hrest, hrev⟩
  · exact Or.inl ⟨evm2, σ2, locals2, shares, ExecBlock.consNormal hcall hrest, hs2, hret⟩
  · exact Or.inr ⟨ExecBlock.consNormal hcall hrest, hrev⟩

end Benchmarks.CurveVault
