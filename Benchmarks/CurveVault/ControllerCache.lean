import Benchmarks.CurveVault.Storage
import Reasoning.ExternalCall
import Reasoning.SteleArithmetic

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch
namespace Benchmarks.CurveVault

def vaultControllerCacheBody : List Stmt :=
  [.letDecl "controller_word" (some (.elem (.int (.uint ⟨256, by decide⟩)))) (.storage {base := "_controller", steps := []}),
    .letDecl "controller" (some (.elem .address)) (.cast (.var "controller_word") (.elem .address))]

def vaultControllerCacheLocals (locals : Store) (controller : UInt256) : Store :=
  (locals.insert "controller_word" (.int (Int.ofNat controller.toNat))).insert
    "controller" (.address (AccountAddress.ofUInt256 controller))

theorem vaultControllerCache {s0 evm : State} {I : ExecutionEnv} {σ : AccountMap} {locals : Store}
    (hs : SourceState s0 I σ evm) (hb : locals.get? "_controller" = none) :
    ExecBlock fork config {contract := contract, locals := locals} evm vaultControllerCacheBody
      (.ok {contract := contract, locals := vaultControllerCacheLocals locals (codeOwnerStorageWord I σ ⟨3⟩)} evm) := by
  let controller := codeOwnerStorageWord I σ ⟨3⟩
  have hread : evalExpr? config {contract := contract, locals := locals} evm
      (.storage {base := "_controller", steps := []}) = .ok (.int (Int.ofNat controller.toNat)) := by
    simpa only [wordToElem, normalizeInt_uint256_word, hs.storageRead] using
      vaultEvalScalar evm locals "_controller" (.int (.uint ⟨256, by decide⟩)) ⟨3⟩ hb rfl rfl
  apply ExecBlock.consNormal (ExecStmt.letDecl hread)
  refine ExecBlock.consNormal (ExecStmt.letDecl ?_) ExecBlock.nil
  have heval := evalExpr_varUInt256 (cfg := config) (contract := contract) (evm := evm)
    (store_get_self locals "controller_word" (.int (Int.ofNat controller.toNat)))
  rw [evalExpr?]
  simp only [heval, EvalResult.bind, bind, castValue?, EvalResult.ofOption]
  have hn : ¬ Int.ofNat controller.toNat < 0 := Int.not_lt.mpr (Int.natCast_nonneg _)
  rw [if_neg hn]
  rw [accountAddress_ofUInt256_eq_ofNat_toNat]
  rfl

theorem vaultControllerCacheLocals_get (locals : Store) (controller : UInt256) (name : Ident)
    (hword : ("controller_word" == name) = false) (hcontroller : ("controller" == name) = false) :
    (vaultControllerCacheLocals locals controller).get? name = locals.get? name :=
  store_get_ne2 locals _ _ hword hcontroller

end Benchmarks.CurveVault
