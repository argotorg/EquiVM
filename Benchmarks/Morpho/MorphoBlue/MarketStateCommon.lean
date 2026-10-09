import Benchmarks.Morpho.MorphoBlue.Storage
import Benchmarks.Morpho.MorphoBlue.ReturnCommon

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

def marketReturnEntries (σ : AccountMap) (I : ExecutionEnv) (id : UInt256) :
    List (ElemType × Value × UInt256) :=
  [0, 1, 2, 3, 4, 5].map fun i =>
    let w := marketFieldWord σ I id i
    (.int (.uint ⟨128, by decide⟩), .int (Int.ofNat w.toNat), w)

def marketStateWords (σ : AccountMap) (I : ExecutionEnv) (id : UInt256) : List UInt256 :=
  (marketReturnEntries σ I id).map (fun e ↦ e.2.2)

def marketStateValue (σ : AccountMap) (I : ExecutionEnv) (id : UInt256) : Value :=
  .tuple ((marketReturnEntries σ I id).map (fun e ↦ e.2.1))

def marketStateExpr (key : Expr) : Expr := .tupleLit
  (([0, 1, 2, 3, 4, 5] : List (Fin 6)).map fun i =>
    .storage ⟨"market", [.mindex key, .field (marketFieldName i)]⟩)

theorem evalMarketState (evm : EVM.State) (locals imms : Store) (key : Expr) (id : UInt256)
    (hbase : locals.get? "market" = none)
    (hkey : evalExpr? config { contract := contract, locals := locals, immutables := imms }
      evm key = .ok (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE id))) :
    evalExpr? config { contract := contract, locals := locals, immutables := imms }
      evm (marketStateExpr key) = .ok (marketStateValue evm.accountMap evm.executionEnv id) := by
  have he (i : Fin 6) := evalMorphoMarketField evm locals imms key id i hbase hkey
  simp only [marketStateExpr, List.map_cons, List.map_nil, evalExpr?, evalExprList?, he,
    marketStateValue, marketReturnEntries, pure, bind, EvalResult.bind]
  rfl

theorem encodeMarketState (σ : AccountMap) (I : ExecutionEnv) (id : UInt256) :
    encodeABIValue? Syntax.marketABI (marketStateValue σ I id) =
      some (returnWordBytes (marketStateWords σ I id)).toList := by
  have henc : ∀ e ∈ marketReturnEntries σ I id,
      encodeABIValue? (.elem e.1) e.2.1 = some (EVM.Word.toBytesBE e.2.2) := by
    intro e he
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp he
    exact encodeABIValue_uint _ _ (halfWord_bound _ _)
  exact elementaryWordsTupleEncoding (marketReturnEntries σ I id) henc

end Benchmarks.Morpho.MorphoBlue
