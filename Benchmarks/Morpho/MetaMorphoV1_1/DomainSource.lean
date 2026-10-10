import Benchmarks.Morpho.MetaMorphoV1_1.DomainHashSource
import Benchmarks.Morpho.MetaMorphoV1_1.AccessControl
import Benchmarks.Morpho.MetaMorphoV1_1.AllocationSource

/-! Cached and rebuilt domain separators in the source semantics. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1

set_option maxRecDepth 2000

def domainCacheValid (v : MetaMorphoV1_1Immutables) (I : ExecutionEnv) : Prop :=
  I.codeOwner = v._cachedThis ∧ UInt256.ofNat Ethereum.chainId = v._cachedChainId

instance (v : MetaMorphoV1_1Immutables) (I : ExecutionEnv) : Decidable (domainCacheValid v I) :=
  inferInstanceAs (Decidable (_ ∧ _))

def domainSeparatorWord (v : MetaMorphoV1_1Immutables) (I : ExecutionEnv) : UInt256 :=
  if domainCacheValid v I then v._cachedDomainSeparator else domainHash v I

def domainSeparatorFunction : FunctionDecl := contract.functions[38]!

def domainCacheExpr : Expr :=
  .binary .and (.binary .eq (.env .this) (.immutable "_cachedThis"))
    (.binary .eq (.env .chainid) (.immutable "_cachedChainId"))

-- GENERALIZES evalExpr_eq_int_true/false to arbitrary frames and word-valued operands.
theorem evalExpr_wordEq {cfg : Config} {frame : Frame} {evm : State}
    {lhs rhs : Expr} {a b : UInt256}
    (ha : evalExpr? cfg frame evm lhs = .ok (uint256Value a))
    (hb : evalExpr? cfg frame evm rhs = .ok (uint256Value b)) :
    evalExpr? cfg frame evm (.binary .eq lhs rhs) = .ok (.bool (decide (a = b))) := by
  rw [evalExpr_binary_nonshort (by decide) (by decide)]
  simp only [ha, hb, uint256Value, bind, EvalResult.bind, evalBinaryOp_eq_int_ok]
  have he : a.toNat = b.toNat ↔ a = b := by
    constructor
    · exact u256_inj
    · intro h; rw [h]
  simp [BEq.beq, he]

theorem domainCacheSource (evm : State) (v : MetaMorphoV1_1Immutables) (locals : Store) :
    evalExpr? config (domainFrame v locals) evm domainCacheExpr =
      .ok (.bool (decide (domainCacheValid v evm.executionEnv))) := by
  have hself : evalExpr? config (domainFrame v locals) evm (.env .this) =
      .ok (.address evm.executionEnv.codeOwner) := by simp only [evalExpr?]; rfl
  have hthis := evalExpr_addressEq hself (evalImmutable__cachedThis config contract locals evm v)
  have hchain : evalExpr? config (domainFrame v locals) evm (.env .chainid) =
      .ok (uint256Value (UInt256.ofNat Ethereum.chainId)) := by simp only [evalExpr?]; rfl
  have hsame := evalExpr_wordEq hchain (evalImmutable__cachedChainId config contract locals evm v)
  simpa [domainCacheExpr, domainCacheValid] using SourceMemory.boolAndSource hthis hsame

theorem domainSeparatorBody (evm : State) (v : MetaMorphoV1_1Immutables) :
    ∃ frame', ExecFuncBody config (domainFrame v ∅) evm domainSeparatorFunction.body
      (.returned frame' evm (some [wordBytes32Value (domainSeparatorWord v evm.executionEnv)])) :=
    by
  have hc := domainCacheSource evm v ∅
  by_cases hvalid : domainCacheValid v evm.executionEnv
  · simp only [domainSeparatorWord, if_pos hvalid]
    simp only [hvalid, decide_true] at hc
    refine ⟨domainFrame v ∅, ExecFuncBody.execBlockRet ?_⟩
    apply ExecBlock.consReturn (ExecStmt.iteTrue hc ?_)
    apply ExecBlock.consReturn (ExecStmt.return (evalExprs?_singleton ?_))
    exact evalExpr_uintToBytes32 (evalImmutable__cachedDomainSeparator config contract ∅ evm v)
  · simp only [hvalid, decide_false] at hc
    refine ⟨domainFrame v ((∅ : Store).insert "__c0" (wordBytes32Value
      (domainHash v evm.executionEnv))), ExecFuncBody.execBlockRet ?_⟩
    apply ExecBlock.consReturn (ExecStmt.iteFalse hc ?_)
    apply ExecBlock.consNormal (buildDomainCall evm v ∅ "__c0")
    apply ExecBlock.consReturn (ExecStmt.return (evalExprs?_singleton ?_))
    simp only [evalExpr?, domainFrame, store_get_self, EvalResult.ofOption,
      domainSeparatorWord, if_neg hvalid]

theorem domainSeparatorCall (evm : State) (v : MetaMorphoV1_1Immutables) (locals : Store)
    (retVar : Ident) :
    ExecStmt config (domainFrame v locals) evm (.internalCall "_domainSeparatorV4" [] retVar)
      (.ok (domainFrame v (locals.insert retVar
        (wordBytes32Value (domainSeparatorWord v evm.executionEnv)))) evm) := by
  obtain ⟨frame', hbody⟩ := domainSeparatorBody evm v
  exact internalCallFunctionReturn (callee := domainSeparatorFunction)
    (argVals := []) (value := some [wordBytes32Value (domainSeparatorWord v evm.executionEnv)])
    (by simp only [evalExprs?, pure]) rfl rfl hbody

theorem domainSeparatorViewBody (evm : State) (v : MetaMorphoV1_1Immutables)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < 2 ^ 255 + 4) :
    ExecTransitionBody config contract evm ∅ dOMAIN_SEPARATORTransition.body
      (.returned (domainFrame v
        (((∅ : Store).insert "__calldata" (.bytes evm.executionEnv.calldata)).insert
          "__c0" (wordBytes32Value (domainSeparatorWord v evm.executionEnv))))
        evm (some [wordBytes32Value (domainSeparatorWord v evm.executionEnv)])) (immStore v) := by
  apply ExecFuncBody.execBlockRet
  apply (nonpayableCalldataPrefix "__calldata" (2 ^ 255 + 4) hwv hhi).run
  apply ExecBlock.consNormal (domainSeparatorCall evm v _ "__c0")
  apply ExecBlock.consReturn (ExecStmt.return (evalExprs?_singleton ?_))
  simp only [evalExpr?, domainFrame, store_get_self, EvalResult.ofOption]

end Benchmarks.Morpho.MetaMorphoV1_1
