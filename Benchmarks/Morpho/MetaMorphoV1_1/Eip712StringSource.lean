import Benchmarks.Morpho.MetaMorphoV1_1.ShortStringSource
import Benchmarks.Morpho.MetaMorphoV1_1.StringStorageSource
import Benchmarks.Morpho.MetaMorphoV1_1.DomainSource

/-! Immutable or storage-backed EIP-712 name and version values. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1

set_option maxRecDepth 2000

def domainStringImmutable (v : MetaMorphoV1_1Immutables) (version : Bool) : UInt256 :=
  if version then v._version else v._name

def domainStringImmutableName (version : Bool) : Ident := if version then "_version" else "_name"

def domainStringFallbackField (version : Bool) : Ident :=
  if version then "_versionFallback" else "_nameFallback"

def domainStringFallbackSlot (version : Bool) : UInt256 := if version then ⟨6⟩ else ⟨5⟩

def domainStringFunction (version : Bool) : FunctionDecl :=
  contract.functions[if version then 40 else 39]!

def domainStringBytes (v : MetaMorphoV1_1Immutables) (version : Bool) (evm : State) : ByteArray :=
  if domainStringImmutable v version = ⟨255⟩ then
    storageStringBytes evm (domainStringFallbackSlot version)
  else shortStringBytes (domainStringImmutable v version)

def domainStringValid (v : MetaMorphoV1_1Immutables) (version : Bool) (evm : State) : Prop :=
  if domainStringImmutable v version = ⟨255⟩ then
    storageStringValid (storageStringHeader evm (domainStringFallbackSlot version))
  else shortStringValid (domainStringImmutable v version)

instance (v : MetaMorphoV1_1Immutables) (version : Bool) (evm : State) :
    Decidable (domainStringValid v version evm) := by
  unfold domainStringValid
  infer_instance

theorem domainStringFunction_body (version : Bool) :
    (domainStringFunction version).body =
      [.ite (.binary .eq (.immutable (domainStringImmutableName version)) (.intLit 255))
        [.return [.storage ⟨domainStringFallbackField version, []⟩]] [],
       .internalCall "ShortStrings_toString"
         [.cast (.immutable (domainStringImmutableName version)) (.elem (.bytes abiBytes32Width))]
         "result",
       .return [.var "result"]] := by
  cases version <;> rfl

theorem domainStringImmutableSource (evm : State) (v : MetaMorphoV1_1Immutables)
    (version : Bool) (locals : Store) :
    evalExpr? config (domainFrame v locals) evm (.immutable (domainStringImmutableName version)) =
      .ok (uint256Value (domainStringImmutable v version)) := by
  cases version
  · exact evalImmutable__name config contract locals evm v
  · exact evalImmutable__version config contract locals evm v

theorem domainStringFallbackSource (evm : State) (v : MetaMorphoV1_1Immutables)
    (version : Bool) :
    evalExpr? config (domainFrame v ∅) evm
      (.storage ⟨domainStringFallbackField version, []⟩) =
      if storageStringValid (storageStringHeader evm (domainStringFallbackSlot version)) then
        .ok (.bytes (storageStringBytes evm (domainStringFallbackSlot version))) else .revert := by
  have hr : resolveStorageRef? config (domainFrame v ∅) evm
      ⟨domainStringFallbackField version, []⟩ =
      .ok (⟨domainStringFallbackField version, []⟩, .string) := by
    apply resolveStorageRef?_ok (by simp [domainFrame])
    · simp [evalStorageRef, evalStorageRefSteps, bind, EvalResult.bind, pure]
    · cases version <;> rfl
  rw [evalExpr?, hr]
  by_cases hvalid : storageStringValid
      (storageStringHeader evm (domainStringFallbackSlot version))
  · rw [if_pos hvalid]
    exact storageStringReadAt _ _ evm (by cases version <;> rfl) hvalid
  · rw [if_neg hvalid]
    exact storageStringReadAtReverts _ _ evm (by cases version <;> rfl) hvalid

theorem domainStringBodyReturns (evm : State) (v : MetaMorphoV1_1Immutables) (version : Bool)
    (hvalid : domainStringValid v version evm) :
    ∃ frame', ExecFuncBody config (domainFrame v ∅) evm (domainStringFunction version).body
      (.returned frame' evm (some [.bytes (domainStringBytes v version evm)])) := by
  have hc := evalExpr_wordEq (domainStringImmutableSource evm v version ∅)
    (show evalExpr? config (domainFrame v ∅) evm (.intLit 255) =
      .ok (uint256Value ⟨255⟩) by simp only [evalExpr?, pure]; rfl)
  rw [domainStringFunction_body]
  by_cases hf : domainStringImmutable v version = ⟨255⟩
  · simp only [domainStringValid, if_pos hf] at hvalid
    refine ⟨domainFrame v ∅, ExecFuncBody.execBlockRet ?_⟩
    apply ExecBlock.consReturn (ExecStmt.iteTrue (by simpa only [hf, decide_true] using hc) ?_)
    apply ExecBlock.consReturn (ExecStmt.return (evalExprs?_singleton ?_))
    simpa only [domainStringBytes, if_pos hf, if_pos hvalid] using
      domainStringFallbackSource evm v version
  · simp only [domainStringValid, if_neg hf] at hvalid
    refine ⟨domainFrame v ((∅ : Store).insert "result"
      (.bytes (shortStringBytes (domainStringImmutable v version)))),
      ExecFuncBody.execBlockRet ?_⟩
    apply ExecBlock.consNormal
      (ExecStmt.iteFalse (by simpa only [hf, decide_false] using hc) ExecBlock.nil)
    apply ExecBlock.consNormal (internalCallFunctionReturn (callee := shortStringFunction)
      (argVals := [wordBytes32Value (domainStringImmutable v version)])
      (value := some [.bytes (shortStringBytes (domainStringImmutable v version))])
      (evalExprs?_singleton (evalExpr_uintToBytes32
        (domainStringImmutableSource evm v version ∅))) rfl rfl
      (shortStringBodyReturns evm (immStore v) _ hvalid))
    apply ExecBlock.consReturn (ExecStmt.return (evalExprs?_singleton ?_))
    simp only [evalExpr?, domainFrame, resumeAfterInternalCall, collapseReturns,
      store_get_self, EvalResult.ofOption, domainStringBytes, if_neg hf]

theorem domainStringBodyReverts (evm : State) (v : MetaMorphoV1_1Immutables) (version : Bool)
    (hbad : ¬ domainStringValid v version evm) :
    ExecFuncBody config (domainFrame v ∅) evm (domainStringFunction version).body .reverted := by
  have hc := evalExpr_wordEq (domainStringImmutableSource evm v version ∅)
    (show evalExpr? config (domainFrame v ∅) evm (.intLit 255) =
      .ok (uint256Value ⟨255⟩) by simp only [evalExpr?, pure]; rfl)
  rw [domainStringFunction_body]
  apply ExecFuncBody.execBlockRevert
  by_cases hf : domainStringImmutable v version = ⟨255⟩
  · simp only [domainStringValid, if_pos hf] at hbad
    apply ExecBlock.consRevert
      (ExecStmt.iteTrue (by simpa only [hf, decide_true] using hc) ?_)
    apply ExecBlock.consRevert (ExecStmt.returnRevert ?_)
    simp only [evalExprs?, domainStringFallbackSource, if_neg hbad, bind, EvalResult.bind]
  · simp only [domainStringValid, if_neg hf] at hbad
    apply ExecBlock.consNormal
      (ExecStmt.iteFalse (by simpa only [hf, decide_false] using hc) ExecBlock.nil)
    exact ExecBlock.consRevert (internalCallFunctionRevert (callee := shortStringFunction)
      (argVals := [wordBytes32Value (domainStringImmutable v version)])
      (evalExprs?_singleton (evalExpr_uintToBytes32
        (domainStringImmutableSource evm v version ∅))) rfl rfl
      (shortStringBodyReverts evm (immStore v) _ hbad))

def domainStringFunctionName (version : Bool) : Ident :=
  if version then "_EIP712Version" else "_EIP712Name"

theorem domainStringCallReturns (evm : State) (v : MetaMorphoV1_1Immutables) (version : Bool)
    (locals : Store) (retVar : Ident) (hvalid : domainStringValid v version evm) :
    ExecStmt config (domainFrame v locals) evm
      (.internalCall (domainStringFunctionName version) [] retVar)
      (.ok (domainFrame v (locals.insert retVar (.bytes (domainStringBytes v version evm))))
        evm) := by
  obtain ⟨frame', hbody⟩ := domainStringBodyReturns evm v version hvalid
  exact internalCallFunctionReturn (callee := domainStringFunction version)
    (argVals := []) (value := some [.bytes (domainStringBytes v version evm)])
    (by simp only [evalExprs?, pure]) (by cases version <;> rfl) (by cases version <;> rfl) hbody

theorem domainStringCallReverts (evm : State) (v : MetaMorphoV1_1Immutables) (version : Bool)
    (locals : Store) (retVar : Ident) (hbad : ¬ domainStringValid v version evm) :
    ExecStmt config (domainFrame v locals) evm
      (.internalCall (domainStringFunctionName version) [] retVar) .reverted := by
  exact internalCallFunctionRevert (callee := domainStringFunction version)
    (argVals := []) (by simp only [evalExprs?, pure])
    (by cases version <;> rfl) (by cases version <;> rfl)
    (domainStringBodyReverts evm v version hbad)

theorem domainStringBytes_bound (evm : State) (v : MetaMorphoV1_1Immutables) (version : Bool) :
    (domainStringBytes v version evm).size < 2 ^ 255 := by
  unfold domainStringBytes
  split
  · rw [storageStringBytes_size]
    exact storageStringLength_lt _
  · rw [shortStringBytes, ByteArray.size_extract, toByteArray_size]
    omega

end Benchmarks.Morpho.MetaMorphoV1_1
