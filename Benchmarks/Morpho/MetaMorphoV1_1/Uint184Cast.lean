import Benchmarks.Morpho.MetaMorphoV1_1.Uint128Cast
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_065

/-! The checked uint184 conversion shared by both cap-submission branches. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option maxRecDepth 2000

def toUint184Function : FunctionDecl := contract.functions[15]!

def toUint184Frame (imms : Store) (x : UInt256) : Frame :=
  { contract := contract, locals := (∅ : Store).insert "value" (uint256Value x),
    immutables := imms }

theorem toUint184Guard (imms : Store) (x : UInt256) (evm : State) :
    evalExpr? config (toUint184Frame imms x) evm
      (.binary .le (.var "value") (.intLit (2 ^ 184 - 1))) =
      .ok (.bool (decide (x.toNat ≤ 2 ^ 184 - 1))) := by
  apply naturalLeSource
  · simp only [evalExpr?, toUint184Frame, store_get_self, EvalResult.ofOption]
  · simp only [evalExpr?, pure]; rfl

theorem toUint184Body (imms : Store) (x : UInt256) (evm : State)
    (hfit : x.toNat < 2 ^ 184) :
    ExecFuncBody config (toUint184Frame imms x) evm toUint184Function.body
      (.returned (toUint184Frame imms x) evm (some [uint256Value x])) := by
  apply ExecFuncBody.execBlockRet
  apply ABlock.returns (ABlock.requireStep ABlock.start ?_)
  · exact uintCastSource _
      (by simp only [evalExpr?, toUint184Frame, store_get_self, EvalResult.ofOption]) hfit
  · have hle : x.toNat ≤ 2 ^ 184 - 1 := by omega
    simpa only [hle, decide_true] using toUint184Guard imms x evm

theorem toUint184BodyReverts (imms : Store) (x : UInt256) (evm : State)
    (hover : 2 ^ 184 ≤ x.toNat) :
    ExecFuncBody config (toUint184Frame imms x) evm toUint184Function.body .reverted := by
  apply ExecFuncBody.execBlockRevert
  apply ABlock.start.requireRevert
  have hle : ¬ x.toNat ≤ 2 ^ 184 - 1 := by omega
  simpa only [hle, decide_false] using toUint184Guard imms x evm

theorem toUint184Call (evm : State) (locals imms : Store) (x : UInt256)
    (retVar : Ident) (expr : Expr) (hfit : x.toNat < 2 ^ 184)
    (hx : evalExpr? config { contract := contract, locals := locals, immutables := imms }
      evm expr = .ok (uint256Value x)) :
    ExecStmt config { contract := contract, locals := locals, immutables := imms } evm
      (.internalCall "SafeCast_toUint184" [expr] retVar)
      (.ok { contract := contract, locals := locals.insert retVar (uint256Value x),
             immutables := imms } evm) :=
  internalCallFunctionReturn (callee := toUint184Function)
    (caller := { contract := contract, locals := locals, immutables := imms })
    (value := some [uint256Value x]) (argVals := [uint256Value x])
    (evalExprs?_singleton hx) rfl rfl (toUint184Body imms x evm hfit)

theorem toUint184CallReverts (evm : State) (locals imms : Store) (x : UInt256)
    (retVar : Ident) (expr : Expr) (hover : 2 ^ 184 ≤ x.toNat)
    (hx : evalExpr? config { contract := contract, locals := locals, immutables := imms }
      evm expr = .ok (uint256Value x)) :
    ExecStmt config { contract := contract, locals := locals, immutables := imms } evm
      (.internalCall "SafeCast_toUint184" [expr] retVar) .reverted :=
  internalCallFunctionRevert (callee := toUint184Function) (argVals := [uint256Value x])
    (evalExprs?_singleton hx) rfl rfl (toUint184BodyReverts imms x evm hover)

theorem toUint184Runtime {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw x ret : UInt256} {σ : AccountMap} {k C : Nat}
    {R : List UInt256} (v : MetaMorphoV1_1Immutables) (hstack : R.length + 5 ≤ 1024)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD (deployedRuntime v) I g s0 ⟨13399⟩ (x :: ret :: R) mem aw out σ k C) :
    (2 ^ 184 ≤ x.toNat ∧ RDrev (deployedRuntime v) g s0) ∨
    (x.toNat < 2 ^ 184 ∧ ∃ k' C',
      RD (deployedRuntime v) I g s0 ret (x :: R) mem aw out σ k' C') := by
  have hmask : UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 184))
      (UInt256.ofNat 1) = UInt256.ofNat (2 ^ 184 - 1) := by decide +kernel
  have hmax : (UInt256.ofNat (2 ^ 184 - 1)).toNat = 2 ^ 184 - 1 :=
    UInt256.toNat_ofNat_of_lt (by decide)
  by_cases hfit : x.toNat < 2 ^ 184
  · have r1 := metaMorphoV1_1_block_13399_fallthrough (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega)
      (by rw [hmask]; exact ugt_zero (by rw [hmax]; omega)) rd
    have r2 := metaMorphoV1_1_block_13414 (immWords := wordsOf (immStore v)) hstack hret r1
    refine .inr ⟨hfit, k + 10 + 8, C + 35 + 29, ?_⟩
    simpa only [metaMorphoV1_1_block_13414_stack, hmask,
      u256_land_comm, u256LandMaskCleanOfToNat x _ hmax hfit] using r2
  · have r1 := metaMorphoV1_1_block_13399_taken (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega)
      (by rw [hmask, ugt_one (by rw [hmax]; omega)]; decide)
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
    exact .inl ⟨by omega, metaMorphoV1_1_block_13425 (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega) r1⟩

end Benchmarks.Morpho.MetaMorphoV1_1
