import Benchmarks.Morpho.MetaMorphoV1_1.Arithmetic
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_067

/-! Arithmetic helpers used by the market-balance and share-conversion routines. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode

def zeroFloorSubFunction : FunctionDecl := contract.functions[18]!

def zeroFloorSubFrame (imms : Store) (a b : Nat) : Frame :=
  { contract := contract
    locals := ((∅ : Store).insert "y" (.int (Int.ofNat b))).insert "x" (.int (Int.ofNat a))
    immutables := imms }

theorem zeroFloorSubBody (evm : EVM.State) (imms : Store) (a b : Nat) :
    ExecFuncBody config (zeroFloorSubFrame imms a b) evm zeroFloorSubFunction.body
      (.returned (zeroFloorSubFrame imms a b) evm (some [.int (Int.ofNat (a - b))])) := by
  apply ExecFuncBody.execBlockRet
  apply ABlock.start.returns
  apply evalExpr_zeroFloorSub
  · simp only [evalExpr?, zeroFloorSubFrame, store_get_self, EvalResult.ofOption]
  · simp only [evalExpr?, zeroFloorSubFrame,
      store_get_ne _ _ (show ("x" == "y") = false from by decide),
      store_get_self, EvalResult.ofOption]

theorem zeroFloorSubCall (evm : EVM.State) (locals imms : Store) (a b : Nat)
    (retVar : Ident) (lhs rhs : Expr)
    (ha : evalExpr? config { contract := contract, locals := locals, immutables := imms }
      evm lhs = .ok (.int (Int.ofNat a)))
    (hb : evalExpr? config { contract := contract, locals := locals, immutables := imms }
      evm rhs = .ok (.int (Int.ofNat b))) :
    ExecStmt config { contract := contract, locals := locals, immutables := imms } evm
      (.internalCall "UtilsLib_zeroFloorSub" [lhs, rhs] retVar)
      (.ok
        { contract := contract
          locals := locals.insert retVar (.int (Int.ofNat (a - b)))
          immutables := imms } evm) := by
  exact internalCallFunctionReturn
    (caller := { contract := contract, locals := locals, immutables := imms })
    (callee := zeroFloorSubFunction) (value := some [.int (Int.ofNat (a - b))])
    (argVals := [.int (Int.ofNat a), .int (Int.ofNat b)])
    (by simp [evalExprs?, ha, hb, bind, EvalResult.bind, pure]) rfl rfl
    (zeroFloorSubBody evm imms a b)

set_option maxRecDepth 2000 in
theorem maxDepositZeroFloorSub {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {a b ret : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 5 ≤ 1024)
    (rd : RD (deployedRuntime v) I g s0 ⟨14045⟩ (b :: a :: ret :: R) mem aw rdata σ k C) :
    ∃ k' C', RD (deployedRuntime v) I g s0 ⟨12077⟩
      (ret :: UInt256.ofNat (a.toNat - b.toNat) :: R) mem aw rdata σ k' C' := by
  have hret := metaMorphoV1_1Blocks.metaMorphoV1_1_block_14045
    (immWords := wordsOf (immStore v)) hstack
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  change RD _ _ _ _ _ (ret :: UInt256.mul (UInt256.gt a b) (UInt256.sub a b) :: R)
    _ _ _ _ _ _ at hret
  rw [wordZeroFloorSub] at hret
  exact ⟨_, _, hret⟩

end Benchmarks.Morpho.MetaMorphoV1_1
