import Benchmarks.CurveVault.Limits
import Benchmarks.CurveVault.RuntimeBlocks_029

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch
namespace Benchmarks.CurveVault

abbrev vaultSubOrZeroFunction : FunctionDecl := contract.functions[36]!

theorem vaultSubOrZeroSource {evm : State} {locals : Store} {a b : UInt256}
    (ha : locals.get? "a" = some (.int (Int.ofNat a.toNat)))
    (hb : locals.get? "b" = some (.int (Int.ofNat b.toNat))) :
    ExecFuncBody fork config {contract := contract, locals := locals} evm vaultSubOrZeroFunction.body
      (.returned {contract := contract, locals := locals} evm
        (some [.int (Int.ofNat (UInt256.sub (wordMax a b) b).toNat)])) := by
  have hevalA := evalExpr_varUInt256 (cfg := config) (contract := contract) (evm := evm) ha
  have hevalB := evalExpr_varUInt256 (cfg := config) (contract := contract) (evm := evm) hb
  exact ExecFuncBody.execBlockRet <| ExecBlock.consReturn <| ExecStmt.return <| evalExprs?_singleton
    (evalExpr_castSub256_of_le (evalExpr_max256 hevalA hevalB) hevalB (wordMax_ge_right a b))

theorem vaultSubOrZeroReach {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {a b dest returnPc : UInt256} {R : List UInt256}
    (ha : memLoad (UInt256.ofNat 64) mem = a)
    (hb : memLoad (UInt256.ofNat 96) mem = b)
    (hstack : R.length + 9 ≤ 1024)
    (hvalid : (D_J vaultBytecode 0).contains returnPc = true)
    (h : RD fork vaultBytecode I g s0 (UInt256.ofNat 7791) (dest :: returnPc :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD fork vaultBytecode I g s0 returnPc R
      ((UInt256.sub (wordMax a b) b).toByteArray.write 0 mem dest.toNat 32) aw' rdata σ k' C' := by
  have rd := vaultBlocks.vault_block_7791 hstack hvalid h
  change RD fork vaultBytecode I g s0 returnPc R
    ((UInt256.sub (UInt256.xor (UInt256.mul (UInt256.gt (memLoad (UInt256.ofNat 64) mem)
      (memLoad (UInt256.ofNat 96) mem)) (UInt256.xor (memLoad (UInt256.ofNat 96) mem)
        (memLoad (UInt256.ofNat 64) mem))) (memLoad (UInt256.ofNat 96) mem))
      (memLoad (UInt256.ofNat 96) mem)).toByteArray.write 0 mem dest.toNat 32) _ rdata σ _ _ at rd
  rw [ha, hb, branchlessMax] at rd
  exact ⟨_, _, _, rd⟩
end Benchmarks.CurveVault
