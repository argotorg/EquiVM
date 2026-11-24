import Benchmarks.EAS.EAS.TimeArrayFinish
import Benchmarks.EAS.EAS.OffchainSource

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

theorem offchainArrayArgs_eval {evm : EVM.State} {locals imms : Store}
    {words : List UInt256} {time : UInt256} {heap i : Nat} {word : UInt256}
    (h : TimeArrayInv locals words time heap i) (hi : i < words.length)
    (hw : lookupNth? words i = some word) :
    evalExprs? config {contract := contract, locals := locals, immutables := imms} evm
      [.env .caller, .index (.var "data") (.var "i"), .var "time", .var "$EAS.freeMemory"] =
      .ok [.address evm.executionEnv.source, wordBytes32Value word, .int (Int.ofNat time.toNat), .int (Int.ofNat heap)] := by
  rw [evalExprs?, evalExpr?]
  simp only [envValue, pure, bind, EvalResult.bind, timeArrayArgs_eval h hi hw]

def offchainArrayIteration : Body := [
  .internalCall "_revokeOffchain" [.env .caller, .index (.var "data") (.var "i"), .var "time", .var "$EAS.freeMemory"] "__c1$allocation",
  .letDecl "__c1" none (.tupleGet (.var "__c1$allocation") 0),
  .assign .localVar {base := "$EAS.freeMemory"} (.tupleGet (.var "__c1$allocation") 1),
  .assign .localVar {base := "i"} (.cast (.binary .add (.var "i") (.intLit 1)) (.elem (.int (.uint ⟨256, by decide⟩))))]

theorem offchainArrayIteration_ok {evm : EVM.State} {locals imms : Store}
    {words : List UInt256} {time word : UInt256} {heap i : Nat}
    (h : TimeArrayInv locals words time heap i) (hi : i < words.length)
    (hw : lookupNth? words i = some word) (hlen : words.length < UInt256.size)
    (hz : offchainWord evm evm.executionEnv.source word = ⟨0⟩)
    (hperm : evm.executionEnv.perm = true) :
    ExecBlock fork config {contract := contract, locals := locals, immutables := imms} evm offchainArrayIteration
      (.ok {contract := contract, locals := timeArrayNext locals heap i, immutables := imms} (offchainStore evm evm.executionEnv.source word time)) := by
  exact timeArrayFinish h hi hlen (offchainCall_ok (fork := fork) (hperm := hperm) (offchainArrayArgs_eval h hi hw) hz)

theorem offchainArrayIteration_revert {evm : EVM.State} {locals imms : Store}
    {words : List UInt256} {time word : UInt256} {heap i : Nat}
    (h : TimeArrayInv locals words time heap i) (hi : i < words.length)
    (hw : lookupNth? words i = some word) (hz : offchainWord evm evm.executionEnv.source word ≠ ⟨0⟩) :
    ExecBlock fork config {contract := contract, locals := locals, immutables := imms} evm offchainArrayIteration .reverted :=
  ExecBlock.consRevert (offchainCall_revert (offchainArrayArgs_eval h hi hw) hz)

theorem offchainArrayIteration_static {evm : EVM.State} {locals imms : Store}
    {words : List UInt256} {time word : UInt256} {heap i : Nat}
    (h : TimeArrayInv locals words time heap i) (hi : i < words.length)
    (hw : lookupNth? words i = some word) (hz : offchainWord evm evm.executionEnv.source word = ⟨0⟩) (hp : evm.executionEnv.perm = false) :
    ExecBlock fork config {contract := contract, locals := locals, immutables := imms} evm offchainArrayIteration .staticViolation :=
  ExecBlock.consStatic (offchainCall_static (offchainArrayArgs_eval h hi hw) hz hp)

theorem offchainStore_env (evm : EVM.State) (word time : UInt256) :
    (offchainStore evm evm.executionEnv.source word time).executionEnv = evm.executionEnv := by
  exact storageStore_executionEnv _ _ _ _

end Benchmarks.EAS.EAS
