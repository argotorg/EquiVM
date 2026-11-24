import Benchmarks.EAS.EAS.TimeArrayFinish
import Benchmarks.EAS.EAS.TimestampSource

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

def timestampArrayIteration : Body := [
  .internalCall "_timestamp" [.index (.var "data") (.var "i"), .var "time", .var "$EAS.freeMemory"] "__c1$allocation",
  .letDecl "__c1" none (.tupleGet (.var "__c1$allocation") 0),
  .assign .localVar {base := "$EAS.freeMemory"} (.tupleGet (.var "__c1$allocation") 1),
  .assign .localVar {base := "i"} (.cast (.binary .add (.var "i") (.intLit 1)) (.elem (.int (.uint ⟨256, by decide⟩))))]

theorem timestampArrayIteration_ok {evm : EVM.State} {locals imms : Store}
    {words : List UInt256} {time word : UInt256} {heap i : Nat}
    (h : TimeArrayInv locals words time heap i) (hi : i < words.length)
    (hw : lookupNth? words i = some word) (hlen : words.length < UInt256.size)
    (hz : timestampWord evm word = ⟨0⟩)
    (hperm : evm.executionEnv.perm = true) :
    ExecBlock fork config {contract := contract, locals := locals, immutables := imms} evm timestampArrayIteration
      (.ok {contract := contract, locals := timeArrayNext locals heap i, immutables := imms} (timestampStore evm word time)) := by
  exact timeArrayFinish h hi hlen (timestampCall_ok (fork := fork) (hperm := hperm) (timeArrayArgs_eval h hi hw) hz)

theorem timestampArrayIteration_revert {evm : EVM.State} {locals imms : Store}
    {words : List UInt256} {time word : UInt256} {heap i : Nat}
    (h : TimeArrayInv locals words time heap i) (hi : i < words.length)
    (hw : lookupNth? words i = some word) (hz : timestampWord evm word ≠ ⟨0⟩) :
    ExecBlock fork config {contract := contract, locals := locals, immutables := imms} evm timestampArrayIteration .reverted :=
  ExecBlock.consRevert (timestampCall_revert (timeArrayArgs_eval h hi hw) hz)

theorem timestampArrayIteration_static {evm : EVM.State} {locals imms : Store}
    {words : List UInt256} {time word : UInt256} {heap i : Nat}
    (h : TimeArrayInv locals words time heap i) (hi : i < words.length)
    (hw : lookupNth? words i = some word) (hz : timestampWord evm word = ⟨0⟩) (hp : evm.executionEnv.perm = false) :
    ExecBlock fork config {contract := contract, locals := locals, immutables := imms} evm timestampArrayIteration .staticViolation :=
  ExecBlock.consStatic (timestampCall_static (timeArrayArgs_eval h hi hw) hz hp)

theorem timestampStore_env (evm : EVM.State) (word time : UInt256) :
    (timestampStore evm word time).executionEnv = evm.executionEnv := by
  exact storageStore_executionEnv _ _ _ _

end Benchmarks.EAS.EAS
