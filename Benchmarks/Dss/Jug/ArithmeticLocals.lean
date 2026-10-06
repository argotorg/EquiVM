import Reasoning.SolmRpow
import Reasoning.SolmArithmetic
import Benchmarks.Dss.Jug.ArithmeticExpr

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

open Reasoning.Theory.RpowB

namespace Benchmarks.Dss.Jug


theorem RpowLoopStore.eval_x {evm : EVM.State} {x n b z half : UInt256} {locals : Store}
    (h : RpowLoopStore x n b z half locals) :
    evalExpr? config { contract := contract, locals := locals } evm (.var "x") =
      .ok (.int (Int.ofNat x.toNat)) :=
  Reasoning.Theory.RpowB.RpowLoopStore.eval_x (cfg := config) (contract := contract) h

theorem RpowLoopStore.eval_n {evm : EVM.State} {x n b z half : UInt256} {locals : Store}
    (h : RpowLoopStore x n b z half locals) :
    evalExpr? config { contract := contract, locals := locals } evm (.var "n") =
      .ok (.int (Int.ofNat n.toNat)) :=
  Reasoning.Theory.RpowB.RpowLoopStore.eval_n (cfg := config) (contract := contract) h

theorem RpowLoopStore.eval_b {evm : EVM.State} {x n b z half : UInt256} {locals : Store}
    (h : RpowLoopStore x n b z half locals) :
    evalExpr? config { contract := contract, locals := locals } evm (.var "b") =
      .ok (.int (Int.ofNat b.toNat)) :=
  Reasoning.Theory.RpowB.RpowLoopStore.eval_b (cfg := config) (contract := contract) h

theorem RpowLoopStore.eval_z {evm : EVM.State} {x n b z half : UInt256} {locals : Store}
    (h : RpowLoopStore x n b z half locals) :
    evalExpr? config { contract := contract, locals := locals } evm (.var "z") =
      .ok (.int (Int.ofNat z.toNat)) :=
  Reasoning.Theory.RpowB.RpowLoopStore.eval_z (cfg := config) (contract := contract) h

theorem RpowLoopStore.eval_half {evm : EVM.State} {x n b z half : UInt256}
    {locals : Store} (h : RpowLoopStore x n b z half locals) :
    evalExpr? config { contract := contract, locals := locals } evm (.var "half") =
      .ok (.int (Int.ofNat half.toNat)) :=
  Reasoning.Theory.RpowB.RpowLoopStore.eval_half (cfg := config) (contract := contract) h

theorem RpowLoopStore.eval_while_false {evm : EVM.State} {x b z half : UInt256}
    {locals : Store} (h : RpowLoopStore x ⟨0⟩ b z half locals) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.binary .ne (.var "n") (.intLit 0)) = .ok (.bool false) :=
  Reasoning.Theory.RpowB.RpowLoopStore.eval_while_false (cfg := config) (contract := contract) h

theorem RpowLoopStore.eval_while_true {evm : EVM.State} {x n b z half : UInt256}
    {locals : Store} (h : RpowLoopStore x n b z half locals) (hnz : n ≠ ⟨0⟩) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.binary .ne (.var "n") (.intLit 0)) = .ok (.bool true) :=
  Reasoning.Theory.RpowB.RpowLoopStore.eval_while_true (cfg := config) (contract := contract) h hnz

end Benchmarks.Dss.Jug
