import Benchmarks.UniswapV4PoolManager.BlockResultTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

-- LIBRARY CANDIDATE: a function trace rules out normal fallthrough and loop-control results.
theorem execFuncBody_of_trace {cfg : Config} {f : Frame} {evm : State}
    {body : List Stmt} {result : ExecResult} {code : ByteArray} {g : Sat256} {s0 : State}
    {returns : State → Option (List Value) → Prop}
    (hs : ExecBlock cfg f evm body result) (ht : functionResultTrace code g s0 returns result) :
    ExecFuncBody cfg f evm body result := by
  cases result with
  | returned => exact .execBlockRet hs
  | reverted => exact .execBlockRevert hs
  | staticViolation => exact .execBlockStatic hs
  | ok | «break» | «continue» => exact False.elim ht

-- LIBRARY CANDIDATE: append a proved function tail to a block with existential normal continuations.
theorem execBlock_trace_append {cfg : Config} {f : Frame} {evm : State}
    {pre rest : List Stmt} {result : ExecResult} {code : ByteArray} {g : Sat256} {s0 : State}
    {normal : Frame → State → Prop} {returns : State → Option (List Value) → Prop}
    (hs : ExecBlock cfg f evm pre result)
    (ht : blockResultTrace code g s0 normal (fun _ _ => False) result)
    (hn : ∀ ff post, result = .ok ff post → normal ff post →
      X (g.toNat+1) (D_J code 0) s0 = .error .OutOfGass ∨
      ∃ final, ExecBlock cfg ff post rest final ∧ functionResultTrace code g s0 returns final) :
    X (g.toNat+1) (D_J code 0) s0 = .error .OutOfGass ∨
      ∃ final, ExecBlock cfg f evm (pre ++ rest) final ∧ functionResultTrace code g s0 returns final := by
  cases result with
  | ok ff post =>
      rcases hn ff post rfl ht with hog | ⟨final, hfinal, htrace⟩
      · exact .inl hog
      · exact .inr ⟨final, execBlock_append hs hfinal, htrace⟩
  | reverted => exact .inr ⟨.reverted, execBlock_reverted_append hs, ht⟩
  | staticViolation => exact .inr ⟨.staticViolation, execBlock_append_term hs (by intros; intro he; cases he), ht⟩
  | returned | «break» | «continue» => exact False.elim ht

end Benchmarks.UniswapV4PoolManager
