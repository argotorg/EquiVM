import Benchmarks.UniswapV4PoolManager.Values

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

-- LIBRARY CANDIDATE: source locals containing unsigned machine words.
def wordLocal (f : Frame) (name : Ident) (w : UInt256) : Frame :=
  {f with locals := f.locals.insert name (.int (Int.ofNat w.toNat))}

theorem wordLocal_get (f : Frame) (name key : Ident) (w : UInt256) :
    (wordLocal f name w).locals.get? key =
      if name == key then some (.int (Int.ofNat w.toNat)) else f.locals.get? key := by
  simp only [wordLocal, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]

theorem wordLocal_eval {cfg : Config} {f : Frame} {evm : EVM.State} {name : Ident} {w : UInt256} :
    evalExpr? cfg (wordLocal f name w) evm (.var name) = .ok (.int (Int.ofNat w.toNat)) :=
  evalLocalValue (store_get_self _ _ _)

end Benchmarks.UniswapV4PoolManager
