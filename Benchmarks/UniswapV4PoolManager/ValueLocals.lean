import Benchmarks.UniswapV4PoolManager.WordLocals

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

-- LIBRARY CANDIDATE: arbitrary local values, with projection lemmas that avoid expanding stores.
def valueLocal (f : Frame) (name : Ident) (value : Value) : Frame :=
  {f with locals := f.locals.insert name value}

theorem valueLocal_contract (f : Frame) (name : Ident) (value : Value) :
    (valueLocal f name value).contract = f.contract := rfl

theorem wordLocal_contract (f : Frame) (name : Ident) (word : UInt256) :
    (wordLocal f name word).contract = f.contract := rfl

theorem valueLocal_get (f : Frame) (name key : Ident) (value : Value) :
    (valueLocal f name value).locals.get? key =
      if name == key then some value else f.locals.get? key := by
  simp only [valueLocal, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]

end Benchmarks.UniswapV4PoolManager
