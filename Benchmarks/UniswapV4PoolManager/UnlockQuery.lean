import Benchmarks.UniswapV4PoolManager.Spec
open Benchmarks.UniswapV4PoolManager
#eval contract.functions.zipIdx |>.filter (fun p => ["Lock_unlock", "Lock_lock", "NonzeroDeltaCount_read"].contains p.1.name)
#eval unlockTransition
