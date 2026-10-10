import Benchmarks.UniswapV3.Pool.SourceFrame

open Solm
namespace Benchmarks.UniswapV3.Pool

-- LIBRARY CANDIDATE: internal-call results leave other caller bindings untouched.
theorem resumeAfterInternalCall_get (frame : Frame) (retVar name : Ident)
    (values : Option (List Value)) (hn : name ≠ retVar) :
    (resumeAfterInternalCall frame retVar values).locals.get? name = frame.locals.get? name := by
  cases values <;> simp only [resumeAfterInternalCall, Std.HashMap.get?_eq_getElem?,
    Std.HashMap.getElem?_insert, beq_iff_eq, Ne.symm hn, if_false]

end Benchmarks.UniswapV3.Pool
