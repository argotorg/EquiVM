import Solidity.Theory.Sound.Small
import Solidity.Theory.Sound.Stmt
import Solidity.Theory.Sound.Member
import Solidity.Theory.Sound.Call
import Solidity.Theory.Sound.Expr

/-!
# Soundness of the interpreter

Every result the fuel-indexed interpreter produces is derivable in the relational semantics.
-/

namespace Solidity

open Interp

variable {cfg : Config} {o : Oracle} {fc : FlatContract}

theorem soundAt_succ {n} (ih : SoundAt cfg o fc n) : SoundAt cfg o fc (n+1) where
  expr := evalExpr_sound_step ih
  member := evalMember_sound_step ih
  builtin := evalBuiltin_sound_step ih
  call := evalCall_sound_step ih
  namedCall := evalNamedCall_sound_step ih
  abi := evalAbi_sound_step ih
  memberCall := evalMemberCall_sound_step ih
  valueOpt := evalValueOpt_sound_step ih
  saltOpt := evalSaltOpt_sound_step ih
  gasOpt := evalGasOpt_sound_step ih
  exprs := evalExprs_sound_step ih
  lvalue := evalLValue_sound_step ih
  assignTuple := assignTuple_sound_step ih
  declareTuple := declareTuple_sound_step ih
  stmt := execStmt_sound_step ih
  loop := execLoop_sound_step ih
  loopBody := execLoopBody_sound_step ih
  block := execBlock_sound_step ih
  chain := execChain_sound_step ih
  mods := evalMods_sound_step ih
  callFn := callFn_sound_step ih

theorem soundAt (cfg : Config) (o : Oracle) (fc : FlatContract) : ∀ n, SoundAt cfg o fc n
  | 0 => soundAt_zero cfg o fc
  | n+1 => soundAt_succ (soundAt cfg o fc n)

theorem evalExpr_sound {n fr m e r} (h : (evalExpr cfg o fc n fr m e).run = some r) :
    EvalExpr cfg o fc fr m e (resOf r) :=
  (soundAt cfg o fc n).expr _ _ _ _ h

theorem execStmt_sound {n fr m s r} (h : (execStmt cfg o fc n fr m s).run = some r) :
    ExecStmt cfg o fc fr m s (execOf r) :=
  (soundAt cfg o fc n).stmt _ _ _ _ h

theorem execBlock_sound {n fr m ss r} (h : (execBlock cfg o fc n fr m ss).run = some r) :
    ExecBlock cfg o fc fr m ss (execOf r) :=
  (soundAt cfg o fc n).block _ _ _ _ h

theorem callFn_sound {n fr m fn args r} (h : (callFn cfg o fc n fr m fn args).run = some r) :
    CallFn cfg o fc fr m fn args (fnOf r) :=
  (soundAt cfg o fc n).callFn _ _ _ _ _ h

end Solidity
