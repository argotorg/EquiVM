# WExp proof notes (working file — delete when done)

## Emitted spec (verified by #eval, post-fix)
`wExpTransition.body` = [require cv=0, letDecl __calldata=msgData, require len<2^255+4,
  internalCall "wExp_body" [.var "x"] "__r", return [.var "__r"]]
`wExp_body.body` (8 stmts) = [require(x != -2^255 via .ne? — check: emitted as `.require (.binary .ne? ...)` or `.not (.eq)`),
  .ite (.binary .lt (.var "x") (.intLit 0))
    [.internalCall "wExp_body" [.cast (.unary .neg (.var "x")) (.elem (.int (.sint 256)))] "__c0",
     .return [.binary .div (.intLit 1e36) (.var "__c0")]],
  .letDecl "q" none (.cast (.binary .sdiv (.cast (.binary .add (.var "x") (.intLit C3)) sint) (.intLit C2)) sint),
  .letDecl "r" none (.cast (.binary .sub (.var "x") (.cast (.binary .mul (.var "q") (.intLit C2)) sint)) sint),
  .letDecl "secondTerm" none (.cast (.binary .sdiv (.cast (.binary .mul (.var "r") (.var "r")) sint) (.intLit 2e18)) sint),
  .letDecl "thirdTerm" none (.cast (.binary .sdiv (.cast (.binary .mul (.var "secondTerm") (.var "r")) sint) (.intLit 3e18)) sint),
  .letDecl "expR" none (.cast (.binary .add (.binary .add (.binary .add (.intLit 1e18) (.var "r")) (.var "secondTerm")) (.var "thirdTerm")) sint),  -- nested casts: expR = int256(int256(int256(1e18+r)+st)+tt)
  .return [.binary .shl (.cast (.var "expR") (.elem (.int (.uint 256)))) (.cast (.var "q") (.elem (.int (.uint 256))))]]
C2=693147180559945309 (ln2), C3=322611214989459870 (offset), LN=4987541511039073.

## EVM blocks (tickLibWrapperBlocks.*)
- Arm: `block_93_taken` (callvalue≠0→131) / `block_93_fallthrough` (→99); `block_99_taken` (calldata <36 →131) / `block_99_fallthrough` (→111); `block_111`: PUSH1 32, PUSH2 123, PUSH1 4, CALLDATALOAD, PUSH2 591, JUMP → at 591 stack `[argWord, 123, 32, R]`.
- `block_591_taken` (cond `isZero(slt x0 0)≠0` i.e. x0≥0) → 636 `[x0::R]`; `block_591_fallthrough` (x0<0) → 600 `[x0::R]`.
- `block_600`: `[x0::R]`→`[0-x0, 610, R]` at 591.
- `block_636`: `[x0,x1::R]`→`[polyEvm(x0), R]` at pc x1. polyEvm = `shiftLeft (((r)+sdiv(r*r,2e18)+sdiv(st*r,3e18))+1e18) q` where `q=sdiv(x0+C3,C2)`, `r=x0-q*C2` (all UInt256 ops — see def in RuntimeBlocks_005:115).
- `block_610_taken` (isZero x0≠0 → 456 panic revert) / `block_610_fallthrough` (→617); `block_617`: `[x0,x1::R]`→`[1e36/x0, R]` at x1.
- `block_456` → RDrev (panic). `block_123`: `[x0,x1::R]` → RDret `(x0.toByteArray.write 0 mem (memLoad 64 mem).toNat 32).readWithPadding (memLoad 64 mem).toNat x1.toNat` — for x1=32 → `toByteArray x0` at mem[128..160] (dispatchMemLoad64: memLoad 64 = ⟨128⟩).
- `tickLibWrapperReachWExpBody` → `RD ... pc 93 [selWord] mem96 ...` — wait, its stack is `[]`? Check: it ends with stack `[]`? — NO: reach gives `RD ... 93 [(shiftRight (uInt256OfByteArray (cd.readBytes 0 32)) 224)]` — wait for wExp it's `[]`? Line 221: `[]` — hmm actually the stack at 93 for wExp is `[]`? — the reach for wExp (line 217-223) shows stack `[]` — CHECK actual signature.
  — Correction from Dispatch.lean:220-222: `RD ... (ofNat 93) [] mem96 (M 0 64 32) ∅ σ k C` — stack EMPTY? — wait no — read again: `[tickLibWrapperSelBytes 5]` reach — the stack is `[]`?? — actually at line 221 `[]` yes — NO WAIT — maxTick/others have `[shiftRight ...]` — wExp's reach ends `[]`? — VERIFY — probably `[]` because the arm pops the selector. Hmm — actually looking at line 221: `[]` — the wExp reach stack is empty list? For maxTick it's `[shiftRight (uInt256OfByteArray ...) 224]`. WExp's is probably `[shiftRight ...]` too — need to check line 221 carefully — I recalled `[]` but likely `[selWord]` — VERIFY before use.

## Key eval/combinator facts
- `Expr.cast` → `castValue?` → `.int (normalizeInt ty i)` (wrap, `castValue_int`).
- `.inRange` → revert iff out of range.
- `.sdiv` on `.int` → `.int (Int.tdiv a b)`, `.revert` if b=0. `.div` → `.int (Int.ediv a b)` (=floor=trunc on nonneg), `.revert` if b=0.
- `.ne` → `.bool (a ≠ b)`; `!=` emits `.binary .ne`.
- `ABlock`: `start`, `.requireStep (heval : evalExpr? cond = .ok (.bool true))`, `.letStep (heval : evalExpr? expr = .ok v)`, `.returns (heval : evalExpr? expr = .ok v)`, `.requireRevert (evalExpr? cond = .ok (.bool false))`, `.run ExecBlock.nil` for `.ok` finish; `ExecBlock.consNormal (ExecStmt.iteFalse heval) rest`, `ExecFuncBody.execBlockOK/execBlockRet/execBlockRevert`.
- `ExecStmt.internalCallReturn` args: evalExprs? args = .ok argVals; lookupCallable? = some callee; bindParams? = some locals; ExecFuncBody callee → `.ok (resumeAfterInternalCall ...)`.
- `internalCallFunctionReturn` (SteleBody.lean:254) — same, callee : FunctionDecl.
- `evalCallvalueEq_true/false`; `evalCalldataLen_true/false`, `store_get_self` (in MaxTick.lean — import it if needed).
- `internalCall`'s caller-side resume: `ExecStmt.internalCallReturn` produces `.ok` then `.return` continues — in ABlock use `consNormal`.
- `runtimeRefinementFor`: `.execution` (Ξ_res + steleRes + execResultsEquiv) / `.outOfGas` (Ξ = .error .OutOfGass). `RDret.reEquivExecution hcode hd hdec hbody henc`; `RDrev.reEquivExecutionRevert`; `reEquiv_outOfGas (Xi_error_of_X_sat ...)`.
- `execResultsEquiv.stackOverflowHalt`: `.error .StackOverflow` ↔ `.reverted` (NEW — user added).

## x=-2^255 case
- Spec: require fails → `.reverted` (ExecFuncBody.execBlockRevert via requireRevert).
- EVM: infinite loop 591→600→591, +1 stack word/iter → `.error .StackOverflow` for g ≥ ~48k; `.error .OutOfGass` for g < 48k → `outOfGas` ctor.
- Need: `X (g+1) (D_J code 0) s0 = .error .StackOverflow` via n-iter RD induction then Xstep push-overflow error (model on `RD.returndatacopyOOG_error` Reach.lean ~4827 / Xstep def Semantics.lean:686). `Ξ = .error .StackOverflow` then `execution` + `stackOverflowHalt` + spec `.reverted`.

## Arithmetic bridge needed
`block_636_stack argWord = wordOfInt (specResult)` — write `wordOfInt_sdiv/_mul/_shiftLeft` locally; `wordOfInt_add_words`, `wordOfInt_sub_toUInt256`, `wordOfInt_neg_natCast_eq_sub_zero`, `normalizeInt_sint256_word`, `uInt256_ofNat`-style helpers in Reasoning/.

## Build
`lake env lean Benchmarks/Midnight/TickLibWrapper/WExp.lean`
Done already: MaxTick/LnOnePlusDelta/PriceRoundingStep/Constructor compile clean. TickToPrice/PriceToTick = OTHER agents.

## Verified corrections (this session)
- `tickLibWrapperReachWExpBody` stack at pc 93 = `[]` (empty — selector consumed; Dispatch.lean:220-222).
- `tickLibWrapperBlock` names confirmed: `block_93_taken/_fallthrough` (callvalue), `block_99_taken/_fallthrough` (cd<36→131 | →111), `block_111` (loads arg → 591, stack [arg,123,32,R]), `block_591_taken` (x0≥0→636) / `block_591_fallthrough` (x0<0→600), `block_600` ([x,R]→[0-x,610,R]@591), `block_636` (poly_evm(x0), jump x1), `block_610_taken` (x0=0→456 panic)/`fallthrough`(→617), `block_617` ([x0,x1::R]→[1e36/x0,R]@x1), `block_456`→RDrev, `block_123`→RDret `(x0.toByteArray.write 0 mem (memLoad 64 mem).toNat 32).readWithPadding _ x1.toNat` (x1=32→toByteArray x0).
- `wExp_body.body.length = 8` — `require` emitted (verified; stale-olean artifact earlier).
- `wExpTransition.body` (5 stmts): `[require cv, letDecl __calldata, require len<2^255+4, internalCall wExp_body [x] __r, return __r]`. Param `x : .sint 256`.
- `ABlock` combinators: NO `.iteStep`/`.internalCallStep` — use `ExecBlock.consNormal (ExecStmt.iteFalse heval) rest` / `consNormal (internalCallFunctionReturn ...) rest`.
- `execResultsEquiv.stackOverflowHalt` (NEW, user-added): `.error .StackOverflow` ↔ `.reverted`.
- Decode: `externalABI = defaultExternalCallABI` = `.modern` mode; scalar-word decode lemmas only for `_legacy`/`_vyper` — need `decodeCalldataWithMode`/`decodeABIWord?` unfold for `.modern` (.sint→`.int (normalizeInt (.sint 256) word)`).
- `ABlock.run ExecBlock.nil` → `.ok`; `ExecFuncBody.execBlockOK` → `.returned … none`.
- Build: `lake env lean Benchmarks/Midnight/TickLibWrapper/WExp.lean` — current state: compiles with 2 sorries (wExpDecode_ok, tickLibWrapperWExpBody).
- `Int.toWord` doesn't exist; `.sint 256` needs `(ABI.IntType.sint ⟨256, by decide⟩)`; `EVM.wordOfInt i` for `.int`→word.
