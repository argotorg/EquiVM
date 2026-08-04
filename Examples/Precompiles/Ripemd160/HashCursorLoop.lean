import Examples.Precompiles.Ripemd160.HashCursorRound

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Ripemd160

theorem runtimeLeftGroupCursor_padded {I : ExecutionEnv}
    {initial : RuntimeMemCursor} {n group rounds : Nat}
    (hc : RuntimePaddedCursor I initial n)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize) :
    RuntimePaddedCursor I
      (runtimeLeftGroupCursor initial (hashScratchPtr I) group rounds) n := by
  induction rounds with
  | zero => simpa [runtimeLeftGroupCursor] using hc
  | succ round ih =>
      simpa [runtimeLeftGroupCursor] using runtimeLeftRoundCursor_padded ih hsmall

theorem runtimeRightGroupCursor_padded {I : ExecutionEnv}
    {initial : RuntimeMemCursor} {n group rounds : Nat}
    (hc : RuntimePaddedCursor I initial n)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize) :
    RuntimePaddedCursor I
      (runtimeRightGroupCursor initial (hashScratchPtr I) group rounds) n := by
  induction rounds with
  | zero => simpa [runtimeRightGroupCursor] using hc
  | succ round ih =>
      simpa [runtimeRightGroupCursor] using runtimeRightRoundCursor_padded ih hsmall

theorem runtimeLeftLineCursor_padded {I : ExecutionEnv}
    {initial : RuntimeMemCursor} {n groups : Nat}
    (hc : RuntimePaddedCursor I initial n)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize) :
    RuntimePaddedCursor I
      (runtimeLeftLineCursor initial (hashScratchPtr I) groups) n := by
  induction groups with
  | zero => simpa [runtimeLeftLineCursor] using hc
  | succ group ih =>
      simpa [runtimeLeftLineCursor] using runtimeLeftGroupCursor_padded ih hsmall

theorem runtimeRightLineCursor_padded {I : ExecutionEnv}
    {initial : RuntimeMemCursor} {n groups : Nat}
    (hc : RuntimePaddedCursor I initial n)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize) :
    RuntimePaddedCursor I
      (runtimeRightLineCursor initial (hashScratchPtr I) groups) n := by
  induction groups with
  | zero => simpa [runtimeRightLineCursor] using hc
  | succ group ih =>
      simpa [runtimeRightLineCursor] using runtimeRightGroupCursor_padded ih hsmall

theorem runtimeHashStep_padded {I : ExecutionEnv}
    {s : RuntimeHashState} {block : Nat}
    (hc : RuntimePaddedCursor I s.cursor 0)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize)
    (hblock : block < Model.paddedLength I.calldata.size / 64) :
    RuntimePaddedCursor I (runtimeHashStep I block s).cursor 0 := by
  let parsed := hashParseCursor I (UInt256.ofNat block) s.cursor 16
  have hp : RuntimePaddedCursor I parsed 16 :=
    hashParseCursor_padded_of_cursor I hc hsmall hblock (by omega)
  let leftInit := hashLeftInitCursor I s.chain parsed
  have hl0 : RuntimePaddedCursor I leftInit 16 := hashLeftInitCursor_padded hp hsmall
  let left := runtimeLeftLineCursor leftInit (hashScratchPtr I) 5
  have hl : RuntimePaddedCursor I left 16 := runtimeLeftLineCursor_padded hl0 hsmall
  let rightInit := hashRightInitCursor I s.chain left
  have hr0 : RuntimePaddedCursor I rightInit 16 := hashRightInitCursor_padded hl hsmall
  let right := runtimeRightLineCursor rightInit (hashScratchPtr I) 5
  have hr : RuntimePaddedCursor I right 16 := runtimeRightLineCursor_padded hr0 hsmall
  have hrzero := hr.weaken (m := 0) (by omega)
  simpa [runtimeHashStep, parsed, leftInit, left, rightInit, right] using hrzero

theorem runtimeHashRun_padded {I : ExecutionEnv}
    {initial : RuntimeHashState} {blocks : Nat}
    (hc : RuntimePaddedCursor I initial.cursor 0)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize)
    (hblocks : blocks ≤ Model.paddedLength I.calldata.size / 64) :
    RuntimePaddedCursor I (runtimeHashRun I blocks initial).cursor 0 := by
  induction blocks with
  | zero => simpa [runtimeHashRun] using hc
  | succ block ih =>
      have hprev := ih (by omega)
      simpa [runtimeHashRun] using runtimeHashStep_padded hprev hsmall (by omega)

end Ripemd160
