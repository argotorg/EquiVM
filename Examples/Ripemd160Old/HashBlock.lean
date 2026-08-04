import Examples.Ripemd160Old.HashRecombine
import Examples.Precompiles.Ripemd160.HashRun

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 5000000

namespace Ripemd160Old

open Ripemd160

def oldRuntimeHashStep (I : ExecutionEnv) (block : Nat)
    (s : RuntimeHashState) : RuntimeHashState :=
  let blk := UInt256.ofNat block
  let X := runtimeParsedWords I blk s.cursor
  let parsed := hashParseCursor I blk s.cursor 16
  let leftCursor := oldLeftLineCursor
    (hashLeftInitCursor I s.chain parsed) (hashScratchPtr I) 80
  let finalCursor := oldRightLineCursor
    (hashRightInitCursor I s.chain leftCursor) (hashScratchPtr I) 80
  { cursor := finalCursor
    chain := runtimeCompressChain X s.chain }

def oldRuntimeHashRun (I : ExecutionEnv) : Nat → RuntimeHashState → RuntimeHashState
  | 0, s => s
  | block + 1, s => oldRuntimeHashStep I block (oldRuntimeHashRun I block s)

/-- Execute one complete compression block in the old 80-round-loop runtime. -/
theorem runtime_compressBlock {cA gh bl σ σ₀ A I} {g : Sat256}
    {block : Nat} {h : RuntimeChain} {initial : RuntimeMemCursor} {k C : Nat}
    (hpadded : RuntimePaddedCursor I initial 0)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize)
    (hblock : block < Model.paddedLength I.calldata.size / 64)
    (rd8533 : RD runtimeBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨8533⟩
      (oldBlockLoopStack I (UInt256.ofNat block) h) initial.mem initial.aw
      ByteArray.empty (cA, σ) k C) :
    let parsed := hashParseCursor I (UInt256.ofNat block) initial 16
    let X := runtimeParsedWords I (UInt256.ofNat block) initial
    let left := runtimePureLeftLine X 5 (runtimeLineOfChain h)
    let leftCursor := oldLeftLineCursor (hashLeftInitCursor I h parsed)
      (hashScratchPtr I) 80
    let right := runtimePureRightLine X 5 (runtimeLineOfChain h)
    let finalCursor := oldRightLineCursor (hashRightInitCursor I h leftCursor)
      (hashScratchPtr I) 80
    ∃ k' C',
      RD runtimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨8533⟩
        (oldBlockLoopStack I (UInt256.ofNat block + ⟨1⟩)
          (runtimeCompressChain X h))
        finalCursor.mem finalCursor.aw ByteArray.empty (cA, σ) k' C' ∧
      RuntimeRightWideInvariant I finalCursor 16 X left right := by
  dsimp only
  obtain ⟨_, _, rd8635⟩ := runtime_enterParseLoop hsmall hblock rd8533
  obtain ⟨_, _, rd8646⟩ := runtime_parseBlock hblock rd8635
  have hp : RuntimePaddedCursor I
      (hashParseCursor I (UInt256.ofNat block) initial 16) 16 :=
    hashParseCursor_padded_of_cursor I hpadded hsmall hblock (by omega)
  have hm := hashParseCursor_message_padded hpadded hsmall hblock
  obtain ⟨_, _, rd8694⟩ := runtime_reachLeftLoop rd8646
  have hleft0 := hm.hashLeftInitWide hp hsmall (h := h)
  obtain ⟨_, _, rdLeft⟩ := runtime_leftLoop (rounds := 80) (by decide) rd8694
  have hleft := oldLeftLineCursor_wideInvariant (rounds := 80) hleft0 hsmall
  obtain ⟨_, _, rd8704⟩ := runtime_leftLoopExit rdLeft
  obtain ⟨_, _, rd8767⟩ := runtime_reachRightLoop rd8704
  have hright0 := hleft.hashRightInitWide hsmall (h := h)
  obtain ⟨_, _, rdRight⟩ := runtime_rightLoop (rounds := 80) (by decide) rd8767
  have hright := oldRightLineCursor_wideInvariant (rounds := 80) hright0 hsmall
  obtain ⟨_, _, rd8777⟩ := runtime_rightLoopExit rdRight
  have hright' : RuntimeRightWideInvariant I
      (oldRightLineCursor
        (hashRightInitCursor I h
          (oldLeftLineCursor
            (hashLeftInitCursor I h
              (hashParseCursor I (UInt256.ofNat block) initial 16))
            (hashScratchPtr I) 80))
        (hashScratchPtr I) 80)
      16 (runtimeParsedWords I (UInt256.ofNat block) initial)
      (runtimePureLeftLine (runtimeParsedWords I (UInt256.ofNat block) initial)
        5 (runtimeLineOfChain h))
      (runtimePureRightLine (runtimeParsedWords I (UInt256.ofNat block) initial)
        5 (runtimeLineOfChain h)) := by
    simpa only [oldPureLeftLine_80, oldPureRightLine_80] using hright
  obtain ⟨k', C', rdNext⟩ := runtime_recombine hright' hsmall rd8777
  exact ⟨k', C', by simpa [runtimeCompressChain] using rdNext, hright'⟩

theorem oldRuntimeHashStep_padded {I : ExecutionEnv}
    {s : RuntimeHashState} {block : Nat}
    (hpadded : RuntimePaddedCursor I s.cursor 0)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize)
    (hblock : block < Model.paddedLength I.calldata.size / 64) :
    RuntimePaddedCursor I (oldRuntimeHashStep I block s).cursor 0 := by
  let parsed := hashParseCursor I (UInt256.ofNat block) s.cursor 16
  have hp : RuntimePaddedCursor I parsed 16 :=
    hashParseCursor_padded_of_cursor I hpadded hsmall hblock (by omega)
  let leftInit := hashLeftInitCursor I s.chain parsed
  have hm := hashParseCursor_message_padded hpadded hsmall hblock
  have hl0 := hm.hashLeftInitWide hp hsmall (h := s.chain)
  let left := oldLeftLineCursor leftInit (hashScratchPtr I) 80
  have hl := oldLeftLineCursor_wideInvariant (rounds := 80) hl0 hsmall
  let rightInit := hashRightInitCursor I s.chain left
  have hr0 := hl.hashRightInitWide hsmall (h := s.chain)
  let right := oldRightLineCursor rightInit (hashScratchPtr I) 80
  have hr := oldRightLineCursor_wideInvariant (rounds := 80) hr0 hsmall
  simpa [oldRuntimeHashStep, parsed, leftInit, left, rightInit, right] using
    hr.padded.weaken (m := 0) (by omega)

end Ripemd160Old
