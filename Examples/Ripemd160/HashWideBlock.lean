import Examples.Ripemd160.HashWideRecombine

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Ripemd160

/-- Execute one complete compression block without imposing a byte-address `< 2^64` bound. -/
theorem ripemd160X_compressBlock_wide {cA gh bl σ σ₀ A I} {g : Sat256}
    {block : Nat} {h : RuntimeChain} {initial : RuntimeMemCursor} {k C : Nat}
    (hblk : UInt256.lt (UInt256.ofNat block) (hashBlockCountWord I) = ⟨1⟩)
    (hpadded : RuntimePaddedCursor I initial 0)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize)
    (hblock : block < Model.paddedLength I.calldata.size / 64)
    (rd1028 : RD ripemd160RuntimeBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1028⟩
      (hashBlockLoopStack I (UInt256.ofNat block) h) initial.mem initial.aw
      ByteArray.empty (cA, σ) k C) :
    let parsed := hashParseCursor I (UInt256.ofNat block) initial 16
    let X := runtimeParsedWords I (UInt256.ofNat block) initial
    let left := runtimePureLeftLine X 5 (runtimeLineOfChain h)
    let leftCursor := runtimeLeftLineCursor (hashLeftInitCursor I h parsed)
      (hashScratchPtr I) 5
    let right := runtimePureRightLine X 5 (runtimeLineOfChain h)
    let finalCursor := runtimeRightLineCursor (hashRightInitCursor I h leftCursor)
      (hashScratchPtr I) 5
    ∃ k' C',
      RD ripemd160RuntimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1028⟩
        (hashBlockLoopStack I (UInt256.ofNat block + ⟨1⟩)
          (runtimeCompressChain X h))
        finalCursor.mem finalCursor.aw ByteArray.empty (cA, σ) k' C' ∧
      RuntimeRightWideInvariant I finalCursor 16 X left right := by
  dsimp only
  obtain ⟨_, _, rd1304⟩ := ripemd160X_enterParseLoop hblk rd1028
  obtain ⟨_, _, rd1314⟩ := ripemd160X_parseBlock rd1304
  have hp : RuntimePaddedCursor I
      (hashParseCursor I (UInt256.ofNat block) initial 16) 16 :=
    hashParseCursor_padded_of_cursor I hpadded hsmall hblock (by omega)
  have hm := hashParseCursor_message_padded hpadded hsmall hblock
  obtain ⟨_, _, rd1350⟩ := ripemd160X_reachLeftGroups rd1314
  have hleft0 := hm.hashLeftInitWide hp hsmall (h := h)
  obtain ⟨_, _, rd1360⟩ := ripemd160X_leftLine (by
    simpa [hashLeftGroupStack] using rd1350)
  have hleft := runtimeLeftLineCursor_wideInvariant (groups := 5) hleft0 hsmall
  obtain ⟨_, _, rd1396⟩ := ripemd160X_reachRightGroups rd1360
  have hright0 := hleft.hashRightInitWide hsmall (h := h)
  obtain ⟨_, _, rd1406⟩ := ripemd160X_rightLine (by
    simpa [hashRightGroupStack] using rd1396)
  have hright := runtimeRightLineCursor_wideInvariant (groups := 5) hright0 hsmall
  obtain ⟨k', C', rdNext⟩ := ripemd160X_recombine_wide hright hsmall rd1406
  exact ⟨k', C', by simpa [runtimeCompressChain] using rdNext, hright⟩

end Ripemd160
