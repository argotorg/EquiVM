import Examples.Precompiles.Ripemd160.HashWideRecombine

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Ripemd160

/-- Execute one complete compression block without imposing a byte-address `< 2^64` bound. -/
theorem ripemd160X_compressBlock_wideGas {cA gh bl σ σ₀ A I} {g : Sat256}
    {block : Nat} {h : RuntimeChain} {initial : RuntimeMemCursor} {k C : Nat}
    (hblk : UInt256.lt (UInt256.ofNat block) (hashBlockCountWord I) = ⟨1⟩)
    (hpadded : RuntimePaddedCursor I initial 0)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize)
    (hblock : block < Model.paddedLength I.calldata.size / 64)
    (rd1028 : RDx ripemd160RuntimeBytecode I g
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
    ∃ k',
      RDx ripemd160RuntimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1028⟩
        (hashBlockLoopStack I (UInt256.ofNat block + ⟨1⟩)
          (runtimeCompressChain X h))
        finalCursor.mem finalCursor.aw ByteArray.empty (cA, σ) k'
          (C + ripemd160CompressBlockGas I block { cursor := initial, chain := h }) ∧
      RuntimeRightWideInvariant I finalCursor 16 X left right := by
  dsimp only
  obtain ⟨_, rd1304⟩ := ripemd160X_enterParseLoopGas hblk rd1028
  obtain ⟨_, rd1314⟩ := ripemd160X_parseBlockGas rd1304
  have hp : RuntimePaddedCursor I
      (hashParseCursor I (UInt256.ofNat block) initial 16) 16 :=
    hashParseCursor_padded_of_cursor I hpadded hsmall hblock (by omega)
  have hm := hashParseCursor_message_padded hpadded hsmall hblock
  obtain ⟨_, rd1350⟩ := ripemd160X_reachLeftGroupsGas rd1314
  have hleft0 := hm.hashLeftInitWide hp hsmall (h := h)
  obtain ⟨_, rd1360⟩ := ripemd160X_leftLineGas (by
    simpa [hashLeftGroupStack] using rd1350)
  have hleft := runtimeLeftLineCursor_wideInvariant (groups := 5) hleft0 hsmall
  obtain ⟨_, rd1396⟩ := ripemd160X_reachRightGroupsGas rd1360
  have hright0 := hleft.hashRightInitWide hsmall (h := h)
  obtain ⟨_, rd1406⟩ := ripemd160X_rightLineGas (by
    simpa [hashRightGroupStack] using rd1396)
  have hright := runtimeRightLineCursor_wideInvariant (groups := 5) hright0 hsmall
  obtain ⟨k', rdNext⟩ := ripemd160X_recombine_wideGas hright hsmall rd1406
  have rdExact := RDx.withIndices rdNext
    (C' := C + ripemd160CompressBlockGas I block { cursor := initial, chain := h })
    (by rfl) (by simp only [ripemd160CompressBlockGas]; omega)
  exact ⟨k', by simpa [runtimeCompressChain] using rdExact, hright⟩

theorem ripemd160X_compressBlock_wide {cA gh bl σ σ₀ A I} {g : Sat256}
    {block : Nat} {h : RuntimeChain} {initial : RuntimeMemCursor} {k C : Nat}
    (hblk : UInt256.lt (UInt256.ofNat block) (hashBlockCountWord I) = ⟨1⟩)
    (hpadded : RuntimePaddedCursor I initial 0)
    (hsmall : I.calldata.size ≤ maxFallbackCalldataSize)
    (hblock : block < Model.paddedLength I.calldata.size / 64)
    (rd1028 : RDx ripemd160RuntimeBytecode I g
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
      RDx ripemd160RuntimeBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1028⟩
        (hashBlockLoopStack I (UInt256.ofNat block + ⟨1⟩)
          (runtimeCompressChain X h))
        finalCursor.mem finalCursor.aw ByteArray.empty (cA, σ) k' C' ∧
      RuntimeRightWideInvariant I finalCursor 16 X left right := by
  dsimp only
  obtain ⟨k', rd', hi⟩ := ripemd160X_compressBlock_wideGas
    hblk hpadded hsmall hblock rd1028
  exact ⟨k', _, rd', hi⟩

end Ripemd160
