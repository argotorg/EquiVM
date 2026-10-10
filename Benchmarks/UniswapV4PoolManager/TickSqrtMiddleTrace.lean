import Benchmarks.UniswapV4PoolManager.TickSqrtConditionalTrace
import Benchmarks.UniswapV4PoolManager.Routines
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_047
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_048
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_049

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def tickSqrtMiddleFactors : List (UInt256 × UInt256) := (tickSqrtFactors.drop 1).take 17

set_option maxHeartbeats 1000000 in
theorem tickSqrtMiddleTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw absTick tick price : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length + 5 ≤ 1024)
    (h : RD (deployedRuntime v) I g s0 ⟨16809⟩ (absTick :: tick :: price :: R) mem aw rdata σ k C) :
    ∃ k' C', RD (deployedRuntime v) I g s0 ⟨16976⟩
      (absTick :: tick :: tickSqrtStages absTick price tickSqrtMiddleFactors :: R) mem aw rdata σ k' C' := by
  let p1 := tickSqrtStage absTick price (UInt256.ofNat 4) (UInt256.ofNat 340214320654664324051920982716015181260)
  have h1 : ∃ k' C', RD (deployedRuntime v) I g s0 ⟨16818⟩
      (absTick :: tick :: p1 :: R) mem aw rdata σ k' C' := by
    apply tickSqrtConditionalTrace (fun p => absTick :: tick :: p :: R)
    · intro hz
      exact ⟨_, _, poolManagerBlocks.poolManager_block_16809_fallthrough (by simp only [List.length_cons]; omega) hz h⟩
    · intro hn
      have taken := poolManagerBlocks.poolManager_block_16809_taken (by simp only [List.length_cons]; omega) hn
        (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
      have scaled := poolManagerBlocks.poolManager_block_17510 (by omega)
        (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) taken
      change RD (deployedRuntime v) I g s0 ⟨16818⟩
        (absTick :: tick :: UInt256.shiftRight (UInt256.mul (UInt256.ofNat 340214320654664324051920982716015181260) price) (UInt256.ofNat 128) :: R)
        mem aw rdata σ _ _ at scaled
      rw [u256_mul_comm (UInt256.ofNat 340214320654664324051920982716015181260) price] at scaled
      exact ⟨_, _, scaled⟩
  obtain ⟨k1, C1, rd1⟩ := h1
  let p2 := tickSqrtStage absTick p1 (UInt256.ofNat 8) (UInt256.ofNat 340146287995602323631171512101879684304)
  have h2 : ∃ k' C', RD (deployedRuntime v) I g s0 ⟨16827⟩
      (absTick :: tick :: p2 :: R) mem aw rdata σ k' C' := by
    apply tickSqrtConditionalTrace (fun p => absTick :: tick :: p :: R)
    · intro hz
      exact ⟨_, _, poolManagerBlocks.poolManager_block_16818_fallthrough (by simp only [List.length_cons]; omega) hz rd1⟩
    · intro hn
      have taken := poolManagerBlocks.poolManager_block_16818_taken (by simp only [List.length_cons]; omega) hn
        (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd1
      have scaled := poolManagerBlocks.poolManager_block_17482 (by omega)
        (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) taken
      change RD (deployedRuntime v) I g s0 ⟨16827⟩
        (absTick :: tick :: UInt256.shiftRight (UInt256.mul (UInt256.ofNat 340146287995602323631171512101879684304) p1) (UInt256.ofNat 128) :: R)
        mem aw rdata σ _ _ at scaled
      rw [u256_mul_comm (UInt256.ofNat 340146287995602323631171512101879684304) p1] at scaled
      exact ⟨_, _, scaled⟩
  obtain ⟨k2, C2, rd2⟩ := h2
  let p3 := tickSqrtStage absTick p2 (UInt256.ofNat 16) (UInt256.ofNat 340010263488231146823593991679159461444)
  have h3 : ∃ k' C', RD (deployedRuntime v) I g s0 ⟨16836⟩
      (absTick :: tick :: p3 :: R) mem aw rdata σ k' C' := by
    apply tickSqrtConditionalTrace (fun p => absTick :: tick :: p :: R)
    · intro hz
      exact ⟨_, _, poolManagerBlocks.poolManager_block_16827_fallthrough (by simp only [List.length_cons]; omega) hz rd2⟩
    · intro hn
      have taken := poolManagerBlocks.poolManager_block_16827_taken (by simp only [List.length_cons]; omega) hn
        (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd2
      have scaled := poolManagerBlocks.poolManager_block_17454 (by omega)
        (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) taken
      change RD (deployedRuntime v) I g s0 ⟨16836⟩
        (absTick :: tick :: UInt256.shiftRight (UInt256.mul (UInt256.ofNat 340010263488231146823593991679159461444) p2) (UInt256.ofNat 128) :: R)
        mem aw rdata σ _ _ at scaled
      rw [u256_mul_comm (UInt256.ofNat 340010263488231146823593991679159461444) p2] at scaled
      exact ⟨_, _, scaled⟩
  obtain ⟨k3, C3, rd3⟩ := h3
  let p4 := tickSqrtStage absTick p3 (UInt256.ofNat 32) (UInt256.ofNat 339738377640345403697157401104375502016)
  have h4 : ∃ k' C', RD (deployedRuntime v) I g s0 ⟨16845⟩
      (absTick :: tick :: p4 :: R) mem aw rdata σ k' C' := by
    apply tickSqrtConditionalTrace (fun p => absTick :: tick :: p :: R)
    · intro hz
      exact ⟨_, _, poolManagerBlocks.poolManager_block_16836_fallthrough (by simp only [List.length_cons]; omega) hz rd3⟩
    · intro hn
      have taken := poolManagerBlocks.poolManager_block_16836_taken (by simp only [List.length_cons]; omega) hn
        (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd3
      have scaled := poolManagerBlocks.poolManager_block_17426 (by omega)
        (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) taken
      change RD (deployedRuntime v) I g s0 ⟨16845⟩
        (absTick :: tick :: UInt256.shiftRight (UInt256.mul (UInt256.ofNat 339738377640345403697157401104375502016) p3) (UInt256.ofNat 128) :: R)
        mem aw rdata σ _ _ at scaled
      rw [u256_mul_comm (UInt256.ofNat 339738377640345403697157401104375502016) p3] at scaled
      exact ⟨_, _, scaled⟩
  obtain ⟨k4, C4, rd4⟩ := h4
  let p5 := tickSqrtStage absTick p4 (UInt256.ofNat 64) (UInt256.ofNat 339195258003219555707034227454543997025)
  have h5 : ∃ k' C', RD (deployedRuntime v) I g s0 ⟨16854⟩
      (absTick :: tick :: p5 :: R) mem aw rdata σ k' C' := by
    apply tickSqrtConditionalTrace (fun p => absTick :: tick :: p :: R)
    · intro hz
      exact ⟨_, _, poolManagerBlocks.poolManager_block_16845_fallthrough (by simp only [List.length_cons]; omega) hz rd4⟩
    · intro hn
      have taken := poolManagerBlocks.poolManager_block_16845_taken (by simp only [List.length_cons]; omega) hn
        (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd4
      have scaled := poolManagerBlocks.poolManager_block_17398 (by omega)
        (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) taken
      change RD (deployedRuntime v) I g s0 ⟨16854⟩
        (absTick :: tick :: UInt256.shiftRight (UInt256.mul (UInt256.ofNat 339195258003219555707034227454543997025) p4) (UInt256.ofNat 128) :: R)
        mem aw rdata σ _ _ at scaled
      rw [u256_mul_comm (UInt256.ofNat 339195258003219555707034227454543997025) p4] at scaled
      exact ⟨_, _, scaled⟩
  obtain ⟨k5, C5, rd5⟩ := h5
  let p6 := tickSqrtStage absTick p5 (UInt256.ofNat 128) (UInt256.ofNat 338111622100601834656805679988414885971)
  have h6 : ∃ k' C', RD (deployedRuntime v) I g s0 ⟨16863⟩
      (absTick :: tick :: p6 :: R) mem aw rdata σ k' C' := by
    apply tickSqrtConditionalTrace (fun p => absTick :: tick :: p :: R)
    · intro hz
      exact ⟨_, _, poolManagerBlocks.poolManager_block_16854_fallthrough (by simp only [List.length_cons]; omega) hz rd5⟩
    · intro hn
      have taken := poolManagerBlocks.poolManager_block_16854_taken (by simp only [List.length_cons]; omega) hn
        (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd5
      have scaled := poolManagerBlocks.poolManager_block_17370 (by omega)
        (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) taken
      change RD (deployedRuntime v) I g s0 ⟨16863⟩
        (absTick :: tick :: UInt256.shiftRight (UInt256.mul (UInt256.ofNat 338111622100601834656805679988414885971) p5) (UInt256.ofNat 128) :: R)
        mem aw rdata σ _ _ at scaled
      rw [u256_mul_comm (UInt256.ofNat 338111622100601834656805679988414885971) p5] at scaled
      exact ⟨_, _, scaled⟩
  obtain ⟨k6, C6, rd6⟩ := h6
  let p7 := tickSqrtStage absTick p6 (UInt256.ofNat 256) (UInt256.ofNat 335954724994790223023589805789778977700)
  have h7 : ∃ k' C', RD (deployedRuntime v) I g s0 ⟨16873⟩
      (absTick :: tick :: p7 :: R) mem aw rdata σ k' C' := by
    apply tickSqrtConditionalTrace (fun p => absTick :: tick :: p :: R)
    · intro hz
      exact ⟨_, _, poolManagerBlocks.poolManager_block_16863_fallthrough (by simp only [List.length_cons]; omega) hz rd6⟩
    · intro hn
      have taken := poolManagerBlocks.poolManager_block_16863_taken (by simp only [List.length_cons]; omega) hn
        (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd6
      have scaled := poolManagerBlocks.poolManager_block_17342 (by omega)
        (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) taken
      change RD (deployedRuntime v) I g s0 ⟨16873⟩
        (absTick :: tick :: UInt256.shiftRight (UInt256.mul (UInt256.ofNat 335954724994790223023589805789778977700) p6) (UInt256.ofNat 128) :: R)
        mem aw rdata σ _ _ at scaled
      rw [u256_mul_comm (UInt256.ofNat 335954724994790223023589805789778977700) p6] at scaled
      exact ⟨_, _, scaled⟩
  obtain ⟨k7, C7, rd7⟩ := h7
  let p8 := tickSqrtStage absTick p7 (UInt256.ofNat 512) (UInt256.ofNat 331682121138379247127172139078559817300)
  have h8 : ∃ k' C', RD (deployedRuntime v) I g s0 ⟨16883⟩
      (absTick :: tick :: p8 :: R) mem aw rdata σ k' C' := by
    apply tickSqrtConditionalTrace (fun p => absTick :: tick :: p :: R)
    · intro hz
      exact ⟨_, _, poolManagerBlocks.poolManager_block_16873_fallthrough (by simp only [List.length_cons]; omega) hz rd7⟩
    · intro hn
      have taken := poolManagerBlocks.poolManager_block_16873_taken (by simp only [List.length_cons]; omega) hn
        (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd7
      have scaled := poolManagerBlocks.poolManager_block_17314 (by omega)
        (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) taken
      change RD (deployedRuntime v) I g s0 ⟨16883⟩
        (absTick :: tick :: UInt256.shiftRight (UInt256.mul (UInt256.ofNat 331682121138379247127172139078559817300) p7) (UInt256.ofNat 128) :: R)
        mem aw rdata σ _ _ at scaled
      rw [u256_mul_comm (UInt256.ofNat 331682121138379247127172139078559817300) p7] at scaled
      exact ⟨_, _, scaled⟩
  obtain ⟨k8, C8, rd8⟩ := h8
  let p9 := tickSqrtStage absTick p8 (UInt256.ofNat 1024) (UInt256.ofNat 323299236684853023288211250268160618739)
  have h9 : ∃ k' C', RD (deployedRuntime v) I g s0 ⟨16893⟩
      (absTick :: tick :: p9 :: R) mem aw rdata σ k' C' := by
    apply tickSqrtConditionalTrace (fun p => absTick :: tick :: p :: R)
    · intro hz
      exact ⟨_, _, poolManagerBlocks.poolManager_block_16883_fallthrough (by simp only [List.length_cons]; omega) hz rd8⟩
    · intro hn
      have taken := poolManagerBlocks.poolManager_block_16883_taken (by simp only [List.length_cons]; omega) hn
        (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd8
      have scaled := poolManagerBlocks.poolManager_block_17286 (by omega)
        (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) taken
      change RD (deployedRuntime v) I g s0 ⟨16893⟩
        (absTick :: tick :: UInt256.shiftRight (UInt256.mul (UInt256.ofNat 323299236684853023288211250268160618739) p8) (UInt256.ofNat 128) :: R)
        mem aw rdata σ _ _ at scaled
      rw [u256_mul_comm (UInt256.ofNat 323299236684853023288211250268160618739) p8] at scaled
      exact ⟨_, _, scaled⟩
  obtain ⟨k9, C9, rd9⟩ := h9
  let p10 := tickSqrtStage absTick p9 (UInt256.ofNat 2048) (UInt256.ofNat 307163716377032989948697243942600083929)
  have h10 : ∃ k' C', RD (deployedRuntime v) I g s0 ⟨16903⟩
      (absTick :: tick :: p10 :: R) mem aw rdata σ k' C' := by
    apply tickSqrtConditionalTrace (fun p => absTick :: tick :: p :: R)
    · intro hz
      exact ⟨_, _, poolManagerBlocks.poolManager_block_16893_fallthrough (by simp only [List.length_cons]; omega) hz rd9⟩
    · intro hn
      have taken := poolManagerBlocks.poolManager_block_16893_taken (by simp only [List.length_cons]; omega) hn
        (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd9
      have scaled := poolManagerBlocks.poolManager_block_17258 (by omega)
        (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) taken
      change RD (deployedRuntime v) I g s0 ⟨16903⟩
        (absTick :: tick :: UInt256.shiftRight (UInt256.mul (UInt256.ofNat 307163716377032989948697243942600083929) p9) (UInt256.ofNat 128) :: R)
        mem aw rdata σ _ _ at scaled
      rw [u256_mul_comm (UInt256.ofNat 307163716377032989948697243942600083929) p9] at scaled
      exact ⟨_, _, scaled⟩
  obtain ⟨k10, C10, rd10⟩ := h10
  let p11 := tickSqrtStage absTick p10 (UInt256.ofNat 4096) (UInt256.ofNat 277268403626896220162999269216087595045)
  have h11 : ∃ k' C', RD (deployedRuntime v) I g s0 ⟨16913⟩
      (absTick :: tick :: p11 :: R) mem aw rdata σ k' C' := by
    apply tickSqrtConditionalTrace (fun p => absTick :: tick :: p :: R)
    · intro hz
      exact ⟨_, _, poolManagerBlocks.poolManager_block_16903_fallthrough (by simp only [List.length_cons]; omega) hz rd10⟩
    · intro hn
      have taken := poolManagerBlocks.poolManager_block_16903_taken (by simp only [List.length_cons]; omega) hn
        (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd10
      have scaled := poolManagerBlocks.poolManager_block_17230 (by omega)
        (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) taken
      change RD (deployedRuntime v) I g s0 ⟨16913⟩
        (absTick :: tick :: UInt256.shiftRight (UInt256.mul (UInt256.ofNat 277268403626896220162999269216087595045) p10) (UInt256.ofNat 128) :: R)
        mem aw rdata σ _ _ at scaled
      rw [u256_mul_comm (UInt256.ofNat 277268403626896220162999269216087595045) p10] at scaled
      exact ⟨_, _, scaled⟩
  obtain ⟨k11, C11, rd11⟩ := h11
  let p12 := tickSqrtStage absTick p11 (UInt256.ofNat 8192) (UInt256.ofNat 225923453940442621947126027127485391333)
  have h12 : ∃ k' C', RD (deployedRuntime v) I g s0 ⟨16923⟩
      (absTick :: tick :: p12 :: R) mem aw rdata σ k' C' := by
    apply tickSqrtConditionalTrace (fun p => absTick :: tick :: p :: R)
    · intro hz
      exact ⟨_, _, poolManagerBlocks.poolManager_block_16913_fallthrough (by simp only [List.length_cons]; omega) hz rd11⟩
    · intro hn
      have taken := poolManagerBlocks.poolManager_block_16913_taken (by simp only [List.length_cons]; omega) hn
        (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd11
      have scaled := poolManagerBlocks.poolManager_block_17202 (by omega)
        (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) taken
      change RD (deployedRuntime v) I g s0 ⟨16923⟩
        (absTick :: tick :: UInt256.shiftRight (UInt256.mul (UInt256.ofNat 225923453940442621947126027127485391333) p11) (UInt256.ofNat 128) :: R)
        mem aw rdata σ _ _ at scaled
      rw [u256_mul_comm (UInt256.ofNat 225923453940442621947126027127485391333) p11] at scaled
      exact ⟨_, _, scaled⟩
  obtain ⟨k12, C12, rd12⟩ := h12
  let p13 := tickSqrtStage absTick p12 (UInt256.ofNat 16384) (UInt256.ofNat 149997214084966997727330242082538205943)
  have h13 : ∃ k' C', RD (deployedRuntime v) I g s0 ⟨16933⟩
      (absTick :: tick :: p13 :: R) mem aw rdata σ k' C' := by
    apply tickSqrtConditionalTrace (fun p => absTick :: tick :: p :: R)
    · intro hz
      exact ⟨_, _, poolManagerBlocks.poolManager_block_16923_fallthrough (by simp only [List.length_cons]; omega) hz rd12⟩
    · intro hn
      have taken := poolManagerBlocks.poolManager_block_16923_taken (by simp only [List.length_cons]; omega) hn
        (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd12
      have scaled := poolManagerBlocks.poolManager_block_17174 (by omega)
        (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) taken
      change RD (deployedRuntime v) I g s0 ⟨16933⟩
        (absTick :: tick :: UInt256.shiftRight (UInt256.mul (UInt256.ofNat 149997214084966997727330242082538205943) p12) (UInt256.ofNat 128) :: R)
        mem aw rdata σ _ _ at scaled
      rw [u256_mul_comm (UInt256.ofNat 149997214084966997727330242082538205943) p12] at scaled
      exact ⟨_, _, scaled⟩
  obtain ⟨k13, C13, rd13⟩ := h13
  let p14 := tickSqrtStage absTick p13 (UInt256.ofNat 32768) (UInt256.ofNat 66119101136024775622716233608466517926)
  have h14 : ∃ k' C', RD (deployedRuntime v) I g s0 ⟨16943⟩
      (absTick :: tick :: p14 :: R) mem aw rdata σ k' C' := by
    apply tickSqrtConditionalTrace (fun p => absTick :: tick :: p :: R)
    · intro hz
      exact ⟨_, _, poolManagerBlocks.poolManager_block_16933_fallthrough (by simp only [List.length_cons]; omega) hz rd13⟩
    · intro hn
      have taken := poolManagerBlocks.poolManager_block_16933_taken (by simp only [List.length_cons]; omega) hn
        (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd13
      have scaled := poolManagerBlocks.poolManager_block_17146 (by omega)
        (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) taken
      change RD (deployedRuntime v) I g s0 ⟨16943⟩
        (absTick :: tick :: UInt256.shiftRight (UInt256.mul (UInt256.ofNat 66119101136024775622716233608466517926) p13) (UInt256.ofNat 128) :: R)
        mem aw rdata σ _ _ at scaled
      rw [u256_mul_comm (UInt256.ofNat 66119101136024775622716233608466517926) p13] at scaled
      exact ⟨_, _, scaled⟩
  obtain ⟨k14, C14, rd14⟩ := h14
  let p15 := tickSqrtStage absTick p14 (UInt256.ofNat 65536) (UInt256.ofNat 12847376061809297530290974190478138313)
  have h15 : ∃ k' C', RD (deployedRuntime v) I g s0 ⟨16954⟩
      (absTick :: tick :: p15 :: R) mem aw rdata σ k' C' := by
    apply tickSqrtConditionalTrace (fun p => absTick :: tick :: p :: R)
    · intro hz
      exact ⟨_, _, poolManagerBlocks.poolManager_block_16943_fallthrough (by simp only [List.length_cons]; omega) hz rd14⟩
    · intro hn
      have taken := poolManagerBlocks.poolManager_block_16943_taken (by simp only [List.length_cons]; omega) hn
        (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd14
      have scaled := poolManagerBlocks.poolManager_block_17118 (by omega)
        (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) taken
      change RD (deployedRuntime v) I g s0 ⟨16954⟩
        (absTick :: tick :: UInt256.shiftRight (UInt256.mul (UInt256.ofNat 12847376061809297530290974190478138313) p14) (UInt256.ofNat 128) :: R)
        mem aw rdata σ _ _ at scaled
      rw [u256_mul_comm (UInt256.ofNat 12847376061809297530290974190478138313) p14] at scaled
      exact ⟨_, _, scaled⟩
  obtain ⟨k15, C15, rd15⟩ := h15
  let p16 := tickSqrtStage absTick p15 (UInt256.ofNat 131072) (UInt256.ofNat 485053260817066172746253684029974020)
  have h16 : ∃ k' C', RD (deployedRuntime v) I g s0 ⟨16965⟩
      (absTick :: tick :: p16 :: R) mem aw rdata σ k' C' := by
    apply tickSqrtConditionalTrace (fun p => absTick :: tick :: p :: R)
    · intro hz
      exact ⟨_, _, poolManagerBlocks.poolManager_block_16954_fallthrough (by simp only [List.length_cons]; omega) hz rd15⟩
    · intro hn
      have taken := poolManagerBlocks.poolManager_block_16954_taken (by simp only [List.length_cons]; omega) hn
        (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd15
      have scaled := poolManagerBlocks.poolManager_block_17091 (by omega)
        (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) taken
      change RD (deployedRuntime v) I g s0 ⟨16965⟩
        (absTick :: tick :: UInt256.shiftRight (UInt256.mul (UInt256.ofNat 485053260817066172746253684029974020) p15) (UInt256.ofNat 128) :: R)
        mem aw rdata σ _ _ at scaled
      rw [u256_mul_comm (UInt256.ofNat 485053260817066172746253684029974020) p15] at scaled
      exact ⟨_, _, scaled⟩
  obtain ⟨k16, C16, rd16⟩ := h16
  let p17 := tickSqrtStage absTick p16 (UInt256.ofNat 262144) (UInt256.ofNat 691415978906521570653435304214168)
  have h17 : ∃ k' C', RD (deployedRuntime v) I g s0 ⟨16976⟩
      (absTick :: tick :: p17 :: R) mem aw rdata σ k' C' := by
    apply tickSqrtConditionalTrace (fun p => absTick :: tick :: p :: R)
    · intro hz
      exact ⟨_, _, poolManagerBlocks.poolManager_block_16965_fallthrough (by simp only [List.length_cons]; omega) hz rd16⟩
    · intro hn
      have taken := poolManagerBlocks.poolManager_block_16965_taken (by simp only [List.length_cons]; omega) hn
        (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd16
      have scaled := poolManagerBlocks.poolManager_block_17064 (by omega)
        (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) taken
      exact ⟨_, _, scaled⟩
  obtain ⟨k17, C17, rd17⟩ := h17
  exact ⟨_, _, rd17⟩

end Benchmarks.UniswapV4PoolManager
