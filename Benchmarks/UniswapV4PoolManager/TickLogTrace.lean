import Benchmarks.UniswapV4PoolManager.TickLogBlockTrace
import Benchmarks.UniswapV4PoolManager.TickLogUnroll

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

set_option maxHeartbeats 1000000 in
theorem tickLogTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw r msb : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length + 20 ≤ 1024)
    (h : RD (deployedRuntime v) I g s0 ⟨18089⟩ (r :: msb :: R) mem aw rdata σ k C) :
    let log2 := (tickLogStages r (tickPriceLogStart msb) tickLogStageData).2
    ∃ k' C', RD (deployedRuntime v) I g s0 ⟨18536⟩
      (UInt256.ofNat 2 :: tickPriceLowRaw log2 :: tickPriceScaled log2 :: R) mem aw rdata σ k' C' := by
  let r0 := r
  let r1 := tickLogNext r0 true
  let r2 := tickLogNext r1 true
  let r3 := tickLogNext r2 true
  let r4 := tickLogNext r3 true
  let r5 := tickLogNext r4 true
  let r6 := tickLogNext r5 true
  let r7 := tickLogNext r6 true
  let r8 := tickLogNext r7 true
  let r9 := tickLogNext r8 true
  let r10 := tickLogNext r9 true
  let r11 := tickLogNext r10 true
  let r12 := tickLogNext r11 true
  let r13 := tickLogNext r12 true
  obtain ⟨k1, C1, rd1⟩ := tickLogBlock18089 (r0 := r0) v (by (try simp only [List.length_cons]); omega) h
  change RD (deployedRuntime v) I g s0 ⟨18108⟩
    ((UInt256.mul r1 r1) :: (tickLogSquare r1) :: (UInt256.mul r1 r1) :: (UInt256.mul r0 r0) :: msb :: R) mem aw rdata σ k1 C1 at rd1
  obtain ⟨k2, C2, rd2⟩ := tickLogBlock18108 (r1 := r1) v (by (try simp only [List.length_cons]); omega) rd1
  change RD (deployedRuntime v) I g s0 ⟨18128⟩
    ((UInt256.ofNat 127) :: (UInt256.mul r3 r3) :: (UInt256.mul r3 r3) :: (UInt256.mul r2 r2) :: (UInt256.mul r1 r1) :: (UInt256.mul r0 r0) :: msb :: R) mem aw rdata σ k2 C2 at rd2
  obtain ⟨k3, C3, rd3⟩ := tickLogBlock18128 (r3 := r3) v (by (try simp only [List.length_cons]); omega) rd2
  change RD (deployedRuntime v) I g s0 ⟨18147⟩
    ((UInt256.mul r5 r5) :: (UInt256.mul r4 r4) :: (UInt256.mul r3 r3) :: (UInt256.mul r2 r2) :: (UInt256.mul r1 r1) :: (UInt256.mul r0 r0) :: msb :: R) mem aw rdata σ k3 C3 at rd3
  obtain ⟨k4, C4, rd4⟩ := tickLogBlock18147 (r5 := r5) v (by (try simp only [List.length_cons]); omega) rd3
  change RD (deployedRuntime v) I g s0 ⟨18167⟩
    ((tickLogFlag r6) :: (tickLogSquare r6) :: (UInt256.mul r5 r5) :: (UInt256.mul r6 r6) :: (UInt256.mul r4 r4) :: (UInt256.mul r3 r3) :: (UInt256.mul r2 r2) :: (UInt256.mul r1 r1) :: (UInt256.mul r0 r0) :: msb :: R) mem aw rdata σ k4 C4 at rd4
  obtain ⟨k5, C5, rd5⟩ := tickLogBlock18167 (r3 := r3) (r4 := r4) (r5 := r5) (r6 := r6) v (by (try simp only [List.length_cons]); omega) rd4
  change RD (deployedRuntime v) I g s0 ⟨18186⟩
    ((UInt256.ofNat 127) :: (UInt256.mul r8 r8) :: (UInt256.mul r3 r3) :: (UInt256.mul r4 r4) :: (UInt256.mul r5 r5) :: (UInt256.mul r6 r6) :: (UInt256.mul r7 r7) :: (UInt256.mul r8 r8) :: (UInt256.mul r2 r2) :: (UInt256.mul r1 r1) :: (UInt256.mul r0 r0) :: msb :: R) mem aw rdata σ k5 C5 at rd5
  obtain ⟨k6, C6, rd6⟩ := tickLogBlock18186 (r2 := r2) (r3 := r3) (r4 := r4) (r5 := r5) (r6 := r6) (r7 := r7) (r8 := r8) v (by (try simp only [List.length_cons]); omega) rd5
  change RD (deployedRuntime v) I g s0 ⟨18205⟩
    (r10 :: r10 :: (UInt256.mul r2 r2) :: (UInt256.mul r3 r3) :: (UInt256.mul r4 r4) :: (UInt256.mul r5 r5) :: (UInt256.mul r6 r6) :: (UInt256.mul r7 r7) :: (UInt256.mul r8 r8) :: (UInt256.mul r9 r9) :: (UInt256.mul r1 r1) :: (UInt256.mul r0 r0) :: msb :: R) mem aw rdata σ k6 C6 at rd6
  obtain ⟨k7, C7, rd7⟩ := tickLogBlock18205 (r0 := r0) (r1 := r1) (r2 := r2) (r3 := r3) (r4 := r4) (r5 := r5) (r6 := r6) (r7 := r7) (r8 := r8) (r9 := r9) (r10 := r10) v (by (try simp only [List.length_cons]); omega) rd6
  change RD (deployedRuntime v) I g s0 ⟨18224⟩
    ((UInt256.mul r11 r11) :: (tickLogSquare r11) :: (UInt256.mul r0 r0) :: (UInt256.mul r1 r1) :: (UInt256.mul r2 r2) :: (UInt256.mul r3 r3) :: (UInt256.mul r4 r4) :: (UInt256.mul r5 r5) :: (UInt256.mul r6 r6) :: (UInt256.mul r7 r7) :: (UInt256.mul r8 r8) :: (UInt256.mul r9 r9) :: (UInt256.mul r10 r10) :: (UInt256.mul r11 r11) :: msb :: R) mem aw rdata σ k7 C7 at rd7
  obtain ⟨k8, C8, rd8⟩ := tickLogBlock18224 (r0 := r0) (r1 := r1) (r2 := r2) (r3 := r3) (r4 := r4) (r5 := r5) (r6 := r6) (r7 := r7) (r8 := r8) (r9 := r9) (r10 := r10) (r11 := r11) (msb := msb) v (by (try simp only [List.length_cons]); omega) rd7
  change RD (deployedRuntime v) I g s0 ⟨18243⟩
    ((UInt256.mul r13 r13) :: msb :: (UInt256.mul r0 r0) :: (UInt256.mul r1 r1) :: (UInt256.mul r2 r2) :: (UInt256.mul r3 r3) :: (UInt256.mul r4 r4) :: (UInt256.mul r5 r5) :: (UInt256.mul r6 r6) :: (UInt256.mul r7 r7) :: (UInt256.mul r8 r8) :: (UInt256.mul r9 r9) :: (UInt256.mul r10 r10) :: (UInt256.mul r11 r11) :: (UInt256.mul r12 r12) :: R) mem aw rdata σ k8 C8 at rd8
  obtain ⟨k9, C9, rd9⟩ := tickLogBlock18243 (r0 := r0) (r1 := r1) (r2 := r2) (r3 := r3) (r4 := r4) (r5 := r5) (r6 := r6) (r7 := r7) (r8 := r8) (r9 := r9) (r10 := r10) (r11 := r11) (r12 := r12) (r13 := r13) (msb := msb) v (by (try simp only [List.length_cons]); omega) rd8
  change RD (deployedRuntime v) I g s0 ⟨18284⟩
    ((UInt256.ofNat 202) :: (UInt256.mul r10 r10) :: msb :: (UInt256.mul r0 r0) :: (UInt256.mul r1 r1) :: (UInt256.mul r2 r2) :: (UInt256.mul r3 r3) :: (UInt256.mul r4 r4) :: (UInt256.mul r5 r5) :: (UInt256.mul r6 r6) :: (UInt256.mul r7 r7) :: (UInt256.mul r8 r8) :: (UInt256.mul r9 r9) :: (UInt256.shiftLeft (tickLogFlag r11) (UInt256.ofNat 52)) :: (UInt256.shiftLeft (tickLogFlag r12) (UInt256.ofNat 51)) :: (UInt256.shiftLeft (tickLogFlag r13) (UInt256.ofNat 50)) :: R) mem aw rdata σ k9 C9 at rd9
  obtain ⟨k10, C10, rd10⟩ := tickLogBlock18284 (r0 := r0) (r1 := r1) (r2 := r2) (r3 := r3) (r4 := r4) (r5 := r5) (r6 := r6) (r7 := r7) (r8 := r8) (r9 := r9) (r10 := r10) (msb := msb) v (by (try simp only [List.length_cons]); omega) rd9
  change RD (deployedRuntime v) I g s0 ⟨18324⟩
    ((UInt256.shiftRight (UInt256.mul r7 r7) (UInt256.ofNat 199)) :: msb :: (UInt256.mul r0 r0) :: (UInt256.mul r1 r1) :: (UInt256.mul r2 r2) :: (UInt256.mul r3 r3) :: (UInt256.mul r4 r4) :: (UInt256.mul r5 r5) :: (UInt256.mul r6 r6) :: (UInt256.shiftLeft (tickLogFlag r8) (UInt256.ofNat 55)) :: (UInt256.shiftLeft (tickLogFlag r9) (UInt256.ofNat 54)) :: (UInt256.shiftLeft (tickLogFlag r10) (UInt256.ofNat 53)) :: (UInt256.shiftLeft (tickLogFlag r11) (UInt256.ofNat 52)) :: (UInt256.shiftLeft (tickLogFlag r12) (UInt256.ofNat 51)) :: (UInt256.shiftLeft (tickLogFlag r13) (UInt256.ofNat 50)) :: R) mem aw rdata σ k10 C10 at rd10
  obtain ⟨k11, C11, rd11⟩ := tickLogBlock18324 (r0 := r0) (r1 := r1) (r2 := r2) (r3 := r3) (r4 := r4) (r5 := r5) (r6 := r6) (r7 := r7) (msb := msb) v (by (try simp only [List.length_cons]); omega) rd10
  change RD (deployedRuntime v) I g s0 ⟨18375⟩
    ((UInt256.ofNat 576460752303423488) :: (UInt256.shiftRight (UInt256.mul r4 r4) (UInt256.ofNat 196)) :: msb :: (UInt256.mul r0 r0) :: (UInt256.mul r1 r1) :: (UInt256.mul r2 r2) :: (UInt256.mul r3 r3) :: (UInt256.shiftLeft (tickLogFlag r5) (UInt256.ofNat 58)) :: (UInt256.shiftLeft (tickLogFlag r6) (UInt256.ofNat 57)) :: (UInt256.shiftLeft (tickLogFlag r7) (UInt256.ofNat 56)) :: (UInt256.shiftLeft (tickLogFlag r8) (UInt256.ofNat 55)) :: (UInt256.shiftLeft (tickLogFlag r9) (UInt256.ofNat 54)) :: (UInt256.shiftLeft (tickLogFlag r10) (UInt256.ofNat 53)) :: (UInt256.shiftLeft (tickLogFlag r11) (UInt256.ofNat 52)) :: (UInt256.shiftLeft (tickLogFlag r12) (UInt256.ofNat 51)) :: (UInt256.shiftLeft (tickLogFlag r13) (UInt256.ofNat 50)) :: R) mem aw rdata σ k11 C11 at rd11
  obtain ⟨k12, C12, rd12⟩ := tickLogBlock18375 (r0 := r0) (r1 := r1) (r2 := r2) (r3 := r3) (r4 := r4) (msb := msb) v (by (try simp only [List.length_cons]); omega) rd11
  change RD (deployedRuntime v) I g s0 ⟨18418⟩
    ((UInt256.shiftLeft (tickLogFlag r1) (UInt256.ofNat 62)) :: msb :: (UInt256.mul r0 r0) :: (UInt256.shiftLeft (tickLogFlag r2) (UInt256.ofNat 61)) :: (UInt256.shiftLeft (tickLogFlag r3) (UInt256.ofNat 60)) :: (UInt256.shiftLeft (tickLogFlag r4) (UInt256.ofNat 59)) :: (UInt256.shiftLeft (tickLogFlag r5) (UInt256.ofNat 58)) :: (UInt256.shiftLeft (tickLogFlag r6) (UInt256.ofNat 57)) :: (UInt256.shiftLeft (tickLogFlag r7) (UInt256.ofNat 56)) :: (UInt256.shiftLeft (tickLogFlag r8) (UInt256.ofNat 55)) :: (UInt256.shiftLeft (tickLogFlag r9) (UInt256.ofNat 54)) :: (UInt256.shiftLeft (tickLogFlag r10) (UInt256.ofNat 53)) :: (UInt256.shiftLeft (tickLogFlag r11) (UInt256.ofNat 52)) :: (UInt256.shiftLeft (tickLogFlag r12) (UInt256.ofNat 51)) :: (UInt256.shiftLeft (tickLogFlag r13) (UInt256.ofNat 50)) :: R) mem aw rdata σ k12 C12 at rd12
  obtain ⟨k13, C13, rd13⟩ := tickLogBlock18418 (r0 := r0) (r1 := r1) (r2 := r2) (r3 := r3) (r4 := r4) (r5 := r5) (msb := msb) v (by (try simp only [List.length_cons]); omega) rd12
  change RD (deployedRuntime v) I g s0 ⟨18476⟩
    ((UInt256.lor (UInt256.lor (UInt256.lor (UInt256.lor (UInt256.lor (UInt256.lor (tickPriceLogStart msb) (UInt256.shiftLeft (tickLogFlag r0) (UInt256.ofNat 63))) (UInt256.shiftLeft (tickLogFlag r1) (UInt256.ofNat 62))) (UInt256.shiftLeft (tickLogFlag r2) (UInt256.ofNat 61))) (UInt256.shiftLeft (tickLogFlag r3) (UInt256.ofNat 60))) (UInt256.shiftLeft (tickLogFlag r4) (UInt256.ofNat 59))) (UInt256.shiftLeft (tickLogFlag r5) (UInt256.ofNat 58))) :: (UInt256.shiftLeft (tickLogFlag r6) (UInt256.ofNat 57)) :: (UInt256.shiftLeft (tickLogFlag r7) (UInt256.ofNat 56)) :: (UInt256.shiftLeft (tickLogFlag r8) (UInt256.ofNat 55)) :: (UInt256.shiftLeft (tickLogFlag r9) (UInt256.ofNat 54)) :: (UInt256.shiftLeft (tickLogFlag r10) (UInt256.ofNat 53)) :: (UInt256.shiftLeft (tickLogFlag r11) (UInt256.ofNat 52)) :: (UInt256.shiftLeft (tickLogFlag r12) (UInt256.ofNat 51)) :: (UInt256.shiftLeft (tickLogFlag r13) (UInt256.ofNat 50)) :: R) mem aw rdata σ k13 C13 at rd13
  obtain ⟨k14, C14, rd14⟩ := tickLogBlock18476 (r0 := r0) (r1 := r1) (r2 := r2) (r3 := r3) (r4 := r4) (r5 := r5) (r6 := r6) (r7 := r7) (r8 := r8) (r9 := r9) (r10 := r10) (r11 := r11) (r12 := r12) (r13 := r13) v (by (try simp only [List.length_cons]); omega) rd13
  change RD (deployedRuntime v) I g s0 ⟨18536⟩
    ((UInt256.ofNat 2) :: (UInt256.sar (UInt256.ofNat 128) ((UInt256.mul (UInt256.ofNat 255738958999603826347141) (UInt256.lor (UInt256.lor (UInt256.lor (UInt256.lor (UInt256.lor (UInt256.lor (UInt256.lor (UInt256.lor (UInt256.lor (UInt256.lor (UInt256.lor (UInt256.lor (UInt256.lor (UInt256.lor (tickPriceLogStart msb) (UInt256.shiftLeft (tickLogFlag r0) (UInt256.ofNat 63))) (UInt256.shiftLeft (tickLogFlag r1) (UInt256.ofNat 62))) (UInt256.shiftLeft (tickLogFlag r2) (UInt256.ofNat 61))) (UInt256.shiftLeft (tickLogFlag r3) (UInt256.ofNat 60))) (UInt256.shiftLeft (tickLogFlag r4) (UInt256.ofNat 59))) (UInt256.shiftLeft (tickLogFlag r5) (UInt256.ofNat 58))) (UInt256.shiftLeft (tickLogFlag r6) (UInt256.ofNat 57))) (UInt256.shiftLeft (tickLogFlag r7) (UInt256.ofNat 56))) (UInt256.shiftLeft (tickLogFlag r8) (UInt256.ofNat 55))) (UInt256.shiftLeft (tickLogFlag r9) (UInt256.ofNat 54))) (UInt256.shiftLeft (tickLogFlag r10) (UInt256.ofNat 53))) (UInt256.shiftLeft (tickLogFlag r11) (UInt256.ofNat 52))) (UInt256.shiftLeft (tickLogFlag r12) (UInt256.ofNat 51))) (UInt256.shiftLeft (tickLogFlag r13) (UInt256.ofNat 50)))) + (UInt256.ofNat 115792089237316195423570985008687907853266581672683754907038987867812469392726))) :: (UInt256.mul (UInt256.ofNat 255738958999603826347141) (UInt256.lor (UInt256.lor (UInt256.lor (UInt256.lor (UInt256.lor (UInt256.lor (UInt256.lor (UInt256.lor (UInt256.lor (UInt256.lor (UInt256.lor (UInt256.lor (UInt256.lor (UInt256.lor (tickPriceLogStart msb) (UInt256.shiftLeft (tickLogFlag r0) (UInt256.ofNat 63))) (UInt256.shiftLeft (tickLogFlag r1) (UInt256.ofNat 62))) (UInt256.shiftLeft (tickLogFlag r2) (UInt256.ofNat 61))) (UInt256.shiftLeft (tickLogFlag r3) (UInt256.ofNat 60))) (UInt256.shiftLeft (tickLogFlag r4) (UInt256.ofNat 59))) (UInt256.shiftLeft (tickLogFlag r5) (UInt256.ofNat 58))) (UInt256.shiftLeft (tickLogFlag r6) (UInt256.ofNat 57))) (UInt256.shiftLeft (tickLogFlag r7) (UInt256.ofNat 56))) (UInt256.shiftLeft (tickLogFlag r8) (UInt256.ofNat 55))) (UInt256.shiftLeft (tickLogFlag r9) (UInt256.ofNat 54))) (UInt256.shiftLeft (tickLogFlag r10) (UInt256.ofNat 53))) (UInt256.shiftLeft (tickLogFlag r11) (UInt256.ofNat 52))) (UInt256.shiftLeft (tickLogFlag r12) (UInt256.ofNat 51))) (UInt256.shiftLeft (tickLogFlag r13) (UInt256.ofNat 50)))) :: R) mem aw rdata σ k14 C14 at rd14
  have hlog := tickLogStages_unroll (tickPriceLogStart msb) r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
  change (tickLogStages r (tickPriceLogStart msb) tickLogStageData).2 = _ at hlog
  simp only [← hlog] at rd14
  generalize he : (tickLogStages r (tickPriceLogStart msb) tickLogStageData).2 = log2 at rd14 ⊢
  simp only [u256_mul_comm (UInt256.ofNat 255738958999603826347141)] at rd14
  have hlow := tickPriceLowRaw_compiled log2
  simp only [tickPriceScaled] at hlow
  rw [hlow] at rd14
  exact ⟨_, _, rd14⟩

end Benchmarks.UniswapV4PoolManager
