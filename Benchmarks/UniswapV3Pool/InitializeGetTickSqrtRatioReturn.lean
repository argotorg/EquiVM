import Benchmarks.UniswapV3Pool.InitializeGetTickSqrtRatioBitsHigh

open Solm ABI Ethereum Ethereum.EVM Benchmarks.UniswapV3Pool.Immutables
open Reasoning.Theory Reasoning.Reach

namespace Benchmarks.UniswapV3Pool

def getSqrtRatioTickPosWord (tick : UInt256) : UInt256 :=
  UInt256.sgt (getSqrtRatioTickInt24Word tick) ⟨0⟩

def getSqrtRatioMaxUintWord : UInt256 :=
  UInt256.lnot (⟨0⟩ : UInt256)

def getSqrtRatioInvertedWord (ratio : UInt256) : UInt256 :=
  UInt256.div getSqrtRatioMaxUintWord ratio

def getSqrtRatioRoundBaseWord : UInt256 :=
  ⟨4294967296⟩

def getSqrtRatioRemainderWord (ratio : UInt256) : UInt256 :=
  UInt256.mod ratio getSqrtRatioRoundBaseWord

def getSqrtRatioRoundUpFlagWord (ratio : UInt256) : UInt256 :=
  UInt256.isZero (UInt256.isZero (getSqrtRatioRemainderWord ratio))

def getSqrtRatioReturnAddWord (ratio : UInt256) : UInt256 :=
  UInt256.land ⟨255⟩ (getSqrtRatioRoundUpFlagWord ratio)

def getSqrtRatioReturnWord (ratio : UInt256) : UInt256 :=
  UInt256.shiftRight ratio ⟨32⟩ + getSqrtRatioReturnAddWord ratio

def getSqrtRatioFinalRatioWord (tick ratio : UInt256) : UInt256 :=
  if getSqrtRatioTickPosWord tick = ⟨0⟩ then ratio else getSqrtRatioInvertedWord ratio

def getSqrtRatioTailReturnWord (tick ratio : UInt256) : UInt256 :=
  getSqrtRatioReturnWord (getSqrtRatioFinalRatioWord tick ratio)

def getSqrtRatioAfterBit2048BranchWord (absTick ratio : UInt256) : UInt256 :=
  if getSqrtRatioBit2048Word absTick = ⟨0⟩ then ratio
  else getSqrtRatioAfterBit2048Word ratio

def getSqrtRatioAfterBit4096BranchWord (absTick ratio : UInt256) : UInt256 :=
  if getSqrtRatioBit4096Word absTick = ⟨0⟩ then ratio
  else getSqrtRatioAfterBit4096Word ratio

def getSqrtRatioAfterBit8192BranchWord (absTick ratio : UInt256) : UInt256 :=
  if getSqrtRatioBit8192Word absTick = ⟨0⟩ then ratio
  else getSqrtRatioAfterBit8192Word ratio

def getSqrtRatioAfterBit16384BranchWord (absTick ratio : UInt256) : UInt256 :=
  if getSqrtRatioBit16384Word absTick = ⟨0⟩ then ratio
  else getSqrtRatioAfterBit16384Word ratio

def getSqrtRatioAfterBit32768BranchWord (absTick ratio : UInt256) : UInt256 :=
  if getSqrtRatioBit32768Word absTick = ⟨0⟩ then ratio
  else getSqrtRatioAfterBit32768Word ratio

def getSqrtRatioAfterBit65536BranchWord (absTick ratio : UInt256) : UInt256 :=
  if getSqrtRatioBit65536Word absTick = ⟨0⟩ then ratio
  else getSqrtRatioAfterBit65536Word ratio

def getSqrtRatioAfterBit131072BranchWord (absTick ratio : UInt256) : UInt256 :=
  if getSqrtRatioBit131072Word absTick = ⟨0⟩ then ratio
  else getSqrtRatioAfterBit131072Word ratio

def getSqrtRatioAfterBit262144BranchWord (absTick ratio : UInt256) : UInt256 :=
  if getSqrtRatioBit262144Word absTick = ⟨0⟩ then ratio
  else getSqrtRatioAfterBit262144Word ratio

def getSqrtRatioAfterBit524288BranchWord (absTick ratio : UInt256) : UInt256 :=
  if getSqrtRatioBit524288Word absTick = ⟨0⟩ then ratio
  else getSqrtRatioAfterBit524288Word ratio

def getSqrtRatioAfterHighBitsWord (absTick ratio : UInt256) : UInt256 :=
  let r2048 := getSqrtRatioAfterBit2048BranchWord absTick ratio
  let r4096 := getSqrtRatioAfterBit4096BranchWord absTick r2048
  let r8192 := getSqrtRatioAfterBit8192BranchWord absTick r4096
  let r16384 := getSqrtRatioAfterBit16384BranchWord absTick r8192
  let r32768 := getSqrtRatioAfterBit32768BranchWord absTick r16384
  let r65536 := getSqrtRatioAfterBit65536BranchWord absTick r32768
  let r131072 := getSqrtRatioAfterBit131072BranchWord absTick r65536
  let r262144 := getSqrtRatioAfterBit262144BranchWord absTick r131072
  getSqrtRatioAfterBit524288BranchWord absTick r262144

private theorem uniswapV3PoolInitializePatchPreservesJumpDest12402 :
    D_J_auxPreservesTargetBool uniswapV3PoolBytecode uniswapV3PoolPatchOffsets
      ⟨12402⟩ 0 = true := by
  native_decide

private theorem uniswapV3PoolInitializePatchPreservesJumpDest12406 :
    D_J_auxPreservesTargetBool uniswapV3PoolBytecode uniswapV3PoolPatchOffsets
      ⟨12406⟩ 0 = true := by
  native_decide

private theorem uniswapV3PoolInitializePatchPreservesJumpDest12426 :
    D_J_auxPreservesTargetBool uniswapV3PoolBytecode uniswapV3PoolPatchOffsets
      ⟨12426⟩ 0 = true := by
  native_decide

private theorem uniswapV3PoolInitializePatchPreservesJumpDest12429 :
    D_J_auxPreservesTargetBool uniswapV3PoolBytecode uniswapV3PoolPatchOffsets
      ⟨12429⟩ 0 = true := by
  native_decide

private theorem uniswapV3PoolInitializePatchPreservesJumpDest14758 :
    D_J_auxPreservesTargetBool uniswapV3PoolBytecode uniswapV3PoolPatchOffsets
      ⟨14758⟩ 0 = true := by
  native_decide

theorem uniswapV3PoolJumpDestPatched12402 {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    (D_J code 0).contains ⟨12402⟩ = true := by
  exact D_J_aux_contains_of_patchRuntime_preservesTarget hpatch
    (uniswapV3PoolPatchOffsetMem v)
    uniswapV3PoolInitializePatchPreservesJumpDest12402

theorem uniswapV3PoolJumpDestPatched12406 {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    (D_J code 0).contains ⟨12406⟩ = true := by
  exact D_J_aux_contains_of_patchRuntime_preservesTarget hpatch
    (uniswapV3PoolPatchOffsetMem v)
    uniswapV3PoolInitializePatchPreservesJumpDest12406

theorem uniswapV3PoolJumpDestPatched12426 {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    (D_J code 0).contains ⟨12426⟩ = true := by
  exact D_J_aux_contains_of_patchRuntime_preservesTarget hpatch
    (uniswapV3PoolPatchOffsetMem v)
    uniswapV3PoolInitializePatchPreservesJumpDest12426

theorem uniswapV3PoolJumpDestPatched12429 {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    (D_J code 0).contains ⟨12429⟩ = true := by
  exact D_J_aux_contains_of_patchRuntime_preservesTarget hpatch
    (uniswapV3PoolPatchOffsetMem v)
    uniswapV3PoolInitializePatchPreservesJumpDest12429

theorem uniswapV3PoolJumpDestPatched14758 {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    (D_J code 0).contains ⟨14758⟩ = true := by
  exact D_J_aux_contains_of_patchRuntime_preservesTarget hpatch
    (uniswapV3PoolPatchOffsetMem v)
    uniswapV3PoolInitializePatchPreservesJumpDest14758

-- LIBRARY CANDIDATE: fills the missing generic `RD` wrapper for EVM `MOD`.
private theorem getSqrtRatioModXstep {s : State} {code : ByteArray}
    {pcv a b : UInt256} {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pcv)
    (hdec : decode code pcv = some (.MOD, .none))
    (hstk : s.machineState.stack = a :: b :: t) (hov : t.length + 1 ≤ 1024) :
    Xstep (D_J code 0) s
      = (if s.machineState.gasAvailable.toNat < 5 then .error .OutOfGass
         else .ok (stBinop5 s (UInt256.mod a b) t, .none)) := by
  have hd : decode s.executionEnv.code s.machineState.pc = some (.MOD, .none) := by
    rw [hcode, hpc]
    exact hdec
  rw [← hcode, step_mod s hd, hstk]
  have hov' : ¬ ((a :: b :: t).length - 2 + 1 > 1024) := by
    simp only [List.length_cons]
    omega
  simp only [if_neg hov', GasConstants.Glow, stBinop5]

-- LIBRARY CANDIDATE: fills the missing generic `RD` wrapper for EVM `MOD`.
private theorem getSqrtRatioRDMod {code : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {pc : UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : ℕ} {a b : UInt256} {t : List UInt256}
    (h : RD code ee g s0 pc (a :: b :: t) mem aw rdata acc k C)
    (hdec : decode code pc = some (.MOD, .none)) (hov : t.length + 1 ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩) (UInt256.mod a b :: t) mem aw rdata acc
      (k + 1) (C + 5) := by
  unfold RD at h ⊢
  rcases h with hoog | ⟨s, hX, hcode, hpc, hstk, hgas, hk, hC, hmem, haw, hrdata, hacc,
    hee, hworld⟩
  · exact Or.inl hoog
  · have st := getSqrtRatioModXstep hcode hpc hdec hstk hov
    by_cases gg : g.toNat < C + 5
    · exact Or.inl (hX.trans (stepOOG hgas st hk hC (by omega)))
    · refine Or.inr ⟨stBinop5 s (UInt256.mod a b) t,
        hX.trans (stepContinue hgas st hk (Nat.not_lt.mp gg)), ?_, ?_, ?_, ?_,
        by omega, by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [stBinop5]; exact hcode
      · simp only [stBinop5]; rw [hpc]
      · rfl
      · simp only [stBinop5]; rw [hgas, Sat256.subNat_sub_add_of_sub_sub]
      · simp only [stBinop5]; exact hmem
      · simp only [stBinop5]; exact haw
      · simp only [stBinop5]; exact hrdata
      · simp only [stBinop5]; exact hacc
      · exact hee
      · exact hworld

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem uniswapV3PoolGetSqrtRatioAtTickHighBits {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {ratio absTick tick ret : UInt256} {R : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨12094⟩ (ratio :: absTick :: ⟨0⟩ :: tick :: ret :: R)
      mem aw rdata acc k C)
    (hov : R.length + 7 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨12379⟩
      (getSqrtRatioAfterHighBitsWord absTick ratio :: absTick :: ⟨0⟩ :: tick :: ret :: R)
      mem aw rdata acc k' C' := by
  let r2048 := getSqrtRatioAfterBit2048BranchWord absTick ratio
  have h2048 : ∃ k' C', RD code ee g s0 ⟨12126⟩
      (r2048 :: absTick :: ⟨0⟩ :: tick :: ret :: R) mem aw rdata acc k' C' := by
    by_cases hbit : getSqrtRatioBit2048Word absTick = ⟨0⟩
    · obtain ⟨_, _, hnext⟩ :=
        uniswapV3PoolGetSqrtRatioAtTickBit2048Zero (v := v) (code := code)
          (ee := ee) (g := g) (s0 := s0) (ratio := ratio) (absTick := absTick)
          (tick := tick) (ret := ret) (R := R) (mem := mem) (aw := aw)
          (rdata := rdata) (acc := acc) hpatch h hbit hov
      exact ⟨_, _, by
        simpa [r2048, getSqrtRatioAfterBit2048BranchWord, hbit] using hnext⟩
    · obtain ⟨_, _, hnext⟩ :=
        uniswapV3PoolGetSqrtRatioAtTickBit2048Set (v := v) (code := code)
          (ee := ee) (g := g) (s0 := s0) (ratio := ratio) (absTick := absTick)
          (tick := tick) (ret := ret) (R := R) (mem := mem) (aw := aw)
          (rdata := rdata) (acc := acc) hpatch h hbit hov
      exact ⟨_, _, by
        simpa [r2048, getSqrtRatioAfterBit2048BranchWord, hbit] using hnext⟩
  obtain ⟨_, _, h2048⟩ := h2048
  let r4096 := getSqrtRatioAfterBit4096BranchWord absTick r2048
  have h4096 : ∃ k' C', RD code ee g s0 ⟨12158⟩
      (r4096 :: absTick :: ⟨0⟩ :: tick :: ret :: R) mem aw rdata acc k' C' := by
    by_cases hbit : getSqrtRatioBit4096Word absTick = ⟨0⟩
    · obtain ⟨_, _, hnext⟩ :=
        uniswapV3PoolGetSqrtRatioAtTickBit4096Zero (v := v) (code := code)
          (ee := ee) (g := g) (s0 := s0) (ratio := r2048) (absTick := absTick)
          (tick := tick) (ret := ret) (R := R) (mem := mem) (aw := aw)
          (rdata := rdata) (acc := acc) hpatch h2048 hbit hov
      exact ⟨_, _, by
        simpa [r4096, getSqrtRatioAfterBit4096BranchWord, hbit] using hnext⟩
    · obtain ⟨_, _, hnext⟩ :=
        uniswapV3PoolGetSqrtRatioAtTickBit4096Set (v := v) (code := code)
          (ee := ee) (g := g) (s0 := s0) (ratio := r2048) (absTick := absTick)
          (tick := tick) (ret := ret) (R := R) (mem := mem) (aw := aw)
          (rdata := rdata) (acc := acc) hpatch h2048 hbit hov
      exact ⟨_, _, by
        simpa [r4096, getSqrtRatioAfterBit4096BranchWord, hbit] using hnext⟩
  obtain ⟨_, _, h4096⟩ := h4096
  let r8192 := getSqrtRatioAfterBit8192BranchWord absTick r4096
  have h8192 : ∃ k' C', RD code ee g s0 ⟨12190⟩
      (r8192 :: absTick :: ⟨0⟩ :: tick :: ret :: R) mem aw rdata acc k' C' := by
    by_cases hbit : getSqrtRatioBit8192Word absTick = ⟨0⟩
    · obtain ⟨_, _, hnext⟩ :=
        uniswapV3PoolGetSqrtRatioAtTickBit8192Zero (v := v) (code := code)
          (ee := ee) (g := g) (s0 := s0) (ratio := r4096) (absTick := absTick)
          (tick := tick) (ret := ret) (R := R) (mem := mem) (aw := aw)
          (rdata := rdata) (acc := acc) hpatch h4096 hbit hov
      exact ⟨_, _, by
        simpa [r8192, getSqrtRatioAfterBit8192BranchWord, hbit] using hnext⟩
    · obtain ⟨_, _, hnext⟩ :=
        uniswapV3PoolGetSqrtRatioAtTickBit8192Set (v := v) (code := code)
          (ee := ee) (g := g) (s0 := s0) (ratio := r4096) (absTick := absTick)
          (tick := tick) (ret := ret) (R := R) (mem := mem) (aw := aw)
          (rdata := rdata) (acc := acc) hpatch h4096 hbit hov
      exact ⟨_, _, by
        simpa [r8192, getSqrtRatioAfterBit8192BranchWord, hbit] using hnext⟩
  obtain ⟨_, _, h8192⟩ := h8192
  let r16384 := getSqrtRatioAfterBit16384BranchWord absTick r8192
  have h16384 : ∃ k' C', RD code ee g s0 ⟨12222⟩
      (r16384 :: absTick :: ⟨0⟩ :: tick :: ret :: R) mem aw rdata acc k' C' := by
    by_cases hbit : getSqrtRatioBit16384Word absTick = ⟨0⟩
    · obtain ⟨_, _, hnext⟩ :=
        uniswapV3PoolGetSqrtRatioAtTickBit16384Zero (v := v) (code := code)
          (ee := ee) (g := g) (s0 := s0) (ratio := r8192) (absTick := absTick)
          (tick := tick) (ret := ret) (R := R) (mem := mem) (aw := aw)
          (rdata := rdata) (acc := acc) hpatch h8192 hbit hov
      exact ⟨_, _, by
        simpa [r16384, getSqrtRatioAfterBit16384BranchWord, hbit] using hnext⟩
    · obtain ⟨_, _, hnext⟩ :=
        uniswapV3PoolGetSqrtRatioAtTickBit16384Set (v := v) (code := code)
          (ee := ee) (g := g) (s0 := s0) (ratio := r8192) (absTick := absTick)
          (tick := tick) (ret := ret) (R := R) (mem := mem) (aw := aw)
          (rdata := rdata) (acc := acc) hpatch h8192 hbit hov
      exact ⟨_, _, by
        simpa [r16384, getSqrtRatioAfterBit16384BranchWord, hbit] using hnext⟩
  obtain ⟨_, _, h16384⟩ := h16384
  let r32768 := getSqrtRatioAfterBit32768BranchWord absTick r16384
  have h32768 : ∃ k' C', RD code ee g s0 ⟨12254⟩
      (r32768 :: absTick :: ⟨0⟩ :: tick :: ret :: R) mem aw rdata acc k' C' := by
    by_cases hbit : getSqrtRatioBit32768Word absTick = ⟨0⟩
    · obtain ⟨_, _, hnext⟩ :=
        uniswapV3PoolGetSqrtRatioAtTickBit32768Zero (v := v) (code := code)
          (ee := ee) (g := g) (s0 := s0) (ratio := r16384) (absTick := absTick)
          (tick := tick) (ret := ret) (R := R) (mem := mem) (aw := aw)
          (rdata := rdata) (acc := acc) hpatch h16384 hbit hov
      exact ⟨_, _, by
        simpa [r32768, getSqrtRatioAfterBit32768BranchWord, hbit] using hnext⟩
    · obtain ⟨_, _, hnext⟩ :=
        uniswapV3PoolGetSqrtRatioAtTickBit32768Set (v := v) (code := code)
          (ee := ee) (g := g) (s0 := s0) (ratio := r16384) (absTick := absTick)
          (tick := tick) (ret := ret) (R := R) (mem := mem) (aw := aw)
          (rdata := rdata) (acc := acc) hpatch h16384 hbit hov
      exact ⟨_, _, by
        simpa [r32768, getSqrtRatioAfterBit32768BranchWord, hbit] using hnext⟩
  obtain ⟨_, _, h32768⟩ := h32768
  let r65536 := getSqrtRatioAfterBit65536BranchWord absTick r32768
  have h65536 : ∃ k' C', RD code ee g s0 ⟨12287⟩
      (r65536 :: absTick :: ⟨0⟩ :: tick :: ret :: R) mem aw rdata acc k' C' := by
    by_cases hbit : getSqrtRatioBit65536Word absTick = ⟨0⟩
    · obtain ⟨_, _, hnext⟩ :=
        uniswapV3PoolGetSqrtRatioAtTickBit65536Zero (v := v) (code := code)
          (ee := ee) (g := g) (s0 := s0) (ratio := r32768) (absTick := absTick)
          (tick := tick) (ret := ret) (R := R) (mem := mem) (aw := aw)
          (rdata := rdata) (acc := acc) hpatch h32768 hbit hov
      exact ⟨_, _, by
        simpa [r65536, getSqrtRatioAfterBit65536BranchWord, hbit] using hnext⟩
    · obtain ⟨_, _, hnext⟩ :=
        uniswapV3PoolGetSqrtRatioAtTickBit65536Set (v := v) (code := code)
          (ee := ee) (g := g) (s0 := s0) (ratio := r32768) (absTick := absTick)
          (tick := tick) (ret := ret) (R := R) (mem := mem) (aw := aw)
          (rdata := rdata) (acc := acc) hpatch h32768 hbit hov
      exact ⟨_, _, by
        simpa [r65536, getSqrtRatioAfterBit65536BranchWord, hbit] using hnext⟩
  obtain ⟨_, _, h65536⟩ := h65536
  let r131072 := getSqrtRatioAfterBit131072BranchWord absTick r65536
  have h131072 : ∃ k' C', RD code ee g s0 ⟨12319⟩
      (r131072 :: absTick :: ⟨0⟩ :: tick :: ret :: R) mem aw rdata acc k' C' := by
    by_cases hbit : getSqrtRatioBit131072Word absTick = ⟨0⟩
    · obtain ⟨_, _, hnext⟩ :=
        uniswapV3PoolGetSqrtRatioAtTickBit131072Zero (v := v) (code := code)
          (ee := ee) (g := g) (s0 := s0) (ratio := r65536) (absTick := absTick)
          (tick := tick) (ret := ret) (R := R) (mem := mem) (aw := aw)
          (rdata := rdata) (acc := acc) hpatch h65536 hbit hov
      exact ⟨_, _, by
        simpa [r131072, getSqrtRatioAfterBit131072BranchWord, hbit] using hnext⟩
    · obtain ⟨_, _, hnext⟩ :=
        uniswapV3PoolGetSqrtRatioAtTickBit131072Set (v := v) (code := code)
          (ee := ee) (g := g) (s0 := s0) (ratio := r65536) (absTick := absTick)
          (tick := tick) (ret := ret) (R := R) (mem := mem) (aw := aw)
          (rdata := rdata) (acc := acc) hpatch h65536 hbit hov
      exact ⟨_, _, by
        simpa [r131072, getSqrtRatioAfterBit131072BranchWord, hbit] using hnext⟩
  obtain ⟨_, _, h131072⟩ := h131072
  let r262144 := getSqrtRatioAfterBit262144BranchWord absTick r131072
  have h262144 : ∃ k' C', RD code ee g s0 ⟨12350⟩
      (r262144 :: absTick :: ⟨0⟩ :: tick :: ret :: R) mem aw rdata acc k' C' := by
    by_cases hbit : getSqrtRatioBit262144Word absTick = ⟨0⟩
    · obtain ⟨_, _, hnext⟩ :=
        uniswapV3PoolGetSqrtRatioAtTickBit262144Zero (v := v) (code := code)
          (ee := ee) (g := g) (s0 := s0) (ratio := r131072) (absTick := absTick)
          (tick := tick) (ret := ret) (R := R) (mem := mem) (aw := aw)
          (rdata := rdata) (acc := acc) hpatch h131072 hbit hov
      exact ⟨_, _, by
        simpa [r262144, getSqrtRatioAfterBit262144BranchWord, hbit] using hnext⟩
    · obtain ⟨_, _, hnext⟩ :=
        uniswapV3PoolGetSqrtRatioAtTickBit262144Set (v := v) (code := code)
          (ee := ee) (g := g) (s0 := s0) (ratio := r131072) (absTick := absTick)
          (tick := tick) (ret := ret) (R := R) (mem := mem) (aw := aw)
          (rdata := rdata) (acc := acc) hpatch h131072 hbit hov
      exact ⟨_, _, by
        simpa [r262144, getSqrtRatioAfterBit262144BranchWord, hbit] using hnext⟩
  obtain ⟨_, _, h262144⟩ := h262144
  let r524288 := getSqrtRatioAfterBit524288BranchWord absTick r262144
  have h524288 : ∃ k' C', RD code ee g s0 ⟨12379⟩
      (r524288 :: absTick :: ⟨0⟩ :: tick :: ret :: R) mem aw rdata acc k' C' := by
    by_cases hbit : getSqrtRatioBit524288Word absTick = ⟨0⟩
    · obtain ⟨_, _, hnext⟩ :=
        uniswapV3PoolGetSqrtRatioAtTickBit524288Zero (v := v) (code := code)
          (ee := ee) (g := g) (s0 := s0) (ratio := r262144) (absTick := absTick)
          (tick := tick) (ret := ret) (R := R) (mem := mem) (aw := aw)
          (rdata := rdata) (acc := acc) hpatch h262144 hbit hov
      exact ⟨_, _, by
        simpa [r524288, getSqrtRatioAfterBit524288BranchWord, hbit] using hnext⟩
    · obtain ⟨_, _, hnext⟩ :=
        uniswapV3PoolGetSqrtRatioAtTickBit524288Set (v := v) (code := code)
          (ee := ee) (g := g) (s0 := s0) (ratio := r262144) (absTick := absTick)
          (tick := tick) (ret := ret) (R := R) (mem := mem) (aw := aw)
          (rdata := rdata) (acc := acc) hpatch h262144 hbit hov
      exact ⟨_, _, by
        simpa [r524288, getSqrtRatioAfterBit524288BranchWord, hbit] using hnext⟩
  obtain ⟨_, _, h524288⟩ := h524288
  exact ⟨_, _, by
    simpa [getSqrtRatioAfterHighBitsWord, r2048, r4096, r8192, r16384, r32768,
      r65536, r131072, r262144, r524288] using h524288⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem uniswapV3PoolGetSqrtRatioAtTickTickNonPos {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {ratio absTick tick ret : UInt256} {R : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨12379⟩ (ratio :: absTick :: ⟨0⟩ :: tick :: ret :: R)
      mem aw rdata acc k C)
    (hpos : getSqrtRatioTickPosWord tick = ⟨0⟩)
    (hov : R.length + 8 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨12406⟩ (ratio :: absTick :: ⟨0⟩ :: tick :: ret :: R)
      mem aw rdata acc k' C' := by
  have hdecode {pc : UInt256} (hlo : 11629 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 13989) :
      decode code pc = decode uniswapV3PoolBytecode pc := by
    rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by
        have hsize : 13989 ≤ uniswapV3PoolBytecode.size := by native_decide
        omega)
      (uniswapV3PoolInitializePatchDisjointGetSqrtRatioAtTick hlo hhi)]
  have hd12379 : decode code ⟨12379⟩ = some (.JUMPDEST, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12380 : decode code ⟨12380⟩ = some (.Push .PUSH1, some (⟨0⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12382 : decode code ⟨12382⟩ = some (.DUP5, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12383 : decode code ⟨12383⟩ = some (.Push .PUSH1, some (⟨2⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12385 : decode code ⟨12385⟩ = some (.SIGNEXTEND, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12386 : decode code ⟨12386⟩ = some (.SGT, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12387 : decode code ⟨12387⟩ = some (.ISZERO, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12388 : decode code ⟨12388⟩ = some (.Push .PUSH2, some (⟨12406⟩, 2)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12391 : decode code ⟨12391⟩ = some (.JUMPI, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hcond : UInt256.isZero (getSqrtRatioTickPosWord tick) ≠ ⟨0⟩ := by
    rw [hpos]
    native_decide
  have rd12380 := by
    simpa using h.jumpdest hd12379 (by
      simp only [List.length_cons]
      omega)
  have rd12382 := by
    simpa using rd12380.push1 ⟨0⟩ hd12380 (by
      simp only [List.length_cons]
      omega)
  have rd12383 := by
    simpa using RD.dup5 rd12382 hd12382 (by
      simp only [List.length_cons]
      omega)
  have rd12385 := by
    simpa using rd12383.push1 ⟨2⟩ hd12383 (by
      simp only [List.length_cons]
      omega)
  have rd12386 := by
    simpa [getSqrtRatioTickInt24Word] using RD.signextend rd12385 hd12385 (by
      simp only [List.length_cons]
      omega)
  have rd12387 := by
    simpa [getSqrtRatioTickPosWord] using rd12386.sgt hd12386 (by
      simp only [List.length_cons]
      omega)
  have rd12388 := by
    simpa using rd12387.iszero hd12387 (by
      simp only [List.length_cons]
      omega)
  have rd12391 := by
    simpa using rd12388.push2 ⟨12406⟩ hd12388 (by
      simp only [List.length_cons]
      omega)
  exact ⟨_, _, rd12391.jumpiT hd12391 hcond
    (uniswapV3PoolJumpDestPatched12406 hpatch) (by
      simp only [List.length_cons]
      omega)⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem uniswapV3PoolGetSqrtRatioAtTickTickPos {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {ratio absTick tick ret : UInt256} {R : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨12379⟩ (ratio :: absTick :: ⟨0⟩ :: tick :: ret :: R)
      mem aw rdata acc k C)
    (hpos : getSqrtRatioTickPosWord tick ≠ ⟨0⟩)
    (hratio : ratio ≠ ⟨0⟩)
    (hov : R.length + 9 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨12406⟩
      (getSqrtRatioInvertedWord ratio :: absTick :: ⟨0⟩ :: tick :: ret :: R)
      mem aw rdata acc k' C' := by
  have hdecode {pc : UInt256} (hlo : 11629 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 13989) :
      decode code pc = decode uniswapV3PoolBytecode pc := by
    rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by
        have hsize : 13989 ≤ uniswapV3PoolBytecode.size := by native_decide
        omega)
      (uniswapV3PoolInitializePatchDisjointGetSqrtRatioAtTick hlo hhi)]
  have hd12379 : decode code ⟨12379⟩ = some (.JUMPDEST, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12380 : decode code ⟨12380⟩ = some (.Push .PUSH1, some (⟨0⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12382 : decode code ⟨12382⟩ = some (.DUP5, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12383 : decode code ⟨12383⟩ = some (.Push .PUSH1, some (⟨2⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12385 : decode code ⟨12385⟩ = some (.SIGNEXTEND, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12386 : decode code ⟨12386⟩ = some (.SGT, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12387 : decode code ⟨12387⟩ = some (.ISZERO, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12388 : decode code ⟨12388⟩ = some (.Push .PUSH2, some (⟨12406⟩, 2)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12391 : decode code ⟨12391⟩ = some (.JUMPI, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12392 : decode code ⟨12392⟩ = some (.DUP1, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12393 : decode code ⟨12393⟩ = some (.Push .PUSH1, some (⟨0⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12395 : decode code ⟨12395⟩ = some (.NOT, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12396 : decode code ⟨12396⟩ = some (.DUP2, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12397 : decode code ⟨12397⟩ = some (.Push .PUSH2, some (⟨12402⟩, 2)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12400 : decode code ⟨12400⟩ = some (.JUMPI, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12402 : decode code ⟨12402⟩ = some (.JUMPDEST, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12403 : decode code ⟨12403⟩ = some (.DIV, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12404 : decode code ⟨12404⟩ = some (.SWAP1, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12405 : decode code ⟨12405⟩ = some (.POP, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hskip : UInt256.isZero (getSqrtRatioTickPosWord tick) = ⟨0⟩ :=
    isZero_eq_zero_of_ne hpos
  have rd12380 := by
    simpa using h.jumpdest hd12379 (by
      simp only [List.length_cons]
      omega)
  have rd12382 := by
    simpa using rd12380.push1 ⟨0⟩ hd12380 (by
      simp only [List.length_cons]
      omega)
  have rd12383 := by
    simpa using RD.dup5 rd12382 hd12382 (by
      simp only [List.length_cons]
      omega)
  have rd12385 := by
    simpa using rd12383.push1 ⟨2⟩ hd12383 (by
      simp only [List.length_cons]
      omega)
  have rd12386 := by
    simpa [getSqrtRatioTickInt24Word] using RD.signextend rd12385 hd12385 (by
      simp only [List.length_cons]
      omega)
  have rd12387 := by
    simpa [getSqrtRatioTickPosWord] using rd12386.sgt hd12386 (by
      simp only [List.length_cons]
      omega)
  have rd12388 := by
    simpa using rd12387.iszero hd12387 (by
      simp only [List.length_cons]
      omega)
  have rd12391 := by
    simpa using rd12388.push2 ⟨12406⟩ hd12388 (by
      simp only [List.length_cons]
      omega)
  have rd12392 := rd12391.jumpiNT hd12391 hskip (by
    simp only [List.length_cons]
    omega)
  have rd12393 := by
    simpa using rd12392.dup1 hd12392 (by
      simp only [List.length_cons]
      omega)
  have rd12395 := by
    simpa using rd12393.push1 ⟨0⟩ hd12393 (by
      simp only [List.length_cons]
      omega)
  have rd12396 := by
    simpa [getSqrtRatioMaxUintWord] using rd12395.not hd12395 (by
      simp only [List.length_cons]
      omega)
  have rd12397 := by
    simpa using rd12396.dup2 hd12396 (by
      simp only [List.length_cons]
      omega)
  have rd12400 := by
    simpa using rd12397.push2 ⟨12402⟩ hd12397 (by
      simp only [List.length_cons]
      omega)
  have rd12402 := rd12400.jumpiT hd12400 hratio
    (uniswapV3PoolJumpDestPatched12402 hpatch) (by
      simp only [List.length_cons]
      omega)
  have rd12403 := by
    simpa using rd12402.jumpdest hd12402 (by
      simp only [List.length_cons]
      omega)
  have rd12404 := by
    simpa [getSqrtRatioInvertedWord, getSqrtRatioMaxUintWord] using
      rd12403.div hd12403 (by
        simp only [List.length_cons]
        omega)
  have rd12405 := by
    simpa using rd12404.swap1 hd12404 (by
      simp only [List.length_cons]
      omega)
  have rd12406 := by
    simpa using rd12405.pop hd12405 (by
      simp only [List.length_cons]
      omega)
  exact ⟨_, _, by simpa using rd12406⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem uniswapV3PoolGetSqrtRatioAtTickReturnRemainderZero {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {ratio absTick tick ret : UInt256} {R : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨12406⟩ (ratio :: absTick :: ⟨0⟩ :: tick :: ret :: R)
      mem aw rdata acc k C)
    (hrem : getSqrtRatioRemainderWord ratio = ⟨0⟩)
    (hret : (D_J code 0).contains ret = true)
    (hov : R.length + 8 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ret (getSqrtRatioReturnWord ratio :: R)
      mem aw rdata acc k' C' := by
  have hdecode {pc : UInt256} (hlo : 11629 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 13989) :
      decode code pc = decode uniswapV3PoolBytecode pc := by
    rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by
        have hsize : 13989 ≤ uniswapV3PoolBytecode.size := by native_decide
        omega)
      (uniswapV3PoolInitializePatchDisjointGetSqrtRatioAtTick hlo hhi)]
  have hd12406 : decode code ⟨12406⟩ = some (.JUMPDEST, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12407 : decode code ⟨12407⟩ = some (.Push .PUSH5, some (⟨4294967296⟩, 5)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12413 : decode code ⟨12413⟩ = some (.DUP2, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12414 : decode code ⟨12414⟩ = some (.MOD, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12415 : decode code ⟨12415⟩ = some (.ISZERO, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12416 : decode code ⟨12416⟩ = some (.Push .PUSH2, some (⟨12426⟩, 2)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12419 : decode code ⟨12419⟩ = some (.JUMPI, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12426 : decode code ⟨12426⟩ = some (.JUMPDEST, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12427 : decode code ⟨12427⟩ = some (.Push .PUSH1, some (⟨0⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12429 : decode code ⟨12429⟩ = some (.JUMPDEST, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12430 : decode code ⟨12430⟩ = some (.Push .PUSH1, some (⟨255⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12432 : decode code ⟨12432⟩ = some (.AND, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12433 : decode code ⟨12433⟩ = some (.Push .PUSH1, some (⟨32⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12435 : decode code ⟨12435⟩ = some (.DUP3, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12436 : decode code ⟨12436⟩ = some (.SWAP1, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12437 : decode code ⟨12437⟩ = some (.SHR, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12438 : decode code ⟨12438⟩ = some (.ADD, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12439 : decode code ⟨12439⟩ = some (.SWAP3, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12440 : decode code ⟨12440⟩ = some (.POP, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12441 : decode code ⟨12441⟩ = some (.POP, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12442 : decode code ⟨12442⟩ = some (.POP, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12443 : decode code ⟨12443⟩ = some (.SWAP2, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12444 : decode code ⟨12444⟩ = some (.SWAP1, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12445 : decode code ⟨12445⟩ = some (.POP, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12446 : decode code ⟨12446⟩ = some (.JUMP, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hcond : UInt256.isZero (getSqrtRatioRemainderWord ratio) ≠ ⟨0⟩ := by
    rw [hrem]
    native_decide
  have hround :
      UInt256.land (⟨255⟩ : UInt256) ⟨0⟩ = getSqrtRatioReturnAddWord ratio := by
    rw [getSqrtRatioReturnAddWord, getSqrtRatioRoundUpFlagWord, hrem]
    native_decide
  have rd12407 := by
    simpa using h.jumpdest hd12406 (by
      simp only [List.length_cons]
      omega)
  have rd12413 := by
    simpa [getSqrtRatioRoundBaseWord] using
      rd12407.pushConst (⟨4294967296⟩ : UInt256)
        (by native_decide : Operation.POp.PUSH5 ≠ .PUSH0) hd12407 (by
          simp only [List.length_cons]
          omega)
  have rd12414 := by
    simpa using rd12413.dup2 hd12413 (by
      simp only [List.length_cons]
      omega)
  have rd12415 := by
    simpa [getSqrtRatioRemainderWord, getSqrtRatioRoundBaseWord] using
      getSqrtRatioRDMod rd12414 hd12414 (by
        simp only [List.length_cons]
        omega)
  have rd12416 := by
    simpa using rd12415.iszero hd12415 (by
      simp only [List.length_cons]
      omega)
  have rd12419 := by
    simpa using rd12416.push2 ⟨12426⟩ hd12416 (by
      simp only [List.length_cons]
      omega)
  have rd12426 := rd12419.jumpiT hd12419 hcond
    (uniswapV3PoolJumpDestPatched12426 hpatch) (by
      simp only [List.length_cons]
      omega)
  have rd12427 := by
    simpa using rd12426.jumpdest hd12426 (by
      simp only [List.length_cons]
      omega)
  have rd12429 := by
    simpa using rd12427.push1 ⟨0⟩ hd12427 (by
      simp only [List.length_cons]
      omega)
  have rd12430 := by
    simpa using rd12429.jumpdest hd12429 (by
      simp only [List.length_cons]
      omega)
  have rd12432 := by
    simpa using rd12430.push1 ⟨255⟩ hd12430 (by
      simp only [List.length_cons]
      omega)
  have rd12433 := by
    simpa [hround] using rd12432.and hd12432 (by
      simp only [List.length_cons]
      omega)
  have rd12435 := by
    simpa using rd12433.push1 ⟨32⟩ hd12433 (by
      simp only [List.length_cons]
      omega)
  have rd12436 := by
    simpa using RD.dup3 rd12435 hd12435 (by
      simp only [List.length_cons]
      omega)
  have rd12437 := by
    simpa using rd12436.swap1 hd12436 (by
      simp only [List.length_cons]
      omega)
  have rd12438 := by
    simpa using rd12437.shr hd12437 (by
      simp only [List.length_cons]
      omega)
  have rd12439 := by
    simpa [getSqrtRatioReturnWord] using rd12438.add hd12438 (by
      simp only [List.length_cons]
      omega)
  have rd12440 := by
    simpa using RD.swap3 rd12439 hd12439 (by
      simp only [List.length_cons]
      omega)
  have rd12441 := by
    simpa using rd12440.pop hd12440 (by
      simp only [List.length_cons]
      omega)
  have rd12442 := by
    simpa using rd12441.pop hd12441 (by
      simp only [List.length_cons]
      omega)
  have rd12443 := by
    simpa using rd12442.pop hd12442 (by
      simp only [List.length_cons]
      omega)
  have rd12444 := by
    simpa using RD.swap2 rd12443 hd12443 (by
      omega)
  have rd12445 := by
    simpa using rd12444.swap1 hd12444 (by
      simp only [List.length_cons]
      omega)
  have rd12446 := by
    simpa using rd12445.pop hd12445 (by
      simp only [List.length_cons]
      omega)
  exact ⟨_, _, rd12446.jump hd12446 hret (by
    simp only [List.length_cons]
    omega)⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem uniswapV3PoolGetSqrtRatioAtTickReturnRemainderNonzero {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {ratio absTick tick ret : UInt256} {R : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨12406⟩ (ratio :: absTick :: ⟨0⟩ :: tick :: ret :: R)
      mem aw rdata acc k C)
    (hrem : getSqrtRatioRemainderWord ratio ≠ ⟨0⟩)
    (hret : (D_J code 0).contains ret = true)
    (hov : R.length + 8 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ret (getSqrtRatioReturnWord ratio :: R)
      mem aw rdata acc k' C' := by
  have hdecode {pc : UInt256} (hlo : 11629 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 13989) :
      decode code pc = decode uniswapV3PoolBytecode pc := by
    rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by
        have hsize : 13989 ≤ uniswapV3PoolBytecode.size := by native_decide
        omega)
      (uniswapV3PoolInitializePatchDisjointGetSqrtRatioAtTick hlo hhi)]
  have hd12406 : decode code ⟨12406⟩ = some (.JUMPDEST, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12407 : decode code ⟨12407⟩ = some (.Push .PUSH5, some (⟨4294967296⟩, 5)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12413 : decode code ⟨12413⟩ = some (.DUP2, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12414 : decode code ⟨12414⟩ = some (.MOD, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12415 : decode code ⟨12415⟩ = some (.ISZERO, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12416 : decode code ⟨12416⟩ = some (.Push .PUSH2, some (⟨12426⟩, 2)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12419 : decode code ⟨12419⟩ = some (.JUMPI, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12420 : decode code ⟨12420⟩ = some (.Push .PUSH1, some (⟨1⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12422 : decode code ⟨12422⟩ = some (.Push .PUSH2, some (⟨12429⟩, 2)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12425 : decode code ⟨12425⟩ = some (.JUMP, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12429 : decode code ⟨12429⟩ = some (.JUMPDEST, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12430 : decode code ⟨12430⟩ = some (.Push .PUSH1, some (⟨255⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12432 : decode code ⟨12432⟩ = some (.AND, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12433 : decode code ⟨12433⟩ = some (.Push .PUSH1, some (⟨32⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12435 : decode code ⟨12435⟩ = some (.DUP3, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12436 : decode code ⟨12436⟩ = some (.SWAP1, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12437 : decode code ⟨12437⟩ = some (.SHR, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12438 : decode code ⟨12438⟩ = some (.ADD, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12439 : decode code ⟨12439⟩ = some (.SWAP3, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12440 : decode code ⟨12440⟩ = some (.POP, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12441 : decode code ⟨12441⟩ = some (.POP, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12442 : decode code ⟨12442⟩ = some (.POP, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12443 : decode code ⟨12443⟩ = some (.SWAP2, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12444 : decode code ⟨12444⟩ = some (.SWAP1, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12445 : decode code ⟨12445⟩ = some (.POP, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd12446 : decode code ⟨12446⟩ = some (.JUMP, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hskip : UInt256.isZero (getSqrtRatioRemainderWord ratio) = ⟨0⟩ :=
    isZero_eq_zero_of_ne hrem
  have hround :
      UInt256.land (⟨255⟩ : UInt256) ⟨1⟩ = getSqrtRatioReturnAddWord ratio := by
    rw [getSqrtRatioReturnAddWord, getSqrtRatioRoundUpFlagWord, hskip]
    native_decide
  have rd12407 := by
    simpa using h.jumpdest hd12406 (by
      simp only [List.length_cons]
      omega)
  have rd12413 := by
    simpa [getSqrtRatioRoundBaseWord] using
      rd12407.pushConst (⟨4294967296⟩ : UInt256)
        (by native_decide : Operation.POp.PUSH5 ≠ .PUSH0) hd12407 (by
          simp only [List.length_cons]
          omega)
  have rd12414 := by
    simpa using rd12413.dup2 hd12413 (by
      simp only [List.length_cons]
      omega)
  have rd12415 := by
    simpa [getSqrtRatioRemainderWord, getSqrtRatioRoundBaseWord] using
      getSqrtRatioRDMod rd12414 hd12414 (by
        simp only [List.length_cons]
        omega)
  have rd12416 := by
    simpa using rd12415.iszero hd12415 (by
      simp only [List.length_cons]
      omega)
  have rd12419 := by
    simpa using rd12416.push2 ⟨12426⟩ hd12416 (by
      simp only [List.length_cons]
      omega)
  have rd12420 := rd12419.jumpiNT hd12419 hskip (by
    simp only [List.length_cons]
    omega)
  have rd12422 := by
    simpa using rd12420.push1 ⟨1⟩ hd12420 (by
      simp only [List.length_cons]
      omega)
  have rd12425 := by
    simpa using rd12422.push2 ⟨12429⟩ hd12422 (by
      simp only [List.length_cons]
      omega)
  have rd12429 := rd12425.jump hd12425
    (uniswapV3PoolJumpDestPatched12429 hpatch) (by
      simp only [List.length_cons]
      omega)
  have rd12430 := by
    simpa using rd12429.jumpdest hd12429 (by
      simp only [List.length_cons]
      omega)
  have rd12432 := by
    simpa using rd12430.push1 ⟨255⟩ hd12430 (by
      simp only [List.length_cons]
      omega)
  have rd12433 := by
    simpa [hround] using rd12432.and hd12432 (by
      simp only [List.length_cons]
      omega)
  have rd12435 := by
    simpa using rd12433.push1 ⟨32⟩ hd12433 (by
      simp only [List.length_cons]
      omega)
  have rd12436 := by
    simpa using RD.dup3 rd12435 hd12435 (by
      simp only [List.length_cons]
      omega)
  have rd12437 := by
    simpa using rd12436.swap1 hd12436 (by
      simp only [List.length_cons]
      omega)
  have rd12438 := by
    simpa using rd12437.shr hd12437 (by
      simp only [List.length_cons]
      omega)
  have rd12439 := by
    simpa [getSqrtRatioReturnWord] using rd12438.add hd12438 (by
      simp only [List.length_cons]
      omega)
  have rd12440 := by
    simpa using RD.swap3 rd12439 hd12439 (by
      simp only [List.length_cons]
      omega)
  have rd12441 := by
    simpa using rd12440.pop hd12440 (by
      simp only [List.length_cons]
      omega)
  have rd12442 := by
    simpa using rd12441.pop hd12441 (by
      simp only [List.length_cons]
      omega)
  have rd12443 := by
    simpa using rd12442.pop hd12442 (by
      simp only [List.length_cons]
      omega)
  have rd12444 := by
    simpa using RD.swap2 rd12443 hd12443 (by
      omega)
  have rd12445 := by
    simpa using rd12444.swap1 hd12444 (by
      simp only [List.length_cons]
      omega)
  have rd12446 := by
    simpa using rd12445.pop hd12445 (by
      simp only [List.length_cons]
      omega)
  exact ⟨_, _, rd12446.jump hd12446 hret (by
    simp only [List.length_cons]
    omega)⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem uniswapV3PoolGetSqrtRatioAtTickReturnTail {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {ratio absTick tick ret : UInt256} {R : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨12379⟩ (ratio :: absTick :: ⟨0⟩ :: tick :: ret :: R)
      mem aw rdata acc k C)
    (hratio : ratio ≠ ⟨0⟩)
    (hret : (D_J code 0).contains ret = true)
    (hov : R.length + 9 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ret (getSqrtRatioTailReturnWord tick ratio :: R)
      mem aw rdata acc k' C' := by
  by_cases hpos : getSqrtRatioTickPosWord tick = ⟨0⟩
  · obtain ⟨_, _, htail⟩ :=
      uniswapV3PoolGetSqrtRatioAtTickTickNonPos (v := v) (code := code)
        (ee := ee) (g := g) (s0 := s0) (ratio := ratio) (absTick := absTick)
        (tick := tick) (ret := ret) (R := R) (mem := mem) (aw := aw) (rdata := rdata)
        (acc := acc) hpatch h hpos (by omega)
    by_cases hrem : getSqrtRatioRemainderWord ratio = ⟨0⟩
    · obtain ⟨_, _, hdone⟩ :=
        uniswapV3PoolGetSqrtRatioAtTickReturnRemainderZero (v := v) (code := code)
          (ee := ee) (g := g) (s0 := s0) (ratio := ratio) (absTick := absTick)
          (tick := tick) (ret := ret) (R := R) (mem := mem) (aw := aw)
          (rdata := rdata) (acc := acc) hpatch htail hrem hret (by omega)
      exact ⟨_, _, by
        simpa [getSqrtRatioTailReturnWord, getSqrtRatioFinalRatioWord, hpos] using hdone⟩
    · obtain ⟨_, _, hdone⟩ :=
        uniswapV3PoolGetSqrtRatioAtTickReturnRemainderNonzero (v := v) (code := code)
          (ee := ee) (g := g) (s0 := s0) (ratio := ratio) (absTick := absTick)
          (tick := tick) (ret := ret) (R := R) (mem := mem) (aw := aw)
          (rdata := rdata) (acc := acc) hpatch htail hrem hret (by omega)
      exact ⟨_, _, by
        simpa [getSqrtRatioTailReturnWord, getSqrtRatioFinalRatioWord, hpos] using hdone⟩
  · obtain ⟨_, _, htail⟩ :=
      uniswapV3PoolGetSqrtRatioAtTickTickPos (v := v) (code := code)
        (ee := ee) (g := g) (s0 := s0) (ratio := ratio) (absTick := absTick)
        (tick := tick) (ret := ret) (R := R) (mem := mem) (aw := aw) (rdata := rdata)
        (acc := acc) hpatch h hpos hratio hov
    by_cases hrem : getSqrtRatioRemainderWord (getSqrtRatioInvertedWord ratio) = ⟨0⟩
    · obtain ⟨_, _, hdone⟩ :=
        uniswapV3PoolGetSqrtRatioAtTickReturnRemainderZero (v := v) (code := code)
          (ee := ee) (g := g) (s0 := s0) (ratio := getSqrtRatioInvertedWord ratio)
          (absTick := absTick) (tick := tick) (ret := ret) (R := R) (mem := mem)
          (aw := aw) (rdata := rdata) (acc := acc) hpatch htail hrem hret (by omega)
      exact ⟨_, _, by
        simpa [getSqrtRatioTailReturnWord, getSqrtRatioFinalRatioWord, hpos] using hdone⟩
    · obtain ⟨_, _, hdone⟩ :=
        uniswapV3PoolGetSqrtRatioAtTickReturnRemainderNonzero (v := v) (code := code)
          (ee := ee) (g := g) (s0 := s0) (ratio := getSqrtRatioInvertedWord ratio)
          (absTick := absTick) (tick := tick) (ret := ret) (R := R) (mem := mem)
          (aw := aw) (rdata := rdata) (acc := acc) hpatch htail hrem hret (by omega)
      exact ⟨_, _, by
        simpa [getSqrtRatioTailReturnWord, getSqrtRatioFinalRatioWord, hpos] using hdone⟩

end Benchmarks.UniswapV3Pool
