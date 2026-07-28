import Benchmarks.UniswapV3Pool.InitializeGetTickSqrtRatioReturn

open Solm ABI Ethereum Ethereum.EVM Benchmarks.UniswapV3Pool.Immutables
open Reasoning.Theory Reasoning.Reach

namespace Benchmarks.UniswapV3Pool

def getSqrtRatioAfterBit2BranchWord (absTick ratio : UInt256) : UInt256 :=
  if getSqrtRatioBit2Word absTick = ⟨0⟩ then getSqrtRatioRatioMaskedWord ratio
  else getSqrtRatioAfterBit2Word ratio

def getSqrtRatioAfterBit4BranchWord (absTick ratio : UInt256) : UInt256 :=
  if getSqrtRatioBit4Word absTick = ⟨0⟩ then ratio
  else getSqrtRatioAfterBit4Word ratio

def getSqrtRatioAfterBit8BranchWord (absTick ratio : UInt256) : UInt256 :=
  if getSqrtRatioBit8Word absTick = ⟨0⟩ then ratio
  else getSqrtRatioAfterBit8Word ratio

def getSqrtRatioAfterBit16BranchWord (absTick ratio : UInt256) : UInt256 :=
  if getSqrtRatioBit16Word absTick = ⟨0⟩ then ratio
  else getSqrtRatioAfterBit16Word ratio

def getSqrtRatioAfterBit32BranchWord (absTick ratio : UInt256) : UInt256 :=
  if getSqrtRatioBit32Word absTick = ⟨0⟩ then ratio
  else getSqrtRatioAfterBit32Word ratio

def getSqrtRatioAfterBit64BranchWord (absTick ratio : UInt256) : UInt256 :=
  if getSqrtRatioBit64Word absTick = ⟨0⟩ then ratio
  else getSqrtRatioAfterBit64Word ratio

def getSqrtRatioAfterBit128BranchWord (absTick ratio : UInt256) : UInt256 :=
  if getSqrtRatioBit128Word absTick = ⟨0⟩ then ratio
  else getSqrtRatioAfterBit128Word ratio

def getSqrtRatioAfterBit256BranchWord (absTick ratio : UInt256) : UInt256 :=
  if getSqrtRatioBit256Word absTick = ⟨0⟩ then ratio
  else getSqrtRatioAfterBit256Word ratio

def getSqrtRatioAfterBit512BranchWord (absTick ratio : UInt256) : UInt256 :=
  if getSqrtRatioBit512Word absTick = ⟨0⟩ then ratio
  else getSqrtRatioAfterBit512Word ratio

def getSqrtRatioAfterBit1024BranchWord (absTick ratio : UInt256) : UInt256 :=
  if getSqrtRatioBit1024Word absTick = ⟨0⟩ then ratio
  else getSqrtRatioAfterBit1024Word ratio

def getSqrtRatioAfterLowBitsWord (absTick ratio : UInt256) : UInt256 :=
  let r4 := getSqrtRatioAfterBit4BranchWord absTick ratio
  let r8 := getSqrtRatioAfterBit8BranchWord absTick r4
  let r16 := getSqrtRatioAfterBit16BranchWord absTick r8
  let r32 := getSqrtRatioAfterBit32BranchWord absTick r16
  let r64 := getSqrtRatioAfterBit64BranchWord absTick r32
  let r128 := getSqrtRatioAfterBit128BranchWord absTick r64
  let r256 := getSqrtRatioAfterBit256BranchWord absTick r128
  let r512 := getSqrtRatioAfterBit512BranchWord absTick r256
  getSqrtRatioAfterBit1024BranchWord absTick r512

def getSqrtRatioAfterAllBitsWord (absTick ratio : UInt256) : UInt256 :=
  let r2 := getSqrtRatioAfterBit2BranchWord absTick ratio
  let r1024 := getSqrtRatioAfterLowBitsWord absTick r2
  getSqrtRatioAfterHighBitsWord absTick r1024

def getSqrtRatioAbsTickBranchWord (tick : UInt256) : UInt256 :=
  if getSqrtRatioTickNegWord tick = ⟨0⟩ then getSqrtRatioTickInt24Word tick
  else getSqrtRatioAbsTickNegWord tick

def getSqrtRatioInitialBranchWord (absTick : UInt256) : UInt256 :=
  if getSqrtRatioBit1Word absTick = ⟨0⟩ then getSqrtRatioInitialEvenWord
  else getSqrtRatioInitialOddWord

def getSqrtRatioAtTickResultWord (tick : UInt256) : UInt256 :=
  let absTick := getSqrtRatioAbsTickBranchWord tick
  let ratio := getSqrtRatioInitialBranchWord absTick
  getSqrtRatioTailReturnWord tick (getSqrtRatioAfterAllBitsWord absTick ratio)

def getTickHiSqrtRatioCleanWord (sqrtRatio : UInt256) : UInt256 :=
  UInt256.land slot0Uint160Mask sqrtRatio

def getTickHiSqrtRatioGtInputWord (ee : ExecutionEnv) (sqrtRatio : UInt256) : UInt256 :=
  UInt256.gt (getTickHiSqrtRatioCleanWord sqrtRatio) (initializeArgWord ee)

def getTickAfterHiSqrtRatioWord (ee : ExecutionEnv) (sqrtRatio : UInt256) : UInt256 :=
  if getTickHiSqrtRatioGtInputWord ee sqrtRatio = ⟨0⟩ then getTickHiWord ee
  else getTickLowWord ee

def getTickHiSqrtRatioWord (ee : ExecutionEnv) : UInt256 :=
  getSqrtRatioAtTickResultWord (getTickHiWord ee)

def getTickEstimatedWord (ee : ExecutionEnv) : UInt256 :=
  if getTickLowEqHiWord ee = ⟨0⟩ then getTickAfterHiSqrtRatioWord ee (getTickHiSqrtRatioWord ee)
  else getTickLowWord ee

private theorem uniswapV3PoolInitializePatchPreservesJumpDest14779 :
    D_J_auxPreservesTargetBool uniswapV3PoolBytecode uniswapV3PoolPatchOffsets
      ⟨14779⟩ 0 = true := by
  native_decide

private theorem uniswapV3PoolInitializePatchPreservesJumpDest14781 :
    D_J_auxPreservesTargetBool uniswapV3PoolBytecode uniswapV3PoolPatchOffsets
      ⟨14781⟩ 0 = true := by
  native_decide

theorem uniswapV3PoolJumpDestPatched14779 {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    (D_J code 0).contains ⟨14779⟩ = true := by
  exact D_J_aux_contains_of_patchRuntime_preservesTarget hpatch
    (uniswapV3PoolPatchOffsetMem v)
    uniswapV3PoolInitializePatchPreservesJumpDest14779

theorem uniswapV3PoolJumpDestPatched14781 {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    (D_J code 0).contains ⟨14781⟩ = true := by
  exact D_J_aux_contains_of_patchRuntime_preservesTarget hpatch
    (uniswapV3PoolPatchOffsetMem v)
    uniswapV3PoolInitializePatchPreservesJumpDest14781

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem uniswapV3PoolGetSqrtRatioAtTickLowBits {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {ratio absTick tick ret : UInt256} {R : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨11812⟩ (ratio :: absTick :: ⟨0⟩ :: tick :: ret :: R)
      mem aw rdata acc k C)
    (hov : R.length + 7 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨12094⟩
      (getSqrtRatioAfterLowBitsWord absTick ratio :: absTick :: ⟨0⟩ :: tick :: ret :: R)
      mem aw rdata acc k' C' := by
  let r4 := getSqrtRatioAfterBit4BranchWord absTick ratio
  have h4 : ∃ k' C', RD code ee g s0 ⟨11843⟩
      (r4 :: absTick :: ⟨0⟩ :: tick :: ret :: R) mem aw rdata acc k' C' := by
    by_cases hbit : getSqrtRatioBit4Word absTick = ⟨0⟩
    · obtain ⟨_, _, hnext⟩ :=
        uniswapV3PoolGetSqrtRatioAtTickBit4Zero (v := v) (code := code)
          (ee := ee) (g := g) (s0 := s0) (ratio := ratio) (absTick := absTick)
          (tick := tick) (ret := ret) (R := R) (mem := mem) (aw := aw)
          (rdata := rdata) (acc := acc) hpatch h hbit hov
      exact ⟨_, _, by simpa [r4, getSqrtRatioAfterBit4BranchWord, hbit] using hnext⟩
    · obtain ⟨_, _, hnext⟩ :=
        uniswapV3PoolGetSqrtRatioAtTickBit4Set (v := v) (code := code)
          (ee := ee) (g := g) (s0 := s0) (ratio := ratio) (absTick := absTick)
          (tick := tick) (ret := ret) (R := R) (mem := mem) (aw := aw)
          (rdata := rdata) (acc := acc) hpatch h hbit hov
      exact ⟨_, _, by simpa [r4, getSqrtRatioAfterBit4BranchWord, hbit] using hnext⟩
  obtain ⟨_, _, h4⟩ := h4
  let r8 := getSqrtRatioAfterBit8BranchWord absTick r4
  have h8 : ∃ k' C', RD code ee g s0 ⟨11874⟩
      (r8 :: absTick :: ⟨0⟩ :: tick :: ret :: R) mem aw rdata acc k' C' := by
    by_cases hbit : getSqrtRatioBit8Word absTick = ⟨0⟩
    · obtain ⟨_, _, hnext⟩ :=
        uniswapV3PoolGetSqrtRatioAtTickBit8Zero (v := v) (code := code)
          (ee := ee) (g := g) (s0 := s0) (ratio := r4) (absTick := absTick)
          (tick := tick) (ret := ret) (R := R) (mem := mem) (aw := aw)
          (rdata := rdata) (acc := acc) hpatch h4 hbit hov
      exact ⟨_, _, by simpa [r8, getSqrtRatioAfterBit8BranchWord, hbit] using hnext⟩
    · obtain ⟨_, _, hnext⟩ :=
        uniswapV3PoolGetSqrtRatioAtTickBit8Set (v := v) (code := code)
          (ee := ee) (g := g) (s0 := s0) (ratio := r4) (absTick := absTick)
          (tick := tick) (ret := ret) (R := R) (mem := mem) (aw := aw)
          (rdata := rdata) (acc := acc) hpatch h4 hbit hov
      exact ⟨_, _, by simpa [r8, getSqrtRatioAfterBit8BranchWord, hbit] using hnext⟩
  obtain ⟨_, _, h8⟩ := h8
  let r16 := getSqrtRatioAfterBit16BranchWord absTick r8
  have h16 : ∃ k' C', RD code ee g s0 ⟨11905⟩
      (r16 :: absTick :: ⟨0⟩ :: tick :: ret :: R) mem aw rdata acc k' C' := by
    by_cases hbit : getSqrtRatioBit16Word absTick = ⟨0⟩
    · obtain ⟨_, _, hnext⟩ :=
        uniswapV3PoolGetSqrtRatioAtTickBit16Zero (v := v) (code := code)
          (ee := ee) (g := g) (s0 := s0) (ratio := r8) (absTick := absTick)
          (tick := tick) (ret := ret) (R := R) (mem := mem) (aw := aw)
          (rdata := rdata) (acc := acc) hpatch h8 hbit hov
      exact ⟨_, _, by simpa [r16, getSqrtRatioAfterBit16BranchWord, hbit] using hnext⟩
    · obtain ⟨_, _, hnext⟩ :=
        uniswapV3PoolGetSqrtRatioAtTickBit16Set (v := v) (code := code)
          (ee := ee) (g := g) (s0 := s0) (ratio := r8) (absTick := absTick)
          (tick := tick) (ret := ret) (R := R) (mem := mem) (aw := aw)
          (rdata := rdata) (acc := acc) hpatch h8 hbit hov
      exact ⟨_, _, by simpa [r16, getSqrtRatioAfterBit16BranchWord, hbit] using hnext⟩
  obtain ⟨_, _, h16⟩ := h16
  let r32 := getSqrtRatioAfterBit32BranchWord absTick r16
  have h32 : ∃ k' C', RD code ee g s0 ⟨11936⟩
      (r32 :: absTick :: ⟨0⟩ :: tick :: ret :: R) mem aw rdata acc k' C' := by
    by_cases hbit : getSqrtRatioBit32Word absTick = ⟨0⟩
    · obtain ⟨_, _, hnext⟩ :=
        uniswapV3PoolGetSqrtRatioAtTickBit32Zero (v := v) (code := code)
          (ee := ee) (g := g) (s0 := s0) (ratio := r16) (absTick := absTick)
          (tick := tick) (ret := ret) (R := R) (mem := mem) (aw := aw)
          (rdata := rdata) (acc := acc) hpatch h16 hbit hov
      exact ⟨_, _, by simpa [r32, getSqrtRatioAfterBit32BranchWord, hbit] using hnext⟩
    · obtain ⟨_, _, hnext⟩ :=
        uniswapV3PoolGetSqrtRatioAtTickBit32Set (v := v) (code := code)
          (ee := ee) (g := g) (s0 := s0) (ratio := r16) (absTick := absTick)
          (tick := tick) (ret := ret) (R := R) (mem := mem) (aw := aw)
          (rdata := rdata) (acc := acc) hpatch h16 hbit hov
      exact ⟨_, _, by simpa [r32, getSqrtRatioAfterBit32BranchWord, hbit] using hnext⟩
  obtain ⟨_, _, h32⟩ := h32
  let r64 := getSqrtRatioAfterBit64BranchWord absTick r32
  have h64 : ∃ k' C', RD code ee g s0 ⟨11967⟩
      (r64 :: absTick :: ⟨0⟩ :: tick :: ret :: R) mem aw rdata acc k' C' := by
    by_cases hbit : getSqrtRatioBit64Word absTick = ⟨0⟩
    · obtain ⟨_, _, hnext⟩ :=
        uniswapV3PoolGetSqrtRatioAtTickBit64Zero (v := v) (code := code)
          (ee := ee) (g := g) (s0 := s0) (ratio := r32) (absTick := absTick)
          (tick := tick) (ret := ret) (R := R) (mem := mem) (aw := aw)
          (rdata := rdata) (acc := acc) hpatch h32 hbit hov
      exact ⟨_, _, by simpa [r64, getSqrtRatioAfterBit64BranchWord, hbit] using hnext⟩
    · obtain ⟨_, _, hnext⟩ :=
        uniswapV3PoolGetSqrtRatioAtTickBit64Set (v := v) (code := code)
          (ee := ee) (g := g) (s0 := s0) (ratio := r32) (absTick := absTick)
          (tick := tick) (ret := ret) (R := R) (mem := mem) (aw := aw)
          (rdata := rdata) (acc := acc) hpatch h32 hbit hov
      exact ⟨_, _, by simpa [r64, getSqrtRatioAfterBit64BranchWord, hbit] using hnext⟩
  obtain ⟨_, _, h64⟩ := h64
  let r128 := getSqrtRatioAfterBit128BranchWord absTick r64
  have h128 : ∃ k' C', RD code ee g s0 ⟨11998⟩
      (r128 :: absTick :: ⟨0⟩ :: tick :: ret :: R) mem aw rdata acc k' C' := by
    by_cases hbit : getSqrtRatioBit128Word absTick = ⟨0⟩
    · obtain ⟨_, _, hnext⟩ :=
        uniswapV3PoolGetSqrtRatioAtTickBit128Zero (v := v) (code := code)
          (ee := ee) (g := g) (s0 := s0) (ratio := r64) (absTick := absTick)
          (tick := tick) (ret := ret) (R := R) (mem := mem) (aw := aw)
          (rdata := rdata) (acc := acc) hpatch h64 hbit hov
      exact ⟨_, _, by simpa [r128, getSqrtRatioAfterBit128BranchWord, hbit] using hnext⟩
    · obtain ⟨_, _, hnext⟩ :=
        uniswapV3PoolGetSqrtRatioAtTickBit128Set (v := v) (code := code)
          (ee := ee) (g := g) (s0 := s0) (ratio := r64) (absTick := absTick)
          (tick := tick) (ret := ret) (R := R) (mem := mem) (aw := aw)
          (rdata := rdata) (acc := acc) hpatch h64 hbit hov
      exact ⟨_, _, by simpa [r128, getSqrtRatioAfterBit128BranchWord, hbit] using hnext⟩
  obtain ⟨_, _, h128⟩ := h128
  let r256 := getSqrtRatioAfterBit256BranchWord absTick r128
  have h256 : ∃ k' C', RD code ee g s0 ⟨12030⟩
      (r256 :: absTick :: ⟨0⟩ :: tick :: ret :: R) mem aw rdata acc k' C' := by
    by_cases hbit : getSqrtRatioBit256Word absTick = ⟨0⟩
    · obtain ⟨_, _, hnext⟩ :=
        uniswapV3PoolGetSqrtRatioAtTickBit256Zero (v := v) (code := code)
          (ee := ee) (g := g) (s0 := s0) (ratio := r128) (absTick := absTick)
          (tick := tick) (ret := ret) (R := R) (mem := mem) (aw := aw)
          (rdata := rdata) (acc := acc) hpatch h128 hbit hov
      exact ⟨_, _, by simpa [r256, getSqrtRatioAfterBit256BranchWord, hbit] using hnext⟩
    · obtain ⟨_, _, hnext⟩ :=
        uniswapV3PoolGetSqrtRatioAtTickBit256Set (v := v) (code := code)
          (ee := ee) (g := g) (s0 := s0) (ratio := r128) (absTick := absTick)
          (tick := tick) (ret := ret) (R := R) (mem := mem) (aw := aw)
          (rdata := rdata) (acc := acc) hpatch h128 hbit hov
      exact ⟨_, _, by simpa [r256, getSqrtRatioAfterBit256BranchWord, hbit] using hnext⟩
  obtain ⟨_, _, h256⟩ := h256
  let r512 := getSqrtRatioAfterBit512BranchWord absTick r256
  have h512 : ∃ k' C', RD code ee g s0 ⟨12062⟩
      (r512 :: absTick :: ⟨0⟩ :: tick :: ret :: R) mem aw rdata acc k' C' := by
    by_cases hbit : getSqrtRatioBit512Word absTick = ⟨0⟩
    · obtain ⟨_, _, hnext⟩ :=
        uniswapV3PoolGetSqrtRatioAtTickBit512Zero (v := v) (code := code)
          (ee := ee) (g := g) (s0 := s0) (ratio := r256) (absTick := absTick)
          (tick := tick) (ret := ret) (R := R) (mem := mem) (aw := aw)
          (rdata := rdata) (acc := acc) hpatch h256 hbit hov
      exact ⟨_, _, by simpa [r512, getSqrtRatioAfterBit512BranchWord, hbit] using hnext⟩
    · obtain ⟨_, _, hnext⟩ :=
        uniswapV3PoolGetSqrtRatioAtTickBit512Set (v := v) (code := code)
          (ee := ee) (g := g) (s0 := s0) (ratio := r256) (absTick := absTick)
          (tick := tick) (ret := ret) (R := R) (mem := mem) (aw := aw)
          (rdata := rdata) (acc := acc) hpatch h256 hbit hov
      exact ⟨_, _, by simpa [r512, getSqrtRatioAfterBit512BranchWord, hbit] using hnext⟩
  obtain ⟨_, _, h512⟩ := h512
  let r1024 := getSqrtRatioAfterBit1024BranchWord absTick r512
  have h1024 : ∃ k' C', RD code ee g s0 ⟨12094⟩
      (r1024 :: absTick :: ⟨0⟩ :: tick :: ret :: R) mem aw rdata acc k' C' := by
    by_cases hbit : getSqrtRatioBit1024Word absTick = ⟨0⟩
    · obtain ⟨_, _, hnext⟩ :=
        uniswapV3PoolGetSqrtRatioAtTickBit1024Zero (v := v) (code := code)
          (ee := ee) (g := g) (s0 := s0) (ratio := r512) (absTick := absTick)
          (tick := tick) (ret := ret) (R := R) (mem := mem) (aw := aw)
          (rdata := rdata) (acc := acc) hpatch h512 hbit hov
      exact ⟨_, _, by simpa [r1024, getSqrtRatioAfterBit1024BranchWord, hbit] using hnext⟩
    · obtain ⟨_, _, hnext⟩ :=
        uniswapV3PoolGetSqrtRatioAtTickBit1024Set (v := v) (code := code)
          (ee := ee) (g := g) (s0 := s0) (ratio := r512) (absTick := absTick)
          (tick := tick) (ret := ret) (R := R) (mem := mem) (aw := aw)
          (rdata := rdata) (acc := acc) hpatch h512 hbit hov
      exact ⟨_, _, by simpa [r1024, getSqrtRatioAfterBit1024BranchWord, hbit] using hnext⟩
  obtain ⟨_, _, h1024⟩ := h1024
  exact ⟨_, _, by
    simpa [getSqrtRatioAfterLowBitsWord, r4, r8, r16, r32, r64, r128, r256, r512,
      r1024] using h1024⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem uniswapV3PoolGetSqrtRatioAtTickAllBits {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {ratio absTick tick ret : UInt256} {R : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨11760⟩ (ratio :: ⟨0⟩ :: absTick :: ⟨0⟩ :: tick :: ret :: R)
      mem aw rdata acc k C)
    (hov : R.length + 7 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨12379⟩
      (getSqrtRatioAfterAllBitsWord absTick ratio :: absTick :: ⟨0⟩ :: tick :: ret :: R)
      mem aw rdata acc k' C' := by
  let r2 := getSqrtRatioAfterBit2BranchWord absTick ratio
  have h2 : ∃ k' C', RD code ee g s0 ⟨11812⟩
      (r2 :: absTick :: ⟨0⟩ :: tick :: ret :: R) mem aw rdata acc k' C' := by
    by_cases hbit : getSqrtRatioBit2Word absTick = ⟨0⟩
    · obtain ⟨_, _, hnext⟩ :=
        uniswapV3PoolGetSqrtRatioAtTickBit2Zero (v := v) (code := code)
          (ee := ee) (g := g) (s0 := s0) (ratio := ratio) (absTick := absTick)
          (tick := tick) (ret := ret) (R := R) (mem := mem) (aw := aw)
          (rdata := rdata) (acc := acc) hpatch h hbit hov
      exact ⟨_, _, by simpa [r2, getSqrtRatioAfterBit2BranchWord, hbit] using hnext⟩
    · obtain ⟨_, _, hnext⟩ :=
        uniswapV3PoolGetSqrtRatioAtTickBit2Set (v := v) (code := code)
          (ee := ee) (g := g) (s0 := s0) (ratio := ratio) (absTick := absTick)
          (tick := tick) (ret := ret) (R := R) (mem := mem) (aw := aw)
          (rdata := rdata) (acc := acc) hpatch h hbit hov
      exact ⟨_, _, by simpa [r2, getSqrtRatioAfterBit2BranchWord, hbit] using hnext⟩
  obtain ⟨_, _, h2⟩ := h2
  obtain ⟨_, _, hlow⟩ :=
    uniswapV3PoolGetSqrtRatioAtTickLowBits (v := v) (code := code)
      (ee := ee) (g := g) (s0 := s0) (ratio := r2) (absTick := absTick)
      (tick := tick) (ret := ret) (R := R) (mem := mem) (aw := aw)
      (rdata := rdata) (acc := acc) hpatch h2 hov
  obtain ⟨_, _, hhigh⟩ :=
    uniswapV3PoolGetSqrtRatioAtTickHighBits (v := v) (code := code)
      (ee := ee) (g := g) (s0 := s0) (ratio := getSqrtRatioAfterLowBitsWord absTick r2)
      (absTick := absTick) (tick := tick) (ret := ret) (R := R) (mem := mem)
      (aw := aw) (rdata := rdata) (acc := acc) hpatch hlow hov
  exact ⟨_, _, by
    simpa [getSqrtRatioAfterAllBitsWord, r2] using hhigh⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem uniswapV3PoolGetTickAtSqrtRatioReturnAfterHiSqrt {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {sqrtRatio ret : UInt256} {R : List UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨14758⟩
      (sqrtRatio :: initializeArgWord ee :: getTickHiWord ee :: getTickLowWord ee ::
        getTickLogSqrt10001Word ee :: getTickLog2After50Word ee :: getTickMsbWord ee ::
          getTickLogRShifted50Word ee :: getTickRatioWord ee :: ⟨0⟩ :: initializeArgWord ee ::
            ⟨10793⟩ :: ⟨0⟩ :: initializeArgWord ee :: ret :: R)
      solcFreePtrMem (UInt256.ofNat 3) rdata acc k C)
    (hov : R.length + 18 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨10793⟩
      (getTickAfterHiSqrtRatioWord ee sqrtRatio :: ⟨0⟩ :: initializeArgWord ee :: ret :: R)
      solcFreePtrMem (UInt256.ofNat 3) rdata acc k' C' := by
  have hdecode {pc : UInt256} (hlo : 13989 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 15650) :
      decode code pc = decode uniswapV3PoolBytecode pc := by
    rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by
        have hsize : 15650 ≤ uniswapV3PoolBytecode.size := by native_decide
        omega)
      (uniswapV3PoolInitializePatchDisjointGetTickAtSqrtRatio hlo hhi)]
  have hd14758 : decode code ⟨14758⟩ = some (.JUMPDEST, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14759 : decode code ⟨14759⟩ = some (.Push .PUSH1, some (⟨1⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14761 : decode code ⟨14761⟩ = some (.Push .PUSH1, some (⟨1⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14763 : decode code ⟨14763⟩ = some (.Push .PUSH1, some (⟨160⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14765 : decode code ⟨14765⟩ = some (.SHL, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14766 : decode code ⟨14766⟩ = some (.SUB, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14767 : decode code ⟨14767⟩ = some (.AND, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14768 : decode code ⟨14768⟩ = some (.GT, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14769 : decode code ⟨14769⟩ = some (.ISZERO, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14770 : decode code ⟨14770⟩ = some (.Push .PUSH2, some (⟨14779⟩, 2)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14773 : decode code ⟨14773⟩ = some (.JUMPI, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14774 : decode code ⟨14774⟩ = some (.DUP2, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14775 : decode code ⟨14775⟩ = some (.Push .PUSH2, some (⟨14781⟩, 2)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14778 : decode code ⟨14778⟩ = some (.JUMP, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14779 : decode code ⟨14779⟩ = some (.JUMPDEST, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14780 : decode code ⟨14780⟩ = some (.DUP1, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14781 : decode code ⟨14781⟩ = some (.JUMPDEST, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14782 : decode code ⟨14782⟩ = some (.Push .PUSH2, some (⟨14788⟩, 2)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd14785 : decode code ⟨14785⟩ = some (.JUMP, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have rd14759 := by
    simpa using h.jumpdest hd14758 (by
      simp only [List.length_cons]
      omega)
  have rd14761 := by
    simpa using rd14759.push1 ⟨1⟩ hd14759 (by
      simp only [List.length_cons]
      omega)
  have rd14763 := by
    simpa using rd14761.push1 ⟨1⟩ hd14761 (by
      simp only [List.length_cons]
      omega)
  have rd14765 := by
    simpa using rd14763.push1 ⟨160⟩ hd14763 (by
      simp only [List.length_cons]
      omega)
  have rd14766 := by
    simpa using rd14765.shl hd14765 (by
      simp only [List.length_cons]
      omega)
  have rd14767 := by
    simpa [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        slot0Uint160Mask by native_decide] using rd14766.sub hd14766 (by
      simp only [List.length_cons]
      omega)
  have rd14768 := by
    simpa [getTickHiSqrtRatioCleanWord] using rd14767.and hd14767 (by
      simp only [List.length_cons]
      omega)
  have rd14769 := by
    simpa [getTickHiSqrtRatioGtInputWord] using rd14768.gt hd14768 (by
      simp only [List.length_cons]
      omega)
  have rd14770 := by
    simpa using rd14769.iszero hd14769 (by
      simp only [List.length_cons]
      omega)
  have rd14773 := by
    simpa using rd14770.push2 ⟨14779⟩ hd14770 (by
      simp only [List.length_cons]
      omega)
  by_cases hgt : getTickHiSqrtRatioGtInputWord ee sqrtRatio = ⟨0⟩
  · have hcond : UInt256.isZero (getTickHiSqrtRatioGtInputWord ee sqrtRatio) ≠ ⟨0⟩ := by
      rw [hgt]
      native_decide
    have rd14779 := rd14773.jumpiT hd14773 hcond
      (uniswapV3PoolJumpDestPatched14779 hpatch) (by
        simp only [List.length_cons]
        omega)
    have rd14780 := by
      simpa using rd14779.jumpdest hd14779 (by
        simp only [List.length_cons]
        omega)
    have rd14781 := by
      simpa using rd14780.dup1 hd14780 (by
        simp only [List.length_cons]
        omega)
    have rd14782 := by
      simpa using rd14781.jumpdest hd14781 (by
        simp only [List.length_cons]
        omega)
    have rd14785 := by
      simpa using rd14782.push2 ⟨14788⟩ hd14782 (by
        simp only [List.length_cons]
        omega)
    have rd14788 := rd14785.jump hd14785 (uniswapV3PoolJumpDestPatched14788 hpatch) (by
      simp only [List.length_cons]
      omega)
    obtain ⟨_, _, hdone⟩ :=
      uniswapV3PoolGetTickAtSqrtRatioReturnCleanup (v := v) (code := code)
        (ee := ee) (g := g) (s0 := s0) (tick := getTickHiWord ee)
        (a := getTickHiWord ee) (b := getTickLowWord ee)
        (c := getTickLogSqrt10001Word ee) (d := getTickLog2After50Word ee)
        (e := getTickMsbWord ee) (f := getTickLogRShifted50Word ee)
        (gg := getTickRatioWord ee) (ret := ret) (R := R) (rdata := rdata)
        (acc := acc) hpatch rd14788 hov
    exact ⟨_, _, by simpa [getTickAfterHiSqrtRatioWord, hgt] using hdone⟩
  · have hcond : UInt256.isZero (getTickHiSqrtRatioGtInputWord ee sqrtRatio) = ⟨0⟩ :=
      isZero_eq_zero_of_ne hgt
    have rd14774 := rd14773.jumpiNT hd14773 hcond (by
      simp only [List.length_cons]
      omega)
    have rd14775 := by
      simpa using rd14774.dup2 hd14774 (by
        simp only [List.length_cons]
        omega)
    have rd14778 := by
      simpa using rd14775.push2 ⟨14781⟩ hd14775 (by
        simp only [List.length_cons]
        omega)
    have rd14781 := rd14778.jump hd14778 (uniswapV3PoolJumpDestPatched14781 hpatch) (by
      simp only [List.length_cons]
      omega)
    have rd14782 := by
      simpa using rd14781.jumpdest hd14781 (by
        simp only [List.length_cons]
        omega)
    have rd14785 := by
      simpa using rd14782.push2 ⟨14788⟩ hd14782 (by
        simp only [List.length_cons]
        omega)
    have rd14788 := rd14785.jump hd14785 (uniswapV3PoolJumpDestPatched14788 hpatch) (by
      simp only [List.length_cons]
      omega)
    obtain ⟨_, _, hdone⟩ :=
      uniswapV3PoolGetTickAtSqrtRatioReturnCleanup (v := v) (code := code)
        (ee := ee) (g := g) (s0 := s0) (tick := getTickLowWord ee)
        (a := getTickHiWord ee) (b := getTickLowWord ee)
        (c := getTickLogSqrt10001Word ee) (d := getTickLog2After50Word ee)
        (e := getTickMsbWord ee) (f := getTickLogRShifted50Word ee)
        (gg := getTickRatioWord ee) (ret := ret) (R := R) (rdata := rdata)
        (acc := acc) hpatch rd14788 hov
    exact ⟨_, _, by simpa [getTickAfterHiSqrtRatioWord, hgt] using hdone⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem uniswapV3PoolGetSqrtRatioAtTickReturn {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {tick ret : UInt256} {R : List UInt256}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨11629⟩ (tick :: ret :: R) mem aw rdata acc k C)
    (hok : getSqrtRatioAbsTickInRangeWord (getSqrtRatioAbsTickBranchWord tick) ≠ ⟨0⟩)
    (hratio :
      getSqrtRatioAfterAllBitsWord (getSqrtRatioAbsTickBranchWord tick)
        (getSqrtRatioInitialBranchWord (getSqrtRatioAbsTickBranchWord tick)) ≠ ⟨0⟩)
    (hret : (D_J code 0).contains ret = true)
    (hov : R.length + 9 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ret (getSqrtRatioAtTickResultWord tick :: R)
      mem aw rdata acc k' C' := by
  by_cases hneg : getSqrtRatioTickNegWord tick = ⟨0⟩
  · obtain ⟨_, _, habs⟩ :=
      uniswapV3PoolGetSqrtRatioAtTickAbsTickNonNeg (v := v) (code := code)
        (ee := ee) (g := g) (s0 := s0) (tick := tick) (ret := ret) (R := R)
        (mem := mem) (aw := aw) (rdata := rdata) (acc := acc) hpatch h hneg
        (by omega)
    let absTick := getSqrtRatioTickInt24Word tick
    obtain ⟨_, _, hrange⟩ :=
      uniswapV3PoolGetSqrtRatioAtTickRangeOk (v := v) (code := code)
        (ee := ee) (g := g) (s0 := s0) (absTick := absTick) (tick := tick)
        (ret := ret) (R := R) (mem := mem) (aw := aw) (rdata := rdata)
        (acc := acc) hpatch (by simpa [absTick] using habs) (by
          simpa [absTick, getSqrtRatioAbsTickBranchWord, hneg] using hok) (by omega)
    by_cases hbit : getSqrtRatioBit1Word absTick = ⟨0⟩
    · obtain ⟨_, _, hinit⟩ :=
        uniswapV3PoolGetSqrtRatioAtTickRatioInitEven (v := v) (code := code)
          (ee := ee) (g := g) (s0 := s0) (absTick := absTick) (tick := tick)
          (ret := ret) (R := R) (mem := mem) (aw := aw) (rdata := rdata)
          (acc := acc) hpatch hrange hbit (by omega)
      let ratio := getSqrtRatioInitialEvenWord
      obtain ⟨_, _, hall⟩ :=
        uniswapV3PoolGetSqrtRatioAtTickAllBits (v := v) (code := code)
          (ee := ee) (g := g) (s0 := s0) (ratio := ratio) (absTick := absTick)
          (tick := tick) (ret := ret) (R := R) (mem := mem) (aw := aw)
          (rdata := rdata) (acc := acc) hpatch (by simpa [ratio] using hinit) (by omega)
      have hratio' : getSqrtRatioAfterAllBitsWord absTick ratio ≠ ⟨0⟩ := by
        simpa [absTick, ratio, getSqrtRatioAbsTickBranchWord,
          getSqrtRatioInitialBranchWord, hneg, hbit] using hratio
      obtain ⟨_, _, hdone⟩ :=
        uniswapV3PoolGetSqrtRatioAtTickReturnTail (v := v) (code := code)
          (ee := ee) (g := g) (s0 := s0)
          (ratio := getSqrtRatioAfterAllBitsWord absTick ratio) (absTick := absTick)
          (tick := tick) (ret := ret) (R := R) (mem := mem) (aw := aw)
          (rdata := rdata) (acc := acc) hpatch hall hratio' hret hov
      exact ⟨_, _, by
        simpa [getSqrtRatioAtTickResultWord, getSqrtRatioAbsTickBranchWord,
          getSqrtRatioInitialBranchWord, absTick, ratio, hneg, hbit] using hdone⟩
    · obtain ⟨_, _, hinit⟩ :=
        uniswapV3PoolGetSqrtRatioAtTickRatioInitOdd (v := v) (code := code)
          (ee := ee) (g := g) (s0 := s0) (absTick := absTick) (tick := tick)
          (ret := ret) (R := R) (mem := mem) (aw := aw) (rdata := rdata)
          (acc := acc) hpatch hrange hbit (by omega)
      let ratio := getSqrtRatioInitialOddWord
      obtain ⟨_, _, hall⟩ :=
        uniswapV3PoolGetSqrtRatioAtTickAllBits (v := v) (code := code)
          (ee := ee) (g := g) (s0 := s0) (ratio := ratio) (absTick := absTick)
          (tick := tick) (ret := ret) (R := R) (mem := mem) (aw := aw)
          (rdata := rdata) (acc := acc) hpatch (by simpa [ratio] using hinit) (by omega)
      have hratio' : getSqrtRatioAfterAllBitsWord absTick ratio ≠ ⟨0⟩ := by
        simpa [absTick, ratio, getSqrtRatioAbsTickBranchWord,
          getSqrtRatioInitialBranchWord, hneg, hbit] using hratio
      obtain ⟨_, _, hdone⟩ :=
        uniswapV3PoolGetSqrtRatioAtTickReturnTail (v := v) (code := code)
          (ee := ee) (g := g) (s0 := s0)
          (ratio := getSqrtRatioAfterAllBitsWord absTick ratio) (absTick := absTick)
          (tick := tick) (ret := ret) (R := R) (mem := mem) (aw := aw)
          (rdata := rdata) (acc := acc) hpatch hall hratio' hret hov
      exact ⟨_, _, by
        simpa [getSqrtRatioAtTickResultWord, getSqrtRatioAbsTickBranchWord,
          getSqrtRatioInitialBranchWord, absTick, ratio, hneg, hbit] using hdone⟩
  · obtain ⟨_, _, habs⟩ :=
      uniswapV3PoolGetSqrtRatioAtTickAbsTickNeg (v := v) (code := code)
        (ee := ee) (g := g) (s0 := s0) (tick := tick) (ret := ret) (R := R)
        (mem := mem) (aw := aw) (rdata := rdata) (acc := acc) hpatch h hneg
        (by omega)
    let absTick := getSqrtRatioAbsTickNegWord tick
    obtain ⟨_, _, hrange⟩ :=
      uniswapV3PoolGetSqrtRatioAtTickRangeOk (v := v) (code := code)
        (ee := ee) (g := g) (s0 := s0) (absTick := absTick) (tick := tick)
        (ret := ret) (R := R) (mem := mem) (aw := aw) (rdata := rdata)
        (acc := acc) hpatch (by simpa [absTick] using habs) (by
          simpa [absTick, getSqrtRatioAbsTickBranchWord, hneg] using hok) (by omega)
    by_cases hbit : getSqrtRatioBit1Word absTick = ⟨0⟩
    · obtain ⟨_, _, hinit⟩ :=
        uniswapV3PoolGetSqrtRatioAtTickRatioInitEven (v := v) (code := code)
          (ee := ee) (g := g) (s0 := s0) (absTick := absTick) (tick := tick)
          (ret := ret) (R := R) (mem := mem) (aw := aw) (rdata := rdata)
          (acc := acc) hpatch hrange hbit (by omega)
      let ratio := getSqrtRatioInitialEvenWord
      obtain ⟨_, _, hall⟩ :=
        uniswapV3PoolGetSqrtRatioAtTickAllBits (v := v) (code := code)
          (ee := ee) (g := g) (s0 := s0) (ratio := ratio) (absTick := absTick)
          (tick := tick) (ret := ret) (R := R) (mem := mem) (aw := aw)
          (rdata := rdata) (acc := acc) hpatch (by simpa [ratio] using hinit) (by omega)
      have hratio' : getSqrtRatioAfterAllBitsWord absTick ratio ≠ ⟨0⟩ := by
        simpa [absTick, ratio, getSqrtRatioAbsTickBranchWord,
          getSqrtRatioInitialBranchWord, hneg, hbit] using hratio
      obtain ⟨_, _, hdone⟩ :=
        uniswapV3PoolGetSqrtRatioAtTickReturnTail (v := v) (code := code)
          (ee := ee) (g := g) (s0 := s0)
          (ratio := getSqrtRatioAfterAllBitsWord absTick ratio) (absTick := absTick)
          (tick := tick) (ret := ret) (R := R) (mem := mem) (aw := aw)
          (rdata := rdata) (acc := acc) hpatch hall hratio' hret hov
      exact ⟨_, _, by
        simpa [getSqrtRatioAtTickResultWord, getSqrtRatioAbsTickBranchWord,
          getSqrtRatioInitialBranchWord, absTick, ratio, hneg, hbit] using hdone⟩
    · obtain ⟨_, _, hinit⟩ :=
        uniswapV3PoolGetSqrtRatioAtTickRatioInitOdd (v := v) (code := code)
          (ee := ee) (g := g) (s0 := s0) (absTick := absTick) (tick := tick)
          (ret := ret) (R := R) (mem := mem) (aw := aw) (rdata := rdata)
          (acc := acc) hpatch hrange hbit (by omega)
      let ratio := getSqrtRatioInitialOddWord
      obtain ⟨_, _, hall⟩ :=
        uniswapV3PoolGetSqrtRatioAtTickAllBits (v := v) (code := code)
          (ee := ee) (g := g) (s0 := s0) (ratio := ratio) (absTick := absTick)
          (tick := tick) (ret := ret) (R := R) (mem := mem) (aw := aw)
          (rdata := rdata) (acc := acc) hpatch (by simpa [ratio] using hinit) (by omega)
      have hratio' : getSqrtRatioAfterAllBitsWord absTick ratio ≠ ⟨0⟩ := by
        simpa [absTick, ratio, getSqrtRatioAbsTickBranchWord,
          getSqrtRatioInitialBranchWord, hneg, hbit] using hratio
      obtain ⟨_, _, hdone⟩ :=
        uniswapV3PoolGetSqrtRatioAtTickReturnTail (v := v) (code := code)
          (ee := ee) (g := g) (s0 := s0)
          (ratio := getSqrtRatioAfterAllBitsWord absTick ratio) (absTick := absTick)
          (tick := tick) (ret := ret) (R := R) (mem := mem) (aw := aw)
          (rdata := rdata) (acc := acc) hpatch hall hratio' hret hov
      exact ⟨_, _, by
        simpa [getSqrtRatioAtTickResultWord, getSqrtRatioAbsTickBranchWord,
          getSqrtRatioInitialBranchWord, absTick, ratio, hneg, hbit] using hdone⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem uniswapV3PoolGetTickAtSqrtRatioReturnTickEstimate {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {ret : UInt256} {R : List UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨14739⟩
      (⟨14786⟩ :: getTickLowEqHiWord ee :: getTickHiWord ee :: getTickLowWord ee ::
        getTickLogSqrt10001Word ee :: getTickLog2After50Word ee :: getTickMsbWord ee ::
          getTickLogRShifted50Word ee :: getTickRatioWord ee :: ⟨0⟩ :: initializeArgWord ee ::
            ⟨10793⟩ :: ⟨0⟩ :: initializeArgWord ee :: ret :: R)
      solcFreePtrMem (UInt256.ofNat 3) rdata acc k C)
    (hok :
      getSqrtRatioAbsTickInRangeWord (getSqrtRatioAbsTickBranchWord (getTickHiWord ee)) ≠
        ⟨0⟩)
    (hratio :
      getSqrtRatioAfterAllBitsWord
        (getSqrtRatioAbsTickBranchWord (getTickHiWord ee))
        (getSqrtRatioInitialBranchWord (getSqrtRatioAbsTickBranchWord (getTickHiWord ee))) ≠
        ⟨0⟩)
    (hov : R.length + 23 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨10793⟩
      (getTickEstimatedWord ee :: ⟨0⟩ :: initializeArgWord ee :: ret :: R)
      solcFreePtrMem (UInt256.ofNat 3) rdata acc k' C' := by
  by_cases heq : getTickLowEqHiWord ee = ⟨0⟩
  · obtain ⟨_, _, hsqrtEntry⟩ :=
      uniswapV3PoolGetTickAtSqrtRatioSqrtRatioCallSetup (v := v) (code := code)
        (ee := ee) (g := g) (s0 := s0) (ret := ret) (R := R) (rdata := rdata)
        (acc := acc) hpatch h heq (by omega)
    let tail :=
      initializeArgWord ee :: getTickHiWord ee :: getTickLowWord ee ::
        getTickLogSqrt10001Word ee :: getTickLog2After50Word ee :: getTickMsbWord ee ::
          getTickLogRShifted50Word ee :: getTickRatioWord ee :: ⟨0⟩ ::
            initializeArgWord ee :: ⟨10793⟩ :: ⟨0⟩ :: initializeArgWord ee :: ret :: R
    obtain ⟨_, _, hsqrtDone⟩ :=
      uniswapV3PoolGetSqrtRatioAtTickReturn (v := v) (code := code)
        (ee := ee) (g := g) (s0 := s0) (tick := getTickHiWord ee) (ret := ⟨14758⟩)
        (R := tail) (mem := solcFreePtrMem) (aw := UInt256.ofNat 3) (rdata := rdata)
        (acc := acc) hpatch (by simpa [tail] using hsqrtEntry) hok hratio
        (uniswapV3PoolJumpDestPatched14758 hpatch) (by
          simp only [tail, List.length_cons]
          omega)
    obtain ⟨_, _, hdone⟩ :=
      uniswapV3PoolGetTickAtSqrtRatioReturnAfterHiSqrt (v := v) (code := code)
        (ee := ee) (g := g) (s0 := s0) (sqrtRatio := getTickHiSqrtRatioWord ee)
        (ret := ret) (R := R) (rdata := rdata) (acc := acc) hpatch
        (by simpa [tail, getTickHiSqrtRatioWord] using hsqrtDone) (by omega)
    exact ⟨_, _, by simpa [getTickEstimatedWord, getTickHiSqrtRatioWord, heq] using hdone⟩
  · obtain ⟨_, _, hdone⟩ :=
      uniswapV3PoolGetTickAtSqrtRatioReturnTickLowEq (v := v) (code := code)
        (ee := ee) (g := g) (s0 := s0) (ret := ret) (R := R) (rdata := rdata)
        (acc := acc) hpatch h heq (by omega)
    exact ⟨_, _, by simpa [getTickEstimatedWord, heq] using hdone⟩

end Benchmarks.UniswapV3Pool
