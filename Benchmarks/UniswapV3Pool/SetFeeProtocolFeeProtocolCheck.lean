import Benchmarks.UniswapV3Pool.SetFeeProtocolSource

open Solm ABI Ethereum Ethereum.EVM Benchmarks.UniswapV3Pool.Immutables
open Reasoning.Theory Reasoning.Reach Reasoning.Refinement

namespace Benchmarks.UniswapV3Pool

abbrev setFeeProtocolEnabledNat (n : Nat) : Prop :=
  n = 0 ∨ (4 ≤ n ∧ n ≤ 10)

private theorem uniswapV3PoolPatchPreservesJumpDest8484 :
    D_J_auxPreservesTargetBool uniswapV3PoolBytecode uniswapV3PoolPatchOffsets
      ⟨8484⟩ 0 = true := by
  native_decide

private theorem uniswapV3PoolPatchPreservesJumpDest8526 :
    D_J_auxPreservesTargetBool uniswapV3PoolBytecode uniswapV3PoolPatchOffsets
      ⟨8526⟩ 0 = true := by
  native_decide

private theorem uniswapV3PoolPatchPreservesJumpDest8535 :
    D_J_auxPreservesTargetBool uniswapV3PoolBytecode uniswapV3PoolPatchOffsets
      ⟨8535⟩ 0 = true := by
  native_decide

theorem uniswapV3PoolJumpDestPatched8484 {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    (D_J code 0).contains ⟨8484⟩ = true := by
  exact D_J_aux_contains_of_patchRuntime_preservesTarget hpatch
    (uniswapV3PoolPatchOffsetMem v)
    uniswapV3PoolPatchPreservesJumpDest8484

theorem uniswapV3PoolJumpDestPatched8526 {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    (D_J code 0).contains ⟨8526⟩ = true := by
  exact D_J_aux_contains_of_patchRuntime_preservesTarget hpatch
    (uniswapV3PoolPatchOffsetMem v)
    uniswapV3PoolPatchPreservesJumpDest8526

theorem uniswapV3PoolJumpDestPatched8535 {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    (D_J code 0).contains ⟨8535⟩ = true := by
  exact D_J_aux_contains_of_patchRuntime_preservesTarget hpatch
    (uniswapV3PoolPatchOffsetMem v)
    uniswapV3PoolPatchPreservesJumpDest8535

theorem setFeeProtocolDecodeNoArgAfterFactory {v : PoolImmutables}
    {code : ByteArray} {pc : UInt256} {byte : UInt8} {op : Operation}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hlo : 8347 ≤ pc.toNat) (hhi : pc.toNat + 1 ≤ 8829)
    (hgetTemplate : uniswapV3PoolBytecode.get? pc.toNat = some byte)
    (hparse : (some byte >>= parseInstr) = some op)
    (harg : argOnNBytesOfInstr op = 0) :
    decode code pc = some (op, .none) := by
  have hsize : 8829 ≤ uniswapV3PoolBytecode.size := by native_decide
  exact uniswapV3PoolDecodePatchedNoArg hpatch (by omega)
    (uniswapV3PoolSetFeeProtocolOwnerCallPatchDisjointAfterFactory
      (n := 1) hlo hhi)
    hgetTemplate hparse harg

theorem setFeeProtocolDecodePush1AfterFactory {v : PoolImmutables}
    {code : ByteArray} {pc n : UInt256}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hlo : 8347 ≤ pc.toNat) (hhi : pc.toNat + 2 ≤ 8829)
    (hgetTemplate : uniswapV3PoolBytecode.get? pc.toNat = some 0x60)
    (hval :
      uInt256OfByteArray
        (uniswapV3PoolBytecode.extract' pc.toNat.succ (pc.toNat.succ + 1)) = n) :
    decode code pc = some (.Push .PUSH1, some (n, 1)) := by
  have hsize : 8829 ≤ uniswapV3PoolBytecode.size := by native_decide
  exact uniswapV3PoolSetFeeProtocolOwnerCallDecodePatchedPush1 hpatch (by omega)
    (uniswapV3PoolSetFeeProtocolOwnerCallPatchDisjointAfterFactory
      (n := 2) hlo hhi)
    hgetTemplate hval

theorem setFeeProtocolDecodePush2AfterFactory {v : PoolImmutables}
    {code : ByteArray} {pc n : UInt256}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hlo : 8347 ≤ pc.toNat) (hhi : pc.toNat + 3 ≤ 8829)
    (hgetTemplate : uniswapV3PoolBytecode.get? pc.toNat = some 0x61)
    (hval :
      uInt256OfByteArray
        (uniswapV3PoolBytecode.extract' pc.toNat.succ (pc.toNat.succ + 2)) = n) :
    decode code pc = some (.Push .PUSH2, some (n, 2)) := by
  have hsize : 8829 ≤ uniswapV3PoolBytecode.size := by native_decide
  exact uniswapV3PoolSetFeeProtocolOwnerCallDecodePatchedPush2 hpatch (by omega)
    (uniswapV3PoolSetFeeProtocolOwnerCallPatchDisjointAfterFactory
      (n := 3) hlo hhi)
    hgetTemplate hval

theorem setFeeProtocolArg0Word_clean (I : ExecutionEnv) :
    UInt256.land (setFeeProtocolArg0Word I) ⟨255⟩ = setFeeProtocolArg0Word I := by
  have hmask : (⟨255⟩ : UInt256) = slot0Uint8Mask := by native_decide
  have hsource : setFeeProtocolUint8Mask = slot0Uint8Mask := by native_decide
  have hbound : (setFeeProtocolArg0Word I).toNat < EVM.twoPow 8 := by
    rw [setFeeProtocolArg0Word, hsource]
    exact slot0Uint8Mask_bound (calldataWord I.calldata 4)
  rw [hmask]
  exact slot0Uint8Mask_clean hbound

theorem setFeeProtocolArg1Word_clean (I : ExecutionEnv) :
    UInt256.land (setFeeProtocolArg1Word I) ⟨255⟩ = setFeeProtocolArg1Word I := by
  have hmask : (⟨255⟩ : UInt256) = slot0Uint8Mask := by native_decide
  have hsource : setFeeProtocolUint8Mask = slot0Uint8Mask := by native_decide
  have hbound : (setFeeProtocolArg1Word I).toNat < EVM.twoPow 8 := by
    rw [setFeeProtocolArg1Word, hsource]
    exact slot0Uint8Mask_bound (calldataWord I.calldata 36)
  rw [hmask]
  exact slot0Uint8Mask_clean hbound

set_option maxHeartbeats 1000000 in
theorem uniswapV3PoolSetFeeProtocolFeeProtocol0ZeroTo8484 {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {R : List UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨8449⟩
      (setFeeProtocolArg1Word ee :: setFeeProtocolArg0Word ee :: R)
      mem aw rdata acc k C)
    (hzero : (setFeeProtocolArg0Word ee).toNat = 0)
    (hov : R.length + 5 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨8484⟩
      (⟨1⟩ :: setFeeProtocolArg1Word ee :: setFeeProtocolArg0Word ee :: R)
      mem aw rdata acc k' C' := by
  have hd8449 : decode code ⟨8449⟩ = some (.JUMPDEST, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8449⟩) (byte := 0x5b)
      (op := .JUMPDEST) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8450 : decode code ⟨8450⟩ = some (.Push .PUSH1, some (⟨255⟩, 1)) := by
    exact setFeeProtocolDecodePush1AfterFactory (pc := ⟨8450⟩)
      (n := ⟨255⟩) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have hd8452 : decode code ⟨8452⟩ = some (.DUP3, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8452⟩) (byte := 0x82)
      (op := .DUP3) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8453 : decode code ⟨8453⟩ = some (.AND, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8453⟩) (byte := 0x16)
      (op := .AND) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8454 : decode code ⟨8454⟩ = some (.ISZERO, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8454⟩) (byte := 0x15)
      (op := .ISZERO) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8455 : decode code ⟨8455⟩ = some (.DUP1, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8455⟩) (byte := 0x80)
      (op := .DUP1) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8456 : decode code ⟨8456⟩ = some (.Push .PUSH2, some (⟨8484⟩, 2)) := by
    exact setFeeProtocolDecodePush2AfterFactory (pc := ⟨8456⟩)
      (n := ⟨8484⟩) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have hd8459 : decode code ⟨8459⟩ = some (.JUMPI, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8459⟩) (byte := 0x57)
      (op := .JUMPI) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have harg0Zero : setFeeProtocolArg0Word ee = ⟨0⟩ :=
    uint256_toNat_eq_zero hzero
  have rd8459 := evm_run h with [
    raw jumpdest hd8449 (by evm_ov),
    raw push1 ⟨255⟩ hd8450 (by evm_ov),
    raw dup3 hd8452 (by evm_ov),
    raw and hd8453 (by evm_ov),
    raw iszero hd8454 (by evm_ov),
    raw dup1 hd8455 (by evm_ov),
    raw push2 ⟨8484⟩ hd8456 (by evm_ov)]
  rw [setFeeProtocolArg0Word_clean ee, harg0Zero] at rd8459
  have rd8484 := rd8459.jumpiT hd8459 (by decide)
    (uniswapV3PoolJumpDestPatched8484 hpatch) (by evm_ov)
  exact ⟨_, _, by simpa [harg0Zero] using rd8484⟩

set_option maxHeartbeats 1000000 in
theorem uniswapV3PoolSetFeeProtocolFeeProtocol0RangeTo8484 {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {R : List UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨8449⟩
      (setFeeProtocolArg1Word ee :: setFeeProtocolArg0Word ee :: R)
      mem aw rdata acc k C)
    (hge : 4 ≤ (setFeeProtocolArg0Word ee).toNat)
    (hle : (setFeeProtocolArg0Word ee).toNat ≤ 10)
    (hov : R.length + 5 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨8484⟩
      (⟨1⟩ :: setFeeProtocolArg1Word ee :: setFeeProtocolArg0Word ee :: R)
      mem aw rdata acc k' C' := by
  have hd8449 : decode code ⟨8449⟩ = some (.JUMPDEST, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8449⟩) (byte := 0x5b)
      (op := .JUMPDEST) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8450 : decode code ⟨8450⟩ = some (.Push .PUSH1, some (⟨255⟩, 1)) := by
    exact setFeeProtocolDecodePush1AfterFactory (pc := ⟨8450⟩)
      (n := ⟨255⟩) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have hd8452 : decode code ⟨8452⟩ = some (.DUP3, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8452⟩) (byte := 0x82)
      (op := .DUP3) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8453 : decode code ⟨8453⟩ = some (.AND, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8453⟩) (byte := 0x16)
      (op := .AND) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8454 : decode code ⟨8454⟩ = some (.ISZERO, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8454⟩) (byte := 0x15)
      (op := .ISZERO) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8455 : decode code ⟨8455⟩ = some (.DUP1, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8455⟩) (byte := 0x80)
      (op := .DUP1) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8456 : decode code ⟨8456⟩ = some (.Push .PUSH2, some (⟨8484⟩, 2)) := by
    exact setFeeProtocolDecodePush2AfterFactory (pc := ⟨8456⟩)
      (n := ⟨8484⟩) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have hd8459 : decode code ⟨8459⟩ = some (.JUMPI, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8459⟩) (byte := 0x57)
      (op := .JUMPI) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8460 : decode code ⟨8460⟩ = some (.POP, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8460⟩) (byte := 0x50)
      (op := .POP) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8461 : decode code ⟨8461⟩ = some (.Push .PUSH1, some (⟨4⟩, 1)) := by
    exact setFeeProtocolDecodePush1AfterFactory (pc := ⟨8461⟩)
      (n := ⟨4⟩) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have hd8463 : decode code ⟨8463⟩ = some (.DUP3, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8463⟩) (byte := 0x82)
      (op := .DUP3) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8464 : decode code ⟨8464⟩ = some (.Push .PUSH1, some (⟨255⟩, 1)) := by
    exact setFeeProtocolDecodePush1AfterFactory (pc := ⟨8464⟩)
      (n := ⟨255⟩) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have hd8466 : decode code ⟨8466⟩ = some (.AND, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8466⟩) (byte := 0x16)
      (op := .AND) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8467 : decode code ⟨8467⟩ = some (.LT, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8467⟩) (byte := 0x10)
      (op := .LT) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8468 : decode code ⟨8468⟩ = some (.ISZERO, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8468⟩) (byte := 0x15)
      (op := .ISZERO) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8469 : decode code ⟨8469⟩ = some (.DUP1, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8469⟩) (byte := 0x80)
      (op := .DUP1) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8470 : decode code ⟨8470⟩ = some (.ISZERO, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8470⟩) (byte := 0x15)
      (op := .ISZERO) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8471 : decode code ⟨8471⟩ = some (.Push .PUSH2, some (⟨8484⟩, 2)) := by
    exact setFeeProtocolDecodePush2AfterFactory (pc := ⟨8471⟩)
      (n := ⟨8484⟩) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have hd8474 : decode code ⟨8474⟩ = some (.JUMPI, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8474⟩) (byte := 0x57)
      (op := .JUMPI) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8475 : decode code ⟨8475⟩ = some (.POP, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8475⟩) (byte := 0x50)
      (op := .POP) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8476 : decode code ⟨8476⟩ = some (.Push .PUSH1, some (⟨10⟩, 1)) := by
    exact setFeeProtocolDecodePush1AfterFactory (pc := ⟨8476⟩)
      (n := ⟨10⟩) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have hd8478 : decode code ⟨8478⟩ = some (.DUP3, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8478⟩) (byte := 0x82)
      (op := .DUP3) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8479 : decode code ⟨8479⟩ = some (.Push .PUSH1, some (⟨255⟩, 1)) := by
    exact setFeeProtocolDecodePush1AfterFactory (pc := ⟨8479⟩)
      (n := ⟨255⟩) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have hd8481 : decode code ⟨8481⟩ = some (.AND, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8481⟩) (byte := 0x16)
      (op := .AND) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8482 : decode code ⟨8482⟩ = some (.GT, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8482⟩) (byte := 0x11)
      (op := .GT) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8483 : decode code ⟨8483⟩ = some (.ISZERO, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8483⟩) (byte := 0x15)
      (op := .ISZERO) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have harg0Ne : setFeeProtocolArg0Word ee ≠ ⟨0⟩ := by
    intro hbad
    have hbadNat := congrArg UInt256.toNat hbad
    simp at hbadNat
    omega
  have hlt0 : UInt256.lt (setFeeProtocolArg0Word ee) ⟨4⟩ = ⟨0⟩ := by
    exact ult_zero (by simpa using hge)
  have hgt0 : UInt256.gt (setFeeProtocolArg0Word ee) ⟨10⟩ = ⟨0⟩ := by
    exact ugt_zero (by simpa using hle)
  have rd8459 := evm_run h with [
    raw jumpdest hd8449 (by evm_ov),
    raw push1 ⟨255⟩ hd8450 (by evm_ov),
    raw dup3 hd8452 (by evm_ov),
    raw and hd8453 (by evm_ov),
    raw iszero hd8454 (by evm_ov),
    raw dup1 hd8455 (by evm_ov),
    raw push2 ⟨8484⟩ hd8456 (by evm_ov)]
  rw [setFeeProtocolArg0Word_clean ee, isZero_eq_zero_of_ne harg0Ne] at rd8459
  have rd8460 := rd8459.jumpiNT hd8459 (by decide) (by evm_ov)
  have rd8474 := evm_run rd8460 with [
    raw pop hd8460 (by evm_ov),
    raw push1 ⟨4⟩ hd8461 (by evm_ov),
    raw dup3 hd8463 (by evm_ov),
    raw push1 ⟨255⟩ hd8464 (by evm_ov),
    raw and hd8466 (by evm_ov),
    raw lt hd8467 (by evm_ov),
    raw iszero hd8468 (by evm_ov),
    raw dup1 hd8469 (by evm_ov),
    raw iszero hd8470 (by evm_ov),
    raw push2 ⟨8484⟩ hd8471 (by evm_ov)]
  rw [u256_land_comm ⟨255⟩ (setFeeProtocolArg0Word ee),
    setFeeProtocolArg0Word_clean ee, hlt0] at rd8474
  have rd8475 := rd8474.jumpiNT hd8474 (by decide) (by evm_ov)
  have rd8484 := evm_run rd8475 with [
    raw pop hd8475 (by evm_ov),
    raw push1 ⟨10⟩ hd8476 (by evm_ov),
    raw dup3 hd8478 (by evm_ov),
    raw push1 ⟨255⟩ hd8479 (by evm_ov),
    raw and hd8481 (by evm_ov),
    raw gt hd8482 (by evm_ov),
    raw iszero hd8483 (by evm_ov)]
  rw [u256_land_comm ⟨255⟩ (setFeeProtocolArg0Word ee),
    setFeeProtocolArg0Word_clean ee, hgt0] at rd8484
  exact ⟨_, _, by simpa using rd8484⟩

theorem uniswapV3PoolSetFeeProtocolFeeProtocol0EnabledTo8484 {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {R : List UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨8449⟩
      (setFeeProtocolArg1Word ee :: setFeeProtocolArg0Word ee :: R)
      mem aw rdata acc k C)
    (hfee0 : setFeeProtocolEnabledNat (setFeeProtocolArg0Word ee).toNat)
    (hov : R.length + 5 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨8484⟩
      (⟨1⟩ :: setFeeProtocolArg1Word ee :: setFeeProtocolArg0Word ee :: R)
      mem aw rdata acc k' C' := by
  rcases hfee0 with hzero | hrange
  · exact uniswapV3PoolSetFeeProtocolFeeProtocol0ZeroTo8484 hpatch h hzero hov
  · exact uniswapV3PoolSetFeeProtocolFeeProtocol0RangeTo8484 hpatch h
      hrange.1 hrange.2 hov

set_option maxHeartbeats 1000000 in
theorem uniswapV3PoolSetFeeProtocolFeeProtocolFalseAt8526Reverts {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {R : List UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨8526⟩ (⟨0⟩ :: R) mem aw rdata acc k C)
    (hov : R.length + 2 ≤ 1024) :
    RDrev code g s0 := by
  have hd8526 : decode code ⟨8526⟩ = some (.JUMPDEST, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8526⟩) (byte := 0x5b)
      (op := .JUMPDEST) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8527 : decode code ⟨8527⟩ = some (.Push .PUSH2, some (⟨8535⟩, 2)) := by
    exact setFeeProtocolDecodePush2AfterFactory (pc := ⟨8527⟩)
      (n := ⟨8535⟩) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have hd8530 : decode code ⟨8530⟩ = some (.JUMPI, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8530⟩) (byte := 0x57)
      (op := .JUMPI) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8531 : decode code ⟨8531⟩ = some (.Push .PUSH1, some (⟨0⟩, 1)) := by
    exact setFeeProtocolDecodePush1AfterFactory (pc := ⟨8531⟩)
      (n := ⟨0⟩) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have hd8533 : decode code ⟨8533⟩ = some (.DUP1, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8533⟩) (byte := 0x80)
      (op := .DUP1) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8534 : decode code ⟨8534⟩ = some (.REVERT, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8534⟩) (byte := 0xfd)
      (op := .REVERT) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have rd8530 := evm_run h with [
    raw jumpdest hd8526 (by evm_ov),
    raw push2 ⟨8535⟩ hd8527 (by evm_ov)]
  have rd8531 := rd8530.jumpiNT hd8530 (by decide) (by evm_ov)
  exact RD.solcPush1Dup1Revert0 rd8531 hd8531
    (by simpa [show (⟨8531⟩ : UInt256) + UInt256.ofNat 2 = ⟨8533⟩ by native_decide]
      using hd8533)
    (by simpa [
        show (⟨8531⟩ : UInt256) + UInt256.ofNat 2 + ⟨1⟩ = ⟨8534⟩ by native_decide]
      using hd8534)
    (by omega)

set_option maxHeartbeats 1000000 in
theorem uniswapV3PoolSetFeeProtocolFeeProtocolFalseAt8484Reverts {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {R : List UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨8484⟩ (⟨0⟩ :: R) mem aw rdata acc k C)
    (hov : R.length + 3 ≤ 1024) :
    RDrev code g s0 := by
  have hd8484 : decode code ⟨8484⟩ = some (.JUMPDEST, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8484⟩) (byte := 0x5b)
      (op := .JUMPDEST) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8485 : decode code ⟨8485⟩ = some (.DUP1, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8485⟩) (byte := 0x80)
      (op := .DUP1) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8486 : decode code ⟨8486⟩ = some (.ISZERO, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8486⟩) (byte := 0x15)
      (op := .ISZERO) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8487 : decode code ⟨8487⟩ = some (.Push .PUSH2, some (⟨8526⟩, 2)) := by
    exact setFeeProtocolDecodePush2AfterFactory (pc := ⟨8487⟩)
      (n := ⟨8526⟩) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have hd8490 : decode code ⟨8490⟩ = some (.JUMPI, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8490⟩) (byte := 0x57)
      (op := .JUMPI) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have rd8490 := evm_run h with [
    raw jumpdest hd8484 (by evm_ov),
    raw dup1 hd8485 (by evm_ov),
    raw iszero hd8486 (by evm_ov),
    raw push2 ⟨8526⟩ hd8487 (by evm_ov)]
  have rd8526 := rd8490.jumpiT hd8490 (by decide)
    (uniswapV3PoolJumpDestPatched8526 hpatch) (by evm_ov)
  exact uniswapV3PoolSetFeeProtocolFeeProtocolFalseAt8526Reverts hpatch rd8526
    (by omega)

set_option maxHeartbeats 1000000 in
theorem uniswapV3PoolSetFeeProtocolFeeProtocolTrueAt8484To8492 {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {R : List UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨8484⟩ (⟨1⟩ :: R) mem aw rdata acc k C)
    (hov : R.length + 3 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨8492⟩ R mem aw rdata acc k' C' := by
  have hd8484 : decode code ⟨8484⟩ = some (.JUMPDEST, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8484⟩) (byte := 0x5b)
      (op := .JUMPDEST) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8485 : decode code ⟨8485⟩ = some (.DUP1, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8485⟩) (byte := 0x80)
      (op := .DUP1) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8486 : decode code ⟨8486⟩ = some (.ISZERO, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8486⟩) (byte := 0x15)
      (op := .ISZERO) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8487 : decode code ⟨8487⟩ = some (.Push .PUSH2, some (⟨8526⟩, 2)) := by
    exact setFeeProtocolDecodePush2AfterFactory (pc := ⟨8487⟩)
      (n := ⟨8526⟩) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have hd8490 : decode code ⟨8490⟩ = some (.JUMPI, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8490⟩) (byte := 0x57)
      (op := .JUMPI) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8491 : decode code ⟨8491⟩ = some (.POP, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8491⟩) (byte := 0x50)
      (op := .POP) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have rd8490 := evm_run h with [
    raw jumpdest hd8484 (by evm_ov),
    raw dup1 hd8485 (by evm_ov),
    raw iszero hd8486 (by evm_ov),
    raw push2 ⟨8526⟩ hd8487 (by evm_ov)]
  have rd8491 := rd8490.jumpiNT hd8490 (by decide) (by evm_ov)
  exact ⟨_, _, by
    simpa [show
        (⟨8484⟩ : UInt256) + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 3 + ⟨1⟩ + ⟨1⟩ =
          ⟨8492⟩ by native_decide] using
      (evm_run rd8491 with [raw pop hd8491 (by evm_ov)])⟩

set_option maxHeartbeats 1000000 in
theorem uniswapV3PoolSetFeeProtocolFeeProtocol1ZeroTo8526 {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {R : List UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨8492⟩
      (setFeeProtocolArg1Word ee :: setFeeProtocolArg0Word ee :: R)
      mem aw rdata acc k C)
    (hzero : (setFeeProtocolArg1Word ee).toNat = 0)
    (hov : R.length + 5 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨8526⟩
      (⟨1⟩ :: setFeeProtocolArg1Word ee :: setFeeProtocolArg0Word ee :: R)
      mem aw rdata acc k' C' := by
  have hd8492 : decode code ⟨8492⟩ = some (.Push .PUSH1, some (⟨255⟩, 1)) := by
    exact setFeeProtocolDecodePush1AfterFactory (pc := ⟨8492⟩)
      (n := ⟨255⟩) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have hd8494 : decode code ⟨8494⟩ = some (.DUP2, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8494⟩) (byte := 0x81)
      (op := .DUP2) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8495 : decode code ⟨8495⟩ = some (.AND, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8495⟩) (byte := 0x16)
      (op := .AND) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8496 : decode code ⟨8496⟩ = some (.ISZERO, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8496⟩) (byte := 0x15)
      (op := .ISZERO) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8497 : decode code ⟨8497⟩ = some (.DUP1, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8497⟩) (byte := 0x80)
      (op := .DUP1) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8498 : decode code ⟨8498⟩ = some (.Push .PUSH2, some (⟨8526⟩, 2)) := by
    exact setFeeProtocolDecodePush2AfterFactory (pc := ⟨8498⟩)
      (n := ⟨8526⟩) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have hd8501 : decode code ⟨8501⟩ = some (.JUMPI, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8501⟩) (byte := 0x57)
      (op := .JUMPI) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have harg1Zero : setFeeProtocolArg1Word ee = ⟨0⟩ :=
    uint256_toNat_eq_zero hzero
  have rd8501 := evm_run h with [
    raw push1 ⟨255⟩ hd8492 (by evm_ov),
    raw dup2 hd8494 (by evm_ov),
    raw and hd8495 (by evm_ov),
    raw iszero hd8496 (by evm_ov),
    raw dup1 hd8497 (by evm_ov),
    raw push2 ⟨8526⟩ hd8498 (by evm_ov)]
  rw [setFeeProtocolArg1Word_clean ee, harg1Zero] at rd8501
  have rd8526 := rd8501.jumpiT hd8501 (by decide)
    (uniswapV3PoolJumpDestPatched8526 hpatch) (by evm_ov)
  exact ⟨_, _, by simpa [harg1Zero] using rd8526⟩

set_option maxHeartbeats 1000000 in
theorem uniswapV3PoolSetFeeProtocolFeeProtocol1RangeTo8526 {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {R : List UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨8492⟩
      (setFeeProtocolArg1Word ee :: setFeeProtocolArg0Word ee :: R)
      mem aw rdata acc k C)
    (hge : 4 ≤ (setFeeProtocolArg1Word ee).toNat)
    (hle : (setFeeProtocolArg1Word ee).toNat ≤ 10)
    (hov : R.length + 5 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨8526⟩
      (⟨1⟩ :: setFeeProtocolArg1Word ee :: setFeeProtocolArg0Word ee :: R)
      mem aw rdata acc k' C' := by
  have hd8492 : decode code ⟨8492⟩ = some (.Push .PUSH1, some (⟨255⟩, 1)) := by
    exact setFeeProtocolDecodePush1AfterFactory (pc := ⟨8492⟩)
      (n := ⟨255⟩) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have hd8494 : decode code ⟨8494⟩ = some (.DUP2, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8494⟩) (byte := 0x81)
      (op := .DUP2) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8495 : decode code ⟨8495⟩ = some (.AND, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8495⟩) (byte := 0x16)
      (op := .AND) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8496 : decode code ⟨8496⟩ = some (.ISZERO, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8496⟩) (byte := 0x15)
      (op := .ISZERO) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8497 : decode code ⟨8497⟩ = some (.DUP1, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8497⟩) (byte := 0x80)
      (op := .DUP1) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8498 : decode code ⟨8498⟩ = some (.Push .PUSH2, some (⟨8526⟩, 2)) := by
    exact setFeeProtocolDecodePush2AfterFactory (pc := ⟨8498⟩)
      (n := ⟨8526⟩) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have hd8501 : decode code ⟨8501⟩ = some (.JUMPI, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8501⟩) (byte := 0x57)
      (op := .JUMPI) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8502 : decode code ⟨8502⟩ = some (.POP, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8502⟩) (byte := 0x50)
      (op := .POP) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8503 : decode code ⟨8503⟩ = some (.Push .PUSH1, some (⟨4⟩, 1)) := by
    exact setFeeProtocolDecodePush1AfterFactory (pc := ⟨8503⟩)
      (n := ⟨4⟩) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have hd8505 : decode code ⟨8505⟩ = some (.DUP2, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8505⟩) (byte := 0x81)
      (op := .DUP2) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8506 : decode code ⟨8506⟩ = some (.Push .PUSH1, some (⟨255⟩, 1)) := by
    exact setFeeProtocolDecodePush1AfterFactory (pc := ⟨8506⟩)
      (n := ⟨255⟩) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have hd8508 : decode code ⟨8508⟩ = some (.AND, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8508⟩) (byte := 0x16)
      (op := .AND) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8509 : decode code ⟨8509⟩ = some (.LT, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8509⟩) (byte := 0x10)
      (op := .LT) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8510 : decode code ⟨8510⟩ = some (.ISZERO, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8510⟩) (byte := 0x15)
      (op := .ISZERO) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8511 : decode code ⟨8511⟩ = some (.DUP1, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8511⟩) (byte := 0x80)
      (op := .DUP1) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8512 : decode code ⟨8512⟩ = some (.ISZERO, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8512⟩) (byte := 0x15)
      (op := .ISZERO) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8513 : decode code ⟨8513⟩ = some (.Push .PUSH2, some (⟨8526⟩, 2)) := by
    exact setFeeProtocolDecodePush2AfterFactory (pc := ⟨8513⟩)
      (n := ⟨8526⟩) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have hd8516 : decode code ⟨8516⟩ = some (.JUMPI, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8516⟩) (byte := 0x57)
      (op := .JUMPI) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8517 : decode code ⟨8517⟩ = some (.POP, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8517⟩) (byte := 0x50)
      (op := .POP) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8518 : decode code ⟨8518⟩ = some (.Push .PUSH1, some (⟨10⟩, 1)) := by
    exact setFeeProtocolDecodePush1AfterFactory (pc := ⟨8518⟩)
      (n := ⟨10⟩) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have hd8520 : decode code ⟨8520⟩ = some (.DUP2, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8520⟩) (byte := 0x81)
      (op := .DUP2) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8521 : decode code ⟨8521⟩ = some (.Push .PUSH1, some (⟨255⟩, 1)) := by
    exact setFeeProtocolDecodePush1AfterFactory (pc := ⟨8521⟩)
      (n := ⟨255⟩) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have hd8523 : decode code ⟨8523⟩ = some (.AND, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8523⟩) (byte := 0x16)
      (op := .AND) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8524 : decode code ⟨8524⟩ = some (.GT, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8524⟩) (byte := 0x11)
      (op := .GT) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8525 : decode code ⟨8525⟩ = some (.ISZERO, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8525⟩) (byte := 0x15)
      (op := .ISZERO) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have harg1Ne : setFeeProtocolArg1Word ee ≠ ⟨0⟩ := by
    intro hbad
    have hbadNat := congrArg UInt256.toNat hbad
    simp at hbadNat
    omega
  have hlt0 : UInt256.lt (setFeeProtocolArg1Word ee) ⟨4⟩ = ⟨0⟩ := by
    exact ult_zero (by simpa using hge)
  have hgt0 : UInt256.gt (setFeeProtocolArg1Word ee) ⟨10⟩ = ⟨0⟩ := by
    exact ugt_zero (by simpa using hle)
  have rd8501 := evm_run h with [
    raw push1 ⟨255⟩ hd8492 (by evm_ov),
    raw dup2 hd8494 (by evm_ov),
    raw and hd8495 (by evm_ov),
    raw iszero hd8496 (by evm_ov),
    raw dup1 hd8497 (by evm_ov),
    raw push2 ⟨8526⟩ hd8498 (by evm_ov)]
  rw [setFeeProtocolArg1Word_clean ee, isZero_eq_zero_of_ne harg1Ne] at rd8501
  have rd8502 := rd8501.jumpiNT hd8501 (by decide) (by evm_ov)
  have rd8516 := evm_run rd8502 with [
    raw pop hd8502 (by evm_ov),
    raw push1 ⟨4⟩ hd8503 (by evm_ov),
    raw dup2 hd8505 (by evm_ov),
    raw push1 ⟨255⟩ hd8506 (by evm_ov),
    raw and hd8508 (by evm_ov),
    raw lt hd8509 (by evm_ov),
    raw iszero hd8510 (by evm_ov),
    raw dup1 hd8511 (by evm_ov),
    raw iszero hd8512 (by evm_ov),
    raw push2 ⟨8526⟩ hd8513 (by evm_ov)]
  rw [u256_land_comm ⟨255⟩ (setFeeProtocolArg1Word ee),
    setFeeProtocolArg1Word_clean ee, hlt0] at rd8516
  have rd8517 := rd8516.jumpiNT hd8516 (by decide) (by evm_ov)
  have rd8526 := evm_run rd8517 with [
    raw pop hd8517 (by evm_ov),
    raw push1 ⟨10⟩ hd8518 (by evm_ov),
    raw dup2 hd8520 (by evm_ov),
    raw push1 ⟨255⟩ hd8521 (by evm_ov),
    raw and hd8523 (by evm_ov),
    raw gt hd8524 (by evm_ov),
    raw iszero hd8525 (by evm_ov)]
  rw [u256_land_comm ⟨255⟩ (setFeeProtocolArg1Word ee),
    setFeeProtocolArg1Word_clean ee, hgt0] at rd8526
  exact ⟨_, _, by simpa using rd8526⟩

theorem uniswapV3PoolSetFeeProtocolFeeProtocol1EnabledTo8526 {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {R : List UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨8492⟩
      (setFeeProtocolArg1Word ee :: setFeeProtocolArg0Word ee :: R)
      mem aw rdata acc k C)
    (hfee1 : setFeeProtocolEnabledNat (setFeeProtocolArg1Word ee).toNat)
    (hov : R.length + 5 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨8526⟩
      (⟨1⟩ :: setFeeProtocolArg1Word ee :: setFeeProtocolArg0Word ee :: R)
      mem aw rdata acc k' C' := by
  rcases hfee1 with hzero | hrange
  · exact uniswapV3PoolSetFeeProtocolFeeProtocol1ZeroTo8526 hpatch h hzero hov
  · exact uniswapV3PoolSetFeeProtocolFeeProtocol1RangeTo8526 hpatch h
      hrange.1 hrange.2 hov

set_option maxHeartbeats 1000000 in
theorem uniswapV3PoolSetFeeProtocolFeeProtocol1NonzeroTo8502 {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {R : List UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨8492⟩
      (setFeeProtocolArg1Word ee :: setFeeProtocolArg0Word ee :: R)
      mem aw rdata acc k C)
    (hne : setFeeProtocolArg1Word ee ≠ ⟨0⟩)
    (hov : R.length + 5 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨8502⟩
      (⟨0⟩ :: setFeeProtocolArg1Word ee :: setFeeProtocolArg0Word ee :: R)
      mem aw rdata acc k' C' := by
  have hd8492 : decode code ⟨8492⟩ = some (.Push .PUSH1, some (⟨255⟩, 1)) := by
    exact setFeeProtocolDecodePush1AfterFactory (pc := ⟨8492⟩)
      (n := ⟨255⟩) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have hd8494 : decode code ⟨8494⟩ = some (.DUP2, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8494⟩) (byte := 0x81)
      (op := .DUP2) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8495 : decode code ⟨8495⟩ = some (.AND, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8495⟩) (byte := 0x16)
      (op := .AND) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8496 : decode code ⟨8496⟩ = some (.ISZERO, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8496⟩) (byte := 0x15)
      (op := .ISZERO) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8497 : decode code ⟨8497⟩ = some (.DUP1, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8497⟩) (byte := 0x80)
      (op := .DUP1) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8498 : decode code ⟨8498⟩ = some (.Push .PUSH2, some (⟨8526⟩, 2)) := by
    exact setFeeProtocolDecodePush2AfterFactory (pc := ⟨8498⟩)
      (n := ⟨8526⟩) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have hd8501 : decode code ⟨8501⟩ = some (.JUMPI, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8501⟩) (byte := 0x57)
      (op := .JUMPI) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have rd8501 := evm_run h with [
    raw push1 ⟨255⟩ hd8492 (by evm_ov),
    raw dup2 hd8494 (by evm_ov),
    raw and hd8495 (by evm_ov),
    raw iszero hd8496 (by evm_ov),
    raw dup1 hd8497 (by evm_ov),
    raw push2 ⟨8526⟩ hd8498 (by evm_ov)]
  rw [setFeeProtocolArg1Word_clean ee, isZero_eq_zero_of_ne hne] at rd8501
  exact ⟨_, _, rd8501.jumpiNT hd8501 (by decide) (by evm_ov)⟩

set_option maxHeartbeats 1000000 in
theorem uniswapV3PoolSetFeeProtocolFeeProtocol1BelowTo8526False {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {R : List UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨8502⟩
      (⟨0⟩ :: setFeeProtocolArg1Word ee :: setFeeProtocolArg0Word ee :: R)
      mem aw rdata acc k C)
    (hlt : (setFeeProtocolArg1Word ee).toNat < 4)
    (hov : R.length + 5 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨8526⟩
      (⟨0⟩ :: setFeeProtocolArg1Word ee :: setFeeProtocolArg0Word ee :: R)
      mem aw rdata acc k' C' := by
  have hd8502 : decode code ⟨8502⟩ = some (.POP, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8502⟩) (byte := 0x50)
      (op := .POP) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8503 : decode code ⟨8503⟩ = some (.Push .PUSH1, some (⟨4⟩, 1)) := by
    exact setFeeProtocolDecodePush1AfterFactory (pc := ⟨8503⟩)
      (n := ⟨4⟩) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have hd8505 : decode code ⟨8505⟩ = some (.DUP2, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8505⟩) (byte := 0x81)
      (op := .DUP2) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8506 : decode code ⟨8506⟩ = some (.Push .PUSH1, some (⟨255⟩, 1)) := by
    exact setFeeProtocolDecodePush1AfterFactory (pc := ⟨8506⟩)
      (n := ⟨255⟩) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have hd8508 : decode code ⟨8508⟩ = some (.AND, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8508⟩) (byte := 0x16)
      (op := .AND) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8509 : decode code ⟨8509⟩ = some (.LT, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8509⟩) (byte := 0x10)
      (op := .LT) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8510 : decode code ⟨8510⟩ = some (.ISZERO, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8510⟩) (byte := 0x15)
      (op := .ISZERO) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8511 : decode code ⟨8511⟩ = some (.DUP1, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8511⟩) (byte := 0x80)
      (op := .DUP1) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8512 : decode code ⟨8512⟩ = some (.ISZERO, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8512⟩) (byte := 0x15)
      (op := .ISZERO) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8513 : decode code ⟨8513⟩ = some (.Push .PUSH2, some (⟨8526⟩, 2)) := by
    exact setFeeProtocolDecodePush2AfterFactory (pc := ⟨8513⟩)
      (n := ⟨8526⟩) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have hd8516 : decode code ⟨8516⟩ = some (.JUMPI, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8516⟩) (byte := 0x57)
      (op := .JUMPI) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hlt1 : UInt256.lt (setFeeProtocolArg1Word ee) ⟨4⟩ = ⟨1⟩ := by
    exact ult_one (by simpa using hlt)
  have rd8516 := evm_run h with [
    raw pop hd8502 (by evm_ov),
    raw push1 ⟨4⟩ hd8503 (by evm_ov),
    raw dup2 hd8505 (by evm_ov),
    raw push1 ⟨255⟩ hd8506 (by evm_ov),
    raw and hd8508 (by evm_ov),
    raw lt hd8509 (by evm_ov),
    raw iszero hd8510 (by evm_ov),
    raw dup1 hd8511 (by evm_ov),
    raw iszero hd8512 (by evm_ov),
    raw push2 ⟨8526⟩ hd8513 (by evm_ov)]
  rw [u256_land_comm ⟨255⟩ (setFeeProtocolArg1Word ee),
    setFeeProtocolArg1Word_clean ee, hlt1] at rd8516
  exact ⟨_, _, rd8516.jumpiT hd8516 (by decide)
    (uniswapV3PoolJumpDestPatched8526 hpatch) (by evm_ov)⟩

set_option maxHeartbeats 1000000 in
theorem uniswapV3PoolSetFeeProtocolFeeProtocol1AboveTo8526False {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {R : List UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨8502⟩
      (⟨0⟩ :: setFeeProtocolArg1Word ee :: setFeeProtocolArg0Word ee :: R)
      mem aw rdata acc k C)
    (hge : 4 ≤ (setFeeProtocolArg1Word ee).toNat)
    (hgt : 10 < (setFeeProtocolArg1Word ee).toNat)
    (hov : R.length + 5 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨8526⟩
      (⟨0⟩ :: setFeeProtocolArg1Word ee :: setFeeProtocolArg0Word ee :: R)
      mem aw rdata acc k' C' := by
  have hd8502 : decode code ⟨8502⟩ = some (.POP, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8502⟩) (byte := 0x50)
      (op := .POP) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8503 : decode code ⟨8503⟩ = some (.Push .PUSH1, some (⟨4⟩, 1)) := by
    exact setFeeProtocolDecodePush1AfterFactory (pc := ⟨8503⟩)
      (n := ⟨4⟩) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have hd8505 : decode code ⟨8505⟩ = some (.DUP2, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8505⟩) (byte := 0x81)
      (op := .DUP2) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8506 : decode code ⟨8506⟩ = some (.Push .PUSH1, some (⟨255⟩, 1)) := by
    exact setFeeProtocolDecodePush1AfterFactory (pc := ⟨8506⟩)
      (n := ⟨255⟩) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have hd8508 : decode code ⟨8508⟩ = some (.AND, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8508⟩) (byte := 0x16)
      (op := .AND) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8509 : decode code ⟨8509⟩ = some (.LT, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8509⟩) (byte := 0x10)
      (op := .LT) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8510 : decode code ⟨8510⟩ = some (.ISZERO, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8510⟩) (byte := 0x15)
      (op := .ISZERO) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8511 : decode code ⟨8511⟩ = some (.DUP1, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8511⟩) (byte := 0x80)
      (op := .DUP1) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8512 : decode code ⟨8512⟩ = some (.ISZERO, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8512⟩) (byte := 0x15)
      (op := .ISZERO) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8513 : decode code ⟨8513⟩ = some (.Push .PUSH2, some (⟨8526⟩, 2)) := by
    exact setFeeProtocolDecodePush2AfterFactory (pc := ⟨8513⟩)
      (n := ⟨8526⟩) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have hd8516 : decode code ⟨8516⟩ = some (.JUMPI, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8516⟩) (byte := 0x57)
      (op := .JUMPI) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8517 : decode code ⟨8517⟩ = some (.POP, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8517⟩) (byte := 0x50)
      (op := .POP) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8518 : decode code ⟨8518⟩ = some (.Push .PUSH1, some (⟨10⟩, 1)) := by
    exact setFeeProtocolDecodePush1AfterFactory (pc := ⟨8518⟩)
      (n := ⟨10⟩) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have hd8520 : decode code ⟨8520⟩ = some (.DUP2, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8520⟩) (byte := 0x81)
      (op := .DUP2) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8521 : decode code ⟨8521⟩ = some (.Push .PUSH1, some (⟨255⟩, 1)) := by
    exact setFeeProtocolDecodePush1AfterFactory (pc := ⟨8521⟩)
      (n := ⟨255⟩) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have hd8523 : decode code ⟨8523⟩ = some (.AND, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8523⟩) (byte := 0x16)
      (op := .AND) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8524 : decode code ⟨8524⟩ = some (.GT, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8524⟩) (byte := 0x11)
      (op := .GT) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8525 : decode code ⟨8525⟩ = some (.ISZERO, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8525⟩) (byte := 0x15)
      (op := .ISZERO) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hlt0 : UInt256.lt (setFeeProtocolArg1Word ee) ⟨4⟩ = ⟨0⟩ := by
    exact ult_zero (by simpa using hge)
  have hgt1 : UInt256.gt (setFeeProtocolArg1Word ee) ⟨10⟩ = ⟨1⟩ := by
    exact ugt_one (by simpa using hgt)
  have rd8516 := evm_run h with [
    raw pop hd8502 (by evm_ov),
    raw push1 ⟨4⟩ hd8503 (by evm_ov),
    raw dup2 hd8505 (by evm_ov),
    raw push1 ⟨255⟩ hd8506 (by evm_ov),
    raw and hd8508 (by evm_ov),
    raw lt hd8509 (by evm_ov),
    raw iszero hd8510 (by evm_ov),
    raw dup1 hd8511 (by evm_ov),
    raw iszero hd8512 (by evm_ov),
    raw push2 ⟨8526⟩ hd8513 (by evm_ov)]
  rw [u256_land_comm ⟨255⟩ (setFeeProtocolArg1Word ee),
    setFeeProtocolArg1Word_clean ee, hlt0] at rd8516
  have rd8517 := rd8516.jumpiNT hd8516 (by decide) (by evm_ov)
  have rd8526 := evm_run rd8517 with [
    raw pop hd8517 (by evm_ov),
    raw push1 ⟨10⟩ hd8518 (by evm_ov),
    raw dup2 hd8520 (by evm_ov),
    raw push1 ⟨255⟩ hd8521 (by evm_ov),
    raw and hd8523 (by evm_ov),
    raw gt hd8524 (by evm_ov),
    raw iszero hd8525 (by evm_ov)]
  rw [u256_land_comm ⟨255⟩ (setFeeProtocolArg1Word ee),
    setFeeProtocolArg1Word_clean ee, hgt1] at rd8526
  exact ⟨_, _, by simpa using rd8526⟩

theorem uniswapV3PoolSetFeeProtocolFeeProtocol1DisabledReverts {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {R : List UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨8492⟩
      (setFeeProtocolArg1Word ee :: setFeeProtocolArg0Word ee :: R)
      mem aw rdata acc k C)
    (hbad : ¬ setFeeProtocolEnabledNat (setFeeProtocolArg1Word ee).toNat)
    (hov : R.length + 5 ≤ 1024) :
    RDrev code g s0 := by
  have hne : setFeeProtocolArg1Word ee ≠ ⟨0⟩ := by
    intro hzero
    have hzeroNat := congrArg UInt256.toNat hzero
    simp at hzeroNat
    exact hbad (Or.inl hzeroNat)
  obtain ⟨_, _, rd8502⟩ :=
    uniswapV3PoolSetFeeProtocolFeeProtocol1NonzeroTo8502 hpatch h hne hov
  by_cases hge : 4 ≤ (setFeeProtocolArg1Word ee).toNat
  · have hnle : ¬ (setFeeProtocolArg1Word ee).toNat ≤ 10 := by
      intro hle
      exact hbad (Or.inr ⟨hge, hle⟩)
    obtain ⟨_, _, rd8526⟩ :=
      uniswapV3PoolSetFeeProtocolFeeProtocol1AboveTo8526False hpatch rd8502 hge
        (Nat.lt_of_not_ge hnle) hov
    exact uniswapV3PoolSetFeeProtocolFeeProtocolFalseAt8526Reverts hpatch rd8526
      (by simp only [List.length_cons]; omega)
  · obtain ⟨_, _, rd8526⟩ :=
      uniswapV3PoolSetFeeProtocolFeeProtocol1BelowTo8526False hpatch rd8502
        (Nat.lt_of_not_ge hge) hov
    exact uniswapV3PoolSetFeeProtocolFeeProtocolFalseAt8526Reverts hpatch rd8526
      (by simp only [List.length_cons]; omega)

set_option maxHeartbeats 1000000 in
theorem uniswapV3PoolSetFeeProtocolFeeProtocol0NonzeroTo8460 {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {R : List UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨8449⟩
      (setFeeProtocolArg1Word ee :: setFeeProtocolArg0Word ee :: R)
      mem aw rdata acc k C)
    (hne : setFeeProtocolArg0Word ee ≠ ⟨0⟩)
    (hov : R.length + 5 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨8460⟩
      (⟨0⟩ :: setFeeProtocolArg1Word ee :: setFeeProtocolArg0Word ee :: R)
      mem aw rdata acc k' C' := by
  have hd8449 : decode code ⟨8449⟩ = some (.JUMPDEST, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8449⟩) (byte := 0x5b)
      (op := .JUMPDEST) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8450 : decode code ⟨8450⟩ = some (.Push .PUSH1, some (⟨255⟩, 1)) := by
    exact setFeeProtocolDecodePush1AfterFactory (pc := ⟨8450⟩)
      (n := ⟨255⟩) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have hd8452 : decode code ⟨8452⟩ = some (.DUP3, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8452⟩) (byte := 0x82)
      (op := .DUP3) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8453 : decode code ⟨8453⟩ = some (.AND, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8453⟩) (byte := 0x16)
      (op := .AND) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8454 : decode code ⟨8454⟩ = some (.ISZERO, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8454⟩) (byte := 0x15)
      (op := .ISZERO) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8455 : decode code ⟨8455⟩ = some (.DUP1, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8455⟩) (byte := 0x80)
      (op := .DUP1) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8456 : decode code ⟨8456⟩ = some (.Push .PUSH2, some (⟨8484⟩, 2)) := by
    exact setFeeProtocolDecodePush2AfterFactory (pc := ⟨8456⟩)
      (n := ⟨8484⟩) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have hd8459 : decode code ⟨8459⟩ = some (.JUMPI, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8459⟩) (byte := 0x57)
      (op := .JUMPI) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have rd8459 := evm_run h with [
    raw jumpdest hd8449 (by evm_ov),
    raw push1 ⟨255⟩ hd8450 (by evm_ov),
    raw dup3 hd8452 (by evm_ov),
    raw and hd8453 (by evm_ov),
    raw iszero hd8454 (by evm_ov),
    raw dup1 hd8455 (by evm_ov),
    raw push2 ⟨8484⟩ hd8456 (by evm_ov)]
  rw [setFeeProtocolArg0Word_clean ee, isZero_eq_zero_of_ne hne] at rd8459
  exact ⟨_, _, rd8459.jumpiNT hd8459 (by decide) (by evm_ov)⟩

set_option maxHeartbeats 1000000 in
theorem uniswapV3PoolSetFeeProtocolFeeProtocol0BelowTo8484False {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {R : List UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨8460⟩
      (⟨0⟩ :: setFeeProtocolArg1Word ee :: setFeeProtocolArg0Word ee :: R)
      mem aw rdata acc k C)
    (hlt : (setFeeProtocolArg0Word ee).toNat < 4)
    (hov : R.length + 5 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨8484⟩
      (⟨0⟩ :: setFeeProtocolArg1Word ee :: setFeeProtocolArg0Word ee :: R)
      mem aw rdata acc k' C' := by
  have hd8460 : decode code ⟨8460⟩ = some (.POP, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8460⟩) (byte := 0x50)
      (op := .POP) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8461 : decode code ⟨8461⟩ = some (.Push .PUSH1, some (⟨4⟩, 1)) := by
    exact setFeeProtocolDecodePush1AfterFactory (pc := ⟨8461⟩)
      (n := ⟨4⟩) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have hd8463 : decode code ⟨8463⟩ = some (.DUP3, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8463⟩) (byte := 0x82)
      (op := .DUP3) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8464 : decode code ⟨8464⟩ = some (.Push .PUSH1, some (⟨255⟩, 1)) := by
    exact setFeeProtocolDecodePush1AfterFactory (pc := ⟨8464⟩)
      (n := ⟨255⟩) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have hd8466 : decode code ⟨8466⟩ = some (.AND, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8466⟩) (byte := 0x16)
      (op := .AND) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8467 : decode code ⟨8467⟩ = some (.LT, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8467⟩) (byte := 0x10)
      (op := .LT) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8468 : decode code ⟨8468⟩ = some (.ISZERO, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8468⟩) (byte := 0x15)
      (op := .ISZERO) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8469 : decode code ⟨8469⟩ = some (.DUP1, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8469⟩) (byte := 0x80)
      (op := .DUP1) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8470 : decode code ⟨8470⟩ = some (.ISZERO, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8470⟩) (byte := 0x15)
      (op := .ISZERO) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8471 : decode code ⟨8471⟩ = some (.Push .PUSH2, some (⟨8484⟩, 2)) := by
    exact setFeeProtocolDecodePush2AfterFactory (pc := ⟨8471⟩)
      (n := ⟨8484⟩) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have hd8474 : decode code ⟨8474⟩ = some (.JUMPI, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8474⟩) (byte := 0x57)
      (op := .JUMPI) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hlt1 : UInt256.lt (setFeeProtocolArg0Word ee) ⟨4⟩ = ⟨1⟩ := by
    exact ult_one (by simpa using hlt)
  have rd8474 := evm_run h with [
    raw pop hd8460 (by evm_ov),
    raw push1 ⟨4⟩ hd8461 (by evm_ov),
    raw dup3 hd8463 (by evm_ov),
    raw push1 ⟨255⟩ hd8464 (by evm_ov),
    raw and hd8466 (by evm_ov),
    raw lt hd8467 (by evm_ov),
    raw iszero hd8468 (by evm_ov),
    raw dup1 hd8469 (by evm_ov),
    raw iszero hd8470 (by evm_ov),
    raw push2 ⟨8484⟩ hd8471 (by evm_ov)]
  rw [u256_land_comm ⟨255⟩ (setFeeProtocolArg0Word ee),
    setFeeProtocolArg0Word_clean ee, hlt1] at rd8474
  exact ⟨_, _, rd8474.jumpiT hd8474 (by decide)
    (uniswapV3PoolJumpDestPatched8484 hpatch) (by evm_ov)⟩

set_option maxHeartbeats 1000000 in
theorem uniswapV3PoolSetFeeProtocolFeeProtocol0AboveTo8484False {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {R : List UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨8460⟩
      (⟨0⟩ :: setFeeProtocolArg1Word ee :: setFeeProtocolArg0Word ee :: R)
      mem aw rdata acc k C)
    (hge : 4 ≤ (setFeeProtocolArg0Word ee).toNat)
    (hgt : 10 < (setFeeProtocolArg0Word ee).toNat)
    (hov : R.length + 5 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨8484⟩
      (⟨0⟩ :: setFeeProtocolArg1Word ee :: setFeeProtocolArg0Word ee :: R)
      mem aw rdata acc k' C' := by
  have hd8460 : decode code ⟨8460⟩ = some (.POP, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8460⟩) (byte := 0x50)
      (op := .POP) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8461 : decode code ⟨8461⟩ = some (.Push .PUSH1, some (⟨4⟩, 1)) := by
    exact setFeeProtocolDecodePush1AfterFactory (pc := ⟨8461⟩)
      (n := ⟨4⟩) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have hd8463 : decode code ⟨8463⟩ = some (.DUP3, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8463⟩) (byte := 0x82)
      (op := .DUP3) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8464 : decode code ⟨8464⟩ = some (.Push .PUSH1, some (⟨255⟩, 1)) := by
    exact setFeeProtocolDecodePush1AfterFactory (pc := ⟨8464⟩)
      (n := ⟨255⟩) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have hd8466 : decode code ⟨8466⟩ = some (.AND, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8466⟩) (byte := 0x16)
      (op := .AND) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8467 : decode code ⟨8467⟩ = some (.LT, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8467⟩) (byte := 0x10)
      (op := .LT) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8468 : decode code ⟨8468⟩ = some (.ISZERO, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8468⟩) (byte := 0x15)
      (op := .ISZERO) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8469 : decode code ⟨8469⟩ = some (.DUP1, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8469⟩) (byte := 0x80)
      (op := .DUP1) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8470 : decode code ⟨8470⟩ = some (.ISZERO, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8470⟩) (byte := 0x15)
      (op := .ISZERO) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8471 : decode code ⟨8471⟩ = some (.Push .PUSH2, some (⟨8484⟩, 2)) := by
    exact setFeeProtocolDecodePush2AfterFactory (pc := ⟨8471⟩)
      (n := ⟨8484⟩) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have hd8474 : decode code ⟨8474⟩ = some (.JUMPI, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8474⟩) (byte := 0x57)
      (op := .JUMPI) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8475 : decode code ⟨8475⟩ = some (.POP, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8475⟩) (byte := 0x50)
      (op := .POP) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8476 : decode code ⟨8476⟩ = some (.Push .PUSH1, some (⟨10⟩, 1)) := by
    exact setFeeProtocolDecodePush1AfterFactory (pc := ⟨8476⟩)
      (n := ⟨10⟩) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have hd8478 : decode code ⟨8478⟩ = some (.DUP3, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8478⟩) (byte := 0x82)
      (op := .DUP3) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8479 : decode code ⟨8479⟩ = some (.Push .PUSH1, some (⟨255⟩, 1)) := by
    exact setFeeProtocolDecodePush1AfterFactory (pc := ⟨8479⟩)
      (n := ⟨255⟩) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have hd8481 : decode code ⟨8481⟩ = some (.AND, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8481⟩) (byte := 0x16)
      (op := .AND) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8482 : decode code ⟨8482⟩ = some (.GT, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8482⟩) (byte := 0x11)
      (op := .GT) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8483 : decode code ⟨8483⟩ = some (.ISZERO, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8483⟩) (byte := 0x15)
      (op := .ISZERO) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hlt0 : UInt256.lt (setFeeProtocolArg0Word ee) ⟨4⟩ = ⟨0⟩ := by
    exact ult_zero (by simpa using hge)
  have hgt1 : UInt256.gt (setFeeProtocolArg0Word ee) ⟨10⟩ = ⟨1⟩ := by
    exact ugt_one (by simpa using hgt)
  have rd8474 := evm_run h with [
    raw pop hd8460 (by evm_ov),
    raw push1 ⟨4⟩ hd8461 (by evm_ov),
    raw dup3 hd8463 (by evm_ov),
    raw push1 ⟨255⟩ hd8464 (by evm_ov),
    raw and hd8466 (by evm_ov),
    raw lt hd8467 (by evm_ov),
    raw iszero hd8468 (by evm_ov),
    raw dup1 hd8469 (by evm_ov),
    raw iszero hd8470 (by evm_ov),
    raw push2 ⟨8484⟩ hd8471 (by evm_ov)]
  rw [u256_land_comm ⟨255⟩ (setFeeProtocolArg0Word ee),
    setFeeProtocolArg0Word_clean ee, hlt0] at rd8474
  have rd8475 := rd8474.jumpiNT hd8474 (by decide) (by evm_ov)
  have rd8484 := evm_run rd8475 with [
    raw pop hd8475 (by evm_ov),
    raw push1 ⟨10⟩ hd8476 (by evm_ov),
    raw dup3 hd8478 (by evm_ov),
    raw push1 ⟨255⟩ hd8479 (by evm_ov),
    raw and hd8481 (by evm_ov),
    raw gt hd8482 (by evm_ov),
    raw iszero hd8483 (by evm_ov)]
  rw [u256_land_comm ⟨255⟩ (setFeeProtocolArg0Word ee),
    setFeeProtocolArg0Word_clean ee, hgt1] at rd8484
  exact ⟨_, _, by simpa using rd8484⟩

theorem uniswapV3PoolSetFeeProtocolFeeProtocol0DisabledReverts {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {R : List UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨8449⟩
      (setFeeProtocolArg1Word ee :: setFeeProtocolArg0Word ee :: R)
      mem aw rdata acc k C)
    (hbad : ¬ setFeeProtocolEnabledNat (setFeeProtocolArg0Word ee).toNat)
    (hov : R.length + 5 ≤ 1024) :
    RDrev code g s0 := by
  have hne : setFeeProtocolArg0Word ee ≠ ⟨0⟩ := by
    intro hzero
    have hzeroNat := congrArg UInt256.toNat hzero
    simp at hzeroNat
    exact hbad (Or.inl hzeroNat)
  obtain ⟨_, _, rd8460⟩ :=
    uniswapV3PoolSetFeeProtocolFeeProtocol0NonzeroTo8460 hpatch h hne hov
  by_cases hge : 4 ≤ (setFeeProtocolArg0Word ee).toNat
  · have hnle : ¬ (setFeeProtocolArg0Word ee).toNat ≤ 10 := by
      intro hle
      exact hbad (Or.inr ⟨hge, hle⟩)
    obtain ⟨_, _, rd8484⟩ :=
      uniswapV3PoolSetFeeProtocolFeeProtocol0AboveTo8484False hpatch rd8460 hge
        (Nat.lt_of_not_ge hnle) hov
    exact uniswapV3PoolSetFeeProtocolFeeProtocolFalseAt8484Reverts hpatch rd8484
      (by simp only [List.length_cons]; omega)
  · obtain ⟨_, _, rd8484⟩ :=
      uniswapV3PoolSetFeeProtocolFeeProtocol0BelowTo8484False hpatch rd8460
        (Nat.lt_of_not_ge hge) hov
    exact uniswapV3PoolSetFeeProtocolFeeProtocolFalseAt8484Reverts hpatch rd8484
      (by simp only [List.length_cons]; omega)

set_option maxHeartbeats 1000000 in
theorem uniswapV3PoolSetFeeProtocolFeeProtocolTrueAt8526To8535 {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {R : List UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨8526⟩ (⟨1⟩ :: R) mem aw rdata acc k C)
    (hov : R.length + 2 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨8535⟩ R mem aw rdata acc k' C' := by
  have hd8526 : decode code ⟨8526⟩ = some (.JUMPDEST, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8526⟩) (byte := 0x5b)
      (op := .JUMPDEST) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8527 : decode code ⟨8527⟩ = some (.Push .PUSH2, some (⟨8535⟩, 2)) := by
    exact setFeeProtocolDecodePush2AfterFactory (pc := ⟨8527⟩)
      (n := ⟨8535⟩) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have hd8530 : decode code ⟨8530⟩ = some (.JUMPI, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8530⟩) (byte := 0x57)
      (op := .JUMPI) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have rd8530 := evm_run h with [
    raw jumpdest hd8526 (by evm_ov),
    raw push2 ⟨8535⟩ hd8527 (by evm_ov)]
  have rd8535 := rd8530.jumpiT hd8530 (by decide)
    (uniswapV3PoolJumpDestPatched8535 hpatch) (by evm_ov)
  exact ⟨_, _, by simpa using rd8535⟩

theorem uniswapV3PoolSetFeeProtocolFeeProtocolGuardsOk {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {R : List UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨8449⟩
      (setFeeProtocolArg1Word ee :: setFeeProtocolArg0Word ee :: R)
      mem aw rdata acc k C)
    (hfee0 : setFeeProtocolEnabledNat (setFeeProtocolArg0Word ee).toNat)
    (hfee1 : setFeeProtocolEnabledNat (setFeeProtocolArg1Word ee).toNat)
    (hov : R.length + 5 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨8535⟩
      (setFeeProtocolArg1Word ee :: setFeeProtocolArg0Word ee :: R)
      mem aw rdata acc k' C' := by
  obtain ⟨_, _, rd8484⟩ :=
    uniswapV3PoolSetFeeProtocolFeeProtocol0EnabledTo8484 hpatch h hfee0 hov
  obtain ⟨_, _, rd8492⟩ :=
    uniswapV3PoolSetFeeProtocolFeeProtocolTrueAt8484To8492 hpatch rd8484
      (by simp only [List.length_cons]; omega)
  obtain ⟨_, _, rd8526⟩ :=
    uniswapV3PoolSetFeeProtocolFeeProtocol1EnabledTo8526 hpatch rd8492 hfee1 hov
  exact uniswapV3PoolSetFeeProtocolFeeProtocolTrueAt8526To8535 hpatch rd8526
    (by simp only [List.length_cons]; omega)

theorem uniswapV3PoolSetFeeProtocolFeeProtocolGuardsRevert {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {R : List UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨8449⟩
      (setFeeProtocolArg1Word ee :: setFeeProtocolArg0Word ee :: R)
      mem aw rdata acc k C)
    (hbad :
      ¬(setFeeProtocolEnabledNat (setFeeProtocolArg0Word ee).toNat ∧
        setFeeProtocolEnabledNat (setFeeProtocolArg1Word ee).toNat))
    (hov : R.length + 5 ≤ 1024) :
    RDrev code g s0 := by
  by_cases hfee0 : setFeeProtocolEnabledNat (setFeeProtocolArg0Word ee).toNat
  · have hfee1 : ¬ setFeeProtocolEnabledNat (setFeeProtocolArg1Word ee).toNat := by
      intro hfee1
      exact hbad ⟨hfee0, hfee1⟩
    obtain ⟨_, _, rd8484⟩ :=
      uniswapV3PoolSetFeeProtocolFeeProtocol0EnabledTo8484 hpatch h hfee0 hov
    obtain ⟨_, _, rd8492⟩ :=
      uniswapV3PoolSetFeeProtocolFeeProtocolTrueAt8484To8492 hpatch rd8484
        (by simp only [List.length_cons]; omega)
    exact uniswapV3PoolSetFeeProtocolFeeProtocol1DisabledReverts hpatch rd8492 hfee1 hov
  · exact uniswapV3PoolSetFeeProtocolFeeProtocol0DisabledReverts hpatch h hfee0 hov

theorem setFeeProtocolStoreWithOwner_feeProtocol0 (I : ExecutionEnv) (out : ByteArray) :
    (setFeeProtocolStoreWithOwner I out).get? "feeProtocol0" =
      some (setFeeProtocolArg0Value I) := by
  rw [setFeeProtocolStoreWithOwner]
  rw [store_get_ne (setFeeProtocolStore I) (.address (setFeeProtocolOwnerAddress out))
    (by decide)]
  exact setFeeProtocolStore_feeProtocol0 I

theorem setFeeProtocolStoreWithOwner_feeProtocol1 (I : ExecutionEnv) (out : ByteArray) :
    (setFeeProtocolStoreWithOwner I out).get? "feeProtocol1" =
      some (setFeeProtocolArg1Value I) := by
  rw [setFeeProtocolStoreWithOwner]
  rw [store_get_ne (setFeeProtocolStore I) (.address (setFeeProtocolOwnerAddress out))
    (by decide)]
  exact setFeeProtocolStore_feeProtocol1 I

theorem evalExpr_setFeeProtocol_feeProtocol0_withOwner {v : PoolImmutables}
    (evm : EVM.State) (I : ExecutionEnv) (out : ByteArray) :
    evalExpr? (config v) { contract := contract v, locals := setFeeProtocolStoreWithOwner I out }
      evm (.var "feeProtocol0") = .ok (setFeeProtocolArg0Value I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [setFeeProtocolStoreWithOwner_feeProtocol0]

theorem evalExpr_setFeeProtocol_feeProtocol1_withOwner {v : PoolImmutables}
    (evm : EVM.State) (I : ExecutionEnv) (out : ByteArray) :
    evalExpr? (config v) { contract := contract v, locals := setFeeProtocolStoreWithOwner I out }
      evm (.var "feeProtocol1") = .ok (setFeeProtocolArg1Value I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [setFeeProtocolStoreWithOwner_feeProtocol1]

theorem evalExpr_setFeeProtocol_feeProtocol0Enabled_true {v : PoolImmutables}
    (evm : EVM.State) (I : ExecutionEnv) (out : ByteArray)
    (h : setFeeProtocolEnabledNat (setFeeProtocolArg0Word I).toNat) :
    evalExpr? (config v) { contract := contract v, locals := setFeeProtocolStoreWithOwner I out }
      evm (feeProtocolEnabled (.var "feeProtocol0")) = .ok (.bool true) := by
  rcases h with hzero | hrange
  · simp only [feeProtocolEnabled, orE, andE, geE, leE, eqE, evalExpr?,
      evalExpr_setFeeProtocol_feeProtocol0_withOwner, bind, EvalResult.bind, evalBinaryOp?,
      pure]
    simp [setFeeProtocolArg0Value, hzero, BEq.beq]
  · have hne : ¬(setFeeProtocolArg0Word I).toNat = 0 := by omega
    simp only [feeProtocolEnabled, orE, andE, geE, leE, eqE, evalExpr?,
      evalExpr_setFeeProtocol_feeProtocol0_withOwner, bind, EvalResult.bind, evalBinaryOp?,
      pure]
    simp [setFeeProtocolArg0Value, hne, BEq.beq, hrange.1, hrange.2]

theorem evalExpr_setFeeProtocol_feeProtocol1Enabled_true {v : PoolImmutables}
    (evm : EVM.State) (I : ExecutionEnv) (out : ByteArray)
    (h : setFeeProtocolEnabledNat (setFeeProtocolArg1Word I).toNat) :
    evalExpr? (config v) { contract := contract v, locals := setFeeProtocolStoreWithOwner I out }
      evm (feeProtocolEnabled (.var "feeProtocol1")) = .ok (.bool true) := by
  rcases h with hzero | hrange
  · simp only [feeProtocolEnabled, orE, andE, geE, leE, eqE, evalExpr?,
      evalExpr_setFeeProtocol_feeProtocol1_withOwner, bind, EvalResult.bind, evalBinaryOp?,
      pure]
    simp [setFeeProtocolArg1Value, hzero, BEq.beq]
  · have hne : ¬(setFeeProtocolArg1Word I).toNat = 0 := by omega
    simp only [feeProtocolEnabled, orE, andE, geE, leE, eqE, evalExpr?,
      evalExpr_setFeeProtocol_feeProtocol1_withOwner, bind, EvalResult.bind, evalBinaryOp?,
      pure]
    simp [setFeeProtocolArg1Value, hne, BEq.beq, hrange.1, hrange.2]

theorem evalExpr_setFeeProtocol_feeProtocol0Enabled_false {v : PoolImmutables}
    (evm : EVM.State) (I : ExecutionEnv) (out : ByteArray)
    (h : ¬ setFeeProtocolEnabledNat (setFeeProtocolArg0Word I).toNat) :
    evalExpr? (config v) { contract := contract v, locals := setFeeProtocolStoreWithOwner I out }
      evm (feeProtocolEnabled (.var "feeProtocol0")) = .ok (.bool false) := by
  have hneZero : ¬(setFeeProtocolArg0Word I).toNat = 0 := by
    intro hzero
    exact h (Or.inl hzero)
  have hnotRange : ¬(4 ≤ (setFeeProtocolArg0Word I).toNat ∧
      (setFeeProtocolArg0Word I).toNat ≤ 10) := by
    intro hrange
    exact h (Or.inr hrange)
  by_cases hge : 4 ≤ (setFeeProtocolArg0Word I).toNat
  · have hnotLe : ¬(setFeeProtocolArg0Word I).toNat ≤ 10 := by
      intro hle
      exact hnotRange ⟨hge, hle⟩
    simp only [feeProtocolEnabled, orE, andE, geE, leE, eqE, evalExpr?,
      evalExpr_setFeeProtocol_feeProtocol0_withOwner, bind, EvalResult.bind, evalBinaryOp?,
      pure]
    simp [setFeeProtocolArg0Value, hneZero, hge, hnotLe, BEq.beq]
  · simp only [feeProtocolEnabled, orE, andE, geE, leE, eqE, evalExpr?,
      evalExpr_setFeeProtocol_feeProtocol0_withOwner, bind, EvalResult.bind, evalBinaryOp?,
      pure]
    simp [setFeeProtocolArg0Value, hneZero, hge, BEq.beq]

theorem evalExpr_setFeeProtocol_feeProtocol1Enabled_false {v : PoolImmutables}
    (evm : EVM.State) (I : ExecutionEnv) (out : ByteArray)
    (h : ¬ setFeeProtocolEnabledNat (setFeeProtocolArg1Word I).toNat) :
    evalExpr? (config v) { contract := contract v, locals := setFeeProtocolStoreWithOwner I out }
      evm (feeProtocolEnabled (.var "feeProtocol1")) = .ok (.bool false) := by
  have hneZero : ¬(setFeeProtocolArg1Word I).toNat = 0 := by
    intro hzero
    exact h (Or.inl hzero)
  have hnotRange : ¬(4 ≤ (setFeeProtocolArg1Word I).toNat ∧
      (setFeeProtocolArg1Word I).toNat ≤ 10) := by
    intro hrange
    exact h (Or.inr hrange)
  by_cases hge : 4 ≤ (setFeeProtocolArg1Word I).toNat
  · have hnotLe : ¬(setFeeProtocolArg1Word I).toNat ≤ 10 := by
      intro hle
      exact hnotRange ⟨hge, hle⟩
    simp only [feeProtocolEnabled, orE, andE, geE, leE, eqE, evalExpr?,
      evalExpr_setFeeProtocol_feeProtocol1_withOwner, bind, EvalResult.bind, evalBinaryOp?,
      pure]
    simp [setFeeProtocolArg1Value, hneZero, hge, hnotLe, BEq.beq]
  · simp only [feeProtocolEnabled, orE, andE, geE, leE, eqE, evalExpr?,
      evalExpr_setFeeProtocol_feeProtocol1_withOwner, bind, EvalResult.bind, evalBinaryOp?,
      pure]
    simp [setFeeProtocolArg1Value, hneZero, hge, BEq.beq]

theorem uniswapV3PoolSetFeeProtocolSourceFeeProtocolRequireSuccess {v : PoolImmutables}
    {evm evmOwner : EVM.State} {I : ExecutionEnv} {out : ByteArray}
    (howner :
      ExecBlock (config v) { contract := contract v, locals := setFeeProtocolStore I } evm
        [ .require (.binary .gt (.extCodeSize (addrLit v.factory)) (.intLit 0)),
          .externalCall (addrLit v.factory) "owner" (.intLit 0) [] "_factoryOwner"
            (perm := false),
          .require (eqE (.env .caller) (.var "_factoryOwner")) ]
        (.ok { contract := contract v, locals := setFeeProtocolStoreWithOwner I out } evmOwner))
    (hfee0 : setFeeProtocolEnabledNat (setFeeProtocolArg0Word I).toNat)
    (hfee1 : setFeeProtocolEnabledNat (setFeeProtocolArg1Word I).toNat) :
    ExecBlock (config v) { contract := contract v, locals := setFeeProtocolStore I } evm
      [ .require (.binary .gt (.extCodeSize (addrLit v.factory)) (.intLit 0)),
        .externalCall (addrLit v.factory) "owner" (.intLit 0) [] "_factoryOwner"
          (perm := false),
        .require (eqE (.env .caller) (.var "_factoryOwner")),
        .require
          (andE (feeProtocolEnabled (.var "feeProtocol0"))
            (feeProtocolEnabled (.var "feeProtocol1"))) ]
      (.ok { contract := contract v, locals := setFeeProtocolStoreWithOwner I out } evmOwner) := by
  have hreq :
      ExecBlock (config v) { contract := contract v, locals := setFeeProtocolStoreWithOwner I out }
        evmOwner
        [ .require
          (andE (feeProtocolEnabled (.var "feeProtocol0"))
            (feeProtocolEnabled (.var "feeProtocol1"))) ]
        (.ok { contract := contract v, locals := setFeeProtocolStoreWithOwner I out }
          evmOwner) := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · simp only [andE, evalExpr?, evalExpr_setFeeProtocol_feeProtocol0Enabled_true
        evmOwner I out hfee0, bind, EvalResult.bind]
      rw [evalExpr_setFeeProtocol_feeProtocol1Enabled_true evmOwner I out hfee1]
      rfl
    · exact ExecBlock.nil
  simpa using execBlock_append howner hreq

theorem uniswapV3PoolSetFeeProtocolSourceFeeProtocolRequireRevert {v : PoolImmutables}
    {evm evmOwner : EVM.State} {I : ExecutionEnv} {out : ByteArray}
    (howner :
      ExecBlock (config v) { contract := contract v, locals := setFeeProtocolStore I } evm
        [ .require (.binary .gt (.extCodeSize (addrLit v.factory)) (.intLit 0)),
          .externalCall (addrLit v.factory) "owner" (.intLit 0) [] "_factoryOwner"
            (perm := false),
          .require (eqE (.env .caller) (.var "_factoryOwner")) ]
        (.ok { contract := contract v, locals := setFeeProtocolStoreWithOwner I out } evmOwner))
    (hfee :
      ¬(setFeeProtocolEnabledNat (setFeeProtocolArg0Word I).toNat ∧
        setFeeProtocolEnabledNat (setFeeProtocolArg1Word I).toNat)) :
    ExecBlock (config v) { contract := contract v, locals := setFeeProtocolStore I } evm
      [ .require (.binary .gt (.extCodeSize (addrLit v.factory)) (.intLit 0)),
        .externalCall (addrLit v.factory) "owner" (.intLit 0) [] "_factoryOwner"
          (perm := false),
        .require (eqE (.env .caller) (.var "_factoryOwner")),
        .require
          (andE (feeProtocolEnabled (.var "feeProtocol0"))
            (feeProtocolEnabled (.var "feeProtocol1"))) ]
      .reverted := by
  have hreq :
      ExecBlock (config v) { contract := contract v, locals := setFeeProtocolStoreWithOwner I out }
        evmOwner
        [ .require
          (andE (feeProtocolEnabled (.var "feeProtocol0"))
            (feeProtocolEnabled (.var "feeProtocol1"))) ] .reverted := by
    by_cases hfee0 : setFeeProtocolEnabledNat (setFeeProtocolArg0Word I).toNat
    · have hfee1 : ¬ setFeeProtocolEnabledNat (setFeeProtocolArg1Word I).toNat := by
        intro hfee1
        exact hfee ⟨hfee0, hfee1⟩
      refine ExecBlock.consRevert (ExecStmt.requireFalse ?_)
      simp only [andE, evalExpr?, evalExpr_setFeeProtocol_feeProtocol0Enabled_true
        evmOwner I out hfee0, bind, EvalResult.bind]
      rw [evalExpr_setFeeProtocol_feeProtocol1Enabled_false evmOwner I out hfee1]
      rfl
    · refine ExecBlock.consRevert (ExecStmt.requireFalse ?_)
      simp only [andE, evalExpr?, evalExpr_setFeeProtocol_feeProtocol0Enabled_false
        evmOwner I out hfee0, bind, EvalResult.bind]
      rfl
  simpa using execBlock_append howner hreq

theorem uniswapV3PoolSetFeeProtocolSourceFeeProtocolRequireSuccessPrefixExact
    {v : PoolImmutables} {cA gh bl σ σ₀ A I} {g : Sat256}
    {evmOwner : EVM.State} {out : ByteArray}
    (hprefix :
      ExecBlock (config v) { contract := contract v, locals := setFeeProtocolStore I }
        (initState cA gh bl σ σ₀ g A I)
        [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
          .require (.storage (slot0F "unlocked")),
          .assign .storage (slot0F "unlocked") (.boolLit false),
          .require (.binary .gt (.extCodeSize (addrLit v.factory)) (.intLit 0)),
          .externalCall (addrLit v.factory) "owner" (.intLit 0) [] "_factoryOwner"
            (perm := false),
          .require (eqE (.env .caller) (.var "_factoryOwner")) ]
        (.ok { contract := contract v, locals := setFeeProtocolStoreWithOwner I out } evmOwner))
    (hfee0 : setFeeProtocolEnabledNat (setFeeProtocolArg0Word I).toNat)
    (hfee1 : setFeeProtocolEnabledNat (setFeeProtocolArg1Word I).toNat) :
    ExecBlock (config v) { contract := contract v, locals := setFeeProtocolStore I }
      (initState cA gh bl σ σ₀ g A I)
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .require (.storage (slot0F "unlocked")),
        .assign .storage (slot0F "unlocked") (.boolLit false),
        .require (.binary .gt (.extCodeSize (addrLit v.factory)) (.intLit 0)),
        .externalCall (addrLit v.factory) "owner" (.intLit 0) [] "_factoryOwner"
          (perm := false),
        .require (eqE (.env .caller) (.var "_factoryOwner")),
        .require
          (andE (feeProtocolEnabled (.var "feeProtocol0"))
            (feeProtocolEnabled (.var "feeProtocol1"))) ]
      (.ok { contract := contract v, locals := setFeeProtocolStoreWithOwner I out } evmOwner) := by
  have hreq :
      ExecBlock (config v) { contract := contract v, locals := setFeeProtocolStoreWithOwner I out }
        evmOwner
        [ .require
          (andE (feeProtocolEnabled (.var "feeProtocol0"))
            (feeProtocolEnabled (.var "feeProtocol1"))) ]
        (.ok { contract := contract v, locals := setFeeProtocolStoreWithOwner I out }
          evmOwner) := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · simp only [andE, evalExpr?, evalExpr_setFeeProtocol_feeProtocol0Enabled_true
        evmOwner I out hfee0, bind, EvalResult.bind]
      rw [evalExpr_setFeeProtocol_feeProtocol1Enabled_true evmOwner I out hfee1]
      rfl
    · exact ExecBlock.nil
  simpa using execBlock_append hprefix hreq

theorem uniswapV3PoolSetFeeProtocolSourceFeeProtocolRequireRevertBody
    {v : PoolImmutables} {cA gh bl σ σ₀ A I} {g : Sat256}
    {evmOwner : EVM.State} {out : ByteArray}
    (hprefix :
      ExecBlock (config v) { contract := contract v, locals := setFeeProtocolStore I }
        (initState cA gh bl σ σ₀ g A I)
        [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
          .require (.storage (slot0F "unlocked")),
          .assign .storage (slot0F "unlocked") (.boolLit false),
          .require (.binary .gt (.extCodeSize (addrLit v.factory)) (.intLit 0)),
          .externalCall (addrLit v.factory) "owner" (.intLit 0) [] "_factoryOwner"
            (perm := false),
          .require (eqE (.env .caller) (.var "_factoryOwner")) ]
        (.ok { contract := contract v, locals := setFeeProtocolStoreWithOwner I out } evmOwner))
    (hfee :
      ¬(setFeeProtocolEnabledNat (setFeeProtocolArg0Word I).toNat ∧
        setFeeProtocolEnabledNat (setFeeProtocolArg1Word I).toNat)) :
    ExecTransitionBody (config v) (contract v)
      (initState cA gh bl σ σ₀ g A I) (setFeeProtocolStore I)
      (setfeeprotocolTransition v).body .reverted := by
  change ExecTransitionBody (config v) (contract v)
      (initState cA gh bl σ σ₀ g A I) (setFeeProtocolStore I)
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .require (.storage (slot0F "unlocked")),
        .assign .storage (slot0F "unlocked") (.boolLit false),
        .require (.binary .gt (.extCodeSize (addrLit v.factory)) (.intLit 0)),
        .externalCall (addrLit v.factory) "owner" (.intLit 0) [] "_factoryOwner"
          (perm := false),
        .require (eqE (.env .caller) (.var "_factoryOwner")),
        .require
          (andE (feeProtocolEnabled (.var "feeProtocol0"))
            (feeProtocolEnabled (.var "feeProtocol1"))),
        .letDecl "feeProtocolOld" (some uint8) (.storage (slot0F "feeProtocol")),
        .assign .storage (slot0F "feeProtocol")
          (addE (.var "feeProtocol0") (shlE (.var "feeProtocol1") (.intLit 4))),
        .assign .storage (slot0F "unlocked") (.boolLit true) ] .reverted
  refine ExecFuncBody.execBlockRevert ?_
  have hfeeRevert :
      ExecBlock (config v) { contract := contract v, locals := setFeeProtocolStore I }
        (initState cA gh bl σ σ₀ g A I)
        [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
          .require (.storage (slot0F "unlocked")),
          .assign .storage (slot0F "unlocked") (.boolLit false),
          .require (.binary .gt (.extCodeSize (addrLit v.factory)) (.intLit 0)),
          .externalCall (addrLit v.factory) "owner" (.intLit 0) [] "_factoryOwner"
            (perm := false),
          .require (eqE (.env .caller) (.var "_factoryOwner")),
          .require
            (andE (feeProtocolEnabled (.var "feeProtocol0"))
              (feeProtocolEnabled (.var "feeProtocol1"))) ]
        .reverted := by
    have hreq :
        ExecBlock (config v) { contract := contract v, locals := setFeeProtocolStoreWithOwner I out }
          evmOwner
          [ .require
            (andE (feeProtocolEnabled (.var "feeProtocol0"))
              (feeProtocolEnabled (.var "feeProtocol1"))) ] .reverted := by
      by_cases hfee0 : setFeeProtocolEnabledNat (setFeeProtocolArg0Word I).toNat
      · have hfee1 : ¬ setFeeProtocolEnabledNat (setFeeProtocolArg1Word I).toNat := by
          intro hfee1
          exact hfee ⟨hfee0, hfee1⟩
        refine ExecBlock.consRevert (ExecStmt.requireFalse ?_)
        simp only [andE, evalExpr?, evalExpr_setFeeProtocol_feeProtocol0Enabled_true
          evmOwner I out hfee0, bind, EvalResult.bind]
        rw [evalExpr_setFeeProtocol_feeProtocol1Enabled_false evmOwner I out hfee1]
        rfl
      · refine ExecBlock.consRevert (ExecStmt.requireFalse ?_)
        simp only [andE, evalExpr?, evalExpr_setFeeProtocol_feeProtocol0Enabled_false
          evmOwner I out hfee0, bind, EvalResult.bind]
        rfl
    simpa using execBlock_append hprefix hreq
  exact execBlock_append_term (s2 :=
    [ .letDecl "feeProtocolOld" (some uint8) (.storage (slot0F "feeProtocol")),
      .assign .storage (slot0F "feeProtocol")
        (addE (.var "feeProtocol0") (shlE (.var "feeProtocol1") (.intLit 4))),
      .assign .storage (slot0F "unlocked") (.boolLit true) ])
    hfeeRevert (by intro f e h; cases h)

end Benchmarks.UniswapV3Pool
