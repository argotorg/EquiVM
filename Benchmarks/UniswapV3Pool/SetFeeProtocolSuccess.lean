import Benchmarks.UniswapV3Pool.SetFeeProtocolFeeProtocolCheck

open Solm ABI Ethereum Ethereum.EVM Benchmarks.UniswapV3Pool.Immutables
open Reasoning.Theory Reasoning.Reach

namespace Benchmarks.UniswapV3Pool

abbrev setFeeProtocolFeeProtocolLoc : StorageLoc :=
  loc ⟨0⟩ ⟨29, by decide⟩ ⟨1, by decide⟩ (by decide) (.int uint8Int)

abbrev setFeeProtocolNewFeeProtocolNat (I : ExecutionEnv) : Nat :=
  (setFeeProtocolArg0Word I).toNat +
    ((setFeeProtocolArg1Word I).toNat * 2 ^ 4) % EVM.wordModulus

abbrev setFeeProtocolNewFeeProtocolValue (I : ExecutionEnv) : Value :=
  .int (Int.ofNat (setFeeProtocolNewFeeProtocolNat I))

abbrev setFeeProtocolFeeProtocolSlotWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  UInt256.ofNat
    ((Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩).toNat % 2 ^ 232 +
      (setFeeProtocolNewFeeProtocolNat I % 2 ^ 8) * 2 ^ 232 +
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩).toNat / 2 ^ 240 *
          2 ^ 240)

abbrev setFeeProtocolAfterFeeProtocolState (evm : EVM.State) (I : ExecutionEnv) :
    EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨0⟩
    (setFeeProtocolFeeProtocolSlotWord evm I)

abbrev setFeeProtocolUnlockedTrueSlotWord (evm : EVM.State) : UInt256 :=
  UInt256.ofNat
    ((Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩).toNat % 2 ^ 240 +
      2 ^ 240 +
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩).toNat / 2 ^ 248 *
          2 ^ 248)

abbrev setFeeProtocolAfterUnlockState (evm : EVM.State) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨0⟩
    (setFeeProtocolUnlockedTrueSlotWord evm)

abbrev setFeeProtocolFeeProtocolClearMask : UInt256 :=
  ⟨115790329291997763829805189145943027211779609632852660590886017564236060819455⟩

abbrev setFeeProtocolEvmNewFeeProtocolWord (I : ExecutionEnv) : UInt256 :=
  UInt256.land
    ⟨255⟩
    (setFeeProtocolArg0Word I +
      UInt256.land (UInt256.shiftLeft (setFeeProtocolArg1Word I) ⟨4⟩) ⟨4080⟩)

abbrev setFeeProtocolEvmFeeProtocolSlotWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.lor
    (UInt256.land (codeOwnerStorageWord I σ ⟨0⟩) setFeeProtocolFeeProtocolClearMask)
    (UInt256.mul (UInt256.shiftLeft ⟨1⟩ ⟨232⟩)
      (setFeeProtocolEvmNewFeeProtocolWord I))

abbrev setFeeProtocolEvmUnlockedClearMask : UInt256 :=
  UInt256.lnot (UInt256.shiftLeft ⟨255⟩ ⟨240⟩)

abbrev setFeeProtocolEvmUnlockedTrueSlotWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.lor
    (UInt256.shiftLeft ⟨1⟩ ⟨240⟩)
    (UInt256.land setFeeProtocolEvmUnlockedClearMask (codeOwnerStorageWord I σ ⟨0⟩))

abbrev setFeeProtocolEventTopic : UInt256 :=
  ⟨68407994909122337899402930436989363150185057688881605929376750743032331481395⟩

abbrev setFeeProtocolEventOldFeeProtocolWord (oldSlot : UInt256) : UInt256 :=
  UInt256.land (UInt256.div oldSlot (UInt256.shiftLeft ⟨1⟩ ⟨232⟩)) ⟨255⟩

abbrev setFeeProtocolEventOldFeeProtocol0Word (oldFeeProtocol : UInt256) : UInt256 :=
  UInt256.land ⟨255⟩ (UInt256.mod oldFeeProtocol ⟨16⟩)

abbrev setFeeProtocolEventOldFeeProtocol1Word (oldFeeProtocol : UInt256) : UInt256 :=
  UInt256.land (UInt256.shiftRight oldFeeProtocol ⟨4⟩) ⟨15⟩

abbrev setFeeProtocolEventNewFeeProtocol0Word (I : ExecutionEnv) : UInt256 :=
  UInt256.land ⟨255⟩ (setFeeProtocolArg0Word I)

abbrev setFeeProtocolEventNewFeeProtocol1Word (I : ExecutionEnv) : UInt256 :=
  UInt256.land (setFeeProtocolArg1Word I) ⟨255⟩

abbrev setFeeProtocolEventMem0 (w0 : UInt256) (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray w0).write 0 mem 128 32

abbrev setFeeProtocolEventMem1 (w0 w1 : UInt256) (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray w1).write 0 (setFeeProtocolEventMem0 w0 mem) 160 32

abbrev setFeeProtocolEventMem2 (w0 w1 w2 : UInt256) (mem : ByteArray) : ByteArray :=
  (UInt256.toByteArray w2).write 0 (setFeeProtocolEventMem1 w0 w1 mem) 192 32

abbrev setFeeProtocolEventMem3 (w0 w1 w2 w3 : UInt256) (mem : ByteArray) :
    ByteArray :=
  (UInt256.toByteArray w3).write 0 (setFeeProtocolEventMem2 w0 w1 w2 mem) 224 32

abbrev setFeeProtocolEventMem (oldSlot : UInt256) (I : ExecutionEnv) (out : ByteArray) :
    ByteArray :=
  let oldFeeProtocol := setFeeProtocolEventOldFeeProtocolWord oldSlot
  setFeeProtocolEventMem3
    (setFeeProtocolEventOldFeeProtocol0Word oldFeeProtocol)
    (setFeeProtocolEventOldFeeProtocol1Word oldFeeProtocol)
    (setFeeProtocolEventNewFeeProtocol0Word I)
    (setFeeProtocolEventNewFeeProtocol1Word I)
    (setFeeProtocolOwnerStaticcallMem out)

private theorem setFeeProtocolEventMem0_size {mem : ByteArray} (w0 : UInt256)
    (hmem : mem.size = 160) :
    (setFeeProtocolEventMem0 w0 mem).size = 160 := by
  exact toByteArray_write32_size_of_le mem w0 128 160 160 hmem
    (by rw [hmem]; omega)
    (by norm_num)

private theorem setFeeProtocolEventMem1_size {mem : ByteArray} (w0 w1 : UInt256)
    (hmem : mem.size = 160) :
    (setFeeProtocolEventMem1 w0 w1 mem).size = 192 := by
  exact toByteArray_write32_size_of_le (setFeeProtocolEventMem0 w0 mem) w1 160 160 192
    (setFeeProtocolEventMem0_size w0 hmem)
    (by rw [setFeeProtocolEventMem0_size w0 hmem])
    (by norm_num)

private theorem setFeeProtocolEventMem2_size {mem : ByteArray} (w0 w1 w2 : UInt256)
    (hmem : mem.size = 160) :
    (setFeeProtocolEventMem2 w0 w1 w2 mem).size = 224 := by
  exact toByteArray_write32_size_of_le (setFeeProtocolEventMem1 w0 w1 mem) w2 192 192 224
    (setFeeProtocolEventMem1_size w0 w1 hmem)
    (by rw [setFeeProtocolEventMem1_size w0 w1 hmem])
    (by norm_num)

private theorem setFeeProtocolEventMem3_size {mem : ByteArray} (w0 w1 w2 w3 : UInt256)
    (hmem : mem.size = 160) :
    (setFeeProtocolEventMem3 w0 w1 w2 w3 mem).size = 256 := by
  exact toByteArray_write32_size_of_le (setFeeProtocolEventMem2 w0 w1 w2 mem) w3
    224 224 256
    (setFeeProtocolEventMem2_size w0 w1 w2 hmem)
    (by rw [setFeeProtocolEventMem2_size w0 w1 w2 hmem])
    (by norm_num)

private theorem setFeeProtocolEventMem3_read64_of_base {mem : ByteArray}
    (w0 w1 w2 w3 : UInt256) (hmem : mem.size = 160)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (setFeeProtocolEventMem3 w0 w1 w2 w3 mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  change ((UInt256.toByteArray w3).write 0 (setFeeProtocolEventMem2 w0 w1 w2 mem)
      224 32).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩
  rw [write32_read_below _ _ 224 64 (by rw [toByteArray_size])
    (by rw [setFeeProtocolEventMem2_size w0 w1 w2 hmem]) (by omega)]
  change ((UInt256.toByteArray w2).write 0 (setFeeProtocolEventMem1 w0 w1 mem)
      192 32).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩
  rw [write32_read_below _ _ 192 64 (by rw [toByteArray_size])
    (by rw [setFeeProtocolEventMem1_size w0 w1 hmem]) (by omega)]
  change ((UInt256.toByteArray w1).write 0 (setFeeProtocolEventMem0 w0 mem)
      160 32).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩
  rw [write32_read_below _ _ 160 64 (by rw [toByteArray_size])
    (by rw [setFeeProtocolEventMem0_size w0 hmem]) (by omega)]
  change ((UInt256.toByteArray w0).write 0 mem 128 32).readWithPadding 64 32 =
    UInt256.toByteArray ⟨128⟩
  rw [write32_read_below _ _ 128 64 (by rw [toByteArray_size])
    (by rw [hmem]; omega) (by omega)]
  exact hread64

theorem setFeeProtocolEventMem_mload64_of_size_ge (oldSlot : UInt256) (I : ExecutionEnv)
    (out : ByteArray) (hlo : 32 ≤ out.size) (hhi : out.size < UInt256.size) :
    (if (⟨64⟩ : UInt256).toNat ≥ (setFeeProtocolEventMem oldSlot I out).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 8 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((setFeeProtocolEventMem oldSlot I out).readWithPadding
          (⟨64⟩ : UInt256).toNat 32))) =
      ⟨128⟩ := by
  let oldFeeProtocol := setFeeProtocolEventOldFeeProtocolWord oldSlot
  exact mloadFreePtrValue
    (by
      have hsz : (setFeeProtocolEventMem oldSlot I out).size = 256 := by
        dsimp [setFeeProtocolEventMem, oldFeeProtocol]
        exact setFeeProtocolEventMem3_size _ _ _ _
          (setFeeProtocolOwnerStaticcallMem_size_of_size_ge out hlo hhi)
      dsimp [setFeeProtocolEventMem, oldFeeProtocol]
      rw [hsz]
      decide)
    (by native_decide)
    (by
      dsimp [setFeeProtocolEventMem, oldFeeProtocol]
      exact setFeeProtocolEventMem3_read64_of_base _ _ _ _
        (setFeeProtocolOwnerStaticcallMem_size_of_size_ge out hlo hhi)
        (setFeeProtocolOwnerStaticcallMem_read64_of_size_ge out hlo hhi))

private theorem setFeeProtocolModXstep {s : State} {code : ByteArray}
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

private theorem setFeeProtocolRDMod {code : ByteArray} {ee : ExecutionEnv} {g : Sat256}
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
  · have st := setFeeProtocolModXstep hcode hpc hdec hstk hov
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

private theorem uniswapV3PoolPatchPreservesJumpDest857 :
    D_J_auxPreservesTargetBool uniswapV3PoolBytecode uniswapV3PoolPatchOffsets
      ⟨857⟩ 0 = true := by
  native_decide

theorem uniswapV3PoolJumpDestPatched857 {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    (D_J code 0).contains ⟨857⟩ = true := by
  exact D_J_aux_contains_of_patchRuntime_preservesTarget hpatch
    (uniswapV3PoolPatchOffsetMem v)
    uniswapV3PoolPatchPreservesJumpDest857

set_option maxHeartbeats 1000000 in
theorem uniswapV3PoolSetFeeProtocolFeeProtocolStoreEvm {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {R : List UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨8535⟩
      (setFeeProtocolArg1Word ee :: setFeeProtocolArg0Word ee :: R)
      mem aw rdata (cA, σ) k C)
    (hperm : ee.perm = true)
    (hov : R.length + 9 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨8603⟩
      (⟨255⟩ :: codeOwnerStorageWord ee σ ⟨0⟩ :: UInt256.shiftLeft ⟨1⟩ ⟨232⟩ ::
        setFeeProtocolArg1Word ee :: setFeeProtocolArg0Word ee :: R)
      mem aw rdata
      (cA, sstoreAccountMap ee.codeOwner σ ⟨0⟩
        (setFeeProtocolEvmFeeProtocolSlotWord σ ee))
      k' C' := by
  have hd8535 : decode code ⟨8535⟩ = some (.JUMPDEST, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8535⟩) (byte := 0x5b)
      (op := .JUMPDEST) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8536 : decode code ⟨8536⟩ = some (.Push .PUSH1, some (⟨0⟩, 1)) := by
    exact setFeeProtocolDecodePush1AfterFactory (pc := ⟨8536⟩)
      (n := ⟨0⟩) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have hd8538 : decode code ⟨8538⟩ = some (.DUP1, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8538⟩) (byte := 0x80)
      (op := .DUP1) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8539 : decode code ⟨8539⟩ = some (.SLOAD, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8539⟩) (byte := 0x54)
      (op := .SLOAD) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8540 : decode code ⟨8540⟩ = some (.Push .PUSH2, some (⟨4080⟩, 2)) := by
    exact setFeeProtocolDecodePush2AfterFactory (pc := ⟨8540⟩)
      (n := ⟨4080⟩) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have hd8543 : decode code ⟨8543⟩ = some (.Push .PUSH1, some (⟨4⟩, 1)) := by
    exact setFeeProtocolDecodePush1AfterFactory (pc := ⟨8543⟩)
      (n := ⟨4⟩) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have hd8545 : decode code ⟨8545⟩ = some (.DUP5, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8545⟩) (byte := 0x84)
      (op := .DUP5) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8546 : decode code ⟨8546⟩ = some (.SWAP1, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8546⟩) (byte := 0x90)
      (op := .SWAP1) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8547 : decode code ⟨8547⟩ = some (.SHL, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8547⟩) (byte := 0x1b)
      (op := .SHL) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8548 : decode code ⟨8548⟩ = some (.AND, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8548⟩) (byte := 0x16)
      (op := .AND) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8549 : decode code ⟨8549⟩ = some (.DUP5, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8549⟩) (byte := 0x84)
      (op := .DUP5) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8550 : decode code ⟨8550⟩ = some (.ADD, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8550⟩) (byte := 0x01)
      (op := .ADD) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8551 : decode code ⟨8551⟩ = some (.Push .PUSH1, some (⟨255⟩, 1)) := by
    exact setFeeProtocolDecodePush1AfterFactory (pc := ⟨8551⟩)
      (n := ⟨255⟩) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have hd8553 : decode code ⟨8553⟩ = some (.SWAP1, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8553⟩) (byte := 0x90)
      (op := .SWAP1) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8554 : decode code ⟨8554⟩ = some (.DUP2, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8554⟩) (byte := 0x81)
      (op := .DUP2) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8555 : decode code ⟨8555⟩ = some (.AND, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8555⟩) (byte := 0x16)
      (op := .AND) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8556 : decode code ⟨8556⟩ = some (.Push .PUSH1, some (⟨1⟩, 1)) := by
    exact setFeeProtocolDecodePush1AfterFactory (pc := ⟨8556⟩)
      (n := ⟨1⟩) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have hd8558 : decode code ⟨8558⟩ = some (.Push .PUSH1, some (⟨232⟩, 1)) := by
    exact setFeeProtocolDecodePush1AfterFactory (pc := ⟨8558⟩)
      (n := ⟨232⟩) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have hd8560 : decode code ⟨8560⟩ = some (.SHL, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8560⟩) (byte := 0x1b)
      (op := .SHL) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8561 : decode code ⟨8561⟩ = some (.SWAP1, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8561⟩) (byte := 0x90)
      (op := .SWAP1) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8562 : decode code ⟨8562⟩ = some (.DUP2, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8562⟩) (byte := 0x81)
      (op := .DUP2) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8563 : decode code ⟨8563⟩ = some (.MUL, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8563⟩) (byte := 0x02)
      (op := .MUL) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8564 :
      decode code ⟨8564⟩ =
        some (.Push .PUSH32, some (setFeeProtocolFeeProtocolClearMask, 32)) := by
    rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by native_decide)
      (uniswapV3PoolSetFeeProtocolOwnerCallPatchDisjointAfterFactory
        (n := 33) (by native_decide) (by native_decide))]
    native_decide
  have hd8597 : decode code ⟨8597⟩ = some (.DUP5, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8597⟩) (byte := 0x84)
      (op := .DUP5) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8598 : decode code ⟨8598⟩ = some (.AND, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8598⟩) (byte := 0x16)
      (op := .AND) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8599 : decode code ⟨8599⟩ = some (.OR, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8599⟩) (byte := 0x17)
      (op := .OR) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8600 : decode code ⟨8600⟩ = some (.SWAP1, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8600⟩) (byte := 0x90)
      (op := .SWAP1) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8601 : decode code ⟨8601⟩ = some (.SWAP4, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8601⟩) (byte := 0x93)
      (op := .SWAP4) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8602 : decode code ⟨8602⟩ = some (.SSTORE, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8602⟩) (byte := 0x55)
      (op := .SSTORE) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have rd8539 := evm_run h with [
    raw jumpdest hd8535 (by evm_ov),
    raw push1 ⟨0⟩ hd8536 (by evm_ov),
    raw dup1 hd8538 (by evm_ov)]
  obtain ⟨_, _, rd8540₀⟩ := rd8539.sload hd8539 (by evm_ov)
  have rd8602 := evm_run rd8540₀ with [
    raw push2 ⟨4080⟩ hd8540 (by evm_ov),
    raw push1 ⟨4⟩ hd8543 (by evm_ov),
    raw dup5 hd8545 (by evm_ov),
    raw swap1 hd8546 (by evm_ov),
    raw shl hd8547 (by evm_ov),
    raw and hd8548 (by evm_ov),
    raw dup5 hd8549 (by evm_ov),
    raw add hd8550 (by evm_ov),
    raw push1 ⟨255⟩ hd8551 (by evm_ov),
    raw swap1 hd8553 (by evm_ov),
    raw dup2 hd8554 (by evm_ov),
    raw and hd8555 (by evm_ov),
    raw push1 ⟨1⟩ hd8556 (by evm_ov),
    raw push1 ⟨232⟩ hd8558 (by
      have h := hov
      simp only [List.length_cons] at h ⊢
      omega),
    raw shl hd8560 (by evm_ov),
    raw swap1 hd8561 (by evm_ov),
    raw dup2 hd8562 (by
      have h := hov
      simp only [List.length_cons] at h ⊢
      omega),
    raw mul hd8563 (by evm_ov),
    raw pushConst setFeeProtocolFeeProtocolClearMask
      (show Operation.POp.PUSH32 ≠ .PUSH0 by native_decide)
      hd8564
      (by
        have h := hov
        simp only [List.length_cons] at h ⊢
        omega),
    raw dup5 hd8597 (by
      have h := hov
      simp only [List.length_cons] at h ⊢
      omega),
    raw and hd8598 (by
      have h := hov
      simp only [List.length_cons] at h ⊢
      omega),
    raw lor hd8599 (by evm_ov),
    raw swap1 hd8600 (by evm_ov),
    raw swap4 hd8601 (by evm_ov)]
  obtain ⟨_, _, rd8603⟩ := rd8602.sstore hperm hd8602 (by evm_ov)
  norm_num at rd8603
  exact ⟨_, _, by
    simpa [setFeeProtocolEvmFeeProtocolSlotWord, setFeeProtocolEvmNewFeeProtocolWord,
      codeOwnerStorageWord] using rd8603⟩

set_option maxHeartbeats 1000000 in
theorem uniswapV3PoolSetFeeProtocolEventLogEvm {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {R : List UInt256} {out : ByteArray} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ}
    {oldSlot : UInt256}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨8603⟩
      (⟨255⟩ :: oldSlot :: UInt256.shiftLeft ⟨1⟩ ⟨232⟩ ::
        setFeeProtocolArg1Word ee :: setFeeProtocolArg0Word ee :: R)
      (setFeeProtocolOwnerStaticcallMem out) setFeeProtocolOwnerStaticcallActiveWords
      rdata (cA, σ) k C)
    (hperm : ee.perm = true)
    (houtSize32 : 32 ≤ out.size) (houtSize : out.size < UInt256.size)
    (hov : R.length + 12 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨8696⟩
      (setFeeProtocolEventOldFeeProtocolWord oldSlot ::
        setFeeProtocolArg1Word ee :: setFeeProtocolArg0Word ee :: R)
      (setFeeProtocolEventMem oldSlot ee out) (UInt256.ofNat 8)
      rdata (cA, σ) k' C' := by
  have hd8603 : decode code ⟨8603⟩ = some (.SWAP2, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8603⟩) (byte := 0x91)
      (op := .SWAP2) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8604 : decode code ⟨8604⟩ = some (.SWAP1, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8604⟩) (byte := 0x90)
      (op := .SWAP1) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8605 : decode code ⟨8605⟩ = some (.DIV, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8605⟩) (byte := 0x04)
      (op := .DIV) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8606 : decode code ⟨8606⟩ = some (.AND, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8606⟩) (byte := 0x16)
      (op := .AND) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8607 :
      decode code ⟨8607⟩ =
        some (.Push .PUSH32, some (setFeeProtocolEventTopic, 32)) := by
    rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by native_decide)
      (uniswapV3PoolSetFeeProtocolOwnerCallPatchDisjointAfterFactory
        (n := 33) (by native_decide) (by native_decide))]
    native_decide
  have hd8640 : decode code ⟨8640⟩ = some (.Push .PUSH1, some (⟨16⟩, 1)) := by
    exact setFeeProtocolDecodePush1AfterFactory (pc := ⟨8640⟩)
      (n := ⟨16⟩) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have hd8642 : decode code ⟨8642⟩ = some (.DUP3, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8642⟩) (byte := 0x82)
      (op := .DUP3) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8643 : decode code ⟨8643⟩ = some (.Push .PUSH1, some (⟨64⟩, 1)) := by
    exact setFeeProtocolDecodePush1AfterFactory (pc := ⟨8643⟩)
      (n := ⟨64⟩) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have hd8645 : decode code ⟨8645⟩ = some (.DUP1, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8645⟩) (byte := 0x80)
      (op := .DUP1) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8646 : decode code ⟨8646⟩ = some (.MLOAD, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8646⟩) (byte := 0x51)
      (op := .MLOAD) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8647 : decode code ⟨8647⟩ = some (.Push .PUSH1, some (⟨255⟩, 1)) := by
    exact setFeeProtocolDecodePush1AfterFactory (pc := ⟨8647⟩)
      (n := ⟨255⟩) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have hd8649 : decode code ⟨8649⟩ = some (.SWAP4, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8649⟩) (byte := 0x93)
      (op := .SWAP4) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8650 : decode code ⟨8650⟩ = some (.SWAP1, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8650⟩) (byte := 0x90)
      (op := .SWAP1) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8651 : decode code ⟨8651⟩ = some (.SWAP3, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8651⟩) (byte := 0x92)
      (op := .SWAP3) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8652 : decode code ⟨8652⟩ = some (.MOD, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8652⟩) (byte := 0x06)
      (op := .MOD) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8653 : decode code ⟨8653⟩ = some (.DUP4, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8653⟩) (byte := 0x83)
      (op := .DUP4) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8654 : decode code ⟨8654⟩ = some (.AND, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8654⟩) (byte := 0x16)
      (op := .AND) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8655 : decode code ⟨8655⟩ = some (.DUP3, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8655⟩) (byte := 0x82)
      (op := .DUP3) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8656 : decode code ⟨8656⟩ = some (.MSTORE, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8656⟩) (byte := 0x52)
      (op := .MSTORE) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8657 : decode code ⟨8657⟩ = some (.Push .PUSH1, some (⟨15⟩, 1)) := by
    exact setFeeProtocolDecodePush1AfterFactory (pc := ⟨8657⟩)
      (n := ⟨15⟩) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have hd8659 : decode code ⟨8659⟩ = some (.Push .PUSH1, some (⟨4⟩, 1)) := by
    exact setFeeProtocolDecodePush1AfterFactory (pc := ⟨8659⟩)
      (n := ⟨4⟩) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have hd8661 : decode code ⟨8661⟩ = some (.DUP7, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8661⟩) (byte := 0x86)
      (op := .DUP7) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8662 : decode code ⟨8662⟩ = some (.SWAP1, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8662⟩) (byte := 0x90)
      (op := .SWAP1) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8663 : decode code ⟨8663⟩ = some (.SHR, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8663⟩) (byte := 0x1c)
      (op := .SHR) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8664 : decode code ⟨8664⟩ = some (.AND, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8664⟩) (byte := 0x16)
      (op := .AND) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8665 : decode code ⟨8665⟩ = some (.Push .PUSH1, some (⟨32⟩, 1)) := by
    exact setFeeProtocolDecodePush1AfterFactory (pc := ⟨8665⟩)
      (n := ⟨32⟩) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have hd8667 : decode code ⟨8667⟩ = some (.DUP4, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8667⟩) (byte := 0x83)
      (op := .DUP4) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8668 : decode code ⟨8668⟩ = some (.ADD, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8668⟩) (byte := 0x01)
      (op := .ADD) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8669 : decode code ⟨8669⟩ = some (.MSTORE, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8669⟩) (byte := 0x52)
      (op := .MSTORE) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8670 : decode code ⟨8670⟩ = some (.DUP7, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8670⟩) (byte := 0x86)
      (op := .DUP7) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8671 : decode code ⟨8671⟩ = some (.DUP4, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8671⟩) (byte := 0x83)
      (op := .DUP4) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8672 : decode code ⟨8672⟩ = some (.AND, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8672⟩) (byte := 0x16)
      (op := .AND) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8673 : decode code ⟨8673⟩ = some (.DUP3, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8673⟩) (byte := 0x82)
      (op := .DUP3) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8674 : decode code ⟨8674⟩ = some (.DUP3, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8674⟩) (byte := 0x82)
      (op := .DUP3) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8675 : decode code ⟨8675⟩ = some (.ADD, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8675⟩) (byte := 0x01)
      (op := .ADD) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8676 : decode code ⟨8676⟩ = some (.MSTORE, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8676⟩) (byte := 0x52)
      (op := .MSTORE) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8677 : decode code ⟨8677⟩ = some (.SWAP2, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8677⟩) (byte := 0x91)
      (op := .SWAP2) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8678 : decode code ⟨8678⟩ = some (.DUP6, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8678⟩) (byte := 0x85)
      (op := .DUP6) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8679 : decode code ⟨8679⟩ = some (.AND, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8679⟩) (byte := 0x16)
      (op := .AND) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8680 : decode code ⟨8680⟩ = some (.Push .PUSH1, some (⟨96⟩, 1)) := by
    exact setFeeProtocolDecodePush1AfterFactory (pc := ⟨8680⟩)
      (n := ⟨96⟩) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have hd8682 : decode code ⟨8682⟩ = some (.DUP3, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8682⟩) (byte := 0x82)
      (op := .DUP3) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8683 : decode code ⟨8683⟩ = some (.ADD, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8683⟩) (byte := 0x01)
      (op := .ADD) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8684 : decode code ⟨8684⟩ = some (.MSTORE, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8684⟩) (byte := 0x52)
      (op := .MSTORE) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8685 : decode code ⟨8685⟩ = some (.SWAP1, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8685⟩) (byte := 0x90)
      (op := .SWAP1) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8686 : decode code ⟨8686⟩ = some (.MLOAD, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8686⟩) (byte := 0x51)
      (op := .MLOAD) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8687 : decode code ⟨8687⟩ = some (.SWAP1, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8687⟩) (byte := 0x90)
      (op := .SWAP1) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8688 : decode code ⟨8688⟩ = some (.DUP2, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8688⟩) (byte := 0x81)
      (op := .DUP2) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8689 : decode code ⟨8689⟩ = some (.SWAP1, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8689⟩) (byte := 0x90)
      (op := .SWAP1) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8690 : decode code ⟨8690⟩ = some (.SUB, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8690⟩) (byte := 0x03)
      (op := .SUB) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8691 : decode code ⟨8691⟩ = some (.Push .PUSH1, some (⟨128⟩, 1)) := by
    exact setFeeProtocolDecodePush1AfterFactory (pc := ⟨8691⟩)
      (n := ⟨128⟩) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have hd8693 : decode code ⟨8693⟩ = some (.ADD, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8693⟩) (byte := 0x01)
      (op := .ADD) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8694 : decode code ⟨8694⟩ = some (.SWAP1, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8694⟩) (byte := 0x90)
      (op := .SWAP1) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8695 : decode code ⟨8695⟩ = some (.LOG1, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8695⟩) (byte := 0xa1)
      (op := .LOG1) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have rd8652 := evm_run h with [
    raw swap2 hd8603 (by evm_ov),
    raw swap1 hd8604 (by evm_ov),
    raw div hd8605 (by evm_ov),
    raw and hd8606 (by evm_ov),
    raw pushConst setFeeProtocolEventTopic
      (show Operation.POp.PUSH32 ≠ .PUSH0 by native_decide)
      hd8607
      (by evm_ov),
    raw push1 ⟨16⟩ hd8640 (by evm_ov),
    raw dup3 hd8642 (by evm_ov),
    raw push1 ⟨64⟩ hd8643 (by evm_ov),
    raw dup1 hd8645 (by evm_ov),
    raw mload 0 ⟨128⟩ setFeeProtocolOwnerStaticcallActiveWords hd8646 mem_cost
      (setFeeProtocolOwnerStaticcallMem_mload64_of_size_ge out houtSize32 houtSize)
      (by native_decide) (by evm_ov),
    raw push1 ⟨255⟩ hd8647 (by evm_ov),
    raw swap4 hd8649 (by evm_ov),
    raw swap1 hd8650 (by evm_ov),
    raw swap3 hd8651 (by evm_ov)]
  have rd8653 := setFeeProtocolRDMod rd8652 hd8652 (by evm_ov)
  have rd8696 := evm_run rd8653 with [
    raw dup4 hd8653 (by evm_ov),
    raw and hd8654 (by evm_ov),
    raw dup3 hd8655 (by evm_ov),
    raw mstore 0
      (setFeeProtocolEventMem0
        (setFeeProtocolEventOldFeeProtocol0Word
          (setFeeProtocolEventOldFeeProtocolWord oldSlot))
        (setFeeProtocolOwnerStaticcallMem out))
      setFeeProtocolOwnerStaticcallActiveWords hd8656 mem_cost rfl
      (by native_decide) (by evm_ov),
    raw push1 ⟨15⟩ hd8657 (by evm_ov),
    raw push1 ⟨4⟩ hd8659 (by evm_ov),
    raw dup7 hd8661 (by evm_ov),
    raw swap1 hd8662 (by evm_ov),
    raw shr hd8663 (by evm_ov),
    raw and hd8664 (by evm_ov),
    raw push1 ⟨32⟩ hd8665 (by evm_ov),
    raw dup4 hd8667 (by evm_ov),
    raw add hd8668 (by evm_ov),
    raw mstore 3
      (setFeeProtocolEventMem1
        (setFeeProtocolEventOldFeeProtocol0Word
          (setFeeProtocolEventOldFeeProtocolWord oldSlot))
        (setFeeProtocolEventOldFeeProtocol1Word
          (setFeeProtocolEventOldFeeProtocolWord oldSlot))
        (setFeeProtocolOwnerStaticcallMem out))
      (UInt256.ofNat 6) hd8669 mem_cost rfl
      (by native_decide) (by evm_ov),
    raw dup7 hd8670 (by evm_ov),
    raw dup4 hd8671 (by evm_ov),
    raw and hd8672 (by evm_ov),
    raw dup3 hd8673 (by evm_ov),
    raw dup3 hd8674 (by evm_ov),
    raw add hd8675 (by evm_ov),
    raw mstore 3
      (setFeeProtocolEventMem2
        (setFeeProtocolEventOldFeeProtocol0Word
          (setFeeProtocolEventOldFeeProtocolWord oldSlot))
        (setFeeProtocolEventOldFeeProtocol1Word
          (setFeeProtocolEventOldFeeProtocolWord oldSlot))
        (setFeeProtocolEventNewFeeProtocol0Word ee)
        (setFeeProtocolOwnerStaticcallMem out))
      (UInt256.ofNat 7) hd8676 mem_cost rfl
      (by native_decide) (by evm_ov),
    raw swap2 hd8677 (by evm_ov),
    raw dup6 hd8678 (by evm_ov),
    raw and hd8679 (by evm_ov),
    raw push1 ⟨96⟩ hd8680 (by evm_ov),
    raw dup3 hd8682 (by evm_ov),
    raw add hd8683 (by evm_ov),
    raw mstore 3
      (setFeeProtocolEventMem oldSlot ee out)
      (UInt256.ofNat 8) hd8684 mem_cost
      (by rfl)
      (by native_decide) (by evm_ov),
    raw swap1 hd8685 (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) hd8686 mem_cost
      (setFeeProtocolEventMem_mload64_of_size_ge oldSlot ee out houtSize32 houtSize)
      (by native_decide) (by evm_ov),
    raw swap1 hd8687 (by evm_ov),
    raw dup2 hd8688 (by evm_ov),
    raw swap1 hd8689 (by evm_ov),
    raw sub hd8690 (by evm_ov),
    raw push1 ⟨128⟩ hd8691 (by evm_ov),
    raw add hd8693 (by evm_ov),
    raw swap1 hd8694 (by evm_ov),
    raw log1 0 (UInt256.ofNat 8) hd8695 hperm mem_cost
      (by native_decide) (by evm_ov)]
  exact ⟨_, _, rd8696⟩

set_option maxHeartbeats 1000000 in
theorem uniswapV3PoolSetFeeProtocolUnlockReturnEvm {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {R : List UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ}
    {oldFeeProtocol : UInt256}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨8696⟩
      (oldFeeProtocol :: setFeeProtocolArg1Word ee :: setFeeProtocolArg0Word ee :: ⟨857⟩ :: R)
      mem aw rdata (cA, σ) k C)
    (hperm : ee.perm = true)
    (hov : R.length + 6 ≤ 1024) :
    RDret code g s0
      (cA, sstoreAccountMap ee.codeOwner σ ⟨0⟩
        (setFeeProtocolEvmUnlockedTrueSlotWord σ ee))
      ByteArray.empty := by
  have hd8696 : decode code ⟨8696⟩ = some (.POP, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8696⟩) (byte := 0x50)
      (op := .POP) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8697 : decode code ⟨8697⟩ = some (.POP, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8697⟩) (byte := 0x50)
      (op := .POP) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8698 : decode code ⟨8698⟩ = some (.Push .PUSH1, some (⟨0⟩, 1)) := by
    exact setFeeProtocolDecodePush1AfterFactory (pc := ⟨8698⟩)
      (n := ⟨0⟩) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have hd8700 : decode code ⟨8700⟩ = some (.DUP1, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8700⟩) (byte := 0x80)
      (op := .DUP1) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8701 : decode code ⟨8701⟩ = some (.SLOAD, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8701⟩) (byte := 0x54)
      (op := .SLOAD) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8702 : decode code ⟨8702⟩ = some (.Push .PUSH1, some (⟨255⟩, 1)) := by
    exact setFeeProtocolDecodePush1AfterFactory (pc := ⟨8702⟩)
      (n := ⟨255⟩) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have hd8704 : decode code ⟨8704⟩ = some (.Push .PUSH1, some (⟨240⟩, 1)) := by
    exact setFeeProtocolDecodePush1AfterFactory (pc := ⟨8704⟩)
      (n := ⟨240⟩) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have hd8706 : decode code ⟨8706⟩ = some (.SHL, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8706⟩) (byte := 0x1b)
      (op := .SHL) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8707 : decode code ⟨8707⟩ = some (.NOT, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8707⟩) (byte := 0x19)
      (op := .NOT) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8708 : decode code ⟨8708⟩ = some (.AND, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8708⟩) (byte := 0x16)
      (op := .AND) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8709 : decode code ⟨8709⟩ = some (.Push .PUSH1, some (⟨1⟩, 1)) := by
    exact setFeeProtocolDecodePush1AfterFactory (pc := ⟨8709⟩)
      (n := ⟨1⟩) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have hd8711 : decode code ⟨8711⟩ = some (.Push .PUSH1, some (⟨240⟩, 1)) := by
    exact setFeeProtocolDecodePush1AfterFactory (pc := ⟨8711⟩)
      (n := ⟨240⟩) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have hd8713 : decode code ⟨8713⟩ = some (.SHL, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8713⟩) (byte := 0x1b)
      (op := .SHL) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8714 : decode code ⟨8714⟩ = some (.OR, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8714⟩) (byte := 0x17)
      (op := .OR) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8715 : decode code ⟨8715⟩ = some (.SWAP1, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8715⟩) (byte := 0x90)
      (op := .SWAP1) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8716 : decode code ⟨8716⟩ = some (.SSTORE, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8716⟩) (byte := 0x55)
      (op := .SSTORE) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8717 : decode code ⟨8717⟩ = some (.POP, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8717⟩) (byte := 0x50)
      (op := .POP) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd8718 : decode code ⟨8718⟩ = some (.JUMP, .none) := by
    refine setFeeProtocolDecodeNoArgAfterFactory (pc := ⟨8718⟩) (byte := 0x56)
      (op := .JUMP) hpatch (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide)
  have hd857 : decode code ⟨857⟩ = some (.JUMPDEST, .none) := by
    rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
    native_decide
  have hd858 : decode code ⟨858⟩ = some (.STOP, .none) := by
    rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
    native_decide
  have rd8701 := evm_run h with [
    raw pop hd8696 (by evm_ov),
    raw pop hd8697 (by evm_ov),
    raw push1 ⟨0⟩ hd8698 (by evm_ov),
    raw dup1 hd8700 (by evm_ov)]
  obtain ⟨_, _, rd8702₀⟩ := rd8701.sload hd8701 (by evm_ov)
  have rd8716 := evm_run rd8702₀ with [
    raw push1 ⟨255⟩ hd8702 (by
      have h := hov
      simp only [List.length_cons] at h ⊢
      omega),
    raw push1 ⟨240⟩ hd8704 (by
      have h := hov
      simp only [List.length_cons] at h ⊢
      omega),
    raw shl hd8706 (by
      have h := hov
      simp only [List.length_cons] at h ⊢
      omega),
    raw not hd8707 (by
      have h := hov
      simp only [List.length_cons] at h ⊢
      omega),
    raw and hd8708 (by
      have h := hov
      simp only [List.length_cons] at h ⊢
      omega),
    raw push1 ⟨1⟩ hd8709 (by
      have h := hov
      simp only [List.length_cons] at h ⊢
      omega),
    raw push1 ⟨240⟩ hd8711 (by
      have h := hov
      simp only [List.length_cons] at h ⊢
      omega),
    raw shl hd8713 (by
      have h := hov
      simp only [List.length_cons] at h ⊢
      omega),
    raw lor hd8714 (by evm_ov),
    raw swap1 hd8715 (by evm_ov)]
  obtain ⟨_, _, rd8717⟩ := rd8716.sstore hperm hd8716 (by evm_ov)
  have rd8718 := evm_run rd8717 with [
    raw pop hd8717 (by evm_ov)]
  have rd857 := rd8718.jump hd8718 (uniswapV3PoolJumpDestPatched857 hpatch) (by evm_ov)
  have rd858 := rd857.jumpdest hd857 (by evm_ov)
  obtain ⟨k858, C858, rd858'⟩ : ∃ k' C', RD code ee g s0 ⟨858⟩ R mem aw rdata
      (cA, sstoreAccountMap ee.codeOwner σ ⟨0⟩
        (setFeeProtocolEvmUnlockedTrueSlotWord σ ee)) k' C' := by
    exact ⟨_, _, by
      simpa [setFeeProtocolEvmUnlockedTrueSlotWord, setFeeProtocolEvmUnlockedClearMask,
        codeOwnerStorageWord] using rd858⟩
  exact rd858'.stop hd858 (by
    have h := hov
    omega)

theorem setFeeProtocolNewFeeProtocolNat_lt_word (I : ExecutionEnv) :
    setFeeProtocolNewFeeProtocolNat I < UInt256.size := by
  have h0 : (setFeeProtocolArg0Word I).toNat < 2 ^ 8 := by
    simpa [setFeeProtocolArg0Word, setFeeProtocolUint8Mask, slot0Uint8Mask] using
      slot0Uint8Mask_bound (calldataWord I.calldata 4)
  have h1 : (setFeeProtocolArg1Word I).toNat < 2 ^ 8 := by
    simpa [setFeeProtocolArg1Word, setFeeProtocolUint8Mask, slot0Uint8Mask] using
      slot0Uint8Mask_bound (calldataWord I.calldata 36)
  have hshift :
      ((setFeeProtocolArg1Word I).toNat * 2 ^ 4) % EVM.wordModulus < 2 ^ 12 := by
    exact lt_of_le_of_lt (Nat.mod_le _ _) (Nat.mul_lt_mul_of_pos_right h1 (by norm_num))
  have hsum : (setFeeProtocolArg0Word I).toNat +
      ((setFeeProtocolArg1Word I).toNat * 2 ^ 4) % EVM.wordModulus < 2 ^ 13 := by
    calc
      (setFeeProtocolArg0Word I).toNat +
          ((setFeeProtocolArg1Word I).toNat * 2 ^ 4) % EVM.wordModulus
          < 2 ^ 8 + 2 ^ 12 := by omega
      _ < 2 ^ 13 := by norm_num
  dsimp [setFeeProtocolNewFeeProtocolNat]
  exact lt_trans hsum (pow_lt_size (by omega : 13 < 256))

theorem setFeeProtocolNewFeeProtocolNat_mod_lt (I : ExecutionEnv) :
    setFeeProtocolNewFeeProtocolNat I % 2 ^ 8 < 2 ^ 8 :=
  Nat.mod_lt _ (by norm_num)

theorem setFeeProtocolFeeProtocolSlotWord_nat_lt (evm : EVM.State) (I : ExecutionEnv) :
    (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩).toNat % 2 ^ 232 +
        (setFeeProtocolNewFeeProtocolNat I % 2 ^ 8) * 2 ^ 232 +
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩).toNat / 2 ^ 240 *
            2 ^ 240 <
      UInt256.size := by
  let w := Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩
  have hlow : w.toNat % 2 ^ 232 ≤ 2 ^ 232 - 1 :=
    Nat.le_pred_of_lt (Nat.mod_lt _ (by norm_num))
  have hbyte : setFeeProtocolNewFeeProtocolNat I % 2 ^ 8 ≤ 2 ^ 8 - 1 :=
    Nat.le_pred_of_lt (setFeeProtocolNewFeeProtocolNat_mod_lt I)
  have hhighLt : w.toNat / 2 ^ 240 < 2 ^ 16 := by
    apply Nat.div_lt_of_lt_mul
    rw [show 2 ^ 240 * 2 ^ 16 = (2 : Nat) ^ 256 by rw [← Nat.pow_add]]
    change w.val.val < UInt256.size
    exact w.val.isLt
  have hhigh : w.toNat / 2 ^ 240 ≤ 2 ^ 16 - 1 := Nat.le_pred_of_lt hhighLt
  have hmax :
      (2 ^ 232 - 1) + (2 ^ 8 - 1) * 2 ^ 232 + (2 ^ 16 - 1) * 2 ^ 240 <
        UInt256.size := by
    norm_num [UInt256.size, Nat.pow_add]
  dsimp [w] at hlow hhigh
  omega

theorem setFeeProtocolUnlockedTrueSlotWord_nat_lt (evm : EVM.State) :
    (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩).toNat % 2 ^ 240 +
        2 ^ 240 +
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩).toNat / 2 ^ 248 *
            2 ^ 248 <
      UInt256.size := by
  let w := Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩
  have hlow : w.toNat % 2 ^ 240 ≤ 2 ^ 240 - 1 :=
    Nat.le_pred_of_lt (Nat.mod_lt _ (by norm_num))
  have hhighLt : w.toNat / 2 ^ 248 < 2 ^ 8 := by
    apply Nat.div_lt_of_lt_mul
    rw [show 2 ^ 248 * 2 ^ 8 = (2 : Nat) ^ 256 by rw [← Nat.pow_add]]
    change w.val.val < UInt256.size
    exact w.val.isLt
  have hhigh : w.toNat / 2 ^ 248 ≤ 2 ^ 8 - 1 := Nat.le_pred_of_lt hhighLt
  have hmax : (2 ^ 240 - 1) + 2 ^ 240 + (2 ^ 8 - 1) * 2 ^ 248 <
      UInt256.size := by
    norm_num [UInt256.size, Nat.pow_add]
  dsimp [w] at hlow hhigh
  omega

private theorem setFeeProtocolEnabledNat_lt_16 {n : Nat}
    (h : setFeeProtocolEnabledNat n) : n < 16 := by
  rcases h with hzero | hrange
  · omega
  · omega

private theorem setFeeProtocolUInt256_eq_of_toNat_eq {w : UInt256} {n : Nat}
    (h : w.toNat = n) (hn : n < UInt256.size) : w = UInt256.ofNat n := by
  apply u256_inj
  rw [h]
  exact (ulit_toNat' n hn).symm

theorem setFeeProtocolEvmNewFeeProtocolWord_eq (I : ExecutionEnv)
    (hfee0 : setFeeProtocolEnabledNat (setFeeProtocolArg0Word I).toNat)
    (hfee1 : setFeeProtocolEnabledNat (setFeeProtocolArg1Word I).toNat) :
    setFeeProtocolEvmNewFeeProtocolWord I = UInt256.ofNat (setFeeProtocolNewFeeProtocolNat I) := by
  have h0lt16 := setFeeProtocolEnabledNat_lt_16 hfee0
  have h1lt16 := setFeeProtocolEnabledNat_lt_16 hfee1
  have h0lt : (setFeeProtocolArg0Word I).toNat < UInt256.size :=
    (setFeeProtocolArg0Word I).val.isLt
  have h1lt : (setFeeProtocolArg1Word I).toNat < UInt256.size :=
    (setFeeProtocolArg1Word I).val.isLt
  dsimp [setFeeProtocolEvmNewFeeProtocolWord, setFeeProtocolNewFeeProtocolNat]
  interval_cases h0 : (setFeeProtocolArg0Word I).toNat <;>
    interval_cases h1 : (setFeeProtocolArg1Word I).toNat <;>
    rw [setFeeProtocolUInt256_eq_of_toNat_eq h0 h0lt,
      setFeeProtocolUInt256_eq_of_toNat_eq h1 h1lt] <;>
    native_decide

theorem setFeeProtocolNewFeeProtocolNat_lt_256_of_enabled (I : ExecutionEnv)
    (hfee0 : setFeeProtocolEnabledNat (setFeeProtocolArg0Word I).toNat)
    (hfee1 : setFeeProtocolEnabledNat (setFeeProtocolArg1Word I).toNat) :
    setFeeProtocolNewFeeProtocolNat I < 2 ^ 8 := by
  have h0lt := setFeeProtocolEnabledNat_lt_16 hfee0
  have h1lt := setFeeProtocolEnabledNat_lt_16 hfee1
  dsimp [setFeeProtocolNewFeeProtocolNat]
  have hmod : ((setFeeProtocolArg1Word I).toNat * 16) % EVM.wordModulus =
      (setFeeProtocolArg1Word I).toNat * 16 := by
    apply Nat.mod_eq_of_lt
    have : (setFeeProtocolArg1Word I).toNat * 16 < 16 * 16 := by
      exact Nat.mul_lt_mul_of_pos_right h1lt (by norm_num)
    norm_num [EVM.wordModulus, EVM.twoPow] at this ⊢
    omega
  rw [hmod]
  have : (setFeeProtocolArg1Word I).toNat * 16 < 16 * 16 := by
    exact Nat.mul_lt_mul_of_pos_right h1lt (by norm_num)
  omega

theorem setFeeProtocolFeeProtocolClearMask_toNat :
    setFeeProtocolFeeProtocolClearMask.toNat = 2 ^ 256 - 2 ^ 240 + (2 ^ 232 - 1) := by
  native_decide

theorem natLandClearByte232 (n : Nat) (hn : n < 2 ^ 256) :
    Nat.land n (2 ^ 256 - 2 ^ 240 + (2 ^ 232 - 1)) =
      n % 2 ^ 232 + (n / 2 ^ 240) * 2 ^ 240 := by
  apply Nat.eq_of_testBit_eq
  intro i
  change (n &&& (2 ^ 256 - 2 ^ 240 + (2 ^ 232 - 1))).testBit i =
    (n % 2 ^ 232 + n / 2 ^ 240 * 2 ^ 240).testBit i
  rw [Nat.testBit_and]
  rw [show n % 2 ^ 232 + (n / 2 ^ 240) * 2 ^ 240 =
      2 ^ 240 * (n / 2 ^ 240) + n % 2 ^ 232 by ring]
  rw [Nat.testBit_two_pow_mul_add (a := n / 2 ^ 240)
    (b_lt := lt_trans (Nat.mod_lt _ (show 0 < 2 ^ 232 by norm_num))
      (by norm_num : 2 ^ 232 < 2 ^ 240))]
  rw [show 2 ^ 256 - 2 ^ 240 + (2 ^ 232 - 1) =
      2 ^ 240 * (2 ^ 16 - 1) + (2 ^ 232 - 1) by norm_num [Nat.pow_add]]
  have hmaskLow : 2 ^ 232 - 1 < 2 ^ 240 := by norm_num
  rw [Nat.testBit_two_pow_mul_add (a := 2 ^ 16 - 1) (b_lt := hmaskLow)]
  by_cases hi240 : i < 240
  · simp [hi240]
    change (n.testBit i && (2 ^ 232 - 1).testBit i) = (n % 2 ^ 232).testBit i
    by_cases hi232 : i < 232
    · have hmask : (2 ^ 232 - 1).testBit i = true := by
        rw [Nat.testBit_two_pow_sub_one]
        exact decide_eq_true hi232
      have hmod : (n % 2 ^ 232).testBit i = n.testBit i := by
        rw [Nat.testBit_mod_two_pow]
        simp [hi232]
      rw [hmask, hmod]
      simp
    · have hmask : (2 ^ 232 - 1).testBit i = false := by
        rw [Nat.testBit_two_pow_sub_one]
        exact decide_eq_false hi232
      have hmod : (n % 2 ^ 232).testBit i = false := by
        rw [Nat.testBit_mod_two_pow]
        simp [hi232]
      rw [hmask, hmod]
      simp
  · have h240le : 240 ≤ i := Nat.le_of_not_gt hi240
    simp [hi240]
    change (n.testBit i && (2 ^ 16 - 1).testBit (i - 240)) =
      (n / 2 ^ 240).testBit (i - 240)
    by_cases hi256 : i < 256
    · have hsub16 : i - 240 < 16 := by omega
      have hdiv := divPow_testBit n 240 i h240le
      have hmask : (2 ^ 16 - 1).testBit (i - 240) = true := by
        rw [Nat.testBit_two_pow_sub_one]
        exact decide_eq_true hsub16
      rw [hdiv, hmask]
      simp
    · have hsub16 : ¬ i - 240 < 16 := by omega
      have hnbit : n.testBit i = false := by
        exact Nat.testBit_lt_two_pow
          (lt_of_lt_of_le hn (Nat.pow_le_pow_right (by norm_num) (by omega : 256 ≤ i)))
      have hdivfalse : (n / 2 ^ 240).testBit (i - 240) = false := by
        rw [divPow_testBit n 240 i h240le, hnbit]
      have hmask : (2 ^ 16 - 1).testBit (i - 240) = false := by
        rw [Nat.testBit_two_pow_sub_one]
        exact decide_eq_false hsub16
      rw [hmask, hdivfalse]
      simp

private theorem nat_lor_packed_byte232 (n byte : Nat) (hbyte : byte < 2 ^ 8) :
    Nat.lor (n % 2 ^ 232 + n / 2 ^ 240 * 2 ^ 240) (byte * 2 ^ 232) =
      n % 2 ^ 232 + byte * 2 ^ 232 + n / 2 ^ 240 * 2 ^ 240 := by
  apply Nat.eq_of_testBit_eq
  intro i
  change ((n % 2 ^ 232 + n / 2 ^ 240 * 2 ^ 240) ||| (byte * 2 ^ 232)).testBit i =
    (n % 2 ^ 232 + byte * 2 ^ 232 + n / 2 ^ 240 * 2 ^ 240).testBit i
  rw [Nat.testBit_or]
  rw [show n % 2 ^ 232 + n / 2 ^ 240 * 2 ^ 240 =
      2 ^ 240 * (n / 2 ^ 240) + n % 2 ^ 232 by ring]
  rw [Nat.testBit_two_pow_mul_add (a := n / 2 ^ 240)
    (b_lt := lt_trans (Nat.mod_lt _ (show 0 < 2 ^ 232 by norm_num))
      (by norm_num : 2 ^ 232 < 2 ^ 240))]
  rw [show n % 2 ^ 232 + byte * 2 ^ 232 + n / 2 ^ 240 * 2 ^ 240 =
      2 ^ 240 * (n / 2 ^ 240) + (2 ^ 232 * byte + n % 2 ^ 232) by ring]
  have hmid : 2 ^ 232 * byte + n % 2 ^ 232 < 2 ^ 240 := by
    have hlow : n % 2 ^ 232 ≤ 2 ^ 232 - 1 :=
      Nat.le_pred_of_lt (Nat.mod_lt _ (show 0 < 2 ^ 232 by norm_num))
    have hbytele : byte ≤ 2 ^ 8 - 1 := Nat.le_pred_of_lt hbyte
    have hmax : 2 ^ 232 * (2 ^ 8 - 1) + (2 ^ 232 - 1) < 2 ^ 240 := by
      norm_num [Nat.pow_add]
    nlinarith
  rw [Nat.testBit_two_pow_mul_add (a := n / 2 ^ 240) (b_lt := hmid)]
  rw [Nat.testBit_two_pow_mul_add (a := byte)
    (b_lt := Nat.mod_lt _ (show 0 < 2 ^ 232 by norm_num))]
  rw [show byte * 2 ^ 232 = 2 ^ 232 * byte + 0 by ring]
  rw [Nat.testBit_two_pow_mul_add (a := byte) (b_lt := show 0 < 2 ^ 232 by norm_num)]
  by_cases hi232 : i < 232
  · simp [hi232]
  · have h232le : 232 ≤ i := Nat.le_of_not_gt hi232
    have hlowfalse : (n % 2 ^ 232).testBit i = false := by
      exact Nat.testBit_lt_two_pow
        (lt_of_lt_of_le (Nat.mod_lt _ (show 0 < 2 ^ 232 by norm_num))
          (Nat.pow_le_pow_right (by norm_num) h232le))
    by_cases hi240 : i < 240
    · simp [hi232, hi240]
      intro hlowtrue
      have hlowfalse' :
          (n % 6901746346790563787434755862277025452451108972170386555162524223799296).testBit i =
            false := by
        simpa using hlowfalse
      rw [hlowfalse'] at hlowtrue
      cases hlowtrue
    · have hbytefalse : byte.testBit (i - 232) = false := by
        exact Nat.testBit_lt_two_pow
          (lt_of_lt_of_le hbyte (Nat.pow_le_pow_right (by norm_num) (by omega)))
      simp [hi232, hi240]
      intro hbytetrue
      rw [hbytefalse] at hbytetrue
      cases hbytetrue

private theorem nat_lor_packed_byte240 (n byte : Nat) (hbyte : byte < 2 ^ 8) :
    Nat.lor (n % 2 ^ 240 + n / 2 ^ 248 * 2 ^ 248) (byte * 2 ^ 240) =
      n % 2 ^ 240 + byte * 2 ^ 240 + n / 2 ^ 248 * 2 ^ 248 := by
  apply Nat.eq_of_testBit_eq
  intro i
  change ((n % 2 ^ 240 + n / 2 ^ 248 * 2 ^ 248) ||| (byte * 2 ^ 240)).testBit i =
    (n % 2 ^ 240 + byte * 2 ^ 240 + n / 2 ^ 248 * 2 ^ 248).testBit i
  rw [Nat.testBit_or]
  rw [show n % 2 ^ 240 + n / 2 ^ 248 * 2 ^ 248 =
      2 ^ 248 * (n / 2 ^ 248) + n % 2 ^ 240 by ring]
  rw [Nat.testBit_two_pow_mul_add (a := n / 2 ^ 248)
    (b_lt := lt_trans (Nat.mod_lt _ (show 0 < 2 ^ 240 by norm_num))
      (by norm_num : 2 ^ 240 < 2 ^ 248))]
  rw [show n % 2 ^ 240 + byte * 2 ^ 240 + n / 2 ^ 248 * 2 ^ 248 =
      2 ^ 248 * (n / 2 ^ 248) + (2 ^ 240 * byte + n % 2 ^ 240) by ring]
  have hmid : 2 ^ 240 * byte + n % 2 ^ 240 < 2 ^ 248 := by
    have hlow : n % 2 ^ 240 ≤ 2 ^ 240 - 1 :=
      Nat.le_pred_of_lt (Nat.mod_lt _ (show 0 < 2 ^ 240 by norm_num))
    have hbytele : byte ≤ 2 ^ 8 - 1 := Nat.le_pred_of_lt hbyte
    have hmax : 2 ^ 240 * (2 ^ 8 - 1) + (2 ^ 240 - 1) < 2 ^ 248 := by
      norm_num [Nat.pow_add]
    nlinarith
  rw [Nat.testBit_two_pow_mul_add (a := n / 2 ^ 248) (b_lt := hmid)]
  rw [Nat.testBit_two_pow_mul_add (a := byte)
    (b_lt := Nat.mod_lt _ (show 0 < 2 ^ 240 by norm_num))]
  rw [show byte * 2 ^ 240 = 2 ^ 240 * byte + 0 by ring]
  rw [Nat.testBit_two_pow_mul_add (a := byte) (b_lt := show 0 < 2 ^ 240 by norm_num)]
  by_cases hi240 : i < 240
  · simp [hi240]
  · have h240le : 240 ≤ i := Nat.le_of_not_gt hi240
    have hlowfalse : (n % 2 ^ 240).testBit i = false := by
      exact Nat.testBit_lt_two_pow
        (lt_of_lt_of_le (Nat.mod_lt _ (show 0 < 2 ^ 240 by norm_num))
          (Nat.pow_le_pow_right (by norm_num) h240le))
    by_cases hi248 : i < 248
    · simp [hi240, hi248]
      intro hlowtrue
      have hlowfalse' :
          (n % 1766847064778384329583297500742918515827483896875618958121606201292619776).testBit i =
            false := by
        simpa using hlowfalse
      rw [hlowfalse'] at hlowtrue
      cases hlowtrue
    · have hbytefalse : byte.testBit (i - 240) = false := by
        exact Nat.testBit_lt_two_pow
          (lt_of_lt_of_le hbyte (Nat.pow_le_pow_right (by norm_num) (by omega)))
      simp [hi240, hi248]
      intro hbytetrue
      rw [hbytefalse] at hbytetrue
      cases hbytetrue

private theorem nat_lor_packed_true_byte240 (n : Nat) :
    Nat.lor (n % 2 ^ 240 + n / 2 ^ 248 * 2 ^ 248) (2 ^ 240) =
      n % 2 ^ 240 + 2 ^ 240 + n / 2 ^ 248 * 2 ^ 248 := by
  simpa using nat_lor_packed_byte240 n 1 (by norm_num : 1 < 2 ^ 8)

theorem setFeeProtocolStorageLoad_codeOwner_eq {evm : EVM.State} {σ : AccountMap}
    {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ evm.accountMap) (hEnv : evm.executionEnv = I) :
    Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩ = codeOwnerStorageWord I σ ⟨0⟩ := by
  have hslot := accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨0⟩ (⟨0⟩ : UInt256)
  simpa [Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage,
    codeOwnerStorageWord, hEnv] using hslot.symm

theorem setFeeProtocolEvmFeeProtocolSlotWord_eq {evm : EVM.State} {σ : AccountMap}
    {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ evm.accountMap) (hEnv : evm.executionEnv = I)
    (hfee0 : setFeeProtocolEnabledNat (setFeeProtocolArg0Word I).toNat)
    (hfee1 : setFeeProtocolEnabledNat (setFeeProtocolArg1Word I).toNat) :
    setFeeProtocolEvmFeeProtocolSlotWord σ I = setFeeProtocolFeeProtocolSlotWord evm I := by
  have hload := setFeeProtocolStorageLoad_codeOwner_eq (evm := evm) (σ := σ) (I := I)
    hAccounts hEnv
  have hnew := setFeeProtocolEvmNewFeeProtocolWord_eq I hfee0 hfee1
  have hnewLt := setFeeProtocolNewFeeProtocolNat_lt_256_of_enabled I hfee0 hfee1
  have hclearLt :
      (codeOwnerStorageWord I σ ⟨0⟩).toNat % 2 ^ 232 +
          (codeOwnerStorageWord I σ ⟨0⟩).toNat / 2 ^ 240 * 2 ^ 240 < UInt256.size := by
    rw [← natLandClearByte232 (codeOwnerStorageWord I σ ⟨0⟩).toNat
      (codeOwnerStorageWord I σ ⟨0⟩).val.isLt]
    exact lt_of_le_of_lt (nat_land_le_right _ _) (by norm_num [UInt256.size])
  have hinsertLt : 2 ^ 232 * setFeeProtocolNewFeeProtocolNat I < UInt256.size := by
    have hmul : 2 ^ 232 * setFeeProtocolNewFeeProtocolNat I < 2 ^ 232 * 2 ^ 8 := by
      exact Nat.mul_lt_mul_of_pos_left hnewLt (by norm_num)
    norm_num [UInt256.size, Nat.pow_add] at hmul ⊢
    omega
  have hloadHigh :
      (codeOwnerStorageWord I σ ⟨0⟩).toNat / 2 ^ 240 * 2 ^ 240 =
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩).toNat / 2 ^ 240 *
          2 ^ 240 :=
    congrArg (fun w : UInt256 => w.toNat / 2 ^ 240 * 2 ^ 240) hload.symm
  have hloadLow :
      (codeOwnerStorageWord I σ ⟨0⟩).toNat % 2 ^ 232 =
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩).toNat % 2 ^ 232 :=
    congrArg (fun w : UInt256 => w.toNat % 2 ^ 232) hload.symm
  have hsourceLtNested :
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩).toNat % 2 ^ 232 +
            (setFeeProtocolNewFeeProtocolNat I % 2 ^ 8 % 2 ^ 8) * 2 ^ 232 +
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩).toNat / 2 ^ 240 *
            2 ^ 240 < UInt256.size := by
    rw [Nat.mod_eq_of_lt (setFeeProtocolNewFeeProtocolNat_mod_lt I)]
    exact setFeeProtocolFeeProtocolSlotWord_nat_lt evm I
  apply u256_inj
  rw [setFeeProtocolEvmFeeProtocolSlotWord, setFeeProtocolFeeProtocolSlotWord]
  rw [u256_lor_toNat, u256_land_toNat, u256_mul_toNat]
  rw [hnew]
  rw [ulit_toNat' _ (lt_trans hnewLt (by norm_num [UInt256.size]))]
  rw [setFeeProtocolFeeProtocolClearMask_toNat]
  rw [natLandClearByte232]
  rw [Nat.mod_eq_of_lt hclearLt]
  rw [show (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨232⟩).toNat = 2 ^ 232 by native_decide]
  rw [Nat.mod_eq_of_lt hinsertLt]
  rw [show 2 ^ 232 * setFeeProtocolNewFeeProtocolNat I =
      setFeeProtocolNewFeeProtocolNat I * 2 ^ 232 by ring]
  rw [nat_lor_packed_byte232 _ _ hnewLt]
  rw [hloadHigh, hloadLow]
  rw [← show setFeeProtocolNewFeeProtocolNat I % 2 ^ 8 = setFeeProtocolNewFeeProtocolNat I by
    exact Nat.mod_eq_of_lt hnewLt]
  rw [ulit_toNat' _ hsourceLtNested]
  rw [Nat.mod_eq_of_lt (setFeeProtocolNewFeeProtocolNat_mod_lt I)]
  exact Nat.mod_eq_of_lt (setFeeProtocolFeeProtocolSlotWord_nat_lt evm I)
  exact (codeOwnerStorageWord I σ ⟨0⟩).val.isLt

theorem setFeeProtocolEvmUnlockedClearMask_toNat :
    setFeeProtocolEvmUnlockedClearMask.toNat = 2 ^ 256 - 2 ^ 248 + (2 ^ 240 - 1) := by
  native_decide

theorem setFeeProtocolEvmUnlockedTrueSlotWord_eq {evm : EVM.State} {σ : AccountMap}
    {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ evm.accountMap) (hEnv : evm.executionEnv = I) :
    setFeeProtocolEvmUnlockedTrueSlotWord σ I = setFeeProtocolUnlockedTrueSlotWord evm := by
  have hload := setFeeProtocolStorageLoad_codeOwner_eq (evm := evm) (σ := σ) (I := I)
    hAccounts hEnv
  have hclearLt :
      (codeOwnerStorageWord I σ ⟨0⟩).toNat % 2 ^ 240 +
          (codeOwnerStorageWord I σ ⟨0⟩).toNat / 2 ^ 248 * 2 ^ 248 < UInt256.size := by
    rw [← natLandClearByte240 (codeOwnerStorageWord I σ ⟨0⟩).toNat
      (codeOwnerStorageWord I σ ⟨0⟩).val.isLt]
    exact lt_of_le_of_lt (nat_land_le_right _ _) (by norm_num [UInt256.size])
  have hloadHigh :
      (codeOwnerStorageWord I σ ⟨0⟩).toNat / 2 ^ 248 * 2 ^ 248 =
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩).toNat / 2 ^ 248 *
          2 ^ 248 :=
    congrArg (fun w : UInt256 => w.toNat / 2 ^ 248 * 2 ^ 248) hload.symm
  have hloadLow :
      (codeOwnerStorageWord I σ ⟨0⟩).toNat % 2 ^ 240 =
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩).toNat % 2 ^ 240 :=
    congrArg (fun w : UInt256 => w.toNat % 2 ^ 240) hload.symm
  apply u256_inj
  rw [setFeeProtocolEvmUnlockedTrueSlotWord, setFeeProtocolUnlockedTrueSlotWord]
  rw [u256_lor_toNat, u256_land_toNat]
  rw [setFeeProtocolEvmUnlockedClearMask_toNat]
  rw [nat_land_comm]
  rw [natLandClearByte240]
  rw [Nat.mod_eq_of_lt hclearLt]
  rw [show (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨240⟩).toNat = 2 ^ 240 by native_decide]
  rw [nat_lor_comm]
  rw [nat_lor_packed_true_byte240]
  rw [hloadHigh, hloadLow]
  rw [ulit_toNat' _ (setFeeProtocolUnlockedTrueSlotWord_nat_lt evm)]
  exact Nat.mod_eq_of_lt (setFeeProtocolUnlockedTrueSlotWord_nat_lt evm)
  exact (codeOwnerStorageWord I σ ⟨0⟩).val.isLt

theorem setFeeProtocolFinalAccountMapEquiv {evmOwner : EVM.State} {σOwnerEvm : AccountMap}
    {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σOwnerEvm evmOwner.accountMap)
    (hEnv : evmOwner.executionEnv = I)
    (hfee0 : setFeeProtocolEnabledNat (setFeeProtocolArg0Word I).toNat)
    (hfee1 : setFeeProtocolEnabledNat (setFeeProtocolArg1Word I).toNat) :
    accountMapEquiv
      (sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner σOwnerEvm ⟨0⟩
          (setFeeProtocolEvmFeeProtocolSlotWord σOwnerEvm I))
        ⟨0⟩
        (setFeeProtocolEvmUnlockedTrueSlotWord
          (sstoreAccountMap I.codeOwner σOwnerEvm ⟨0⟩
            (setFeeProtocolEvmFeeProtocolSlotWord σOwnerEvm I)) I))
      (setFeeProtocolAfterUnlockState
        (setFeeProtocolAfterFeeProtocolState evmOwner I)).accountMap := by
  have hfirstWord := setFeeProtocolEvmFeeProtocolSlotWord_eq
    (evm := evmOwner) (σ := σOwnerEvm) (I := I) hAccounts hEnv hfee0 hfee1
  have hFirstAccounts :
      accountMapEquiv
        (sstoreAccountMap I.codeOwner σOwnerEvm ⟨0⟩
          (setFeeProtocolEvmFeeProtocolSlotWord σOwnerEvm I))
        (setFeeProtocolAfterFeeProtocolState evmOwner I).accountMap := by
    rw [hfirstWord]
    simpa [setFeeProtocolAfterFeeProtocolState, storageStore_accountMap, hEnv] using
      accountMapEquiv_sstoreAccountMap I.codeOwner ⟨0⟩
        (setFeeProtocolFeeProtocolSlotWord evmOwner I) hAccounts
  have hFirstEnv : (setFeeProtocolAfterFeeProtocolState evmOwner I).executionEnv = I := by
    simp [setFeeProtocolAfterFeeProtocolState, storageStore_executionEnv, hEnv]
  have hsecondWord := setFeeProtocolEvmUnlockedTrueSlotWord_eq
    (evm := setFeeProtocolAfterFeeProtocolState evmOwner I)
    (σ := sstoreAccountMap I.codeOwner σOwnerEvm ⟨0⟩
      (setFeeProtocolEvmFeeProtocolSlotWord σOwnerEvm I))
    (I := I) hFirstAccounts hFirstEnv
  rw [hsecondWord]
  simpa [setFeeProtocolAfterUnlockState, storageStore_accountMap, hFirstEnv] using
    accountMapEquiv_sstoreAccountMap I.codeOwner ⟨0⟩
      (setFeeProtocolUnlockedTrueSlotWord (setFeeProtocolAfterFeeProtocolState evmOwner I))
      hFirstAccounts

theorem setFeeProtocolStorageLocStore_feeProtocol (evm : EVM.State) (I : ExecutionEnv) :
    storageLocStore evm setFeeProtocolFeeProtocolLoc (setFeeProtocolNewFeeProtocolValue I) =
      some (setFeeProtocolAfterFeeProtocolState evm I) := by
  unfold storageLocStore storageLocWriteWord setFeeProtocolFeeProtocolLoc loc
  simp only [valueToWord, bind, Option.bind]
  congr 2
  apply u256_inj
  let w := Solm.EVM.storageLoad evm evm.executionEnv.codeOwner { val := 0 }
  show fromBytes'
      ((List.take 29 ↑(EVM.Word.toBytesLEWithSizeProof w) ++
          List.take 1 ↑(EVM.Word.toBytesLEWithSizeProof
            (UInt256.ofNat (setFeeProtocolNewFeeProtocolNat I)))) ++
        List.drop (29 + 1) ↑(EVM.Word.toBytesLEWithSizeProof w)) =
    (setFeeProtocolFeeProtocolSlotWord evm I).toNat
  rw [fromBytes'_append, fromBytes'_append]
  rw [fromBytes'_take_wordLE, fromBytes'_take_wordLE, fromBytes'_drop_wordLE]
  rw [show 256 ^ (29 : Nat) = 2 ^ 232 by norm_num [Nat.pow_add]]
  rw [show 256 ^ (1 : Nat) = 2 ^ 8 by norm_num]
  rw [show 256 ^ (30 : Nat) = 2 ^ 240 by norm_num [Nat.pow_add]]
  have hnewLt := setFeeProtocolNewFeeProtocolNat_lt_word I
  rw [ulit_toNat' _ hnewLt]
  have hlen29 : (List.take 29 (EVM.Word.toBytesLEWithSizeProof w).1).length = 29 := by
    rw [List.length_take, (EVM.Word.toBytesLEWithSizeProof w).2]
    norm_num
  have hlen1 :
      (List.take 1 (EVM.Word.toBytesLEWithSizeProof
        (UInt256.ofNat (setFeeProtocolNewFeeProtocolNat I))).1).length = 1 := by
    rw [List.length_take, (EVM.Word.toBytesLEWithSizeProof
      (UInt256.ofNat (setFeeProtocolNewFeeProtocolNat I))).2]
    norm_num
  have hlen30 :
      (List.take 29 (EVM.Word.toBytesLEWithSizeProof w).1 ++
        List.take 1 (EVM.Word.toBytesLEWithSizeProof
          (UInt256.ofNat (setFeeProtocolNewFeeProtocolNat I))).1).length = 30 := by
    rw [List.length_append, hlen29, hlen1]
  rw [hlen29, hlen30]
  rw [show (setFeeProtocolFeeProtocolSlotWord evm I).toNat =
      w.toNat % 2 ^ 232 + (setFeeProtocolNewFeeProtocolNat I % 2 ^ 8) * 2 ^ 232 +
        w.toNat / 2 ^ 240 * 2 ^ 240 by
    dsimp [setFeeProtocolFeeProtocolSlotWord, w]
    exact ulit_toNat' _ (setFeeProtocolFeeProtocolSlotWord_nat_lt evm I)]
  ring

theorem setFeeProtocolStorageLocStore_unlocked_true (evm : EVM.State) :
    storageLocStore evm setFeeProtocolUnlockedLoc (.bool true) =
      some (setFeeProtocolAfterUnlockState evm) := by
  unfold storageLocStore storageLocWriteWord setFeeProtocolUnlockedLoc loc
  simp only [valueToWord, Bool.toUInt256_true, bind, Option.bind]
  congr 2
  apply u256_inj
  let w := Solm.EVM.storageLoad evm evm.executionEnv.codeOwner { val := 0 }
  show fromBytes'
      ((List.take 30 ↑(EVM.Word.toBytesLEWithSizeProof w) ++
          List.take 1 ↑(EVM.Word.toBytesLEWithSizeProof (UInt256.ofNat 1))) ++
        List.drop (30 + 1) ↑(EVM.Word.toBytesLEWithSizeProof w)) =
    (setFeeProtocolUnlockedTrueSlotWord evm).toNat
  rw [show List.take 1 ↑(EVM.Word.toBytesLEWithSizeProof (UInt256.ofNat 1)) =
      ([1] : List UInt8) by
    native_decide]
  rw [fromBytes'_append, fromBytes'_append]
  rw [fromBytes'_take_wordLE, fromBytes'_drop_wordLE]
  rw [show 256 ^ (30 : Nat) = 2 ^ 240 by norm_num [Nat.pow_add]]
  rw [show 256 ^ (31 : Nat) = 2 ^ 248 by norm_num [Nat.pow_add]]
  have hlen30 : (List.take 30 (EVM.Word.toBytesLEWithSizeProof w).1).length = 30 := by
    rw [List.length_take, (EVM.Word.toBytesLEWithSizeProof w).2]
    norm_num
  have hlen31 : (List.take 30 (EVM.Word.toBytesLEWithSizeProof w).1 ++ [1]).length = 31 := by
    rw [List.length_append, hlen30]
    norm_num
  rw [hlen30, hlen31]
  rw [show (setFeeProtocolUnlockedTrueSlotWord evm).toNat =
      w.toNat % 2 ^ 240 + 2 ^ 240 + w.toNat / 2 ^ 248 * 2 ^ 248 by
    dsimp [setFeeProtocolUnlockedTrueSlotWord, w]
    exact ulit_toNat' _ (setFeeProtocolUnlockedTrueSlotWord_nat_lt evm)]
  simp [fromBytes']
  ring

abbrev setFeeProtocolOldFeeProtocolWord (evm : EVM.State) : UInt256 :=
  UInt256.land
    (UInt256.div (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩)
      (slot0ShiftBytes 29))
    slot0Uint8Mask

abbrev setFeeProtocolOldFeeProtocolValue (evm : EVM.State) : Value :=
  .int (Int.ofNat (setFeeProtocolOldFeeProtocolWord evm).toNat)

abbrev setFeeProtocolStoreWithOwnerAndOld (I : ExecutionEnv) (out : ByteArray)
    (evm : EVM.State) : Store :=
  (setFeeProtocolStoreWithOwner I out).insert "feeProtocolOld"
    (setFeeProtocolOldFeeProtocolValue evm)

theorem setFeeProtocolStoreWithOwnerAndOld_feeProtocol0 (I : ExecutionEnv) (out : ByteArray)
    (evm : EVM.State) :
    (setFeeProtocolStoreWithOwnerAndOld I out evm).get? "feeProtocol0" =
      some (setFeeProtocolArg0Value I) := by
  rw [setFeeProtocolStoreWithOwnerAndOld]
  rw [store_get_ne (setFeeProtocolStoreWithOwner I out)
    (setFeeProtocolOldFeeProtocolValue evm) (by decide)]
  exact setFeeProtocolStoreWithOwner_feeProtocol0 I out

theorem setFeeProtocolStoreWithOwnerAndOld_feeProtocol1 (I : ExecutionEnv) (out : ByteArray)
    (evm : EVM.State) :
    (setFeeProtocolStoreWithOwnerAndOld I out evm).get? "feeProtocol1" =
      some (setFeeProtocolArg1Value I) := by
  rw [setFeeProtocolStoreWithOwnerAndOld]
  rw [store_get_ne (setFeeProtocolStoreWithOwner I out)
    (setFeeProtocolOldFeeProtocolValue evm) (by decide)]
  exact setFeeProtocolStoreWithOwner_feeProtocol1 I out

theorem evalExpr_setFeeProtocol_feeProtocol0_withOld {v : PoolImmutables}
    (evm evmOld : EVM.State) (I : ExecutionEnv) (out : ByteArray) :
    evalExpr? (config v)
        { contract := contract v, locals := setFeeProtocolStoreWithOwnerAndOld I out evmOld }
        evm (.var "feeProtocol0") = .ok (setFeeProtocolArg0Value I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [setFeeProtocolStoreWithOwnerAndOld_feeProtocol0]

theorem evalExpr_setFeeProtocol_feeProtocol1_withOld {v : PoolImmutables}
    (evm evmOld : EVM.State) (I : ExecutionEnv) (out : ByteArray) :
    evalExpr? (config v)
        { contract := contract v, locals := setFeeProtocolStoreWithOwnerAndOld I out evmOld }
        evm (.var "feeProtocol1") = .ok (setFeeProtocolArg1Value I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [setFeeProtocolStoreWithOwnerAndOld_feeProtocol1]

theorem evalExpr_setFeeProtocol_feeProtocolStorage {v : PoolImmutables}
    (evm : EVM.State) (I : ExecutionEnv) (out : ByteArray) :
    evalExpr? (config v) { contract := contract v, locals := setFeeProtocolStoreWithOwner I out }
      evm (.storage (slot0F "feeProtocol")) =
      .ok (setFeeProtocolOldFeeProtocolValue evm) := by
  rw [evalExpr_storage_scalar
    (t := .int uint8Int)
    (slot := slot0F "feeProtocol")
    (er := { base := "slot0", steps := [.field "feeProtocol"] })
    (loc := setFeeProtocolFeeProtocolLoc)
    (hbase := by simp [slot0F, setFeeProtocolStoreWithOwner, setFeeProtocolStore])
    (her := by
      simp [evalStorageRef, evalStorageRefStep, slot0F, EvalResult.bind, pure, bind])
    (hty := by
      simp [contract, storageDecls, storageTypeAt?, storageTypeStep?, slot0StructTy,
        uint8St])
    (hloc := by
      funext evm
      simp [config, storageLayout, storageLayoutRaw, solidityStorageLayout,
        setFeeProtocolFeeProtocolLoc, loc])]
  simpa [setFeeProtocolOldFeeProtocolValue, setFeeProtocolOldFeeProtocolWord] using
    slot0StorageLocLoad_feeProtocol evm

theorem setFeeProtocolArg1Word_toNat_lt_wordModulus (I : ExecutionEnv) :
    (setFeeProtocolArg1Word I).toNat < EVM.wordModulus := by
  have h1small : (setFeeProtocolArg1Word I).toNat < 2 ^ 8 := by
    simpa [setFeeProtocolArg1Word, setFeeProtocolUint8Mask, slot0Uint8Mask] using
      slot0Uint8Mask_bound (calldataWord I.calldata 36)
  exact lt_trans h1small (by
    change 2 ^ 8 < 2 ^ 256
    exact Nat.pow_lt_pow_right (by norm_num) (by norm_num))

theorem setFeeProtocolArg1Word_int_lt_wordModulus (I : ExecutionEnv) :
    (Int.ofNat (setFeeProtocolArg1Word I).toNat) < (EVM.wordModulus : Int) :=
  Int.ofNat_lt.mpr (setFeeProtocolArg1Word_toNat_lt_wordModulus I)

theorem evalBinaryOp_setFeeProtocol_shl_feeProtocol1 (I : ExecutionEnv) :
    evalBinaryOp? .shl (setFeeProtocolArg1Value I) (.int 4) =
      .ok (.int (((setFeeProtocolArg1Word I).toNat : Int) * 2 ^ (4 : Nat) %
        (EVM.wordModulus : Int))) := by
  have h1ltInt := setFeeProtocolArg1Word_int_lt_wordModulus I
  simp only [evalBinaryOp?]
  rw [if_pos (by
    constructor
    · exact Int.natCast_nonneg _
    · constructor
      · exact h1ltInt
      · norm_num)]
  rw [if_neg (by norm_num)]
  rw [show Int.toNat 4 = 4 by native_decide]
  rw [show (Int.ofNat (setFeeProtocolArg1Word I).toNat).toNat =
      (setFeeProtocolArg1Word I).toNat by simp]

theorem evalBinaryOp_setFeeProtocol_add_newFeeProtocol (I : ExecutionEnv) :
    evalBinaryOp? .add (setFeeProtocolArg0Value I)
        (.int (((setFeeProtocolArg1Word I).toNat : Int) * 2 ^ (4 : Nat) %
          (EVM.wordModulus : Int))) =
      .ok (setFeeProtocolNewFeeProtocolValue I) := by
  simp only [evalBinaryOp?]
  congr 2

theorem evalExpr_setFeeProtocol_shl_feeProtocol1_withOld {v : PoolImmutables}
    (evm evmOld : EVM.State) (I : ExecutionEnv) (out : ByteArray) :
    evalExpr? (config v)
        { contract := contract v, locals := setFeeProtocolStoreWithOwnerAndOld I out evmOld }
        evm (shlE (.var "feeProtocol1") (.intLit 4)) =
      .ok (.int (((setFeeProtocolArg1Word I).toNat : Int) * 2 ^ (4 : Nat) %
        (EVM.wordModulus : Int))) := by
  simp only [shlE, evalExpr?, evalExpr_setFeeProtocol_feeProtocol1_withOld, bind,
    EvalResult.bind, pure]
  exact evalBinaryOp_setFeeProtocol_shl_feeProtocol1 I

theorem evalExpr_setFeeProtocol_newFeeProtocol_withOld {v : PoolImmutables}
    (evm evmOld : EVM.State) (I : ExecutionEnv) (out : ByteArray) :
    evalExpr? (config v)
        { contract := contract v, locals := setFeeProtocolStoreWithOwnerAndOld I out evmOld }
        evm (addE (.var "feeProtocol0") (shlE (.var "feeProtocol1") (.intLit 4))) =
      .ok (setFeeProtocolNewFeeProtocolValue I) := by
  simp only [addE, evalExpr?, evalExpr_setFeeProtocol_feeProtocol0_withOld,
    evalExpr_setFeeProtocol_shl_feeProtocol1_withOld, bind, EvalResult.bind]
  exact evalBinaryOp_setFeeProtocol_add_newFeeProtocol I

theorem assignStorageRef_setFeeProtocol_feeProtocol {v : PoolImmutables}
    (evm evmOld : EVM.State) (I : ExecutionEnv) (out : ByteArray) :
    assignStorageRef? (config v)
        { contract := contract v, locals := setFeeProtocolStoreWithOwnerAndOld I out evmOld }
        evm .storage (slot0F "feeProtocol") (setFeeProtocolNewFeeProtocolValue I) =
      .ok ({ contract := contract v,
             locals := setFeeProtocolStoreWithOwnerAndOld I out evmOld },
        setFeeProtocolAfterFeeProtocolState evm I) := by
  apply assignStorageRef_storage_scalar_value
      (er := { base := "slot0", steps := [.field "feeProtocol"] })
      (ty := .elem (.int uint8Int))
      (loc := setFeeProtocolFeeProtocolLoc)
  · simp [slot0F, setFeeProtocolStoreWithOwnerAndOld, setFeeProtocolStoreWithOwner,
      setFeeProtocolStore]
  · simp [evalStorageRef, evalStorageRefStep, slot0F, EvalResult.bind, pure, bind]
  · simp [contract, storageDecls, storageTypeAt?, storageTypeStep?, slot0StructTy,
      uint8St]
  · funext evm
    simp [config, storageLayout, storageLayoutRaw, solidityStorageLayout,
      setFeeProtocolFeeProtocolLoc, loc]
  · trivial
  · exact setFeeProtocolStorageLocStore_feeProtocol evm I

theorem assignStorageRef_setFeeProtocol_unlocked_true {v : PoolImmutables}
    (evm evmOld : EVM.State) (I : ExecutionEnv) (out : ByteArray) :
    assignStorageRef? (config v)
        { contract := contract v, locals := setFeeProtocolStoreWithOwnerAndOld I out evmOld }
        evm .storage (slot0F "unlocked") (.bool true) =
      .ok ({ contract := contract v,
             locals := setFeeProtocolStoreWithOwnerAndOld I out evmOld },
        setFeeProtocolAfterUnlockState evm) := by
  apply assignStorageRef_storage_scalar_value
      (er := { base := "slot0", steps := [.field "unlocked"] })
      (ty := .elem .bool)
      (loc := setFeeProtocolUnlockedLoc)
  · simp [slot0F, setFeeProtocolStoreWithOwnerAndOld, setFeeProtocolStoreWithOwner,
      setFeeProtocolStore]
  · simp [evalStorageRef, evalStorageRefStep, slot0F, EvalResult.bind, pure, bind]
  · simp [contract, storageDecls, storageTypeAt?, storageTypeStep?, slot0StructTy, boolSt]
  · funext evm
    simp [config, storageLayout, storageLayoutRaw, solidityStorageLayout,
      setFeeProtocolUnlockedLoc, loc]
  · trivial
  · exact setFeeProtocolStorageLocStore_unlocked_true evm

theorem uniswapV3PoolSetFeeProtocolSourceSuccessBody
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
          .require (eqE (.env .caller) (.var "_factoryOwner")),
          .require
            (andE (feeProtocolEnabled (.var "feeProtocol0"))
              (feeProtocolEnabled (.var "feeProtocol1"))) ]
        (.ok { contract := contract v, locals := setFeeProtocolStoreWithOwner I out } evmOwner)) :
    ExecTransitionBody (config v) (contract v)
      (initState cA gh bl σ σ₀ g A I) (setFeeProtocolStore I)
      (setfeeprotocolTransition v).body
      (.returned
        { contract := contract v, locals := setFeeProtocolStoreWithOwnerAndOld I out evmOwner }
        (setFeeProtocolAfterUnlockState
          (setFeeProtocolAfterFeeProtocolState evmOwner I))
        none) := by
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
        .assign .storage (slot0F "unlocked") (.boolLit true) ]
      (.returned
        { contract := contract v, locals := setFeeProtocolStoreWithOwnerAndOld I out evmOwner }
        (setFeeProtocolAfterUnlockState
          (setFeeProtocolAfterFeeProtocolState evmOwner I))
        none)
  refine ExecFuncBody.execBlockOK ?_
  have htail :
      ExecBlock (config v)
        { contract := contract v, locals := setFeeProtocolStoreWithOwner I out } evmOwner
        [ .letDecl "feeProtocolOld" (some uint8) (.storage (slot0F "feeProtocol")),
          .assign .storage (slot0F "feeProtocol")
            (addE (.var "feeProtocol0") (shlE (.var "feeProtocol1") (.intLit 4))),
          .assign .storage (slot0F "unlocked") (.boolLit true) ]
        (.ok
          { contract := contract v, locals := setFeeProtocolStoreWithOwnerAndOld I out evmOwner }
          (setFeeProtocolAfterUnlockState
            (setFeeProtocolAfterFeeProtocolState evmOwner I))) := by
    refine ExecBlock.consNormal
      (ExecStmt.letDecl (evalExpr_setFeeProtocol_feeProtocolStorage evmOwner I out)) ?_
    refine ExecBlock.consNormal
      (ExecStmt.assign
        (evalExpr_setFeeProtocol_newFeeProtocol_withOld
          evmOwner evmOwner I out)
        (assignStorageRef_setFeeProtocol_feeProtocol evmOwner evmOwner I out)) ?_
    exact ExecBlock.consNormal
      (ExecStmt.assign (by simp [evalExpr?, pure])
        (assignStorageRef_setFeeProtocol_unlocked_true
          (setFeeProtocolAfterFeeProtocolState evmOwner I) evmOwner I out))
      ExecBlock.nil
  simpa using execBlock_append hprefix htail

end Benchmarks.UniswapV3Pool
