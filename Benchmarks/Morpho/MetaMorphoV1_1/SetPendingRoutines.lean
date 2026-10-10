import Benchmarks.Morpho.MetaMorphoV1_1.SetTimelockSource
import Benchmarks.Morpho.MetaMorphoV1_1.SetGuardianSource
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_069
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_071

/-! Bytecode implementations of the internal pending-update setters. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode

set_option maxRecDepth 2000 in
theorem setTimelockReturn {evm : EVM.State} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {k C : Nat}
    {R : List UInt256} {value ret : UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 5 ≤ 1024)
    (hperm : evm.executionEnv.perm = true)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD (deployedRuntime v) evm.executionEnv g s0 ⟨14755⟩ (value :: ret :: R)
      mem aw rdata evm.accountMap k C) :
    ∃ aw' k' C', RD (deployedRuntime v) evm.executionEnv g s0 ret R
      (value.toByteArray.write 0 mem (memLoad ⟨64⟩ mem).toNat 32)
      aw' rdata (setTimelockState evm value).accountMap k' C' := by
  simpa only [setTimelockState, setTimelockValueState, storageStore_accountMap,
    storageStore_executionEnv] using
    (metaMorphoV1_1_block_14755_packed (immWords := wordsOf (immStore v)) hstack hperm hret rd)

set_option maxRecDepth 2000 in
theorem setGuardianReturn {evm : EVM.State} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {k C : Nat}
    {R : List UInt256} {value : AccountAddress} {ret : UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 7 ≤ 1024)
    (hperm : evm.executionEnv.perm = true)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD (deployedRuntime v) evm.executionEnv g s0 ⟨15404⟩
      (UInt256.ofNat value.val :: ret :: R) mem aw rdata evm.accountMap k C) :
    ∃ aw' k' C', RD (deployedRuntime v) evm.executionEnv g s0 ret R mem
      aw' rdata (setGuardianState evm value).accountMap k' C' := by
  obtain ⟨aw', k', C', h⟩ := metaMorphoV1_1_block_15404_packed
    (immWords := wordsOf (immStore v)) hstack hperm hret rd
  have hm : UInt256.lor
      (UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
        (UInt256.ofNat 1)) (UInt256.ofNat value.val))
      (UInt256.land (UInt256.lnot (UInt256.sub
        (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)))
        (codeOwnerStorageWord evm.executionEnv evm.accountMap (UInt256.ofNat 12))) =
      setAddressOffset0Word (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨12⟩)
        (UInt256.ofNat value.val) := by
    change UInt256.lor (UInt256.land solcAddrMask (UInt256.ofNat value.val))
      (UInt256.land (UInt256.lnot solcAddrMask)
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨12⟩)) = _
    rw [u256_land_comm solcAddrMask]
    exact setAddressOffset0Word_bytecode _ _
  rw [hm] at h
  refine ⟨aw', k', C', ?_⟩
  simpa only [setGuardianState, setGuardianValueState, storageStore_accountMap,
    storageStore_executionEnv] using h

set_option maxRecDepth 2000 in
theorem setTimelockStatic {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} {value : UInt256} {ret : UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 5 ≤ 1024)
    (hperm : I.perm = false)
    (rd : RD (deployedRuntime v) I g s0 ⟨14755⟩ (value :: ret :: R)
      mem aw rdata σ k C) : RDstatic (deployedRuntime v) g s0 := by
  let r0 := rd
  have r1 := r0.jumpdest (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨14755⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none,
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.dup1 (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨14756⟩ : UInt256), UInt8.ofNat 128, .DUP1, none,
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.push1 (UInt256.ofNat 14) (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨14757⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 14), 1),
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  exact r3.sstoreStatic hperm (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨14759⟩ : UInt256), UInt8.ofNat 85, .SSTORE, none,
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)

set_option maxRecDepth 2000 in
theorem setGuardianStatic {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} {value : AccountAddress} {ret : UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 7 ≤ 1024)
    (hperm : I.perm = false)
    (rd : RD (deployedRuntime v) I g s0 ⟨15404⟩ (UInt256.ofNat value.val :: ret :: R)
      mem aw rdata σ k C) : RDstatic (deployedRuntime v) g s0 := by
  let r0 := rd
  have r1 := r0.jumpdest (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨15404⟩ : UInt256), UInt8.ofNat 91, .JUMPDEST, none,
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r2 := r1.push1 (UInt256.ofNat 12) (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨15405⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 12), 1),
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r3 := r2.dup1 (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨15407⟩ : UInt256), UInt8.ofNat 128, .DUP1, none,
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  obtain ⟨_, _, r4⟩ := RD.sload r3 (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨15408⟩ : UInt256), UInt8.ofNat 84, .SLOAD, none,
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 1) (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨15409⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1),
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r6 := r5.push1 (UInt256.ofNat 1) (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨15411⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1),
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r7 := r6.push1 (UInt256.ofNat 160) (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨15413⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 160), 1),
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r8 := r7.shl (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨15415⟩ : UInt256), UInt8.ofNat 27, .SHL, none,
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r9 := r8.sub (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨15416⟩ : UInt256), UInt8.ofNat 3, .SUB, none,
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r10 := r9.not (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨15417⟩ : UInt256), UInt8.ofNat 25, .NOT, none,
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r11 := r10.and (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨15418⟩ : UInt256), UInt8.ofNat 22, .AND, none,
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r12 := r11.push1 (UInt256.ofNat 1) (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨15419⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1),
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r13 := r12.push1 (UInt256.ofNat 1) (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨15421⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 1), 1),
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r14 := r13.push1 (UInt256.ofNat 160) (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨15423⟩ : UInt256), UInt8.ofNat 96, .Push .PUSH1, some ((UInt256.ofNat 160), 1),
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r15 := r14.shl (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨15425⟩ : UInt256), UInt8.ofNat 27, .SHL, none,
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r16 := r15.sub (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨15426⟩ : UInt256), UInt8.ofNat 3, .SUB, none,
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r17 := r16.swap3 (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨15427⟩ : UInt256), UInt8.ofNat 146, .SWAP3, none,
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r18 := r17.swap1 (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨15428⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none,
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r19 := r18.swap3 (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨15429⟩ : UInt256), UInt8.ofNat 146, .SWAP3, none,
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r20 := r19.and (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨15430⟩ : UInt256), UInt8.ofNat 22, .AND, none,
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r21 := r20.swap2 (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨15431⟩ : UInt256), UInt8.ofNat 145, .SWAP2, none,
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r22 := r21.dup3 (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨15432⟩ : UInt256), UInt8.ofNat 130, .DUP3, none,
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r23 := r22.or (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨15433⟩ : UInt256), UInt8.ofNat 23, .OR, none,
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  have r24 := r23.swap1 (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨15434⟩ : UInt256), UInt8.ofNat 144, .SWAP1, none,
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)
  exact r24.sstoreStatic hperm (by
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨15435⟩ : UInt256), UInt8.ofNat 85, .SSTORE, none,
      immutableLayout_inBounds, immutableTemplate_size64)) (by evm_ov)

end Benchmarks.Morpho.MetaMorphoV1_1
