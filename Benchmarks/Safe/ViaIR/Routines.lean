import Benchmarks.Safe.ViaIR.Common
import Benchmarks.Safe.ViaIR.Blocks.Runtime_007
import Benchmarks.Safe.ViaIR.Blocks.Runtime_030

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.ViaIR.RuntimeBlocks

namespace Benchmarks.Safe.ViaIR

set_option maxRecDepth 100000 in
theorem safeReturnWordFromMem {I g s0 σ k C aw rdata} {v : UInt256}
    {mem : ByteArray} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨1055⟩ (v :: ⟨32⟩ :: R) mem aw rdata σ k C)
    (hov : R.length + 4 ≤ 1024)
    (hptr : memLoad (UInt256.ofNat 64) mem = ⟨128⟩)
    (hread : (v.toByteArray.write 0 mem 128 32).readWithPadding 128 32 = v.toByteArray) :
    RDret fork safeBytecode g s0 σ v.toByteArray := by
  have hret := safeRuntime_block_1055 hov h
  simpa only [hptr, show (⟨128⟩ : UInt256).toNat = 128 from rfl,
    show (⟨32⟩ : UInt256).toNat = 32 from rfl, hread] using hret

theorem safeReturnWord {I g s0 σ k C rdata} {v : UInt256} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨1055⟩ (v :: ⟨32⟩ :: R) solcFreePtrMem (UInt256.ofNat 3)
      rdata σ k C)
    (hov : R.length + 4 ≤ 1024) : RDret fork safeBytecode g s0 σ v.toByteArray := by
  exact safeReturnWordFromMem h hov solcFreePtrMem_mload64 (solcReturnMem_read128 v)

theorem safeReturnWordFromScratch {I g s0 σ k C rdata aw} {v : UInt256}
    {R : List UInt256} {scratch : ByteArray}
    (h : RD fork safeBytecode I g s0 ⟨1055⟩ (v :: ⟨32⟩ :: R) scratch aw rdata σ k C)
    (hov : R.length + 4 ≤ 1024)
    (hsize : scratch.size = 96)
    (hread : scratch.readWithPadding 64 32 = (⟨128⟩ : UInt256).toByteArray) :
    RDret fork safeBytecode g s0 σ v.toByteArray := by
  exact safeReturnWordFromMem h hov (mloadFreePtrValue (by rw [hsize]; decide) hread)
    (solcScratchReturnMem_read128 v hsize)

set_option maxRecDepth 100000 in
theorem safeReturnBoolFromScratch {I g s0 σ k C rdata aw} {b : Bool}
    {R : List UInt256} {scratch : ByteArray}
    (h : RD fork safeBytecode I g s0 ⟨6377⟩ (b.toUInt256 :: ⟨32⟩ :: R) scratch aw rdata σ k C)
    (hov : R.length + 4 ≤ 1024)
    (hsize : scratch.size = 96)
    (hread : scratch.readWithPadding 64 32 = (⟨128⟩ : UInt256).toByteArray) :
    RDret fork safeBytecode g s0 σ b.toUInt256.toByteArray := by
  have hptr : memLoad (UInt256.ofNat 64) scratch = ⟨128⟩ :=
    mloadFreePtrValue (by rw [hsize]; decide) hread
  have hb : UInt256.isZero (UInt256.isZero b.toUInt256) = b.toUInt256 := by
    cases b <;> rfl
  have hret := safeRuntime_block_6377 hov h
  rw [hptr, hb] at hret
  change RDret fork safeBytecode g s0 σ
    ((solcScratchReturnMem scratch b.toUInt256).readWithPadding 128 32) at hret
  rw [solcScratchReturnMem_read128 _ hsize] at hret
  exact hret

set_option maxRecDepth 100000 in
theorem safeReturnIsZeroFromScratch {I g s0 σ k C rdata aw} {w : UInt256}
    {R : List UInt256} {scratch : ByteArray}
    (h : RD fork safeBytecode I g s0 ⟨6432⟩ (w :: R) scratch aw rdata σ k C)
    (hov : R.length + 4 ≤ 1024)
    (hsize : scratch.size = 96)
    (hread : scratch.readWithPadding 64 32 = (⟨128⟩ : UInt256).toByteArray) :
    RDret fork safeBytecode g s0 σ (UInt256.isZero w).toByteArray := by
  have hptr : memLoad (UInt256.ofNat 64) scratch = ⟨128⟩ :=
    mloadFreePtrValue (by rw [hsize]; decide) hread
  have hret := safeRuntime_block_6432 hov h
  rw [hptr] at hret
  change RDret fork safeBytecode g s0 σ
    ((solcScratchReturnMem scratch (UInt256.isZero w)).readWithPadding 128 32) at hret
  rw [solcScratchReturnMem_read128 _ hsize] at hret
  exact hret

-- LIBRARY CANDIDATE: ABI encoding for an arbitrary normalized boolean.
theorem boolReturnEncoding (b : Bool) :
    encodeReturnValue? (.elem .bool) (.bool b) = some b.toUInt256.toByteArray := by
  cases b
  · exact boolFalseReturnEncoding
  · exact boolTrueReturnEncoding

end Benchmarks.Safe.ViaIR
