import Benchmarks.Safe.Common
import Benchmarks.Safe.Blocks.Runtime_007
import Benchmarks.Safe.Blocks.Runtime_008

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open safeRuntimeBlocks

namespace Benchmarks.Safe

set_option maxRecDepth 100000 in
theorem safeReturnWordFromMem {I g s0 σ k C aw rdata} {v : UInt256}
    {mem : ByteArray} {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨974⟩ (v :: R) mem aw rdata σ k C)
    (hov : R.length + 3 ≤ 1024)
    (hptr : memLoad (UInt256.ofNat 64) mem = ⟨128⟩)
    (hptr' : memLoad (UInt256.ofNat 64) (v.toByteArray.write 0 mem 128 32) = ⟨128⟩)
    (hread : (v.toByteArray.write 0 mem 128 32).readWithPadding 128 32 = v.toByteArray) :
    RDret safeBytecode g s0 σ v.toByteArray := by
  have h771 := safeRuntime_block_974 hov (by jump_dest) h
  simp only [safeRuntime_block_974_stack, safeRuntime_block_974_memory, hptr,
    show (⟨128⟩ : UInt256).toNat = 128 by rfl] at h771
  have hret := safeRuntime_block_771 hov h771
  simpa only [hptr', show (UInt256.sub (UInt256.ofNat 32 + ⟨128⟩) ⟨128⟩).toNat = 32 by
    decide, show (⟨128⟩ : UInt256).toNat = 128 by rfl, hread] using hret

theorem safeReturnWord {I g s0 σ k C rdata} {v : UInt256} {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨974⟩ (v :: R) solcFreePtrMem (UInt256.ofNat 3)
      rdata σ k C)
    (hov : R.length + 3 ≤ 1024) : RDret safeBytecode g s0 σ v.toByteArray := by
  exact safeReturnWordFromMem h hov solcFreePtrMem_mload64
    (solcReturnMem_mload64 v) (solcReturnMem_read128 v)

theorem safeReturnWordFromScratch {I g s0 σ k C rdata aw} {v : UInt256}
    {R : List UInt256} {scratch : ByteArray}
    (h : RD safeBytecode I g s0 ⟨974⟩ (v :: R) scratch aw rdata σ k C)
    (hov : R.length + 3 ≤ 1024)
    (hsize : scratch.size = 96)
    (hread : scratch.readWithPadding 64 32 = (⟨128⟩ : UInt256).toByteArray) :
    RDret safeBytecode g s0 σ v.toByteArray := by
  exact safeReturnWordFromMem h hov
    (mloadFreePtrValue (by rw [hsize]; decide) hread)
    (solcScratchReturnMem_mload64 v hsize hread) (solcScratchReturnMem_read128 v hsize)

set_option maxRecDepth 100000 in
theorem safeReturnBoolFromScratch {I g s0 σ k C rdata aw} {b : Bool}
    {R : List UInt256} {scratch : ByteArray}
    (h : RD safeBytecode I g s0 ⟨759⟩ (b.toUInt256 :: R) scratch aw rdata σ k C)
    (hov : R.length + 3 ≤ 1024)
    (hsize : scratch.size = 96)
    (hread : scratch.readWithPadding 64 32 = (⟨128⟩ : UInt256).toByteArray) :
    RDret safeBytecode g s0 σ b.toUInt256.toByteArray := by
  have hptr : memLoad (UInt256.ofNat 64) scratch = ⟨128⟩ :=
    mloadFreePtrValue (by rw [hsize]; decide) hread
  have hb : UInt256.isZero (UInt256.isZero b.toUInt256) = b.toUInt256 := by
    cases b <;> rfl
  have h771 := safeRuntime_block_759 hov h
  simp only [safeRuntime_block_759_stack, safeRuntime_block_759_memory, hptr, hb,
    show (⟨128⟩ : UInt256).toNat = 128 by rfl] at h771
  have hret := safeRuntime_block_771 hov h771
  have hptr' : memLoad (UInt256.ofNat 64)
      (b.toUInt256.toByteArray.write 0 scratch 128 32) = ⟨128⟩ :=
    solcScratchReturnMem_mload64 b.toUInt256 hsize hread
  have hbytes : (b.toUInt256.toByteArray.write 0 scratch 128 32).readWithPadding 128 32 =
      b.toUInt256.toByteArray := solcScratchReturnMem_read128 b.toUInt256 hsize
  simpa only [hptr',
    show (UInt256.sub (UInt256.ofNat 32 + ⟨128⟩) ⟨128⟩).toNat = 32 by decide,
    show (⟨128⟩ : UInt256).toNat = 128 by rfl,
    hbytes] using hret

-- LIBRARY CANDIDATE: ABI encoding for an arbitrary normalized boolean.
theorem boolReturnEncoding (b : Bool) :
    encodeReturnValue? (.elem .bool) (.bool b) = some b.toUInt256.toByteArray := by
  cases b
  · exact boolFalseReturnEncoding
  · exact boolTrueReturnEncoding

end Benchmarks.Safe
