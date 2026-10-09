import Benchmarks.Safe.BoolBytesEncoding
import Benchmarks.Safe.MemoryBytesDecoded
import Benchmarks.Safe.Blocks.Runtime_007

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open safeRuntimeBlocks

namespace Benchmarks.Safe

set_option maxRecDepth 100000 in
theorem safeBoolBytesReturn {I g s0 σ k C aw mem rdata src dst} {R : List UInt256}
    (z : Bool) (out : ByteArray)
    (h : RD safeBytecode I g s0 ⟨873⟩ (UInt256.ofNat src :: z.toUInt256 :: R)
      mem aw rdata σ k C)
    (hf : memLoad ⟨64⟩ mem = UInt256.ofNat dst)
    (hl : memLoad (UInt256.ofNat src) mem = UInt256.ofNat out.size)
    (hd : mem.readWithPadding (src + 32) out.size = out)
    (hm : 96 ≤ mem.size) (hp : 96 ≤ dst)
    (hin : src + 32 + out.size ≤ mem.size) (ha : src + 32 + out.size ≤ dst)
    (hb : dst + 160 + out.size < UInt256.size) (hov : R.length + 18 ≤ 1024) :
    RDret safeBytecode g s0 σ (boolBytesReturnBytes z out) := by
  let headMem := boolBytesHeaderMemory mem dst z
  let words := memoryWords headMem (src + 32) ((out.size + 31) / 32)
  have hn : words.length = (out.size + 31) / 32 := memoryWords_length _ _ _
  have hh : headMem.size = max mem.size (dst + 64) := boolBytesHeaderMemory_size _ _ _
  have hi : src + 32 + 32 * words.length ≤ headMem.size := by rw [hh, hn]; omega
  have hd' : headMem.readWithPadding (src + 32) out.size = out := by
    rw [show headMem = writeWords mem dst [z.toUInt256, ⟨64⟩] from rfl,
      writeWords_readBelow _ _ _ _ _ hin ha, hd]
  have hw : (wordBytes words).extract 0 out.size = out :=
    (memoryWords_prefix _ _ _ ((out.size + 31) / 32)
      (by simpa only [hn] using hi) (by omega)).trans hd'
  have hl' : memLoad (UInt256.ofNat src) headMem = UInt256.ofNat out.size := by
    rw [memLoadReadWord, ulit_toNat' _ (by omega)]
    rw [show headMem = writeWords mem dst [z.toUInt256, ⟨64⟩] from rfl,
      writeWords_readBelow _ _ _ _ _ (by omega) (by omega)]
    simpa only [ulit_toNat' src (by omega)] using (memLoadReadWord mem (UInt256.ofNat src)).symm
      |>.trans hl
  have h32 : (UInt256.ofNat dst + UInt256.ofNat 32).toNat = dst + 32 :=
    uadd_ofNat_toNat (by omega) (by decide) (by omega)
  have h64 : UInt256.ofNat dst + UInt256.ofNat 64 = UInt256.ofNat (dst + 64) := by
    apply u256_inj
    rw [uadd_toNat, ulit_toNat' dst (by omega)]
    rfl
  have hz : UInt256.isZero (UInt256.isZero z.toUInt256) = z.toUInt256 := by
    cases z <;> decide
  have h₁ := safeRuntime_block_873 (by simp; omega) (by jump_dest) h
  change memLoad (UInt256.ofNat 64) mem = UInt256.ofNat dst at hf
  simp only [safeRuntime_block_873_stack, hf] at h₁
  have h₂ := safeRuntime_block_9810 (by simp; omega) (by jump_dest) h₁
  simp only [safeRuntime_block_9810_stack, safeRuntime_block_9810_memory, hz,
    h32, h64, ulit_toNat' dst (by omega)] at h₂
  change RD safeBytecode I g s0 ⟨9767⟩
    (UInt256.ofNat src :: UInt256.ofNat (dst + 64) :: ⟨9836⟩ :: ⟨0⟩ ::
      UInt256.ofNat dst :: UInt256.ofNat src :: z.toUInt256 :: ⟨771⟩ :: R)
    headMem _ rdata σ _ _ at h₂
  obtain ⟨aw₃, k₃, C₃, h₃⟩ := safeMemoryBytesEncodeInto words h₂ hl'
    (memoryWords_view _ _ _) hn (by rw [hn]; omega) hi (by rw [hn]; omega)
    (by simp; omega) (by jump_dest)
  have h₄ := safeRuntime_block_9836 (by simp; omega) (by jump_dest) h₃
  have hr := safeRuntime_block_771 (by simp; omega) h₄
  have hf' : memLoad (UInt256.ofNat 64)
      (memoryBytesEncodedInto headMem (dst + 64) out.size words) = UInt256.ofNat dst := by
    rw [memLoadReadWord, show (UInt256.ofNat 64).toNat = 64 by rfl,
      memoryBytesEncodedInto_preserved _ _ _ _ _ _ (by rw [hh]; omega) (by omega)]
    rw [show headMem = writeWords mem dst [z.toUInt256, ⟨64⟩] from rfl,
      writeWords_readBelow _ _ _ _ _ hm hp]
    exact (memLoadReadWord mem (UInt256.ofNat 64)).symm.trans hf
  rw [hf', ulit_toNat' dst (by omega)] at hr
  have hlen : (UInt256.sub (UInt256.ofNat (dst + 64 + 32 + 32 * words.length))
      (UInt256.ofNat dst)).toNat = 96 + 32 * words.length := by
    have he : (UInt256.ofNat (dst + 64 + 32 + 32 * words.length)).toNat =
        dst + 64 + 32 + 32 * words.length := ulit_toNat' _ (by rw [hn]; omega)
    rw [usub_toNat (by rw [he, ulit_toNat' dst (by omega)]; omega), he,
      ulit_toNat' dst (by omega)]
    omega
  rw [hlen, boolBytesEncodedRead mem dst out.size words z out hn rfl hw] at hr
  exact hr

end Benchmarks.Safe
