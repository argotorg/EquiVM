import Benchmarks.Safe.ViaIR.SetupPaymentTrace
import Benchmarks.Safe.ViaIR.SetupDataAllocate
import Benchmarks.Safe.ViaIR.SetupModulesTrace

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe.ViaIR

set_option maxRecDepth 5000

theorem setupModulesMemory_load (mem : ByteArray) (off : UInt256)
    (hin : off.toNat + 32 ≤ mem.size) (hlo : 64 ≤ off.toNat) :
    memLoad off (setupModulesMemory mem) = memLoad off mem := by
  rw [memLoadReadWord, setupModulesMemory_read mem off.toNat 32 hin hlo, ← memLoadReadWord]

theorem safeSetupModulesCallTrace (evm : EVM.State)
    {I g s0 σ k C aw mem rdata n len locals} {scratch : UInt256} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨3401⟩
      (scratch :: UInt256.ofNat len :: UInt256.ofNat (setupDataStart I.calldata) :: ⟨3409⟩ ::
        calldataWord I.calldata 68 :: calldataWord I.calldata 68 ::
        calldataWord I.calldata 164 :: calldataWord I.calldata 228 ::
        calldataWord I.calldata 196 :: ⟨0⟩ :: R) mem aw rdata σ k C)
    (hee : evm.executionEnv = I) (hacc : evm.accountMap = σ) (hworld : evm.σ₀ = s0.σ₀)
    (hl : SetupLocals (setupCalldataInput I.calldata n len) locals)
    (hb : SetupCalldataBounds I.calldata n len)
    (hf : memLoad ⟨64⟩ mem = UInt256.ofNat (160 + 32 * n)) (hm : 128 ≤ mem.size)
    (hperm : I.perm = true) (hov : R.length + 36 ≤ 1024) :
    SetupTailOutcome fork (setupCalldataInput I.calldata n len)
      { contract := contract, locals := locals } evm (setupTransition.body.drop 5) g s0 := by
  let p := setupCalldataInput I.calldata n len
  let ptr := 160 + 32 * n
  let finish := ptr + 32 + ABI.paddedSize len
  let allocated := calldataBufferMemory I.calldata mem (setupDataStart I.calldata)
    ptr len len finish
  have hword : ptr + 64 + len < UInt256.size := by
    have := hb.ownersLength
    have := hb.dataLength
    change 160 + 32 * n + 64 + len < 2 ^ 256
    omega
  have hlen : p.payload.size = len := by
    change (I.calldata.extract (setupDataStart I.calldata)
      (setupDataStart I.calldata + len)).size = len
    rw [ByteArray.size_extract]
    have := hb.dataEnd
    omega
  have hn : p.owners.length = n := calldataWords_length _ _ _
  have halloc : BytesMemory allocated ptr p.payload :=
    calldataBufferMemory_bytes _ _ _ _ _ _ (by omega) hb.dataEnd (by omega)
  have hsize : 128 ≤ allocated.size := by
    change 128 ≤ (calldataBufferMemory _ _ _ _ _ _ _).size
    rw [calldataBufferMemory_size _ _ _ _ _ _ _ (by omega) hb.dataEnd]
    omega
  have hfree : memLoad ⟨64⟩ allocated = UInt256.ofNat finish :=
    calldataBufferMemory_free _ _ _ _ _ _ _ (by omega) (by omega) hb.dataEnd
  obtain ⟨hbad, hrev⟩ | ⟨aw₁, k₁, C₁, hcap, h₁⟩ :=
    safeSetupModulesAllocate h hb hf hword (by simp; omega) (by jump_dest)
  · refine .allocationRevert ?_ hrev
    intro ha
    have hlim := safeSetupAllocationLimit_le p
    have hbase := le_trans ha hlim
    rw [hn, hlen] at hbase
    unfold ABI.paddedSize at hbad
    omega
  obtain ⟨hrev, hs⟩ | ⟨f', evm', out, aw₂, k₂, C₂, x, y, hs, hee', hw', h₂⟩ :=
    safeSetupModulesTrace p.modulesInput evm h₁ hee hacc hworld halloc (by omega)
      (by change ptr + 64 + p.payload.size < _; rw [hlen]; exact hword)
      hb.target hperm (by simp; omega)
  · exact .reverted (.consRevert (safeSetupModulesCall p evm hl hs)) hrev
  have htail := safeSetupPaymentTrace p evm' h₂ hee' rfl hw'
    (hl.set "_modulesSetup" .unit (by decide)) hb.paymentToken hb.paymentReceiver
    ((setupModulesMemory_load allocated ⟨64⟩ (by change 96 ≤ allocated.size; omega)
      (by decide)).trans hfree)
    (by dsimp [finish, ptr]; omega)
    (by rw [hn, hlen]) hcap hperm hov
  exact htail.prepend (safeSetupModulesCall p evm hl hs)

end Benchmarks.Safe.ViaIR
