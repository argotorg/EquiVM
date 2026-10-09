import Benchmarks.Safe.SetupPaymentTrace
import Benchmarks.Safe.SetupDataAllocate

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe

set_option maxRecDepth 100000

theorem setupModulesMemory_load (mem : ByteArray) (off : UInt256)
    (hin : off.toNat + 32 ≤ mem.size) (hlo : 64 ≤ off.toNat) :
    memLoad off (setupModulesMemory mem) = memLoad off mem := by
  rw [memLoadReadWord, setupModulesMemory_read mem off.toNat 32 hin hlo, ← memLoadReadWord]

theorem safeSetupModulesCallTrace (evm : EVM.State)
    {I g s0 σ k C aw mem rdata n len ptr locals} {ret : UInt256} {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨4719⟩ (setupDecodedStack I.calldata n len (ret :: R))
      mem aw rdata σ k C)
    (hee : evm.executionEnv = I) (hacc : evm.accountMap = σ) (hworld : evm.σ₀ = s0.σ₀)
    (hl : SetupLocals (setupCalldataInput I.calldata n len) locals)
    (hb : SetupCalldataBounds I.calldata n len)
    (hf : memLoad ⟨64⟩ mem = UInt256.ofNat ptr) (hm : 128 ≤ mem.size) (hp : 128 ≤ ptr)
    (hz : memLoad ⟨96⟩ mem = ⟨0⟩) (hptr : ptr + 64 + len < 2 ^ 220)
    (hperm : I.perm = true) (hov : R.length + 36 ≤ 1024)
    (hret : (D_J safeBytecode 0).contains ret = true) :
    VoidRoutineOutcome config { contract := contract, locals := locals } evm
      (setupTransition.body.drop 4) safeBytecode I g s0 ret R := by
  let p := setupCalldataInput I.calldata n len
  let finish := ptr + 32 + ABI.paddedSize len
  let allocated := calldataBufferMemory I.calldata mem (setupDataStart I.calldata)
    ptr len len finish
  have hword : ptr + 64 + len < UInt256.size := by
    have : 2 ^ 220 < UInt256.size := by decide
    omega
  have hlen : p.payload.size = len := by
    change (I.calldata.extract (setupDataStart I.calldata)
      (setupDataStart I.calldata + len)).size = len
    rw [ByteArray.size_extract]
    have := hb.dataEnd
    omega
  have halloc : BytesMemory allocated ptr p.payload :=
    calldataBufferMemory_bytes _ _ _ _ _ _ (by omega) hb.dataEnd (by omega)
  have hsize : 128 ≤ allocated.size := by
    change 128 ≤ (calldataBufferMemory _ _ _ _ _ _ _).size
    rw [calldataBufferMemory_size _ _ _ _ _ _ _ (by omega) hb.dataEnd]
    omega
  have hfree : memLoad ⟨64⟩ allocated = UInt256.ofNat finish :=
    calldataBufferMemory_free _ _ _ _ _ _ _ (by omega) (by omega) hb.dataEnd
  have hzero : memLoad ⟨96⟩ allocated = ⟨0⟩ := by
    have hpres := calldataBufferMemory_preserved I.calldata mem
      (setupDataStart I.calldata) ptr len len finish (by omega) hb.dataEnd
    exact (hpres.load ⟨96⟩ (by decide) (by change 128 ≤ ptr; omega)
      (by change 128 ≤ mem.size; omega)).trans hz
  obtain ⟨aw₁, k₁, C₁, h₁⟩ := safeSetupModulesAllocate h hb hf hword (by simp; omega)
  obtain ⟨hrev, hs⟩ | ⟨f', evm', out, aw₂, k₂, C₂, hs, hee', hw', h₂⟩ :=
    safeSetupModulesTrace p.modulesInput evm h₁ hee hacc hworld halloc (by omega)
      (by change ptr + 64 + p.payload.size < _; rw [hlen]; exact hword)
      hb.target hperm (by simp [setupDecodedStack]; omega) (by jump_dest)
  · exact .reverted (.consRevert (safeSetupModulesCall p evm hl hs)) hrev
  have hpad : ABI.paddedSize len ≤ len + 31 := by unfold ABI.paddedSize; omega
  have hsize₂ : 128 ≤ (setupModulesMemory allocated).size := by
    rw [setupModulesMemory_size allocated (by omega)]
    exact hsize
  have htail := safeSetupPaymentTrace evm' h₂ hee' rfl hw'
    (hl.set "_modulesSetup" .unit (by decide)) hb
    ((setupModulesMemory_load allocated ⟨64⟩ (by change 96 ≤ allocated.size; omega)
      (by decide)).trans hfree)
    hsize₂
    (by dsimp only [finish]; omega)
    ((setupModulesMemory_load allocated ⟨96⟩ (by change 128 ≤ allocated.size; omega)
      (by decide)).trans hzero)
    (by dsimp only [finish]; omega) hov hret
  exact htail.prepend (safeSetupModulesCall p evm hl hs)

end Benchmarks.Safe
