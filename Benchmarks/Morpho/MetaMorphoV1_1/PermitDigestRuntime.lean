import Benchmarks.Morpho.MetaMorphoV1_1.PermitData
import Benchmarks.Morpho.MetaMorphoV1_1.PermitNonceRuntime
import Benchmarks.Morpho.MetaMorphoV1_1.PermitHashRuntime
import Benchmarks.Morpho.MetaMorphoV1_1.TypedDataDomainRuntime

/-! The complete permit nonce and digest computation before signature recovery. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1

def permitDigestMemory (p : PermitData) (evm : State) (v : MetaMorphoV1_1Immutables)
    (mem : ByteArray) (free : Nat) : ByteArray :=
  typedDataDomainMemory v evm.executionEnv
    (permitHashMemory mem free p.owner p.spender p.value (nonceWord evm p.owner) p.deadline)
    (free + 224) (p.structHash evm)

theorem permitDigestMemory_free (p : PermitData) (evm : State) (v : MetaMorphoV1_1Immutables)
    (mem : ByteArray) (free : Nat) :
    memLoad (UInt256.ofNat 64) (permitDigestMemory p evm v mem free) =
      UInt256.ofNat (domainSeparatorCursor v evm.executionEnv (free + 224)) := by
  apply typedDataDomainMemory_free
  · omega
  · have := permitHashMemory_size mem free p.owner p.spender p.value (nonceWord evm p.owner)
      p.deadline
    omega
  · exact permitHashMemory_free _ _ _ _ _ _ _

theorem permitDigestRoutine {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} (p : PermitData) (v : MetaMorphoV1_1Immutables) (free : Nat)
    (hstack : R.length + 17 ≤ 1024) (hperm : I.perm = true)
    (hlo : 96 ≤ free) (hfit : free + 416 < 2 ^ 64) (hmem : 96 ≤ mem.size)
    (hfree : memLoad (UInt256.ofNat 64) mem = UInt256.ofNat free)
    (hs : SourceState s0 I σ evm)
    (rd : RD (deployedRuntime v) I g s0 ⟨1648⟩
      (p.sigV :: UInt256.ofNat p.owner.toNat :: UInt256.ofNat p.spender.toNat :: p.value ::
        p.deadline :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨19083⟩
      (p.digest v evm :: p.sigV :: uInt256OfByteArray (I.calldata.readBytes 164 32) ::
        uInt256OfByteArray (I.calldata.readBytes 196 32) :: ⟨1831⟩ :: ⟨1840⟩ ::
        UInt256.ofNat p.owner.toNat :: UInt256.ofNat p.spender.toNat :: p.value ::
        UInt256.ofNat p.owner.toNat :: R)
      (permitDigestMemory p evm v mem free) aw' rdata (consumeNonceState evm p.owner).accountMap
      k' C' := by
  obtain ⟨aw1, k1, C1, r1⟩ := permitConsumeNonce v free (by omega) hperm
    (by change free + 160 < 2 ^ 256; omega) hmem hfree hs rd
  obtain ⟨aw2, k2, C2, r2⟩ := permitStructHashRoutine v free
    (by simp only [List.length_cons]; omega) hlo (by omega) r1
  obtain ⟨aw3, k3, C3, r3⟩ := typedDataDomainRoutine v (free + 224)
    (by simpa only [List.length_cons] using hstack) (by omega) (by omega)
    (permitHashMemory_free _ _ _ _ _ _ _) r2
  exact ⟨aw3, k3, C3, by
    simpa only [permitDigestMemory, PermitData.digest, PermitData.structHash, hs.env] using r3⟩

end Benchmarks.Morpho.MetaMorphoV1_1
