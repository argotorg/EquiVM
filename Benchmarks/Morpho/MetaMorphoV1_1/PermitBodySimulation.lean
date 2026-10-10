import Benchmarks.Morpho.MetaMorphoV1_1.PermitDigestRuntime
import Benchmarks.Morpho.MetaMorphoV1_1.PermitApprovalRuntime
import Benchmarks.Morpho.MetaMorphoV1_1.PermitTailSource
import Benchmarks.Morpho.MetaMorphoV1_1.ECDSASimulation

/-! Permit simulation from nonce consumption through signature checks and approval. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option maxRecDepth 2000

theorem permitBodySimulation {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {R : List UInt256} (p : PermitData) (v : MetaMorphoV1_1Immutables) (free : Nat)
    (hstack : R.length + 17 ≤ 1024) (hperm : I.perm = true)
    (hlo : 96 ≤ free) (hfit : free + 416 < 2 ^ 64) (hmem : 96 ≤ mem.size)
    (hfree : memLoad (UInt256.ofNat 64) mem = UInt256.ofNat free)
    (hv : p.sigV.toNat < 256)
    (hr : uInt256OfByteArray (I.calldata.readBytes 164 32) = p.sigR)
    (hss : uInt256OfByteArray (I.calldata.readBytes 196 32) = p.sigS)
    (hs : SourceState s0 I σ evm)
    (rd : RD (deployedRuntime v) I g s0 ⟨1648⟩
      (p.sigV :: UInt256.ofNat p.owner.toNat :: UInt256.ofNat p.spender.toNat :: p.value ::
        p.deadline :: R) mem aw rdata σ k C) :
    (ExecBlock config (p.entryFrame evm v) evm (permitTransition.body.drop 4) .reverted ∧
      RDrev (deployedRuntime v) g s0) ∨
    ∃ state frame,
      ExecBlock config (p.entryFrame evm v) evm (permitTransition.body.drop 4) (.ok frame state) ∧
      RDret (deployedRuntime v) g s0 state.accountMap ByteArray.empty := by
  obtain ⟨aw1, k1, C1, r1⟩ := permitDigestRoutine p v free hstack hperm hlo hfit hmem hfree hs rd
  rw [hr, hss] at r1
  have hs1 : SourceState s0 I (consumeNonceState evm p.owner).accountMap
      (consumeNonceState evm p.owner) :=
    ⟨(consumeNonceSourceState hs p.owner).world, (consumeNonceSourceState hs p.owner).env, rfl⟩
  have hb := domainSeparatorCursor_bounds v evm.executionEnv (free + 224)
  rcases ecdsaRecoverSimulation v (domainSeparatorCursor v evm.executionEnv (free + 224))
      (by simp only [List.length_cons]; omega) (by omega)
      (by change domainSeparatorCursor v evm.executionEnv (free + 224) + 128 < 2 ^ 256; omega)
      hv (permitDigestMemory_free p evm v mem free)
      (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) hs1 r1 with
    ⟨hsource, hrev⟩ | ⟨state, out, recoverFrame, aw2, k2, C2, hs2, hnonzero, hsource, r2⟩
  · exact .inl ⟨permitHashPrefix p evm v (permitRecoverReverts hsource), hrev⟩
  · by_cases hsign : ecrecoverSigner out = p.owner
    · rw [hsign] at hsource r2 hnonzero
      obtain ⟨k3, C3, r3⟩ := permitSignerMatch v (by omega) r2
      by_cases hspender : p.spender ≠ AccountAddress.ofNat 0
      · obtain ⟨frame, htail⟩ := permitApprovalReturns (evm := evm) (state := state)
          (v := v) hnonzero hspender
        exact .inr ⟨approvalState state p.owner p.spender p.value, frame,
          permitHashPrefix p evm v (permitRecoverPrefix hsource htail),
          permitApprovalReturn v (by omega) hperm hnonzero hspender hs2 r3⟩
      · have hbad : ¬ (p.owner ≠ AccountAddress.ofNat 0 ∧ p.spender ≠ AccountAddress.ofNat 0) :=
          fun h ↦ hspender h.2
        exact .inl ⟨permitHashPrefix p evm v
          (permitRecoverPrefix hsource (permitApprovalReverts hbad)),
          approvalRevertAddress v (by omega) hbad r3⟩
    · exact .inl ⟨permitHashPrefix p evm v
        (permitRecoverPrefix hsource (permitSignerReverts hsign)),
        permitSignerMismatch v (by omega) hsign r2⟩

end Benchmarks.Morpho.MetaMorphoV1_1
