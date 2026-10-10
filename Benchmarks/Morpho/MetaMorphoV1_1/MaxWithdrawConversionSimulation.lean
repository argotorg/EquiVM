import Benchmarks.Morpho.MetaMorphoV1_1.MaxWithdrawState
import Benchmarks.Morpho.MetaMorphoV1_1.MaxWithdrawBalance
import Benchmarks.Morpho.MetaMorphoV1_1.ConvertAssetsRoutines

/-! Simulation of the withdrawal limit between accrued fees and the liquidity loop. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false
set_option maxRecDepth 2000

theorem maxWithdrawConversionSimulation {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {frame : Frame} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {owner : AccountAddress} {lost total shares ptr : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 20 ≤ 1024)
    (hl : MaxWithdrawAccruedLocals v frame owner total shares (codeOwnerStorageWord I σ ⟨2⟩) ptr)
    (hs : SourceState s0 I σ evm)
    (rd : RD (deployedRuntime v) I g s0 ⟨15894⟩
      ([lost, total, shares, UInt256.ofNat owner.toNat, ⟨15935⟩] ++ R) mem aw rdata σ k C) :
    (ExecBlock config frame evm (allocatedMaxWithdrawFunction.body.drop 10) .reverted ∧
      RDrev (deployedRuntime v) g s0) ∨
    ∃ (locals' : Store) (assets : UInt256),
      MaxWithdrawResultLocals ⟨contract, locals', immStore v⟩ assets
        (codeOwnerStorageWord I σ ⟨2⟩ + shares) total ptr ∧
      (∀ outcome, ExecBlock config ⟨contract, locals', immStore v⟩ evm
          (allocatedMaxWithdrawFunction.body.drop 14) outcome →
        ExecBlock config frame evm (allocatedMaxWithdrawFunction.body.drop 10) outcome) ∧
      ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨15935⟩
        ([assets, codeOwnerStorageWord I σ ⟨2⟩ + shares, total] ++ R)
        (twoWordHashMem (UInt256.ofNat owner.toNat) ⟨0⟩ mem) aw' rdata σ k' C' := by
  rcases frame with ⟨cc, locals, imms⟩
  have hc := hl.contract
  have himms := hl.imms
  dsimp only at hc himms
  subst cc imms
  obtain ⟨aw1, k1, C1, h1⟩ := metaMorphoV1_1_block_15894_packed
    (immWords := wordsOf (immStore v)) (by simp only [List.append]; omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  by_cases hadd : (codeOwnerStorageWord I σ ⟨2⟩).toNat + shares.toNat < UInt256.size
  · obtain ⟨k2, C2, h2⟩ := checkedAddReturn v
      (by simp only [List.append, List.length_cons]; omega) hadd
      (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) h1
    obtain ⟨aw3, k3, C3, h3⟩ := maxWithdrawReadBalance v owner
      (by simp only [List.append, List.length_cons]; omega) h2
    have hbalance : balanceInternalWord evm owner =
        codeOwnerStorageWord I σ (solcMappingSlot ⟨0⟩ (UInt256.ofNat owner.toNat)) :=
      hs.storageRead _
    have hp := maxWithdrawBalanceSource (imms := immStore v) (evm := evm)
      hl.owner hl.supply hl.feeShares hl.newSupply hadd
    rw [hbalance] at hp
    have hlb := hl.balance (balance :=
      codeOwnerStorageWord I σ (solcMappingSlot ⟨0⟩ (UInt256.ofNat owner.toNat)))
    have hb : (maxWithdrawBalanceFrame ⟨contract, locals, immStore v⟩
        (codeOwnerStorageWord I σ ⟨2⟩ + shares)
        (codeOwnerStorageWord I σ (solcMappingSlot ⟨0⟩ (UInt256.ofNat owner.toNat)))).locals.get?
        "__c2" = some (uint256Value
          (codeOwnerStorageWord I σ (solcMappingSlot ⟨0⟩ (UInt256.ofNat owner.toNat)))) :=
      store_get_self _ _ _
    by_cases hfit : convertAssetsFits v.DECIMALS_OFFSET
        (codeOwnerStorageWord I σ (solcMappingSlot ⟨0⟩ (UInt256.ofNat owner.toNat)))
        (codeOwnerStorageWord I σ ⟨2⟩ + shares) total
    · obtain ⟨aw4, k4, C4, h4⟩ := convertAssetsReturn v
        (by simp only [List.append, List.length_cons]; omega) hfit
        (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) h3
      have hconvert := maxWithdrawConvertSource v (evm := evm)
        hlb.supply hlb.total hb hlb.assets hfit
      exact .inr ⟨_, _, hlb.converted _, (fun _ h ↦ hp.run (hconvert.run h)),
        aw4, k4, C4, h4⟩
    · exact .inl ⟨hp.run (maxWithdrawConvertReverts v hlb.supply hlb.total hb hfit),
        convertAssetsRevert v (by simp only [List.append, List.length_cons]; omega) hfit h3⟩
  · exact .inl ⟨maxWithdrawSupplyReverts hl.supply hl.feeShares (Nat.le_of_not_gt hadd),
      checkedAddRevert v (by simp only [List.append, List.length_cons]; omega)
        (Nat.le_of_not_gt hadd) h1⟩

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
