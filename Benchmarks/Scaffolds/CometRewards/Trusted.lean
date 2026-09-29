import Benchmarks.Scaffolds.CometRewards.Bytecode
import Solm.Semantics

open Solm ABI Ethereum Ethereum.EVM

namespace Benchmarks.CompoundIII.CometRewards

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-!
# CometRewards selector proofs

These ABI selector proofs match the solc AST `functionSelector` metadata for the checked-in
bytecode artifact.
-/

/-- `keccak("withdrawToken(address,address,uint256)")[0:4] = 0x01e33667`. -/
theorem withdrawTokenSelectorBytes :
    (KEC (String.toByteArray (Solm.transitionSigStr withdrawTokenTransition))).extract 0 4 =
      ⟨#[0x01, 0xe3, 0x36, 0x67]⟩ := by
  simp [Solm.transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, ABI.intTypeToSigStr, withdrawTokenTransition, addr, uint256, uint256Int]; decide +kernel

/-- `keccak("governor()")[0:4] = 0x0c340a24`. -/
theorem governorSelectorBytes :
    (KEC (String.toByteArray (Solm.transitionSigStr governorTransition))).extract 0 4 =
      ⟨#[0x0c, 0x34, 0x0a, 0x24]⟩ := by decide +kernel

/-- `keccak("rewardConfig(address)")[0:4] = 0x2289b6b8`. -/
theorem rewardConfigSelectorBytes :
    (KEC (String.toByteArray (Solm.transitionSigStr rewardConfigTransition))).extract 0 4 =
      ⟨#[0x22, 0x89, 0xb6, 0xb8]⟩ := by
  simp [Solm.transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, rewardConfigTransition, addr]; decide +kernel

/-- `keccak("getRewardOwed(address,address)")[0:4] = 0x41e0cad6`. -/
theorem getRewardOwedSelectorBytes :
    (KEC (String.toByteArray (Solm.transitionSigStr getRewardOwedTransition))).extract 0 4 =
      ⟨#[0x41, 0xe0, 0xca, 0xd6]⟩ := by
  simp [Solm.transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, getRewardOwedTransition, addr]; decide +kernel

/-- `keccak("claimTo(address,address,address,bool)")[0:4] = 0x4ff85d94`. -/
theorem claimToSelectorBytes :
    (KEC (String.toByteArray (Solm.transitionSigStr claimToTransition))).extract 0 4 =
      ⟨#[0x4f, 0xf8, 0x5d, 0x94]⟩ := by
  simp [Solm.transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, claimToTransition, addr, boolTy]; decide +kernel

/-- `keccak("setRewardsClaimed(address,address[],uint256[])")[0:4] = 0x6394f161`. -/
theorem setRewardsClaimedSelectorBytes :
    (KEC (String.toByteArray (Solm.transitionSigStr setRewardsClaimedTransition))).extract 0 4 =
      ⟨#[0x63, 0x94, 0xf1, 0x61]⟩ := by
  simp [Solm.transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, ABI.intTypeToSigStr, setRewardsClaimedTransition, addr, uint256, uint256Int]; decide +kernel

/-- `keccak("rewardsClaimed(address,address)")[0:4] = 0x65e12392`. -/
theorem rewardsClaimedSelectorBytes :
    (KEC (String.toByteArray (Solm.transitionSigStr rewardsClaimedTransition))).extract 0 4 =
      ⟨#[0x65, 0xe1, 0x23, 0x92]⟩ := by
  simp [Solm.transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, rewardsClaimedTransition, addr]; decide +kernel

/-- `keccak("setRewardConfig(address,address)")[0:4] = 0x95e36d2c`. -/
theorem setRewardConfigSelectorBytes :
    (KEC (String.toByteArray (Solm.transitionSigStr setRewardConfigTransition))).extract 0 4 =
      ⟨#[0x95, 0xe3, 0x6d, 0x2c]⟩ := by
  simp [Solm.transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, setRewardConfigTransition, addr]; decide +kernel

/-- `keccak("claim(address,address,bool)")[0:4] = 0xb7034f7e`. -/
theorem claimSelectorBytes :
    (KEC (String.toByteArray (Solm.transitionSigStr claimTransition))).extract 0 4 =
      ⟨#[0xb7, 0x03, 0x4f, 0x7e]⟩ := by
  simp [Solm.transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, claimTransition, addr, boolTy]; decide +kernel

/-- `keccak("transferGovernor(address)")[0:4] = 0xb8cc9ce6`. -/
theorem transferGovernorSelectorBytes :
    (KEC (String.toByteArray (Solm.transitionSigStr transferGovernorTransition))).extract 0 4 =
      ⟨#[0xb8, 0xcc, 0x9c, 0xe6]⟩ := by
  simp [Solm.transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, transferGovernorTransition, addr]; decide +kernel

/-- `keccak("setRewardConfigWithMultiplier(address,address,uint256)")[0:4] = 0xcdc0ca09`. -/
theorem setRewardConfigWithMultiplierSelectorBytes :
    (KEC
        (String.toByteArray
          (Solm.transitionSigStr setRewardConfigWithMultiplierTransition))).extract 0 4 =
      ⟨#[0xcd, 0xc0, 0xca, 0x09]⟩ := by
  simp [Solm.transitionSigStr, transitionSignature, ABI.printSignature, ABI.abiToSigStr, ABI.elemToSigStr, ABI.intTypeToSigStr, setRewardConfigWithMultiplierTransition, addr, uint256, uint256Int]; decide +kernel

end Benchmarks.CompoundIII.CometRewards
