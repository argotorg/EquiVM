import Benchmarks.Scaffolds.CometRewards.Bytecode
import Solm.Semantics

open Solm Ethereum Ethereum.EVM

namespace Benchmarks.CompoundIII.CometRewards

/-!
# CometRewards trusted selector facts

The selector facts are trusted because `ffi.KEC` is opaque to Lean.  They are the standard
ABI-selector facts allowed by the benchmark prompt and match the solc AST `functionSelector`
metadata for the checked-in bytecode artifact.
-/

/-- `keccak("withdrawToken(address,address,uint256)")[0:4] = 0x01e33667`. -/
axiom withdrawTokenSelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr withdrawTokenTransition))).extract 0 4 =
      ⟨#[0x01, 0xe3, 0x36, 0x67]⟩

/-- `keccak("governor()")[0:4] = 0x0c340a24`. -/
axiom governorSelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr governorTransition))).extract 0 4 =
      ⟨#[0x0c, 0x34, 0x0a, 0x24]⟩

/-- `keccak("rewardConfig(address)")[0:4] = 0x2289b6b8`. -/
axiom rewardConfigSelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr rewardConfigTransition))).extract 0 4 =
      ⟨#[0x22, 0x89, 0xb6, 0xb8]⟩

/-- `keccak("getRewardOwed(address,address)")[0:4] = 0x41e0cad6`. -/
axiom getRewardOwedSelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr getRewardOwedTransition))).extract 0 4 =
      ⟨#[0x41, 0xe0, 0xca, 0xd6]⟩

/-- `keccak("claimTo(address,address,address,bool)")[0:4] = 0x4ff85d94`. -/
axiom claimToSelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr claimToTransition))).extract 0 4 =
      ⟨#[0x4f, 0xf8, 0x5d, 0x94]⟩

/-- `keccak("setRewardsClaimed(address,address[],uint256[])")[0:4] = 0x6394f161`. -/
axiom setRewardsClaimedSelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr setRewardsClaimedTransition))).extract 0 4 =
      ⟨#[0x63, 0x94, 0xf1, 0x61]⟩

/-- `keccak("rewardsClaimed(address,address)")[0:4] = 0x65e12392`. -/
axiom rewardsClaimedSelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr rewardsClaimedTransition))).extract 0 4 =
      ⟨#[0x65, 0xe1, 0x23, 0x92]⟩

/-- `keccak("setRewardConfig(address,address)")[0:4] = 0x95e36d2c`. -/
axiom setRewardConfigSelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr setRewardConfigTransition))).extract 0 4 =
      ⟨#[0x95, 0xe3, 0x6d, 0x2c]⟩

/-- `keccak("claim(address,address,bool)")[0:4] = 0xb7034f7e`. -/
axiom claimSelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr claimTransition))).extract 0 4 =
      ⟨#[0xb7, 0x03, 0x4f, 0x7e]⟩

/-- `keccak("transferGovernor(address)")[0:4] = 0xb8cc9ce6`. -/
axiom transferGovernorSelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr transferGovernorTransition))).extract 0 4 =
      ⟨#[0xb8, 0xcc, 0x9c, 0xe6]⟩

/-- `keccak("setRewardConfigWithMultiplier(address,address,uint256)")[0:4] = 0xcdc0ca09`. -/
axiom setRewardConfigWithMultiplierSelectorBytes :
    (ffi.KEC
        (String.toByteArray
          (Solm.transitionSigStr setRewardConfigWithMultiplierTransition))).extract 0 4 =
      ⟨#[0xcd, 0xc0, 0xca, 0x09]⟩

end Benchmarks.CompoundIII.CometRewards
