import Reasoning.StateFacts
import Reasoning.WordArithmetic
import Reasoning.EVMWord
import Benchmarks.Dss.DaiJoin.Dispatch
import Reasoning.ExternalCall

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.DaiJoin

/-! Shared target-address and code-size facts for DaiJoin external calls. -/

abbrev daiJoinVatTargetWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  solcAddressSlotWord ⟨1⟩ σ I

abbrev daiJoinVatAddress (σ : AccountMap) (I : ExecutionEnv) : AccountAddress :=
  AccountAddress.ofNat (daiJoinVatTargetWord σ I).toNat

abbrev daiJoinDaiTargetWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  solcAddressSlotWord ⟨2⟩ σ I

abbrev daiJoinDaiAddress (σ : AccountMap) (I : ExecutionEnv) : AccountAddress :=
  AccountAddress.ofNat (daiJoinDaiTargetWord σ I).toNat


theorem daiJoinVatAddress_eq_target (σ : AccountMap) (I : ExecutionEnv) :
    daiJoinVatAddress σ I = AccountAddress.ofUInt256 (daiJoinVatTargetWord σ I) := by
  exact address_eq_target _

theorem daiJoinDaiAddress_eq_target (σ : AccountMap) (I : ExecutionEnv) :
    daiJoinDaiAddress σ I = AccountAddress.ofUInt256 (daiJoinDaiTargetWord σ I) := by
  exact address_eq_target _


theorem daiJoinVatEvmAddress_eq_target (σ : AccountMap) (I : ExecutionEnv) :
    EVM.address (daiJoinVatAddress σ I) =
      AccountAddress.ofUInt256 (daiJoinVatTargetWord σ I) := by
  rw [address_of_val]
  exact daiJoinVatAddress_eq_target σ I

theorem daiJoinDaiEvmAddress_eq_target (σ : AccountMap) (I : ExecutionEnv) :
    EVM.address (daiJoinDaiAddress σ I) =
      AccountAddress.ofUInt256 (daiJoinDaiTargetWord σ I) := by
  rw [address_of_val]
  exact daiJoinDaiAddress_eq_target σ I


theorem daiJoinVatCode_zero_of_codeSize_zero {evm : EVM.State}
    (hzero :
      Reasoning.Theory.extCodeSizeWord evm.accountMap
        (daiJoinVatTargetWord evm.accountMap evm.executionEnv) = ⟨0⟩) :
    (UInt256.ofNat
      ((evm.lookupAccount (daiJoinVatAddress evm.accountMap evm.executionEnv)).option 0
        (fun acc => acc.code.size))).toNat = 0 := by
  exact code_zero_of_codeSize_zero
    (daiJoinVatAddress_eq_target evm.accountMap evm.executionEnv) hzero

theorem daiJoinVatCode_pos_of_codeSize_ne_zero {evm : EVM.State}
    (hne :
      Reasoning.Theory.extCodeSizeWord evm.accountMap
        (daiJoinVatTargetWord evm.accountMap evm.executionEnv) ≠ ⟨0⟩) :
    0 <
      (UInt256.ofNat
        ((evm.lookupAccount (daiJoinVatAddress evm.accountMap evm.executionEnv)).option 0
          (fun acc => acc.code.size))).toNat := by
  exact code_pos_of_codeSize_ne_zero
    (daiJoinVatAddress_eq_target evm.accountMap evm.executionEnv) hne

theorem daiJoinDaiCode_zero_of_codeSize_zero {evm : EVM.State}
    (hzero :
      Reasoning.Theory.extCodeSizeWord evm.accountMap
        (daiJoinDaiTargetWord evm.accountMap evm.executionEnv) = ⟨0⟩) :
    (UInt256.ofNat
      ((evm.lookupAccount (daiJoinDaiAddress evm.accountMap evm.executionEnv)).option 0
        (fun acc => acc.code.size))).toNat = 0 := by
  exact code_zero_of_codeSize_zero
    (daiJoinDaiAddress_eq_target evm.accountMap evm.executionEnv) hzero

theorem daiJoinDaiCode_pos_of_codeSize_ne_zero {evm : EVM.State}
    (hne :
      Reasoning.Theory.extCodeSizeWord evm.accountMap
        (daiJoinDaiTargetWord evm.accountMap evm.executionEnv) ≠ ⟨0⟩) :
    0 <
      (UInt256.ofNat
        ((evm.lookupAccount (daiJoinDaiAddress evm.accountMap evm.executionEnv)).option 0
          (fun acc => acc.code.size))).toNat := by
  exact code_pos_of_codeSize_ne_zero
    (daiJoinDaiAddress_eq_target evm.accountMap evm.executionEnv) hne


end Benchmarks.Dss.DaiJoin
