import Benchmarks.CompoundIII.Comet.PrincipalValueModel
import Benchmarks.CompoundIII.Comet.Signed104Encoding

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

theorem principalValueWord_encode (evm : EVM.State) (present : UInt256) :
    EVM.wordOfInt (principalValueInt evm present) = principalValueWord evm present := by
  unfold principalValueInt principalValueWord
  split_ifs
  · exact wordOfInt_ofNat_toNat _
  · exact wordOfInt_neg_natCast_eq_sub_zero _

theorem principalValueWord_signed104 {evm : EVM.State} {present : UInt256}
    (hf : PrincipalValueFits evm present) :
    signed104 (principalValueWord evm present) = principalValueInt evm present := by
  by_cases hp : 0 ≤ signedWord present
  · have hn : ¬ signedWord present < 0 := by omega
    have hq : (principalValueMagnitude evm present false).toNat < 2^103 := by
      simpa only [decide_eq_false hn] using hf.2.2
    simp only [principalValueWord, principalValueInt, if_pos hp]
    exact signed104_low hq
  · have hn : signedWord present < 0 := by omega
    have hq : (principalValueMagnitude evm present true).toNat < 2^103 := by
      simpa only [decide_eq_true hn] using hf.2.2
    simp only [principalValueWord, principalValueInt, if_neg hp]
    exact signed104_zeroSub (le_of_lt hq)

theorem principalValueWord_clean {evm : EVM.State} {present : UInt256}
    (hf : PrincipalValueFits evm present) :
    UInt256.signextend (UInt256.ofNat 12) (principalValueWord evm present) =
      principalValueWord evm present := by
  change UInt256.signextend ⟨12⟩ _ = _
  rw [← signed104_word, principalValueWord_signed104 hf, principalValueWord_encode]

end Benchmarks.CompoundIII.Comet
