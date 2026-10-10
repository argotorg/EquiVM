import Benchmarks.CompoundIII.Comet.RepayAmountsModel
import Benchmarks.CompoundIII.Comet.WithdrawAmountsWords

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

attribute [local irreducible] signed104

theorem supplyAmount_lt (old next : UInt256) :
    (supplyAmount old next).toNat < 2^104 := by
  unfold supplyAmount
  split_ifs
  · decide
  · decide
  · exact principalDecrease_lt _ _
  · exact lt_trans (positivePrincipal_lt _) (by decide)

theorem repayAmount_lt {old next : UInt256} (hf : RepayAmountsFits old next) :
    (repayAmount old next).toNat < 2^104 := by
  unfold repayAmount
  split_ifs with hi hn ho
  · decide
  · exact principalDecrease_lt _ _
  · decide
  · have hm : -(2^103 : Int) < signed104 old := by
      simpa only [RepayAmountsFits, if_neg hi, if_neg hn, if_neg ho] using hf
    exact lt_trans (negativePrincipal_lt hm) (by decide)

end Benchmarks.CompoundIII.Comet
