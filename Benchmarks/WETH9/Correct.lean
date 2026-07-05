import Benchmarks.WETH9.Constructor
import Benchmarks.WETH9.Name
import Benchmarks.WETH9.Approve
import Benchmarks.WETH9.TotalSupply
import Benchmarks.WETH9.TransferFrom
import Benchmarks.WETH9.Withdraw
import Benchmarks.WETH9.Decimals
import Benchmarks.WETH9.BalanceOf
import Benchmarks.WETH9.Symbol
import Benchmarks.WETH9.Transfer
import Benchmarks.WETH9.Deposit
import Benchmarks.WETH9.Allowance

/-!
# WETH9 benchmark correctness

The top-level runtime theorem performs WETH9's binary-search dispatch: for calldata ≥ 4 it splits on
each ABI selector, routing to that function's `…BodyCore`; the payable `deposit` selector and every
non-matching selector (and calldata < 4) fall through to the payable fallback (`deposit` body).
There is no shared callvalue guard — each non-payable function guards its own callvalue.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace Benchmarks.WETH9

theorem weth9Correct :
    runtimeEquivalence!?! config weth9Bytecode contract := by
  refine ⟨fun cA gh bl σ_evm σ_solm σ₀ g A I hcode hsize hperm hAccounts => ?_⟩
  by_cases hsz : 4 ≤ I.calldata.size
  · by_cases h0 : selIs I (weth9SelBytes 0)
    · exact weth9NameBodyCore hcode hsize hperm h0 hAccounts
    · by_cases h1 : selIs I (weth9SelBytes 1)
      · exact weth9ApproveBodyCore hcode hsize hperm h1 hAccounts
      · by_cases h2 : selIs I (weth9SelBytes 2)
        · exact weth9TotalSupplyBodyCore hcode hsize hperm h2 hAccounts
        · by_cases h3 : selIs I (weth9SelBytes 3)
          · exact weth9TransferFromBodyCore hcode hsize hperm h3 hAccounts
          · by_cases h4 : selIs I (weth9SelBytes 4)
            · exact weth9WithdrawBodyCore hcode hsize hperm h4 hAccounts
            · by_cases h5 : selIs I (weth9SelBytes 5)
              · exact weth9DecimalsBodyCore hcode hsize hperm h5 hAccounts
              · by_cases h6 : selIs I (weth9SelBytes 6)
                · exact weth9BalanceOfBodyCore hcode hsize hperm h6 hAccounts
                · by_cases h7 : selIs I (weth9SelBytes 7)
                  · exact weth9SymbolBodyCore hcode hsize hperm h7 hAccounts
                  · by_cases h8 : selIs I (weth9SelBytes 8)
                    · exact weth9TransferBodyCore hcode hsize hperm h8 hAccounts
                    · by_cases h9 : selIs I (weth9SelBytes 9)
                      · exact weth9DepositBodyCore hcode hsize hperm h9 hAccounts
                      · by_cases h10 : selIs I (weth9SelBytes 10)
                        · exact weth9AllowanceBodyCore hcode hsize hperm h10 hAccounts
                        · refine weth9FallbackBodyCore hcode hsize hperm hsz ?_ hAccounts
                          intro i hi
                          interval_cases i
                          · simpa [selIs] using h0
                          · simpa [selIs] using h1
                          · simpa [selIs] using h2
                          · simpa [selIs] using h3
                          · simpa [selIs] using h4
                          · simpa [selIs] using h5
                          · simpa [selIs] using h6
                          · simpa [selIs] using h7
                          · simpa [selIs] using h8
                          · simpa [selIs] using h9
                          · simpa [selIs] using h10
  · exact weth9ShortFallbackBodyCore hcode hsize hperm (by omega) hAccounts

theorem weth9ContractCorrect :
    contractEquivalence config weth9CreationBytecode weth9Bytecode contract :=
  contractEquivalence.intro weth9ConstructorCorrect weth9Correct

end Benchmarks.WETH9
