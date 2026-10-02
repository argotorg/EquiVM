import Examples.VyperERC20.TransferFromStoresBeforeFromStore

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 20000000
set_option linter.unusedSimpArgs false

namespace VyperERC20

theorem erc20X_transferFromAfterFromStore {σ σ₀ A I} {g : Sat256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD vyperERC20Bytecode I g (initState σ σ₀ g A I) ⟨526⟩
      [transferFromFromSlot I,
        transferFromBalanceDebitWord
          (transferFromAfterAllowanceState (initState σ σ₀ g A I) I) I,
        transferFromFromSlot I, transferFromSelectorWord]
      (transferFromAfterFromLoadMemI σ I)
      (UInt256.ofNat 5) ByteArray.empty
      (transferFromAccountMapAfterAllowanceI σ I
        (transferFromAllowanceDebitI σ σ₀ A I g)) k C) :
    ∃ k C, RD vyperERC20Bytecode I g (initState σ σ₀ g A I) ⟨528⟩
      [transferFromSelectorWord]
      (transferFromAfterFromLoadMemI σ I)
      (UInt256.ofNat 5) ByteArray.empty
      (transferFromAccountMapAfterBalanceI σ I
        (transferFromAllowanceDebitI σ σ₀ A I g)
        (transferFromBalanceDebitWord
          (transferFromAfterAllowanceState (initState σ σ₀ g A I) I) I)) k C := by
  obtain ⟨k, C, rd526⟩ := hreach
  obtain ⟨k1, C1, rdAfterStore⟩ := rd526.sstore hperm
    (by vyper_erc20_transferFrom_decode) (by evm_ov)
  exact ⟨_, _, evm_run rdAfterStore with [pop]⟩


end VyperERC20
