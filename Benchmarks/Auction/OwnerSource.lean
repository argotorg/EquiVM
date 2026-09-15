import Benchmarks.Auction.OwnerGuard

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

-- LIBRARY CANDIDATE: equality between a canonical address word and CALLER.
theorem sourceAddress_eq_iff (I : ExecutionEnv) (w : UInt256)
    (hc : w.toNat < EVM.addressModulus) :
    I.source = AccountAddress.ofNat w.toNat ↔ solcSourceWord I = w := by
  constructor
  · intro h
    have hw := congrArg (fun a => valueToWord (.address a)) h
    dsimp only at hw
    rw [valueToWord_address_ofNat_canonical w hc] at hw
    exact Option.some.inj hw
  · intro h
    rw [← h, solcSource_ofNat]

theorem ownerWord_canonical (σ : AccountMap) (I : ExecutionEnv) :
    (ownerWord σ I).toNat < EVM.addressModulus := by
  rw [ownerWord, u256_land_comm]
  exact solcAddrMask_result_canonical _

theorem ownerWord_equiv {σ₁ σ₂ : AccountMap} (h : accountMapEquiv σ₁ σ₂)
    (I : ExecutionEnv) : ownerWord σ₁ I = ownerWord σ₂ I := by
  rw [ownerWord, ownerWord, storedWord_equiv h]

theorem ownerRead (evm : EVM.State) (locals : Store)
    (hbase : locals.get? "_owner" = none) :
    evalExpr? auctionConfig { contract := auctionContract, locals := locals } evm
      (.storage ownerRef) = .ok (.address
        (AccountAddress.ofNat (ownerWord evm.accountMap evm.executionEnv).toNat)) := by
  rw [ownerRef, scalarRead evm locals "_owner" .address (auctionAddrLoc ⟨151⟩)
    hbase (by native_decide) rfl, loadAddress]
  congr 3
  exact congrArg UInt256.toNat (u256_land_comm _ _)

theorem evalOwnerEq_true (evm : EVM.State) (locals : Store)
    (hbase : locals.get? "_owner" = none)
    (ho : solcSourceWord evm.executionEnv = ownerWord evm.accountMap evm.executionEnv) :
    evalExpr? auctionConfig { contract := auctionContract, locals := locals } evm
      (.binary .eq sender (.storage ownerRef)) = .ok (.bool true) := by
  have ha := (sourceAddress_eq_iff evm.executionEnv _
    (ownerWord_canonical evm.accountMap evm.executionEnv)).mpr ho
  have hv : (Value.address evm.executionEnv.source == Value.address
      (AccountAddress.ofNat (ownerWord evm.accountMap evm.executionEnv).toNat)) = true := by
    rw [ha]
    exact beq_self_eq_true _
  simp only [sender, evalExpr?, ownerRead evm locals hbase, EvalResult.bind,
    bind, pure, envValue, evalBinaryOp?, hv]

theorem evalOwnerEq_false (evm : EVM.State) (locals : Store)
    (hbase : locals.get? "_owner" = none)
    (ho : solcSourceWord evm.executionEnv ≠ ownerWord evm.accountMap evm.executionEnv) :
    evalExpr? auctionConfig { contract := auctionContract, locals := locals } evm
      (.binary .eq sender (.storage ownerRef)) = .ok (.bool false) := by
  have ha : evm.executionEnv.source ≠
      AccountAddress.ofNat (ownerWord evm.accountMap evm.executionEnv).toNat := by
    exact fun h => ho ((sourceAddress_eq_iff evm.executionEnv _
      (ownerWord_canonical evm.accountMap evm.executionEnv)).mp h)
  have hv : (Value.address evm.executionEnv.source == Value.address
      (AccountAddress.ofNat (ownerWord evm.accountMap evm.executionEnv).toNat)) = false := by
    rw [beq_eq_false_iff_ne]
    exact fun h => ha (Value.address.inj h)
  simp only [sender, evalExpr?, ownerRead evm locals hbase, EvalResult.bind,
    bind, pure, envValue, evalBinaryOp?, hv]

end Auction
