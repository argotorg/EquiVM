import Solm.Benchmarks.Auction.BidSource
import Solm.Benchmarks.Auction.CreateStorage

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

def bidAmountState (evm : EVM.State) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨208⟩ evm.executionEnv.weiValue

def bidWinnerState (evm : EVM.State) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨211⟩
    (setAddressOffset0Word (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨211⟩)
      (solcSourceWord evm.executionEnv))

def bidStoredState (evm : EVM.State) : EVM.State := bidWinnerState (bidAmountState evm)

def bidStoredAccounts (σ : AccountMap) (I : ExecutionEnv) : AccountMap :=
  let σ1 := sstoreAccountMap I.codeOwner σ ⟨208⟩ I.weiValue
  sstoreAccountMap I.codeOwner σ1 ⟨211⟩
    (setAddressOffset0Word (storedWord σ1 I ⟨211⟩) (solcSourceWord I))

theorem SourceState.bidStores {s0 I cA σ evm} (hs : SourceState s0 I cA σ evm) :
    SourceState s0 I cA (bidStoredAccounts σ I) (bidStoredState evm) := by
  have hs1 : SourceState s0 I cA (sstoreAccountMap I.codeOwner σ ⟨208⟩ I.weiValue)
      (bidAmountState evm) := by
    simpa only [bidAmountState, hs.env] using hs.storageWrite ⟨208⟩ I.weiValue
  have hs2 := hs1.readModifyWrite ⟨211⟩ (fun old ↦ setAddressOffset0Word old (solcSourceWord I))
  simpa only [bidStoredAccounts, bidStoredState, bidWinnerState, hs1.env] using hs2

def bidStoreStmts : List Stmt :=
  [.assign .storage (aField "amount") (.env .callvalue),
    .assign .storage (aField "bidder") sender]

theorem bidStoresSource {evm locals} (ha : locals.get? "auction" = none) :
    ExecBlock auctionConfig { contract := auctionContract, locals := locals } evm bidStoreStmts
      (.ok { contract := auctionContract, locals := locals } (bidStoredState evm)) := by
  apply ExecBlock.consNormal (ExecStmt.assign (value := .int (Int.ofNat
    evm.executionEnv.weiValue.toNat))
    (by simp only [evalExpr?, envValue, pure]; rfl)
    (auctionFieldWrite evm _ locals "amount" (.elem (.int uint256Int)) (auctionUint256Loc ⟨208⟩)
      _ ha (by native_decide) rfl (by trivial)
      (storageLocStore_uint256 evm ⟨208⟩ evm.executionEnv.weiValue)))
  change ExecBlock _ _ (bidAmountState evm) _ _
  apply ExecBlock.consNormal (ExecStmt.assign
    (value := .address (bidAmountState evm).executionEnv.source)
    (by simp only [sender, evalExpr?, envValue, pure])
    (auctionFieldWrite _ _ locals "bidder" (.elem .address) (auctionAddrLoc ⟨211⟩)
      _ ha (by native_decide) rfl (by trivial) (by
        have hw := storageLocStore_address_offset0 (bidAmountState evm) ⟨211⟩
          (solcSourceWord (bidAmountState evm).executionEnv)
          (solcSourceWord_canonical (bidAmountState evm).executionEnv)
        rwa [solcSource_ofNat] at hw)))
  exact ExecBlock.nil

theorem bidStoresRuntime {I g s0 bidder snap noun ret R mem aw rdata cA σ k C}
    (h : RD auctionBytecode I g s0 ⟨1715⟩ (bidder :: snap :: noun :: ret :: R)
      mem aw rdata (cA, σ) k C)
    (hperm : I.perm = true) (hov : R.length + 9 ≤ 1024) :
    ∃ k' C', RD auctionBytecode I g s0 ⟨1738⟩ (bidder :: snap :: noun :: ret :: R)
      mem aw rdata (cA, bidStoredAccounts σ I) k' C' := by
  have rd1719 := evm_run h with [jumpdest, callvalue, push1 ⟨208⟩]
  obtain ⟨_, _, rd1720⟩ := rd1719.sstore hperm (by native_decide) (by evm_ov)
  have rd1723 := evm_run rd1720 with [push1 ⟨211⟩, dup1]
  obtain ⟨_, _, rd1724⟩ := rd1723.sload (by native_decide) (by evm_ov)
  have rd1737 := evm_run rd1724 with [push1 ⟨1⟩, push1 ⟨1⟩, push1 ⟨160⟩, shl, sub,
    not, and, caller, or, swap1]
  have hmask : UInt256.sub (UInt256.shiftLeft ⟨1⟩ ⟨160⟩) ⟨1⟩ = solcAddrMask := by decide
  rw [hmask, u256_land_comm (UInt256.lnot solcAddrMask), u256_lor_comm] at rd1737
  rw [bidStoredAccounts, setAddressOffset0Word, solcAddrMask_clean (solcSourceWord_canonical I)]
  exact rd1737.sstore hperm (by native_decide) (by evm_ov)

theorem bidExit {I g s0 extended bidder snap noun ret R mem aw rdata cA σ k C}
    (h : RD auctionBytecode I g s0 ⟨1923⟩ (extended :: bidder :: snap :: noun :: ret :: R)
      mem aw rdata (cA, σ) k C)
    (hperm : I.perm = true) (hret : (D_J auctionBytecode 0).contains ret = true)
    (hov : R.length + 5 ≤ 1024) :
    ∃ k' C', RD auctionBytecode I g s0 ret R mem aw rdata
      (cA, sstoreAccountMap I.codeOwner σ ⟨101⟩ ⟨1⟩) k' C' := by
  have rd1930 := evm_run h with [jumpdest, pop, pop, push1 ⟨1⟩, push1 ⟨101⟩]
  obtain ⟨_, _, rd1931⟩ := rd1930.sstore hperm (by native_decide) (by evm_ov)
  exact ⟨_, _, evm_run rd1931 with [pop, pop, jump hret]⟩

end Auction
