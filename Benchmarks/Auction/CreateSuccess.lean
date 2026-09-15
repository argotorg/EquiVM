import Benchmarks.Auction.CreateSource
import Benchmarks.Auction.CreateSnapshot
import Benchmarks.Auction.CreateEvent
import Benchmarks.Auction.CheckedAdd

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

theorem createAdditionPrefix {I g s0 noun ret R mem aw rdata cA σ k C}
    (h : RD auctionBytecode I g s0 ⟨3172⟩ (noun :: ret :: R) mem aw rdata (cA, σ) k C)
    (hov : R.length + 8 ≤ 1024) :
    ∃ k' C', RD auctionBytecode I g s0 ⟨5704⟩
      (UInt256.ofNat I.header.timestamp :: storedWord σ I ⟨206⟩ :: ⟨3189⟩ ::
        ⟨0⟩ :: UInt256.ofNat I.header.timestamp :: noun :: ret :: R)
      mem aw rdata (cA, σ) k' C' := by
  have rd3175 := evm_run h with [jumpdest, push1 ⟨206⟩]
  obtain ⟨_, _, rd3176⟩ := rd3175.sload (by native_decide) (by evm_ov)
  exact ⟨_, _, evm_run rd3176 with [timestamp, swap1, push0, swap1, push2 ⟨3189⟩,
    swap1, dup4, push2 ⟨5704⟩, jump (by jump_dest)]⟩

theorem createSuccessRoutine {I g s0 noun ret R mem aw ptr rdata cA σ k C evm locals}
    (h : RD auctionBytecode I g s0 ⟨3172⟩ (noun :: ret :: R) mem aw rdata (cA, σ) k C)
    (hs : SourceState s0 I cA σ evm) (hperm : I.perm = true)
    (hm : MemoryCursor mem aw ptr) (hb : ptr.toNat + 256 ≤ 2 ^ 200)
    (ha : locals.get? "auction" = none) (hd : locals.get? "duration" = none)
    (hn : locals.get? "nounId" = some (.int (Int.ofNat noun.toNat)))
    (hret : (D_J auctionBytecode 0).contains ret = true) (hov : R.length + 14 ≤ 1024) :
    (∃ evm' σ' locals' mem' aw' k' C',
      ExecBlock auctionConfig { contract := auctionContract, locals := locals } evm
        createSuccessStmts (.ok { contract := auctionContract, locals := locals' } evm') ∧
      SourceState s0 I cA σ' evm' ∧
      RD auctionBytecode I g s0 ret R mem' aw' rdata (cA, σ') k' C') ∨
    (ExecBlock auctionConfig { contract := auctionContract, locals := locals } evm
      createSuccessStmts .reverted ∧ RDrev auctionBytecode g s0) := by
  obtain ⟨_, _, rd5704⟩ := createAdditionPrefix h (by omega)
  by_cases hno : (UInt256.ofNat I.header.timestamp).toNat +
      (storedWord σ I ⟨206⟩).toNat < UInt256.size
  · have hb192 : ptr.toNat + 192 ≤ 2 ^ 200 := by omega
    obtain ⟨_, _, rd3189⟩ := checkedAddOk rd5704 hno (by jump_dest) (by evm_ov)
    rw [u256_add_comm (storedWord σ I ⟨206⟩)] at rd3189
    obtain ⟨_, _, rd3240⟩ := createSnapshotPrefix rd3189 hm hb192 hov
    obtain ⟨_, _, rd3274⟩ := createStorePrefix rd3240 hperm (by omega)
    have hh := (createdSnapshot noun (UInt256.ofNat I.header.timestamp)
      (UInt256.ofNat I.header.timestamp + storedWord σ I ⟨206⟩)).mem_cursorHeap hm hb192
    have hp : (ptr + ⟨192⟩).toNat = ptr.toNat + 192 :=
      addWord_toNat ptr ⟨192⟩ (by change ptr.toNat + 192 < 2 ^ 256; omega)
    obtain ⟨_, _, rdret⟩ := createEvent rd3274 hh.cursor (by omega) hperm hret (by omega)
    exact Or.inl ⟨_, _, _, _, _, _, _, createSuccessSource hs ha hd hn hno,
      hs.createdAuction _ _ _, rdret⟩
  · exact Or.inr ⟨createSuccessSourceOverflow hs hd (by omega),
      checkedAddOverflow rd5704 (by omega) (by evm_ov)⟩

end Auction
