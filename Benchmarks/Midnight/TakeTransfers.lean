import Benchmarks.Midnight.TakeTransfersSource
import Benchmarks.Midnight.TakeBuyCallback
import Benchmarks.Midnight.MemoryCharge

variable {fork : Ethereum.Fork}

/-! The fee and seller token transfers, retaining memory for the seller callback. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

theorem offerStoredLoanToken {mem : ByteArray} {market arrayPtr callbackPtr offerRoot : UInt256}
    {offer : OfferData}
    (ho : OfferStored mem ⟨832⟩ market arrayPtr callbackPtr offerRoot offer)
    (hoffer : memLoad (UInt256.ofNat 384) mem = ⟨832⟩) :
    memLoad (memLoad (memLoad (UInt256.ofNat 384) mem) mem + UInt256.ofNat 64) mem =
      UInt256.ofNat offer.market.loanToken.val := by
  have hm : memLoad (⟨832⟩ : UInt256) mem = market :=
    ho.words.load_offset ⟨0, by change 0 < 15; decide⟩ rfl
  rw [hoffer, hm]
  exact ho.market.loanToken

theorem midnightTakeTransfers {I : ExecutionEnv} {g : UInt256} {s0 evm : State}
    {frame : Frame} {mem rdata : ByteArray}
    {aw root market arrayPtr callbackPtr offerRoot bought sold ignored sellerCallback : UInt256}
    {offer : OfferData} {payer receiver : AccountAddress} {σ : AccountMap} {k C : Nat}
    {R : List UInt256} (hstack : R.length + 20 ≤ 1024)
    (hc : frame.contract = contract)
    (hfOffer : frame.locals.get? "offer" = some (Model.offerValue offer.value))
    (hfPayer : frame.locals.get? "payer" = some (.address payer))
    (hfReceiver : frame.locals.get? "receiver" = some (.address receiver))
    (hfBought : frame.locals.get? "buyerAssets" = some (.int bought.toNat))
    (hfSold : frame.locals.get? "sellerAssets" = some (.int sold.toNat))
    (hle : sold.toNat ≤ bought.toNat)
    (ho : OfferStored mem ⟨832⟩ market arrayPtr callbackPtr offerRoot offer)
    (hlimit : offerRoot.toNat ≤ root.toNat) (hlo : 832 ≤ root.toNat) (hmem : 608 ≤ mem.size)
    (hoffer : memLoad (UInt256.ofNat 384) mem = ⟨832⟩)
    (hbought : memLoad (UInt256.ofNat 256) mem = bought)
    (hsold : memLoad (UInt256.ofNat 416) mem = sold)
    (hreceiver : memLoad (UInt256.ofNat 128) mem = UInt256.ofNat receiver.val)
    (hh : TransferHeap mem aw root C)
    (hgas : midnightGasBound g) (hfork : fork ≥ .osaka) (hs : SourceState s0 I σ evm)
    (rd : RD fork midnightBytecode I (Sat256.ofUInt256 g) s0 ⟨13252⟩
      ([ignored, sellerCallback, UInt256.ofNat payer.val] ++ R) mem aw rdata σ k C) :
    X fork (g.toNat + 1) (D_J midnightBytecode 0) s0 = .error .OutOfGass ∨
    (ExecBlock fork config frame evm (takeTransition.body.drop 68) .reverted ∧
      RDrev fork midnightBytecode (Sat256.ofUInt256 g) s0) ∨
    ∃ (evm' : State) (σ' : AccountMap) (mem' out : ByteArray) (root' aw' : UInt256) (k' C' : Nat),
      (∀ result, ExecBlock fork config
          (resumeAfterInternalCall (resumeAfterInternalCall frame "__c28" none) "__c29" none)
          evm' (takeTransition.body.drop 70) result →
        ExecBlock fork config frame evm (takeTransition.body.drop 68) result) ∧
      SourceState s0 I σ' evm' ∧ MemoryPrefix mem mem' root.toNat ∧
      root.toNat ≤ root'.toNat ∧ TransferHeap mem' aw' root' C' ∧
      RD fork midnightBytecode I (Sat256.ofUInt256 g) s0 ⟨13329⟩
        (sellerCallback :: solcAddrMask :: R) mem' aw' out σ' k' C' := by
  simp only [List.cons_append, List.nil_append] at rd
  have rd1 := midnightBlocks.midnight_block_13252 (by omega) (by jump_dest) rd
  have ha1 := memoryFundingAt (credit := transferHeapCredit root) rd1 (by memory_fund hh.funding)
  have hloan := offerStoredLoanToken ho hoffer
  have hclean : UInt256.land (UInt256.ofNat offer.market.loanToken.val) solcAddrMask =
      UInt256.ofNat offer.market.loanToken.val := addressWord_val_clean _
  simp only [midnightBlocks.midnight_block_13252_stack, hbought, hsold, hloan,
    addressMask_computed, hclean] at rd1
  obtain ⟨k2, C2, hc2, rd2⟩ := midnightCheckedSub_mono
    (by simp only [List.length_cons]; omega) hle (by jump_dest) rd1
  have rd3 := midnightBlocks.midnight_block_13295
    (by simp only [List.length_cons]; omega) (by jump_dest) rd2
  have ha3 := memoryFundingAt (credit := transferHeapCredit root) rd3 (ha1.mono (by omega))
  have hh3 : TransferHeap mem _ root _ := { hh with
    covered := hh.covered.trans (Nat.mul_le_mul_left 32 (by memory_expands))
    funding := ha3 }
  simp only [midnightBlocks.midnight_block_13295_stack] at rd3
  have he1 := takeFeeTransferArgs_eval (evm := evm) hfOffer hfPayer hfBought hfSold hle
  rw [hs.env] at he1
  have hl : lookupCallable? frame.contract "SafeTransferLib_safeTransferFrom" =
      some (safeTransferFunctionFor true).toCallable := by
    rw [hc]; exact safeTransferLookup true
  rcases safeTransferHeap true frame.immutables (R :=
      [UInt256.ofNat payer.val, ⟨13329⟩, sellerCallback, solcAddrMask] ++ R)
      (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
      hh3 hgas hfork hs (by jump_dest) rd3 with
    hoog | ⟨hx, hr⟩ |
      ⟨evm1, σ1, out1, mem1, root1, aw1, k1, C1, hx1, hs1, hp1, hlo1, hh1, rd4⟩
  · exact Or.inl hoog
  · refine Or.inr (Or.inl ⟨?_, hr⟩)
    rw [takeTransfers_shape]
    exact ExecBlock.consRevert (internalCallFunctionRevert he1 hl
      (safeTransferBind true offer.market.loanToken payer I.codeOwner (UInt256.sub bought sold))
      (by simpa only [safeTransferFrame, hc] using hx))
  · let frame1 := resumeAfterInternalCall frame "__c28" none
    have hx1' : ExecStmt fork config frame evm
        (.internalCall "SafeTransferLib_safeTransferFrom" takeFeeTransferArgs "__c28")
        (.ok frame1 evm1) :=
      internalCallFunctionReturn he1 hl
        (safeTransferBind true offer.market.loanToken payer I.codeOwner (UInt256.sub bought sold))
        (by simpa only [safeTransferFrame, hc] using hx1)
    have hc1 : frame1.contract = contract := hc
    have hget (name : Ident) (hn : name ≠ "__c28") :
        frame1.locals.get? name = frame.locals.get? name :=
      store_get_ne _ _ (by simpa using hn.symm)
    have hread (off : UInt256) (hloff : 96 ≤ off.toNat) (hhi : off.toNat + 32 ≤ 608) :
        memLoad off mem1 = memLoad off mem := hp1.load off hloff (by omega) (by omega)
    have ho1 := ho.preserve (hp1.mono hlimit)
    have hloan1 := offerStoredLoanToken ho1 ((hread _ (by decide) (by decide)).trans hoffer)
    have rd5 := midnightBlocks.midnight_block_13304
      (by change R.length + 8 ≤ 1024; omega) (by jump_dest) rd4
    have ha5 := memoryFundingAt (credit := transferHeapCredit root1) rd5
      (by memory_fund hh1.funding)
    have hh5 : TransferHeap mem1 _ root1 _ := { hh1 with
      covered := hh1.covered.trans (Nat.mul_le_mul_left 32 (by memory_expands))
      funding := ha5 }
    simp only [midnightBlocks.midnight_block_13304_stack, hloan1, hclean,
      hread (UInt256.ofNat 416) (by decide) (by decide), hsold,
      hread (UInt256.ofNat 128) (by decide) (by decide), hreceiver] at rd5
    have he2 := takeSellerTransferArgs_eval (evm := evm1)
      ((hget _ (by decide)).trans hfOffer) ((hget _ (by decide)).trans hfPayer)
      ((hget _ (by decide)).trans hfReceiver) ((hget _ (by decide)).trans hfSold)
    rcases safeTransferHeap true frame1.immutables (R := sellerCallback :: solcAddrMask :: R)
        (by simp only [List.length_cons]; omega) hh5 hgas hfork hs1 (by jump_dest) rd5 with
      hoog | ⟨hx, hr⟩ |
        ⟨evm2, σ2, out2, mem2, root2, aw2, k2, C2, hx2, hs2, hp2, hlo2, hh2, rd6⟩
    · exact Or.inl hoog
    · refine Or.inr (Or.inl ⟨?_, hr⟩)
      rw [takeTransfers_shape]
      exact ExecBlock.consNormal hx1' (ExecBlock.consRevert (internalCallFunctionRevert he2 hl
        (safeTransferBind true offer.market.loanToken payer receiver sold)
        (by simpa only [safeTransferFrame, hc1] using hx)))
    · refine Or.inr (Or.inr ⟨evm2, σ2, mem2, out2, root2, aw2, k2, C2, ?_, hs2,
        hp1.trans (hp2.mono hlo1), hlo1.trans hlo2, hh2, rd6⟩)
      intro result hx
      rw [takeTransfers_shape]
      exact ExecBlock.consNormal hx1' (ExecBlock.consNormal (internalCallFunctionReturn he2 hl
        (safeTransferBind true offer.market.loanToken payer receiver sold)
        (by simpa only [safeTransferFrame, hc1] using hx2)) hx)

end Benchmarks.Midnight
