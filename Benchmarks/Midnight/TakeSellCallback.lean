import Benchmarks.Midnight.SellCallback

variable {fork : Ethereum.Fork}

/-! The optional seller callback rejoins the two token transfers. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

def takeSellDataFrame (frame : Frame) (offer : OfferData) (data : ByteArray) : Frame :=
  { frame with locals := frame.locals.insert "sellerCallbackData" (.bytes (takeSellerData offer data)) }

theorem takeSellCondition_eval {frame : Frame} {evm : State} {callback : AccountAddress}
    (hc : frame.locals.get? "sellerCallback" = some (.address callback)) :
    evalExpr? config frame evm takeSellCondition = .ok (.bool (decide (callback ≠ 0))) := by
  have hcast : castValue? (.int 0) (.elem .address) = some (.address 0) := rfl
  simp only [takeSellCondition, evalExpr?, hc, EvalResult.ofOption,
    EvalResult.bind, bind, pure, hcast, evalBinaryOp?]
  by_cases hz : callback = 0 <;> simp [hz]

theorem takeSellStmt_shape : takeTransition.body[70]! =
    .ite takeSellCondition
      [.letDecl "sellerCallbackData" (some .bytes) takeSellerDataExpr,
        sellCallbackStmt, .require sellMagicGuard] [] := by decide +kernel

theorem midnightTakeSellCallback {credit : Nat} {I : ExecutionEnv} {g : Sat256}
    {s0 evm : State} {frame : Frame} {mem rdata data : ByteArray}
    {aw root market arrayPtr offerRoot callbackPtr takerPtr id assets units fee user receiver
      wasLocked saved : UInt256} {offer : OfferData}
    {callback : AccountAddress} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 28 ≤ 1024)
    (ho : OfferStored mem ⟨832⟩ market arrayPtr callbackPtr offerRoot offer)
    (hlimit : offerRoot.toNat ≤ root.toNat)
    (hroot : root.toNat + 32 < 2^64) (hlo : 832 ≤ root.toNat) (hmem : 608 ≤ mem.size)
    (hd : MemoryByteString mem takerPtr data)
    (hbelow : takerPtr.toNat + 32 + paddedSize data.size ≤ root.toNat)
    (hoffer : memLoad (UInt256.ofNat 384) mem = ⟨832⟩)
    (htaker : memLoad (UInt256.ofNat 320) mem = takerPtr)
    (hfree : memLoad (UInt256.ofNat 64) mem = root)
    (hid : memLoad (UInt256.ofNat 512) mem = id)
    (haRead : memLoad (UInt256.ofNat 416) mem = assets)
    (huRead : calldataWord I.calldata 68 = units)
    (hfRead : memLoad (UInt256.ofNat 160) mem = fee)
    (hbRead : memLoad (UInt256.ofNat 448) mem = user)
    (hrRead : memLoad (UInt256.ofNat 128) mem = receiver)
    (hrcanon : receiver.toNat < EVM.addressModulus)
    (hf128 : fee.toNat < 2^128) (huser : user.toNat < EVM.addressModulus)
    (hfOffer : frame.locals.get? "offer" = some (Model.offerValue offer.value))
    (hfData : frame.locals.get? "takerCallbackData" = some (.bytes data))
    (hfId : frame.locals.get? "id" = some (wordBytes32Value id))
    (hfAssets : frame.locals.get? "sellerAssets" = some (.int assets.toNat))
    (hfUnits : frame.locals.get? "units" = some (.int units.toNat))
    (hfFee : frame.locals.get? "sellerPendingFeeDecrease" = some (.int fee.toNat))
    (hfUser : frame.locals.get? "seller" = some (.address (AccountAddress.ofNat user.toNat)))
    (hfReceiver : frame.locals.get? "receiver" =
      some (.address (AccountAddress.ofNat receiver.toNat)))
    (ht : frame.locals.get? "sellerCallback" = some (.address callback))
    (ha : MemoryFunding credit mem aw C) (hs : SourceState s0 I σ evm)
    (rd : RD fork midnightBytecode I g s0 ⟨13329⟩
      ([UInt256.ofNat callback.val, solcAddrMask, wasLocked, saved] ++ R)
      mem aw rdata σ k C) :
    X fork (g.toNat + 1) (D_J midnightBytecode 0) s0 = .error .OutOfGass ∨
    (ExecStmt fork config frame evm takeTransition.body[70]! .reverted ∧
      RDrev fork midnightBytecode g s0) ∨
    ∃ (frame' : Frame) (evm' : State) (σ' : AccountMap) (mem' out : ByteArray)
      (root' aw' ignored : UInt256) (k' C' : Nat),
      ExecStmt fork config frame evm takeTransition.body[70]! (.ok frame' evm') ∧
      frame'.contract = frame.contract ∧
      (∀ name, name ≠ "sellerCallbackData" → name ≠ "__c30" →
        frame'.locals.get? name = frame.locals.get? name) ∧
      SourceState s0 I σ' evm' ∧ MemoryPrefix mem mem' root.toNat ∧
      (root' = root ∨ root' = root + UInt256.ofNat 32) ∧
      memLoad (UInt256.ofNat 64) mem' = root' ∧ MemoryFunding credit mem' aw' C' ∧
      RD fork midnightBytecode I g s0 ⟨13336⟩
        ([ignored, wasLocked, saved] ++ R) mem' aw' out σ' k' C' := by
  rw [takeSellStmt_shape]
  have hc := takeSellCondition_eval (evm := evm) ht
  have hz : UInt256.ofNat callback.val = ⟨0⟩ ↔ callback = 0 := by
    rw [← accountAddress_roundtrip callback]
    constructor
    · intro h
      have hh := congrArg AccountAddress.ofUInt256 h
      simpa only [accountAddress_roundtrip] using hh
    · intro h
      rw [h]
      rfl
  have hclean : UInt256.land (UInt256.ofNat callback.val) solcAddrMask =
      UInt256.ofNat callback.val := addressWord_val_clean _
  by_cases hcb : callback = 0
  · have rd0 := midnightBlocks.midnight_block_13329_fallthrough
      (by change R.length + 5 ≤ 1024; omega) (by rw [hclean]; exact hz.mpr hcb) rd
    have ha0 := memoryFundingAt (credit := credit) rd0 (ha.mono (by omega))
    simp only [midnightBlocks.midnight_block_13329_fallthrough_stack, hclean] at rd0
    refine Or.inr (Or.inr ⟨frame, evm, σ, mem, rdata, root, _,
      UInt256.ofNat callback.val, _, _, ?_, rfl, ?_, hs, MemoryPrefix.refl _ _,
      Or.inl rfl, hfree, ha0, rd0⟩)
    · exact ExecStmt.iteFalse (by simpa only [hcb, ne_eq, not_true_eq_false, decide_false] using hc)
        ExecBlock.nil
    · intros; rfl
  · have rd0 := midnightBlocks.midnight_block_13329_taken
      (by change R.length + 5 ≤ 1024; omega)
      (by rw [hclean]; exact fun h ↦ hcb (hz.mp h)) (by jump_dest) rd
    have ha0 := memoryFundingAt (credit := credit) rd0 (ha.mono (by omega))
    simp only [midnightBlocks.midnight_block_13329_taken_stack, hclean] at rd0
    obtain ⟨aw1, k1, C1, ha1, rd1⟩ := midnightTakeSellerData
      (by change R.length + 7 ≤ 1024; omega) ho hoffer htaker ha0 rd0
    have hdata := takeSellerData_stored ho.callback hd
    have hdataBelow : (takeSellerDataPtr offer callbackPtr takerPtr).toNat + 32 +
        paddedSize (takeSellerData offer data).size ≤ root.toNat := by
      have hh := ho.extent
      by_cases hb : offer.buy = ⟨0⟩
      · simp only [takeSellerDataPtr, takeSellerData, if_pos hb]
        omega
      · simpa only [takeSellerDataPtr, takeSellerData, if_neg hb] using hbelow
    have hmarket : memLoad (memLoad (UInt256.ofNat 384) mem) mem = market := by
      rw [hoffer]
      exact ho.words.load_offset ⟨0, by change 0 < 15; decide⟩ rfl
    let frame1 := takeSellDataFrame frame offer data
    have hget (name : Ident) (hn : name ≠ "sellerCallbackData") :
        frame1.locals.get? name = frame.locals.get? name :=
      store_get_ne _ _ (by simpa using hn.symm)
    have hargs := sellCallbackArgs (frame := frame1) (evm := evm)
      ((hget _ (by decide)).trans hfOffer) ((hget _ (by decide)).trans hfId)
      ((hget _ (by decide)).trans hfAssets) ((hget _ (by decide)).trans hfUnits)
      ((hget _ (by decide)).trans hfFee) ((hget _ (by decide)).trans hfUser)
      ((hget _ (by decide)).trans hfReceiver)
      (by exact store_get_self _ _ _)
    have hdecl : ExecStmt fork config frame evm
        (.letDecl "sellerCallbackData" (some .bytes) takeSellerDataExpr) (.ok frame1 evm) :=
      ExecStmt.letDecl (evalTakeSellerData hfOffer hfData)
    have hcond : evalExpr? config frame evm takeSellCondition = .ok (.bool true) := by
      simpa only [decide_eq_true hcb] using hc
    rcases midnightSellCallback offer.market (by change R.length + 28 ≤ 1024; exact hstack)
        ho.market (by have hh := ho.extent; omega) hroot hlo hmem hdata hdataBelow hmarket hfree hid haRead huRead
        hfRead hbRead hrRead hrcanon hf128 huser ((hget _ (by decide)).trans ht) hargs ha1 hs rd1 with
      hoog | ⟨hx, hr⟩ | ⟨evm', σ', out, mem', aw2, k2, C2, hx, hs', hp, hfree', hm', ha2, rd2⟩
    · exact Or.inl hoog
    · exact Or.inr (Or.inl ⟨ExecStmt.iteTrue hcond (ExecBlock.consNormal hdecl hx), hr⟩)
    · have rd3 := midnightBlocks.midnight_block_13665
        (by change R.length + 4 ≤ 1024; omega) (by jump_dest) rd2
      have ha3 := memoryFundingAt (credit := credit) rd3
        ((ha2.weaken (by omega)).mono (by omega))
      refine Or.inr (Or.inr ⟨sellCallbackFrame frame1 (calldataWord out 0), evm', σ', mem', out, root + UInt256.ofNat 32, _, saved,
        _, _, ExecStmt.iteTrue hcond (ExecBlock.consNormal hdecl hx), rfl, ?_, hs', hp,
        Or.inr rfl, hfree', ha3, rd3⟩)
      intro name hn hn'
      exact (store_get_ne _ _ (by simpa using hn'.symm)).trans (hget name hn)

end Benchmarks.Midnight
