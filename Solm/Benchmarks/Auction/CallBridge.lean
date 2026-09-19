import Solm.Benchmarks.Auction.CallState

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

def callOutputMem (mem out : ByteArray) (offset size : UInt256) : ByteArray :=
  out.write 0 mem offset.toNat (min size (UInt256.ofNat out.size)).toNat

def callActiveWords (aw inOffset inSize outOffset outSize : UInt256) : UInt256 :=
  UInt256.ofNat (MachineState.M (MachineState.M aw.toNat inOffset.toNat inSize.toNat)
    outOffset.toNat outSize.toNat)

-- LIBRARY CANDIDATE: every CALL outcome is paired with the same source-level raw call.
-- The call gas and input substate come from the proved RD step's actual Θ link.
theorem callBridge {code I g s0 pc R mem aw rdata cA σ k C evm}
    {gasArg target value inOffset inSize outOffset outSize : UInt256} {calldata : ByteArray}
    (h : RD code I g s0 pc
      (gasArg :: target :: value :: inOffset :: inSize :: outOffset :: outSize :: R)
      mem aw rdata (cA, σ) k C)
    (hs : SourceState s0 I cA σ evm) (hperm : I.perm = true)
    (hdec : decode code pc = some (.CALL, .none))
    (hcd : mem.readWithPadding inOffset.toNat inSize.toNat = calldata)
    (hsmall : calldata.size ≤ Ethereum.EVM.maxReturnDataSizeByGas)
    (hov : R.length + 1 ≤ 1024) :
    ∃ (evm' : EVM.State) (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap)
      (z : Bool) (out : ByteArray) (k' C' : Nat),
      callViaEVM evm (AccountAddress.ofUInt256 target) (Int.ofNat value.toNat)
        calldata (z, evm', out) ∧
      SourceState s0 I cA' σ' evm' ∧
      RD code I g s0 (pc + ⟨1⟩) ((if z then ⟨1⟩ else ⟨0⟩) :: R)
        (callOutputMem mem out outOffset outSize)
        (callActiveWords aw inOffset inSize outOffset outSize) out (cA', σ') k' C' ∧
      out.size < 2 ^ 138 := by
  by_cases hd : I.depth = 1024
  · obtain ⟨_, _, rd⟩ := h.callValueDepthLimit hperm hdec hd hov
    have hraw := callStateNotMade (target := target) (value := value) (calldata := calldata)
      hs (fun hn => hn.2 hd)
    obtain ⟨evm', hcall, hs'⟩ := hs.callTransport hraw
    exact ⟨evm', cA, σ, false, ByteArray.empty, _, _, hcall, hs', rd, by decide⟩
  · have hdlt : I.depth.val < 1024 := by
      have hb := I.depth.isLt
      have hn : I.depth.val ≠ 1024 := by
        intro hv
        exact hd (Fin.ext hv)
      omega
    by_cases hb : value ≤ (σ.find? I.codeOwner |>.elim ⟨0⟩ (·.balance))
    · obtain ⟨cA', σ', z, out, AIn, callGas, k', C', ⟨gasLeft, AS', hΘ⟩, rd, _⟩ :=
        h.callValueMade hdec hperm hb hdlt hov
      rw [hcd] at hΘ
      have ho : out.size < 2 ^ 138 :=
        Theta_returnData_size_lt_2pow138_of_eq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hΘ hsmall
      have hraw := callStateMade hs hperm hb hdlt hΘ
      obtain ⟨evm', hcall, hs'⟩ := hs.callTransport hraw
      exact ⟨evm', cA', σ', z, out, k', C', hcall, hs', rd, ho⟩
    · obtain ⟨_, _, rd⟩ := h.callValueInsufficientBalance hperm hdec hb hdlt hov
      have hraw := callStateNotMade (target := target) (value := value) (calldata := calldata)
        hs (fun hn => hb hn.1)
      obtain ⟨evm', hcall, hs'⟩ := hs.callTransport hraw
      exact ⟨evm', cA, σ, false, ByteArray.empty, _, _, hcall, hs', rd, by decide⟩

end Auction
