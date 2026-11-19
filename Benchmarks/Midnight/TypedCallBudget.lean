import Benchmarks.Midnight.TypedCallFunding
import Benchmarks.Midnight.TransferBudget

/-! A zero-value typed CALL preserves a transfer budget for buffers already in memory. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

theorem typedZeroValueCallBudget {budgetRoot : UInt256} {credit : Nat} {code : ByteArray} {I : ExecutionEnv}
    {g : Sat256} {s0 evm : State} {pc : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {cfg : Config} {name : Ident} {args : List Value}
    {gasArg target inOffset inSize outOffset outSize : UInt256}
    (rd : RD code I g s0 pc
      (gasArg :: target :: ⟨0⟩ :: inOffset :: inSize :: outOffset :: outSize :: R)
      mem aw rdata σ k C)
    (hs : SourceState s0 I σ evm) (hdec : decode code pc = some (.CALL, .none))
    (hcd : cfg.externalABI.encode? name args =
      some (mem.readWithPadding inOffset.toNat inSize.toNat))
    (hsmall : inSize.toNat ≤ Ethereum.EVM.maxReturnDataSizeByGas)
    (hstack : R.length + 1 ≤ 1024) (ha : TransferBudget budgetRoot credit mem aw C)
    (hin : inOffset.toNat + inSize.toNat ≤ mem.size)
    (hout : outOffset.toNat + outSize.toNat ≤ mem.size) :
    X (g.toNat + 1) (D_J code 0) s0 = .error .OutOfGass ∨
    ∃ (evm' : State) (σ' : AccountMap) (success : Bool) (out : ByteArray) (aw' : UInt256) (k' C' : Nat),
      typedCallViaEVM cfg evm (AccountAddress.ofUInt256 target) name 0 args
        (success, evm', out) true ∧ SourceState s0 I σ' evm' ∧
      RD code I g s0 (pc + ⟨1⟩) ((if success then ⟨1⟩ else ⟨0⟩) :: R)
        (out.write 0 mem outOffset.toNat (min outSize (UInt256.ofNat out.size)).toNat)
        aw' out σ' k' C' ∧ out.size < 2^138 ∧
      (success = true → TransferBudget budgetRoot credit
        (out.write 0 mem outOffset.toNat (min outSize (UInt256.ofNat out.size)).toNat) aw' C') := by
  by_cases hd : I.depth = 1024
  · obtain ⟨k', C', rd'⟩ := rd.callDepthLimit hdec hd hstack
    refine Or.inr ⟨{ evm with
      substate := callSubstate evm.executionEnv.fork evm.accountMap
        (AccountAddress.ofUInt256 target) evm.substate }, σ,
      false, ByteArray.empty, _, k', C', ?_, ⟨hs.world, hs.env, hs.accounts⟩,
      rd', by decide, by simp⟩
    refine ⟨_, hcd, callViaEVM.callNotMade rfl rfl ?_⟩
    intro hn
    exact hn.2 (by rw [hs.env]; exact hd)
  · have hdlt : I.depth.val < 1024 := by
      have hb := I.depth.isLt
      have hn : I.depth.val ≠ 1024 := fun h ↦ hd (Fin.ext h)
      omega
    obtain ⟨σ', z, out, AIn, callGas, k', C', ⟨g'', A', hΘ, hcost⟩, rd', _, _⟩ :=
      callWithForwardingCost rd hdec hdlt hstack
    rcases hcost with hoog | ⟨hC, _⟩
    · exact Or.inl hoog
    have hsize : out.size < 2^138 :=
      Theta_returnData_size_lt_2pow138_of_eq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hΘ
        ((Ethereum.EVM.ByteArray.readWithPadding_size_le _ _ _).trans hsmall)
    have ha' := transferBudgetAt (root := budgetRoot) (credit := credit) rd' (by
      rcases ha with hsmall | ⟨halign, hf⟩
      · exact Or.inl hsmall
      · exact Or.inr ⟨halign, staticCallMemoryFunding hf (by omega)
          (hin.trans hf.covered) (hout.trans hf.covered)⟩)
    refine Or.inr ⟨{ evm with accountMap := σ', substate := A' }, σ', z, out, _, k', C',
      ?_, ⟨hs.world, hs.env, rfl⟩, rd', hsize, fun _ ↦ ha'⟩
    refine ⟨_, hcd, ?_⟩
    apply callViaEVM.callMade (valueWord := ⟨0⟩) (g' := g'') (A' := A')
      wordOfInt_zero.symm ?_ rfl (Fin.zero_le _) ?_
    · refine ⟨callGas, AIn, ?_⟩
      simpa only [hs.env, hs.world, ← hs.accounts, Bool.true_and, accountAddress_roundtrip]
        using hΘ
    · simpa only [hs.env] using hd

end Benchmarks.Midnight
