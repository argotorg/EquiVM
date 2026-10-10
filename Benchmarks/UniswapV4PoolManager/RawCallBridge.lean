import Benchmarks.UniswapV4PoolManager.Common
import Reasoning.ExternalCall

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

-- GENERALIZES Reasoning.Theory.callBridge to zero-value CALLs in static mode.
theorem rawCallBridge {code : ByteArray} {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {pc : UInt256} {mem rdata calldata : ByteArray} {aw : UInt256} {k C : Nat}
    {gasArg target value inOffset inSize outOffset outSize : UInt256} {R : List UInt256}
    (hI : evm.executionEnv = I) (hσ0 : evm.σ₀ = s0.σ₀)
    (hp : I.perm = true ∨ value = ⟨0⟩)
    (h : RD code I g s0 pc (gasArg :: target :: value :: inOffset :: inSize :: outOffset :: outSize :: R)
      mem aw rdata evm.accountMap k C)
    (hdec : decode code pc = some (.CALL, .none))
    (hcd : mem.readWithPadding inOffset.toNat inSize.toNat = calldata)
    (hsmall : calldata.size ≤ Ethereum.EVM.maxReturnDataSizeByGas) (hstack : R.length+1 ≤ 1024) :
    ∃ evm' z out k' C',
      callViaEVM evm (AccountAddress.ofUInt256 target) (Int.ofNat value.toNat) calldata (z, evm', out) ∧
      evm'.executionEnv = I ∧ evm'.σ₀ = s0.σ₀ ∧
      RD code I g s0 (pc+⟨1⟩) ((if z then ⟨1⟩ else ⟨0⟩) :: R)
        (callOutputMem mem out outOffset outSize) (callActiveWords aw inOffset inSize outOffset outSize)
        out evm'.accountMap k' C' ∧ out.size < 2^138 := by
  rcases hp with hp | rfl
  · obtain ⟨evm', σ', z, out, k', C', hc, hs, hr, ho⟩ :=
      callBridge h ⟨hσ0, hI, rfl⟩ hp hdec hcd hsmall hstack
    rw [hs.accounts] at hr
    exact ⟨evm', z, out, k', C', hc, hs.env, hs.world, hr, ho⟩
  · by_cases hd : I.depth = 1024
    · obtain ⟨k', C', hr⟩ := RD.callDepthLimit h hdec hd hstack
      have hc : callViaEVM evm (AccountAddress.ofUInt256 target) 0 calldata
          (false, {evm with substate := (evm.addAccessedAccount (AccountAddress.ofUInt256 target)).substate}, .empty) := by
        apply callViaEVM.callNotMade rfl rfl
        intro hh
        exact hh.2 (by rw [hI]; exact hd)
      exact ⟨_, false, .empty, k', C', hc, hI, hσ0, hr, by decide⟩
    · have hdepth : I.depth.val < 1024 := by
        have hb := I.depth.isLt
        have hn : I.depth.val ≠ 1024 := fun he => hd (Fin.ext he)
        omega
      obtain ⟨σ', z, out, Ain, callGas, k', C', ⟨gasLeft, A', hΘ⟩, hr, _⟩ :=
        RD.call h hdec hdepth hstack
      rw [hcd] at hΘ
      have ho : out.size < 2^138 :=
        Theta_returnData_size_lt_2pow138_of_eq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hΘ hsmall
      have hc : callViaEVM evm (AccountAddress.ofUInt256 target) 0 calldata
          (z, {evm with accountMap := σ', substate := A'}, out) := by
        apply callViaEVM.callMade (g' := gasLeft) (A' := A') wordOfInt_zero.symm
          ⟨callGas, Ain, ?_⟩ rfl (Fin.zero_le _) (by rw [hI]; exact hd)
        simpa only [hI, hσ0, Bool.true_and, accountAddress_roundtrip] using hΘ
      exact ⟨_, z, out, k', C', hc, hI, hσ0, hr, ho⟩

end Benchmarks.UniswapV4PoolManager
