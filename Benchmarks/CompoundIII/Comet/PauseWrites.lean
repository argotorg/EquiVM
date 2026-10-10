import Benchmarks.CompoundIII.Comet.PauseInputs
import Benchmarks.CompoundIII.Comet.PackedWrites

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 10000

def pauseFlagWord (a : PauseInputs) : UInt256 :=
  UInt256.lor (UInt256.shiftLeft (boolWord a.buy) ⟨4⟩)
    (UInt256.lor (UInt256.shiftLeft (boolWord a.absorb) ⟨3⟩)
      (UInt256.lor (UInt256.shiftLeft (boolWord a.withdraw) ⟨2⟩)
        (UInt256.lor (UInt256.shiftLeft (boolWord a.transfer) ⟨1⟩) (boolWord a.supply))))

def pausePackedWord (old flags : UInt256) : UInt256 :=
  UInt256.lor
    (UInt256.land
      (UInt256.lnot (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 248))
        (UInt256.ofNat 1))) (UInt256.shiftLeft flags (UInt256.ofNat 248)))
    (UInt256.land
      (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 248)) (UInt256.ofNat 1)) old)

-- LIBRARY CANDIDATE: writing the final byte preserves the other 31 packed bytes.
theorem lastByteWriteBits (old flags : BitVec 256) :
    old % BitVec.ofNat 256 (256^31) +
      BitVec.ofNat 256 (256^31) * (flags % BitVec.ofNat 256 256) =
    ((~~~(BitVec.ofNat 256 (2^248-1))) &&& (flags <<< 248)) |||
      (BitVec.ofNat 256 (2^248-1) &&& old) := by bv_decide

theorem pausePackedWord_eq (old flags : UInt256) :
    packedWriteWord old flags 31 1 = pausePackedWord old flags := by
  have ho : old.toNat / 256^(31+1) = 0 := Nat.div_eq_of_lt old.val.isLt
  unfold packedWriteWord
  rw [ho, Nat.mul_zero, Nat.add_zero]
  let x : BitVec 256 := ⟨old.val⟩
  let y : BitVec 256 := ⟨flags.val⟩
  apply congrArg UInt256.mk
  change (BitVec.ofNat 256 (x.toNat % 256^31 + 256^31 * (y.toNat % 256^1))).toFin = _
  rw [BitVec.ofNat_add, BitVec.ofNat_mul, bitvecOfNatMod x _ (by decide),
    bitvecOfNatMod y _ (by decide), Nat.pow_one, lastByteWriteBits]
  simp only [pausePackedWord, UInt256.land, UInt256.lor, UInt256.lnot,
    BitVec.toFin_and, BitVec.toFin_or, BitVec.toFin_not]
  rfl

def pauseSourceState (evm : EVM.State) (a : PauseInputs) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨1⟩
    (pausePackedWord (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩) (pauseFlagWord a))

def pauseAccounts (σ : AccountMap) (I : ExecutionEnv) (a : PauseInputs) : AccountMap :=
  sstoreAccountMap I.codeOwner σ ⟨1⟩ (pausePackedWord (solcSlotWordAt ⟨1⟩ σ I) (pauseFlagWord a))

theorem pauseSourceState_accountMap {σ σ₀ A I} {g : Sat256} (a : PauseInputs) :
    (pauseSourceState (initState σ σ₀ g A I) a).accountMap = pauseAccounts σ I a := by
  simp only [pauseSourceState, storageStore_accountMap, storageLoad_initState_solcSlotWord]
  rfl

theorem assignPauseFlags (evm : EVM.State) (locals imms : Store) (a : PauseInputs)
    (hlocal : locals.get? "pauseFlags" = none) :
    assignStorageRef? config { contract := contract, locals := locals, immutables := imms }
      evm .storage ⟨"pauseFlags", []⟩ (.int (pauseFlagWord a).toNat) =
      .ok ({ contract := contract, locals := locals, immutables := imms }, pauseSourceState evm a) := by
  apply assignStorageRef_storage_scalar (hbackend := rfl)
    (loc := { slot := ⟨1⟩, offset := 31, size := 1, hbound := by decide,
              type := .int (.uint ⟨8, by decide⟩) })
    (er := ⟨"pauseFlags", []⟩) (ty := .elem (.int (.uint ⟨8, by decide⟩))) hlocal
  · simp only [evalStorageRef, evalStorageRefSteps, pure, bind, EvalResult.bind]
  · rfl
  · rfl
  · exact Or.inl ⟨_, rfl⟩
  · unfold pauseSourceState
    rw [← pausePackedWord_eq]
    exact storageLocStore_packed_int evm ⟨1⟩ (pauseFlagWord a) 31 1 _

end Benchmarks.CompoundIII.Comet
