import Benchmarks.Dss.Dog.BarkReach

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Dss.Dog.Immutables

set_option maxRecDepth 2000000
set_option maxHeartbeats 0

section
set_option maxRecDepth 2000000
set_option maxHeartbeats 2000000
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.Dog

theorem RD.dogBarkDecodeToRoutine {v : DogImmutables} {code : ByteArray}
    {ee : ExecutionEnv} {g : Sat256} {s0 : EVM.State} {k C : ℕ}
    {decoded ret de : UInt256} {R : List UInt256} {mem rdata : ByteArray}
    {aw : UInt256} {acc : AccountMap}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (h : RD code ee g s0 decoded (de :: ⟨4⟩ :: ret :: R) mem aw rdata acc k C)
    (hdecoded : decoded = ⟨807⟩)
    (hroutine : (D_J code 0).contains ⟨2813⟩ = true)
    (hov : R.length + 7 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨2813⟩
      (barkKprKey ee :: barkUrnKey ee :: barkIlkWord ee :: ret :: R)
      mem aw rdata acc k' C' := by
  subst hdecoded
  have rd1 := h.jumpdest
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by evm_ov)
  have rd2 := rd1.pop
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by evm_ov)
  have rd3 := rd2.dup1
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by evm_ov)
  have rd4 := rd3.calldataload
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by evm_ov)
  have rd5 := rd4.swap1
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by evm_ov)
  have rd7 := rd5.push1 ⟨1⟩
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by evm_ov)
  have rd9 := rd7.push1 ⟨1⟩
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by evm_ov)
  have rd11 := rd9.push1 ⟨160⟩
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by evm_ov)
  have rd12 := rd11.shl
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by evm_ov)
  have rd13 := rd12.sub
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by evm_ov)
  have rd15 := rd13.push1 ⟨32⟩
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by evm_ov)
  have rd16 := rd15.dup3
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by evm_ov)
  have rd17 := rd16.add
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by evm_ov)
  have rd18 := rd17.calldataload
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by evm_ov)
  have rd19 := rd18.dup2
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by evm_ov)
  have rd20 := rd19.and
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by evm_ov)
  have rd21 := rd20.swap2
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by evm_ov)
  have rd23 := rd21.push1 ⟨64⟩
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by evm_ov)
  have rd24 := rd23.add
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by evm_ov)
  have rd25 := rd24.calldataload
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by evm_ov)
  have rd26 := rd25.and
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by evm_ov)
  have rd29 := rd26.push2 ⟨2813⟩
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by evm_ov)
  exact ⟨_, _, by
    simpa [barkKprKey, barkUrnKey, barkIlkWord, barkKprWord, barkUrnWord, calldataWord,
      show (⟨4⟩ : UInt256).toNat = 4 from by decide,
      show ((⟨32⟩ : UInt256) + ⟨4⟩).toNat = 36 from by decide,
      show ((⟨64⟩ : UInt256) + ⟨4⟩).toNat = 68 from by decide,
      show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask from by decide, u256_land_comm]
      using rd29.jump
        (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
        hroutine (by evm_ov)⟩


end Benchmarks.Dss.Dog
