import Benchmarks.Dss.Dog.BarkRoutine

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Dss.Dog.Immutables

set_option maxRecDepth 2000000
set_option maxHeartbeats 0

section
set_option maxRecDepth 2000000
set_option maxHeartbeats 2000000
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.Dog

theorem RD.dogBarkDecodeToBody {v : DogImmutables} {code : ByteArray}
    {σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (hsize : I.calldata.size < UInt256.size) (hsz100 : 100 ≤ I.calldata.size)
    (hreach : ∃ k C, RD code I g (initState σ σ₀ g A I) ⟨785⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C) :
    ∃ k C, RD code I g (initState σ σ₀ g A I) ⟨2813⟩
      [barkKprKey I, barkUrnKey I, barkIlkWord I, ⟨448⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C := by
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨96⟩ = ⟨0⟩ := by
    exact solcDecodeLenCheckOkUnsigned (by simpa using hsz100) hsize
  have hdecoded := RD.solcExternalStaticArgsLenOk
    (code := code) (sel := sel) (entry := ⟨785⟩) (ret := ⟨448⟩)
    (decoded := ⟨807⟩) (need := ⟨96⟩) hreach
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (dogPatchedDJumpPrefix1405 ⟨807⟩ hpatch (by native_decide))
    hlt
  obtain ⟨_, _, hdecoded'⟩ := hdecoded
  obtain ⟨k, C, hbody⟩ := RD.dogBarkDecodeToRoutine hpatch hdecoded' rfl
    (dogPatchedJumpDest hpatch (by native_decide))
    (by simp only [List.length_singleton]; omega)
  exact ⟨k, C, by simpa using hbody⟩



end Benchmarks.Dss.Dog
