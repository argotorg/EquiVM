import Examples.UniswapV2Pair.Spec

open Ethereum
namespace UniswapV2Pair

/-! Fixed Keccak identities for the compiler's precomputed constructor constants.
These trusted facts were explicitly authorized by the user, following the selector-fact convention.
-/

abbrev constructorNameHashWord : UInt256 :=
  ⟨86753177656789946143617852270382413483605072673293953774383968070347263481656⟩

abbrev constructorVersionHashWord : UInt256 :=
  ⟨90743482286830539503240959006302832933333810038750515972785732718729991261126⟩

/-- `keccak256("Uniswap V2")`, embedded by the compiler at creation PC 107. -/
axiom constructorNameHash :
  ffi.KEC nameBytes = constructorNameHashWord.toByteArray

/-- `keccak256("1")`, embedded by the compiler at creation PC 144. -/
axiom constructorVersionHash :
  ffi.KEC versionBytes = constructorVersionHashWord.toByteArray

end UniswapV2Pair
