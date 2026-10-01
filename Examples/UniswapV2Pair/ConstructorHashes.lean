import Examples.UniswapV2Pair.Spec

open Ethereum
namespace UniswapV2Pair

/-! Keccak identities for the compiler's precomputed constructor constants. -/

abbrev constructorNameHashWord : UInt256 :=
  ⟨86753177656789946143617852270382413483605072673293953774383968070347263481656⟩

abbrev constructorVersionHashWord : UInt256 :=
  ⟨90743482286830539503240959006302832933333810038750515972785732718729991261126⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
/-- `keccak256("Uniswap V2")`, embedded by the compiler at creation PC 107. -/
theorem constructorNameHash :
  KEC nameBytes = constructorNameHashWord.toByteArray := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
/-- `keccak256("1")`, embedded by the compiler at creation PC 144. -/
theorem constructorVersionHash :
  KEC versionBytes = constructorVersionHashWord.toByteArray := by
  decide +kernel

end UniswapV2Pair
