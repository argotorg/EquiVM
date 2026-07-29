import Benchmarks.Dss.Vow.Bytecode
import Solm.Semantics

/-!
# MakerDAO/Sky DSS Vow trusted bytecode facts

The selector facts are trusted because `ffi.KEC` is opaque to Lean. The jump-destination tables are
computed from the concrete byte arrays in `Bytecode.lean`; this file gives them proof-local names.
-/

open Solm Ethereum Ethereum.EVM

namespace Benchmarks.Dss.Vow

/-- `keccak("Ash()")[0:4] = 0x2a1d2b3c`. -/
axiom AshSelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr AshTransition))).extract 0 4 =
      ⟨#[0x2a, 0x1d, 0x2b, 0x3c]⟩

/-- `keccak("Sin()")[0:4] = 0xd0adc35f`. -/
axiom SinSelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr SinTransition))).extract 0 4 =
      ⟨#[0xd0, 0xad, 0xc3, 0x5f]⟩

/-- `keccak("bump()")[0:4] = 0x68110b2f`. -/
axiom bumpSelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr bumpTransition))).extract 0 4 =
      ⟨#[0x68, 0x11, 0x0b, 0x2f]⟩

/-- `keccak("cage()")[0:4] = 0x69245009`. -/
axiom cageSelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr cageTransition))).extract 0 4 =
      ⟨#[0x69, 0x24, 0x50, 0x09]⟩

/-- `keccak("deny(address)")[0:4] = 0x9c52a7f1`. -/
axiom denySelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr denyTransition))).extract 0 4 =
      ⟨#[0x9c, 0x52, 0xa7, 0xf1]⟩

/-- `keccak("dump()")[0:4] = 0xe4330545`. -/
axiom dumpSelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr dumpTransition))).extract 0 4 =
      ⟨#[0xe4, 0x33, 0x05, 0x45]⟩

/-- `keccak("fess(uint256)")[0:4] = 0x697efb78`. -/
axiom fessSelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr fessTransition))).extract 0 4 =
      ⟨#[0x69, 0x7e, 0xfb, 0x78]⟩

/-- `keccak("file(bytes32,uint256)")[0:4] = 0x29ae8114`. -/
axiom fileUintSelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr fileUintTransition))).extract 0 4 =
      ⟨#[0x29, 0xae, 0x81, 0x14]⟩

/-- `keccak("file(bytes32,address)")[0:4] = 0xd4e8be83`. -/
axiom fileAddressSelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr fileAddressTransition))).extract 0 4 =
      ⟨#[0xd4, 0xe8, 0xbe, 0x83]⟩

/-- `keccak("flap()")[0:4] = 0x0e01198b`. -/
axiom flapSelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr flapTransition))).extract 0 4 =
      ⟨#[0x0e, 0x01, 0x19, 0x8b]⟩

/-- `keccak("flapper()")[0:4] = 0x5ca0d723`. -/
axiom flapperSelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr flapperTransition))).extract 0 4 =
      ⟨#[0x5c, 0xa0, 0xd7, 0x23]⟩

/-- `keccak("flog(uint256)")[0:4] = 0xd7ee674b`. -/
axiom flogSelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr flogTransition))).extract 0 4 =
      ⟨#[0xd7, 0xee, 0x67, 0x4b]⟩

/-- `keccak("flop()")[0:4] = 0xbbbb0d7b`. -/
axiom flopSelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr flopTransition))).extract 0 4 =
      ⟨#[0xbb, 0xbb, 0x0d, 0x7b]⟩

/-- `keccak("flopper()")[0:4] = 0x4081d73a`. -/
axiom flopperSelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr flopperTransition))).extract 0 4 =
      ⟨#[0x40, 0x81, 0xd7, 0x3a]⟩

/-- `keccak("heal(uint256)")[0:4] = 0xf37ac61c`. -/
axiom healSelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr healTransition))).extract 0 4 =
      ⟨#[0xf3, 0x7a, 0xc6, 0x1c]⟩

/-- `keccak("hump()")[0:4] = 0x1b8e8cfa`. -/
axiom humpSelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr humpTransition))).extract 0 4 =
      ⟨#[0x1b, 0x8e, 0x8c, 0xfa]⟩

/-- `keccak("kiss(uint256)")[0:4] = 0x2506855a`. -/
axiom kissSelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr kissTransition))).extract 0 4 =
      ⟨#[0x25, 0x06, 0x85, 0x5a]⟩

/-- `keccak("live()")[0:4] = 0x957aa58c`. -/
axiom liveSelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr liveTransition))).extract 0 4 =
      ⟨#[0x95, 0x7a, 0xa5, 0x8c]⟩

/-- `keccak("rely(address)")[0:4] = 0x65fae35e`. -/
axiom relySelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr relyTransition))).extract 0 4 =
      ⟨#[0x65, 0xfa, 0xe3, 0x5e]⟩

/-- `keccak("sin(uint256)")[0:4] = 0xcb5cc109`. -/
axiom sinSelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr sinTransition))).extract 0 4 =
      ⟨#[0xcb, 0x5c, 0xc1, 0x09]⟩

/-- `keccak("sump()")[0:4] = 0xc349d362`. -/
axiom sumpSelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr sumpTransition))).extract 0 4 =
      ⟨#[0xc3, 0x49, 0xd3, 0x62]⟩

/-- `keccak("vat()")[0:4] = 0x36569e77`. -/
axiom vatSelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr vatTransition))).extract 0 4 =
      ⟨#[0x36, 0x56, 0x9e, 0x77]⟩

/-- `keccak("wait()")[0:4] = 0x64bd7013`. -/
axiom waitSelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr waitTransition))).extract 0 4 =
      ⟨#[0x64, 0xbd, 0x70, 0x13]⟩

/-- `keccak("wards(address)")[0:4] = 0xbf353dbb`. -/
axiom wardsSelectorBytes :
    (ffi.KEC (String.toByteArray (Solm.transitionSigStr wardsTransition))).extract 0 4 =
      ⟨#[0xbf, 0x35, 0x3d, 0xbb]⟩

/-- The `JUMPDEST` set of `vowBytecode`, named for the Vow proof. -/
@[valid_jumps] theorem vowValidJumps :
    Ethereum.EVM.D_J vowBytecode 0
      = #[
      ⟨16⟩, ⟨124⟩, ⟨195⟩, ⟨277⟩, ⟨344⟩, ⟨349⟩, ⟨357⟩, ⟨375⟩, ⟨383⟩, ⟨405⟩,
      ⟨412⟩, ⟨414⟩, ⟨436⟩, ⟨449⟩, ⟨457⟩, ⟨465⟩, ⟨493⟩, ⟨501⟩, ⟨509⟩, ⟨517⟩,
      ⟨539⟩, ⟨555⟩, ⟨563⟩, ⟨571⟩, ⟨593⟩, ⟨600⟩, ⟨608⟩, ⟨630⟩, ⟨646⟩, ⟨654⟩,
      ⟨676⟩, ⟨692⟩, ⟨700⟩, ⟨722⟩, ⟨729⟩, ⟨737⟩, ⟨759⟩, ⟨781⟩, ⟨803⟩, ⟨810⟩,
      ⟨818⟩, ⟨840⟩, ⟨847⟩, ⟨933⟩, ⟨953⟩, ⟨975⟩, ⟨985⟩, ⟨993⟩, ⟨1068⟩, ⟨1088⟩,
      ⟨1110⟩, ⟨1190⟩, ⟨1273⟩, ⟨1293⟩, ⟨1315⟩, ⟨1325⟩, ⟨1333⟩, ⟨1403⟩, ⟨1494⟩, ⟨1514⟩,
      ⟨1536⟩, ⟨1543⟩, ⟨1549⟩, ⟨1625⟩, ⟨1700⟩, ⟨1720⟩, ⟨1742⟩, ⟨1823⟩, ⟨1835⟩, ⟨1915⟩,
      ⟨1935⟩, ⟨1942⟩, ⟨2031⟩, ⟨2056⟩, ⟨2081⟩, ⟨2106⟩, ⟨2131⟩, ⟨2156⟩, ⟨2233⟩, ⟨2237⟩,
      ⟨2243⟩, ⟨2258⟩, ⟨2273⟩, ⟨2288⟩, ⟨2294⟩, ⟨2383⟩, ⟨2453⟩, ⟨2482⟩, ⟨2488⟩, ⟨2577⟩,
      ⟨2647⟩, ⟨2750⟩, ⟨2770⟩, ⟨2792⟩, ⟨2856⟩, ⟨2876⟩, ⟨2960⟩, ⟨2980⟩, ⟨3070⟩, ⟨3090⟩,
      ⟨3112⟩, ⟨3189⟩, ⟨3209⟩, ⟨3231⟩, ⟨3238⟩, ⟨3292⟩, ⟨3312⟩, ⟨3318⟩, ⟨3407⟩, ⟨3433⟩,
      ⟨3462⟩, ⟨3468⟩, ⟨3474⟩, ⟨3563⟩, ⟨3589⟩, ⟨3675⟩, ⟨3753⟩, ⟨3828⟩, ⟨3848⟩, ⟨3870⟩,
      ⟨3945⟩, ⟨3959⟩, ⟨4060⟩, ⟨4078⟩, ⟨4084⟩, ⟨4102⟩, ⟨4108⟩, ⟨4197⟩, ⟨4296⟩, ⟨4316⟩,
      ⟨4419⟩, ⟨4439⟩, ⟨4448⟩, ⟨4498⟩, ⟨4511⟩, ⟨4586⟩, ⟨4614⟩, ⟨4634⟩, ⟨4640⟩, ⟨4715⟩,
      ⟨4735⟩, ⟨4757⟩, ⟨4838⟩, ⟨4921⟩, ⟨4997⟩, ⟨5074⟩, ⟨5090⟩, ⟨5096⟩, ⟨5112⟩, ⟨5128⟩,
      ⟨5130⟩
      ] := by
  simpa using validJumps

/-- The `JUMPDEST` set of `vowCreationBytecode`, named for the Vow proof. -/
@[valid_jumps] theorem vowCreationValidJumps :
    Ethereum.EVM.D_J vowCreationBytecode 0
      = #[
      ⟨16⟩, ⟨51⟩, ⟨213⟩, ⟨233⟩, ⟨276⟩, ⟨384⟩, ⟨455⟩, ⟨537⟩, ⟨604⟩, ⟨609⟩,
      ⟨617⟩, ⟨635⟩, ⟨643⟩, ⟨665⟩, ⟨672⟩, ⟨674⟩, ⟨696⟩, ⟨709⟩, ⟨717⟩, ⟨725⟩,
      ⟨753⟩, ⟨761⟩, ⟨769⟩, ⟨777⟩, ⟨799⟩, ⟨815⟩, ⟨823⟩, ⟨831⟩, ⟨853⟩, ⟨860⟩,
      ⟨868⟩, ⟨890⟩, ⟨906⟩, ⟨914⟩, ⟨936⟩, ⟨952⟩, ⟨960⟩, ⟨982⟩, ⟨989⟩, ⟨997⟩,
      ⟨1019⟩, ⟨1041⟩, ⟨1063⟩, ⟨1070⟩, ⟨1078⟩, ⟨1100⟩, ⟨1107⟩, ⟨1193⟩, ⟨1213⟩, ⟨1235⟩,
      ⟨1245⟩, ⟨1253⟩, ⟨1328⟩, ⟨1348⟩, ⟨1370⟩, ⟨1450⟩, ⟨1533⟩, ⟨1553⟩, ⟨1575⟩, ⟨1585⟩,
      ⟨1593⟩, ⟨1663⟩, ⟨1754⟩, ⟨1774⟩, ⟨1796⟩, ⟨1803⟩, ⟨1809⟩, ⟨1885⟩, ⟨1960⟩, ⟨1980⟩,
      ⟨2002⟩, ⟨2083⟩, ⟨2095⟩, ⟨2175⟩, ⟨2195⟩, ⟨2202⟩, ⟨2291⟩, ⟨2316⟩, ⟨2341⟩, ⟨2366⟩,
      ⟨2391⟩, ⟨2416⟩, ⟨2493⟩, ⟨2497⟩, ⟨2503⟩, ⟨2518⟩, ⟨2533⟩, ⟨2548⟩, ⟨2554⟩, ⟨2643⟩,
      ⟨2713⟩, ⟨2742⟩, ⟨2748⟩, ⟨2837⟩, ⟨2907⟩, ⟨3010⟩, ⟨3030⟩, ⟨3052⟩, ⟨3116⟩, ⟨3136⟩,
      ⟨3220⟩, ⟨3240⟩, ⟨3330⟩, ⟨3350⟩, ⟨3372⟩, ⟨3449⟩, ⟨3469⟩, ⟨3491⟩, ⟨3498⟩, ⟨3552⟩,
      ⟨3572⟩, ⟨3578⟩, ⟨3667⟩, ⟨3693⟩, ⟨3722⟩, ⟨3728⟩, ⟨3734⟩, ⟨3823⟩, ⟨3849⟩, ⟨3935⟩,
      ⟨4013⟩, ⟨4088⟩, ⟨4108⟩, ⟨4130⟩, ⟨4205⟩, ⟨4219⟩, ⟨4320⟩, ⟨4338⟩, ⟨4344⟩, ⟨4362⟩,
      ⟨4368⟩, ⟨4457⟩, ⟨4556⟩, ⟨4576⟩, ⟨4679⟩, ⟨4699⟩, ⟨4708⟩, ⟨4758⟩, ⟨4771⟩, ⟨4846⟩,
      ⟨4874⟩, ⟨4894⟩, ⟨4900⟩, ⟨4975⟩, ⟨4995⟩, ⟨5017⟩, ⟨5098⟩, ⟨5181⟩, ⟨5257⟩, ⟨5334⟩,
      ⟨5350⟩, ⟨5356⟩, ⟨5372⟩, ⟨5388⟩, ⟨5390⟩
      ] := by
  simpa using creationValidJumps

end Benchmarks.Dss.Vow
