# CometWithExtendedAssetList bytecode report

Derived from `runtime.hex`/`creation.hex` by `scripts/bytecode_report.py`; a development aid, not a proof artifact.

- runtime: 18599 bytes (18546 executable + 53 metadata), 10434 instructions, 1237 basic blocks
- creation: 21425 bytes (21372 executable), 12312 instructions, 1342 basic blocks
- compiler: solc 0.8.15+commit.e14f2714.Linux.g++; settings `{"optimizer": {"details": {"yulDetails": {"optimizerSteps": "dhfoDgvulfnTUtnIf [xa[r]scLM cCTUtTOntnfDIul Lcul Vcul [j] Tpeul xa[rul] xa[r]cL gvif CTUca[r]LsTOtfDnca[r]Iulc] jmul[jul] VcTOcul jmul"}}, "enabled": true, "runs": 1}, "viaIR": true}`
- immutables: `governor` (AST id 1249) at offsets [1592, 3441, 5137, 6161], `pauseGuardian` (AST id 1253) at offsets [2168, 3703], `baseToken` (AST id 1257) at offsets [2078, 5008, 5625, 6266, 6450, 9907, 12117, 12429, 14552, 15644, 15869], `baseTokenPriceFeed` (AST id 1261) at offsets [6768, 10264, 17068, 18119], `extensionDelegate` (AST id 1265) at offsets [3767, 18431], `supplyKink` (AST id 1269) at offsets [4926, 8616], `supplyPerSecondInterestRateSlopeLow` (AST id 1273) at offsets [3925, 8676, 8782], `supplyPerSecondInterestRateSlopeHigh` (AST id 1277) at offsets [4196, 8830], `supplyPerSecondInterestRateBase` (AST id 1281) at offsets [4550, 8715], `borrowKink` (AST id 1285) at offsets [4430, 8888], `borrowPerSecondInterestRateSlopeLow` (AST id 1289) at offsets [2599, 8948, 9054], `borrowPerSecondInterestRateSlopeHigh` (AST id 1293) at offsets [2353, 9102], `borrowPerSecondInterestRateBase` (AST id 1297) at offsets [4064, 8987], `storeFrontPriceFactor` (AST id 1301) at offsets [1966, 18059], `baseScale` (AST id 1305) at offsets [3313, 10302, 11157, 17180, 18175], `trackingIndexScale` (AST id 1309) at offsets [5072, 11824], `baseTrackingSupplySpeed` (AST id 1313) at offsets [1772, 8308], `baseTrackingBorrowSpeed` (AST id 1317) at offsets [4610, 8188], `baseMinForRewards` (AST id 1321) at offsets [4490, 8046], `baseBorrowMin` (AST id 1325) at offsets [2721, 15134, 16028], `targetReserves` (AST id 1329) at offsets [2844, 6688], `decimals` (AST id 1333) at offsets [2783], `numAssets` (AST id 1337) at offsets [4865, 7501, 10357, 10878, 17114], `accrualDescaleFactor` (AST id 1340) at offsets [11863], `assetList` (AST id 1343) at offsets [6070, 7222]

## Opcode census (runtime)

| opcode | count |
|---|---|
| CALL | 4 |
| CALLCODE | 1 |
| CREATE2 | 2 |
| DELEGATECALL | 1 |
| EXTCODESIZE | 3 |
| GAS | 13 |
| INVALID | 1 |
| KECCAK256 | 17 |
| LOG1 | 1 |
| LOG2 | 1 |
| LOG3 | 6 |
| LOG4 | 2 |
| RETURN | 41 |
| RETURNDATACOPY | 4 |
| RETURNDATASIZE | 16 |
| REVERT | 33 |
| SIGNEXTEND | 29 |
| SLOAD | 86 |
| SSTORE | 19 |
| STATICCALL | 6 |
| STOP | 5 |
| TIMESTAMP | 2 |

## Dispatcher (runtime)

- callvalue guard: none before dispatch (per-function or payable)
- short-calldata check: JUMPI at pc 13 → pc 24

| compare pc | selector | signature | arm → pc | source function |
|---|---|---|---|---|
| 32 | 0x042e02cf | isLiquidatable(address) | 1384 | CometWithExtendedAssetList helper |
| 43 | 0x0902f1ac | getReserves() | 1375 | CometWithExtendedAssetList helper |
| 54 | 0x0bc47ad1 | isSupplyPaused() | 1366 | CometWithExtendedAssetList helper |
| 65 | 0x0c340a24 | governor() | 1357 | CometWithExtendedAssetList helper |
| 76 | 0x18160ddd | totalSupply() | 1348 | CometWithExtendedAssetList helper |
| 87 | 0x189bb2f1 | baseTrackingSupplySpeed() | 1339 | CometWithExtendedAssetList helper |
| 98 | 0x1c9f7fb9 | initializeStorage() | 1330 | CometWithExtendedAssetList helper |
| 109 | 0x1f5954bd | storeFrontPriceFactor() | 1321 | CometWithExtendedAssetList helper |
| 120 | 0x23b872dd | transferFrom(address,address,uint256) | 1312 | CometWithExtendedAssetList helper |
| 131 | 0x24a3d622 | pauseGuardian() | 1303 | CometWithExtendedAssetList helper |
| 142 | 0x26441318 | withdrawFrom(address,address,address,uint256) | 1294 | CometWithExtendedAssetList helper |
| 153 | 0x2a48cf12 | borrowPerSecondInterestRateSlopeHigh() | 1285 | CometWithExtendedAssetList helper |
| 164 | 0x2b92a07d | userCollateral(address,address) | 1276 | CometWithExtendedAssetList helper |
| 175 | 0x2d05670b | borrowPerSecondInterestRateSlopeLow() | 1267 | CometWithExtendedAssetList helper |
| 186 | 0x2e04b8e7 | userNonce(address) | 1258 | CometWithExtendedAssetList helper |
| 197 | 0x300e6beb | baseBorrowMin() | 1249 | CometWithExtendedAssetList helper |
| 208 | 0x313ce567 | decimals() | 1240 | CometWithExtendedAssetList helper |
| 219 | 0x32176c49 | targetReserves() | 1231 | CometWithExtendedAssetList helper |
| 230 | 0x374c49b4 | borrowBalanceOf(address) | 1222 | CometWithExtendedAssetList helper |
| 241 | 0x38aa813f | isBorrowCollateralized(address) | 1213 | CometWithExtendedAssetList helper |
| 252 | 0x3b3bec2e | getAssetInfoByAddress(address) | 1204 | CometWithExtendedAssetList helper |
| 263 | 0x41976e09 | getPrice(address) | 1195 | CometWithExtendedAssetList helper |
| 274 | 0x4232cd63 | supplyTo(address,address,uint256) | 1186 | CometWithExtendedAssetList helper |
| 285 | 0x439e2e45 | transferAsset(address,address,uint256) | 1177 | CometWithExtendedAssetList helper |
| 296 | 0x44c1e5eb | baseScale() | 1168 | CometWithExtendedAssetList helper |
| 307 | 0x44c35d07 | pause(bool,bool,bool,bool,bool) | 1159 | CometWithExtendedAssetList helper |
| 318 | 0x44ff241d | extensionDelegate() | 1150 | CometWithExtendedAssetList helper |
| 329 | 0x59e017bd | totalsCollateral(address) | 1141 | CometWithExtendedAssetList helper |
| 340 | 0x5a94b8d1 | supplyPerSecondInterestRateSlopeLow() | 1132 | CometWithExtendedAssetList helper |
| 351 | 0x67800b5f | isWithdrawPaused() | 1123 | CometWithExtendedAssetList helper |
| 362 | 0x70a08231 | balanceOf(address) | 1114 | CometWithExtendedAssetList helper |
| 373 | 0x7914acc7 | borrowPerSecondInterestRateBase() | 1105 | CometWithExtendedAssetList helper |
| 384 | 0x7ac88ed1 | quoteCollateral(address,uint256) | 1096 | CometWithExtendedAssetList helper |
| 395 | 0x7eb71131 | getUtilization() | 1087 | CometWithExtendedAssetList helper |
| 406 | 0x804de71f | supplyPerSecondInterestRateSlopeHigh() | 1078 | CometWithExtendedAssetList helper |
| 417 | 0x8285ef40 | totalBorrow() | 1069 | CometWithExtendedAssetList helper |
| 428 | 0x8d5d814c | isAbsorbPaused() | 1060 | CometWithExtendedAssetList helper |
| 439 | 0x90323177 | supplyFrom(address,address,address,uint256) | 1051 | CometWithExtendedAssetList helper |
| 450 | 0x9241a561 | borrowKink() | 1042 | CometWithExtendedAssetList helper |
| 461 | 0x9364e18a | baseMinForRewards() | 1033 | CometWithExtendedAssetList helper |
| 472 | 0x94920cca | supplyPerSecondInterestRateBase() | 1024 | CometWithExtendedAssetList helper |
| 483 | 0x9ea99a5a | baseTrackingBorrowSpeed() | 1015 | CometWithExtendedAssetList helper |
| 494 | 0x9fa83b5a | getBorrowRate(uint256) | 1006 | CometWithExtendedAssetList helper |
| 505 | 0x9ff567f8 | getCollateralReserves(address) | 997 | CometWithExtendedAssetList helper |
| 516 | 0xa1654379 | isAllowed(address,address) | 988 | CometWithExtendedAssetList helper |
| 527 | 0xa1a1ef43 | isTransferPaused() | 979 | CometWithExtendedAssetList helper |
| 538 | 0xa46fe83b | numAssets() | 970 | CometWithExtendedAssetList helper |
| 549 | 0xa5b4ff79 | supplyKink() | 961 | CometWithExtendedAssetList helper |
| 560 | 0xa9059cbb | transfer(address,uint256) | 952 | CometWithExtendedAssetList helper |
| 571 | 0xaba7f15e | trackingIndexScale() | 943 | CometWithExtendedAssetList helper |
| 582 | 0xad14777c | approveThis(address,address,uint256) | 934 | CometWithExtendedAssetList helper |
| 593 | 0xbfe69c8d | accrueAccount(address) | 925 | CometWithExtendedAssetList helper |
| 604 | 0xc1ee2c18 | transferAssetFrom(address,address,address,uint256) | 916 | CometWithExtendedAssetList helper |
| 615 | 0xc3b35a7e | withdrawTo(address,address,uint256) | 907 | CometWithExtendedAssetList helper |
| 626 | 0xc3cecfd2 | absorb(address,address[]) | 898 | CometWithExtendedAssetList helper |
| 637 | 0xc55dae63 | baseToken() | 889 | CometWithExtendedAssetList helper |
| 648 | 0xc5fa15cf | liquidatorPoints(address) | 880 | CometWithExtendedAssetList helper |
| 659 | 0xc8c7fe6b | getAssetInfo(uint8) | 871 | CometWithExtendedAssetList helper |
| 670 | 0xcde68041 | hasPermission(address,address) | 862 | CometWithExtendedAssetList helper |
| 681 | 0xd8e5f611 | isBuyPaused() | 853 | CometWithExtendedAssetList helper |
| 692 | 0xd955759d | getSupplyRate(uint256) | 844 | CometWithExtendedAssetList helper |
| 703 | 0xdc4abafd | userBasic(address) | 835 | CometWithExtendedAssetList helper |
| 714 | 0xe372f03a | assetList() | 826 | CometWithExtendedAssetList helper |
| 725 | 0xe478795d | withdrawReserves(address,uint256) | 817 | CometWithExtendedAssetList helper |
| 736 | 0xe4e6e779 | buyCollateral(address,uint256,uint256,address) | 808 | CometWithExtendedAssetList helper |
| 747 | 0xe7dad6bd | baseTokenPriceFeed() | 799 | CometWithExtendedAssetList helper |
| 758 | 0xf2b9fdb8 | supply(address,uint256) | 790 | CometWithExtendedAssetList helper |

ABI functions without a selector arm (served by the fallback, or not dispatched): `withdraw(address,uint256)`

Chain fallthroughs (after the last compare of each chain): pc 767 → falls into 777

## Jump destinations (runtime, 905)

14, 22, 24, 785, 790, 799, 808, 817, 826, 835, 844, 853, 862, 871, 880, 889, 898, 907, 916, 925, 934, 943, 952, 961, 970, 979, 988, 997, 1006, 1015, 1024, 1033, 1042, 1051, 1060, 1069, 1078, 1087, 1096, 1105, 1114, 1123, 1132, 1141, 1150, 1159, 1168, 1177, 1186, 1195, 1204, 1213, 1222, 1231, 1240, 1249, 1258, 1267, 1276, 1285, 1294, 1303, 1312, 1321, 1330, 1339, 1348, 1357, 1366, 1375, 1384, 1393, 1410, 1415, 1450, 1455, 1465, 1476, 1504, 1512, 1550, 1569, 1639, 1678, 1707, 1713, 1738, 1747, 1807, 1861, 1921, 1938, 1941, 2001, 2023, 2040, 2046, 2066, 2076, 2116, 2145, 2215, 2238, 2253, 2270, 2290, 2302, 2308, 2328, 2388, 2413, 2425, 2428, 2451, 2463, 2489, 2512, 2542, 2570, 2574, 2634, 2664, 2696, 2756, 2819, 2879, 2914, 2919, 2954, 2959, 2971, 3067, 3121, 3123, 3159, 3164, 3176, 3211, 3216, 3236, 3245, 3252, 3272, 3281, 3288, 3348, 3361, 3389, 3399, 3409, 3420, 3431, 3483, 3543, 3557, 3571, 3586, 3601, 3616, 3624, 3677, 3682, 3699, 3744, 3814, 3844, 3900, 3960, 3999, 4034, 4039, 4099, 4134, 4143, 4171, 4231, 4270, 4299, 4328, 4367, 4387, 4399, 4405, 4465, 4525, 4585, 4645, 4676, 4694, 4729, 4734, 4758, 4787, 4799, 4838, 4901, 4961, 4994, 5002, 5047, 5107, 5124, 5221, 5232, 5238, 5253, 5259, 5267, 5272, 5305, 5313, 5353, 5416, 5427, 5447, 5459, 5465, 5485, 5494, 5501, 5531, 5602, 5672, 5702, 5782, 5793, 5829, 5834, 5856, 5862, 5901, 5932, 5962, 6047, 6117, 6147, 6208, 6220, 6302, 6316, 6334, 6344, 6352, 6382, 6395, 6403, 6424, 6436, 6486, 6497, 6516, 6575, 6580, 6587, 6622, 6648, 6666, 6684, 6727, 6745, 6815, 6848, 6856, 6868, 6901, 6909, 6921, 6950, 6977, 6982, 7017, 7039, 7055, 7104, 7115, 7126, 7146, 7166, 7179, 7187, 7272, 7284, 7297, 7307, 7335, 7344, 7358, 7375, 7392, 7409, 7426, 7443, 7454, 7462, 7469, 7477, 7482, 7491, 7535, 7562, 7571, 7605, 7614, 7637, 7655, 7670, 7730, 7753, 7775, 7783, 7787, 7799, 7818, 7826, 7830, 7859, 7867, 7871, 7886, 7894, 7920, 7926, 7936, 7946, 7962, 8033, 8044, 8097, 8112, 8117, 8126, 8169, 8224, 8229, 8234, 8244, 8249, 8281, 8289, 8344, 8363, 8401, 8407, 8427, 8445, 8476, 8482, 8520, 8527, 8534, 8559, 8565, 8571, 8577, 8583, 8591, 8603, 8614, 8712, 8751, 8818, 8827, 8866, 8873, 8881, 8886, 8984, 9023, 9090, 9099, 9138, 9146, 9151, 9174, 9184, 9192, 9196, 9246, 9262, 9275, 9305, 9313, 9318, 9355, 9375, 9418, 9426, 9439, 9457, 9469, 9482, 9500, 9518, 9525, 9533, 9541, 9546, 9561, 9607, 9615, 9652, 9668, 9678, 9686, 9693, 9700, 9708, 9713, 9734, 9755, 9763, 9768, 9793, 9812, 9820, 9825, 9836, 9866, 9871, 9903, 9957, 9965, 10022, 10035, 10042, 10048, 10054, 10060, 10103, 10116, 10124, 10129, 10146, 10164, 10178, 10185, 10214, 10225, 10246, 10253, 10259, 10300, 10348, 10391, 10411, 10422, 10427, 10437, 10490, 10498, 10518, 10531, 10554, 10567, 10579, 10587, 10592, 10598, 10603, 10612, 10625, 10633, 10652, 10658, 10666, 10671, 10688, 10746, 10752, 10785, 10800, 10805, 10819, 10848, 10869, 10912, 10931, 10942, 10947, 10957, 11010, 11033, 11046, 11059, 11068, 11078, 11083, 11118, 11132, 11151, 11194, 11204, 11226, 11237, 11268, 11294, 11312, 11323, 11345, 11361, 11369, 11373, 11381, 11386, 11394, 11399, 11407, 11412, 11420, 11425, 11433, 11438, 11456, 11487, 11504, 11523, 11547, 11578, 11692, 11701, 11720, 11793, 11801, 11807, 11822, 11861, 11900, 11918, 11931, 11957, 11973, 11980, 11985, 11998, 12003, 12051, 12057, 12062, 12067, 12096, 12100, 12181, 12187, 12201, 12207, 12227, 12245, 12275, 12293, 12322, 12353, 12377, 12418, 12465, 12473, 12490, 12495, 12522, 12531, 12536, 12543, 12563, 12568, 12575, 12586, 12591, 12598, 12604, 12682, 12716, 12721, 12737, 12742, 12775, 12780, 12813, 12844, 12850, 12859, 12866, 12873, 12878, 12886, 12891, 12899, 12904, 12912, 12917, 12947, 12964, 12971, 12979, 12984, 12992, 12997, 13017, 13035, 13064, 13082, 13114, 13135, 13143, 13148, 13184, 13199, 13216, 13234, 13243, 13259, 13272, 13319, 13332, 13340, 13409, 13414, 13434, 13443, 13476, 13488, 13496, 13503, 13525, 13532, 13540, 13545, 13563, 13572, 13587, 13593, 13601, 13606, 13630, 13637, 13645, 13650, 13665, 13689, 13718, 13749, 13773, 13801, 13820, 13846, 13851, 13861, 13876, 13881, 13899, 13904, 13917, 13927, 13944, 14028, 14033, 14040, 14054, 14059, 14066, 14071, 14077, 14109, 14114, 14132, 14155, 14174, 14209, 14224, 14232, 14249, 14256, 14270, 14290, 14302, 14314, 14321, 14329, 14339, 14379, 14387, 14404, 14411, 14425, 14448, 14455, 14467, 14474, 14485, 14496, 14526, 14620, 14626, 14640, 14646, 14664, 14675, 14686, 14695, 14706, 14715, 14728, 14741, 14751, 14760, 14769, 14779, 14789, 14798, 14808, 14818, 14830, 14841, 14856, 14866, 14876, 14887, 14899, 14909, 14919, 14930, 14940, 14950, 14959, 14977, 14989, 15023, 15051, 15085, 15113, 15123, 15132, 15182, 15192, 15210, 15228, 15263, 15280, 15289, 15305, 15329, 15382, 15413, 15425, 15435, 15449, 15459, 15469, 15482, 15492, 15502, 15511, 15523, 15532, 15541, 15597, 15627, 15708, 15714, 15728, 15734, 15748, 15762, 15776, 15788, 15797, 15813, 15820, 15841, 15852, 15861, 15905, 15983, 16017, 16026, 16076, 16086, 16113, 16171, 16182, 16187, 16208, 16216, 16223, 16241, 16252, 16261, 16268, 16276, 16281, 16335, 16347, 16380, 16389, 16411, 16421, 16430, 16441, 16450, 16502, 16519, 16535, 16557, 16567, 16582, 16642, 16664, 16692, 16695, 16733, 16753, 16758, 16779, 16784, 16794, 16812, 16819, 16837, 16850, 16857, 16942, 16961, 16966, 16972, 16978, 16991, 17009, 17021, 17031, 17047, 17062, 17104, 17110, 17219, 17224, 17230, 17240, 17249, 17261, 17272, 17283, 17295, 17306, 17315, 17327, 17337, 17348, 17360, 17370, 17381, 17390, 17399, 17410, 17493, 17530, 17536, 17542, 17551, 17562, 17567, 17578, 17589, 17620, 17630, 17650, 17660, 17671, 17682, 17694, 17704, 17713, 17736, 17750, 17769, 17783, 17792, 17802, 17811, 17895, 17913, 17936, 17954, 17965, 17981, 18010, 18054, 18095, 18104, 18112, 18155, 18165, 18173, 18213, 18221, 18226, 18234, 18239, 18247, 18252, 18263, 18287, 18340, 18346, 18357, 18413, 18418, 18477

> source map covers 10407 of 10434 runtime instructions (the tail from pc 18481 is unmapped)

## Source functions → runtime pcs

| function | kind | pcs | first JUMPDEST | blocks |
|---|---|---|---|---|
| CometWithExtendedAssetList helper | helper | 0–18388 (5284) | 22 | 0, 22, 24, 42, 53, 64, 75, 86, 97, 108, 119, 130, 141, 152, 163, 174, 185, 196, 207, 218, 229, 240, 251, 262, 273, 284, 295, 306, 317, 328, 339, 350, 361, 372, 383, 394, 405, 416, 427, 438, 449, 460, 471, 482, 493, 504, 515, 526, 537, 548, 559, 570, 581, 592, 603, 614, 625, 636, 647, 658, 669, 680, 691, 702, 713, 724, 735, 746, 757, 768, 778, 785, 790, 799, 808, 817, 826, 835, 844, 853, 862, 871, 880, 889, 898, 907, 916, 925, 934, 943, 952, 961, 970, 979, 988, 997, 1006, 1015, 1024, 1033, 1042, 1051, 1060, 1069, 1078, 1087, 1096, 1105, 1114, 1123, 1132, 1141, 1150, 1159, 1168, 1177, 1186, 1195, 1204, 1213, 1222, 1231, 1240, 1249, 1258, 1267, 1276, 1285, 1294, 1303, 1312, 1321, 1330, 1339, 1348, 1357, 1366, 1375, 1384, 1393, 1409, 1410, 1415, 1422, 1434, 1450, 1455, 1465, 1475, 1476, 1483, 1495, 1504, 1512, 1519, 1531, 1550, 1569, 1576, 1588, 1639, 1646, 1658, 1747, 1754, 1766, 1807, 1814, 1938, 1941, 1948, 1960, 2001, 2013, 2023, 2040, 2046, 2066, 2145, 2152, 2164, 2215, 2228, 2238, 2253, 2270, 2290, 2328, 2335, 2347, 2388, 2401, 2413, 2425, 2428, 2451, 2463, 2489, 2496, 2512, 2570, 2574, 2581, 2593, 2634, 2641, 2653, 2664, 2696, 2703, 2715, 2756, 2763, 2775, 2819, 2826, 2838, 2879, 2886, 2898, 2914, 2919, 2926, 2938, 2954, 2959, 2971, 3067, 3121, 3123, 3130, 3142, 3159, 3164, 3176, 3183, 3195, 3211, 3216, 3236, 3252, 3272, 3288, 3295, 3307, 3348, 3360, 3361, 3368, 3380, 3389, 3399, 3409, 3420, 3431, 3483, 3744, 3751, 3763, 3814, 3821, 3833, 3844, 3900, 3907, 3919, 3960, 3967, 3979, 3999, 4006, 4018, 4034, 4039, 4046, 4058, 4099, 4106, 4118, 4134, 4143, 4150, 4162, 4171, 4178, 4190, 4231, 4238, 4250, 4328, 4335, 4347, 4367, 4387, 4405, 4412, 4424, 4465, 4472, 4484, 4525, 4532, 4544, 4585, 4592, 4604, 4645, 4652, 4664, 4676, 4694, 4701, 4713, 4729, 4734, 4741, 4758, 4799, 4806, 4818, 4838, 4845, 4857, 4901, 4908, 4920, 4961, 4968, 4994, 5047, 5054, 5066, 5107, 5114, 5124, 5177, 5232, 5237, 5272, 5279, 5305, 5353, 5416, 5427, 5447, 5465, 5485, 5501, 5508, 5520, 5531, 5552, 5563, 5575, 5590, 5602, 5609, 5621, 5672, 5679, 5691, 5702, 5782, 5792, 5793, 5800, 5812, 5829, 5834, 5841, 5856, 5862, 5869, 5881, 5901, 5908, 5920, 5932, 5939, 5951, 5962, 6047, 6054, 6066, 6117, 6124, 6136, 6147, 6220, 6352, 6359, 6371, 6382, 6395, 6436, 6745, 6752, 6764, 6815, 6822, 6848, 6868, 6875, 6901, 6982, 7017, 7039, 7055, 7104, 7115, 7126, 7145, 7146, 7165, 7166, 7187, 7316, 7335, 7344, 7358, 7375, 7392, 7409, 7426, 7443, 7454, 7491, 7545, 7627, 7655, 7670, 7730, 7753, 7772, 7775, 7783, 7787, 7799, 7815, 7818, 7826, 7830, 7856, 7859, 7867, 7871, 7920, 8044, 8112, 8244, 8424, 8591, 8600, 8603, 8611, 8873, 8881, 9138, 9146, 9301, 9305, 9313, 9355, 9374, 9491, 9500, 9518, 9546, 9558, 9649, 9713, 9734, 9752, 9755, 9763, 9768, 9793, 9809, 9812, 9820, 10447, 10567, 10587, 10633, 10652, 10658, 10666, 10671, 10683, 10967, 11046, 11358, 11361, 11369, 11373, 11381, 11386, 11394, 11399, 11407, 11412, 11420, 11425, 11433, 11438, 11453, 11523, 11544, 11547, 11578, 11692, 11720, 11793, 11801, 11940, 11957, 12224, 12293, 12319, 12322, 12353, 12374, 12377, 12495, 12563, 12586, 12716, 12891, 12899, 12904, 12912, 12984, 12992, 13014, 13059, 13082, 13114, 13132, 13135, 13143, 13349, 13430, 13449, 13650, 13665, 13689, 13715, 13718, 13749, 13773, 13801, 13881, 13899, 13927, 14059, 14161, 14174, 14188, 14209, 14249, 14314, 14355, 14404, 14467, 14695, 14715, 14728, 14741, 14856, 14899, 15305, 15326, 15762, 15776, 16086, 16519, 16529, 16535, 16557, 16567, 16582, 16642, 16661, 16758, 16779, 16996, 17009, 17021, 17047, 17062, 17327, 17360, 17530, 17694, 17750, 17783, 18226, 18234, 18239, 18247 |
| CometWithExtendedAssetList.isSupplyPaused | function | 1533–12079 (4) |  |  |
| CometMath.toBool | function | 1541–5893 (10) |  |  |
| CometWithExtendedAssetList.governor | getter | 1591–1591 (1) |  |  |
| CometCore helper | helper | 1660–18225 (312) | 9151 | 7013, 9151, 9174, 9181, 9184, 9192, 11083, 11223, 11473, 12270, 12878, 12886, 12971, 12979, 17156, 18213, 18221 |
| CometCore.presentValueSupply | function | 1668–10746 (35) | 1738 | 1738, 9246, 9262, 9318, 10022, 10035, 10746 |
| CometWithExtendedAssetList.totalSupply | function | 1671–1713 (14) | 1678 | 1678, 1707, 1713 |
| CometWithExtendedAssetList.baseTrackingSupplySpeed | getter | 1771–1771 (1) |  |  |
| CometWithExtendedAssetList.initializeStorage | function | 1827–1937 (12) | 1861 | 1827, 1861, 1921 |
| CometWithExtendedAssetList.storeFrontPriceFactor | getter | 1965–1965 (1) |  |  |
| CometWithExtendedAssetList.nonReentrant | modifier | 2053–6920 (94) | 2076 | 2053, 2076, 2116, 2277, 2302, 2308, 3223, 3245, 3259, 3281, 4374, 4399, 4980, 5002, 5434, 5459, 5472, 5494, 6403, 6834, 6856, 6887, 6909 |
| CometWithExtendedAssetList.transferFrom | function | 2077–2140 (4) |  |  |
| CometWithExtendedAssetList.nonReentrantAfter | function | 2134–6647 (4) |  |  |
| CometWithExtendedAssetList.pauseGuardian | getter | 2167–2167 (1) |  |  |
| CometWithExtendedAssetList.withdrawFrom | function | 2303–2303 (1) |  |  |
| CometWithExtendedAssetList.borrowPerSecondInterestRateSlopeHigh | getter | 2352–2352 (1) |  |  |
| CometStorage.userCollateral | getter | 2499–2542 (5) | 2542 | 2542 |
| CometWithExtendedAssetList.borrowPerSecondInterestRateSlopeLow | getter | 2598–2598 (1) |  |  |
| CometWithExtendedAssetList.baseBorrowMin | getter | 2720–2720 (1) |  |  |
| CometWithExtendedAssetList.decimals | getter | 2782–2782 (1) |  |  |
| CometWithExtendedAssetList.targetReserves | getter | 2843–2843 (1) |  |  |
| CometWithExtendedAssetList.supplyTo | function | 3246–3247 (2) |  |  |
| CometWithExtendedAssetList.transferAsset | function | 3282–3283 (2) |  |  |
| CometWithExtendedAssetList.baseScale | getter | 3312–3312 (1) |  |  |
| CometWithExtendedAssetList.pause | function | 3439–3743 (77) | 3543 | 3489, 3543, 3557, 3571, 3586, 3601, 3616, 3624, 3677, 3682, 3699 |
| CometWithExtendedAssetList.extensionDelegate | getter | 3766–3766 (1) |  |  |
| CometStorage.totalsCollateral | getter | 3859–3859 (1) |  |  |
| CometWithExtendedAssetList.supplyPerSecondInterestRateSlopeLow | getter | 3924–3924 (1) |  |  |
| CometWithExtendedAssetList.isWithdrawPaused | function | 3983–15610 (4) |  |  |
| CometWithExtendedAssetList.borrowPerSecondInterestRateBase | getter | 4063–4063 (1) |  |  |
| CometWithExtendedAssetList.supplyPerSecondInterestRateSlopeHigh | getter | 4195–4195 (1) |  |  |
| CometWithExtendedAssetList.totalBorrow | function | 4263–4299 (11) | 4270 | 4270, 4299 |
| CometWithExtendedAssetList.isAbsorbPaused | function | 4351–16678 (4) |  |  |
| CometWithExtendedAssetList.supplyFrom | function | 4400–4400 (1) |  |  |
| CometWithExtendedAssetList.borrowKink | getter | 4429–4429 (1) |  |  |
| CometWithExtendedAssetList.baseMinForRewards | getter | 4489–4489 (1) |  |  |
| CometWithExtendedAssetList.supplyPerSecondInterestRateBase | getter | 4549–4549 (1) |  |  |
| CometWithExtendedAssetList.baseTrackingBorrowSpeed | getter | 4609–4609 (1) |  |  |
| CometStorage.isAllowed | getter | 4745–4787 (6) | 4787 | 4787 |
| CometWithExtendedAssetList.isTransferPaused | function | 4822–14509 (4) |  |  |
| CometWithExtendedAssetList.numAssets | getter | 4864–4864 (1) |  |  |
| CometWithExtendedAssetList.supplyKink | getter | 4925–4925 (1) |  |  |
| CometWithExtendedAssetList.transfer | function | 5006–5042 (5) |  |  |
| CometWithExtendedAssetList.trackingIndexScale | getter | 5071–5071 (1) |  |  |
| CometWithExtendedAssetList.approveThis | function | 5136–5271 (49) | 5221 | 5186, 5221, 5238, 5253, 5259, 5267 |
| CometWithExtendedAssetList.accrueAccount | function | 5291–5426 (9) | 5313 | 5291, 5313 |
| CometWithExtendedAssetList.transferAssetFrom | function | 5460–5460 (1) |  |  |
| CometWithExtendedAssetList.withdrawTo | function | 5495–5496 (2) |  |  |
| CometWithExtendedAssetList.baseToken | getter | 5624–5624 (1) |  |  |
| CometStorage.liquidatorPoints | getter | 5714–5714 (1) |  |  |
| CometWithExtendedAssetList.isBuyPaused | function | 5885–6412 (4) |  |  |
| CometStorage.userBasic | getter | 5974–5974 (1) |  |  |
| CometWithExtendedAssetList.assetList | getter | 6069–6069 (1) |  |  |
| CometWithExtendedAssetList.withdrawReserves | function | 6160–6351 (45) | 6208 | 6201, 6208, 6226, 6302, 6316, 6334, 6344 |
| CometWithExtendedAssetList.buyCollateral | function | 6413–6744 (87) | 6424 | 6417, 6424, 6442, 6486, 6497, 6508, 6516, 6523, 6575, 6580, 6587, 6622, 6648, 6666, 6684, 6727 |
| CometWithExtendedAssetList.baseTokenPriceFeed | getter | 6767–6767 (1) |  |  |
| CometWithExtendedAssetList.supply | function | 6860–6863 (4) |  |  |
| CometWithExtendedAssetList.withdraw | function | 6913–6916 (4) |  |  |
| CometCore.hasPermission | function | 6921–6981 (22) | 6921 | 6921, 6946, 6950, 6977 |
| CometWithExtendedAssetList.getAssetInfo | function | 7179–7481 (58) | 7179 | 7179, 7272, 7280, 7284, 7297, 7307, 7462, 7469, 7477 |
| CometWithExtendedAssetList.getAssetInfoByAddress | function | 7482–7613 (40) | 7482 | 7482, 7535, 7562, 7571, 7605 |
| CometWithExtendedAssetList.getNowInternal | function | 7614–7654 (15) | 7614 | 7614, 7637 |
| CometWithExtendedAssetList.accrueInternal | function | 7886–8406 (105) | 7886 | 7886, 7894, 7926, 7936, 7943, 7946, 7962, 8033, 8097, 8117, 8126, 8169, 8224, 8229, 8234, 8249, 8281, 8289, 8344, 8363, 8401 |
| CometMath.safe64 | function | 8407–8444 (14) | 8407 | 8407, 8427 |
| CometWithExtendedAssetList.accruedInterestIndices | function | 8445–8590 (62) | 8445 | 8445, 8476, 8482, 8520, 8527, 8534, 8559, 8571, 8577, 8583 |
| CometWithExtendedAssetList.mulFactor | function | 8484–18112 (43) | 8565 | 8565, 8712, 8866, 8984, 11132, 18095, 18112 |
| CometWithExtendedAssetList.getSupplyRate | function | 8614–8872 (29) | 8614 | 8614, 8655, 8751, 8818, 8827 |
| CometWithExtendedAssetList.getBorrowRate | function | 8886–9101 (26) | 8886 | 8886, 8927, 9023, 9090, 9099 |
| CometWithExtendedAssetList.getUtilization | function | 9196–9317 (15) | 9196 | 9196, 9269, 9275 |
| CometWithExtendedAssetList.getPrice | function | 9375–9545 (70) | 9375 | 9375, 9418, 9426, 9437, 9439, 9457, 9469, 9482, 9525, 9533, 9541 |
| CometWithExtendedAssetList.getCollateralReserves | function | 9561–9712 (64) | 9561 | 9561, 9607, 9615, 9652, 9668, 9678, 9686, 9693, 9700, 9708 |
| CometWithExtendedAssetList.getReserves | function | 9825–10128 (104) | 9825 | 9825, 9836, 9866, 9871, 9903, 9957, 9965, 10042, 10048, 10054, 10060, 10094, 10103, 10116, 10124 |
| CometMath.signed256 | function | 10129–10163 (13) | 10129 | 10129, 10144, 10146 |
| CometWithExtendedAssetList.isBorrowCollateralized | function | 10164–10632 (165) | 10164 | 10164, 10178, 10185, 10201, 10214, 10225, 10246, 10253, 10259, 10300, 10348, 10391, 10401, 10411, 10422, 10427, 10437, 10490, 10498, 10518, 10531, 10554, 10579, 10592, 10598, 10603, 10612, 10625 |
| CometCore.presentValue | function | 10688–10804 (25) | 10688 | 10688, 10701, 10752, 10785, 10800 |
| CometWithExtendedAssetList.isLiquidatable | function | 10805–11082 (121) | 10805 | 10805, 10819, 10835, 10848, 10869, 10912, 10922, 10931, 10942, 10947, 10957, 11010, 11033, 11059, 11068, 11078 |
| CometMath.toUInt8 | function | 11118–11131 (8) | 11118 | 11118, 11127 |
| CometWithExtendedAssetList.divBaseWei | function | 11151–11193 (7) | 11151 | 11151 |
| CometWithExtendedAssetList.mulPrice | function | 11194–11225 (9) | 11194 | 11194, 11204 |
| CometWithExtendedAssetList.signedMulPrice | function | 11226–11372 (17) | 11226 | 11226, 11237, 11268, 11294, 11312, 11323, 11345 |
| CometWithExtendedAssetList.isInAsset | function | 11456–11522 (38) | 11456 | 11456, 11487, 11498, 11504 |
| CometWithExtendedAssetList.updateBasePrincipal | function | 11701–12066 (86) | 11701 | 11701, 11746, 11807, 11822, 11861, 11900, 11918, 11931, 11973, 11980, 11985, 11998, 12003, 12051, 12057, 12062 |
| CometWithExtendedAssetList.supplyInternal | function | 12067–12206 (49) | 12067 | 12067, 12084, 12096, 12100, 12171, 12181, 12187, 12201 |
| CometMath.safe128 | function | 12207–12244 (14) | 12207 | 12207, 12227 |
| CometWithExtendedAssetList.nonReentrantBefore | function | 12245–12292 (15) | 12245 | 12245, 12275 |
| CometWithExtendedAssetList.supplyBase | function | 12418–12741 (85) | 12418 | 12418, 12465, 12473, 12490, 12522, 12531, 12536, 12543, 12568, 12575, 12591, 12598, 12604, 12679, 12682, 12721, 12737 |
| CometCore.principalValue | function | 12742–12877 (31) | 12742 | 12742, 12751, 12775, 12780, 12813, 12844, 12859, 12866, 12873 |
| CometCore.principalValueBorrow | function | 12784–12872 (7) | 12850 | 12850 |
| CometCore.principalValueSupply | function | 12917–12970 (8) | 12917 | 12917, 12947, 12964 |
| CometMath.safe104 | function | 12997–13034 (14) | 12997 | 12997, 13017 |
| CometMath.signed104 | function | 13035–13081 (13) | 13035 | 13035, 13064 |
| CometWithExtendedAssetList.repayAndSupplyAmount | function | 13148–13271 (53) | 13148 | 13148, 13167, 13174, 13184, 13199, 13207, 13216, 13234, 13243, 13259 |
| CometWithExtendedAssetList.doTransferIn | function | 13272–13649 (185) | 13272 | 13272, 13319, 13332, 13340, 13409, 13414, 13423, 13434, 13443, 13476, 13488, 13496, 13503, 13516, 13525, 13532, 13540, 13545, 13563, 13572, 13587, 13593, 13601, 13606, 13621, 13630, 13637, 13645 |
| CometWithExtendedAssetList.supplyCollateral | function | 13820–14131 (104) | 13820 | 13820, 13846, 13851, 13861, 13876, 13904, 13917, 13944, 13952, 14028, 14033, 14040, 14054, 14066, 14071, 14077, 14109, 14114 |
| CometWithExtendedAssetList.updateAssetsIn | function | 14132–14495 (129) | 14132 | 14132, 14155, 14224, 14232, 14256, 14267, 14270, 14290, 14302, 14321, 14329, 14336, 14339, 14379, 14387, 14411, 14422, 14425, 14448, 14455, 14474, 14485 |
| CometWithExtendedAssetList.transferInternal | function | 14496–14663 (57) | 14496 | 14496, 14514, 14526, 14550, 14610, 14620, 14626, 14640, 14646 |
| CometWithExtendedAssetList.transferBase | function | 14664–15227 (191) | 14664 | 14664, 14675, 14686, 14706, 14751, 14760, 14769, 14779, 14789, 14798, 14808, 14818, 14830, 14841, 14866, 14876, 14887, 14909, 14919, 14930, 14940, 14950, 14959, 14977, 14986, 14989, 15023, 15051, 15085, 15113, 15123, 15132, 15171, 15182, 15187, 15192, 15210 |
| CometWithExtendedAssetList.withdrawAndBorrowAmount | function | 15228–15304 (33) | 15228 | 15228, 15246, 15253, 15263, 15271, 15280, 15289 |
| CometWithExtendedAssetList.transferCollateral | function | 15329–15596 (105) | 15329 | 15329, 15382, 15413, 15425, 15435, 15449, 15459, 15469, 15482, 15492, 15502, 15511, 15523, 15532, 15541, 15547 |
| CometWithExtendedAssetList.withdrawInternal | function | 15597–15733 (46) | 15597 | 15597, 15615, 15627, 15698, 15708, 15714, 15728 |
| CometWithExtendedAssetList.withdrawBase | function | 15734–16085 (89) | 15734 | 15734, 15748, 15788, 15797, 15813, 15820, 15841, 15852, 15861, 15905, 15980, 15983, 16017, 16026, 16065, 16076, 16081 |
| CometWithExtendedAssetList.doTransferOut | function | 16113–16280 (84) | 16113 | 16113, 16132, 16171, 16182, 16187, 16198, 16205, 16208, 16216, 16222, 16223, 16241, 16252, 16261, 16268, 16276 |
| CometWithExtendedAssetList.withdrawCollateral | function | 16281–16518 (74) | 16281 | 16281, 16335, 16347, 16380, 16389, 16411, 16421, 16430, 16441, 16450, 16456, 16502 |
| CometWithExtendedAssetList.absorb | function | 16664–16977 (91) | 16664 | 16664, 16683, 16692, 16695, 16703, 16733, 16753, 16784, 16794, 16812, 16819, 16837, 16850, 16857, 16942, 16961, 16966, 16972 |
| CometWithExtendedAssetList.absorbInternal | function | 16978–17912 (282) | 16978 | 16978, 16991, 17031, 17104, 17110, 17224, 17230, 17240, 17249, 17261, 17272, 17283, 17295, 17306, 17315, 17337, 17348, 17370, 17381, 17390, 17399, 17410, 17490, 17493, 17536, 17542, 17551, 17562, 17567, 17578, 17589, 17620, 17630, 17650, 17660, 17671, 17682, 17704, 17713, 17736, 17769, 17792, 17802, 17811, 17895 |
| CometWithExtendedAssetList.divPrice | function | 17165–17223 (9) | 17219 | 17219 |
| CometMath.unsigned104 | function | 17913–17953 (12) | 17913 | 17913, 17936 |
| CometMath.unsigned256 | function | 17954–17964 (8) | 17954 | 17954, 17963 |
| CometWithExtendedAssetList.quoteCollateral | function | 17965–18212 (42) | 17965 | 17965, 17981, 18010, 18054, 18104, 18155, 18165, 18173 |
| CometWithExtendedAssetList.balanceOf | function | 18252–18345 (28) | 18252 | 18252, 18263, 18287, 18328, 18340 |
| CometWithExtendedAssetList.borrowBalanceOf | function | 18346–18417 (20) | 18346 | 18346, 18357, 18398, 18413 |
| CometWithExtendedAssetList.fallback | fallback | 18418–18480 (28) | 18418 | 18418, 18474, 18477 |

## Internal routines (source-map jump tags)

- `i`-tagged call jumps: 549; `o`-tagged return jumps: 104

| callee entry pc | function at entry | call sites (jump pc ← caller function) |
|---|---|---|
| 1393 | CometWithExtendedAssetList helper | 1449 ← CometWithExtendedAssetList helper, 2022 ← CometWithExtendedAssetList helper, 2039 ← CometWithExtendedAssetList helper, 2237 ← CometWithExtendedAssetList helper, 2252 ← CometWithExtendedAssetList helper, 2269 ← CometWithExtendedAssetList helper, 2412 ← CometWithExtendedAssetList helper, 2424 ← CometWithExtendedAssetList helper, 2663 ← CometWithExtendedAssetList helper, 2913 ← CometWithExtendedAssetList helper, 2953 ← CometWithExtendedAssetList helper, 3158 ← CometWithExtendedAssetList helper, 3210 ← CometWithExtendedAssetList helper, 3843 ← CometWithExtendedAssetList helper, 4033 ← CometWithExtendedAssetList helper, 4133 ← CometWithExtendedAssetList helper, 4728 ← CometWithExtendedAssetList helper, 4993 ← CometWithExtendedAssetList helper, 5304 ← CometWithExtendedAssetList helper, 5530 ← CometWithExtendedAssetList helper, 5701 ← CometWithExtendedAssetList helper, 5961 ← CometWithExtendedAssetList helper, 6146 ← CometWithExtendedAssetList helper, 6381 ← CometWithExtendedAssetList helper, 6394 ← CometWithExtendedAssetList helper, 6847 ← CometWithExtendedAssetList helper, 6900 ← CometWithExtendedAssetList helper, 7125 ← CometWithExtendedAssetList helper, 16566 ← CometWithExtendedAssetList helper |
| 1415 | CometWithExtendedAssetList helper | 1392 ← CometWithExtendedAssetList helper |
| 1465 | CometWithExtendedAssetList helper | 5258 ← CometWithExtendedAssetList.approveThis |
| 1476 | CometWithExtendedAssetList helper | 1383 ← CometWithExtendedAssetList helper |
| 1512 | CometWithExtendedAssetList helper | 1374 ← CometWithExtendedAssetList helper |
| 1550 | CometWithExtendedAssetList helper | 9902 ← CometWithExtendedAssetList.getReserves, 13318 ← CometWithExtendedAssetList.doTransferIn, 13475 ← CometWithExtendedAssetList.doTransferIn |
| 1569 | CometWithExtendedAssetList helper | 1365 ← CometWithExtendedAssetList helper |
| 1639 | CometWithExtendedAssetList helper | 1356 ← CometWithExtendedAssetList helper |
| 1747 | CometWithExtendedAssetList helper | 1347 ← CometWithExtendedAssetList helper |
| 1807 | CometWithExtendedAssetList helper | 1338 ← CometWithExtendedAssetList helper |
| 1941 | CometWithExtendedAssetList helper | 1329 ← CometWithExtendedAssetList helper |
| 2001 | CometWithExtendedAssetList helper | 2065 ← CometWithExtendedAssetList helper, 3235 ← CometWithExtendedAssetList helper, 3271 ← CometWithExtendedAssetList helper, 5123 ← CometWithExtendedAssetList helper, 5484 ← CometWithExtendedAssetList helper |
| 2046 | CometWithExtendedAssetList helper | 1320 ← CometWithExtendedAssetList helper |
| 2145 | CometWithExtendedAssetList helper | 1311 ← CometWithExtendedAssetList helper |
| 2215 | CometWithExtendedAssetList helper | 2289 ← CometWithExtendedAssetList helper, 4386 ← CometWithExtendedAssetList helper, 5446 ← CometWithExtendedAssetList helper |
| 2270 | CometWithExtendedAssetList helper | 1302 ← CometWithExtendedAssetList helper |
| 2328 | CometWithExtendedAssetList helper | 1293 ← CometWithExtendedAssetList helper |
| 2388 | CometWithExtendedAssetList helper | 2511 ← CometWithExtendedAssetList helper, 4757 ← CometWithExtendedAssetList helper, 5855 ← CometWithExtendedAssetList helper |
| 2428 | CometWithExtendedAssetList helper | 2541 ← CometStorage.userCollateral, 4786 ← CometStorage.isAllowed, 6976 ← CometCore.hasPermission, 10177 ← CometWithExtendedAssetList.isBorrowCollateralized, 10213 ← CometWithExtendedAssetList.isBorrowCollateralized, 10245 ← CometWithExtendedAssetList.isBorrowCollateralized, 10497 ← CometWithExtendedAssetList.isBorrowCollateralized, 10517 ← CometWithExtendedAssetList.isBorrowCollateralized, 10818 ← CometWithExtendedAssetList.isLiquidatable, 10847 ← CometWithExtendedAssetList.isLiquidatable, 10868 ← CometWithExtendedAssetList.isLiquidatable, 11979 ← CometWithExtendedAssetList.updateBasePrincipal, 12489 ← CometWithExtendedAssetList.supplyBase, 13875 ← CometWithExtendedAssetList.supplyCollateral, 14027 ← CometWithExtendedAssetList.supplyCollateral, 14032 ← CometWithExtendedAssetList.supplyCollateral, 14053 ← CometWithExtendedAssetList.supplyCollateral, 14065 ← CometWithExtendedAssetList.supplyCollateral, 14231 ← CometWithExtendedAssetList.updateAssetsIn, 14685 ← CometWithExtendedAssetList.transferBase, 14705 ← CometWithExtendedAssetList.transferBase, 15381 ← CometWithExtendedAssetList.transferCollateral, 15412 ← CometWithExtendedAssetList.transferCollateral, 15448 ← CometWithExtendedAssetList.transferCollateral, 15458 ← CometWithExtendedAssetList.transferCollateral, 15481 ← CometWithExtendedAssetList.transferCollateral, 15491 ← CometWithExtendedAssetList.transferCollateral, 15761 ← CometWithExtendedAssetList.withdrawBase, 16334 ← CometWithExtendedAssetList.withdrawCollateral, 16410 ← CometWithExtendedAssetList.withdrawCollateral, 16752 ← CometWithExtendedAssetList.absorb, 16856 ← CometWithExtendedAssetList.absorb, 17008 ← CometWithExtendedAssetList.absorbInternal, 17271 ← CometWithExtendedAssetList.absorbInternal, 17294 ← CometWithExtendedAssetList.absorbInternal, 17619 ← CometWithExtendedAssetList.absorbInternal, 17629 ← CometWithExtendedAssetList.absorbInternal, 17649 ← CometWithExtendedAssetList.absorbInternal, 17659 ← CometWithExtendedAssetList.absorbInternal, 17681 ← CometWithExtendedAssetList.absorbInternal |
| 2451 | CometWithExtendedAssetList helper | 6579 ← CometWithExtendedAssetList.buyCollateral, 13898 ← CometWithExtendedAssetList helper, 13926 ← CometWithExtendedAssetList helper, 13943 ← CometWithExtendedAssetList helper, 16836 ← CometWithExtendedAssetList helper, 17693 ← CometWithExtendedAssetList helper |
| 2463 | CometWithExtendedAssetList helper | 2569 ← CometWithExtendedAssetList helper, 3899 ← CometWithExtendedAssetList helper |
| 2489 | CometWithExtendedAssetList helper | 1284 ← CometWithExtendedAssetList helper |
| 2574 | CometWithExtendedAssetList helper | 1275 ← CometWithExtendedAssetList helper |
| 2634 | CometWithExtendedAssetList helper | 1266 ← CometWithExtendedAssetList helper |
| 2696 | CometWithExtendedAssetList helper | 1257 ← CometWithExtendedAssetList helper |
| 2756 | CometWithExtendedAssetList helper | 1248 ← CometWithExtendedAssetList helper |
| 2819 | CometWithExtendedAssetList helper | 1239 ← CometWithExtendedAssetList helper |
| 2879 | CometWithExtendedAssetList helper | 1230 ← CometWithExtendedAssetList helper |
| 2919 | CometWithExtendedAssetList helper | 1221 ← CometWithExtendedAssetList helper |
| 2959 | CometWithExtendedAssetList helper | 10566 ← CometWithExtendedAssetList helper, 10586 ← CometWithExtendedAssetList helper, 10591 ← CometWithExtendedAssetList.isBorrowCollateralized, 11045 ← CometWithExtendedAssetList helper, 11800 ← CometWithExtendedAssetList helper, 11917 ← CometWithExtendedAssetList helper, 12715 ← CometWithExtendedAssetList helper, 15022 ← CometWithExtendedAssetList helper, 15084 ← CometWithExtendedAssetList helper, 16016 ← CometWithExtendedAssetList helper, 16811 ← CometWithExtendedAssetList helper, 17529 ← CometWithExtendedAssetList helper, 17749 ← CometWithExtendedAssetList helper, 17782 ← CometWithExtendedAssetList helper, 17791 ← CometWithExtendedAssetList.absorbInternal |
| 2971 | CometWithExtendedAssetList helper | 3175 ← CometWithExtendedAssetList helper |
| 3123 | CometWithExtendedAssetList helper | 1212 ← CometWithExtendedAssetList helper |
| 3176 | CometWithExtendedAssetList helper | 1203 ← CometWithExtendedAssetList helper |
| 3216 | CometWithExtendedAssetList helper | 1194 ← CometWithExtendedAssetList helper |
| 3252 | CometWithExtendedAssetList helper | 1185 ← CometWithExtendedAssetList helper |
| 3288 | CometWithExtendedAssetList helper | 1176 ← CometWithExtendedAssetList helper |
| 3348 | CometWithExtendedAssetList helper | 3388 ← CometWithExtendedAssetList helper, 3398 ← CometWithExtendedAssetList helper, 3408 ← CometWithExtendedAssetList helper, 3419 ← CometWithExtendedAssetList helper, 3430 ← CometWithExtendedAssetList helper |
| 3361 | CometWithExtendedAssetList helper | 1167 ← CometWithExtendedAssetList helper |
| 3744 | CometWithExtendedAssetList helper | 1158 ← CometWithExtendedAssetList helper |
| 3814 | CometWithExtendedAssetList helper | 1149 ← CometWithExtendedAssetList helper |
| 3900 | CometWithExtendedAssetList helper | 1140 ← CometWithExtendedAssetList helper |
| 3960 | CometWithExtendedAssetList helper | 1131 ← CometWithExtendedAssetList helper |
| 3999 | CometWithExtendedAssetList helper | 1122 ← CometWithExtendedAssetList helper |
| 4039 | CometWithExtendedAssetList helper | 1113 ← CometWithExtendedAssetList helper |
| 4099 | CometWithExtendedAssetList helper | 1104 ← CometWithExtendedAssetList helper |
| 4143 | CometWithExtendedAssetList helper | 1095 ← CometWithExtendedAssetList helper |
| 4171 | CometWithExtendedAssetList helper | 1086 ← CometWithExtendedAssetList helper |
| 4231 | CometWithExtendedAssetList helper | 1077 ← CometWithExtendedAssetList helper |
| 4328 | CometWithExtendedAssetList helper | 1068 ← CometWithExtendedAssetList helper |
| 4367 | CometWithExtendedAssetList helper | 1059 ← CometWithExtendedAssetList helper |
| 4405 | CometWithExtendedAssetList helper | 1050 ← CometWithExtendedAssetList helper |
| 4465 | CometWithExtendedAssetList helper | 1041 ← CometWithExtendedAssetList helper |
| 4525 | CometWithExtendedAssetList helper | 1032 ← CometWithExtendedAssetList helper |
| 4585 | CometWithExtendedAssetList helper | 1023 ← CometWithExtendedAssetList helper |
| 4645 | CometWithExtendedAssetList helper | 1014 ← CometWithExtendedAssetList helper |
| 4694 | CometWithExtendedAssetList helper | 1005 ← CometWithExtendedAssetList helper |
| 4734 | CometWithExtendedAssetList helper | 996 ← CometWithExtendedAssetList helper |
| 4799 | CometWithExtendedAssetList helper | 987 ← CometWithExtendedAssetList helper |
| 4838 | CometWithExtendedAssetList helper | 978 ← CometWithExtendedAssetList helper |
| 4901 | CometWithExtendedAssetList helper | 969 ← CometWithExtendedAssetList helper |
| 4961 | CometWithExtendedAssetList helper | 960 ← CometWithExtendedAssetList helper |
| 5047 | CometWithExtendedAssetList helper | 951 ← CometWithExtendedAssetList helper |
| 5107 | CometWithExtendedAssetList helper | 942 ← CometWithExtendedAssetList helper |
| 5272 | CometWithExtendedAssetList helper | 933 ← CometWithExtendedAssetList helper |
| 5427 | CometWithExtendedAssetList helper | 924 ← CometWithExtendedAssetList helper |
| 5465 | CometWithExtendedAssetList helper | 915 ← CometWithExtendedAssetList helper |
| 5501 | CometWithExtendedAssetList helper | 906 ← CometWithExtendedAssetList helper |
| 5602 | CometWithExtendedAssetList helper | 897 ← CometWithExtendedAssetList helper |
| 5672 | CometWithExtendedAssetList helper | 888 ← CometWithExtendedAssetList helper |
| 5782 | CometWithExtendedAssetList helper | 5828 ← CometWithExtendedAssetList helper, 7114 ← CometWithExtendedAssetList helper |
| 5793 | CometWithExtendedAssetList helper | 879 ← CometWithExtendedAssetList helper |
| 5834 | CometWithExtendedAssetList helper | 870 ← CometWithExtendedAssetList helper |
| 5862 | CometWithExtendedAssetList helper | 861 ← CometWithExtendedAssetList helper |
| 5901 | CometWithExtendedAssetList helper | 852 ← CometWithExtendedAssetList helper |
| 5932 | CometWithExtendedAssetList helper | 843 ← CometWithExtendedAssetList helper |
| 6047 | CometWithExtendedAssetList helper | 834 ← CometWithExtendedAssetList helper |
| 6117 | CometWithExtendedAssetList helper | 825 ← CometWithExtendedAssetList helper |
| 6352 | CometWithExtendedAssetList helper | 816 ← CometWithExtendedAssetList helper |
| 6745 | CometWithExtendedAssetList helper | 807 ← CometWithExtendedAssetList helper |
| 6815 | CometWithExtendedAssetList helper | 798 ← CometWithExtendedAssetList helper |
| 6868 | CometWithExtendedAssetList helper | 784 ← CometWithExtendedAssetList helper |
| 6921 | CometCore.hasPermission | 5861 ← CometWithExtendedAssetList helper, 12095 ← CometWithExtendedAssetList.supplyInternal, 14525 ← CometWithExtendedAssetList.transferInternal, 15626 ← CometWithExtendedAssetList.withdrawInternal |
| 6982 | CometWithExtendedAssetList helper | 5252 ← CometWithExtendedAssetList.approveThis, 5352 ← CometWithExtendedAssetList helper, 7054 ← CometWithExtendedAssetList helper, 7306 ← CometWithExtendedAssetList.getAssetInfo, 7334 ← CometWithExtendedAssetList helper, 7669 ← CometWithExtendedAssetList helper, 9481 ← CometWithExtendedAssetList.getPrice, 9677 ← CometWithExtendedAssetList.getCollateralReserves, 10102 ← CometWithExtendedAssetList.getReserves, 13524 ← CometWithExtendedAssetList.doTransferIn, 13586 ← CometWithExtendedAssetList.doTransferIn, 13629 ← CometWithExtendedAssetList.doTransferIn, 13664 ← CometWithExtendedAssetList helper, 16260 ← CometWithExtendedAssetList.doTransferOut, 16581 ← CometWithExtendedAssetList helper |
| 7039 | CometWithExtendedAssetList helper | 7186 ← CometWithExtendedAssetList helper, 7490 ← CometWithExtendedAssetList helper |
| 7104 | CometWithExtendedAssetList helper | 7343 ← CometWithExtendedAssetList helper |
| 7115 | CometWithExtendedAssetList helper | 7357 ← CometWithExtendedAssetList helper, 7374 ← CometWithExtendedAssetList helper |
| 7126 | CometWithExtendedAssetList helper | 7391 ← CometWithExtendedAssetList helper, 7408 ← CometWithExtendedAssetList helper, 7425 ← CometWithExtendedAssetList helper, 7442 ← CometWithExtendedAssetList helper |
| 7146 | CometWithExtendedAssetList helper | 7453 ← CometWithExtendedAssetList helper |
| 7166 | CometWithExtendedAssetList helper | 5266 ← CometWithExtendedAssetList.approveThis, 7476 ← CometWithExtendedAssetList.getAssetInfo, 9540 ← CometWithExtendedAssetList.getPrice, 9707 ← CometWithExtendedAssetList.getCollateralReserves, 10123 ← CometWithExtendedAssetList.getReserves, 13539 ← CometWithExtendedAssetList.doTransferIn, 13600 ← CometWithExtendedAssetList.doTransferIn, 13644 ← CometWithExtendedAssetList.doTransferIn, 16275 ← CometWithExtendedAssetList.doTransferOut |
| 7179 | CometWithExtendedAssetList.getAssetInfo | 5833 ← CometWithExtendedAssetList helper, 7570 ← CometWithExtendedAssetList.getAssetInfoByAddress, 10489 ← CometWithExtendedAssetList.isBorrowCollateralized, 11009 ← CometWithExtendedAssetList.isLiquidatable, 17588 ← CometWithExtendedAssetList.absorbInternal |
| 7482 | CometWithExtendedAssetList.getAssetInfoByAddress | 3163 ← CometWithExtendedAssetList helper, 13860 ← CometWithExtendedAssetList.supplyCollateral, 15510 ← CometWithExtendedAssetList.transferCollateral, 16429 ← CometWithExtendedAssetList.withdrawCollateral, 17980 ← CometWithExtendedAssetList.quoteCollateral |
| 7614 | CometWithExtendedAssetList.getNowInternal | 1677 ← CometWithExtendedAssetList.totalSupply, 1860 ← CometWithExtendedAssetList.initializeStorage, 4269 ← CometWithExtendedAssetList.totalBorrow, 7893 ← CometWithExtendedAssetList.accrueInternal, 9835 ← CometWithExtendedAssetList.getReserves, 18262 ← CometWithExtendedAssetList.balanceOf, 18356 ← CometWithExtendedAssetList.borrowBalanceOf |
| 7655 | CometWithExtendedAssetList helper | 12494 ← CometWithExtendedAssetList helper, 14694 ← CometWithExtendedAssetList helper, 14714 ← CometWithExtendedAssetList helper |
| 7730 | CometWithExtendedAssetList helper | 7782 ← CometWithExtendedAssetList helper, 7825 ← CometWithExtendedAssetList helper, 7866 ← CometWithExtendedAssetList helper, 8880 ← CometWithExtendedAssetList helper, 9145 ← CometWithExtendedAssetList helper, 9312 ← CometWithExtendedAssetList helper, 9762 ← CometWithExtendedAssetList helper, 9819 ← CometWithExtendedAssetList helper, 10665 ← CometWithExtendedAssetList helper, 11368 ← CometWithExtendedAssetList helper, 11393 ← CometWithExtendedAssetList helper, 11406 ← CometWithExtendedAssetList helper, 11419 ← CometWithExtendedAssetList helper, 11432 ← CometWithExtendedAssetList helper, 12898 ← CometWithExtendedAssetList helper, 12911 ← CometWithExtendedAssetList helper, 12991 ← CometWithExtendedAssetList helper, 13142 ← CometWithExtendedAssetList helper, 18233 ← CometWithExtendedAssetList helper, 18246 ← CometWithExtendedAssetList helper |
| 7753 | CometWithExtendedAssetList helper | 1706 ← CometWithExtendedAssetList.totalSupply, 4298 ← CometWithExtendedAssetList.totalBorrow, 7925 ← CometWithExtendedAssetList.accrueInternal, 9865 ← CometWithExtendedAssetList.getReserves, 18286 ← CometWithExtendedAssetList.balanceOf |
| 7787 | CometWithExtendedAssetList helper | 8043 ← CometWithExtendedAssetList helper, 8116 ← CometWithExtendedAssetList.accrueInternal, 12562 ← CometWithExtendedAssetList helper, 14855 ← CometWithExtendedAssetList helper, 15840 ← CometWithExtendedAssetList helper, 17326 ← CometWithExtendedAssetList helper |
| 7799 | CometWithExtendedAssetList helper | 1737 ← CometCore.presentValueSupply, 4327 ← CometCore.presentValueSupply, 8223 ← CometWithExtendedAssetList.accrueInternal, 8343 ← CometWithExtendedAssetList.accrueInternal, 8558 ← CometWithExtendedAssetList.accruedInterestIndices, 8564 ← CometWithExtendedAssetList.mulFactor, 8582 ← CometWithExtendedAssetList.accruedInterestIndices, 8711 ← CometWithExtendedAssetList.mulFactor, 8817 ← CometWithExtendedAssetList.mulFactor, 8865 ← CometWithExtendedAssetList.mulFactor, 8983 ← CometWithExtendedAssetList.mulFactor, 9089 ← CometWithExtendedAssetList.mulFactor, 9137 ← CometWithExtendedAssetList.mulFactor, 9245 ← CometCore.presentValueSupply, 9261 ← CometCore.presentValueSupply, 9354 ← CometCore.presentValueSupply, 10021 ← CometCore.presentValueSupply, 10034 ← CometCore.presentValueSupply, 10745 ← CometCore.presentValueSupply, 11150 ← CometWithExtendedAssetList.mulFactor, 11193 ← CometWithExtendedAssetList.divBaseWei, 11203 ← CometWithExtendedAssetList.mulPrice, 11821 ← CometWithExtendedAssetList.updateBasePrincipal, 12061 ← CometWithExtendedAssetList.updateBasePrincipal, 16818 ← CometWithExtendedAssetList.absorb, 17218 ← CometWithExtendedAssetList.divPrice, 18094 ← CometWithExtendedAssetList.mulFactor, 18111 ← CometWithExtendedAssetList.mulFactor, 18164 ← CometWithExtendedAssetList.quoteCollateral |
| 7830 | CometWithExtendedAssetList helper | 8243 ← CometWithExtendedAssetList.accrueInternal, 8248 ← CometWithExtendedAssetList.accrueInternal, 8362 ← CometWithExtendedAssetList.accrueInternal, 8576 ← CometWithExtendedAssetList.accruedInterestIndices |
| 7871 | CometWithExtendedAssetList helper | 8111 ← CometWithExtendedAssetList helper, 12585 ← CometWithExtendedAssetList helper, 14898 ← CometWithExtendedAssetList helper, 15851 ← CometWithExtendedAssetList helper, 17359 ← CometWithExtendedAssetList helper |
| 7886 | CometWithExtendedAssetList.accrueInternal | 5312 ← CometWithExtendedAssetList.accrueAccount, 12472 ← CometWithExtendedAssetList.supplyBase, 14674 ← CometWithExtendedAssetList.transferBase, 15747 ← CometWithExtendedAssetList.withdrawBase, 16691 ← CometWithExtendedAssetList.absorb |
| 8407 | CometMath.safe64 | 8233 ← CometWithExtendedAssetList.accrueInternal, 8570 ← CometWithExtendedAssetList.accruedInterestIndices |
| 8445 | CometWithExtendedAssetList.accruedInterestIndices | 1712 ← CometWithExtendedAssetList.totalSupply, 7961 ← CometWithExtendedAssetList.accrueInternal, 9870 ← CometWithExtendedAssetList.getReserves |
| 8591 | CometWithExtendedAssetList helper | 8750 ← CometWithExtendedAssetList.getSupplyRate, 8872 ← CometWithExtendedAssetList.getSupplyRate, 9022 ← CometWithExtendedAssetList.getBorrowRate, 12849 ← CometCore.principalValueBorrow, 17810 ← CometWithExtendedAssetList.absorbInternal |
| 8603 | CometWithExtendedAssetList helper | 13502 ← CometWithExtendedAssetList.doTransferIn, 16732 ← CometWithExtendedAssetList.absorb |
| 8614 | CometWithExtendedAssetList.getSupplyRate | 5931 ← CometWithExtendedAssetList helper, 8526 ← CometWithExtendedAssetList.accruedInterestIndices |
| 8886 | CometWithExtendedAssetList.getBorrowRate | 4675 ← CometWithExtendedAssetList helper, 8533 ← CometWithExtendedAssetList.accruedInterestIndices |
| 9151 | CometCore helper | 9191 ← CometCore helper, 11380 ← CometWithExtendedAssetList helper, 12885 ← CometCore helper, 12978 ← CometCore helper, 18220 ← CometCore helper |
| 9174 | CometCore helper | 11860 ← CometWithExtendedAssetList.updateBasePrincipal, 11899 ← CometWithExtendedAssetList.updateBasePrincipal, 17223 ← CometWithExtendedAssetList.divPrice, 18212 ← CometWithExtendedAssetList.quoteCollateral |
| 9196 | CometWithExtendedAssetList.getUtilization | 4170 ← CometWithExtendedAssetList helper, 8519 ← CometWithExtendedAssetList.accruedInterestIndices |
| 9318 | CometCore.presentValueSupply | 10799 ← CometCore.presentValue, 12720 ← CometWithExtendedAssetList.supplyBase, 17541 ← CometWithExtendedAssetList.absorbInternal |
| 9355 | CometWithExtendedAssetList helper | 9499 ← CometWithExtendedAssetList helper, 9517 ← CometWithExtendedAssetList helper |
| 9375 | CometWithExtendedAssetList.getPrice | 3215 ← CometWithExtendedAssetList helper, 10299 ← CometWithExtendedAssetList.isBorrowCollateralized, 10553 ← CometWithExtendedAssetList helper, 11032 ← CometWithExtendedAssetList helper, 17103 ← CometWithExtendedAssetList.absorbInternal, 17735 ← CometWithExtendedAssetList.absorbInternal, 18009 ← CometWithExtendedAssetList.quoteCollateral, 18154 ← CometWithExtendedAssetList.quoteCollateral |
| 9546 | CometWithExtendedAssetList helper | 9685 ← CometWithExtendedAssetList.getCollateralReserves |
| 9561 | CometWithExtendedAssetList.getCollateralReserves | 4733 ← CometWithExtendedAssetList helper, 6515 ← CometWithExtendedAssetList.buyCollateral |
| 9713 | CometWithExtendedAssetList helper | 10053 ← CometWithExtendedAssetList.getReserves, 14768 ← CometWithExtendedAssetList.transferBase, 17389 ← CometWithExtendedAssetList.absorbInternal |
| 9768 | CometWithExtendedAssetList helper | 10059 ← CometWithExtendedAssetList.getReserves, 14797 ← CometWithExtendedAssetList.transferBase, 17229 ← CometWithExtendedAssetList.absorbInternal |
| 9825 | CometWithExtendedAssetList.getReserves | 1503 ← CometWithExtendedAssetList helper, 6207 ← CometWithExtendedAssetList.withdrawReserves, 6423 ← CometWithExtendedAssetList.buyCollateral |
| 10129 | CometMath.signed256 | 10041 ← CometWithExtendedAssetList.getReserves, 10047 ← CometWithExtendedAssetList.getReserves, 10602 ← CometWithExtendedAssetList.isBorrowCollateralized, 10751 ← CometCore.presentValue, 11236 ← CometWithExtendedAssetList.signedMulPrice, 12530 ← CometWithExtendedAssetList.supplyBase, 14759 ← CometWithExtendedAssetList.transferBase, 14788 ← CometWithExtendedAssetList.transferBase, 15796 ← CometWithExtendedAssetList.withdrawBase |
| 10164 | CometWithExtendedAssetList.isBorrowCollateralized | 2958 ← CometWithExtendedAssetList helper, 15181 ← CometWithExtendedAssetList.transferBase, 15540 ← CometWithExtendedAssetList.transferCollateral, 16075 ← CometWithExtendedAssetList.withdrawBase, 16449 ← CometWithExtendedAssetList.withdrawCollateral |
| 10633 | CometWithExtendedAssetList helper | 10784 ← CometCore.presentValue, 12056 ← CometWithExtendedAssetList.updateBasePrincipal, 12877 ← CometCore.principalValue, 13242 ← CometWithExtendedAssetList.repayAndSupplyAmount, 15288 ← CometWithExtendedAssetList.withdrawAndBorrowAmount, 18412 ← CometWithExtendedAssetList.borrowBalanceOf |
| 10671 | CometWithExtendedAssetList helper | 10804 ← CometCore.presentValue, 12812 ← CometCore.principalValue, 15131 ← CometWithExtendedAssetList.transferBase, 16025 ← CometWithExtendedAssetList.withdrawBase |
| 10688 | CometCore.presentValue | 10258 ← CometWithExtendedAssetList.isBorrowCollateralized, 12521 ← CometWithExtendedAssetList.supplyBase, 14750 ← CometWithExtendedAssetList.transferBase, 14778 ← CometWithExtendedAssetList.transferBase, 15787 ← CometWithExtendedAssetList.withdrawBase, 17030 ← CometWithExtendedAssetList.absorbInternal |
| 10805 | CometWithExtendedAssetList.isLiquidatable | 1454 ← CometWithExtendedAssetList helper, 16990 ← CometWithExtendedAssetList.absorbInternal |
| 11083 | CometCore helper | 3623 ← CometWithExtendedAssetList.pause, 11700 ← CometWithExtendedAssetList helper, 14320 ← CometWithExtendedAssetList.updateAssetsIn, 14473 ← CometWithExtendedAssetList.updateAssetsIn, 17305 ← CometWithExtendedAssetList.absorbInternal |
| 11118 | CometMath.toUInt8 | 3542 ← CometWithExtendedAssetList.pause, 3570 ← CometWithExtendedAssetList.pause, 3585 ← CometWithExtendedAssetList.pause, 3600 ← CometWithExtendedAssetList.pause, 3615 ← CometWithExtendedAssetList.pause |
| 11132 | CometWithExtendedAssetList.mulFactor | 10597 ← CometWithExtendedAssetList.isBorrowCollateralized, 17801 ← CometWithExtendedAssetList.absorbInternal |
| 11151 | CometWithExtendedAssetList.divBaseWei | 8228 ← CometWithExtendedAssetList.accrueInternal |
| 11194 | CometWithExtendedAssetList.mulPrice | 10578 ← CometWithExtendedAssetList.isBorrowCollateralized, 11058 ← CometWithExtendedAssetList.isLiquidatable, 17409 ← CometWithExtendedAssetList.absorbInternal, 17768 ← CometWithExtendedAssetList.absorbInternal |
| 11226 | CometWithExtendedAssetList.signedMulPrice | 10347 ← CometWithExtendedAssetList.isBorrowCollateralized |
| 11438 | CometWithExtendedAssetList helper | 14289 ← CometWithExtendedAssetList.updateAssetsIn, 14447 ← CometWithExtendedAssetList.updateAssetsIn |
| 11456 | CometWithExtendedAssetList.isInAsset | 10421 ← CometWithExtendedAssetList.isBorrowCollateralized, 10941 ← CometWithExtendedAssetList.isLiquidatable, 17561 ← CometWithExtendedAssetList.absorbInternal |
| 11523 | CometWithExtendedAssetList helper | 11806 ← CometWithExtendedAssetList.updateBasePrincipal |
| 11547 | CometWithExtendedAssetList helper | 11691 ← CometWithExtendedAssetList helper, 14255 ← CometWithExtendedAssetList.updateAssetsIn, 14410 ← CometWithExtendedAssetList.updateAssetsIn, 17282 ← CometWithExtendedAssetList.absorbInternal |
| 11578 | CometWithExtendedAssetList helper | 11984 ← CometWithExtendedAssetList helper |
| 11701 | CometWithExtendedAssetList.updateBasePrincipal | 5426 ← CometWithExtendedAssetList.accrueAccount, 12603 ← CometWithExtendedAssetList.supplyBase, 14939 ← CometWithExtendedAssetList.transferBase, 14949 ← CometWithExtendedAssetList.transferBase, 17260 ← CometWithExtendedAssetList.absorbInternal |
| 12067 | CometWithExtendedAssetList.supplyInternal | 3251 ← CometWithExtendedAssetList.nonReentrant, 4404 ← CometWithExtendedAssetList.nonReentrant, 6867 ← CometWithExtendedAssetList.nonReentrant |
| 12207 | CometMath.safe128 | 6574 ← CometWithExtendedAssetList.buyCollateral, 12200 ← CometWithExtendedAssetList.supplyInternal, 13850 ← CometWithExtendedAssetList.supplyCollateral, 14639 ← CometWithExtendedAssetList.transferInternal, 15727 ← CometWithExtendedAssetList.withdrawInternal |
| 12245 | CometWithExtendedAssetList.nonReentrantBefore | 2075 ← CometWithExtendedAssetList.nonReentrant, 2301 ← CometWithExtendedAssetList.nonReentrant, 3244 ← CometWithExtendedAssetList.nonReentrant, 3280 ← CometWithExtendedAssetList.nonReentrant, 4398 ← CometWithExtendedAssetList.nonReentrant, 5001 ← CometWithExtendedAssetList.nonReentrant, 5458 ← CometWithExtendedAssetList.nonReentrant, 5493 ← CometWithExtendedAssetList.nonReentrant, 6402 ← CometWithExtendedAssetList.nonReentrant, 6855 ← CometWithExtendedAssetList.nonReentrant, 6908 ← CometWithExtendedAssetList.nonReentrant |
| 12293 | CometWithExtendedAssetList helper | 12567 ← CometWithExtendedAssetList.supplyBase, 14865 ← CometWithExtendedAssetList.transferBase, 14908 ← CometWithExtendedAssetList.transferBase, 17336 ← CometWithExtendedAssetList.absorbInternal |
| 12322 | CometWithExtendedAssetList helper | 12574 ← CometWithExtendedAssetList.supplyBase, 14886 ← CometWithExtendedAssetList.transferBase, 17347 ← CometWithExtendedAssetList.absorbInternal |
| 12353 | CometWithExtendedAssetList helper | 12590 ← CometWithExtendedAssetList.supplyBase, 14875 ← CometWithExtendedAssetList.transferBase, 14918 ← CometWithExtendedAssetList.transferBase, 17369 ← CometWithExtendedAssetList.absorbInternal |
| 12377 | CometWithExtendedAssetList helper | 12597 ← CometWithExtendedAssetList.supplyBase, 14929 ← CometWithExtendedAssetList.transferBase, 17380 ← CometWithExtendedAssetList.absorbInternal |
| 12418 | CometWithExtendedAssetList.supplyBase | 12186 ← CometWithExtendedAssetList.supplyInternal |
| 12742 | CometCore.principalValue | 12535 ← CometWithExtendedAssetList.supplyBase, 14807 ← CometWithExtendedAssetList.transferBase, 14817 ← CometWithExtendedAssetList.transferBase, 15812 ← CometWithExtendedAssetList.withdrawBase, 17248 ← CometWithExtendedAssetList.absorbInternal |
| 12917 | CometCore.principalValueSupply | 12774 ← CometCore.principalValue |
| 12997 | CometMath.safe104 | 12872 ← CometCore.principalValueBorrow, 12970 ← CometCore.principalValueSupply |
| 13035 | CometMath.signed104 | 12779 ← CometCore.principalValue |
| 13082 | CometWithExtendedAssetList helper | 13183 ← CometWithExtendedAssetList.repayAndSupplyAmount, 13215 ← CometWithExtendedAssetList.repayAndSupplyAmount, 15262 ← CometWithExtendedAssetList.withdrawAndBorrowAmount, 15279 ← CometWithExtendedAssetList.withdrawAndBorrowAmount |
| 13148 | CometWithExtendedAssetList.repayAndSupplyAmount | 12542 ← CometWithExtendedAssetList.supplyBase, 14840 ← CometWithExtendedAssetList.transferBase, 17314 ← CometWithExtendedAssetList.absorbInternal |
| 13272 | CometWithExtendedAssetList.doTransferIn | 6485 ← CometWithExtendedAssetList.buyCollateral, 12464 ← CometWithExtendedAssetList.supplyBase, 13845 ← CometWithExtendedAssetList.supplyCollateral |
| 13650 | CometWithExtendedAssetList helper | 13880 ← CometWithExtendedAssetList helper |
| 13689 | CometWithExtendedAssetList helper | 13903 ← CometWithExtendedAssetList.supplyCollateral, 14039 ← CometWithExtendedAssetList.supplyCollateral, 15434 ← CometWithExtendedAssetList.transferCollateral |
| 13718 | CometWithExtendedAssetList helper | 13772 ← CometWithExtendedAssetList helper, 14070 ← CometWithExtendedAssetList.supplyCollateral, 15468 ← CometWithExtendedAssetList.transferCollateral, 15501 ← CometWithExtendedAssetList.transferCollateral, 16388 ← CometWithExtendedAssetList.withdrawCollateral, 16420 ← CometWithExtendedAssetList.withdrawCollateral, 17670 ← CometWithExtendedAssetList.absorbInternal, 17712 ← CometWithExtendedAssetList.absorbInternal |
| 13749 | CometWithExtendedAssetList helper | 14058 ← CometWithExtendedAssetList helper |
| 13801 | CometWithExtendedAssetList helper | 14108 ← CometWithExtendedAssetList.supplyCollateral, 15596 ← CometWithExtendedAssetList.transferCollateral, 16518 ← CometWithExtendedAssetList.withdrawCollateral |
| 13820 | CometWithExtendedAssetList.supplyCollateral | 12206 ← CometWithExtendedAssetList.supplyInternal |
| 14132 | CometWithExtendedAssetList.updateAssetsIn | 14076 ← CometWithExtendedAssetList.supplyCollateral, 15522 ← CometWithExtendedAssetList.transferCollateral, 15531 ← CometWithExtendedAssetList.transferCollateral, 16440 ← CometWithExtendedAssetList.withdrawCollateral |
| 14496 | CometWithExtendedAssetList.transferInternal | 2115 ← CometWithExtendedAssetList.nonReentrant, 3287 ← CometWithExtendedAssetList.nonReentrant, 5046 ← CometWithExtendedAssetList.nonReentrant, 5464 ← CometWithExtendedAssetList.nonReentrant |
| 14664 | CometWithExtendedAssetList.transferBase | 14625 ← CometWithExtendedAssetList.transferInternal |
| 15228 | CometWithExtendedAssetList.withdrawAndBorrowAmount | 14829 ← CometWithExtendedAssetList.transferBase, 15819 ← CometWithExtendedAssetList.withdrawBase |
| 15305 | CometWithExtendedAssetList helper | 15424 ← CometWithExtendedAssetList.transferCollateral, 16346 ← CometWithExtendedAssetList.withdrawCollateral, 16379 ← CometWithExtendedAssetList.withdrawCollateral, 17703 ← CometWithExtendedAssetList.absorbInternal |
| 15329 | CometWithExtendedAssetList.transferCollateral | 14645 ← CometWithExtendedAssetList.transferInternal |
| 15597 | CometWithExtendedAssetList.withdrawInternal | 2307 ← CometWithExtendedAssetList.nonReentrant, 5500 ← CometWithExtendedAssetList.nonReentrant, 6920 ← CometWithExtendedAssetList.nonReentrant |
| 15734 | CometWithExtendedAssetList.withdrawBase | 15713 ← CometWithExtendedAssetList.withdrawInternal |
| 16086 | CometWithExtendedAssetList helper | 5220 ← CometWithExtendedAssetList.approveThis, 16170 ← CometWithExtendedAssetList.doTransferOut |
| 16113 | CometWithExtendedAssetList.doTransferOut | 6301 ← CometWithExtendedAssetList.withdrawReserves, 6586 ← CometWithExtendedAssetList.buyCollateral, 15904 ← CometWithExtendedAssetList.withdrawBase, 16501 ← CometWithExtendedAssetList.withdrawCollateral |
| 16281 | CometWithExtendedAssetList.withdrawCollateral | 15733 ← CometWithExtendedAssetList.withdrawInternal |
| 16519 | CometWithExtendedAssetList helper | 16960 ← CometWithExtendedAssetList.absorb |
| 16557 | CometWithExtendedAssetList helper | 16965 ← CometWithExtendedAssetList.absorb |
| 16567 | CometWithExtendedAssetList helper | 16757 ← CometWithExtendedAssetList helper |
| 16642 | CometWithExtendedAssetList helper | 16783 ← CometWithExtendedAssetList.absorb |
| 16664 | CometWithExtendedAssetList.absorb | 5601 ← CometWithExtendedAssetList helper |
| 16978 | CometWithExtendedAssetList.absorbInternal | 16971 ← CometWithExtendedAssetList.absorb |
| 17913 | CometMath.unsigned104 | 17535 ← CometWithExtendedAssetList.absorbInternal, 18339 ← CometWithExtendedAssetList.balanceOf, 18417 ← CometWithExtendedAssetList.borrowBalanceOf |
| 17954 | CometMath.unsigned256 | 6343 ← CometWithExtendedAssetList.withdrawReserves, 17398 ← CometWithExtendedAssetList.absorbInternal |
| 17965 | CometWithExtendedAssetList.quoteCollateral | 4142 ← CometWithExtendedAssetList helper, 6496 ← CometWithExtendedAssetList.buyCollateral |
| 18252 | CometWithExtendedAssetList.balanceOf | 4038 ← CometWithExtendedAssetList helper, 14619 ← CometWithExtendedAssetList.transferInternal, 15707 ← CometWithExtendedAssetList.withdrawInternal |
| 18346 | CometWithExtendedAssetList.borrowBalanceOf | 2918 ← CometWithExtendedAssetList helper, 12180 ← CometWithExtendedAssetList.supplyInternal |
| 18418 | CometWithExtendedAssetList.fallback | 21 ← CometWithExtendedAssetList helper |

## Runtime basic blocks

```text
0: PUSH1 0x80 | 2: PUSH1 0x40 | 4: MSTORE | 5: PUSH1 0x04 | 7: CALLDATASIZE | 8: LT | 9: ISZERO | 10: PUSH2 0x0018 | 13: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
14: JUMPDEST | 15: PUSH2 0x0016 | 18: PUSH2 0x47f2 | 21: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
22: JUMPDEST | 23: STOP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
24: JUMPDEST | 25: PUSH1 0x00 | 27: CALLDATALOAD | 28: PUSH1 0xe0 | 30: SHR | 31: DUP1 | 32: PUSH4 0x042e02cf | 37: EQ | 38: PUSH2 0x0568 | 41: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
42: DUP1 | 43: PUSH4 0x0902f1ac | 48: EQ | 49: PUSH2 0x055f | 52: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
53: DUP1 | 54: PUSH4 0x0bc47ad1 | 59: EQ | 60: PUSH2 0x0556 | 63: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
64: DUP1 | 65: PUSH4 0x0c340a24 | 70: EQ | 71: PUSH2 0x054d | 74: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
75: DUP1 | 76: PUSH4 0x18160ddd | 81: EQ | 82: PUSH2 0x0544 | 85: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
86: DUP1 | 87: PUSH4 0x189bb2f1 | 92: EQ | 93: PUSH2 0x053b | 96: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
97: DUP1 | 98: PUSH4 0x1c9f7fb9 | 103: EQ | 104: PUSH2 0x0532 | 107: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
108: DUP1 | 109: PUSH4 0x1f5954bd | 114: EQ | 115: PUSH2 0x0529 | 118: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
119: DUP1 | 120: PUSH4 0x23b872dd | 125: EQ | 126: PUSH2 0x0520 | 129: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
130: DUP1 | 131: PUSH4 0x24a3d622 | 136: EQ | 137: PUSH2 0x0517 | 140: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
141: DUP1 | 142: PUSH4 0x26441318 | 147: EQ | 148: PUSH2 0x050e | 151: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
152: DUP1 | 153: PUSH4 0x2a48cf12 | 158: EQ | 159: PUSH2 0x0505 | 162: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
163: DUP1 | 164: PUSH4 0x2b92a07d | 169: EQ | 170: PUSH2 0x04fc | 173: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
174: DUP1 | 175: PUSH4 0x2d05670b | 180: EQ | 181: PUSH2 0x04f3 | 184: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
185: DUP1 | 186: PUSH4 0x2e04b8e7 | 191: EQ | 192: PUSH2 0x04ea | 195: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
196: DUP1 | 197: PUSH4 0x300e6beb | 202: EQ | 203: PUSH2 0x04e1 | 206: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
207: DUP1 | 208: PUSH4 0x313ce567 | 213: EQ | 214: PUSH2 0x04d8 | 217: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
218: DUP1 | 219: PUSH4 0x32176c49 | 224: EQ | 225: PUSH2 0x04cf | 228: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
229: DUP1 | 230: PUSH4 0x374c49b4 | 235: EQ | 236: PUSH2 0x04c6 | 239: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
240: DUP1 | 241: PUSH4 0x38aa813f | 246: EQ | 247: PUSH2 0x04bd | 250: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
251: DUP1 | 252: PUSH4 0x3b3bec2e | 257: EQ | 258: PUSH2 0x04b4 | 261: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
262: DUP1 | 263: PUSH4 0x41976e09 | 268: EQ | 269: PUSH2 0x04ab | 272: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
273: DUP1 | 274: PUSH4 0x4232cd63 | 279: EQ | 280: PUSH2 0x04a2 | 283: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
284: DUP1 | 285: PUSH4 0x439e2e45 | 290: EQ | 291: PUSH2 0x0499 | 294: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
295: DUP1 | 296: PUSH4 0x44c1e5eb | 301: EQ | 302: PUSH2 0x0490 | 305: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
306: DUP1 | 307: PUSH4 0x44c35d07 | 312: EQ | 313: PUSH2 0x0487 | 316: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
317: DUP1 | 318: PUSH4 0x44ff241d | 323: EQ | 324: PUSH2 0x047e | 327: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
328: DUP1 | 329: PUSH4 0x59e017bd | 334: EQ | 335: PUSH2 0x0475 | 338: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
339: DUP1 | 340: PUSH4 0x5a94b8d1 | 345: EQ | 346: PUSH2 0x046c | 349: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
350: DUP1 | 351: PUSH4 0x67800b5f | 356: EQ | 357: PUSH2 0x0463 | 360: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
361: DUP1 | 362: PUSH4 0x70a08231 | 367: EQ | 368: PUSH2 0x045a | 371: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
372: DUP1 | 373: PUSH4 0x7914acc7 | 378: EQ | 379: PUSH2 0x0451 | 382: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
383: DUP1 | 384: PUSH4 0x7ac88ed1 | 389: EQ | 390: PUSH2 0x0448 | 393: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
394: DUP1 | 395: PUSH4 0x7eb71131 | 400: EQ | 401: PUSH2 0x043f | 404: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
405: DUP1 | 406: PUSH4 0x804de71f | 411: EQ | 412: PUSH2 0x0436 | 415: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
416: DUP1 | 417: PUSH4 0x8285ef40 | 422: EQ | 423: PUSH2 0x042d | 426: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
427: DUP1 | 428: PUSH4 0x8d5d814c | 433: EQ | 434: PUSH2 0x0424 | 437: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
438: DUP1 | 439: PUSH4 0x90323177 | 444: EQ | 445: PUSH2 0x041b | 448: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
449: DUP1 | 450: PUSH4 0x9241a561 | 455: EQ | 456: PUSH2 0x0412 | 459: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
460: DUP1 | 461: PUSH4 0x9364e18a | 466: EQ | 467: PUSH2 0x0409 | 470: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
471: DUP1 | 472: PUSH4 0x94920cca | 477: EQ | 478: PUSH2 0x0400 | 481: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
482: DUP1 | 483: PUSH4 0x9ea99a5a | 488: EQ | 489: PUSH2 0x03f7 | 492: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
493: DUP1 | 494: PUSH4 0x9fa83b5a | 499: EQ | 500: PUSH2 0x03ee | 503: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
504: DUP1 | 505: PUSH4 0x9ff567f8 | 510: EQ | 511: PUSH2 0x03e5 | 514: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
515: DUP1 | 516: PUSH4 0xa1654379 | 521: EQ | 522: PUSH2 0x03dc | 525: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
526: DUP1 | 527: PUSH4 0xa1a1ef43 | 532: EQ | 533: PUSH2 0x03d3 | 536: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
537: DUP1 | 538: PUSH4 0xa46fe83b | 543: EQ | 544: PUSH2 0x03ca | 547: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
548: DUP1 | 549: PUSH4 0xa5b4ff79 | 554: EQ | 555: PUSH2 0x03c1 | 558: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
559: DUP1 | 560: PUSH4 0xa9059cbb | 565: EQ | 566: PUSH2 0x03b8 | 569: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
570: DUP1 | 571: PUSH4 0xaba7f15e | 576: EQ | 577: PUSH2 0x03af | 580: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
581: DUP1 | 582: PUSH4 0xad14777c | 587: EQ | 588: PUSH2 0x03a6 | 591: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
592: DUP1 | 593: PUSH4 0xbfe69c8d | 598: EQ | 599: PUSH2 0x039d | 602: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
603: DUP1 | 604: PUSH4 0xc1ee2c18 | 609: EQ | 610: PUSH2 0x0394 | 613: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
614: DUP1 | 615: PUSH4 0xc3b35a7e | 620: EQ | 621: PUSH2 0x038b | 624: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
625: DUP1 | 626: PUSH4 0xc3cecfd2 | 631: EQ | 632: PUSH2 0x0382 | 635: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
636: DUP1 | 637: PUSH4 0xc55dae63 | 642: EQ | 643: PUSH2 0x0379 | 646: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
647: DUP1 | 648: PUSH4 0xc5fa15cf | 653: EQ | 654: PUSH2 0x0370 | 657: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
658: DUP1 | 659: PUSH4 0xc8c7fe6b | 664: EQ | 665: PUSH2 0x0367 | 668: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
669: DUP1 | 670: PUSH4 0xcde68041 | 675: EQ | 676: PUSH2 0x035e | 679: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
680: DUP1 | 681: PUSH4 0xd8e5f611 | 686: EQ | 687: PUSH2 0x0355 | 690: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
691: DUP1 | 692: PUSH4 0xd955759d | 697: EQ | 698: PUSH2 0x034c | 701: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
702: DUP1 | 703: PUSH4 0xdc4abafd | 708: EQ | 709: PUSH2 0x0343 | 712: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
713: DUP1 | 714: PUSH4 0xe372f03a | 719: EQ | 720: PUSH2 0x033a | 723: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
724: DUP1 | 725: PUSH4 0xe478795d | 730: EQ | 731: PUSH2 0x0331 | 734: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
735: DUP1 | 736: PUSH4 0xe4e6e779 | 741: EQ | 742: PUSH2 0x0328 | 745: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
746: DUP1 | 747: PUSH4 0xe7dad6bd | 752: EQ | 753: PUSH2 0x031f | 756: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
757: DUP1 | 758: PUSH4 0xf2b9fdb8 | 763: EQ | 764: PUSH2 0x0316 | 767: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
768: PUSH4 0xf3fef3a3 | 773: SUB | 774: PUSH2 0x000e | 777: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
778: PUSH2 0x0311 | 781: PUSH2 0x1ad4 | 784: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
785: JUMPDEST | 786: PUSH2 0x000e | 789: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
790: JUMPDEST | 791: POP | 792: PUSH2 0x0311 | 795: PUSH2 0x1a9f | 798: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
799: JUMPDEST | 800: POP | 801: PUSH2 0x0311 | 804: PUSH2 0x1a59 | 807: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
808: JUMPDEST | 809: POP | 810: PUSH2 0x0311 | 813: PUSH2 0x18d0 | 816: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
817: JUMPDEST | 818: POP | 819: PUSH2 0x0311 | 822: PUSH2 0x17e5 | 825: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
826: JUMPDEST | 827: POP | 828: PUSH2 0x0311 | 831: PUSH2 0x179f | 834: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
835: JUMPDEST | 836: POP | 837: PUSH2 0x0311 | 840: PUSH2 0x172c | 843: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
844: JUMPDEST | 845: POP | 846: PUSH2 0x0311 | 849: PUSH2 0x170d | 852: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
853: JUMPDEST | 854: POP | 855: PUSH2 0x0311 | 858: PUSH2 0x16e6 | 861: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
862: JUMPDEST | 863: POP | 864: PUSH2 0x0311 | 867: PUSH2 0x16ca | 870: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
871: JUMPDEST | 872: POP | 873: PUSH2 0x0311 | 876: PUSH2 0x16a1 | 879: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
880: JUMPDEST | 881: POP | 882: PUSH2 0x0311 | 885: PUSH2 0x1628 | 888: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
889: JUMPDEST | 890: POP | 891: PUSH2 0x0311 | 894: PUSH2 0x15e2 | 897: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
898: JUMPDEST | 899: POP | 900: PUSH2 0x0311 | 903: PUSH2 0x157d | 906: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
907: JUMPDEST | 908: POP | 909: PUSH2 0x0311 | 912: PUSH2 0x1559 | 915: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
916: JUMPDEST | 917: POP | 918: PUSH2 0x0311 | 921: PUSH2 0x1533 | 924: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
925: JUMPDEST | 926: POP | 927: PUSH2 0x0311 | 930: PUSH2 0x1498 | 933: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
934: JUMPDEST | 935: POP | 936: PUSH2 0x0311 | 939: PUSH2 0x13f3 | 942: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
943: JUMPDEST | 944: POP | 945: PUSH2 0x0311 | 948: PUSH2 0x13b7 | 951: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
952: JUMPDEST | 953: POP | 954: PUSH2 0x0311 | 957: PUSH2 0x1361 | 960: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
961: JUMPDEST | 962: POP | 963: PUSH2 0x0311 | 966: PUSH2 0x1325 | 969: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
970: JUMPDEST | 971: POP | 972: PUSH2 0x0311 | 975: PUSH2 0x12e6 | 978: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
979: JUMPDEST | 980: POP | 981: PUSH2 0x0311 | 984: PUSH2 0x12bf | 987: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
988: JUMPDEST | 989: POP | 990: PUSH2 0x0311 | 993: PUSH2 0x127e | 996: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
997: JUMPDEST | 998: POP | 999: PUSH2 0x0311 | 1002: PUSH2 0x1256 | 1005: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
1006: JUMPDEST | 1007: POP | 1008: PUSH2 0x0311 | 1011: PUSH2 0x1225 | 1014: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
1015: JUMPDEST | 1016: POP | 1017: PUSH2 0x0311 | 1020: PUSH2 0x11e9 | 1023: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
1024: JUMPDEST | 1025: POP | 1026: PUSH2 0x0311 | 1029: PUSH2 0x11ad | 1032: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
1033: JUMPDEST | 1034: POP | 1035: PUSH2 0x0311 | 1038: PUSH2 0x1171 | 1041: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
1042: JUMPDEST | 1043: POP | 1044: PUSH2 0x0311 | 1047: PUSH2 0x1135 | 1050: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
1051: JUMPDEST | 1052: POP | 1053: PUSH2 0x0311 | 1056: PUSH2 0x110f | 1059: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
1060: JUMPDEST | 1061: POP | 1062: PUSH2 0x0311 | 1065: PUSH2 0x10e8 | 1068: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
1069: JUMPDEST | 1070: POP | 1071: PUSH2 0x0311 | 1074: PUSH2 0x1087 | 1077: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
1078: JUMPDEST | 1079: POP | 1080: PUSH2 0x0311 | 1083: PUSH2 0x104b | 1086: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
1087: JUMPDEST | 1088: POP | 1089: PUSH2 0x0311 | 1092: PUSH2 0x102f | 1095: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
1096: JUMPDEST | 1097: POP | 1098: PUSH2 0x0311 | 1101: PUSH2 0x1003 | 1104: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
1105: JUMPDEST | 1106: POP | 1107: PUSH2 0x0311 | 1110: PUSH2 0x0fc7 | 1113: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
1114: JUMPDEST | 1115: POP | 1116: PUSH2 0x0311 | 1119: PUSH2 0x0f9f | 1122: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
1123: JUMPDEST | 1124: POP | 1125: PUSH2 0x0311 | 1128: PUSH2 0x0f78 | 1131: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
1132: JUMPDEST | 1133: POP | 1134: PUSH2 0x0311 | 1137: PUSH2 0x0f3c | 1140: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
1141: JUMPDEST | 1142: POP | 1143: PUSH2 0x0311 | 1146: PUSH2 0x0ee6 | 1149: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
1150: JUMPDEST | 1151: POP | 1152: PUSH2 0x0311 | 1155: PUSH2 0x0ea0 | 1158: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
1159: JUMPDEST | 1160: POP | 1161: PUSH2 0x0311 | 1164: PUSH2 0x0d21 | 1167: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
1168: JUMPDEST | 1169: POP | 1170: PUSH2 0x0311 | 1173: PUSH2 0x0cd8 | 1176: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
1177: JUMPDEST | 1178: POP | 1179: PUSH2 0x0311 | 1182: PUSH2 0x0cb4 | 1185: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
1186: JUMPDEST | 1187: POP | 1188: PUSH2 0x0311 | 1191: PUSH2 0x0c90 | 1194: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
1195: JUMPDEST | 1196: POP | 1197: PUSH2 0x0311 | 1200: PUSH2 0x0c68 | 1203: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
1204: JUMPDEST | 1205: POP | 1206: PUSH2 0x0311 | 1209: PUSH2 0x0c33 | 1212: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
1213: JUMPDEST | 1214: POP | 1215: PUSH2 0x0311 | 1218: PUSH2 0x0b67 | 1221: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
1222: JUMPDEST | 1223: POP | 1224: PUSH2 0x0311 | 1227: PUSH2 0x0b3f | 1230: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
1231: JUMPDEST | 1232: POP | 1233: PUSH2 0x0311 | 1236: PUSH2 0x0b03 | 1239: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
1240: JUMPDEST | 1241: POP | 1242: PUSH2 0x0311 | 1245: PUSH2 0x0ac4 | 1248: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
1249: JUMPDEST | 1250: POP | 1251: PUSH2 0x0311 | 1254: PUSH2 0x0a88 | 1257: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
1258: JUMPDEST | 1259: POP | 1260: PUSH2 0x0311 | 1263: PUSH2 0x0a4a | 1266: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
1267: JUMPDEST | 1268: POP | 1269: PUSH2 0x0311 | 1272: PUSH2 0x0a0e | 1275: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
1276: JUMPDEST | 1277: POP | 1278: PUSH2 0x0311 | 1281: PUSH2 0x09b9 | 1284: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
1285: JUMPDEST | 1286: POP | 1287: PUSH2 0x0311 | 1290: PUSH2 0x0918 | 1293: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
1294: JUMPDEST | 1295: POP | 1296: PUSH2 0x0311 | 1299: PUSH2 0x08de | 1302: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
1303: JUMPDEST | 1304: POP | 1305: PUSH2 0x0311 | 1308: PUSH2 0x0861 | 1311: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
1312: JUMPDEST | 1313: POP | 1314: PUSH2 0x0311 | 1317: PUSH2 0x07fe | 1320: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
1321: JUMPDEST | 1322: POP | 1323: PUSH2 0x0311 | 1326: PUSH2 0x0795 | 1329: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
1330: JUMPDEST | 1331: POP | 1332: PUSH2 0x0311 | 1335: PUSH2 0x070f | 1338: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
1339: JUMPDEST | 1340: POP | 1341: PUSH2 0x0311 | 1344: PUSH2 0x06d3 | 1347: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
1348: JUMPDEST | 1349: POP | 1350: PUSH2 0x0311 | 1353: PUSH2 0x0667 | 1356: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
1357: JUMPDEST | 1358: POP | 1359: PUSH2 0x0311 | 1362: PUSH2 0x0621 | 1365: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
1366: JUMPDEST | 1367: POP | 1368: PUSH2 0x0311 | 1371: PUSH2 0x05e8 | 1374: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
1375: JUMPDEST | 1376: POP | 1377: PUSH2 0x0311 | 1380: PUSH2 0x05c4 | 1383: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
1384: JUMPDEST | 1385: POP | 1386: PUSH2 0x0311 | 1389: PUSH2 0x0587 | 1392: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
1393: JUMPDEST | 1394: PUSH1 0x01 | 1396: PUSH1 0x01 | 1398: PUSH1 0xa0 | 1400: SHL | 1401: SUB | 1402: DUP2 | 1403: AND | 1404: SUB | 1405: PUSH2 0x0582 | 1408: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
1409: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
1410: JUMPDEST | 1411: PUSH1 0x00 | 1413: DUP1 | 1414: REVERT    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
1415: JUMPDEST | 1416: POP | 1417: CALLVALUE | 1418: PUSH2 0x0582 | 1421: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
1422: PUSH1 0x20 | 1424: CALLDATASIZE | 1425: PUSH1 0x03 | 1427: NOT | 1428: ADD | 1429: SLT | 1430: PUSH2 0x0582 | 1433: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
1434: PUSH1 0x20 | 1436: PUSH2 0x05af | 1439: PUSH1 0x04 | 1441: CALLDATALOAD | 1442: PUSH2 0x05aa | 1445: DUP2 | 1446: PUSH2 0x0571 | 1449: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
1450: JUMPDEST | 1451: PUSH2 0x2a35 | 1454: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
1455: JUMPDEST | 1456: PUSH1 0x40 | 1458: MLOAD | 1459: SWAP1 | 1460: ISZERO | 1461: ISZERO | 1462: DUP2 | 1463: MSTORE | 1464: RETURN    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
1465: JUMPDEST | 1466: PUSH1 0x00 | 1468: SWAP2 | 1469: SUB | 1470: SLT | 1471: PUSH2 0x0582 | 1474: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
1475: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
1476: JUMPDEST | 1477: POP | 1478: CALLVALUE | 1479: PUSH2 0x0582 | 1482: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
1483: PUSH1 0x00 | 1485: CALLDATASIZE | 1486: PUSH1 0x03 | 1488: NOT | 1489: ADD | 1490: SLT | 1491: PUSH2 0x0582 | 1494: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
1495: PUSH1 0x20 | 1497: PUSH2 0x05e0 | 1500: PUSH2 0x2661 | 1503: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
1504: JUMPDEST | 1505: PUSH1 0x40 | 1507: MLOAD | 1508: SWAP1 | 1509: DUP2 | 1510: MSTORE | 1511: RETURN    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
1512: JUMPDEST | 1513: POP | 1514: CALLVALUE | 1515: PUSH2 0x0582 | 1518: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
1519: PUSH1 0x00 | 1521: CALLDATASIZE | 1522: PUSH1 0x03 | 1524: NOT | 1525: ADD | 1526: SLT | 1527: PUSH2 0x0582 | 1530: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
1531: PUSH1 0x20 | 1533: PUSH1 0x01 | 1535: DUP1 | 1536: SLOAD | 1537: PUSH1 0xf8 | 1539: SHR | 1540: AND | 1541: ISZERO | 1542: ISZERO | 1543: PUSH1 0x40 | 1545: MLOAD | 1546: SWAP1 | 1547: DUP2 | 1548: MSTORE | 1549: RETURN    ;; SLOAD ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
1550: JUMPDEST | 1551: PUSH1 0x01 | 1553: PUSH1 0x01 | 1555: PUSH1 0xa0 | 1557: SHL | 1558: SUB | 1559: SWAP1 | 1560: SWAP2 | 1561: AND | 1562: DUP2 | 1563: MSTORE | 1564: PUSH1 0x20 | 1566: ADD | 1567: SWAP1 | 1568: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
1569: JUMPDEST | 1570: POP | 1571: CALLVALUE | 1572: PUSH2 0x0582 | 1575: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
1576: PUSH1 0x00 | 1578: CALLDATASIZE | 1579: PUSH1 0x03 | 1581: NOT | 1582: ADD | 1583: SLT | 1584: PUSH2 0x0582 | 1587: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
1588: PUSH1 0x40 | 1590: MLOAD | 1591: PUSH32 0x0000000000000000000000000000000000000000000000000000000000000000 | 1624: PUSH1 0x01 | 1626: PUSH1 0x01 | 1628: PUSH1 0xa0 | 1630: SHL | 1631: SUB | 1632: AND | 1633: DUP2 | 1634: MSTORE | 1635: PUSH1 0x20 | 1637: SWAP1 | 1638: RETURN    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
1639: JUMPDEST | 1640: POP | 1641: CALLVALUE | 1642: PUSH2 0x0582 | 1645: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
1646: PUSH1 0x00 | 1648: CALLDATASIZE | 1649: PUSH1 0x03 | 1651: NOT | 1652: ADD | 1653: SLT | 1654: PUSH2 0x0582 | 1657: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
1658: PUSH1 0x20 | 1660: PUSH7 0x038d7ea4c68000 | 1668: PUSH2 0x06ca | 1671: PUSH2 0x068e | 1674: PUSH2 0x1dbe | 1677: JUMP    ;; CometWithExtendedAssetList.totalSupply: getNowInternal()
1678: JUMPDEST | 1679: PUSH2 0x06b1 | 1682: PUSH1 0x01 | 1684: SLOAD | 1685: SWAP2 | 1686: PUSH2 0x06ab | 1689: PUSH5 0xffffffffff | 1695: SWAP2 | 1696: DUP3 | 1697: DUP6 | 1698: PUSH1 0xd0 | 1700: SHR | 1701: AND | 1702: SWAP1 | 1703: PUSH2 0x1e49 | 1706: JUMP    ;; SLOAD ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
1707: JUMPDEST | 1708: AND | 1709: PUSH2 0x20fd | 1712: JUMP    ;; CometWithExtendedAssetList.totalSupply: accruedInterestIndices(getNowInternal() - lastAccrualTime)
1713: JUMPDEST | 1714: POP | 1715: PUSH1 0x01 | 1717: PUSH1 0x01 | 1719: PUSH1 0x40 | 1721: SHL | 1722: SUB | 1723: AND | 1724: SWAP1 | 1725: PUSH1 0x01 | 1727: PUSH1 0x01 | 1729: PUSH1 0x68 | 1731: SHL | 1732: SUB | 1733: AND | 1734: PUSH2 0x1e77 | 1737: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
1738: JUMPDEST | 1739: DIV | 1740: PUSH1 0x40 | 1742: MLOAD | 1743: SWAP1 | 1744: DUP2 | 1745: MSTORE | 1746: RETURN    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
1747: JUMPDEST | 1748: POP | 1749: CALLVALUE | 1750: PUSH2 0x0582 | 1753: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
1754: PUSH1 0x00 | 1756: CALLDATASIZE | 1757: PUSH1 0x03 | 1759: NOT | 1760: ADD | 1761: SLT | 1762: PUSH2 0x0582 | 1765: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
1766: PUSH1 0x20 | 1768: PUSH1 0x40 | 1770: MLOAD | 1771: PUSH32 0x0000000000000000000000000000000000000000000000000000000000000000 | 1804: DUP2 | 1805: MSTORE | 1806: RETURN    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
1807: JUMPDEST | 1808: POP | 1809: CALLVALUE | 1810: PUSH2 0x0582 | 1813: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
1814: PUSH1 0x00 | 1816: DUP1 | 1817: PUSH1 0x03 | 1819: NOT | 1820: CALLDATASIZE | 1821: ADD | 1822: SLT | 1823: PUSH2 0x0792 | 1826: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
1827: PUSH1 0x01 | 1829: SLOAD | 1830: PUSH5 0xffffffffff | 1836: DUP2 | 1837: PUSH1 0xd0 | 1839: SHR | 1840: AND | 1841: PUSH2 0x0781 | 1844: JUMPI    ;; SLOAD ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
1845: PUSH5 0xffffffffff | 1851: PUSH1 0xd0 | 1853: SHL | 1854: PUSH2 0x0745 | 1857: PUSH2 0x1dbe | 1860: JUMP    ;; CometWithExtendedAssetList.initializeStorage: getNowInternal()
1861: JUMPDEST | 1862: PUSH5 0xffffffffff | 1868: PUSH1 0xd0 | 1870: SHL | 1871: NOT | 1872: SWAP1 | 1873: SWAP3 | 1874: AND | 1875: PUSH1 0xd0 | 1877: SWAP3 | 1878: SWAP1 | 1879: SWAP3 | 1880: SHL | 1881: AND | 1882: OR | 1883: PUSH1 0x01 | 1885: SSTORE | 1886: DUP1 | 1887: SLOAD | 1888: PUSH1 0x01 | 1890: PUSH1 0x01 | 1892: PUSH1 0x80 | 1894: SHL | 1895: SUB | 1896: NOT | 1897: AND | 1898: PUSH15 0x038d7ea4c6800000038d7ea4c68000 | 1914: OR | 1915: DUP2 | 1916: SSTORE | 1917: PUSH1 0x40 | 1919: MLOAD | 1920: RETURN    ;; SSTORE,SLOAD,SSTORE ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
1921: JUMPDEST | 1922: PUSH1 0x40 | 1924: MLOAD | 1925: PUSH3 0xdc149f | 1929: PUSH1 0xe4 | 1931: SHL | 1932: DUP2 | 1933: MSTORE | 1934: PUSH1 0x04 | 1936: SWAP1 | 1937: REVERT    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
1938: JUMPDEST | 1939: DUP1 | 1940: REVERT    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
1941: JUMPDEST | 1942: POP | 1943: CALLVALUE | 1944: PUSH2 0x0582 | 1947: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
1948: PUSH1 0x00 | 1950: CALLDATASIZE | 1951: PUSH1 0x03 | 1953: NOT | 1954: ADD | 1955: SLT | 1956: PUSH2 0x0582 | 1959: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
1960: PUSH1 0x20 | 1962: PUSH1 0x40 | 1964: MLOAD | 1965: PUSH32 0x0000000000000000000000000000000000000000000000000000000000000000 | 1998: DUP2 | 1999: MSTORE | 2000: RETURN    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
2001: JUMPDEST | 2002: SWAP1 | 2003: DUP2 | 2004: PUSH1 0x60 | 2006: SWAP2 | 2007: SUB | 2008: SLT | 2009: PUSH2 0x0582 | 2012: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
2013: DUP1 | 2014: CALLDATALOAD | 2015: PUSH2 0x07e7 | 2018: DUP2 | 2019: PUSH2 0x0571 | 2022: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
2023: JUMPDEST | 2024: SWAP2 | 2025: PUSH1 0x40 | 2027: PUSH1 0x20 | 2029: DUP4 | 2030: ADD | 2031: CALLDATALOAD | 2032: PUSH2 0x07f8 | 2035: DUP2 | 2036: PUSH2 0x0571 | 2039: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
2040: JUMPDEST | 2041: SWAP3 | 2042: ADD | 2043: CALLDATALOAD | 2044: SWAP1 | 2045: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
2046: JUMPDEST | 2047: POP | 2048: CALLVALUE | 2049: PUSH2 0x0582 | 2052: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
2053: PUSH2 0x0844 | 2056: PUSH2 0x0812 | 2059: CALLDATASIZE | 2060: PUSH1 0x04 | 2062: PUSH2 0x07d1 | 2065: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
2066: JUMPDEST | 2067: SWAP2 | 2068: SWAP1 | 2069: PUSH2 0x081c | 2072: PUSH2 0x2fd5 | 2075: JUMP    ;; CometWithExtendedAssetList.nonReentrant: modifier nonReentrant() { nonReentrantBefore(); _; nonReentrantAfter();…
2076: JUMPDEST | 2077: PUSH32 0x0000000000000000000000000000000000000000000000000000000000000000 | 2110: SWAP2 | 2111: CALLER | 2112: PUSH2 0x38a0 | 2115: JUMP    ;; CometWithExtendedAssetList.transferFrom: msg.sender
2116: JUMPDEST | 2117: PUSH1 0x00 | 2119: PUSH1 0x00 | 2121: DUP1 | 2122: MLOAD | 2123: PUSH1 0x20 | 2125: PUSH2 0x4852 | 2128: DUP4 | 2129: CODECOPY | 2130: DUP2 | 2131: MLOAD | 2132: SWAP2 | 2133: MSTORE | 2134: SSTORE | 2135: PUSH1 0x20 | 2137: PUSH1 0x40 | 2139: MLOAD | 2140: PUSH1 0x01 | 2142: DUP2 | 2143: MSTORE | 2144: RETURN    ;; SSTORE ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
2145: JUMPDEST | 2146: POP | 2147: CALLVALUE | 2148: PUSH2 0x0582 | 2151: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
2152: PUSH1 0x00 | 2154: CALLDATASIZE | 2155: PUSH1 0x03 | 2157: NOT | 2158: ADD | 2159: SLT | 2160: PUSH2 0x0582 | 2163: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
2164: PUSH1 0x40 | 2166: MLOAD | 2167: PUSH32 0x0000000000000000000000000000000000000000000000000000000000000000 | 2200: PUSH1 0x01 | 2202: PUSH1 0x01 | 2204: PUSH1 0xa0 | 2206: SHL | 2207: SUB | 2208: AND | 2209: DUP2 | 2210: MSTORE | 2211: PUSH1 0x20 | 2213: SWAP1 | 2214: RETURN    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
2215: JUMPDEST | 2216: SWAP2 | 2217: SWAP1 | 2218: DUP3 | 2219: PUSH1 0x80 | 2221: SWAP2 | 2222: SUB | 2223: SLT | 2224: PUSH2 0x0582 | 2227: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
2228: DUP2 | 2229: CALLDATALOAD | 2230: PUSH2 0x08be | 2233: DUP2 | 2234: PUSH2 0x0571 | 2237: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
2238: JUMPDEST | 2239: SWAP2 | 2240: PUSH1 0x20 | 2242: DUP2 | 2243: ADD | 2244: CALLDATALOAD | 2245: PUSH2 0x08cd | 2248: DUP2 | 2249: PUSH2 0x0571 | 2252: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
2253: JUMPDEST | 2254: SWAP2 | 2255: PUSH1 0x60 | 2257: PUSH1 0x40 | 2259: DUP4 | 2260: ADD | 2261: CALLDATALOAD | 2262: PUSH2 0x07f8 | 2265: DUP2 | 2266: PUSH2 0x0571 | 2269: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
2270: JUMPDEST | 2271: POP | 2272: CALLVALUE | 2273: PUSH2 0x0582 | 2276: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
2277: PUSH2 0x0904 | 2280: PUSH2 0x08f2 | 2283: CALLDATASIZE | 2284: PUSH1 0x04 | 2286: PUSH2 0x08a7 | 2289: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
2290: JUMPDEST | 2291: SWAP3 | 2292: PUSH2 0x08fe | 2295: SWAP3 | 2296: SWAP2 | 2297: SWAP3 | 2298: PUSH2 0x2fd5 | 2301: JUMP    ;; CometWithExtendedAssetList.nonReentrant: modifier nonReentrant() { nonReentrantBefore(); _; nonReentrantAfter();…
2302: JUMPDEST | 2303: CALLER | 2304: PUSH2 0x3ced | 2307: JUMP    ;; CometWithExtendedAssetList.nonReentrant: _
2308: JUMPDEST | 2309: PUSH1 0x00 | 2311: PUSH1 0x00 | 2313: DUP1 | 2314: MLOAD | 2315: PUSH1 0x20 | 2317: PUSH2 0x4852 | 2320: DUP4 | 2321: CODECOPY | 2322: DUP2 | 2323: MLOAD | 2324: SWAP2 | 2325: MSTORE | 2326: SSTORE | 2327: STOP    ;; SSTORE ;; CometWithExtendedAssetList.nonReentrant: _
2328: JUMPDEST | 2329: POP | 2330: CALLVALUE | 2331: PUSH2 0x0582 | 2334: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
2335: PUSH1 0x00 | 2337: CALLDATASIZE | 2338: PUSH1 0x03 | 2340: NOT | 2341: ADD | 2342: SLT | 2343: PUSH2 0x0582 | 2346: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
2347: PUSH1 0x20 | 2349: PUSH1 0x40 | 2351: MLOAD | 2352: PUSH32 0x0000000000000000000000000000000000000000000000000000000000000000 | 2385: DUP2 | 2386: MSTORE | 2387: RETURN    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
2388: JUMPDEST | 2389: SWAP2 | 2390: SWAP1 | 2391: DUP3 | 2392: PUSH1 0x40 | 2394: SWAP2 | 2395: SUB | 2396: SLT | 2397: PUSH2 0x0582 | 2400: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
2401: PUSH1 0x20 | 2403: DUP3 | 2404: CALLDATALOAD | 2405: PUSH2 0x096d | 2408: DUP2 | 2409: PUSH2 0x0571 | 2412: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
2413: JUMPDEST | 2414: SWAP3 | 2415: ADD | 2416: CALLDATALOAD | 2417: PUSH2 0x0979 | 2420: DUP2 | 2421: PUSH2 0x0571 | 2424: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
2425: JUMPDEST | 2426: SWAP1 | 2427: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
2428: JUMPDEST | 2429: SWAP1 | 2430: PUSH1 0x01 | 2432: DUP1 | 2433: PUSH1 0xa0 | 2435: SHL | 2436: SUB | 2437: AND | 2438: PUSH1 0x00 | 2440: MSTORE | 2441: PUSH1 0x20 | 2443: MSTORE | 2444: PUSH1 0x40 | 2446: PUSH1 0x00 | 2448: KECCAK256 | 2449: SWAP1 | 2450: JUMP    ;; KECCAK256 ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
2451: JUMPDEST | 2452: PUSH1 0x01 | 2454: PUSH1 0x01 | 2456: PUSH1 0x80 | 2458: SHL | 2459: SUB | 2460: AND | 2461: SWAP1 | 2462: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
2463: JUMPDEST | 2464: PUSH1 0x01 | 2466: PUSH1 0x01 | 2468: PUSH1 0x80 | 2470: SHL | 2471: SUB | 2472: SWAP2 | 2473: DUP3 | 2474: AND | 2475: DUP2 | 2476: MSTORE | 2477: SWAP2 | 2478: AND | 2479: PUSH1 0x20 | 2481: DUP3 | 2482: ADD | 2483: MSTORE | 2484: PUSH1 0x40 | 2486: ADD | 2487: SWAP1 | 2488: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
2489: JUMPDEST | 2490: POP | 2491: CALLVALUE | 2492: PUSH2 0x0582 | 2495: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
2496: PUSH2 0x0a0a | 2499: PUSH2 0x09ee | 2502: PUSH2 0x09d0 | 2505: CALLDATASIZE | 2506: PUSH1 0x04 | 2508: PUSH2 0x0954 | 2511: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
2512: JUMPDEST | 2513: PUSH1 0x01 | 2515: PUSH1 0x01 | 2517: PUSH1 0xa0 | 2519: SHL | 2520: SUB | 2521: SWAP1 | 2522: SWAP2 | 2523: AND | 2524: PUSH1 0x00 | 2526: SWAP1 | 2527: DUP2 | 2528: MSTORE | 2529: PUSH1 0x06 | 2531: PUSH1 0x20 | 2533: MSTORE | 2534: PUSH1 0x40 | 2536: SWAP1 | 2537: KECCAK256 | 2538: PUSH2 0x097c | 2541: JUMP    ;; KECCAK256 ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
2542: JUMPDEST | 2543: SLOAD | 2544: PUSH1 0x40 | 2546: MLOAD | 2547: SWAP2 | 2548: DUP3 | 2549: SWAP2 | 2550: PUSH1 0x80 | 2552: DUP2 | 2553: SWAP1 | 2554: SHR | 2555: SWAP1 | 2556: PUSH1 0x01 | 2558: PUSH1 0x01 | 2560: PUSH1 0x80 | 2562: SHL | 2563: SUB | 2564: AND | 2565: DUP4 | 2566: PUSH2 0x099f | 2569: JUMP    ;; SLOAD ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
2570: JUMPDEST | 2571: SUB | 2572: SWAP1 | 2573: RETURN    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
2574: JUMPDEST | 2575: POP | 2576: CALLVALUE | 2577: PUSH2 0x0582 | 2580: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
2581: PUSH1 0x00 | 2583: CALLDATASIZE | 2584: PUSH1 0x03 | 2586: NOT | 2587: ADD | 2588: SLT | 2589: PUSH2 0x0582 | 2592: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
2593: PUSH1 0x20 | 2595: PUSH1 0x40 | 2597: MLOAD | 2598: PUSH32 0x0000000000000000000000000000000000000000000000000000000000000000 | 2631: DUP2 | 2632: MSTORE | 2633: RETURN    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
2634: JUMPDEST | 2635: POP | 2636: CALLVALUE | 2637: PUSH2 0x0582 | 2640: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
2641: PUSH1 0x20 | 2643: CALLDATASIZE | 2644: PUSH1 0x03 | 2646: NOT | 2647: ADD | 2648: SLT | 2649: PUSH2 0x0582 | 2652: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
2653: PUSH1 0x04 | 2655: CALLDATALOAD | 2656: PUSH2 0x0a68 | 2659: DUP2 | 2660: PUSH2 0x0571 | 2663: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
2664: JUMPDEST | 2665: PUSH1 0x01 | 2667: DUP1 | 2668: PUSH1 0xa0 | 2670: SHL | 2671: SUB | 2672: AND | 2673: PUSH1 0x00 | 2675: MSTORE | 2676: PUSH1 0x04 | 2678: PUSH1 0x20 | 2680: MSTORE | 2681: PUSH1 0x20 | 2683: PUSH1 0x40 | 2685: PUSH1 0x00 | 2687: KECCAK256 | 2688: SLOAD | 2689: PUSH1 0x40 | 2691: MLOAD | 2692: SWAP1 | 2693: DUP2 | 2694: MSTORE | 2695: RETURN    ;; KECCAK256,SLOAD ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
2696: JUMPDEST | 2697: POP | 2698: CALLVALUE | 2699: PUSH2 0x0582 | 2702: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
2703: PUSH1 0x00 | 2705: CALLDATASIZE | 2706: PUSH1 0x03 | 2708: NOT | 2709: ADD | 2710: SLT | 2711: PUSH2 0x0582 | 2714: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
2715: PUSH1 0x20 | 2717: PUSH1 0x40 | 2719: MLOAD | 2720: PUSH32 0x0000000000000000000000000000000000000000000000000000000000000000 | 2753: DUP2 | 2754: MSTORE | 2755: RETURN    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
2756: JUMPDEST | 2757: POP | 2758: CALLVALUE | 2759: PUSH2 0x0582 | 2762: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
2763: PUSH1 0x00 | 2765: CALLDATASIZE | 2766: PUSH1 0x03 | 2768: NOT | 2769: ADD | 2770: SLT | 2771: PUSH2 0x0582 | 2774: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
2775: PUSH1 0x20 | 2777: PUSH1 0x40 | 2779: MLOAD | 2780: PUSH1 0xff | 2782: PUSH32 0x0000000000000000000000000000000000000000000000000000000000000000 | 2815: AND | 2816: DUP2 | 2817: MSTORE | 2818: RETURN    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
2819: JUMPDEST | 2820: POP | 2821: CALLVALUE | 2822: PUSH2 0x0582 | 2825: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
2826: PUSH1 0x00 | 2828: CALLDATASIZE | 2829: PUSH1 0x03 | 2831: NOT | 2832: ADD | 2833: SLT | 2834: PUSH2 0x0582 | 2837: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
2838: PUSH1 0x20 | 2840: PUSH1 0x40 | 2842: MLOAD | 2843: PUSH32 0x0000000000000000000000000000000000000000000000000000000000000000 | 2876: DUP2 | 2877: MSTORE | 2878: RETURN    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
2879: JUMPDEST | 2880: POP | 2881: CALLVALUE | 2882: PUSH2 0x0582 | 2885: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
2886: PUSH1 0x20 | 2888: CALLDATASIZE | 2889: PUSH1 0x03 | 2891: NOT | 2892: ADD | 2893: SLT | 2894: PUSH2 0x0582 | 2897: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
2898: PUSH1 0x20 | 2900: PUSH2 0x05e0 | 2903: PUSH1 0x04 | 2905: CALLDATALOAD | 2906: PUSH2 0x0b62 | 2909: DUP2 | 2910: PUSH2 0x0571 | 2913: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
2914: JUMPDEST | 2915: PUSH2 0x47aa | 2918: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
2919: JUMPDEST | 2920: POP | 2921: CALLVALUE | 2922: PUSH2 0x0582 | 2925: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
2926: PUSH1 0x20 | 2928: CALLDATASIZE | 2929: PUSH1 0x03 | 2931: NOT | 2932: ADD | 2933: SLT | 2934: PUSH2 0x0582 | 2937: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
2938: PUSH1 0x20 | 2940: PUSH2 0x05af | 2943: PUSH1 0x04 | 2945: CALLDATALOAD | 2946: PUSH2 0x0b8a | 2949: DUP2 | 2950: PUSH2 0x0571 | 2953: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
2954: JUMPDEST | 2955: PUSH2 0x27b4 | 2958: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
2959: JUMPDEST | 2960: PUSH1 0x01 | 2962: PUSH1 0x01 | 2964: PUSH1 0x40 | 2966: SHL | 2967: SUB | 2968: AND | 2969: SWAP1 | 2970: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
2971: JUMPDEST | 2972: PUSH2 0x0c31 | 2975: SWAP1 | 2976: SWAP3 | 2977: SWAP2 | 2978: SWAP3 | 2979: PUSH1 0xe0 | 2981: DUP1 | 2982: PUSH2 0x0100 | 2985: DUP4 | 2986: ADD | 2987: SWAP6 | 2988: PUSH1 0xff | 2990: DUP2 | 2991: MLOAD | 2992: AND | 2993: DUP5 | 2994: MSTORE | 2995: PUSH1 0x01 | 2997: DUP1 | 2998: PUSH1 0xa0 | 3000: SHL | 3001: SUB | 3002: DUP1 | 3003: PUSH1 0x20 | 3005: DUP4 | 3006: ADD | 3007: MLOAD | 3008: AND | 3009: PUSH1 0x20 | 3011: DUP7 | 3012: ADD | 3013: MSTORE | 3014: PUSH1 0x40 | 3016: DUP3 | 3017: ADD | 3018: MLOAD | 3019: AND | 3020: PUSH1 0x40 | 3022: DUP6 | 3023: ADD | 3024: MSTORE | 3025: PUSH1 0x01 | 3027: DUP1 | 3028: PUSH1 0x40 | 3030: SHL | 3031: SUB | 3032: PUSH1 0x60 | 3034: DUP3 | 3035: ADD | 3036: MLOAD | 3037: AND | 3038: PUSH1 0x60 | 3040: DUP6 | 3041: ADD | 3042: MSTORE | 3043: PUSH2 0x0bfb | 3046: PUSH1 0x80 | 3048: DUP3 | 3049: ADD | 3050: MLOAD | 3051: PUSH1 0x80 | 3053: DUP7 | 3054: ADD | 3055: SWAP1 | 3056: PUSH1 0x01 | 3058: DUP1 | 3059: PUSH1 0x40 | 3061: SHL | 3062: SUB | 3063: AND | 3064: SWAP1 | 3065: MSTORE | 3066: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
3067: JUMPDEST | 3068: PUSH1 0xa0 | 3070: DUP2 | 3071: DUP2 | 3072: ADD | 3073: MLOAD | 3074: PUSH1 0x01 | 3076: PUSH1 0x01 | 3078: PUSH1 0x40 | 3080: SHL | 3081: SUB | 3082: AND | 3083: SWAP1 | 3084: DUP6 | 3085: ADD | 3086: MSTORE | 3087: PUSH1 0xc0 | 3089: DUP2 | 3090: DUP2 | 3091: ADD | 3092: MLOAD | 3093: PUSH1 0x01 | 3095: PUSH1 0x01 | 3097: PUSH1 0x40 | 3099: SHL | 3100: SUB | 3101: AND | 3102: SWAP1 | 3103: DUP6 | 3104: ADD | 3105: MSTORE | 3106: ADD | 3107: MLOAD | 3108: PUSH1 0x01 | 3110: PUSH1 0x01 | 3112: PUSH1 0x80 | 3114: SHL | 3115: SUB | 3116: AND | 3117: SWAP2 | 3118: ADD | 3119: MSTORE | 3120: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
3121: JUMPDEST | 3122: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
3123: JUMPDEST | 3124: POP | 3125: CALLVALUE | 3126: PUSH2 0x0582 | 3129: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
3130: PUSH1 0x20 | 3132: CALLDATASIZE | 3133: PUSH1 0x03 | 3135: NOT | 3136: ADD | 3137: SLT | 3138: PUSH2 0x0582 | 3141: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
3142: PUSH2 0x0a0a | 3145: PUSH2 0x0c5c | 3148: PUSH1 0x04 | 3150: CALLDATALOAD | 3151: PUSH2 0x0c57 | 3154: DUP2 | 3155: PUSH2 0x0571 | 3158: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
3159: JUMPDEST | 3160: PUSH2 0x1d3a | 3163: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
3164: JUMPDEST | 3165: PUSH1 0x40 | 3167: MLOAD | 3168: SWAP2 | 3169: DUP3 | 3170: SWAP2 | 3171: DUP3 | 3172: PUSH2 0x0b9b | 3175: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
3176: JUMPDEST | 3177: POP | 3178: CALLVALUE | 3179: PUSH2 0x0582 | 3182: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
3183: PUSH1 0x20 | 3185: CALLDATASIZE | 3186: PUSH1 0x03 | 3188: NOT | 3189: ADD | 3190: SLT | 3191: PUSH2 0x0582 | 3194: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
3195: PUSH1 0x20 | 3197: PUSH2 0x05e0 | 3200: PUSH1 0x04 | 3202: CALLDATALOAD | 3203: PUSH2 0x0c8b | 3206: DUP2 | 3207: PUSH2 0x0571 | 3210: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
3211: JUMPDEST | 3212: PUSH2 0x249f | 3215: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
3216: JUMPDEST | 3217: POP | 3218: CALLVALUE | 3219: PUSH2 0x0582 | 3222: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
3223: PUSH2 0x0904 | 3226: PUSH2 0x0ca4 | 3229: CALLDATASIZE | 3230: PUSH1 0x04 | 3232: PUSH2 0x07d1 | 3235: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
3236: JUMPDEST | 3237: SWAP2 | 3238: PUSH2 0x0cad | 3241: PUSH2 0x2fd5 | 3244: JUMP    ;; CometWithExtendedAssetList.nonReentrant: modifier nonReentrant() { nonReentrantBefore(); _; nonReentrantAfter();…
3245: JUMPDEST | 3246: CALLER | 3247: CALLER | 3248: PUSH2 0x2f23 | 3251: JUMP    ;; CometWithExtendedAssetList.supplyTo: msg.sender
3252: JUMPDEST | 3253: POP | 3254: CALLVALUE | 3255: PUSH2 0x0582 | 3258: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
3259: PUSH2 0x0904 | 3262: PUSH2 0x0cc8 | 3265: CALLDATASIZE | 3266: PUSH1 0x04 | 3268: PUSH2 0x07d1 | 3271: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
3272: JUMPDEST | 3273: SWAP2 | 3274: PUSH2 0x0cd1 | 3277: PUSH2 0x2fd5 | 3280: JUMP    ;; CometWithExtendedAssetList.nonReentrant: modifier nonReentrant() { nonReentrantBefore(); _; nonReentrantAfter();…
3281: JUMPDEST | 3282: CALLER | 3283: CALLER | 3284: PUSH2 0x38a0 | 3287: JUMP    ;; CometWithExtendedAssetList.transferAsset: msg.sender
3288: JUMPDEST | 3289: POP | 3290: CALLVALUE | 3291: PUSH2 0x0582 | 3294: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
3295: PUSH1 0x00 | 3297: CALLDATASIZE | 3298: PUSH1 0x03 | 3300: NOT | 3301: ADD | 3302: SLT | 3303: PUSH2 0x0582 | 3306: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
3307: PUSH1 0x20 | 3309: PUSH1 0x40 | 3311: MLOAD | 3312: PUSH32 0x0000000000000000000000000000000000000000000000000000000000000000 | 3345: DUP2 | 3346: MSTORE | 3347: RETURN    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
3348: JUMPDEST | 3349: CALLDATALOAD | 3350: SWAP1 | 3351: DUP2 | 3352: ISZERO | 3353: ISZERO | 3354: DUP3 | 3355: SUB | 3356: PUSH2 0x0582 | 3359: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
3360: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
3361: JUMPDEST | 3362: POP | 3363: CALLVALUE | 3364: PUSH2 0x0582 | 3367: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
3368: PUSH1 0xa0 | 3370: CALLDATASIZE | 3371: PUSH1 0x03 | 3373: NOT | 3374: ADD | 3375: SLT | 3376: PUSH2 0x0582 | 3379: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
3380: PUSH2 0x0d3d | 3383: PUSH1 0x04 | 3385: PUSH2 0x0d14 | 3388: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
3389: JUMPDEST | 3390: PUSH2 0x0d47 | 3393: PUSH1 0x24 | 3395: PUSH2 0x0d14 | 3398: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
3399: JUMPDEST | 3400: PUSH2 0x0d51 | 3403: PUSH1 0x44 | 3405: PUSH2 0x0d14 | 3408: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
3409: JUMPDEST | 3410: SWAP2 | 3411: PUSH2 0x0d5c | 3414: PUSH1 0x64 | 3416: PUSH2 0x0d14 | 3419: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
3420: JUMPDEST | 3421: SWAP3 | 3422: PUSH2 0x0d67 | 3425: PUSH1 0x84 | 3427: PUSH2 0x0d14 | 3430: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
3431: JUMPDEST | 3432: PUSH1 0x01 | 3434: DUP1 | 3435: PUSH1 0xa0 | 3437: SHL | 3438: SUB | 3439: DUP1 | 3440: PUSH32 0x0000000000000000000000000000000000000000000000000000000000000000 | 3473: AND | 3474: CALLER | 3475: EQ | 3476: ISZERO | 3477: SWAP1 | 3478: DUP2 | 3479: PUSH2 0x0e73 | 3482: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
3483: JUMPDEST | 3484: POP | 3485: PUSH2 0x0e62 | 3488: JUMPI    ;; CometWithExtendedAssetList.pause: if (msg.sender != governor && msg.sender != pauseGuardian) revert Unaut…
3489: PUSH32 0x3be39979091ae7ca962aa1c44e645f2df3c221b79f324afa5f44aedc8d2f690d | 3522: SWAP5 | 3523: PUSH2 0x0e5d | 3526: SWAP3 | 3527: PUSH2 0x0e28 | 3530: PUSH2 0x0de5 | 3533: PUSH1 0x00 | 3535: PUSH2 0x0dd7 | 3538: DUP9 | 3539: PUSH2 0x2b6e | 3542: JUMP    ;; CometWithExtendedAssetList.pause: toUInt8(supplyPaused)
3543: JUMPDEST | 3544: SWAP1 | 3545: PUSH1 0xff | 3547: DUP1 | 3548: DUP1 | 3549: SWAP4 | 3550: AND | 3551: SWAP2 | 3552: AND | 3553: SHL | 3554: AND | 3555: SWAP1 | 3556: JUMP    ;; CometCore helper: 0
3557: JUMPDEST | 3558: PUSH2 0x0df3 | 3561: PUSH1 0x01 | 3563: PUSH2 0x0dd7 | 3566: DUP11 | 3567: PUSH2 0x2b6e | 3570: JUMP    ;; CometWithExtendedAssetList.pause: toUInt8(transferPaused)
3571: JUMPDEST | 3572: OR | 3573: PUSH2 0x0e02 | 3576: PUSH1 0x02 | 3578: PUSH2 0x0dd7 | 3581: DUP6 | 3582: PUSH2 0x2b6e | 3585: JUMP    ;; CometWithExtendedAssetList.pause: toUInt8(withdrawPaused)
3586: JUMPDEST | 3587: OR | 3588: PUSH2 0x0e11 | 3591: PUSH1 0x03 | 3593: PUSH2 0x0dd7 | 3596: DUP7 | 3597: PUSH2 0x2b6e | 3600: JUMP    ;; CometWithExtendedAssetList.pause: toUInt8(absorbPaused)
3601: JUMPDEST | 3602: OR | 3603: PUSH2 0x0e20 | 3606: PUSH1 0x04 | 3608: PUSH2 0x0dd7 | 3611: DUP8 | 3612: PUSH2 0x2b6e | 3615: JUMP    ;; CometWithExtendedAssetList.pause: toUInt8(buyPaused)
3616: JUMPDEST | 3617: OR | 3618: PUSH1 0x01 | 3620: PUSH2 0x2b4b | 3623: JUMP    ;; CometWithExtendedAssetList.pause: pauseFlags = uint8(0) | (toUInt8(supplyPaused) << PAUSE_SUPPLY_OFFSET) …
3624: JUMPDEST | 3625: PUSH1 0x40 | 3627: MLOAD | 3628: SWAP6 | 3629: DUP7 | 3630: SWAP6 | 3631: DUP7 | 3632: SWAP4 | 3633: SWAP1 | 3634: SWAP6 | 3635: SWAP5 | 3636: SWAP2 | 3637: SWAP3 | 3638: PUSH1 0x80 | 3640: SWAP4 | 3641: PUSH1 0xa0 | 3643: DUP7 | 3644: ADD | 3645: SWAP8 | 3646: ISZERO | 3647: ISZERO | 3648: DUP7 | 3649: MSTORE | 3650: ISZERO | 3651: ISZERO | 3652: PUSH1 0x20 | 3654: DUP7 | 3655: ADD | 3656: MSTORE | 3657: ISZERO | 3658: ISZERO | 3659: PUSH1 0x40 | 3661: DUP6 | 3662: ADD | 3663: MSTORE | 3664: ISZERO | 3665: ISZERO | 3666: PUSH1 0x60 | 3668: DUP5 | 3669: ADD | 3670: MSTORE | 3671: ISZERO | 3672: ISZERO | 3673: SWAP2 | 3674: ADD | 3675: MSTORE | 3676: JUMP    ;; CometCore helper: 4
3677: JUMPDEST | 3678: SUB | 3679: SWAP1 | 3680: LOG1 | 3681: STOP    ;; LOG1 ;; CometWithExtendedAssetList.pause: PauseAction(supplyPaused, transferPaused, withdrawPaused, absorbPaused,…
3682: JUMPDEST | 3683: PUSH1 0x40 | 3685: MLOAD | 3686: PUSH3 0x82b429 | 3690: PUSH1 0xe8 | 3692: SHL | 3693: DUP2 | 3694: MSTORE | 3695: PUSH1 0x04 | 3697: SWAP1 | 3698: REVERT    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
3699: JUMPDEST | 3700: SWAP1 | 3701: POP | 3702: PUSH32 0x0000000000000000000000000000000000000000000000000000000000000000 | 3735: AND | 3736: CALLER | 3737: EQ | 3738: ISZERO | 3739: CODESIZE | 3740: PUSH2 0x0d9b | 3743: JUMP    ;; CometWithExtendedAssetList.pause: msg.sender != governor && msg.sender != pauseGuardian
3744: JUMPDEST | 3745: POP | 3746: CALLVALUE | 3747: PUSH2 0x0582 | 3750: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
3751: PUSH1 0x00 | 3753: CALLDATASIZE | 3754: PUSH1 0x03 | 3756: NOT | 3757: ADD | 3758: SLT | 3759: PUSH2 0x0582 | 3762: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
3763: PUSH1 0x40 | 3765: MLOAD | 3766: PUSH32 0x0000000000000000000000000000000000000000000000000000000000000000 | 3799: PUSH1 0x01 | 3801: PUSH1 0x01 | 3803: PUSH1 0xa0 | 3805: SHL | 3806: SUB | 3807: AND | 3808: DUP2 | 3809: MSTORE | 3810: PUSH1 0x20 | 3812: SWAP1 | 3813: RETURN    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
3814: JUMPDEST | 3815: POP | 3816: CALLVALUE | 3817: PUSH2 0x0582 | 3820: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
3821: PUSH1 0x20 | 3823: CALLDATASIZE | 3824: PUSH1 0x03 | 3826: NOT | 3827: ADD | 3828: SLT | 3829: PUSH2 0x0582 | 3832: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
3833: PUSH1 0x04 | 3835: CALLDATALOAD | 3836: PUSH2 0x0f04 | 3839: DUP2 | 3840: PUSH2 0x0571 | 3843: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
3844: JUMPDEST | 3845: PUSH1 0x01 | 3847: PUSH1 0x01 | 3849: PUSH1 0xa0 | 3851: SHL | 3852: SUB | 3853: AND | 3854: PUSH1 0x00 | 3856: SWAP1 | 3857: DUP2 | 3858: MSTORE | 3859: PUSH1 0x02 | 3861: PUSH1 0x20 | 3863: MSTORE | 3864: PUSH1 0x40 | 3866: SWAP1 | 3867: DUP2 | 3868: SWAP1 | 3869: KECCAK256 | 3870: SLOAD | 3871: SWAP1 | 3872: MLOAD | 3873: SWAP1 | 3874: DUP2 | 3875: SWAP1 | 3876: PUSH2 0x0a0a | 3879: SWAP1 | 3880: PUSH1 0x80 | 3882: DUP2 | 3883: SWAP1 | 3884: SHR | 3885: SWAP1 | 3886: PUSH1 0x01 | 3888: PUSH1 0x01 | 3890: PUSH1 0x80 | 3892: SHL | 3893: SUB | 3894: AND | 3895: DUP4 | 3896: PUSH2 0x099f | 3899: JUMP    ;; KECCAK256,SLOAD ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
3900: JUMPDEST | 3901: POP | 3902: CALLVALUE | 3903: PUSH2 0x0582 | 3906: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
3907: PUSH1 0x00 | 3909: CALLDATASIZE | 3910: PUSH1 0x03 | 3912: NOT | 3913: ADD | 3914: SLT | 3915: PUSH2 0x0582 | 3918: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
3919: PUSH1 0x20 | 3921: PUSH1 0x40 | 3923: MLOAD | 3924: PUSH32 0x0000000000000000000000000000000000000000000000000000000000000000 | 3957: DUP2 | 3958: MSTORE | 3959: RETURN    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
3960: JUMPDEST | 3961: POP | 3962: CALLVALUE | 3963: PUSH2 0x0582 | 3966: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
3967: PUSH1 0x00 | 3969: CALLDATASIZE | 3970: PUSH1 0x03 | 3972: NOT | 3973: ADD | 3974: SLT | 3975: PUSH2 0x0582 | 3978: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
3979: PUSH1 0x20 | 3981: PUSH1 0x04 | 3983: PUSH1 0x01 | 3985: SLOAD | 3986: PUSH1 0xf8 | 3988: SHR | 3989: AND | 3990: ISZERO | 3991: ISZERO | 3992: PUSH1 0x40 | 3994: MLOAD | 3995: SWAP1 | 3996: DUP2 | 3997: MSTORE | 3998: RETURN    ;; SLOAD ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
3999: JUMPDEST | 4000: POP | 4001: CALLVALUE | 4002: PUSH2 0x0582 | 4005: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
4006: PUSH1 0x20 | 4008: CALLDATASIZE | 4009: PUSH1 0x03 | 4011: NOT | 4012: ADD | 4013: SLT | 4014: PUSH2 0x0582 | 4017: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
4018: PUSH1 0x20 | 4020: PUSH2 0x05e0 | 4023: PUSH1 0x04 | 4025: CALLDATALOAD | 4026: PUSH2 0x0fc2 | 4029: DUP2 | 4030: PUSH2 0x0571 | 4033: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
4034: JUMPDEST | 4035: PUSH2 0x474c | 4038: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
4039: JUMPDEST | 4040: POP | 4041: CALLVALUE | 4042: PUSH2 0x0582 | 4045: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
4046: PUSH1 0x00 | 4048: CALLDATASIZE | 4049: PUSH1 0x03 | 4051: NOT | 4052: ADD | 4053: SLT | 4054: PUSH2 0x0582 | 4057: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
4058: PUSH1 0x20 | 4060: PUSH1 0x40 | 4062: MLOAD | 4063: PUSH32 0x0000000000000000000000000000000000000000000000000000000000000000 | 4096: DUP2 | 4097: MSTORE | 4098: RETURN    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
4099: JUMPDEST | 4100: POP | 4101: CALLVALUE | 4102: PUSH2 0x0582 | 4105: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
4106: PUSH1 0x40 | 4108: CALLDATASIZE | 4109: PUSH1 0x03 | 4111: NOT | 4112: ADD | 4113: SLT | 4114: PUSH2 0x0582 | 4117: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
4118: PUSH1 0x20 | 4120: PUSH2 0x05e0 | 4123: PUSH1 0x04 | 4125: CALLDATALOAD | 4126: PUSH2 0x1026 | 4129: DUP2 | 4130: PUSH2 0x0571 | 4133: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
4134: JUMPDEST | 4135: PUSH1 0x24 | 4137: CALLDATALOAD | 4138: SWAP1 | 4139: PUSH2 0x462d | 4142: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
4143: JUMPDEST | 4144: POP | 4145: CALLVALUE | 4146: PUSH2 0x0582 | 4149: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
4150: PUSH1 0x00 | 4152: CALLDATASIZE | 4153: PUSH1 0x03 | 4155: NOT | 4156: ADD | 4157: SLT | 4158: PUSH2 0x0582 | 4161: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
4162: PUSH1 0x20 | 4164: PUSH2 0x05e0 | 4167: PUSH2 0x23ec | 4170: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
4171: JUMPDEST | 4172: POP | 4173: CALLVALUE | 4174: PUSH2 0x0582 | 4177: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
4178: PUSH1 0x00 | 4180: CALLDATASIZE | 4181: PUSH1 0x03 | 4183: NOT | 4184: ADD | 4185: SLT | 4186: PUSH2 0x0582 | 4189: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
4190: PUSH1 0x20 | 4192: PUSH1 0x40 | 4194: MLOAD | 4195: PUSH32 0x0000000000000000000000000000000000000000000000000000000000000000 | 4228: DUP2 | 4229: MSTORE | 4230: RETURN    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
4231: JUMPDEST | 4232: POP | 4233: CALLVALUE | 4234: PUSH2 0x0582 | 4237: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
4238: PUSH1 0x00 | 4240: CALLDATASIZE | 4241: PUSH1 0x03 | 4243: NOT | 4244: ADD | 4245: SLT | 4246: PUSH2 0x0582 | 4249: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
4250: PUSH1 0x20 | 4252: PUSH7 0x038d7ea4c68000 | 4260: PUSH2 0x06ca | 4263: PUSH2 0x10ae | 4266: PUSH2 0x1dbe | 4269: JUMP    ;; CometWithExtendedAssetList.totalBorrow: getNowInternal()
4270: JUMPDEST | 4271: PUSH2 0x10cb | 4274: PUSH1 0x01 | 4276: SLOAD | 4277: SWAP2 | 4278: PUSH2 0x06ab | 4281: PUSH5 0xffffffffff | 4287: SWAP2 | 4288: DUP3 | 4289: DUP6 | 4290: PUSH1 0xd0 | 4292: SHR | 4293: AND | 4294: SWAP1 | 4295: PUSH2 0x1e49 | 4298: JUMP    ;; SLOAD ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
4299: JUMPDEST | 4300: PUSH1 0x01 | 4302: PUSH1 0x01 | 4304: PUSH1 0x40 | 4306: SHL | 4307: SUB | 4308: AND | 4309: SWAP2 | 4310: PUSH1 0x68 | 4312: SHR | 4313: PUSH1 0x01 | 4315: PUSH1 0x01 | 4317: PUSH1 0x68 | 4319: SHL | 4320: SUB | 4321: AND | 4322: SWAP1 | 4323: POP | 4324: PUSH2 0x1e77 | 4327: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
4328: JUMPDEST | 4329: POP | 4330: CALLVALUE | 4331: PUSH2 0x0582 | 4334: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
4335: PUSH1 0x00 | 4337: CALLDATASIZE | 4338: PUSH1 0x03 | 4340: NOT | 4341: ADD | 4342: SLT | 4343: PUSH2 0x0582 | 4346: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
4347: PUSH1 0x20 | 4349: PUSH1 0x08 | 4351: PUSH1 0x01 | 4353: SLOAD | 4354: PUSH1 0xf8 | 4356: SHR | 4357: AND | 4358: ISZERO | 4359: ISZERO | 4360: PUSH1 0x40 | 4362: MLOAD | 4363: SWAP1 | 4364: DUP2 | 4365: MSTORE | 4366: RETURN    ;; SLOAD ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
4367: JUMPDEST | 4368: POP | 4369: CALLVALUE | 4370: PUSH2 0x0582 | 4373: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
4374: PUSH2 0x0904 | 4377: PUSH2 0x1123 | 4380: CALLDATASIZE | 4381: PUSH1 0x04 | 4383: PUSH2 0x08a7 | 4386: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
4387: JUMPDEST | 4388: SWAP3 | 4389: PUSH2 0x112f | 4392: SWAP3 | 4393: SWAP2 | 4394: SWAP3 | 4395: PUSH2 0x2fd5 | 4398: JUMP    ;; CometWithExtendedAssetList.nonReentrant: modifier nonReentrant() { nonReentrantBefore(); _; nonReentrantAfter();…
4399: JUMPDEST | 4400: CALLER | 4401: PUSH2 0x2f23 | 4404: JUMP    ;; CometWithExtendedAssetList.nonReentrant: _
4405: JUMPDEST | 4406: POP | 4407: CALLVALUE | 4408: PUSH2 0x0582 | 4411: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
4412: PUSH1 0x00 | 4414: CALLDATASIZE | 4415: PUSH1 0x03 | 4417: NOT | 4418: ADD | 4419: SLT | 4420: PUSH2 0x0582 | 4423: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
4424: PUSH1 0x20 | 4426: PUSH1 0x40 | 4428: MLOAD | 4429: PUSH32 0x0000000000000000000000000000000000000000000000000000000000000000 | 4462: DUP2 | 4463: MSTORE | 4464: RETURN    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
4465: JUMPDEST | 4466: POP | 4467: CALLVALUE | 4468: PUSH2 0x0582 | 4471: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
4472: PUSH1 0x00 | 4474: CALLDATASIZE | 4475: PUSH1 0x03 | 4477: NOT | 4478: ADD | 4479: SLT | 4480: PUSH2 0x0582 | 4483: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
4484: PUSH1 0x20 | 4486: PUSH1 0x40 | 4488: MLOAD | 4489: PUSH32 0x0000000000000000000000000000000000000000000000000000000000000000 | 4522: DUP2 | 4523: MSTORE | 4524: RETURN    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
4525: JUMPDEST | 4526: POP | 4527: CALLVALUE | 4528: PUSH2 0x0582 | 4531: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
4532: PUSH1 0x00 | 4534: CALLDATASIZE | 4535: PUSH1 0x03 | 4537: NOT | 4538: ADD | 4539: SLT | 4540: PUSH2 0x0582 | 4543: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
4544: PUSH1 0x20 | 4546: PUSH1 0x40 | 4548: MLOAD | 4549: PUSH32 0x0000000000000000000000000000000000000000000000000000000000000000 | 4582: DUP2 | 4583: MSTORE | 4584: RETURN    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
4585: JUMPDEST | 4586: POP | 4587: CALLVALUE | 4588: PUSH2 0x0582 | 4591: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
4592: PUSH1 0x00 | 4594: CALLDATASIZE | 4595: PUSH1 0x03 | 4597: NOT | 4598: ADD | 4599: SLT | 4600: PUSH2 0x0582 | 4603: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
4604: PUSH1 0x20 | 4606: PUSH1 0x40 | 4608: MLOAD | 4609: PUSH32 0x0000000000000000000000000000000000000000000000000000000000000000 | 4642: DUP2 | 4643: MSTORE | 4644: RETURN    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
4645: JUMPDEST | 4646: POP | 4647: CALLVALUE | 4648: PUSH2 0x0582 | 4651: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
4652: PUSH1 0x20 | 4654: CALLDATASIZE | 4655: PUSH1 0x03 | 4657: NOT | 4658: ADD | 4659: SLT | 4660: PUSH2 0x0582 | 4663: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
4664: PUSH1 0x20 | 4666: PUSH2 0x1244 | 4669: PUSH1 0x04 | 4671: CALLDATALOAD | 4672: PUSH2 0x22b6 | 4675: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
4676: JUMPDEST | 4677: PUSH1 0x40 | 4679: MLOAD | 4680: PUSH1 0x01 | 4682: PUSH1 0x01 | 4684: PUSH1 0x40 | 4686: SHL | 4687: SUB | 4688: SWAP1 | 4689: SWAP2 | 4690: AND | 4691: DUP2 | 4692: MSTORE | 4693: RETURN    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
4694: JUMPDEST | 4695: POP | 4696: CALLVALUE | 4697: PUSH2 0x0582 | 4700: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
4701: PUSH1 0x20 | 4703: CALLDATASIZE | 4704: PUSH1 0x03 | 4706: NOT | 4707: ADD | 4708: SLT | 4709: PUSH2 0x0582 | 4712: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
4713: PUSH1 0x20 | 4715: PUSH2 0x05e0 | 4718: PUSH1 0x04 | 4720: CALLDATALOAD | 4721: PUSH2 0x1279 | 4724: DUP2 | 4725: PUSH2 0x0571 | 4728: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
4729: JUMPDEST | 4730: PUSH2 0x2559 | 4733: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
4734: JUMPDEST | 4735: POP | 4736: CALLVALUE | 4737: PUSH2 0x0582 | 4740: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
4741: PUSH1 0x20 | 4743: PUSH1 0xff | 4745: PUSH2 0x12b3 | 4748: PUSH2 0x1296 | 4751: CALLDATASIZE | 4752: PUSH1 0x04 | 4754: PUSH2 0x0954 | 4757: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
4758: JUMPDEST | 4759: PUSH1 0x01 | 4761: PUSH1 0x01 | 4763: PUSH1 0xa0 | 4765: SHL | 4766: SUB | 4767: SWAP1 | 4768: SWAP2 | 4769: AND | 4770: PUSH1 0x00 | 4772: SWAP1 | 4773: DUP2 | 4774: MSTORE | 4775: PUSH1 0x03 | 4777: DUP6 | 4778: MSTORE | 4779: PUSH1 0x40 | 4781: SWAP1 | 4782: KECCAK256 | 4783: PUSH2 0x097c | 4786: JUMP    ;; KECCAK256 ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
4787: JUMPDEST | 4788: SLOAD | 4789: AND | 4790: PUSH1 0x40 | 4792: MLOAD | 4793: SWAP1 | 4794: ISZERO | 4795: ISZERO | 4796: DUP2 | 4797: MSTORE | 4798: RETURN    ;; SLOAD ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
4799: JUMPDEST | 4800: POP | 4801: CALLVALUE | 4802: PUSH2 0x0582 | 4805: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
4806: PUSH1 0x00 | 4808: CALLDATASIZE | 4809: PUSH1 0x03 | 4811: NOT | 4812: ADD | 4813: SLT | 4814: PUSH2 0x0582 | 4817: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
4818: PUSH1 0x20 | 4820: PUSH1 0x02 | 4822: PUSH1 0x01 | 4824: SLOAD | 4825: PUSH1 0xf8 | 4827: SHR | 4828: AND | 4829: ISZERO | 4830: ISZERO | 4831: PUSH1 0x40 | 4833: MLOAD | 4834: SWAP1 | 4835: DUP2 | 4836: MSTORE | 4837: RETURN    ;; SLOAD ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
4838: JUMPDEST | 4839: POP | 4840: CALLVALUE | 4841: PUSH2 0x0582 | 4844: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
4845: PUSH1 0x00 | 4847: CALLDATASIZE | 4848: PUSH1 0x03 | 4850: NOT | 4851: ADD | 4852: SLT | 4853: PUSH2 0x0582 | 4856: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
4857: PUSH1 0x20 | 4859: PUSH1 0x40 | 4861: MLOAD | 4862: PUSH1 0xff | 4864: PUSH32 0x0000000000000000000000000000000000000000000000000000000000000000 | 4897: AND | 4898: DUP2 | 4899: MSTORE | 4900: RETURN    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
4901: JUMPDEST | 4902: POP | 4903: CALLVALUE | 4904: PUSH2 0x0582 | 4907: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
4908: PUSH1 0x00 | 4910: CALLDATASIZE | 4911: PUSH1 0x03 | 4913: NOT | 4914: ADD | 4915: SLT | 4916: PUSH2 0x0582 | 4919: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
4920: PUSH1 0x20 | 4922: PUSH1 0x40 | 4924: MLOAD | 4925: PUSH32 0x0000000000000000000000000000000000000000000000000000000000000000 | 4958: DUP2 | 4959: MSTORE | 4960: RETURN    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
4961: JUMPDEST | 4962: POP | 4963: CALLVALUE | 4964: PUSH2 0x0582 | 4967: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
4968: PUSH1 0x40 | 4970: CALLDATASIZE | 4971: PUSH1 0x03 | 4973: NOT | 4974: ADD | 4975: SLT | 4976: PUSH2 0x0582 | 4979: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
4980: PUSH2 0x0844 | 4983: PUSH1 0x04 | 4985: CALLDATALOAD | 4986: PUSH2 0x1382 | 4989: DUP2 | 4990: PUSH2 0x0571 | 4993: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
4994: JUMPDEST | 4995: PUSH2 0x138a | 4998: PUSH2 0x2fd5 | 5001: JUMP    ;; CometWithExtendedAssetList.nonReentrant: modifier nonReentrant() { nonReentrantBefore(); _; nonReentrantAfter();…
5002: JUMPDEST | 5003: PUSH1 0x24 | 5005: CALLDATALOAD | 5006: SWAP1 | 5007: PUSH32 0x0000000000000000000000000000000000000000000000000000000000000000 | 5040: SWAP1 | 5041: CALLER | 5042: CALLER | 5043: PUSH2 0x38a0 | 5046: JUMP    ;; CometWithExtendedAssetList.transfer: msg.sender
5047: JUMPDEST | 5048: POP | 5049: CALLVALUE | 5050: PUSH2 0x0582 | 5053: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
5054: PUSH1 0x00 | 5056: CALLDATASIZE | 5057: PUSH1 0x03 | 5059: NOT | 5060: ADD | 5061: SLT | 5062: PUSH2 0x0582 | 5065: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
5066: PUSH1 0x20 | 5068: PUSH1 0x40 | 5070: MLOAD | 5071: PUSH32 0x0000000000000000000000000000000000000000000000000000000000000000 | 5104: DUP2 | 5105: MSTORE | 5106: RETURN    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
5107: JUMPDEST | 5108: POP | 5109: CALLVALUE | 5110: PUSH2 0x0582 | 5113: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
5114: PUSH2 0x1404 | 5117: CALLDATASIZE | 5118: PUSH1 0x04 | 5120: PUSH2 0x07d1 | 5123: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
5124: JUMPDEST | 5125: SWAP2 | 5126: SWAP1 | 5127: PUSH1 0x01 | 5129: PUSH1 0x01 | 5131: PUSH1 0xa0 | 5133: SHL | 5134: SUB | 5135: SWAP1 | 5136: PUSH32 0x0000000000000000000000000000000000000000000000000000000000000000 | 5169: DUP3 | 5170: AND | 5171: CALLER | 5172: SUB | 5173: PUSH2 0x0e62 | 5176: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
5177: AND | 5178: SWAP2 | 5179: DUP3 | 5180: EXTCODESIZE | 5181: ISZERO | 5182: PUSH2 0x0582 | 5185: JUMPI    ;; EXTCODESIZE ;; CometWithExtendedAssetList.approveThis: IERC20NonStandard(asset).approve(manager, amount)
5186: PUSH2 0x1465 | 5189: SWAP3 | 5190: PUSH1 0x00 | 5192: SWAP3 | 5193: DUP4 | 5194: PUSH1 0x40 | 5196: MLOAD | 5197: DUP1 | 5198: SWAP7 | 5199: DUP2 | 5200: SWAP6 | 5201: DUP3 | 5202: SWAP5 | 5203: PUSH4 0x095ea7b3 | 5208: PUSH1 0xe0 | 5210: SHL | 5211: DUP5 | 5212: MSTORE | 5213: PUSH1 0x04 | 5215: DUP5 | 5216: ADD | 5217: PUSH2 0x3ed6 | 5220: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
5221: JUMPDEST | 5222: SUB | 5223: SWAP3 | 5224: GAS | 5225: CALL | 5226: DUP1 | 5227: ISZERO | 5228: PUSH2 0x148b | 5231: JUMPI    ;; CALL ;; CometWithExtendedAssetList.approveThis: IERC20NonStandard(asset).approve(manager, amount)
5232: JUMPDEST | 5233: PUSH2 0x1476 | 5236: JUMPI    ;; CometWithExtendedAssetList.approveThis: IERC20NonStandard(asset).approve(manager, amount)
5237: STOP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
5238: JUMPDEST | 5239: DUP1 | 5240: PUSH2 0x1485 | 5243: PUSH1 0x00 | 5245: PUSH2 0x0016 | 5248: SWAP4 | 5249: PUSH2 0x1b46 | 5252: JUMP    ;; CometWithExtendedAssetList.approveThis: IERC20NonStandard(asset).approve(manager, amount)
5253: JUMPDEST | 5254: DUP1 | 5255: PUSH2 0x05b9 | 5258: JUMP    ;; CometWithExtendedAssetList.approveThis: IERC20NonStandard(asset).approve(manager, amount)
5259: JUMPDEST | 5260: PUSH2 0x1493 | 5263: PUSH2 0x1bfe | 5266: JUMP    ;; CometWithExtendedAssetList.approveThis: IERC20NonStandard(asset).approve(manager, amount)
5267: JUMPDEST | 5268: PUSH2 0x1470 | 5271: JUMP    ;; CometWithExtendedAssetList.approveThis: IERC20NonStandard(asset).approve(manager, amount)
5272: JUMPDEST | 5273: POP | 5274: CALLVALUE | 5275: PUSH2 0x0582 | 5278: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
5279: PUSH1 0x20 | 5281: CALLDATASIZE | 5282: PUSH1 0x03 | 5284: NOT | 5285: ADD | 5286: SLT | 5287: PUSH2 0x0582 | 5290: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
5291: PUSH2 0x0016 | 5294: PUSH1 0x04 | 5296: CALLDATALOAD | 5297: PUSH2 0x14b9 | 5300: DUP2 | 5301: PUSH2 0x0571 | 5304: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
5305: JUMPDEST | 5306: PUSH2 0x14c1 | 5309: PUSH2 0x1ece | 5312: JUMP    ;; CometWithExtendedAssetList.accrueAccount: function accrueAccount(address account) override external { accrueInter…
5313: JUMPDEST | 5314: PUSH1 0x01 | 5316: DUP1 | 5317: PUSH1 0xa0 | 5319: SHL | 5320: SUB | 5321: DUP2 | 5322: AND | 5323: PUSH1 0x00 | 5325: MSTORE | 5326: PUSH1 0x05 | 5328: PUSH1 0x20 | 5330: MSTORE | 5331: PUSH1 0x40 | 5333: PUSH1 0x00 | 5335: KECCAK256 | 5336: PUSH2 0x1528 | 5339: PUSH1 0x40 | 5341: MLOAD | 5342: SWAP2 | 5343: PUSH2 0x14e9 | 5346: PUSH1 0xa0 | 5348: DUP5 | 5349: PUSH2 0x1b46 | 5352: JUMP    ;; KECCAK256 ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
5353: JUMPDEST | 5354: SLOAD | 5355: PUSH1 0x0c | 5357: DUP2 | 5358: SWAP1 | 5359: SIGNEXTEND | 5360: DUP4 | 5361: MSTORE | 5362: PUSH1 0x01 | 5364: PUSH1 0x01 | 5366: PUSH1 0x40 | 5368: SHL | 5369: SUB | 5370: PUSH1 0x68 | 5372: DUP3 | 5373: SWAP1 | 5374: SHR | 5375: DUP2 | 5376: AND | 5377: PUSH1 0x20 | 5379: DUP6 | 5380: ADD | 5381: MSTORE | 5382: PUSH1 0xa8 | 5384: DUP3 | 5385: SWAP1 | 5386: SHR | 5387: AND | 5388: PUSH1 0x40 | 5390: DUP5 | 5391: ADD | 5392: MSTORE | 5393: PUSH2 0xffff | 5396: PUSH1 0xe8 | 5398: DUP3 | 5399: SWAP1 | 5400: SHR | 5401: AND | 5402: PUSH1 0x60 | 5404: DUP5 | 5405: ADD | 5406: MSTORE | 5407: PUSH1 0xf8 | 5409: SHR | 5410: PUSH1 0x80 | 5412: DUP4 | 5413: ADD | 5414: MSTORE | 5415: JUMP    ;; SLOAD ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
5416: JUMPDEST | 5417: DUP1 | 5418: MLOAD | 5419: PUSH1 0x0c | 5421: SIGNEXTEND | 5422: SWAP2 | 5423: PUSH2 0x2db5 | 5426: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
5427: JUMPDEST | 5428: POP | 5429: CALLVALUE | 5430: PUSH2 0x0582 | 5433: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
5434: PUSH2 0x0904 | 5437: PUSH2 0x1547 | 5440: CALLDATASIZE | 5441: PUSH1 0x04 | 5443: PUSH2 0x08a7 | 5446: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
5447: JUMPDEST | 5448: SWAP3 | 5449: PUSH2 0x1553 | 5452: SWAP3 | 5453: SWAP2 | 5454: SWAP3 | 5455: PUSH2 0x2fd5 | 5458: JUMP    ;; CometWithExtendedAssetList.nonReentrant: modifier nonReentrant() { nonReentrantBefore(); _; nonReentrantAfter();…
5459: JUMPDEST | 5460: CALLER | 5461: PUSH2 0x38a0 | 5464: JUMP    ;; CometWithExtendedAssetList.nonReentrant: _
5465: JUMPDEST | 5466: POP | 5467: CALLVALUE | 5468: PUSH2 0x0582 | 5471: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
5472: PUSH2 0x0904 | 5475: PUSH2 0x156d | 5478: CALLDATASIZE | 5479: PUSH1 0x04 | 5481: PUSH2 0x07d1 | 5484: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
5485: JUMPDEST | 5486: SWAP2 | 5487: PUSH2 0x1576 | 5490: PUSH2 0x2fd5 | 5493: JUMP    ;; CometWithExtendedAssetList.nonReentrant: modifier nonReentrant() { nonReentrantBefore(); _; nonReentrantAfter();…
5494: JUMPDEST | 5495: CALLER | 5496: CALLER | 5497: PUSH2 0x3ced | 5500: JUMP    ;; CometWithExtendedAssetList.withdrawTo: msg.sender
5501: JUMPDEST | 5502: POP | 5503: CALLVALUE | 5504: PUSH2 0x0582 | 5507: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
5508: PUSH1 0x40 | 5510: CALLDATASIZE | 5511: PUSH1 0x03 | 5513: NOT | 5514: ADD | 5515: SLT | 5516: PUSH2 0x0582 | 5519: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
5520: PUSH1 0x04 | 5522: CALLDATALOAD | 5523: PUSH2 0x159b | 5526: DUP2 | 5527: PUSH2 0x0571 | 5530: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
5531: JUMPDEST | 5532: PUSH1 0x24 | 5534: CALLDATALOAD | 5535: SWAP1 | 5536: PUSH1 0x01 | 5538: PUSH1 0x01 | 5540: PUSH1 0x40 | 5542: SHL | 5543: SUB | 5544: SWAP1 | 5545: DUP2 | 5546: DUP4 | 5547: GT | 5548: PUSH2 0x0582 | 5551: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
5552: CALLDATASIZE | 5553: PUSH1 0x23 | 5555: DUP5 | 5556: ADD | 5557: SLT | 5558: ISZERO | 5559: PUSH2 0x0582 | 5562: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
5563: DUP3 | 5564: PUSH1 0x04 | 5566: ADD | 5567: CALLDATALOAD | 5568: SWAP2 | 5569: DUP3 | 5570: GT | 5571: PUSH2 0x0582 | 5574: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
5575: CALLDATASIZE | 5576: PUSH1 0x24 | 5578: DUP4 | 5579: PUSH1 0x05 | 5581: SHL | 5582: DUP6 | 5583: ADD | 5584: ADD | 5585: GT | 5586: PUSH2 0x0582 | 5589: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
5590: PUSH1 0x24 | 5592: PUSH2 0x0016 | 5595: SWAP4 | 5596: ADD | 5597: SWAP1 | 5598: PUSH2 0x4118 | 5601: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
5602: JUMPDEST | 5603: POP | 5604: CALLVALUE | 5605: PUSH2 0x0582 | 5608: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
5609: PUSH1 0x00 | 5611: CALLDATASIZE | 5612: PUSH1 0x03 | 5614: NOT | 5615: ADD | 5616: SLT | 5617: PUSH2 0x0582 | 5620: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
5621: PUSH1 0x40 | 5623: MLOAD | 5624: PUSH32 0x0000000000000000000000000000000000000000000000000000000000000000 | 5657: PUSH1 0x01 | 5659: PUSH1 0x01 | 5661: PUSH1 0xa0 | 5663: SHL | 5664: SUB | 5665: AND | 5666: DUP2 | 5667: MSTORE | 5668: PUSH1 0x20 | 5670: SWAP1 | 5671: RETURN    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
5672: JUMPDEST | 5673: POP | 5674: CALLVALUE | 5675: PUSH2 0x0582 | 5678: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
5679: PUSH1 0x20 | 5681: CALLDATASIZE | 5682: PUSH1 0x03 | 5684: NOT | 5685: ADD | 5686: SLT | 5687: PUSH2 0x0582 | 5690: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
5691: PUSH1 0x04 | 5693: CALLDATALOAD | 5694: PUSH2 0x1646 | 5697: DUP2 | 5698: PUSH2 0x0571 | 5701: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
5702: JUMPDEST | 5703: PUSH1 0x01 | 5705: DUP1 | 5706: PUSH1 0xa0 | 5708: SHL | 5709: SUB | 5710: AND | 5711: PUSH1 0x00 | 5713: MSTORE | 5714: PUSH1 0x07 | 5716: PUSH1 0x20 | 5718: MSTORE | 5719: PUSH1 0x80 | 5721: PUSH1 0x40 | 5723: PUSH1 0x00 | 5725: KECCAK256 | 5726: SLOAD | 5727: PUSH1 0x40 | 5729: MLOAD | 5730: SWAP1 | 5731: PUSH4 0xffffffff | 5736: DUP2 | 5737: AND | 5738: DUP3 | 5739: MSTORE | 5740: PUSH1 0x01 | 5742: DUP1 | 5743: PUSH1 0x40 | 5745: SHL | 5746: SUB | 5747: DUP2 | 5748: PUSH1 0x20 | 5750: SHR | 5751: AND | 5752: PUSH1 0x20 | 5754: DUP4 | 5755: ADD | 5756: MSTORE | 5757: PUSH1 0x01 | 5759: DUP1 | 5760: DUP5 | 5761: SHL | 5762: SUB | 5763: DUP2 | 5764: PUSH1 0x60 | 5766: SHR | 5767: AND | 5768: PUSH1 0x40 | 5770: DUP4 | 5771: ADD | 5772: MSTORE | 5773: PUSH1 0xe0 | 5775: SHR | 5776: PUSH1 0x60 | 5778: DUP3 | 5779: ADD | 5780: MSTORE | 5781: RETURN    ;; KECCAK256,SLOAD ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
5782: JUMPDEST | 5783: PUSH1 0xff | 5785: DUP2 | 5786: AND | 5787: SUB | 5788: PUSH2 0x0582 | 5791: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
5792: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
5793: JUMPDEST | 5794: POP | 5795: CALLVALUE | 5796: PUSH2 0x0582 | 5799: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
5800: PUSH1 0x20 | 5802: CALLDATASIZE | 5803: PUSH1 0x03 | 5805: NOT | 5806: ADD | 5807: SLT | 5808: PUSH2 0x0582 | 5811: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
5812: PUSH2 0x0a0a | 5815: PUSH2 0x0c5c | 5818: PUSH1 0x04 | 5820: CALLDATALOAD | 5821: PUSH2 0x16c5 | 5824: DUP2 | 5825: PUSH2 0x1696 | 5828: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
5829: JUMPDEST | 5830: PUSH2 0x1c0b | 5833: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
5834: JUMPDEST | 5835: POP | 5836: CALLVALUE | 5837: PUSH2 0x0582 | 5840: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
5841: PUSH1 0x20 | 5843: PUSH2 0x05af | 5846: PUSH2 0x16e0 | 5849: CALLDATASIZE | 5850: PUSH1 0x04 | 5852: PUSH2 0x0954 | 5855: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
5856: JUMPDEST | 5857: SWAP1 | 5858: PUSH2 0x1b09 | 5861: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
5862: JUMPDEST | 5863: POP | 5864: CALLVALUE | 5865: PUSH2 0x0582 | 5868: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
5869: PUSH1 0x00 | 5871: CALLDATASIZE | 5872: PUSH1 0x03 | 5874: NOT | 5875: ADD | 5876: SLT | 5877: PUSH2 0x0582 | 5880: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
5881: PUSH1 0x20 | 5883: PUSH1 0x10 | 5885: PUSH1 0x01 | 5887: SLOAD | 5888: PUSH1 0xf8 | 5890: SHR | 5891: AND | 5892: ISZERO | 5893: ISZERO | 5894: PUSH1 0x40 | 5896: MLOAD | 5897: SWAP1 | 5898: DUP2 | 5899: MSTORE | 5900: RETURN    ;; SLOAD ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
5901: JUMPDEST | 5902: POP | 5903: CALLVALUE | 5904: PUSH2 0x0582 | 5907: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
5908: PUSH1 0x20 | 5910: CALLDATASIZE | 5911: PUSH1 0x03 | 5913: NOT | 5914: ADD | 5915: SLT | 5916: PUSH2 0x0582 | 5919: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
5920: PUSH1 0x20 | 5922: PUSH2 0x1244 | 5925: PUSH1 0x04 | 5927: CALLDATALOAD | 5928: PUSH2 0x21a6 | 5931: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
5932: JUMPDEST | 5933: POP | 5934: CALLVALUE | 5935: PUSH2 0x0582 | 5938: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
5939: PUSH1 0x20 | 5941: CALLDATASIZE | 5942: PUSH1 0x03 | 5944: NOT | 5945: ADD | 5946: SLT | 5947: PUSH2 0x0582 | 5950: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
5951: PUSH1 0x04 | 5953: CALLDATALOAD | 5954: PUSH2 0x174a | 5957: DUP2 | 5958: PUSH2 0x0571 | 5961: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
5962: JUMPDEST | 5963: PUSH1 0x01 | 5965: DUP1 | 5966: PUSH1 0xa0 | 5968: SHL | 5969: SUB | 5970: AND | 5971: PUSH1 0x00 | 5973: MSTORE | 5974: PUSH1 0x05 | 5976: PUSH1 0x20 | 5978: MSTORE | 5979: PUSH1 0xa0 | 5981: PUSH1 0x40 | 5983: PUSH1 0x00 | 5985: KECCAK256 | 5986: SLOAD | 5987: PUSH1 0x40 | 5989: MLOAD | 5990: SWAP1 | 5991: DUP1 | 5992: PUSH1 0x0c | 5994: SIGNEXTEND | 5995: DUP3 | 5996: MSTORE | 5997: PUSH1 0x01 | 5999: DUP1 | 6000: PUSH1 0x40 | 6002: SHL | 6003: SUB | 6004: DUP1 | 6005: DUP3 | 6006: PUSH1 0x68 | 6008: SHR | 6009: AND | 6010: PUSH1 0x20 | 6012: DUP5 | 6013: ADD | 6014: MSTORE | 6015: DUP2 | 6016: PUSH1 0xa8 | 6018: SHR | 6019: AND | 6020: PUSH1 0x40 | 6022: DUP4 | 6023: ADD | 6024: MSTORE | 6025: PUSH2 0xffff | 6028: DUP2 | 6029: PUSH1 0xe8 | 6031: SHR | 6032: AND | 6033: PUSH1 0x60 | 6035: DUP4 | 6036: ADD | 6037: MSTORE | 6038: PUSH1 0xf8 | 6040: SHR | 6041: PUSH1 0x80 | 6043: DUP3 | 6044: ADD | 6045: MSTORE | 6046: RETURN    ;; KECCAK256,SLOAD ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
6047: JUMPDEST | 6048: POP | 6049: CALLVALUE | 6050: PUSH2 0x0582 | 6053: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
6054: PUSH1 0x00 | 6056: CALLDATASIZE | 6057: PUSH1 0x03 | 6059: NOT | 6060: ADD | 6061: SLT | 6062: PUSH2 0x0582 | 6065: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
6066: PUSH1 0x40 | 6068: MLOAD | 6069: PUSH32 0x0000000000000000000000000000000000000000000000000000000000000000 | 6102: PUSH1 0x01 | 6104: PUSH1 0x01 | 6106: PUSH1 0xa0 | 6108: SHL | 6109: SUB | 6110: AND | 6111: DUP2 | 6112: MSTORE | 6113: PUSH1 0x20 | 6115: SWAP1 | 6116: RETURN    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
6117: JUMPDEST | 6118: POP | 6119: CALLVALUE | 6120: PUSH2 0x0582 | 6123: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
6124: PUSH1 0x40 | 6126: CALLDATASIZE | 6127: PUSH1 0x03 | 6129: NOT | 6130: ADD | 6131: SLT | 6132: PUSH2 0x0582 | 6135: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
6136: PUSH1 0x04 | 6138: CALLDATALOAD | 6139: PUSH2 0x1803 | 6142: DUP2 | 6143: PUSH2 0x0571 | 6146: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
6147: JUMPDEST | 6148: PUSH1 0x24 | 6150: CALLDATALOAD | 6151: SWAP1 | 6152: PUSH1 0x01 | 6154: PUSH1 0x01 | 6156: PUSH1 0xa0 | 6158: SHL | 6159: SUB | 6160: PUSH32 0x0000000000000000000000000000000000000000000000000000000000000000 | 6193: DUP2 | 6194: AND | 6195: CALLER | 6196: SUB | 6197: PUSH2 0x0e62 | 6200: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
6201: PUSH2 0x1840 | 6204: PUSH2 0x2661 | 6207: JUMP    ;; CometWithExtendedAssetList.withdrawReserves: getReserves()
6208: JUMPDEST | 6209: PUSH1 0x00 | 6211: DUP2 | 6212: SLT | 6213: SWAP1 | 6214: DUP2 | 6215: ISZERO | 6216: PUSH2 0x18be | 6219: JUMPI    ;; CometWithExtendedAssetList.withdrawReserves: reserves < 0 || amount > unsigned256(reserves)
6220: JUMPDEST | 6221: POP | 6222: PUSH2 0x18ac | 6225: JUMPI    ;; CometWithExtendedAssetList.withdrawReserves: if (reserves < 0 || amount > unsigned256(reserves)) revert Insufficient…
6226: DUP2 | 6227: PUSH2 0x189e | 6230: DUP5 | 6231: PUSH32 0xec4431f2ba1a9382f6b0c4352b888cba6f7db91667d9f776abe5ad8ddc5401b6 | 6264: SWAP5 | 6265: PUSH32 0x0000000000000000000000000000000000000000000000000000000000000000 | 6298: PUSH2 0x3ef1 | 6301: JUMP    ;; CometWithExtendedAssetList.withdrawReserves: baseToken
6302: JUMPDEST | 6303: PUSH1 0x40 | 6305: MLOAD | 6306: SWAP4 | 6307: DUP5 | 6308: MSTORE | 6309: AND | 6310: SWAP2 | 6311: PUSH1 0x20 | 6313: SWAP1 | 6314: LOG2 | 6315: STOP    ;; LOG2 ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
6316: JUMPDEST | 6317: PUSH1 0x40 | 6319: MLOAD | 6320: PUSH4 0x128bd24d | 6325: PUSH1 0xe3 | 6327: SHL | 6328: DUP2 | 6329: MSTORE | 6330: PUSH1 0x04 | 6332: SWAP1 | 6333: REVERT    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
6334: JUMPDEST | 6335: PUSH2 0x18c8 | 6338: SWAP2 | 6339: POP | 6340: PUSH2 0x4622 | 6343: JUMP    ;; CometWithExtendedAssetList.withdrawReserves: unsigned256(reserves)
6344: JUMPDEST | 6345: DUP4 | 6346: GT | 6347: CODESIZE | 6348: PUSH2 0x184c | 6351: JUMP    ;; CometWithExtendedAssetList.withdrawReserves: reserves < 0 || amount > unsigned256(reserves)
6352: JUMPDEST | 6353: POP | 6354: CALLVALUE | 6355: PUSH2 0x0582 | 6358: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
6359: PUSH1 0x80 | 6361: CALLDATASIZE | 6362: PUSH1 0x03 | 6364: NOT | 6365: ADD | 6366: SLT | 6367: PUSH2 0x0582 | 6370: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
6371: PUSH1 0x04 | 6373: CALLDATALOAD | 6374: PUSH2 0x18ee | 6377: DUP2 | 6378: PUSH2 0x0571 | 6381: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
6382: JUMPDEST | 6383: PUSH1 0x64 | 6385: CALLDATALOAD | 6386: SWAP1 | 6387: PUSH2 0x18fb | 6390: DUP3 | 6391: PUSH2 0x0571 | 6394: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
6395: JUMPDEST | 6396: PUSH2 0x1903 | 6399: PUSH2 0x2fd5 | 6402: JUMP    ;; CometWithExtendedAssetList.nonReentrant: modifier nonReentrant() { nonReentrantBefore(); _; nonReentrantAfter();…
6403: JUMPDEST | 6404: PUSH1 0x10 | 6406: PUSH1 0x01 | 6408: SLOAD | 6409: PUSH1 0xf8 | 6411: SHR | 6412: AND | 6413: PUSH2 0x1a47 | 6416: JUMPI    ;; SLOAD ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
6417: PUSH2 0x1918 | 6420: PUSH2 0x2661 | 6423: JUMP    ;; CometWithExtendedAssetList.buyCollateral: getReserves()
6424: JUMPDEST | 6425: PUSH1 0x00 | 6427: DUP2 | 6428: SLT | 6429: ISZERO | 6430: SWAP1 | 6431: DUP2 | 6432: PUSH2 0x1a1c | 6435: JUMPI    ;; CometWithExtendedAssetList.buyCollateral: reserves >= 0 && uint(reserves) >= targetReserves
6436: JUMPDEST | 6437: POP | 6438: PUSH2 0x1a0a | 6441: JUMPI    ;; CometWithExtendedAssetList.buyCollateral: if (reserves >= 0 && uint(reserves) >= targetReserves) revert NotForSal…
6442: PUSH2 0x1956 | 6445: PUSH1 0x44 | 6447: CALLDATALOAD | 6448: CALLER | 6449: PUSH32 0x0000000000000000000000000000000000000000000000000000000000000000 | 6482: PUSH2 0x33d8 | 6485: JUMP    ;; CometWithExtendedAssetList.buyCollateral: doTransferIn(baseToken, msg.sender, baseAmount)
6486: JUMPDEST | 6487: SWAP1 | 6488: PUSH2 0x1961 | 6491: DUP3 | 6492: DUP3 | 6493: PUSH2 0x462d | 6496: JUMP    ;; CometWithExtendedAssetList.buyCollateral: quoteCollateral(asset, baseAmount)
6497: JUMPDEST | 6498: SWAP3 | 6499: PUSH1 0x24 | 6501: CALLDATALOAD | 6502: DUP5 | 6503: LT | 6504: PUSH2 0x19f8 | 6507: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
6508: PUSH2 0x1974 | 6511: DUP3 | 6512: PUSH2 0x2559 | 6515: JUMP    ;; CometWithExtendedAssetList.buyCollateral: getCollateralReserves(asset)
6516: JUMPDEST | 6517: DUP5 | 6518: GT | 6519: PUSH2 0x18ac | 6522: JUMPI    ;; CometWithExtendedAssetList.buyCollateral: collateralAmount > getCollateralReserves(asset)
6523: PUSH32 0xf891b2a411b0e66a5f0a6ff1368670fefa287a13f541eb633a386a1a9cc7046b | 6556: SWAP2 | 6557: PUSH2 0x19bb | 6560: PUSH2 0x19de | 6563: SWAP3 | 6564: PUSH2 0x19b4 | 6567: PUSH2 0x19af | 6570: DUP9 | 6571: PUSH2 0x2faf | 6574: JUMP    ;; CometWithExtendedAssetList.buyCollateral: safe128(collateralAmount)
6575: JUMPDEST | 6576: PUSH2 0x0993 | 6579: JUMP    ;; CometWithExtendedAssetList.buyCollateral: doTransferOut(asset, recipient, safe128(collateralAmount))
6580: JUMPDEST | 6581: SWAP1 | 6582: DUP4 | 6583: PUSH2 0x3ef1 | 6586: JUMP    ;; CometWithExtendedAssetList.buyCollateral: doTransferOut(asset, recipient, safe128(collateralAmount))
6587: JUMPDEST | 6588: PUSH1 0x40 | 6590: DUP1 | 6591: MLOAD | 6592: SWAP5 | 6593: DUP6 | 6594: MSTORE | 6595: PUSH1 0x20 | 6597: DUP6 | 6598: ADD | 6599: SWAP6 | 6600: SWAP1 | 6601: SWAP6 | 6602: MSTORE | 6603: PUSH1 0x01 | 6605: PUSH1 0x01 | 6607: PUSH1 0xa0 | 6609: SHL | 6610: SUB | 6611: AND | 6612: SWAP4 | 6613: CALLER | 6614: SWAP4 | 6615: SWAP2 | 6616: DUP3 | 6617: SWAP2 | 6618: DUP3 | 6619: ADD | 6620: SWAP1 | 6621: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
6622: JUMPDEST | 6623: SUB | 6624: SWAP1 | 6625: LOG3 | 6626: PUSH2 0x0016 | 6629: PUSH1 0x00 | 6631: PUSH1 0x00 | 6633: DUP1 | 6634: MLOAD | 6635: PUSH1 0x20 | 6637: PUSH2 0x4852 | 6640: DUP4 | 6641: CODECOPY | 6642: DUP2 | 6643: MLOAD | 6644: SWAP2 | 6645: MSTORE | 6646: SSTORE | 6647: JUMP    ;; LOG3,SSTORE ;; CometWithExtendedAssetList.buyCollateral: BuyCollateral(msg.sender, asset, baseAmount, collateralAmount)
6648: JUMPDEST | 6649: PUSH1 0x40 | 6651: MLOAD | 6652: PUSH4 0xfa6ad355 | 6657: PUSH1 0xe0 | 6659: SHL | 6660: DUP2 | 6661: MSTORE | 6662: PUSH1 0x04 | 6664: SWAP1 | 6665: REVERT    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
6666: JUMPDEST | 6667: PUSH1 0x40 | 6669: MLOAD | 6670: PUSH4 0x1d99ddbf | 6675: PUSH1 0xe0 | 6677: SHL | 6678: DUP2 | 6679: MSTORE | 6680: PUSH1 0x04 | 6682: SWAP1 | 6683: REVERT    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
6684: JUMPDEST | 6685: SWAP1 | 6686: POP | 6687: PUSH32 0x0000000000000000000000000000000000000000000000000000000000000000 | 6720: GT | 6721: ISZERO | 6722: CODESIZE | 6723: PUSH2 0x1924 | 6726: JUMP    ;; CometWithExtendedAssetList.buyCollateral: reserves >= 0 && uint(reserves) >= targetReserves
6727: JUMPDEST | 6728: PUSH1 0x40 | 6730: MLOAD | 6731: PUSH4 0x13d0ff59 | 6736: PUSH1 0xe3 | 6738: SHL | 6739: DUP2 | 6740: MSTORE | 6741: PUSH1 0x04 | 6743: SWAP1 | 6744: REVERT    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
6745: JUMPDEST | 6746: POP | 6747: CALLVALUE | 6748: PUSH2 0x0582 | 6751: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
6752: PUSH1 0x00 | 6754: CALLDATASIZE | 6755: PUSH1 0x03 | 6757: NOT | 6758: ADD | 6759: SLT | 6760: PUSH2 0x0582 | 6763: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
6764: PUSH1 0x40 | 6766: MLOAD | 6767: PUSH32 0x0000000000000000000000000000000000000000000000000000000000000000 | 6800: PUSH1 0x01 | 6802: PUSH1 0x01 | 6804: PUSH1 0xa0 | 6806: SHL | 6807: SUB | 6808: AND | 6809: DUP2 | 6810: MSTORE | 6811: PUSH1 0x20 | 6813: SWAP1 | 6814: RETURN    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
6815: JUMPDEST | 6816: POP | 6817: CALLVALUE | 6818: PUSH2 0x0582 | 6821: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
6822: PUSH1 0x40 | 6824: CALLDATASIZE | 6825: PUSH1 0x03 | 6827: NOT | 6828: ADD | 6829: SLT | 6830: PUSH2 0x0582 | 6833: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
6834: PUSH2 0x0904 | 6837: PUSH1 0x04 | 6839: CALLDATALOAD | 6840: PUSH2 0x1ac0 | 6843: DUP2 | 6844: PUSH2 0x0571 | 6847: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
6848: JUMPDEST | 6849: PUSH2 0x1ac8 | 6852: PUSH2 0x2fd5 | 6855: JUMP    ;; CometWithExtendedAssetList.nonReentrant: modifier nonReentrant() { nonReentrantBefore(); _; nonReentrantAfter();…
6856: JUMPDEST | 6857: PUSH1 0x24 | 6859: CALLDATALOAD | 6860: SWAP1 | 6861: CALLER | 6862: CALLER | 6863: CALLER | 6864: PUSH2 0x2f23 | 6867: JUMP    ;; CometWithExtendedAssetList.supply: msg.sender
6868: JUMPDEST | 6869: POP | 6870: CALLVALUE | 6871: PUSH2 0x0582 | 6874: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
6875: PUSH1 0x40 | 6877: CALLDATASIZE | 6878: PUSH1 0x03 | 6880: NOT | 6881: ADD | 6882: SLT | 6883: PUSH2 0x0582 | 6886: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
6887: PUSH2 0x0904 | 6890: PUSH1 0x04 | 6892: CALLDATALOAD | 6893: PUSH2 0x1af5 | 6896: DUP2 | 6897: PUSH2 0x0571 | 6900: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
6901: JUMPDEST | 6902: PUSH2 0x1afd | 6905: PUSH2 0x2fd5 | 6908: JUMP    ;; CometWithExtendedAssetList.nonReentrant: modifier nonReentrant() { nonReentrantBefore(); _; nonReentrantAfter();…
6909: JUMPDEST | 6910: PUSH1 0x24 | 6912: CALLDATALOAD | 6913: SWAP1 | 6914: CALLER | 6915: CALLER | 6916: CALLER | 6917: PUSH2 0x3ced | 6920: JUMP    ;; CometWithExtendedAssetList.withdraw: msg.sender
6921: JUMPDEST | 6922: PUSH1 0x01 | 6924: PUSH1 0x01 | 6926: PUSH1 0xa0 | 6928: SHL | 6929: SUB | 6930: DUP1 | 6931: DUP4 | 6932: AND | 6933: SWAP2 | 6934: AND | 6935: SWAP1 | 6936: DUP2 | 6937: EQ | 6938: SWAP2 | 6939: SWAP1 | 6940: DUP3 | 6941: ISZERO | 6942: PUSH2 0x1b26 | 6945: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
6946: POP | 6947: POP | 6948: SWAP1 | 6949: JUMP    ;; CometCore.hasPermission: return owner == manager || isAllowed[owner][manager]
6950: JUMPDEST | 6951: PUSH1 0xff | 6953: SWAP3 | 6954: POP | 6955: SWAP1 | 6956: PUSH2 0x1b41 | 6959: SWAP2 | 6960: PUSH1 0x00 | 6962: MSTORE | 6963: PUSH1 0x03 | 6965: PUSH1 0x20 | 6967: MSTORE | 6968: PUSH1 0x40 | 6970: PUSH1 0x00 | 6972: KECCAK256 | 6973: PUSH2 0x097c | 6976: JUMP    ;; KECCAK256 ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
6977: JUMPDEST | 6978: SLOAD | 6979: AND | 6980: SWAP1 | 6981: JUMP    ;; SLOAD ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
6982: JUMPDEST | 6983: PUSH1 0x1f | 6985: SWAP1 | 6986: SWAP2 | 6987: ADD | 6988: PUSH1 0x1f | 6990: NOT | 6991: AND | 6992: DUP2 | 6993: ADD | 6994: SWAP1 | 6995: PUSH1 0x01 | 6997: PUSH1 0x01 | 6999: PUSH1 0x40 | 7001: SHL | 7002: SUB | 7003: DUP3 | 7004: GT | 7005: SWAP1 | 7006: DUP3 | 7007: LT | 7008: OR | 7009: PUSH2 0x1b69 | 7012: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
7013: PUSH1 0x40 | 7015: MSTORE | 7016: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
7017: JUMPDEST | 7018: PUSH4 0x4e487b71 | 7023: PUSH1 0xe0 | 7025: SHL | 7026: PUSH1 0x00 | 7028: MSTORE | 7029: PUSH1 0x41 | 7031: PUSH1 0x04 | 7033: MSTORE | 7034: PUSH1 0x24 | 7036: PUSH1 0x00 | 7038: REVERT    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
7039: JUMPDEST | 7040: PUSH1 0x40 | 7042: MLOAD | 7043: SWAP1 | 7044: PUSH2 0x1b8f | 7047: PUSH2 0x0100 | 7050: DUP4 | 7051: PUSH2 0x1b46 | 7054: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
7055: JUMPDEST | 7056: DUP2 | 7057: PUSH1 0xe0 | 7059: PUSH1 0x00 | 7061: SWAP2 | 7062: DUP3 | 7063: DUP2 | 7064: MSTORE | 7065: DUP3 | 7066: PUSH1 0x20 | 7068: DUP3 | 7069: ADD | 7070: MSTORE | 7071: DUP3 | 7072: PUSH1 0x40 | 7074: DUP3 | 7075: ADD | 7076: MSTORE | 7077: DUP3 | 7078: PUSH1 0x60 | 7080: DUP3 | 7081: ADD | 7082: MSTORE | 7083: DUP3 | 7084: PUSH1 0x80 | 7086: DUP3 | 7087: ADD | 7088: MSTORE | 7089: DUP3 | 7090: PUSH1 0xa0 | 7092: DUP3 | 7093: ADD | 7094: MSTORE | 7095: DUP3 | 7096: PUSH1 0xc0 | 7098: DUP3 | 7099: ADD | 7100: MSTORE | 7101: ADD | 7102: MSTORE | 7103: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
7104: JUMPDEST | 7105: MLOAD | 7106: SWAP1 | 7107: PUSH2 0x0c31 | 7110: DUP3 | 7111: PUSH2 0x1696 | 7114: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
7115: JUMPDEST | 7116: MLOAD | 7117: SWAP1 | 7118: PUSH2 0x0c31 | 7121: DUP3 | 7122: PUSH2 0x0571 | 7125: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
7126: JUMPDEST | 7127: MLOAD | 7128: SWAP1 | 7129: PUSH1 0x01 | 7131: PUSH1 0x01 | 7133: PUSH1 0x40 | 7135: SHL | 7136: SUB | 7137: DUP3 | 7138: AND | 7139: DUP3 | 7140: SUB | 7141: PUSH2 0x0582 | 7144: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
7145: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
7146: JUMPDEST | 7147: MLOAD | 7148: SWAP1 | 7149: PUSH1 0x01 | 7151: PUSH1 0x01 | 7153: PUSH1 0x80 | 7155: SHL | 7156: SUB | 7157: DUP3 | 7158: AND | 7159: DUP3 | 7160: SUB | 7161: PUSH2 0x0582 | 7164: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
7165: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
7166: JUMPDEST | 7167: POP | 7168: PUSH1 0x40 | 7170: MLOAD | 7171: RETURNDATASIZE | 7172: PUSH1 0x00 | 7174: DUP3 | 7175: RETURNDATACOPY | 7176: RETURNDATASIZE | 7177: SWAP1 | 7178: REVERT    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
7179: JUMPDEST | 7180: PUSH2 0x1c13 | 7183: PUSH2 0x1b7f | 7186: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
7187: JUMPDEST | 7188: POP | 7189: PUSH1 0x40 | 7191: MLOAD | 7192: PUSH4 0xc8c7fe6b | 7197: PUSH1 0xe0 | 7199: SHL | 7200: DUP2 | 7201: MSTORE | 7202: PUSH1 0xff | 7204: SWAP2 | 7205: SWAP1 | 7206: SWAP2 | 7207: AND | 7208: PUSH1 0x04 | 7210: DUP3 | 7211: ADD | 7212: MSTORE | 7213: PUSH2 0x0100 | 7216: DUP1 | 7217: DUP3 | 7218: PUSH1 0x24 | 7220: DUP2 | 7221: PUSH32 0x0000000000000000000000000000000000000000000000000000000000000000 | 7254: PUSH1 0x01 | 7256: PUSH1 0x01 | 7258: PUSH1 0xa0 | 7260: SHL | 7261: SUB | 7262: AND | 7263: GAS | 7264: STATICCALL | 7265: SWAP2 | 7266: DUP3 | 7267: ISZERO | 7268: PUSH2 0x1d2d | 7271: JUMPI    ;; STATICCALL ;; CometWithExtendedAssetList.getAssetInfo: IAssetList(assetList).getAssetInfo(i)
7272: JUMPDEST | 7273: PUSH1 0x00 | 7275: SWAP3 | 7276: PUSH2 0x1c74 | 7279: JUMPI    ;; CometWithExtendedAssetList.getAssetInfo: IAssetList(assetList).getAssetInfo(i)
7280: POP | 7281: POP | 7282: SWAP1 | 7283: JUMP    ;; CometWithExtendedAssetList.getAssetInfo: return IAssetList(assetList).getAssetInfo(i)
7284: JUMPDEST | 7285: SWAP1 | 7286: SWAP2 | 7287: DUP3 | 7288: DUP3 | 7289: DUP2 | 7290: RETURNDATASIZE | 7291: DUP4 | 7292: GT | 7293: PUSH2 0x1d26 | 7296: JUMPI    ;; CometWithExtendedAssetList.getAssetInfo: IAssetList(assetList).getAssetInfo(i)
7297: JUMPDEST | 7298: PUSH2 0x1c8b | 7301: DUP2 | 7302: DUP4 | 7303: PUSH2 0x1b46 | 7306: JUMP    ;; CometWithExtendedAssetList.getAssetInfo: IAssetList(assetList).getAssetInfo(i)
7307: JUMPDEST | 7308: DUP2 | 7309: ADD | 7310: SUB | 7311: SLT | 7312: PUSH2 0x0792 | 7315: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
7316: POP | 7317: PUSH1 0xe0 | 7319: PUSH2 0x1d1e | 7322: SWAP2 | 7323: PUSH2 0x1ca7 | 7326: PUSH1 0x40 | 7328: MLOAD | 7329: SWAP5 | 7330: DUP6 | 7331: PUSH2 0x1b46 | 7334: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
7335: JUMPDEST | 7336: PUSH2 0x1cb0 | 7339: DUP2 | 7340: PUSH2 0x1bc0 | 7343: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
7344: JUMPDEST | 7345: DUP5 | 7346: MSTORE | 7347: PUSH2 0x1cbe | 7350: PUSH1 0x20 | 7352: DUP3 | 7353: ADD | 7354: PUSH2 0x1bcb | 7357: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
7358: JUMPDEST | 7359: PUSH1 0x20 | 7361: DUP6 | 7362: ADD | 7363: MSTORE | 7364: PUSH2 0x1ccf | 7367: PUSH1 0x40 | 7369: DUP3 | 7370: ADD | 7371: PUSH2 0x1bcb | 7374: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
7375: JUMPDEST | 7376: PUSH1 0x40 | 7378: DUP6 | 7379: ADD | 7380: MSTORE | 7381: PUSH2 0x1ce0 | 7384: PUSH1 0x60 | 7386: DUP3 | 7387: ADD | 7388: PUSH2 0x1bd6 | 7391: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
7392: JUMPDEST | 7393: PUSH1 0x60 | 7395: DUP6 | 7396: ADD | 7397: MSTORE | 7398: PUSH2 0x1cf1 | 7401: PUSH1 0x80 | 7403: DUP3 | 7404: ADD | 7405: PUSH2 0x1bd6 | 7408: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
7409: JUMPDEST | 7410: PUSH1 0x80 | 7412: DUP6 | 7413: ADD | 7414: MSTORE | 7415: PUSH2 0x1d02 | 7418: PUSH1 0xa0 | 7420: DUP3 | 7421: ADD | 7422: PUSH2 0x1bd6 | 7425: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
7426: JUMPDEST | 7427: PUSH1 0xa0 | 7429: DUP6 | 7430: ADD | 7431: MSTORE | 7432: PUSH2 0x1d13 | 7435: PUSH1 0xc0 | 7437: DUP3 | 7438: ADD | 7439: PUSH2 0x1bd6 | 7442: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
7443: JUMPDEST | 7444: PUSH1 0xc0 | 7446: DUP6 | 7447: ADD | 7448: MSTORE | 7449: ADD | 7450: PUSH2 0x1bea | 7453: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
7454: JUMPDEST | 7455: PUSH1 0xe0 | 7457: DUP3 | 7458: ADD | 7459: MSTORE | 7460: SWAP1 | 7461: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
7462: JUMPDEST | 7463: POP | 7464: RETURNDATASIZE | 7465: PUSH2 0x1c81 | 7468: JUMP    ;; CometWithExtendedAssetList.getAssetInfo: IAssetList(assetList).getAssetInfo(i)
7469: JUMPDEST | 7470: PUSH2 0x1d35 | 7473: PUSH2 0x1bfe | 7476: JUMP    ;; CometWithExtendedAssetList.getAssetInfo: IAssetList(assetList).getAssetInfo(i)
7477: JUMPDEST | 7478: PUSH2 0x1c68 | 7481: JUMP    ;; CometWithExtendedAssetList.getAssetInfo: IAssetList(assetList).getAssetInfo(i)
7482: JUMPDEST | 7483: SWAP1 | 7484: PUSH2 0x1d43 | 7487: PUSH2 0x1b7f | 7490: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
7491: JUMPDEST | 7492: POP | 7493: PUSH1 0x00 | 7495: SWAP1 | 7496: PUSH1 0xff | 7498: SWAP3 | 7499: DUP4 | 7500: PUSH32 0x0000000000000000000000000000000000000000000000000000000000000000 | 7533: AND | 7534: SWAP3    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
7535: JUMPDEST | 7536: DUP4 | 7537: DUP6 | 7538: DUP3 | 7539: AND | 7540: LT | 7541: PUSH2 0x1d8a | 7544: JUMPI    ;; CometWithExtendedAssetList.getAssetInfoByAddress: i < numAssets
7545: PUSH1 0x40 | 7547: MLOAD | 7548: PUSH4 0x36405305 | 7553: PUSH1 0xe0 | 7555: SHL | 7556: DUP2 | 7557: MSTORE | 7558: PUSH1 0x04 | 7560: SWAP1 | 7561: REVERT    ;; CometWithExtendedAssetList.getAssetInfoByAddress: BadAsset()
7562: JUMPDEST | 7563: PUSH2 0x1d93 | 7566: DUP2 | 7567: PUSH2 0x1c0b | 7570: JUMP    ;; CometWithExtendedAssetList.getAssetInfoByAddress: getAssetInfo(i)
7571: JUMPDEST | 7572: PUSH1 0x20 | 7574: DUP2 | 7575: ADD | 7576: MLOAD | 7577: PUSH1 0x01 | 7579: PUSH1 0x01 | 7581: PUSH1 0xa0 | 7583: SHL | 7584: SUB | 7585: DUP5 | 7586: DUP2 | 7587: AND | 7588: SWAP2 | 7589: AND | 7590: EQ | 7591: PUSH2 0x1db5 | 7594: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
7595: POP | 7596: PUSH1 0x01 | 7598: ADD | 7599: DUP5 | 7600: AND | 7601: PUSH2 0x1d6f | 7604: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
7605: JUMPDEST | 7606: SWAP4 | 7607: POP | 7608: POP | 7609: POP | 7610: SWAP2 | 7611: POP | 7612: SWAP1 | 7613: JUMP    ;; CometWithExtendedAssetList.getAssetInfoByAddress: return assetInfo
7614: JUMPDEST | 7615: PUSH1 0x01 | 7617: PUSH1 0x28 | 7619: SHL | 7620: TIMESTAMP | 7621: LT | 7622: ISZERO | 7623: PUSH2 0x1dd5 | 7626: JUMPI    ;; CometWithExtendedAssetList.getNowInternal: block.timestamp >= 2**40
7627: PUSH5 0xffffffffff | 7633: TIMESTAMP | 7634: AND | 7635: SWAP1 | 7636: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
7637: JUMPDEST | 7638: PUSH1 0x40 | 7640: MLOAD | 7641: PUSH4 0x3d32ffdb | 7646: PUSH1 0xe0 | 7648: SHL | 7649: DUP2 | 7650: MSTORE | 7651: PUSH1 0x04 | 7653: SWAP1 | 7654: REVERT    ;; CometWithExtendedAssetList.getNowInternal: TimestampTooLarge()
7655: JUMPDEST | 7656: SWAP1 | 7657: PUSH1 0x40 | 7659: MLOAD | 7660: PUSH2 0x1df6 | 7663: PUSH1 0xa0 | 7665: DUP3 | 7666: PUSH2 0x1b46 | 7669: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
7670: JUMPDEST | 7671: PUSH1 0x80 | 7673: DUP2 | 7674: SWAP4 | 7675: SLOAD | 7676: DUP1 | 7677: PUSH1 0x0c | 7679: SIGNEXTEND | 7680: DUP4 | 7681: MSTORE | 7682: PUSH1 0x01 | 7684: DUP1 | 7685: PUSH1 0x40 | 7687: SHL | 7688: SUB | 7689: DUP1 | 7690: DUP3 | 7691: PUSH1 0x68 | 7693: SHR | 7694: AND | 7695: PUSH1 0x20 | 7697: DUP6 | 7698: ADD | 7699: MSTORE | 7700: DUP2 | 7701: PUSH1 0xa8 | 7703: SHR | 7704: AND | 7705: PUSH1 0x40 | 7707: DUP5 | 7708: ADD | 7709: MSTORE | 7710: PUSH2 0xffff | 7713: DUP2 | 7714: PUSH1 0xe8 | 7716: SHR | 7717: AND | 7718: PUSH1 0x60 | 7720: DUP5 | 7721: ADD | 7722: MSTORE | 7723: PUSH1 0xf8 | 7725: SHR | 7726: SWAP2 | 7727: ADD | 7728: MSTORE | 7729: JUMP    ;; SLOAD ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
7730: JUMPDEST | 7731: POP | 7732: PUSH4 0x4e487b71 | 7737: PUSH1 0xe0 | 7739: SHL | 7740: PUSH1 0x00 | 7742: MSTORE | 7743: PUSH1 0x11 | 7745: PUSH1 0x04 | 7747: MSTORE | 7748: PUSH1 0x24 | 7750: PUSH1 0x00 | 7752: REVERT    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
7753: JUMPDEST | 7754: PUSH5 0xffffffffff | 7760: SWAP2 | 7761: DUP3 | 7762: AND | 7763: SWAP2 | 7764: AND | 7765: DUP2 | 7766: DUP2 | 7767: LT | 7768: PUSH2 0x1e5f | 7771: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
7772: SUB | 7773: SWAP1 | 7774: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
7775: JUMPDEST | 7776: PUSH2 0x1e67 | 7779: PUSH2 0x1e32 | 7782: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
7783: JUMPDEST | 7784: SUB | 7785: SWAP1 | 7786: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
7787: JUMPDEST | 7788: PUSH1 0x01 | 7790: PUSH1 0x01 | 7792: PUSH1 0x68 | 7794: SHL | 7795: SUB | 7796: AND | 7797: SWAP1 | 7798: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
7799: JUMPDEST | 7800: DUP1 | 7801: PUSH1 0x00 | 7803: NOT | 7804: DIV | 7805: DUP3 | 7806: GT | 7807: DUP2 | 7808: ISZERO | 7809: ISZERO | 7810: AND | 7811: PUSH2 0x1e8a | 7814: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
7815: MUL | 7816: SWAP1 | 7817: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
7818: JUMPDEST | 7819: PUSH2 0x1e92 | 7822: PUSH2 0x1e32 | 7825: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
7826: JUMPDEST | 7827: MUL | 7828: SWAP1 | 7829: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
7830: JUMPDEST | 7831: PUSH1 0x01 | 7833: PUSH1 0x01 | 7835: PUSH1 0x40 | 7837: SHL | 7838: SUB | 7839: SWAP2 | 7840: DUP3 | 7841: AND | 7842: SWAP2 | 7843: SWAP1 | 7844: DUP2 | 7845: AND | 7846: SWAP1 | 7847: DUP3 | 7848: SWAP1 | 7849: SUB | 7850: DUP2 | 7851: GT | 7852: PUSH2 0x1eb3 | 7855: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
7856: ADD | 7857: SWAP1 | 7858: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
7859: JUMPDEST | 7860: PUSH2 0x1ebb | 7863: PUSH2 0x1e32 | 7866: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
7867: JUMPDEST | 7868: ADD | 7869: SWAP1 | 7870: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
7871: JUMPDEST | 7872: PUSH1 0x68 | 7874: SHR | 7875: PUSH1 0x01 | 7877: PUSH1 0x01 | 7879: PUSH1 0x68 | 7881: SHL | 7882: SUB | 7883: AND | 7884: SWAP1 | 7885: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
7886: JUMPDEST | 7887: PUSH2 0x1ed6 | 7890: PUSH2 0x1dbe | 7893: JUMP    ;; CometWithExtendedAssetList.accrueInternal: getNowInternal()
7894: JUMPDEST | 7895: PUSH2 0x1f00 | 7898: PUSH2 0x1ef6 | 7901: PUSH2 0x1ef0 | 7904: PUSH1 0x01 | 7906: SLOAD | 7907: PUSH5 0xffffffffff | 7913: SWAP1 | 7914: PUSH1 0xd0 | 7916: SHR | 7917: AND | 7918: SWAP1 | 7919: JUMP    ;; SLOAD ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
7920: JUMPDEST | 7921: DUP4 | 7922: PUSH2 0x1e49 | 7925: JUMP    ;; CometWithExtendedAssetList.accrueInternal: now_ - lastAccrualTime
7926: JUMPDEST | 7927: PUSH5 0xffffffffff | 7933: AND | 7934: SWAP1 | 7935: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
7936: JUMPDEST | 7937: SWAP1 | 7938: DUP2 | 7939: PUSH2 0x1f0a | 7942: JUMPI    ;; CometWithExtendedAssetList.accrueInternal: timeElapsed > 0
7943: POP | 7944: POP | 7945: JUMP    ;; CometWithExtendedAssetList.accrueInternal: function accrueInternal() internal { uint40 now_ = getNowInternal(); ui…
7946: JUMPDEST | 7947: DUP2 | 7948: PUSH2 0x1f61 | 7951: PUSH2 0x1f1a | 7954: PUSH2 0x0c31 | 7957: SWAP5 | 7958: PUSH2 0x20fd | 7961: JUMP    ;; CometWithExtendedAssetList.accrueInternal: accruedInterestIndices(timeElapsed)
7962: JUMPDEST | 7963: PUSH1 0x00 | 7965: DUP1 | 7966: SLOAD | 7967: PUSH1 0x01 | 7969: PUSH1 0x40 | 7971: SHL | 7972: PUSH1 0x01 | 7974: PUSH1 0x80 | 7976: SHL | 7977: SUB | 7978: NOT | 7979: AND | 7980: PUSH1 0x40 | 7982: SWAP3 | 7983: SWAP1 | 7984: SWAP3 | 7985: SHL | 7986: PUSH1 0x01 | 7988: PUSH1 0x40 | 7990: SHL | 7991: PUSH1 0x01 | 7993: PUSH1 0x80 | 7995: SHL | 7996: SUB | 7997: AND | 7998: SWAP2 | 7999: SWAP1 | 8000: SWAP2 | 8001: OR | 8002: DUP2 | 8003: SSTORE | 8004: SWAP2 | 8005: SWAP1 | 8006: DUP3 | 8007: SLOAD | 8008: PUSH1 0x01 | 8010: PUSH1 0x01 | 8012: PUSH1 0x40 | 8014: SHL | 8015: SUB | 8016: NOT | 8017: AND | 8018: PUSH1 0x01 | 8020: PUSH1 0x01 | 8022: PUSH1 0x40 | 8024: SHL | 8025: SUB | 8026: SWAP1 | 8027: SWAP2 | 8028: AND | 8029: OR | 8030: DUP3 | 8031: SSTORE | 8032: JUMP    ;; SLOAD,SSTORE,SLOAD,SSTORE ;; CometCore helper: 1e15
8033: JUMPDEST | 8034: PUSH2 0x1f6c | 8037: PUSH1 0x01 | 8039: SLOAD | 8040: PUSH2 0x1e6b | 8043: JUMP    ;; SLOAD ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
8044: JUMPDEST | 8045: PUSH32 0x0000000000000000000000000000000000000000000000000000000000000000 | 8078: SWAP3 | 8079: SWAP1 | 8080: PUSH1 0x01 | 8082: PUSH1 0x01 | 8084: PUSH1 0x68 | 8086: SHL | 8087: SUB | 8088: AND | 8089: DUP4 | 8090: DUP2 | 8091: LT | 8092: ISZERO | 8093: PUSH2 0x2061 | 8096: JUMPI    ;; CometWithExtendedAssetList.accrueInternal: totalSupplyBase >= baseMinForRewards
8097: JUMPDEST | 8098: POP | 8099: PUSH2 0x1fb5 | 8102: PUSH2 0x1fb0 | 8105: PUSH1 0x01 | 8107: SLOAD | 8108: PUSH2 0x1ebf | 8111: JUMP    ;; SLOAD ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
8112: JUMPDEST | 8113: PUSH2 0x1e6b | 8116: JUMP    ;; CometWithExtendedAssetList.accrueInternal: totalBorrowBase >= baseMinForRewards
8117: JUMPDEST | 8118: SWAP3 | 8119: DUP4 | 8120: LT | 8121: ISZERO | 8122: PUSH2 0x1fe9 | 8125: JUMPI    ;; CometWithExtendedAssetList.accrueInternal: totalBorrowBase >= baseMinForRewards
8126: JUMPDEST | 8127: POP | 8128: POP | 8129: PUSH1 0x01 | 8131: DUP1 | 8132: SLOAD | 8133: PUSH5 0xffffffffff | 8139: PUSH1 0xd0 | 8141: SHL | 8142: NOT | 8143: AND | 8144: PUSH1 0xd0 | 8146: SWAP4 | 8147: SWAP1 | 8148: SWAP4 | 8149: SHL | 8150: PUSH5 0xffffffffff | 8156: PUSH1 0xd0 | 8158: SHL | 8159: AND | 8160: SWAP3 | 8161: SWAP1 | 8162: SWAP3 | 8163: OR | 8164: SWAP1 | 8165: SWAP2 | 8166: SSTORE | 8167: POP | 8168: JUMP    ;; SLOAD,SSTORE ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
8169: JUMPDEST | 8170: PUSH2 0x202a | 8173: PUSH2 0x2025 | 8176: PUSH2 0x2059 | 8179: SWAP5 | 8180: PUSH2 0x2020 | 8183: PUSH2 0x2039 | 8186: SWAP5 | 8187: PUSH32 0x0000000000000000000000000000000000000000000000000000000000000000 | 8220: PUSH2 0x1e77 | 8223: JUMP    ;; CometWithExtendedAssetList.accrueInternal: baseTrackingBorrowSpeed
8224: JUMPDEST | 8225: PUSH2 0x2b8f | 8228: JUMP    ;; CometWithExtendedAssetList.accrueInternal: divBaseWei(baseTrackingBorrowSpeed * timeElapsed, totalBorrowBase)
8229: JUMPDEST | 8230: PUSH2 0x20d7 | 8233: JUMP    ;; CometWithExtendedAssetList.accrueInternal: safe64(divBaseWei(baseTrackingBorrowSpeed * timeElapsed, totalBorrowBas…
8234: JUMPDEST | 8235: DUP3 | 8236: SLOAD | 8237: PUSH1 0xc0 | 8239: SHR | 8240: PUSH2 0x1e96 | 8243: JUMP    ;; SLOAD ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
8244: JUMPDEST | 8245: PUSH2 0x1e96 | 8248: JUMP    ;; CometWithExtendedAssetList.accrueInternal: trackingBorrowIndex += safe64(divBaseWei(baseTrackingBorrowSpeed * time…
8249: JUMPDEST | 8250: DUP2 | 8251: SLOAD | 8252: PUSH1 0x01 | 8254: PUSH1 0x01 | 8256: PUSH1 0xc0 | 8258: SHL | 8259: SUB | 8260: AND | 8261: PUSH1 0xc0 | 8263: SWAP2 | 8264: SWAP1 | 8265: SWAP2 | 8266: SHL | 8267: PUSH1 0x01 | 8269: PUSH1 0x01 | 8271: PUSH1 0xc0 | 8273: SHL | 8274: SUB | 8275: NOT | 8276: AND | 8277: OR | 8278: SWAP1 | 8279: SSTORE | 8280: JUMP    ;; SLOAD,SSTORE ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
8281: JUMPDEST | 8282: CODESIZE | 8283: DUP1 | 8284: DUP1 | 8285: PUSH2 0x1fbe | 8288: JUMP    ;; CometWithExtendedAssetList.accrueInternal: if (totalBorrowBase >= baseMinForRewards) { trackingBorrowIndex += safe…
8289: JUMPDEST | 8290: PUSH2 0x20ab | 8293: PUSH2 0x2098 | 8296: PUSH2 0x2025 | 8299: PUSH2 0x20d1 | 8302: SWAP4 | 8303: PUSH2 0x2020 | 8306: DUP7 | 8307: PUSH32 0x0000000000000000000000000000000000000000000000000000000000000000 | 8340: PUSH2 0x1e77 | 8343: JUMP    ;; CometWithExtendedAssetList.accrueInternal: baseTrackingSupplySpeed
8344: JUMPDEST | 8345: DUP5 | 8346: SLOAD | 8347: PUSH1 0x80 | 8349: SHR | 8350: PUSH1 0x01 | 8352: PUSH1 0x01 | 8354: PUSH1 0x40 | 8356: SHL | 8357: SUB | 8358: AND | 8359: PUSH2 0x1e96 | 8362: JUMP    ;; SLOAD ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
8363: JUMPDEST | 8364: DUP4 | 8365: SLOAD | 8366: PUSH1 0x01 | 8368: PUSH1 0x80 | 8370: SHL | 8371: PUSH1 0x01 | 8373: PUSH1 0xc0 | 8375: SHL | 8376: SUB | 8377: NOT | 8378: AND | 8379: PUSH1 0x80 | 8381: SWAP2 | 8382: SWAP1 | 8383: SWAP2 | 8384: SHL | 8385: PUSH1 0x01 | 8387: PUSH1 0x80 | 8389: SHL | 8390: PUSH1 0x01 | 8392: PUSH1 0xc0 | 8394: SHL | 8395: SUB | 8396: AND | 8397: OR | 8398: DUP4 | 8399: SSTORE | 8400: JUMP    ;; SLOAD,SSTORE ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
8401: JUMPDEST | 8402: CODESIZE | 8403: PUSH2 0x1fa1 | 8406: JUMP    ;; CometWithExtendedAssetList.accrueInternal: if (totalSupplyBase >= baseMinForRewards) { trackingSupplyIndex += safe…
8407: JUMPDEST | 8408: PUSH1 0x01 | 8410: PUSH1 0x01 | 8412: PUSH1 0x40 | 8414: SHL | 8415: SUB | 8416: SWAP1 | 8417: DUP2 | 8418: DUP2 | 8419: GT | 8420: PUSH2 0x20eb | 8423: JUMPI    ;; CometMath.safe64: n > type(uint64).max
8424: AND | 8425: SWAP1 | 8426: JUMP    ;; CometMath.safe64: function safe64(uint n) internal pure returns (uint64) { if (n > type(u…
8427: JUMPDEST | 8428: PUSH1 0x40 | 8430: MLOAD | 8431: PUSH4 0x72a1cb51 | 8436: PUSH1 0xe1 | 8438: SHL | 8439: DUP2 | 8440: MSTORE | 8441: PUSH1 0x04 | 8443: SWAP1 | 8444: REVERT    ;; CometMath.safe64: InvalidUInt64()
8445: JUMPDEST | 8446: PUSH1 0x00 | 8448: SLOAD | 8449: PUSH1 0x01 | 8451: PUSH1 0x01 | 8453: PUSH1 0x40 | 8455: SHL | 8456: SUB | 8457: PUSH1 0x40 | 8459: DUP3 | 8460: SWAP1 | 8461: SHR | 8462: DUP2 | 8463: AND | 8464: SWAP4 | 8465: SWAP3 | 8466: SWAP2 | 8467: DUP2 | 8468: AND | 8469: SWAP2 | 8470: SWAP1 | 8471: DUP2 | 8472: PUSH2 0x2122 | 8475: JUMPI    ;; SLOAD ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
8476: JUMPDEST | 8477: POP | 8478: POP | 8479: SWAP2 | 8480: SWAP1 | 8481: JUMP    ;; CometWithExtendedAssetList.accruedInterestIndices: function accruedInterestIndices(uint timeElapsed) internal view returns…
8482: JUMPDEST | 8483: DUP2 | 8484: PUSH2 0x2175 | 8487: PUSH2 0x216f | 8490: PUSH2 0x214f | 8493: SWAP8 | 8494: SWAP5 | 8495: PUSH2 0x2181 | 8498: PUSH2 0x2187 | 8501: SWAP8 | 8502: PUSH2 0x217b | 8505: DUP8 | 8506: PUSH2 0x2156 | 8509: PUSH2 0x217b | 8512: SWAP10 | 8513: PUSH2 0x2148 | 8516: PUSH2 0x23ec | 8519: JUMP    ;; CometWithExtendedAssetList.accruedInterestIndices: getUtilization()
8520: JUMPDEST | 8521: SWAP15 | 8522: DUP16 | 8523: PUSH2 0x21a6 | 8526: JUMP    ;; CometWithExtendedAssetList.accruedInterestIndices: getSupplyRate(utilization)
8527: JUMPDEST | 8528: AND | 8529: SWAP14 | 8530: PUSH2 0x22b6 | 8533: JUMP    ;; CometWithExtendedAssetList.accruedInterestIndices: getBorrowRate(utilization)
8534: JUMPDEST | 8535: AND | 8536: SWAP12 | 8537: PUSH2 0x2175 | 8540: PUSH2 0x216f | 8543: PUSH8 0x0de0b6b3a7640000 | 8552: SWAP10 | 8553: DUP11 | 8554: SWAP4 | 8555: PUSH2 0x1e77 | 8558: JUMP    ;; CometWithExtendedAssetList.accruedInterestIndices: supplyRate * timeElapsed
8559: JUMPDEST | 8560: DUP5 | 8561: PUSH2 0x1e77 | 8564: JUMP    ;; CometWithExtendedAssetList.mulFactor: n * factor
8565: JUMPDEST | 8566: DIV | 8567: PUSH2 0x20d7 | 8570: JUMP    ;; CometWithExtendedAssetList.accruedInterestIndices: safe64(mulFactor(baseSupplyIndex_, supplyRate * timeElapsed))
8571: JUMPDEST | 8572: SWAP1 | 8573: PUSH2 0x1e96 | 8576: JUMP    ;; CometWithExtendedAssetList.accruedInterestIndices: baseSupplyIndex_ += safe64(mulFactor(baseSupplyIndex_, supplyRate * tim…
8577: JUMPDEST | 8578: SWAP9 | 8579: PUSH2 0x1e77 | 8582: JUMP    ;; CometWithExtendedAssetList.accruedInterestIndices: borrowRate * timeElapsed
8583: JUMPDEST | 8584: SWAP2 | 8585: CODESIZE | 8586: DUP1 | 8587: PUSH2 0x211c | 8590: JUMP    ;; CometWithExtendedAssetList.accruedInterestIndices: if (timeElapsed > 0) { uint utilization = getUtilization(); uint supply…
8591: JUMPDEST | 8592: DUP2 | 8593: NOT | 8594: DUP2 | 8595: GT | 8596: PUSH2 0x1eb3 | 8599: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
8600: ADD | 8601: SWAP1 | 8602: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
8603: JUMPDEST | 8604: DUP2 | 8605: DUP2 | 8606: LT | 8607: PUSH2 0x1e5f | 8610: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
8611: SUB | 8612: SWAP1 | 8613: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
8614: JUMPDEST | 8615: PUSH32 0x0000000000000000000000000000000000000000000000000000000000000000 | 8648: DUP1 | 8649: DUP3 | 8650: GT | 8651: PUSH2 0x222f | 8654: JUMPI    ;; CometWithExtendedAssetList.getSupplyRate: utilization <= supplyKink
8655: POP | 8656: PUSH2 0x2025 | 8659: PUSH8 0x0de0b6b3a7640000 | 8668: PUSH2 0x2208 | 8671: PUSH2 0x0979 | 8674: SWAP4 | 8675: PUSH32 0x0000000000000000000000000000000000000000000000000000000000000000 | 8708: PUSH2 0x1e77 | 8711: JUMP    ;; CometWithExtendedAssetList.getSupplyRate: supplyPerSecondInterestRateSlopeLow
8712: JUMPDEST | 8713: DIV | 8714: PUSH32 0x0000000000000000000000000000000000000000000000000000000000000000 | 8747: PUSH2 0x218f | 8750: JUMP    ;; CometWithExtendedAssetList.getSupplyRate: supplyPerSecondInterestRateBase + mulFactor(supplyPerSecondInterestRate…
8751: JUMPDEST | 8752: PUSH2 0x0979 | 8755: SWAP2 | 8756: PUSH2 0x2025 | 8759: SWAP2 | 8760: PUSH2 0x22a2 | 8763: PUSH8 0x0de0b6b3a7640000 | 8772: SWAP2 | 8773: PUSH2 0x2272 | 8776: DUP4 | 8777: PUSH2 0x2208 | 8780: DUP4 | 8781: PUSH32 0x0000000000000000000000000000000000000000000000000000000000000000 | 8814: PUSH2 0x1e77 | 8817: JUMP    ;; CometWithExtendedAssetList.mulFactor: n * factor
8818: JUMPDEST | 8819: SWAP4 | 8820: DUP2 | 8821: DUP2 | 8822: LT | 8823: PUSH2 0x22a9 | 8826: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
8827: JUMPDEST | 8828: SUB | 8829: PUSH32 0x0000000000000000000000000000000000000000000000000000000000000000 | 8862: PUSH2 0x1e77 | 8865: JUMP    ;; CometWithExtendedAssetList.mulFactor: n * factor
8866: JUMPDEST | 8867: DIV | 8868: SWAP1 | 8869: PUSH2 0x218f | 8872: JUMP    ;; CometWithExtendedAssetList.getSupplyRate: supplyPerSecondInterestRateBase + mulFactor(supplyPerSecondInterestRate…
8873: JUMPDEST | 8874: PUSH2 0x22b1 | 8877: PUSH2 0x1e32 | 8880: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
8881: JUMPDEST | 8882: PUSH2 0x227b | 8885: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
8886: JUMPDEST | 8887: PUSH32 0x0000000000000000000000000000000000000000000000000000000000000000 | 8920: DUP1 | 8921: DUP3 | 8922: GT | 8923: PUSH2 0x233f | 8926: JUMPI    ;; CometWithExtendedAssetList.getBorrowRate: utilization <= borrowKink
8927: POP | 8928: PUSH2 0x2025 | 8931: PUSH8 0x0de0b6b3a7640000 | 8940: PUSH2 0x2318 | 8943: PUSH2 0x0979 | 8946: SWAP4 | 8947: PUSH32 0x0000000000000000000000000000000000000000000000000000000000000000 | 8980: PUSH2 0x1e77 | 8983: JUMP    ;; CometWithExtendedAssetList.getBorrowRate: borrowPerSecondInterestRateSlopeLow
8984: JUMPDEST | 8985: DIV | 8986: PUSH32 0x0000000000000000000000000000000000000000000000000000000000000000 | 9019: PUSH2 0x218f | 9022: JUMP    ;; CometWithExtendedAssetList.getBorrowRate: borrowPerSecondInterestRateBase + mulFactor(borrowPerSecondInterestRate…
9023: JUMPDEST | 9024: PUSH2 0x0979 | 9027: SWAP2 | 9028: PUSH2 0x2025 | 9031: SWAP2 | 9032: PUSH2 0x22a2 | 9035: PUSH8 0x0de0b6b3a7640000 | 9044: SWAP2 | 9045: PUSH2 0x2382 | 9048: DUP4 | 9049: PUSH2 0x2318 | 9052: DUP4 | 9053: PUSH32 0x0000000000000000000000000000000000000000000000000000000000000000 | 9086: PUSH2 0x1e77 | 9089: JUMP    ;; CometWithExtendedAssetList.mulFactor: n * factor
9090: JUMPDEST | 9091: SWAP4 | 9092: DUP2 | 9093: DUP2 | 9094: LT | 9095: PUSH2 0x23b2 | 9098: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
9099: JUMPDEST | 9100: SUB | 9101: PUSH32 0x0000000000000000000000000000000000000000000000000000000000000000 | 9134: PUSH2 0x1e77 | 9137: JUMP    ;; CometWithExtendedAssetList.mulFactor: n * factor
9138: JUMPDEST | 9139: PUSH2 0x23ba | 9142: PUSH2 0x1e32 | 9145: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
9146: JUMPDEST | 9147: PUSH2 0x238b | 9150: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
9151: JUMPDEST | 9152: POP | 9153: PUSH4 0x4e487b71 | 9158: PUSH1 0xe0 | 9160: SHL | 9161: PUSH1 0x00 | 9163: MSTORE | 9164: PUSH1 0x12 | 9166: PUSH1 0x04 | 9168: MSTORE | 9169: PUSH1 0x24 | 9171: PUSH1 0x00 | 9173: REVERT    ;; CometCore helper: 1e18
9174: JUMPDEST | 9175: DUP2 | 9176: ISZERO | 9177: PUSH2 0x23e0 | 9180: JUMPI    ;; CometCore helper: 1e18
9181: DIV | 9182: SWAP1 | 9183: JUMP    ;; CometCore helper: 1e18
9184: JUMPDEST | 9185: PUSH2 0x23e8 | 9188: PUSH2 0x23bf | 9191: JUMP    ;; CometCore helper: 1e18
9192: JUMPDEST | 9193: DIV | 9194: SWAP1 | 9195: JUMP    ;; CometCore helper: 1e18
9196: JUMPDEST | 9197: PUSH1 0x00 | 9199: SLOAD | 9200: PUSH1 0x01 | 9202: SLOAD | 9203: PUSH7 0x038d7ea4c68000 | 9211: SWAP1 | 9212: PUSH2 0x242e | 9215: SWAP1 | 9216: PUSH1 0x01 | 9218: PUSH1 0x01 | 9220: PUSH1 0x68 | 9222: SHL | 9223: SUB | 9224: PUSH1 0x01 | 9226: PUSH1 0x01 | 9228: PUSH1 0x40 | 9230: SHL | 9231: SUB | 9232: DUP5 | 9233: PUSH2 0x241e | 9236: DUP3 | 9237: DUP9 | 9238: AND | 9239: DUP5 | 9240: DUP7 | 9241: AND | 9242: PUSH2 0x1e77 | 9245: JUMP    ;; SLOAD,SLOAD ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
9246: JUMPDEST | 9247: DIV | 9248: SWAP6 | 9249: PUSH1 0x40 | 9251: SHR | 9252: AND | 9253: SWAP2 | 9254: PUSH1 0x68 | 9256: SHR | 9257: AND | 9258: PUSH2 0x1e77 | 9261: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
9262: JUMPDEST | 9263: DIV | 9264: DUP2 | 9265: PUSH2 0x243b | 9268: JUMPI    ;; CometWithExtendedAssetList.getUtilization: totalSupply_ == 0
9269: POP | 9270: POP | 9271: PUSH1 0x00 | 9273: SWAP1 | 9274: JUMP    ;; CometWithExtendedAssetList.getUtilization: return 0
9275: JUMPDEST | 9276: PUSH8 0x0de0b6b3a7640000 | 9285: SWAP1 | 9286: DUP1 | 9287: PUSH1 0x00 | 9289: NOT | 9290: DIV | 9291: DUP3 | 9292: GT | 9293: DUP2 | 9294: ISZERO | 9295: ISZERO | 9296: AND | 9297: PUSH2 0x2459 | 9300: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
9301: MUL | 9302: DIV | 9303: SWAP1 | 9304: JUMP    ;; CometWithExtendedAssetList.getUtilization: return totalBorrow_ * FACTOR_SCALE / totalSupply_
9305: JUMPDEST | 9306: PUSH2 0x2461 | 9309: PUSH2 0x1e32 | 9312: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
9313: JUMPDEST | 9314: MUL | 9315: DIV | 9316: SWAP1 | 9317: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
9318: JUMPDEST | 9319: PUSH7 0x038d7ea4c68000 | 9327: SWAP2 | 9328: PUSH2 0x23e8 | 9331: SWAP2 | 9332: PUSH1 0x01 | 9334: PUSH1 0x01 | 9336: PUSH1 0x40 | 9338: SHL | 9339: SUB | 9340: AND | 9341: SWAP1 | 9342: PUSH1 0x01 | 9344: PUSH1 0x01 | 9346: PUSH1 0x68 | 9348: SHL | 9349: SUB | 9350: AND | 9351: PUSH2 0x1e77 | 9354: JUMP    ;; CometCore.presentValueSupply: uint256(principalValue_) * baseSupplyIndex_
9355: JUMPDEST | 9356: MLOAD | 9357: SWAP1 | 9358: PUSH1 0x01 | 9360: PUSH1 0x01 | 9362: PUSH1 0x50 | 9364: SHL | 9365: SUB | 9366: DUP3 | 9367: AND | 9368: DUP3 | 9369: SUB | 9370: PUSH2 0x0582 | 9373: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
9374: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
9375: JUMPDEST | 9376: PUSH1 0x40 | 9378: MLOAD | 9379: PUSH4 0x3fabe5a3 | 9384: PUSH1 0xe2 | 9386: SHL | 9387: DUP2 | 9388: MSTORE | 9389: SWAP1 | 9390: PUSH1 0xa0 | 9392: SWAP1 | 9393: DUP3 | 9394: SWAP1 | 9395: PUSH1 0x04 | 9397: SWAP1 | 9398: DUP3 | 9399: SWAP1 | 9400: PUSH1 0x01 | 9402: PUSH1 0x01 | 9404: PUSH1 0xa0 | 9406: SHL | 9407: SUB | 9408: AND | 9409: GAS | 9410: STATICCALL | 9411: SWAP1 | 9412: DUP2 | 9413: ISZERO | 9414: PUSH2 0x253d | 9417: JUMPI    ;; STATICCALL ;; CometWithExtendedAssetList.getPrice: IPriceFeed(priceFeed).latestRoundData()
9418: JUMPDEST | 9419: PUSH1 0x00 | 9421: SWAP2 | 9422: PUSH2 0x24f1 | 9425: JUMPI    ;; CometWithExtendedAssetList.getPrice: IPriceFeed(priceFeed).latestRoundData()
9426: JUMPDEST | 9427: POP | 9428: PUSH1 0x00 | 9430: DUP2 | 9431: SGT | 9432: ISZERO | 9433: PUSH2 0x24df | 9436: JUMPI    ;; CometWithExtendedAssetList.getPrice: price <= 0
9437: SWAP1 | 9438: JUMP    ;; CometWithExtendedAssetList.getPrice: function getPrice(address priceFeed) override public view returns (uint…
9439: JUMPDEST | 9440: PUSH1 0x40 | 9442: MLOAD | 9443: PUSH4 0xfd1ee349 | 9448: PUSH1 0xe0 | 9450: SHL | 9451: DUP2 | 9452: MSTORE | 9453: PUSH1 0x04 | 9455: SWAP1 | 9456: REVERT    ;; CometWithExtendedAssetList.getPrice: BadPrice()
9457: JUMPDEST | 9458: SWAP1 | 9459: PUSH1 0xa0 | 9461: DUP3 | 9462: RETURNDATASIZE | 9463: DUP3 | 9464: GT | 9465: PUSH2 0x2535 | 9468: JUMPI    ;; CometWithExtendedAssetList.getPrice: IPriceFeed(priceFeed).latestRoundData()
9469: JUMPDEST | 9470: DUP2 | 9471: PUSH2 0x250a | 9474: PUSH1 0xa0 | 9476: SWAP4 | 9477: DUP4 | 9478: PUSH2 0x1b46 | 9481: JUMP    ;; CometWithExtendedAssetList.getPrice: IPriceFeed(priceFeed).latestRoundData()
9482: JUMPDEST | 9483: DUP2 | 9484: ADD | 9485: SUB | 9486: SLT | 9487: PUSH2 0x0792 | 9490: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
9491: POP | 9492: PUSH2 0x251c | 9495: DUP2 | 9496: PUSH2 0x248b | 9499: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
9500: JUMPDEST | 9501: POP | 9502: PUSH2 0x252e | 9505: PUSH1 0x80 | 9507: PUSH1 0x20 | 9509: DUP4 | 9510: ADD | 9511: MLOAD | 9512: SWAP3 | 9513: ADD | 9514: PUSH2 0x248b | 9517: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
9518: JUMPDEST | 9519: POP | 9520: CODESIZE | 9521: PUSH2 0x24d2 | 9524: JUMP    ;; CometWithExtendedAssetList.getPrice: IPriceFeed(priceFeed).latestRoundData()
9525: JUMPDEST | 9526: RETURNDATASIZE | 9527: SWAP2 | 9528: POP | 9529: PUSH2 0x24fd | 9532: JUMP    ;; CometWithExtendedAssetList.getPrice: IPriceFeed(priceFeed).latestRoundData()
9533: JUMPDEST | 9534: PUSH2 0x2545 | 9537: PUSH2 0x1bfe | 9540: JUMP    ;; CometWithExtendedAssetList.getPrice: IPriceFeed(priceFeed).latestRoundData()
9541: JUMPDEST | 9542: PUSH2 0x24ca | 9545: JUMP    ;; CometWithExtendedAssetList.getPrice: IPriceFeed(priceFeed).latestRoundData()
9546: JUMPDEST | 9547: SWAP1 | 9548: DUP2 | 9549: PUSH1 0x20 | 9551: SWAP2 | 9552: SUB | 9553: SLT | 9554: PUSH2 0x0582 | 9557: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
9558: MLOAD | 9559: SWAP1 | 9560: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
9561: JUMPDEST | 9562: PUSH1 0x40 | 9564: MLOAD | 9565: PUSH4 0x70a08231 | 9570: PUSH1 0xe0 | 9572: SHL | 9573: DUP2 | 9574: MSTORE | 9575: ADDRESS | 9576: PUSH1 0x04 | 9578: DUP3 | 9579: ADD | 9580: MSTORE | 9581: SWAP1 | 9582: PUSH1 0x01 | 9584: PUSH1 0x01 | 9586: PUSH1 0xa0 | 9588: SHL | 9589: SUB | 9590: AND | 9591: PUSH1 0x20 | 9593: DUP3 | 9594: PUSH1 0x24 | 9596: DUP2 | 9597: DUP5 | 9598: GAS | 9599: STATICCALL | 9600: SWAP2 | 9601: DUP3 | 9602: ISZERO | 9603: PUSH2 0x25e4 | 9606: JUMPI    ;; STATICCALL ;; CometWithExtendedAssetList.getCollateralReserves: IERC20NonStandard(asset).balanceOf(address(this))
9607: JUMPDEST | 9608: PUSH1 0x00 | 9610: SWAP3 | 9611: PUSH2 0x25b4 | 9614: JUMPI    ;; CometWithExtendedAssetList.getCollateralReserves: IERC20NonStandard(asset).balanceOf(address(this))
9615: JUMPDEST | 9616: POP | 9617: PUSH1 0x00 | 9619: SWAP1 | 9620: DUP2 | 9621: MSTORE | 9622: PUSH1 0x02 | 9624: PUSH1 0x20 | 9626: MSTORE | 9627: PUSH1 0x40 | 9629: SWAP1 | 9630: KECCAK256 | 9631: SLOAD | 9632: PUSH1 0x01 | 9634: PUSH1 0x01 | 9636: PUSH1 0x80 | 9638: SHL | 9639: SUB | 9640: AND | 9641: SWAP1 | 9642: DUP2 | 9643: DUP2 | 9644: LT | 9645: PUSH2 0x1e5f | 9648: JUMPI    ;; KECCAK256,SLOAD ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
9649: SUB | 9650: SWAP1 | 9651: JUMP    ;; CometWithExtendedAssetList.getCollateralReserves: function getCollateralReserves(address asset) override public view retu…
9652: JUMPDEST | 9653: PUSH2 0x25d6 | 9656: SWAP2 | 9657: SWAP3 | 9658: POP | 9659: PUSH1 0x20 | 9661: RETURNDATASIZE | 9662: DUP2 | 9663: GT | 9664: PUSH2 0x25dd | 9667: JUMPI    ;; CometWithExtendedAssetList.getCollateralReserves: IERC20NonStandard(asset).balanceOf(address(this))
9668: JUMPDEST | 9669: PUSH2 0x25ce | 9672: DUP2 | 9673: DUP4 | 9674: PUSH2 0x1b46 | 9677: JUMP    ;; CometWithExtendedAssetList.getCollateralReserves: IERC20NonStandard(asset).balanceOf(address(this))
9678: JUMPDEST | 9679: DUP2 | 9680: ADD | 9681: SWAP1 | 9682: PUSH2 0x254a | 9685: JUMP    ;; CometWithExtendedAssetList.getCollateralReserves: IERC20NonStandard(asset).balanceOf(address(this))
9686: JUMPDEST | 9687: SWAP1 | 9688: CODESIZE | 9689: PUSH2 0x258f | 9692: JUMP    ;; CometWithExtendedAssetList.getCollateralReserves: IERC20NonStandard(asset).balanceOf(address(this))
9693: JUMPDEST | 9694: POP | 9695: RETURNDATASIZE | 9696: PUSH2 0x25c4 | 9699: JUMP    ;; CometWithExtendedAssetList.getCollateralReserves: IERC20NonStandard(asset).balanceOf(address(this))
9700: JUMPDEST | 9701: PUSH2 0x25ec | 9704: PUSH2 0x1bfe | 9707: JUMP    ;; CometWithExtendedAssetList.getCollateralReserves: IERC20NonStandard(asset).balanceOf(address(this))
9708: JUMPDEST | 9709: PUSH2 0x2587 | 9712: JUMP    ;; CometWithExtendedAssetList.getCollateralReserves: IERC20NonStandard(asset).balanceOf(address(this))
9713: JUMPDEST | 9714: PUSH1 0x00 | 9716: DUP3 | 9717: SLT | 9718: DUP1 | 9719: ISZERO | 9720: PUSH1 0x01 | 9722: PUSH1 0xff | 9724: SHL | 9725: DUP5 | 9726: ADD | 9727: DUP4 | 9728: SLT | 9729: AND | 9730: PUSH2 0x261b | 9733: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
9734: JUMPDEST | 9735: PUSH1 0x01 | 9737: PUSH1 0x01 | 9739: PUSH1 0xff | 9741: SHL | 9742: SUB | 9743: DUP4 | 9744: ADD | 9745: DUP3 | 9746: SGT | 9747: AND | 9748: PUSH2 0x1e5f | 9751: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
9752: SUB | 9753: SWAP1 | 9754: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
9755: JUMPDEST | 9756: PUSH2 0x2623 | 9759: PUSH2 0x1e32 | 9762: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
9763: JUMPDEST | 9764: PUSH2 0x2606 | 9767: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
9768: JUMPDEST | 9769: PUSH1 0x00 | 9771: DUP2 | 9772: SLT | 9773: DUP1 | 9774: ISZERO | 9775: PUSH1 0x01 | 9777: PUSH1 0x01 | 9779: PUSH1 0xff | 9781: SHL | 9782: SUB | 9783: DUP4 | 9784: SWAP1 | 9785: SUB | 9786: DUP5 | 9787: SGT | 9788: AND | 9789: PUSH2 0x2654 | 9792: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
9793: JUMPDEST | 9794: PUSH1 0x01 | 9796: PUSH1 0xff | 9798: SHL | 9799: DUP3 | 9800: SWAP1 | 9801: SUB | 9802: DUP4 | 9803: SLT | 9804: AND | 9805: PUSH2 0x1eb3 | 9808: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
9809: ADD | 9810: SWAP1 | 9811: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
9812: JUMPDEST | 9813: PUSH2 0x265c | 9816: PUSH2 0x1e32 | 9819: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
9820: JUMPDEST | 9821: PUSH2 0x2641 | 9824: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
9825: JUMPDEST | 9826: PUSH2 0x0979 | 9829: PUSH2 0x266c | 9832: PUSH2 0x1dbe | 9835: JUMP    ;; CometWithExtendedAssetList.getReserves: getNowInternal()
9836: JUMPDEST | 9837: PUSH2 0x268f | 9840: PUSH2 0x268a | 9843: PUSH2 0x1ef6 | 9846: PUSH1 0x01 | 9848: SLOAD | 9849: SWAP4 | 9850: PUSH5 0xffffffffff | 9856: DUP6 | 9857: PUSH1 0xd0 | 9859: SHR | 9860: AND | 9861: SWAP1 | 9862: PUSH2 0x1e49 | 9865: JUMP    ;; SLOAD ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
9866: JUMPDEST | 9867: PUSH2 0x20fd | 9870: JUMP    ;; CometWithExtendedAssetList.getReserves: accruedInterestIndices(getNowInternal() - lastAccrualTime)
9871: JUMPDEST | 9872: SWAP1 | 9873: PUSH1 0x40 | 9875: MLOAD | 9876: SWAP3 | 9877: PUSH4 0x70a08231 | 9882: PUSH1 0xe0 | 9884: SHL | 9885: DUP5 | 9886: MSTORE | 9887: PUSH1 0x20 | 9889: DUP5 | 9890: DUP1 | 9891: PUSH2 0x26af | 9894: ADDRESS | 9895: PUSH1 0x04 | 9897: DUP4 | 9898: ADD | 9899: PUSH2 0x060e | 9902: JUMP    ;; CometWithExtendedAssetList.getReserves: IERC20NonStandard(baseToken).balanceOf(address(this))
9903: JUMPDEST | 9904: SUB | 9905: DUP2 | 9906: PUSH32 0x0000000000000000000000000000000000000000000000000000000000000000 | 9939: PUSH1 0x01 | 9941: PUSH1 0x01 | 9943: PUSH1 0xa0 | 9945: SHL | 9946: SUB | 9947: AND | 9948: GAS | 9949: STATICCALL | 9950: SWAP4 | 9951: DUP5 | 9952: ISZERO | 9953: PUSH2 0x2784 | 9956: JUMPI    ;; STATICCALL ;; CometWithExtendedAssetList.getReserves: IERC20NonStandard(baseToken).balanceOf(address(this))
9957: JUMPDEST | 9958: PUSH1 0x00 | 9960: SWAP5 | 9961: PUSH2 0x274c | 9964: JUMPI    ;; CometWithExtendedAssetList.getReserves: IERC20NonStandard(baseToken).balanceOf(address(this))
9965: JUMPDEST | 9966: POP | 9967: SWAP2 | 9968: PUSH2 0x2740 | 9971: PUSH2 0x273a | 9974: PUSH2 0x273a | 9977: SWAP4 | 9978: PUSH2 0x2733 | 9981: PUSH2 0x2746 | 9984: SWAP7 | 9985: PUSH7 0x038d7ea4c68000 | 9993: SWAP3 | 9994: PUSH1 0x01 | 9996: DUP1 | 9997: PUSH1 0x40 | 9999: SHL | 10000: SUB | 10001: DUP5 | 10002: PUSH2 0x2726 | 10005: DUP3 | 10006: PUSH1 0x01 | 10008: DUP1 | 10009: PUSH1 0x68 | 10011: SHL | 10012: SUB | 10013: SWAP5 | 10014: AND | 10015: DUP5 | 10016: DUP7 | 10017: AND | 10018: PUSH2 0x1e77 | 10021: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
10022: JUMPDEST | 10023: DIV | 10024: SWAP8 | 10025: AND | 10026: SWAP2 | 10027: PUSH1 0x68 | 10029: SHR | 10030: AND | 10031: PUSH2 0x1e77 | 10034: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
10035: JUMPDEST | 10036: DIV | 10037: SWAP6 | 10038: PUSH2 0x2791 | 10041: JUMP    ;; CometWithExtendedAssetList.getReserves: signed256(balance)
10042: JUMPDEST | 10043: SWAP2 | 10044: PUSH2 0x2791 | 10047: JUMP    ;; CometWithExtendedAssetList.getReserves: signed256(totalSupply_)
10048: JUMPDEST | 10049: SWAP1 | 10050: PUSH2 0x25f1 | 10053: JUMP    ;; CometWithExtendedAssetList.getReserves: signed256(balance) - signed256(totalSupply_)
10054: JUMPDEST | 10055: SWAP1 | 10056: PUSH2 0x2628 | 10059: JUMP    ;; CometWithExtendedAssetList.getReserves: signed256(balance) - signed256(totalSupply_) + signed256(totalBorrow_)
10060: JUMPDEST | 10061: PUSH2 0x2746 | 10064: SWAP4 | 10065: SWAP2 | 10066: SWAP5 | 10067: POP | 10068: PUSH2 0x273a | 10071: PUSH2 0x273a | 10074: SWAP4 | 10075: PUSH2 0x2733 | 10078: PUSH2 0x2777 | 10081: PUSH2 0x2740 | 10084: SWAP5 | 10085: PUSH1 0x20 | 10087: RETURNDATASIZE | 10088: DUP2 | 10089: GT | 10090: PUSH2 0x25dd | 10093: JUMPI    ;; CometWithExtendedAssetList.getReserves: IERC20NonStandard(baseToken).balanceOf(address(this))
10094: PUSH2 0x25ce | 10097: DUP2 | 10098: DUP4 | 10099: PUSH2 0x1b46 | 10102: JUMP    ;; CometWithExtendedAssetList.getReserves: IERC20NonStandard(baseToken).balanceOf(address(this))
10103: JUMPDEST | 10104: SWAP8 | 10105: SWAP5 | 10106: SWAP7 | 10107: POP | 10108: POP | 10109: SWAP4 | 10110: POP | 10111: POP | 10112: PUSH2 0x26ed | 10115: JUMP    ;; CometWithExtendedAssetList.getReserves: IERC20NonStandard(baseToken).balanceOf(address(this))
10116: JUMPDEST | 10117: PUSH2 0x278c | 10120: PUSH2 0x1bfe | 10123: JUMP    ;; CometWithExtendedAssetList.getReserves: IERC20NonStandard(baseToken).balanceOf(address(this))
10124: JUMPDEST | 10125: PUSH2 0x26e5 | 10128: JUMP    ;; CometWithExtendedAssetList.getReserves: IERC20NonStandard(baseToken).balanceOf(address(this))
10129: JUMPDEST | 10130: PUSH1 0x01 | 10132: PUSH1 0x01 | 10134: PUSH1 0xff | 10136: SHL | 10137: SUB | 10138: DUP2 | 10139: GT | 10140: PUSH2 0x27a2 | 10143: JUMPI    ;; CometMath.signed256: n > uint256(type(int256).max)
10144: SWAP1 | 10145: JUMP    ;; CometMath.signed256: function signed256(uint256 n) internal pure returns (int256) { if (n > …
10146: JUMPDEST | 10147: PUSH1 0x40 | 10149: MLOAD | 10150: PUSH4 0xe7e828ad | 10155: PUSH1 0xe0 | 10157: SHL | 10158: DUP2 | 10159: MSTORE | 10160: PUSH1 0x04 | 10162: SWAP1 | 10163: REVERT    ;; CometMath.signed256: InvalidInt256()
10164: JUMPDEST | 10165: PUSH2 0x27c9 | 10168: PUSH2 0x27c2 | 10171: DUP3 | 10172: PUSH1 0x05 | 10174: PUSH2 0x097c | 10177: JUMP    ;; CometWithExtendedAssetList.isBorrowCollateralized: userBasic[account]
10178: JUMPDEST | 10179: SLOAD | 10180: PUSH1 0x0c | 10182: SIGNEXTEND | 10183: SWAP1 | 10184: JUMP    ;; SLOAD ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
10185: JUMPDEST | 10186: SWAP1 | 10187: PUSH1 0x00 | 10189: SWAP2 | 10190: DUP3 | 10191: DUP2 | 10192: PUSH1 0x0c | 10194: SIGNEXTEND | 10195: SLT | 10196: ISZERO | 10197: PUSH2 0x2981 | 10200: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
10201: PUSH2 0x27f1 | 10204: PUSH2 0x27e6 | 10207: DUP4 | 10208: PUSH1 0x05 | 10210: PUSH2 0x097c | 10213: JUMP    ;; CometWithExtendedAssetList.isBorrowCollateralized: userBasic[account]
10214: JUMPDEST | 10215: SLOAD | 10216: PUSH1 0xe8 | 10218: SHR | 10219: PUSH2 0xffff | 10222: AND | 10223: SWAP1 | 10224: JUMP    ;; SLOAD ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
10225: JUMPDEST | 10226: SWAP1 | 10227: PUSH2 0x286c | 10230: PUSH2 0x2813 | 10233: PUSH2 0x280d | 10236: PUSH2 0x2806 | 10239: DUP7 | 10240: PUSH1 0x05 | 10242: PUSH2 0x097c | 10245: JUMP    ;; CometWithExtendedAssetList.isBorrowCollateralized: userBasic[account]
10246: JUMPDEST | 10247: SLOAD | 10248: PUSH1 0xf8 | 10250: SHR | 10251: SWAP1 | 10252: JUMP    ;; SLOAD ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
10253: JUMPDEST | 10254: SWAP3 | 10255: PUSH2 0x29c0 | 10258: JUMP    ;; CometWithExtendedAssetList.isBorrowCollateralized: presentValue(principal)
10259: JUMPDEST | 10260: PUSH2 0x283c | 10263: PUSH32 0x0000000000000000000000000000000000000000000000000000000000000000 | 10296: PUSH2 0x249f | 10299: JUMP    ;; CometWithExtendedAssetList.isBorrowCollateralized: getPrice(baseTokenPriceFeed)
10300: JUMPDEST | 10301: PUSH32 0x0000000000000000000000000000000000000000000000000000000000000000 | 10334: PUSH1 0x01 | 10336: PUSH1 0x01 | 10338: PUSH1 0x40 | 10340: SHL | 10341: SUB | 10342: AND | 10343: SWAP2 | 10344: PUSH2 0x2bda | 10347: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
10348: JUMPDEST | 10349: SWAP3 | 10350: DUP5 | 10351: SWAP2 | 10352: PUSH1 0xff | 10354: SWAP4 | 10355: DUP5 | 10356: PUSH32 0x0000000000000000000000000000000000000000000000000000000000000000 | 10389: AND | 10390: SWAP4    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
10391: JUMPDEST | 10392: DUP5 | 10393: DUP7 | 10394: DUP3 | 10395: AND | 10396: LT | 10397: PUSH2 0x28ab | 10400: JUMPI    ;; CometWithExtendedAssetList.isBorrowCollateralized: i < numAssets
10401: POP | 10402: POP | 10403: POP | 10404: POP | 10405: POP | 10406: POP | 10407: SLT | 10408: ISZERO | 10409: SWAP1 | 10410: JUMP    ;; CometWithExtendedAssetList.isBorrowCollateralized: liquidity >= 0
10411: JUMPDEST | 10412: PUSH2 0x28b6 | 10415: DUP4 | 10416: DUP3 | 10417: DUP5 | 10418: PUSH2 0x2cc0 | 10421: JUMP    ;; CometWithExtendedAssetList.isBorrowCollateralized: isInAsset(assetsIn, i, _reserved)
10422: JUMPDEST | 10423: PUSH2 0x28c5 | 10426: JUMPI    ;; CometWithExtendedAssetList.isBorrowCollateralized: if (isInAsset(assetsIn, i, _reserved)) { if (liquidity >= 0) { return t…
10427: JUMPDEST | 10428: PUSH1 0x01 | 10430: ADD | 10431: DUP6 | 10432: AND | 10433: PUSH2 0x2897 | 10436: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
10437: JUMPDEST | 10438: SWAP6 | 10439: DUP8 | 10440: DUP2 | 10441: SLT | 10442: ISZERO | 10443: PUSH2 0x2974 | 10446: JUMPI    ;; CometWithExtendedAssetList.isBorrowCollateralized: liquidity >= 0
10447: PUSH1 0x01 | 10449: PUSH2 0x296b | 10452: DUP8 | 10453: SWAP3 | 10454: PUSH2 0x2746 | 10457: PUSH2 0x2966 | 10460: DUP9 | 10461: PUSH2 0x2960 | 10464: PUSH2 0x295b | 10467: PUSH1 0x80 | 10469: DUP16 | 10470: PUSH2 0x2923 | 10473: PUSH2 0x2916 | 10476: PUSH2 0x2902 | 10479: PUSH2 0x28fa | 10482: PUSH2 0x2953 | 10485: SWAP5 | 10486: PUSH2 0x1c0b | 10489: JUMP    ;; CometWithExtendedAssetList.isBorrowCollateralized: getAssetInfo(i)
10490: JUMPDEST | 10491: SWAP8 | 10492: PUSH1 0x06 | 10494: PUSH2 0x097c | 10497: JUMP    ;; CometWithExtendedAssetList.isBorrowCollateralized: userCollateral[account]
10498: JUMPDEST | 10499: PUSH1 0x20 | 10501: DUP9 | 10502: ADD | 10503: MLOAD | 10504: PUSH1 0x01 | 10506: PUSH1 0x01 | 10508: PUSH1 0xa0 | 10510: SHL | 10511: SUB | 10512: AND | 10513: SWAP1 | 10514: PUSH2 0x097c | 10517: JUMP    ;; CometWithExtendedAssetList.isBorrowCollateralized: asset.asset
10518: JUMPDEST | 10519: SLOAD | 10520: PUSH1 0x01 | 10522: PUSH1 0x01 | 10524: PUSH1 0x80 | 10526: SHL | 10527: SUB | 10528: AND | 10529: SWAP1 | 10530: JUMP    ;; SLOAD ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
10531: JUMPDEST | 10532: PUSH1 0x40 | 10534: DUP7 | 10535: ADD | 10536: MLOAD | 10537: PUSH2 0x293a | 10540: SWAP1 | 10541: PUSH1 0x01 | 10543: PUSH1 0x01 | 10545: PUSH1 0xa0 | 10547: SHL | 10548: SUB | 10549: AND | 10550: PUSH2 0x249f | 10553: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
10554: JUMPDEST | 10555: PUSH2 0x2947 | 10558: PUSH1 0x60 | 10560: DUP9 | 10561: ADD | 10562: MLOAD | 10563: PUSH2 0x0b8f | 10566: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
10567: JUMPDEST | 10568: SWAP2 | 10569: DUP13 | 10570: DUP1 | 10571: DUP7 | 10572: SHL | 10573: SUB | 10574: AND | 10575: PUSH2 0x2bba | 10578: JUMP    ;; CometCore helper: 1e15
10579: JUMPDEST | 10580: SWAP4 | 10581: ADD | 10582: MLOAD | 10583: PUSH2 0x0b8f | 10586: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
10587: JUMPDEST | 10588: PUSH2 0x0b8f | 10591: JUMP    ;; CometWithExtendedAssetList.isBorrowCollateralized: mulFactor( newAmount, asset.borrowCollateralFactor )
10592: JUMPDEST | 10593: SWAP1 | 10594: PUSH2 0x2b7c | 10597: JUMP    ;; CometWithExtendedAssetList.isBorrowCollateralized: mulFactor( newAmount, asset.borrowCollateralFactor )
10598: JUMPDEST | 10599: PUSH2 0x2791 | 10602: JUMP    ;; CometWithExtendedAssetList.isBorrowCollateralized: signed256(mulFactor( newAmount, asset.borrowCollateralFactor ))
10603: JUMPDEST | 10604: SWAP8 | 10605: SWAP2 | 10606: POP | 10607: POP | 10608: PUSH2 0x28bb | 10611: JUMP    ;; CometWithExtendedAssetList.isBorrowCollateralized: if (isInAsset(assetsIn, i, _reserved)) { if (liquidity >= 0) { return t…
10612: JUMPDEST | 10613: POP | 10614: POP | 10615: POP | 10616: POP | 10617: POP | 10618: POP | 10619: POP | 10620: POP | 10621: PUSH1 0x01 | 10623: SWAP1 | 10624: JUMP    ;; CometWithExtendedAssetList.isBorrowCollateralized: return true
10625: JUMPDEST | 10626: POP | 10627: POP | 10628: POP | 10629: PUSH1 0x01 | 10631: SWAP1 | 10632: JUMP    ;; CometWithExtendedAssetList.isBorrowCollateralized: return true
10633: JUMPDEST | 10634: PUSH1 0x0c | 10636: SIGNEXTEND | 10637: PUSH1 0x01 | 10639: PUSH1 0x01 | 10641: PUSH1 0x67 | 10643: SHL | 10644: SUB | 10645: NOT | 10646: DUP2 | 10647: EQ | 10648: PUSH2 0x29a2 | 10651: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
10652: JUMPDEST | 10653: PUSH1 0x00 | 10655: SUB | 10656: SWAP1 | 10657: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
10658: JUMPDEST | 10659: PUSH2 0x29aa | 10662: PUSH2 0x1e32 | 10665: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
10666: JUMPDEST | 10667: PUSH2 0x299c | 10670: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
10671: JUMPDEST | 10672: PUSH1 0x01 | 10674: PUSH1 0xff | 10676: SHL | 10677: DUP2 | 10678: EQ | 10679: PUSH2 0x29a2 | 10682: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
10683: PUSH1 0x00 | 10685: SUB | 10686: SWAP1 | 10687: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
10688: JUMPDEST | 10689: PUSH1 0x00 | 10691: PUSH1 0x0c | 10693: DUP3 | 10694: SWAP1 | 10695: SIGNEXTEND | 10696: SLT | 10697: PUSH2 0x2a00 | 10700: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
10701: PUSH1 0x00 | 10703: SLOAD | 10704: PUSH2 0x0979 | 10707: SWAP2 | 10708: PUSH7 0x038d7ea4c68000 | 10716: SWAP2 | 10717: PUSH2 0x29fa | 10720: SWAP2 | 10721: PUSH1 0x01 | 10723: PUSH1 0x01 | 10725: PUSH1 0x40 | 10727: SHL | 10728: SUB | 10729: SWAP1 | 10730: SWAP2 | 10731: AND | 10732: SWAP1 | 10733: PUSH1 0x01 | 10735: PUSH1 0x01 | 10737: PUSH1 0x68 | 10739: SHL | 10740: SUB | 10741: AND | 10742: PUSH2 0x1e77 | 10745: JUMP    ;; SLOAD ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
10746: JUMPDEST | 10747: DIV | 10748: PUSH2 0x2791 | 10751: JUMP    ;; CometCore.presentValue: signed256(presentValueSupply(baseSupplyIndex, uint104(principalValue_)))
10752: JUMPDEST | 10753: PUSH2 0x2a30 | 10756: PUSH2 0x2966 | 10759: PUSH2 0x0979 | 10762: SWAP3 | 10763: PUSH2 0x2a21 | 10766: PUSH1 0x01 | 10768: DUP1 | 10769: PUSH1 0x40 | 10771: SHL | 10772: SUB | 10773: PUSH1 0x00 | 10775: SLOAD | 10776: PUSH1 0x40 | 10778: SHR | 10779: AND | 10780: SWAP2 | 10781: PUSH2 0x2989 | 10784: JUMP    ;; SLOAD ;; CometCore helper: 1e15
10785: JUMPDEST | 10786: PUSH1 0x01 | 10788: PUSH1 0x01 | 10790: PUSH1 0x68 | 10792: SHL | 10793: SUB | 10794: AND | 10795: SWAP1 | 10796: PUSH2 0x2466 | 10799: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
10800: JUMPDEST | 10801: PUSH2 0x29af | 10804: JUMP    ;; CometCore.presentValue: -signed256(presentValueBorrow(baseBorrowIndex, uint104(-principalValue_…
10805: JUMPDEST | 10806: PUSH2 0x2a43 | 10809: PUSH2 0x27c2 | 10812: DUP3 | 10813: PUSH1 0x05 | 10815: PUSH2 0x097c | 10818: JUMP    ;; CometWithExtendedAssetList.isLiquidatable: userBasic[account]
10819: JUMPDEST | 10820: SWAP1 | 10821: PUSH1 0x00 | 10823: SWAP2 | 10824: DUP3 | 10825: DUP2 | 10826: PUSH1 0x0c | 10828: SIGNEXTEND | 10829: SLT | 10830: ISZERO | 10831: PUSH2 0x2b46 | 10834: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
10835: PUSH2 0x2a60 | 10838: PUSH2 0x27e6 | 10841: DUP4 | 10842: PUSH1 0x05 | 10844: PUSH2 0x097c | 10847: JUMP    ;; CometWithExtendedAssetList.isLiquidatable: userBasic[account]
10848: JUMPDEST | 10849: SWAP1 | 10850: PUSH2 0x2a75 | 10853: PUSH2 0x2813 | 10856: PUSH2 0x280d | 10859: PUSH2 0x2806 | 10862: DUP7 | 10863: PUSH1 0x05 | 10865: PUSH2 0x097c | 10868: JUMP    ;; CometWithExtendedAssetList.isLiquidatable: userBasic[account]
10869: JUMPDEST | 10870: SWAP3 | 10871: DUP5 | 10872: SWAP2 | 10873: PUSH1 0xff | 10875: SWAP4 | 10876: DUP5 | 10877: PUSH32 0x0000000000000000000000000000000000000000000000000000000000000000 | 10910: AND | 10911: SWAP4    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
10912: JUMPDEST | 10913: DUP5 | 10914: DUP7 | 10915: DUP3 | 10916: AND | 10917: LT | 10918: PUSH2 0x2ab3 | 10921: JUMPI    ;; CometWithExtendedAssetList.isLiquidatable: i < numAssets
10922: POP | 10923: POP | 10924: POP | 10925: POP | 10926: POP | 10927: POP | 10928: SLT | 10929: SWAP1 | 10930: JUMP    ;; CometWithExtendedAssetList.isLiquidatable: liquidity < 0
10931: JUMPDEST | 10932: PUSH2 0x2abe | 10935: DUP4 | 10936: DUP3 | 10937: DUP5 | 10938: PUSH2 0x2cc0 | 10941: JUMP    ;; CometWithExtendedAssetList.isLiquidatable: isInAsset(assetsIn, i, _reserved)
10942: JUMPDEST | 10943: PUSH2 0x2acd | 10946: JUMPI    ;; CometWithExtendedAssetList.isLiquidatable: if (isInAsset(assetsIn, i, _reserved)) { if (liquidity >= 0) { return f…
10947: JUMPDEST | 10948: PUSH1 0x01 | 10950: ADD | 10951: DUP6 | 10952: AND | 10953: PUSH2 0x2aa0 | 10956: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
10957: JUMPDEST | 10958: SWAP6 | 10959: DUP8 | 10960: DUP2 | 10961: SLT | 10962: ISZERO | 10963: PUSH2 0x2b3c | 10966: JUMPI    ;; CometWithExtendedAssetList.isLiquidatable: liquidity >= 0
10967: PUSH1 0x01 | 10969: PUSH2 0x2b33 | 10972: DUP8 | 10973: SWAP3 | 10974: PUSH2 0x2746 | 10977: PUSH2 0x2966 | 10980: DUP9 | 10981: PUSH2 0x2960 | 10984: PUSH2 0x295b | 10987: PUSH1 0xa0 | 10989: DUP16 | 10990: PUSH2 0x2b02 | 10993: PUSH2 0x2916 | 10996: PUSH2 0x2902 | 10999: PUSH2 0x28fa | 11002: PUSH2 0x2953 | 11005: SWAP5 | 11006: PUSH2 0x1c0b | 11009: JUMP    ;; CometWithExtendedAssetList.isLiquidatable: getAssetInfo(i)
11010: JUMPDEST | 11011: PUSH1 0x40 | 11013: DUP7 | 11014: ADD | 11015: MLOAD | 11016: PUSH2 0x2b19 | 11019: SWAP1 | 11020: PUSH1 0x01 | 11022: PUSH1 0x01 | 11024: PUSH1 0xa0 | 11026: SHL | 11027: SUB | 11028: AND | 11029: PUSH2 0x249f | 11032: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
11033: JUMPDEST | 11034: PUSH2 0x2b26 | 11037: PUSH1 0x60 | 11039: DUP9 | 11040: ADD | 11041: MLOAD | 11042: PUSH2 0x0b8f | 11045: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
11046: JUMPDEST | 11047: SWAP2 | 11048: DUP13 | 11049: DUP1 | 11050: PUSH1 0x80 | 11052: SHL | 11053: SUB | 11054: AND | 11055: PUSH2 0x2bba | 11058: JUMP    ;; CometCore helper: 1e15
11059: JUMPDEST | 11060: SWAP8 | 11061: SWAP2 | 11062: POP | 11063: POP | 11064: PUSH2 0x2ac3 | 11067: JUMP    ;; CometWithExtendedAssetList.isLiquidatable: if (isInAsset(assetsIn, i, _reserved)) { if (liquidity >= 0) { return f…
11068: JUMPDEST | 11069: POP | 11070: POP | 11071: POP | 11072: POP | 11073: POP | 11074: POP | 11075: POP | 11076: SWAP1 | 11077: JUMP    ;; CometWithExtendedAssetList.isLiquidatable: return false
11078: JUMPDEST | 11079: POP | 11080: POP | 11081: SWAP1 | 11082: JUMP    ;; CometWithExtendedAssetList.isLiquidatable: return false
11083: JUMPDEST | 11084: DUP1 | 11085: SLOAD | 11086: PUSH1 0x01 | 11088: PUSH1 0x01 | 11090: PUSH1 0xf8 | 11092: SHL | 11093: SUB | 11094: AND | 11095: PUSH1 0xf8 | 11097: SWAP3 | 11098: SWAP1 | 11099: SWAP3 | 11100: SHL | 11101: PUSH1 0x01 | 11103: PUSH1 0x01 | 11105: PUSH1 0xf8 | 11107: SHL | 11108: SUB | 11109: NOT | 11110: AND | 11111: SWAP2 | 11112: SWAP1 | 11113: SWAP2 | 11114: OR | 11115: SWAP1 | 11116: SSTORE | 11117: JUMP    ;; SLOAD,SSTORE ;; CometCore helper: 4
11118: JUMPDEST | 11119: PUSH1 0x00 | 11121: SWAP1 | 11122: ISZERO | 11123: PUSH2 0x0979 | 11126: JUMPI    ;; CometMath.toUInt8: x ? 1 : 0
11127: POP | 11128: PUSH1 0x01 | 11130: SWAP1 | 11131: JUMP    ;; CometMath.toUInt8: function toUInt8(bool x) internal pure returns (uint8) { return x ? 1 :…
11132: JUMPDEST | 11133: PUSH8 0x0de0b6b3a7640000 | 11142: SWAP2 | 11143: PUSH2 0x23e8 | 11146: SWAP2 | 11147: PUSH2 0x1e77 | 11150: JUMP    ;; CometWithExtendedAssetList.mulFactor: function mulFactor(uint n, uint factor) internal pure returns (uint) { …
11151: JUMPDEST | 11152: PUSH2 0x23d6 | 11155: SWAP1 | 11156: PUSH32 0x0000000000000000000000000000000000000000000000000000000000000000 | 11189: SWAP1 | 11190: PUSH2 0x1e77 | 11193: JUMP    ;; CometWithExtendedAssetList.divBaseWei: n * baseScale
11194: JUMPDEST | 11195: SWAP1 | 11196: PUSH2 0x2bc4 | 11199: SWAP2 | 11200: PUSH2 0x1e77 | 11203: JUMP    ;; CometWithExtendedAssetList.mulPrice: function mulPrice(uint n, uint price, uint64 fromScale) internal pure r…
11204: JUMPDEST | 11205: PUSH1 0x01 | 11207: PUSH1 0x01 | 11209: PUSH1 0x40 | 11211: SHL | 11212: SUB | 11213: SWAP1 | 11214: SWAP2 | 11215: AND | 11216: SWAP1 | 11217: DUP2 | 11218: ISZERO | 11219: PUSH2 0x23e0 | 11222: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
11223: DIV | 11224: SWAP1 | 11225: JUMP    ;; CometWithExtendedAssetList.mulPrice: function mulPrice(uint n, uint price, uint64 fromScale) internal pure r…
11226: JUMPDEST | 11227: SWAP2 | 11228: SWAP1 | 11229: PUSH2 0x2be5 | 11232: SWAP1 | 11233: PUSH2 0x2791 | 11236: JUMP    ;; CometWithExtendedAssetList.signedMulPrice: function signedMulPrice(int n, uint price, uint64 fromScale) internal p…
11237: JUMPDEST | 11238: PUSH1 0x00 | 11240: DUP1 | 11241: DUP5 | 11242: SGT | 11243: SWAP4 | 11244: SWAP1 | 11245: DUP3 | 11246: SGT | 11247: PUSH1 0x01 | 11249: PUSH1 0x01 | 11251: PUSH1 0xff | 11253: SHL | 11254: SUB | 11255: DUP6 | 11256: DUP3 | 11257: AND | 11258: DUP5 | 11259: DUP3 | 11260: DIV | 11261: DUP5 | 11262: GT | 11263: AND | 11264: PUSH2 0x2ca1 | 11267: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
11268: JUMPDEST | 11269: PUSH1 0x01 | 11271: PUSH1 0xff | 11273: SHL | 11274: SWAP6 | 11275: PUSH1 0x00 | 11277: DUP6 | 11278: SLT | 11279: SWAP2 | 11280: DUP6 | 11281: SWAP2 | 11282: DUP4 | 11283: AND | 11284: DUP6 | 11285: DUP10 | 11286: SDIV | 11287: DUP4 | 11288: SLT | 11289: AND | 11290: PUSH2 0x2c94 | 11293: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
11294: JUMPDEST | 11295: PUSH1 0x00 | 11297: DUP6 | 11298: SLT | 11299: SWAP4 | 11300: DUP5 | 11301: AND | 11302: DUP3 | 11303: DUP10 | 11304: SDIV | 11305: DUP7 | 11306: SLT | 11307: AND | 11308: PUSH2 0x2c87 | 11311: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
11312: JUMPDEST | 11313: SDIV | 11314: DUP4 | 11315: SLT | 11316: SWAP2 | 11317: AND | 11318: AND | 11319: PUSH2 0x2c7a | 11322: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
11323: JUMPDEST | 11324: PUSH1 0x01 | 11326: PUSH1 0x01 | 11328: PUSH1 0x40 | 11330: SHL | 11331: SUB | 11332: SWAP1 | 11333: SWAP3 | 11334: AND | 11335: SWAP3 | 11336: SWAP2 | 11337: MUL | 11338: SWAP1 | 11339: DUP3 | 11340: ISZERO | 11341: PUSH2 0x2c6d | 11344: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
11345: JUMPDEST | 11346: DUP2 | 11347: EQ | 11348: PUSH1 0x00 | 11350: NOT | 11351: DUP4 | 11352: EQ | 11353: AND | 11354: PUSH2 0x2c61 | 11357: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
11358: SDIV | 11359: SWAP1 | 11360: JUMP    ;; CometWithExtendedAssetList.signedMulPrice: function signedMulPrice(int n, uint price, uint64 fromScale) internal p…
11361: JUMPDEST | 11362: PUSH2 0x2c69 | 11365: PUSH2 0x1e32 | 11368: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
11369: JUMPDEST | 11370: SDIV | 11371: SWAP1 | 11372: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
11373: JUMPDEST | 11374: PUSH2 0x2c75 | 11377: PUSH2 0x23bf | 11380: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
11381: JUMPDEST | 11382: PUSH2 0x2c51 | 11385: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
11386: JUMPDEST | 11387: PUSH2 0x2c82 | 11390: PUSH2 0x1e32 | 11393: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
11394: JUMPDEST | 11395: PUSH2 0x2c3b | 11398: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
11399: JUMPDEST | 11400: PUSH2 0x2c8f | 11403: PUSH2 0x1e32 | 11406: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
11407: JUMPDEST | 11408: PUSH2 0x2c30 | 11411: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
11412: JUMPDEST | 11413: PUSH2 0x2c9c | 11416: PUSH2 0x1e32 | 11419: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
11420: JUMPDEST | 11421: PUSH2 0x2c1e | 11424: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
11425: JUMPDEST | 11426: PUSH2 0x2ca9 | 11429: PUSH2 0x1e32 | 11432: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
11433: JUMPDEST | 11434: PUSH2 0x2c04 | 11437: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
11438: JUMPDEST | 11439: PUSH1 0xff | 11441: SWAP2 | 11442: DUP3 | 11443: AND | 11444: SWAP2 | 11445: AND | 11446: DUP2 | 11447: DUP2 | 11448: LT | 11449: PUSH2 0x1e5f | 11452: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
11453: SUB | 11454: SWAP1 | 11455: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
11456: JUMPDEST | 11457: SWAP1 | 11458: PUSH1 0xff | 11460: AND | 11461: SWAP2 | 11462: PUSH1 0x10 | 11464: DUP4 | 11465: LT | 11466: PUSH1 0x00 | 11468: EQ | 11469: PUSH2 0x2cdf | 11472: JUMPI    ;; CometWithExtendedAssetList.isInAsset: 16
11473: POP | 11474: PUSH1 0x01 | 11476: PUSH2 0xffff | 11479: SWAP3 | 11480: SHL | 11481: AND | 11482: AND | 11483: ISZERO | 11484: ISZERO | 11485: SWAP1 | 11486: JUMP    ;; CometCore helper: 0
11487: JUMPDEST | 11488: SWAP1 | 11489: POP | 11490: PUSH1 0x18 | 11492: DUP3 | 11493: LT | 11494: PUSH2 0x2cf0 | 11497: JUMPI    ;; CometWithExtendedAssetList.isInAsset: assetOffset < 24
11498: POP | 11499: POP | 11500: PUSH1 0x00 | 11502: SWAP1 | 11503: JUMP    ;; CometWithExtendedAssetList.isInAsset: if (assetOffset < 16) { // check bit in assetsIn (for bits 0-15) return…
11504: JUMPDEST | 11505: PUSH1 0x01 | 11507: PUSH1 0xff | 11509: DUP1 | 11510: SWAP4 | 11511: PUSH1 0x0f | 11513: NOT | 11514: ADD | 11515: AND | 11516: SHL | 11517: AND | 11518: AND | 11519: ISZERO | 11520: ISZERO | 11521: SWAP1 | 11522: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
11523: JUMPDEST | 11524: PUSH1 0x01 | 11526: PUSH1 0x01 | 11528: PUSH1 0x40 | 11530: SHL | 11531: SUB | 11532: SWAP2 | 11533: DUP3 | 11534: AND | 11535: SWAP2 | 11536: AND | 11537: DUP2 | 11538: DUP2 | 11539: LT | 11540: PUSH2 0x1e5f | 11543: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
11544: SUB | 11545: SWAP1 | 11546: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
11547: JUMPDEST | 11548: DUP1 | 11549: SLOAD | 11550: PUSH2 0xffff | 11553: PUSH1 0xe8 | 11555: SHL | 11556: NOT | 11557: AND | 11558: PUSH1 0xe8 | 11560: SWAP3 | 11561: SWAP1 | 11562: SWAP3 | 11563: SHL | 11564: PUSH2 0xffff | 11567: PUSH1 0xe8 | 11569: SHL | 11570: AND | 11571: SWAP2 | 11572: SWAP1 | 11573: SWAP2 | 11574: OR | 11575: SWAP1 | 11576: SSTORE | 11577: JUMP    ;; SLOAD,SSTORE ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
11578: JUMPDEST | 11579: DUP2 | 11580: MLOAD | 11581: DUP2 | 11582: SLOAD | 11583: PUSH1 0x20 | 11585: DUP5 | 11586: ADD | 11587: MLOAD | 11588: PUSH1 0x40 | 11590: DUP6 | 11591: ADD | 11592: MLOAD | 11593: PUSH1 0x01 | 11595: PUSH1 0x01 | 11597: PUSH1 0xe8 | 11599: SHL | 11600: SUB | 11601: NOT | 11602: SWAP1 | 11603: SWAP3 | 11604: AND | 11605: PUSH1 0x01 | 11607: PUSH1 0x01 | 11609: PUSH1 0x68 | 11611: SHL | 11612: SUB | 11613: SWAP1 | 11614: SWAP4 | 11615: AND | 11616: SWAP3 | 11617: SWAP1 | 11618: SWAP3 | 11619: OR | 11620: PUSH1 0x68 | 11622: SWAP3 | 11623: SWAP1 | 11624: SWAP3 | 11625: SHL | 11626: PUSH1 0x01 | 11628: PUSH1 0x68 | 11630: SHL | 11631: PUSH1 0x01 | 11633: PUSH1 0xa8 | 11635: SHL | 11636: SUB | 11637: AND | 11638: SWAP2 | 11639: SWAP1 | 11640: SWAP2 | 11641: OR | 11642: PUSH1 0xa8 | 11644: SWAP2 | 11645: SWAP1 | 11646: SWAP2 | 11647: SHL | 11648: PUSH1 0x01 | 11650: PUSH1 0xa8 | 11652: SHL | 11653: PUSH1 0x01 | 11655: PUSH1 0xe8 | 11657: SHL | 11658: SUB | 11659: AND | 11660: OR | 11661: DUP2 | 11662: SSTORE | 11663: PUSH1 0x60 | 11665: DUP3 | 11666: ADD | 11667: MLOAD | 11668: PUSH2 0x0c31 | 11671: SWAP3 | 11672: PUSH1 0xff | 11674: SWAP2 | 11675: PUSH1 0x80 | 11677: SWAP2 | 11678: SWAP1 | 11679: PUSH2 0x2dac | 11682: SWAP1 | 11683: PUSH2 0xffff | 11686: AND | 11687: DUP6 | 11688: PUSH2 0x2d1b | 11691: JUMP    ;; SLOAD,SSTORE ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
11692: JUMPDEST | 11693: ADD | 11694: MLOAD | 11695: AND | 11696: SWAP1 | 11697: PUSH2 0x2b4b | 11700: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
11701: JUMPDEST | 11702: PUSH2 0x2ecc | 11705: SWAP1 | 11706: PUSH2 0x0c31 | 11709: SWAP4 | 11710: PUSH2 0x2dc8 | 11713: DUP5 | 11714: MLOAD | 11715: PUSH1 0x0c | 11717: SIGNEXTEND | 11718: SWAP1 | 11719: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
11720: JUMPDEST | 11721: PUSH1 0x0c | 11723: DUP3 | 11724: SWAP1 | 11725: SIGNEXTEND | 11726: DUP6 | 11727: MSTORE | 11728: PUSH1 0x00 | 11730: SWAP2 | 11731: DUP3 | 11732: SWAP2 | 11733: DUP7 | 11734: DUP4 | 11735: PUSH1 0x0c | 11737: DUP4 | 11738: SWAP1 | 11739: SIGNEXTEND | 11740: DUP2 | 11741: SGT | 11742: PUSH2 0x2ee3 | 11745: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
11746: PUSH2 0x2e55 | 11749: PUSH2 0x2e2e | 11752: PUSH2 0x2e9b | 11755: SWAP5 | 11756: PUSH2 0x2e1f | 11759: PUSH2 0x295b | 11762: PUSH2 0x2e7c | 11765: SWAP7 | 11766: PUSH2 0x2e19 | 11769: PUSH1 0x20 | 11771: PUSH2 0x2e11 | 11774: PUSH2 0x2025 | 11777: SWAP10 | 11778: SLOAD | 11779: PUSH1 0x01 | 11781: DUP1 | 11782: PUSH1 0x40 | 11784: SHL | 11785: SUB | 11786: SWAP1 | 11787: PUSH1 0x80 | 11789: SHR | 11790: AND | 11791: SWAP1 | 11792: JUMP    ;; SLOAD ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
11793: JUMPDEST | 11794: SWAP3 | 11795: ADD | 11796: MLOAD | 11797: PUSH2 0x0b8f | 11800: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
11801: JUMPDEST | 11802: SWAP1 | 11803: PUSH2 0x2d03 | 11806: JUMP    ;; CometWithExtendedAssetList.updateBasePrincipal: trackingSupplyIndex - basic.baseTrackingIndex
11807: JUMPDEST | 11808: SWAP1 | 11809: PUSH1 0x01 | 11811: PUSH1 0x01 | 11813: PUSH1 0x68 | 11815: SHL | 11816: SUB | 11817: AND | 11818: PUSH2 0x1e77 | 11821: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
11822: JUMPDEST | 11823: PUSH32 0x0000000000000000000000000000000000000000000000000000000000000000 | 11856: SWAP1 | 11857: PUSH2 0x23d6 | 11860: JUMP    ;; CometWithExtendedAssetList.updateBasePrincipal: uint104(principal) * indexDelta / trackingIndexScale
11861: JUMPDEST | 11862: PUSH32 0x0000000000000000000000000000000000000000000000000000000000000000 | 11895: SWAP1 | 11896: PUSH2 0x23d6 | 11899: JUMP    ;; CometWithExtendedAssetList.updateBasePrincipal: uint104(principal) * indexDelta / trackingIndexScale / accrualDescaleFa…
11900: JUMPDEST | 11901: PUSH2 0x2e8e | 11904: PUSH1 0x40 | 11906: DUP10 | 11907: ADD | 11908: SWAP2 | 11909: PUSH2 0x2034 | 11912: DUP4 | 11913: MLOAD | 11914: PUSH2 0x0b8f | 11917: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
11918: JUMPDEST | 11919: PUSH1 0x01 | 11921: PUSH1 0x01 | 11923: PUSH1 0x40 | 11925: SHL | 11926: SUB | 11927: AND | 11928: SWAP1 | 11929: MSTORE | 11930: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
11931: JUMPDEST | 11932: PUSH1 0x0c | 11934: SIGNEXTEND | 11935: SLT | 11936: PUSH2 0x2ed1 | 11939: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
11940: SLOAD | 11941: PUSH2 0x2ec5 | 11944: SWAP1 | 11945: PUSH1 0x80 | 11947: SHR | 11948: PUSH1 0x01 | 11950: PUSH1 0x01 | 11952: PUSH1 0x40 | 11954: SHL | 11955: SUB | 11956: AND    ;; SLOAD ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
11957: JUMPDEST | 11958: PUSH1 0x01 | 11960: PUSH1 0x01 | 11962: PUSH1 0x40 | 11964: SHL | 11965: SUB | 11966: AND | 11967: PUSH1 0x20 | 11969: DUP6 | 11970: ADD | 11971: MSTORE | 11972: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
11973: JUMPDEST | 11974: PUSH1 0x05 | 11976: PUSH2 0x097c | 11979: JUMP    ;; CometWithExtendedAssetList.updateBasePrincipal: userBasic[account]
11980: JUMPDEST | 11981: PUSH2 0x2d3a | 11984: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
11985: JUMPDEST | 11986: SLOAD | 11987: PUSH2 0x2ede | 11990: SWAP1 | 11991: PUSH1 0xc0 | 11993: SHR | 11994: PUSH2 0x2eb5 | 11997: JUMP    ;; SLOAD ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
11998: JUMPDEST | 11999: PUSH2 0x2ec5 | 12002: JUMP    ;; CometWithExtendedAssetList.updateBasePrincipal: if (principalNew >= 0) { basic.baseTrackingIndex = trackingSupplyIndex;…
12003: JUMPDEST | 12004: PUSH2 0x2e55 | 12007: PUSH2 0x2e2e | 12010: PUSH2 0x2f1e | 12013: SWAP5 | 12014: PUSH2 0x2f19 | 12017: PUSH2 0x1fb0 | 12020: PUSH2 0x1e6b | 12023: PUSH2 0x2f13 | 12026: PUSH2 0x295b | 12029: PUSH2 0x2e7c | 12032: SWAP10 | 12033: PUSH2 0x2e19 | 12036: PUSH1 0x20 | 12038: PUSH2 0x2e11 | 12041: PUSH2 0x2025 | 12044: SWAP13 | 12045: SLOAD | 12046: PUSH1 0xc0 | 12048: SHR | 12049: SWAP1 | 12050: JUMP    ;; SLOAD ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
12051: JUMPDEST | 12052: SWAP4 | 12053: PUSH2 0x2989 | 12056: JUMP    ;; CometWithExtendedAssetList.updateBasePrincipal: -principal
12057: JUMPDEST | 12058: PUSH2 0x1e77 | 12061: JUMP    ;; CometWithExtendedAssetList.updateBasePrincipal: uint104(-principal) * indexDelta
12062: JUMPDEST | 12063: PUSH2 0x2e9b | 12066: JUMP    ;; CometWithExtendedAssetList.updateBasePrincipal: if (principal >= 0) { uint indexDelta = uint256(trackingSupplyIndex - b…
12067: JUMPDEST | 12068: SWAP4 | 12069: SWAP3 | 12070: SWAP1 | 12071: SWAP4 | 12072: PUSH1 0x01 | 12074: DUP1 | 12075: SLOAD | 12076: PUSH1 0xf8 | 12078: SHR | 12079: AND | 12080: PUSH2 0x1a47 | 12083: JUMPI    ;; SLOAD ;; CometWithExtendedAssetList.supplyInternal: function supplyInternal(address operator, address from, address dst, ad…
12084: PUSH2 0x2f40 | 12087: PUSH2 0x2f44 | 12090: SWAP2 | 12091: DUP7 | 12092: PUSH2 0x1b09 | 12095: JUMP    ;; CometWithExtendedAssetList.supplyInternal: hasPermission(from, operator)
12096: JUMPDEST | 12097: ISZERO | 12098: SWAP1 | 12099: JUMP    ;; CometWithExtendedAssetList.supplyInternal: !hasPermission(from, operator)
12100: JUMPDEST | 12101: PUSH2 0x0e62 | 12104: JUMPI    ;; CometWithExtendedAssetList.supplyInternal: if (!hasPermission(from, operator)) revert Unauthorized()
12105: PUSH1 0x01 | 12107: PUSH1 0x01 | 12109: PUSH1 0xa0 | 12111: SHL | 12112: SUB | 12113: DUP2 | 12114: DUP2 | 12115: AND | 12116: PUSH32 0x0000000000000000000000000000000000000000000000000000000000000000 | 12149: SWAP1 | 12150: SWAP2 | 12151: AND | 12152: SUB | 12153: PUSH2 0x2f9b | 12156: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
12157: POP | 12158: PUSH2 0x0c31 | 12161: SWAP3 | 12162: PUSH1 0x00 | 12164: NOT | 12165: DUP4 | 12166: SUB | 12167: PUSH2 0x3082 | 12170: JUMPI    ;; CometWithExtendedAssetList.supplyInternal: amount
12171: SWAP2 | 12172: POP | 12173: PUSH2 0x2f95 | 12176: DUP2 | 12177: PUSH2 0x47aa | 12180: JUMP    ;; CometWithExtendedAssetList.supplyInternal: borrowBalanceOf(dst)
12181: JUMPDEST | 12182: SWAP2 | 12183: PUSH2 0x3082 | 12186: JUMP    ;; CometWithExtendedAssetList.supplyInternal: amount
12187: JUMPDEST | 12188: SWAP1 | 12189: PUSH2 0x2fa9 | 12192: PUSH2 0x0c31 | 12195: SWAP5 | 12196: SWAP4 | 12197: PUSH2 0x2faf | 12200: JUMP    ;; CometWithExtendedAssetList.supplyInternal: safe128(amount)
12201: JUMPDEST | 12202: SWAP3 | 12203: PUSH2 0x35fc | 12206: JUMP    ;; CometWithExtendedAssetList.supplyInternal: safe128(amount)
12207: JUMPDEST | 12208: PUSH1 0x01 | 12210: PUSH1 0x01 | 12212: PUSH1 0x80 | 12214: SHL | 12215: SUB | 12216: SWAP1 | 12217: DUP2 | 12218: DUP2 | 12219: GT | 12220: PUSH2 0x2fc3 | 12223: JUMPI    ;; CometMath.safe128: n > type(uint128).max
12224: AND | 12225: SWAP1 | 12226: JUMP    ;; CometMath.safe128: function safe128(uint n) internal pure returns (uint128) { if (n > type…
12227: JUMPDEST | 12228: PUSH1 0x40 | 12230: MLOAD | 12231: PUSH4 0x762ea711 | 12236: PUSH1 0xe1 | 12238: SHL | 12239: DUP2 | 12240: MSTORE | 12241: PUSH1 0x04 | 12243: SWAP1 | 12244: REVERT    ;; CometMath.safe128: InvalidUInt128()
12245: JUMPDEST | 12246: PUSH1 0x00 | 12248: DUP1 | 12249: MLOAD | 12250: PUSH1 0x20 | 12252: PUSH2 0x4852 | 12255: DUP4 | 12256: CODECOPY | 12257: DUP2 | 12258: MLOAD | 12259: SWAP2 | 12260: MSTORE | 12261: PUSH1 0x01 | 12263: DUP2 | 12264: SLOAD | 12265: EQ | 12266: PUSH2 0x2ff3 | 12269: JUMPI    ;; SLOAD ;; CometWithExtendedAssetList.nonReentrantBefore: assembly ("memory-safe") { status := sload(slot) }
12270: PUSH1 0x01 | 12272: SWAP1 | 12273: SSTORE | 12274: JUMP    ;; SSTORE ;; CometWithExtendedAssetList.nonReentrantBefore: assembly ("memory-safe") { sstore(slot, REENTRANCY_GUARD_ENTERED) }
12275: JUMPDEST | 12276: PUSH1 0x40 | 12278: MLOAD | 12279: PUSH4 0x139b6435 | 12284: PUSH1 0xe2 | 12286: SHL | 12287: DUP2 | 12288: MSTORE | 12289: PUSH1 0x04 | 12291: SWAP1 | 12292: REVERT    ;; CometWithExtendedAssetList.nonReentrantBefore: ReentrantCallBlocked()
12293: JUMPDEST | 12294: PUSH1 0x01 | 12296: PUSH1 0x01 | 12298: PUSH1 0x68 | 12300: SHL | 12301: SUB | 12302: SWAP2 | 12303: DUP3 | 12304: AND | 12305: SWAP2 | 12306: SWAP1 | 12307: DUP2 | 12308: AND | 12309: SWAP1 | 12310: DUP3 | 12311: SWAP1 | 12312: SUB | 12313: DUP2 | 12314: GT | 12315: PUSH2 0x1eb3 | 12318: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
12319: ADD | 12320: SWAP1 | 12321: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
12322: JUMPDEST | 12323: DUP1 | 12324: SLOAD | 12325: PUSH1 0x01 | 12327: PUSH1 0x01 | 12329: PUSH1 0x68 | 12331: SHL | 12332: SUB | 12333: NOT | 12334: AND | 12335: PUSH1 0x01 | 12337: PUSH1 0x01 | 12339: PUSH1 0x68 | 12341: SHL | 12342: SUB | 12343: SWAP1 | 12344: SWAP3 | 12345: AND | 12346: SWAP2 | 12347: SWAP1 | 12348: SWAP2 | 12349: OR | 12350: SWAP1 | 12351: SSTORE | 12352: JUMP    ;; SLOAD,SSTORE ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
12353: JUMPDEST | 12354: PUSH1 0x01 | 12356: PUSH1 0x01 | 12358: PUSH1 0x68 | 12360: SHL | 12361: SUB | 12362: SWAP2 | 12363: DUP3 | 12364: AND | 12365: SWAP2 | 12366: AND | 12367: DUP2 | 12368: DUP2 | 12369: LT | 12370: PUSH2 0x1e5f | 12373: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
12374: SUB | 12375: SWAP1 | 12376: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
12377: JUMPDEST | 12378: DUP1 | 12379: SLOAD | 12380: PUSH1 0x01 | 12382: PUSH1 0x68 | 12384: SHL | 12385: PUSH1 0x01 | 12387: PUSH1 0xd0 | 12389: SHL | 12390: SUB | 12391: NOT | 12392: AND | 12393: PUSH1 0x68 | 12395: SWAP3 | 12396: SWAP1 | 12397: SWAP3 | 12398: SHL | 12399: PUSH1 0x01 | 12401: PUSH1 0x68 | 12403: SHL | 12404: PUSH1 0x01 | 12406: PUSH1 0xd0 | 12408: SHL | 12409: SUB | 12410: AND | 12411: SWAP2 | 12412: SWAP1 | 12413: SWAP2 | 12414: OR | 12415: SWAP1 | 12416: SSTORE | 12417: JUMP    ;; SLOAD,SSTORE ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
12418: JUMPDEST | 12419: PUSH2 0x30b1 | 12422: PUSH2 0x312f | 12425: SWAP3 | 12426: SWAP4 | 12427: DUP3 | 12428: PUSH32 0x0000000000000000000000000000000000000000000000000000000000000000 | 12461: PUSH2 0x33d8 | 12464: JUMP    ;; CometWithExtendedAssetList.supplyBase: function supplyBase(address from, address dst, uint256 amount) internal…
12465: JUMPDEST | 12466: PUSH2 0x30b9 | 12469: PUSH2 0x1ece | 12472: JUMP    ;; CometWithExtendedAssetList.supplyBase: amount = doTransferIn(baseToken, from, amount)
12473: JUMPDEST | 12474: PUSH2 0x313c | 12477: PUSH2 0x30cf | 12480: PUSH2 0x30ca | 12483: DUP7 | 12484: PUSH1 0x05 | 12486: PUSH2 0x097c | 12489: JUMP    ;; CometWithExtendedAssetList.supplyBase: userBasic[dst]
12490: JUMPDEST | 12491: PUSH2 0x1de7 | 12494: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
12495: JUMPDEST | 12496: DUP1 | 12497: MLOAD | 12498: PUSH1 0x0c | 12500: SIGNEXTEND | 12501: SWAP1 | 12502: PUSH2 0x3136 | 12505: PUSH2 0x30ff | 12508: PUSH2 0x30f8 | 12511: PUSH2 0x30f3 | 12514: PUSH2 0x30ea | 12517: DUP7 | 12518: PUSH2 0x29c0 | 12521: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
12522: JUMPDEST | 12523: PUSH2 0x2746 | 12526: DUP10 | 12527: PUSH2 0x2791 | 12530: JUMP    ;; CometWithExtendedAssetList.supplyBase: signed256(amount)
12531: JUMPDEST | 12532: PUSH2 0x31c6 | 12535: JUMP    ;; CometWithExtendedAssetList.supplyBase: principalValue(dstBalance)
12536: JUMPDEST | 12537: DUP1 | 12538: SWAP5 | 12539: PUSH2 0x335c | 12542: JUMP    ;; CometWithExtendedAssetList.supplyBase: repayAndSupplyAmount(dstPrincipal, dstPrincipalNew)
12543: JUMPDEST | 12544: SWAP8 | 12545: SWAP1 | 12546: PUSH2 0x311f | 12549: PUSH2 0x3118 | 12552: DUP11 | 12553: PUSH2 0x3113 | 12556: PUSH1 0x01 | 12558: SLOAD | 12559: PUSH2 0x1e6b | 12562: JUMP    ;; SLOAD ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
12563: JUMPDEST | 12564: PUSH2 0x3005 | 12567: JUMP    ;; CometWithExtendedAssetList.supplyBase: totalSupplyBase += supplyAmount
12568: JUMPDEST | 12569: PUSH1 0x01 | 12571: PUSH2 0x3022 | 12574: JUMP    ;; CometWithExtendedAssetList.supplyBase: totalSupplyBase += supplyAmount
12575: JUMPDEST | 12576: PUSH2 0x312a | 12579: PUSH1 0x01 | 12581: SLOAD | 12582: PUSH2 0x1ebf | 12585: JUMP    ;; SLOAD ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
12586: JUMPDEST | 12587: PUSH2 0x3041 | 12590: JUMP    ;; CometWithExtendedAssetList.supplyBase: totalBorrowBase -= repayAmount
12591: JUMPDEST | 12592: PUSH1 0x01 | 12594: PUSH2 0x3059 | 12597: JUMP    ;; CometWithExtendedAssetList.supplyBase: totalBorrowBase -= repayAmount
12598: JUMPDEST | 12599: DUP7 | 12600: PUSH2 0x2db5 | 12603: JUMP    ;; CometWithExtendedAssetList.supplyBase: dstPrincipalNew
12604: JUMPDEST | 12605: PUSH1 0x40 | 12607: MLOAD | 12608: SWAP1 | 12609: DUP2 | 12610: MSTORE | 12611: PUSH1 0x01 | 12613: PUSH1 0x01 | 12615: PUSH1 0xa0 | 12617: SHL | 12618: SUB | 12619: SWAP4 | 12620: DUP5 | 12621: AND | 12622: SWAP4 | 12623: DUP5 | 12624: SWAP3 | 12625: AND | 12626: SWAP1 | 12627: PUSH32 0xd1cf3d156d5f8f0d50f6c122ed609cec09d35c9b9fb3fff6ea0959134dae424e | 12660: SWAP1 | 12661: PUSH1 0x20 | 12663: SWAP1 | 12664: LOG3 | 12665: PUSH1 0x01 | 12667: PUSH1 0x01 | 12669: PUSH1 0x68 | 12671: SHL | 12672: SUB | 12673: DUP2 | 12674: AND | 12675: PUSH2 0x318a | 12678: JUMPI    ;; LOG3 ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
12679: POP | 12680: POP | 12681: JUMP    ;; CometWithExtendedAssetList.supplyBase: function supplyBase(address from, address dst, uint256 amount) internal…
12682: JUMPDEST | 12683: PUSH1 0x00 | 12685: DUP1 | 12686: MLOAD | 12687: PUSH1 0x20 | 12689: PUSH2 0x4832 | 12692: DUP4 | 12693: CODECOPY | 12694: DUP2 | 12695: MLOAD | 12696: SWAP2 | 12697: MSTORE | 12698: PUSH2 0x31c1 | 12701: PUSH2 0x31b1 | 12704: PUSH1 0x00 | 12706: SWAP4 | 12707: PUSH2 0x31ac | 12710: DUP6 | 12711: SLOAD | 12712: PUSH2 0x0b8f | 12715: JUMP    ;; SLOAD ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
12716: JUMPDEST | 12717: PUSH2 0x2466 | 12720: JUMP    ;; CometWithExtendedAssetList.supplyBase: presentValueSupply(baseSupplyIndex, supplyAmount)
12721: JUMPDEST | 12722: PUSH1 0x40 | 12724: MLOAD | 12725: SWAP1 | 12726: DUP2 | 12727: MSTORE | 12728: SWAP1 | 12729: DUP2 | 12730: SWAP1 | 12731: PUSH1 0x20 | 12733: DUP3 | 12734: ADD | 12735: SWAP1 | 12736: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
12737: JUMPDEST | 12738: SUB | 12739: SWAP1 | 12740: LOG3 | 12741: JUMP    ;; LOG3 ;; CometWithExtendedAssetList.supplyBase: Transfer(address(0), dst, presentValueSupply(baseSupplyIndex, supplyAmo…
12742: JUMPDEST | 12743: PUSH1 0x00 | 12745: DUP2 | 12746: SLT | 12747: PUSH2 0x31ec | 12750: JUMPI    ;; CometCore.principalValue: 0
12751: PUSH1 0x00 | 12753: SLOAD | 12754: PUSH2 0x0979 | 12757: SWAP2 | 12758: PUSH2 0x31e7 | 12761: SWAP2 | 12762: PUSH1 0x01 | 12764: PUSH1 0x01 | 12766: PUSH1 0x40 | 12768: SHL | 12769: SUB | 12770: AND | 12771: PUSH2 0x3275 | 12774: JUMP    ;; SLOAD ;; CometCore.principalValue: principalValueSupply(baseSupplyIndex, uint256(presentValue_))
12775: JUMPDEST | 12776: PUSH2 0x32eb | 12779: JUMP    ;; CometCore.principalValue: signed104(principalValueSupply(baseSupplyIndex, uint256(presentValue_)))
12780: JUMPDEST | 12781: PUSH2 0x3249 | 12784: PUSH2 0x31e7 | 12787: PUSH2 0x0979 | 12790: SWAP3 | 12791: PUSH2 0x320d | 12794: PUSH1 0x01 | 12796: DUP1 | 12797: PUSH1 0x40 | 12799: SHL | 12800: SUB | 12801: PUSH1 0x00 | 12803: SLOAD | 12804: PUSH1 0x40 | 12806: SHR | 12807: AND | 12808: SWAP2 | 12809: PUSH2 0x29af | 12812: JUMP    ;; SLOAD ;; CometCore helper: 1e15
12813: JUMPDEST | 12814: PUSH2 0x3232 | 12817: DUP3 | 12818: PUSH1 0x00 | 12820: NOT | 12821: SWAP3 | 12822: PUSH7 0x038d7ea4c68000 | 12830: SWAP1 | 12831: DUP1 | 12832: DUP6 | 12833: DIV | 12834: DUP3 | 12835: GT | 12836: DUP2 | 12837: ISZERO | 12838: ISZERO | 12839: AND | 12840: PUSH2 0x3268 | 12843: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
12844: JUMPDEST | 12845: MUL | 12846: PUSH2 0x218f | 12849: JUMP    ;; CometCore.principalValueBorrow: presentValue_ * BASE_INDEX_SCALE + baseBorrowIndex_
12850: JUMPDEST | 12851: PUSH1 0x01 | 12853: DUP2 | 12854: LT | 12855: PUSH2 0x325b | 12858: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
12859: JUMPDEST | 12860: DUP3 | 12861: ISZERO | 12862: PUSH2 0x324e | 12865: JUMPI    ;; CometCore helper: 1e18
12866: JUMPDEST | 12867: ADD | 12868: DIV | 12869: PUSH2 0x32c5 | 12872: JUMP    ;; CometCore.principalValueBorrow: safe104((presentValue_ * BASE_INDEX_SCALE + baseBorrowIndex_ - 1) / bas…
12873: JUMPDEST | 12874: PUSH2 0x2989 | 12877: JUMP    ;; CometCore.principalValue: -signed104(principalValueBorrow(baseBorrowIndex, uint256(-presentValue_…
12878: JUMPDEST | 12879: PUSH2 0x3256 | 12882: PUSH2 0x23bf | 12885: JUMP    ;; CometCore helper: 1e18
12886: JUMPDEST | 12887: PUSH2 0x3242 | 12890: JUMP    ;; CometCore helper: 1e18
12891: JUMPDEST | 12892: PUSH2 0x3263 | 12895: PUSH2 0x1e32 | 12898: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
12899: JUMPDEST | 12900: PUSH2 0x323b | 12903: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
12904: JUMPDEST | 12905: PUSH2 0x3270 | 12908: PUSH2 0x1e32 | 12911: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
12912: JUMPDEST | 12913: PUSH2 0x322c | 12916: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
12917: JUMPDEST | 12918: SWAP1 | 12919: PUSH2 0x0979 | 12922: SWAP2 | 12923: PUSH7 0x038d7ea4c68000 | 12931: SWAP1 | 12932: DUP3 | 12933: PUSH1 0x00 | 12935: NOT | 12936: DIV | 12937: DUP3 | 12938: GT | 12939: DUP4 | 12940: ISZERO | 12941: ISZERO | 12942: AND | 12943: PUSH2 0x32b8 | 12946: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
12947: JUMPDEST | 12948: PUSH1 0x01 | 12950: PUSH1 0x01 | 12952: PUSH1 0x40 | 12954: SHL | 12955: SUB | 12956: AND | 12957: SWAP2 | 12958: DUP3 | 12959: ISZERO | 12960: PUSH2 0x32ab | 12963: JUMPI    ;; CometCore helper: 1e18
12964: JUMPDEST | 12965: MUL | 12966: DIV | 12967: PUSH2 0x32c5 | 12970: JUMP    ;; CometCore.principalValueSupply: safe104((presentValue_ * BASE_INDEX_SCALE) / baseSupplyIndex_)
12971: JUMPDEST | 12972: PUSH2 0x32b3 | 12975: PUSH2 0x23bf | 12978: JUMP    ;; CometCore helper: 1e18
12979: JUMPDEST | 12980: PUSH2 0x32a4 | 12983: JUMP    ;; CometCore helper: 1e18
12984: JUMPDEST | 12985: PUSH2 0x32c0 | 12988: PUSH2 0x1e32 | 12991: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
12992: JUMPDEST | 12993: PUSH2 0x3293 | 12996: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
12997: JUMPDEST | 12998: PUSH1 0x01 | 13000: PUSH1 0x01 | 13002: PUSH1 0x68 | 13004: SHL | 13005: SUB | 13006: SWAP1 | 13007: DUP2 | 13008: DUP2 | 13009: GT | 13010: PUSH2 0x32d9 | 13013: JUMPI    ;; CometMath.safe104: n > type(uint104).max
13014: AND | 13015: SWAP1 | 13016: JUMP    ;; CometMath.safe104: function safe104(uint n) internal pure returns (uint104) { if (n > type…
13017: JUMPDEST | 13018: PUSH1 0x40 | 13020: MLOAD | 13021: PUSH4 0x0dc79255 | 13026: PUSH1 0xe1 | 13028: SHL | 13029: DUP2 | 13030: MSTORE | 13031: PUSH1 0x04 | 13033: SWAP1 | 13034: REVERT    ;; CometMath.safe104: InvalidUInt104()
13035: JUMPDEST | 13036: PUSH1 0x01 | 13038: PUSH1 0x01 | 13040: PUSH1 0x68 | 13042: SHL | 13043: SUB | 13044: AND | 13045: PUSH1 0x01 | 13047: PUSH1 0x01 | 13049: PUSH1 0x67 | 13051: SHL | 13052: SUB | 13053: DUP2 | 13054: GT | 13055: PUSH2 0x3308 | 13058: JUMPI    ;; CometMath.signed104: n > uint104(type(int104).max)
13059: PUSH1 0x0c | 13061: SIGNEXTEND | 13062: SWAP1 | 13063: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
13064: JUMPDEST | 13065: PUSH1 0x40 | 13067: MLOAD | 13068: PUSH4 0x9369ae35 | 13073: PUSH1 0xe0 | 13075: SHL | 13076: DUP2 | 13077: MSTORE | 13078: PUSH1 0x04 | 13080: SWAP1 | 13081: REVERT    ;; CometMath.signed104: InvalidInt104()
13082: JUMPDEST | 13083: PUSH1 0x0c | 13085: SWAP2 | 13086: DUP3 | 13087: SIGNEXTEND | 13088: SWAP2 | 13089: SIGNEXTEND | 13090: PUSH1 0x00 | 13092: DUP3 | 13093: SLT | 13094: DUP1 | 13095: ISZERO | 13096: PUSH1 0x01 | 13098: PUSH1 0x01 | 13100: PUSH1 0x67 | 13102: SHL | 13103: SUB | 13104: NOT | 13105: DUP5 | 13106: ADD | 13107: DUP4 | 13108: SLT | 13109: AND | 13110: PUSH2 0x334f | 13113: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
13114: JUMPDEST | 13115: PUSH1 0x01 | 13117: PUSH1 0x01 | 13119: PUSH1 0x67 | 13121: SHL | 13122: SUB | 13123: DUP4 | 13124: ADD | 13125: DUP3 | 13126: SGT | 13127: AND | 13128: PUSH2 0x1e5f | 13131: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
13132: SUB | 13133: SWAP1 | 13134: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
13135: JUMPDEST | 13136: PUSH2 0x3357 | 13139: PUSH2 0x1e32 | 13142: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
13143: JUMPDEST | 13144: PUSH2 0x333a | 13147: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
13148: JUMPDEST | 13149: SWAP2 | 13150: SWAP1 | 13151: SWAP2 | 13152: DUP1 | 13153: PUSH1 0x0c | 13155: SIGNEXTEND | 13156: DUP4 | 13157: PUSH1 0x0c | 13159: SIGNEXTEND | 13160: DUP2 | 13161: DUP2 | 13162: SLT | 13163: PUSH2 0x33cb | 13166: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
13167: PUSH1 0x00 | 13169: SLT | 13170: PUSH2 0x338f | 13173: JUMPI    ;; CometWithExtendedAssetList.repayAndSupplyAmount: 0
13174: POP | 13175: PUSH2 0x3380 | 13178: SWAP2 | 13179: SWAP3 | 13180: PUSH2 0x331a | 13183: JUMP    ;; CometWithExtendedAssetList.repayAndSupplyAmount: newPrincipal - oldPrincipal
13184: JUMPDEST | 13185: PUSH1 0x01 | 13187: PUSH1 0x01 | 13189: PUSH1 0x68 | 13191: SHL | 13192: SUB | 13193: AND | 13194: SWAP1 | 13195: PUSH1 0x00 | 13197: SWAP1 | 13198: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
13199: JUMPDEST | 13200: PUSH1 0x00 | 13202: SGT | 13203: PUSH2 0x33b2 | 13206: JUMPI    ;; CometWithExtendedAssetList.repayAndSupplyAmount: 0
13207: PUSH2 0x33a0 | 13210: SWAP2 | 13211: SWAP3 | 13212: PUSH2 0x331a | 13215: JUMP    ;; CometWithExtendedAssetList.repayAndSupplyAmount: newPrincipal - oldPrincipal
13216: JUMPDEST | 13217: PUSH1 0x00 | 13219: SWAP2 | 13220: PUSH1 0x01 | 13222: PUSH1 0x01 | 13224: PUSH1 0x68 | 13226: SHL | 13227: SUB | 13228: SWAP2 | 13229: SWAP1 | 13230: SWAP2 | 13231: AND | 13232: SWAP1 | 13233: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
13234: JUMPDEST | 13235: PUSH2 0x33bb | 13238: SWAP1 | 13239: PUSH2 0x2989 | 13242: JUMP    ;; CometWithExtendedAssetList.repayAndSupplyAmount: -oldPrincipal
13243: JUMPDEST | 13244: PUSH1 0x01 | 13246: PUSH1 0x01 | 13248: PUSH1 0x68 | 13250: SHL | 13251: SUB | 13252: SWAP1 | 13253: DUP2 | 13254: AND | 13255: SWAP3 | 13256: AND | 13257: SWAP1 | 13258: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
13259: JUMPDEST | 13260: POP | 13261: POP | 13262: POP | 13263: SWAP1 | 13264: POP | 13265: PUSH1 0x00 | 13267: SWAP1 | 13268: PUSH1 0x00 | 13270: SWAP1 | 13271: JUMP    ;; CometWithExtendedAssetList.repayAndSupplyAmount: return (0, 0)
13272: JUMPDEST | 13273: PUSH1 0x40 | 13275: MLOAD | 13276: PUSH4 0x70a08231 | 13281: PUSH1 0xe0 | 13283: SHL | 13284: DUP1 | 13285: DUP3 | 13286: MSTORE | 13287: SWAP4 | 13288: SWAP1 | 13289: SWAP3 | 13290: PUSH1 0x20 | 13292: SWAP3 | 13293: PUSH1 0x01 | 13295: PUSH1 0x01 | 13297: PUSH1 0xa0 | 13299: SHL | 13300: SUB | 13301: AND | 13302: SWAP2 | 13303: SWAP1 | 13304: DUP4 | 13305: DUP6 | 13306: DUP1 | 13307: PUSH2 0x3407 | 13310: ADDRESS | 13311: PUSH1 0x04 | 13313: DUP4 | 13314: ADD | 13315: PUSH2 0x060e | 13318: JUMP    ;; CometWithExtendedAssetList.doTransferIn: IERC20NonStandard(asset).balanceOf(address(this))
13319: JUMPDEST | 13320: SUB | 13321: DUP2 | 13322: DUP7 | 13323: GAS | 13324: STATICCALL | 13325: SWAP5 | 13326: DUP6 | 13327: ISZERO | 13328: PUSH2 0x3545 | 13331: JUMPI    ;; STATICCALL ;; CometWithExtendedAssetList.doTransferIn: IERC20NonStandard(asset).balanceOf(address(this))
13332: JUMPDEST | 13333: PUSH1 0x00 | 13335: SWAP6 | 13336: PUSH2 0x3526 | 13339: JUMPI    ;; CometWithExtendedAssetList.doTransferIn: IERC20NonStandard(asset).balanceOf(address(this))
13340: JUMPDEST | 13341: POP | 13342: DUP3 | 13343: EXTCODESIZE | 13344: ISZERO | 13345: PUSH2 0x0582 | 13348: JUMPI    ;; EXTCODESIZE ;; CometWithExtendedAssetList.doTransferIn: IERC20NonStandard(asset).transferFrom(from, address(this), amount)
13349: PUSH1 0x40 | 13351: MLOAD | 13352: PUSH4 0x23b872dd | 13357: PUSH1 0xe0 | 13359: SHL | 13360: DUP2 | 13361: MSTORE | 13362: PUSH1 0x01 | 13364: PUSH1 0x01 | 13366: PUSH1 0xa0 | 13368: SHL | 13369: SUB | 13370: SWAP2 | 13371: SWAP1 | 13372: SWAP2 | 13373: AND | 13374: PUSH1 0x04 | 13376: DUP3 | 13377: ADD | 13378: MSTORE | 13379: ADDRESS | 13380: PUSH1 0x24 | 13382: DUP3 | 13383: ADD | 13384: MSTORE | 13385: PUSH1 0x44 | 13387: DUP2 | 13388: ADD | 13389: SWAP2 | 13390: SWAP1 | 13391: SWAP2 | 13392: MSTORE | 13393: PUSH1 0x00 | 13395: DUP2 | 13396: PUSH1 0x64 | 13398: DUP2 | 13399: DUP4 | 13400: DUP7 | 13401: GAS | 13402: CALL | 13403: DUP1 | 13404: ISZERO | 13405: PUSH2 0x3519 | 13408: JUMPI    ;; CALL ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
13409: JUMPDEST | 13410: PUSH2 0x3504 | 13413: JUMPI    ;; CometWithExtendedAssetList.doTransferIn: IERC20NonStandard(asset).transferFrom(from, address(this), amount)
13414: JUMPDEST | 13415: POP | 13416: RETURNDATASIZE | 13417: DUP1 | 13418: ISZERO | 13419: PUSH2 0x34fb | 13422: JUMPI    ;; CometWithExtendedAssetList.doTransferIn: assembly ("memory-safe") { switch returndatasize() case 0 { // This is …
13423: PUSH1 0x20 | 13425: EQ | 13426: PUSH2 0x347a | 13429: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
13430: PUSH1 0x00 | 13432: DUP1 | 13433: REVERT    ;; CometWithExtendedAssetList.doTransferIn: assembly ("memory-safe") { switch returndatasize() case 0 { // This is …
13434: JUMPDEST | 13435: DUP2 | 13436: PUSH1 0x00 | 13438: DUP1 | 13439: RETURNDATACOPY | 13440: PUSH1 0x00 | 13442: MLOAD    ;; CometWithExtendedAssetList.doTransferIn: assembly ("memory-safe") { switch returndatasize() case 0 { // This is …
13443: JUMPDEST | 13444: ISZERO | 13445: PUSH2 0x34e9 | 13448: JUMPI    ;; CometWithExtendedAssetList.doTransferIn: if (!success) revert TransferInFailed()
13449: DUP2 | 13450: PUSH2 0x0979 | 13453: SWAP5 | 13454: PUSH1 0x40 | 13456: MLOAD | 13457: SWAP3 | 13458: DUP4 | 13459: SWAP2 | 13460: DUP3 | 13461: MSTORE | 13462: DUP2 | 13463: DUP1 | 13464: PUSH2 0x34a4 | 13467: ADDRESS | 13468: PUSH1 0x04 | 13470: DUP4 | 13471: ADD | 13472: PUSH2 0x060e | 13475: JUMP    ;; CometWithExtendedAssetList.doTransferIn: IERC20NonStandard(asset).balanceOf(address(this))
13476: JUMPDEST | 13477: SUB | 13478: SWAP2 | 13479: GAS | 13480: STATICCALL | 13481: SWAP2 | 13482: DUP3 | 13483: ISZERO | 13484: PUSH2 0x34dc | 13487: JUMPI    ;; STATICCALL ;; CometWithExtendedAssetList.doTransferIn: IERC20NonStandard(asset).balanceOf(address(this))
13488: JUMPDEST | 13489: PUSH1 0x00 | 13491: SWAP3 | 13492: PUSH2 0x34bf | 13495: JUMPI    ;; CometWithExtendedAssetList.doTransferIn: IERC20NonStandard(asset).balanceOf(address(this))
13496: JUMPDEST | 13497: POP | 13498: POP | 13499: PUSH2 0x219b | 13502: JUMP    ;; CometWithExtendedAssetList.doTransferIn: IERC20NonStandard(asset).balanceOf(address(this)) - preTransferBalance
13503: JUMPDEST | 13504: PUSH2 0x34d5 | 13507: SWAP3 | 13508: POP | 13509: DUP1 | 13510: RETURNDATASIZE | 13511: LT | 13512: PUSH2 0x25dd | 13515: JUMPI    ;; CometWithExtendedAssetList.doTransferIn: IERC20NonStandard(asset).balanceOf(address(this))
13516: PUSH2 0x25ce | 13519: DUP2 | 13520: DUP4 | 13521: PUSH2 0x1b46 | 13524: JUMP    ;; CometWithExtendedAssetList.doTransferIn: IERC20NonStandard(asset).balanceOf(address(this))
13525: JUMPDEST | 13526: CODESIZE | 13527: DUP1 | 13528: PUSH2 0x34b8 | 13531: JUMP    ;; CometWithExtendedAssetList.doTransferIn: IERC20NonStandard(asset).balanceOf(address(this))
13532: JUMPDEST | 13533: PUSH2 0x34e4 | 13536: PUSH2 0x1bfe | 13539: JUMP    ;; CometWithExtendedAssetList.doTransferIn: IERC20NonStandard(asset).balanceOf(address(this))
13540: JUMPDEST | 13541: PUSH2 0x34b0 | 13544: JUMP    ;; CometWithExtendedAssetList.doTransferIn: IERC20NonStandard(asset).balanceOf(address(this))
13545: JUMPDEST | 13546: PUSH1 0x40 | 13548: MLOAD | 13549: PUSH4 0x073d1efd | 13554: PUSH1 0xe5 | 13556: SHL | 13557: DUP2 | 13558: MSTORE | 13559: PUSH1 0x04 | 13561: SWAP1 | 13562: REVERT    ;; CometWithExtendedAssetList.doTransferIn: TransferInFailed()
13563: JUMPDEST | 13564: POP | 13565: PUSH1 0x00 | 13567: NOT | 13568: PUSH2 0x3483 | 13571: JUMP    ;; CometWithExtendedAssetList.doTransferIn: assembly ("memory-safe") { switch returndatasize() case 0 { // This is …
13572: JUMPDEST | 13573: DUP1 | 13574: PUSH2 0x1485 | 13577: PUSH1 0x00 | 13579: PUSH2 0x3513 | 13582: SWAP4 | 13583: PUSH2 0x1b46 | 13586: JUMP    ;; CometWithExtendedAssetList.doTransferIn: IERC20NonStandard(asset).transferFrom(from, address(this), amount)
13587: JUMPDEST | 13588: CODESIZE | 13589: PUSH2 0x3466 | 13592: JUMP    ;; CometWithExtendedAssetList.doTransferIn: IERC20NonStandard(asset).transferFrom(from, address(this), amount)
13593: JUMPDEST | 13594: PUSH2 0x3521 | 13597: PUSH2 0x1bfe | 13600: JUMP    ;; CometWithExtendedAssetList.doTransferIn: IERC20NonStandard(asset).transferFrom(from, address(this), amount)
13601: JUMPDEST | 13602: PUSH2 0x3461 | 13605: JUMP    ;; CometWithExtendedAssetList.doTransferIn: IERC20NonStandard(asset).transferFrom(from, address(this), amount)
13606: JUMPDEST | 13607: PUSH2 0x353e | 13610: SWAP2 | 13611: SWAP6 | 13612: POP | 13613: DUP5 | 13614: RETURNDATASIZE | 13615: DUP7 | 13616: GT | 13617: PUSH2 0x25dd | 13620: JUMPI    ;; CometWithExtendedAssetList.doTransferIn: IERC20NonStandard(asset).balanceOf(address(this))
13621: PUSH2 0x25ce | 13624: DUP2 | 13625: DUP4 | 13626: PUSH2 0x1b46 | 13629: JUMP    ;; CometWithExtendedAssetList.doTransferIn: IERC20NonStandard(asset).balanceOf(address(this))
13630: JUMPDEST | 13631: SWAP4 | 13632: CODESIZE | 13633: PUSH2 0x341c | 13636: JUMP    ;; CometWithExtendedAssetList.doTransferIn: IERC20NonStandard(asset).balanceOf(address(this))
13637: JUMPDEST | 13638: PUSH2 0x354d | 13641: PUSH2 0x1bfe | 13644: JUMP    ;; CometWithExtendedAssetList.doTransferIn: IERC20NonStandard(asset).balanceOf(address(this))
13645: JUMPDEST | 13646: PUSH2 0x3414 | 13649: JUMP    ;; CometWithExtendedAssetList.doTransferIn: IERC20NonStandard(asset).balanceOf(address(this))
13650: JUMPDEST | 13651: SWAP1 | 13652: PUSH1 0x40 | 13654: MLOAD | 13655: PUSH2 0x3561 | 13658: PUSH1 0x40 | 13660: DUP3 | 13661: PUSH2 0x1b46 | 13664: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
13665: JUMPDEST | 13666: SWAP2 | 13667: SLOAD | 13668: PUSH1 0x01 | 13670: PUSH1 0x01 | 13672: PUSH1 0x80 | 13674: SHL | 13675: SUB | 13676: DUP2 | 13677: AND | 13678: DUP4 | 13679: MSTORE | 13680: PUSH1 0x80 | 13682: SHR | 13683: PUSH1 0x20 | 13685: DUP4 | 13686: ADD | 13687: MSTORE | 13688: JUMP    ;; SLOAD ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
13689: JUMPDEST | 13690: PUSH1 0x01 | 13692: PUSH1 0x01 | 13694: PUSH1 0x80 | 13696: SHL | 13697: SUB | 13698: SWAP2 | 13699: DUP3 | 13700: AND | 13701: SWAP2 | 13702: SWAP1 | 13703: DUP2 | 13704: AND | 13705: SWAP1 | 13706: DUP3 | 13707: SWAP1 | 13708: SUB | 13709: DUP2 | 13710: GT | 13711: PUSH2 0x1eb3 | 13714: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
13715: ADD | 13716: SWAP1 | 13717: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
13718: JUMPDEST | 13719: DUP1 | 13720: SLOAD | 13721: PUSH1 0x01 | 13723: PUSH1 0x01 | 13725: PUSH1 0x80 | 13727: SHL | 13728: SUB | 13729: NOT | 13730: AND | 13731: PUSH1 0x01 | 13733: PUSH1 0x01 | 13735: PUSH1 0x80 | 13737: SHL | 13738: SUB | 13739: SWAP1 | 13740: SWAP3 | 13741: AND | 13742: SWAP2 | 13743: SWAP1 | 13744: SWAP2 | 13745: OR | 13746: SWAP1 | 13747: SSTORE | 13748: JUMP    ;; SLOAD,SSTORE ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
13749: JUMPDEST | 13750: SWAP1 | 13751: PUSH1 0x20 | 13753: PUSH1 0x01 | 13755: DUP1 | 13756: PUSH1 0x80 | 13758: SHL | 13759: SUB | 13760: SWAP2 | 13761: PUSH2 0x35cd | 13764: DUP4 | 13765: DUP3 | 13766: MLOAD | 13767: AND | 13768: DUP6 | 13769: PUSH2 0x3596 | 13772: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
13773: JUMPDEST | 13774: ADD | 13775: MLOAD | 13776: DUP3 | 13777: SLOAD | 13778: SWAP1 | 13779: SWAP2 | 13780: AND | 13781: PUSH1 0x80 | 13783: SWAP2 | 13784: SWAP1 | 13785: SWAP2 | 13786: SHL | 13787: PUSH1 0x01 | 13789: PUSH1 0x01 | 13791: PUSH1 0x80 | 13793: SHL | 13794: SUB | 13795: NOT | 13796: AND | 13797: OR | 13798: SWAP1 | 13799: SSTORE | 13800: JUMP    ;; SLOAD,SSTORE ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
13801: JUMPDEST | 13802: PUSH1 0x01 | 13804: PUSH1 0x01 | 13806: PUSH1 0x80 | 13808: SHL | 13809: SUB | 13810: SWAP1 | 13811: SWAP2 | 13812: AND | 13813: DUP2 | 13814: MSTORE | 13815: PUSH1 0x20 | 13817: ADD | 13818: SWAP1 | 13819: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
13820: JUMPDEST | 13821: SWAP2 | 13822: SWAP1 | 13823: SWAP3 | 13824: PUSH2 0x361b | 13827: PUSH2 0x3616 | 13830: PUSH1 0x01 | 13832: DUP1 | 13833: PUSH1 0x80 | 13835: SHL | 13836: SUB | 13837: DUP1 | 13838: SWAP4 | 13839: AND | 13840: DUP6 | 13841: DUP6 | 13842: PUSH2 0x33d8 | 13845: JUMP    ;; CometWithExtendedAssetList.supplyCollateral: doTransferIn(asset, from, amount)
13846: JUMPDEST | 13847: PUSH2 0x2faf | 13850: JUMP    ;; CometWithExtendedAssetList.supplyCollateral: safe128(doTransferIn(asset, from, amount))
13851: JUMPDEST | 13852: SWAP2 | 13853: PUSH2 0x3625 | 13856: DUP2 | 13857: PUSH2 0x1d3a | 13860: JUMP    ;; CometWithExtendedAssetList.supplyCollateral: getAssetInfoByAddress(asset)
13861: JUMPDEST | 13862: SWAP1 | 13863: PUSH2 0x3639 | 13866: PUSH2 0x3634 | 13869: DUP3 | 13870: PUSH1 0x02 | 13872: PUSH2 0x097c | 13875: JUMP    ;; CometWithExtendedAssetList.supplyCollateral: totalsCollateral[asset]
13876: JUMPDEST | 13877: PUSH2 0x3552 | 13880: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
13881: JUMPDEST | 13882: SWAP3 | 13883: PUSH2 0x365d | 13886: PUSH2 0x3650 | 13889: DUP7 | 13890: PUSH2 0x364b | 13893: DUP8 | 13894: MLOAD | 13895: PUSH2 0x0993 | 13898: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
13899: JUMPDEST | 13900: PUSH2 0x3579 | 13903: JUMP    ;; CometWithExtendedAssetList.supplyCollateral: totals.totalSupplyAsset += amount
13904: JUMPDEST | 13905: PUSH1 0x01 | 13907: PUSH1 0x01 | 13909: PUSH1 0x80 | 13911: SHL | 13912: SUB | 13913: AND | 13914: DUP6 | 13915: MSTORE | 13916: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
13917: JUMPDEST | 13918: PUSH2 0x3667 | 13921: DUP5 | 13922: MLOAD | 13923: PUSH2 0x0993 | 13926: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
13927: JUMPDEST | 13928: SWAP1 | 13929: PUSH2 0x3678 | 13932: PUSH2 0x19af | 13935: PUSH1 0xe0 | 13937: DUP7 | 13938: ADD | 13939: MLOAD | 13940: PUSH2 0x0993 | 13943: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
13944: JUMPDEST | 13945: SWAP2 | 13946: AND | 13947: GT | 13948: PUSH2 0x3722 | 13951: JUMPI    ;; CometWithExtendedAssetList.supplyCollateral: totals.totalSupplyAsset > assetInfo.supplyCap
13952: PUSH2 0x36fd | 13955: PUSH2 0x36eb | 13958: DUP6 | 13959: PUSH2 0x371d | 13962: SWAP5 | 13963: PUSH2 0x36f7 | 13966: PUSH32 0xfa56f7b24f17183d81894d3ac2ee654e3c26388d17a28dbd9549b8114304e1f4 | 13999: SWAP8 | 14000: PUSH2 0x36f2 | 14003: DUP8 | 14004: PUSH2 0x36cc | 14007: DUP15 | 14008: PUSH2 0x36d8 | 14011: PUSH2 0x36d1 | 14014: PUSH2 0x2916 | 14017: DUP6 | 14018: PUSH2 0x36cc | 14021: DUP6 | 14022: PUSH1 0x06 | 14024: PUSH2 0x097c | 14027: JUMP    ;; CometWithExtendedAssetList.supplyCollateral: userCollateral[dst]
14028: JUMPDEST | 14029: PUSH2 0x097c | 14032: JUMP    ;; CometWithExtendedAssetList.supplyCollateral: userCollateral[dst][asset]
14033: JUMPDEST | 14034: SWAP9 | 14035: DUP10 | 14036: PUSH2 0x3579 | 14039: JUMP    ;; CometWithExtendedAssetList.supplyCollateral: dstCollateral + amount
14040: JUMPDEST | 14041: SWAP9 | 14042: DUP10 | 14043: SWAP6 | 14044: PUSH2 0x36e6 | 14047: DUP6 | 14048: PUSH1 0x02 | 14050: PUSH2 0x097c | 14053: JUMP    ;; CometWithExtendedAssetList.supplyCollateral: totalsCollateral[asset]
14054: JUMPDEST | 14055: PUSH2 0x35b5 | 14058: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
14059: JUMPDEST | 14060: PUSH1 0x06 | 14062: PUSH2 0x097c | 14065: JUMP    ;; CometWithExtendedAssetList.supplyCollateral: userCollateral[dst]
14066: JUMPDEST | 14067: PUSH2 0x3596 | 14070: JUMP    ;; CometWithExtendedAssetList.supplyCollateral: userCollateral[dst][asset].balance = dstCollateralNew
14071: JUMPDEST | 14072: DUP10 | 14073: PUSH2 0x3734 | 14076: JUMP    ;; CometWithExtendedAssetList.supplyCollateral: dstCollateralNew
14077: JUMPDEST | 14078: PUSH1 0x40 | 14080: MLOAD | 14081: PUSH1 0x01 | 14083: PUSH1 0x01 | 14085: PUSH1 0xa0 | 14087: SHL | 14088: SUB | 14089: SWAP2 | 14090: DUP3 | 14091: AND | 14092: SWAP7 | 14093: DUP3 | 14094: AND | 14095: SWAP6 | 14096: SWAP1 | 14097: SWAP2 | 14098: AND | 14099: SWAP4 | 14100: SWAP1 | 14101: SWAP2 | 14102: DUP3 | 14103: SWAP2 | 14104: DUP3 | 14105: PUSH2 0x35e9 | 14108: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
14109: JUMPDEST | 14110: SUB | 14111: SWAP1 | 14112: LOG4 | 14113: JUMP    ;; LOG4 ;; CometWithExtendedAssetList.supplyCollateral: SupplyCollateral(from, dst, asset, amount)
14114: JUMPDEST | 14115: PUSH1 0x40 | 14117: MLOAD | 14118: PUSH4 0x7ac7b99d | 14123: PUSH1 0xe1 | 14125: SHL | 14126: DUP2 | 14127: MSTORE | 14128: PUSH1 0x04 | 14130: SWAP1 | 14131: REVERT    ;; CometWithExtendedAssetList.supplyCollateral: SupplyCapExceeded()
14132: JUMPDEST | 14133: SWAP1 | 14134: SWAP3 | 14135: SWAP1 | 14136: SWAP2 | 14137: PUSH1 0x01 | 14139: PUSH1 0x01 | 14141: PUSH1 0x80 | 14143: SHL | 14144: SUB | 14145: SWAP1 | 14146: DUP2 | 14147: AND | 14148: ISZERO | 14149: DUP1 | 14150: DUP1 | 14151: PUSH2 0x3895 | 14154: JUMPI    ;; CometWithExtendedAssetList.updateAssetsIn: function updateAssetsIn( address account, AssetInfo memory assetInfo, u…
14155: JUMPDEST | 14156: ISZERO | 14157: PUSH2 0x37f1 | 14160: JUMPI    ;; CometWithExtendedAssetList.updateAssetsIn: if (initialUserBalance == 0 && finalUserBalance != 0) { // set bit for …
14161: POP | 14162: POP | 14163: POP | 14164: PUSH2 0x375e | 14167: DUP3 | 14168: MLOAD | 14169: PUSH1 0xff | 14171: AND | 14172: SWAP1 | 14173: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
14174: JUMPDEST | 14175: PUSH1 0xff | 14177: DUP2 | 14178: AND | 14179: PUSH1 0x10 | 14181: DUP2 | 14182: LT | 14183: ISZERO | 14184: PUSH2 0x37b0 | 14187: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
14188: POP | 14189: POP | 14190: PUSH2 0x3798 | 14193: PUSH2 0x3790 | 14196: PUSH2 0x3781 | 14199: PUSH2 0x0c31 | 14202: SWAP5 | 14203: MLOAD | 14204: PUSH1 0xff | 14206: AND | 14207: SWAP1 | 14208: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
14209: JUMPDEST | 14210: PUSH1 0x01 | 14212: PUSH1 0xff | 14214: SWAP1 | 14215: SWAP2 | 14216: AND | 14217: SHL | 14218: PUSH2 0xffff | 14221: AND | 14222: SWAP1 | 14223: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
14224: JUMPDEST | 14225: SWAP2 | 14226: PUSH1 0x05 | 14228: PUSH2 0x097c | 14231: JUMP    ;; CometWithExtendedAssetList.updateAssetsIn: userBasic[account]
14232: JUMPDEST | 14233: SWAP1 | 14234: PUSH2 0x37a9 | 14237: DUP3 | 14238: SLOAD | 14239: PUSH2 0xffff | 14242: SWAP1 | 14243: PUSH1 0xe8 | 14245: SHR | 14246: AND | 14247: SWAP1 | 14248: JUMP    ;; SLOAD ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
14249: JUMPDEST | 14250: OR | 14251: SWAP1 | 14252: PUSH2 0x2d1b | 14255: JUMP    ;; CometWithExtendedAssetList.updateAssetsIn: userBasic[account].assetsIn |= (uint16(1) << assetInfo.offset)
14256: JUMPDEST | 14257: PUSH1 0x18 | 14259: SWAP2 | 14260: SWAP4 | 14261: POP | 14262: LT | 14263: PUSH2 0x37be | 14266: JUMPI    ;; CometWithExtendedAssetList.updateAssetsIn: assetInfo.offset < 24
14267: POP | 14268: POP | 14269: JUMP    ;; CometWithExtendedAssetList.updateAssetsIn: if (assetInfo.offset < 16) { // set bit in assetsIn for bits 0-15 userB…
14270: JUMPDEST | 14271: PUSH2 0x37de | 14274: PUSH2 0x3790 | 14277: PUSH2 0x37d2 | 14280: PUSH1 0x10 | 14282: PUSH2 0x0c31 | 14285: SWAP6 | 14286: PUSH2 0x2cae | 14289: JUMP    ;; CometWithExtendedAssetList.updateAssetsIn: assetInfo.offset - 16
14290: JUMPDEST | 14291: PUSH1 0x01 | 14293: PUSH1 0xff | 14295: SWAP2 | 14296: DUP3 | 14297: AND | 14298: SHL | 14299: AND | 14300: SWAP1 | 14301: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
14302: JUMPDEST | 14303: SWAP1 | 14304: PUSH2 0x37ea | 14307: DUP3 | 14308: SLOAD | 14309: PUSH1 0xf8 | 14311: SHR | 14312: SWAP1 | 14313: JUMP    ;; SLOAD ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
14314: JUMPDEST | 14315: OR | 14316: SWAP1 | 14317: PUSH2 0x2b4b | 14320: JUMP    ;; CometWithExtendedAssetList.updateAssetsIn: userBasic[account]._reserved |= (uint8(1) << (assetInfo.offset - 16))
14321: JUMPDEST | 14322: ISZERO | 14323: SWAP2 | 14324: DUP3 | 14325: PUSH2 0x388a | 14328: JUMPI    ;; CometWithExtendedAssetList.updateAssetsIn: initialUserBalance != 0 && finalUserBalance == 0
14329: JUMPDEST | 14330: POP | 14331: POP | 14332: PUSH2 0x3803 | 14335: JUMPI    ;; CometWithExtendedAssetList.updateAssetsIn: if (initialUserBalance != 0 && finalUserBalance == 0) { // clear bit fo…
14336: POP | 14337: POP | 14338: JUMP    ;; CometWithExtendedAssetList.updateAssetsIn: if (initialUserBalance == 0 && finalUserBalance != 0) { // set bit for …
14339: JUMPDEST | 14340: DUP2 | 14341: MLOAD | 14342: PUSH1 0xff | 14344: AND | 14345: DUP1 | 14346: PUSH1 0x10 | 14348: DUP2 | 14349: LT | 14350: ISZERO | 14351: PUSH2 0x384b | 14354: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
14355: POP | 14356: POP | 14357: PUSH2 0x3833 | 14360: PUSH2 0x3790 | 14363: PUSH2 0x382b | 14366: PUSH2 0x3781 | 14369: PUSH2 0x0c31 | 14372: SWAP6 | 14373: MLOAD | 14374: PUSH1 0xff | 14376: AND | 14377: SWAP1 | 14378: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
14379: JUMPDEST | 14380: NOT | 14381: PUSH2 0xffff | 14384: AND | 14385: SWAP1 | 14386: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
14387: JUMPDEST | 14388: SWAP1 | 14389: PUSH2 0x3844 | 14392: DUP3 | 14393: SLOAD | 14394: PUSH2 0xffff | 14397: SWAP1 | 14398: PUSH1 0xe8 | 14400: SHR | 14401: AND | 14402: SWAP1 | 14403: JUMP    ;; SLOAD ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
14404: JUMPDEST | 14405: AND | 14406: SWAP1 | 14407: PUSH2 0x2d1b | 14410: JUMP    ;; CometWithExtendedAssetList.updateAssetsIn: userBasic[account].assetsIn &= ~(uint16(1) << assetInfo.offset)
14411: JUMPDEST | 14412: PUSH1 0x18 | 14414: SWAP2 | 14415: SWAP4 | 14416: POP | 14417: LT | 14418: PUSH2 0x3859 | 14421: JUMPI    ;; CometWithExtendedAssetList.updateAssetsIn: assetInfo.offset < 24
14422: POP | 14423: POP | 14424: JUMP    ;; CometWithExtendedAssetList.updateAssetsIn: if (assetInfo.offset < 16) { // clear bit in assetsIn for bits 0-15 use…
14425: JUMPDEST | 14426: PUSH2 0x3877 | 14429: PUSH2 0x3790 | 14432: PUSH2 0x3870 | 14435: PUSH2 0x37d2 | 14438: PUSH1 0x10 | 14440: PUSH2 0x0c31 | 14443: SWAP7 | 14444: PUSH2 0x2cae | 14447: JUMP    ;; CometWithExtendedAssetList.updateAssetsIn: assetInfo.offset - 16
14448: JUMPDEST | 14449: NOT | 14450: PUSH1 0xff | 14452: AND | 14453: SWAP1 | 14454: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
14455: JUMPDEST | 14456: SWAP1 | 14457: PUSH2 0x3883 | 14460: DUP3 | 14461: SLOAD | 14462: PUSH1 0xf8 | 14464: SHR | 14465: SWAP1 | 14466: JUMP    ;; SLOAD ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
14467: JUMPDEST | 14468: AND | 14469: SWAP1 | 14470: PUSH2 0x2b4b | 14473: JUMP    ;; CometWithExtendedAssetList.updateAssetsIn: userBasic[account]._reserved &= ~(uint8(1) << (assetInfo.offset - 16))
14474: JUMPDEST | 14475: AND | 14476: ISZERO | 14477: SWAP1 | 14478: POP | 14479: CODESIZE | 14480: DUP1 | 14481: PUSH2 0x37f9 | 14484: JUMP    ;; CometWithExtendedAssetList.updateAssetsIn: initialUserBalance != 0 && finalUserBalance == 0
14485: JUMPDEST | 14486: POP | 14487: DUP2 | 14488: DUP4 | 14489: AND | 14490: ISZERO | 14491: ISZERO | 14492: PUSH2 0x374b | 14495: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
14496: JUMPDEST | 14497: SWAP4 | 14498: SWAP3 | 14499: SWAP1 | 14500: SWAP4 | 14501: PUSH1 0x02 | 14503: PUSH1 0x01 | 14505: SLOAD | 14506: PUSH1 0xf8 | 14508: SHR | 14509: AND | 14510: PUSH2 0x1a47 | 14513: JUMPI    ;; SLOAD ;; CometWithExtendedAssetList.transferInternal: function transferInternal(address operator, address src, address dst, a…
14514: PUSH2 0x2f40 | 14517: PUSH2 0x38be | 14520: SWAP2 | 14521: DUP7 | 14522: PUSH2 0x1b09 | 14525: JUMP    ;; CometWithExtendedAssetList.transferInternal: hasPermission(src, operator)
14526: JUMPDEST | 14527: PUSH2 0x0e62 | 14530: JUMPI    ;; CometWithExtendedAssetList.transferInternal: if (!hasPermission(src, operator)) revert Unauthorized()
14531: PUSH1 0x01 | 14533: PUSH1 0x01 | 14535: PUSH1 0xa0 | 14537: SHL | 14538: SUB | 14539: DUP5 | 14540: DUP2 | 14541: AND | 14542: DUP4 | 14543: DUP3 | 14544: AND | 14545: EQ | 14546: PUSH2 0x3936 | 14549: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
14550: DUP1 | 14551: PUSH32 0x0000000000000000000000000000000000000000000000000000000000000000 | 14584: AND | 14585: SWAP1 | 14586: DUP3 | 14587: AND | 14588: EQ | 14589: PUSH1 0x00 | 14591: EQ | 14592: PUSH2 0x3922 | 14595: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
14596: POP | 14597: PUSH2 0x0c31 | 14600: SWAP3 | 14601: PUSH1 0x00 | 14603: NOT | 14604: DUP4 | 14605: SUB | 14606: PUSH2 0x3948 | 14609: JUMPI    ;; CometWithExtendedAssetList.transferInternal: amount
14610: SWAP2 | 14611: POP | 14612: PUSH2 0x391c | 14615: DUP3 | 14616: PUSH2 0x474c | 14619: JUMP    ;; CometWithExtendedAssetList.transferInternal: balanceOf(src)
14620: JUMPDEST | 14621: SWAP2 | 14622: PUSH2 0x3948 | 14625: JUMP    ;; CometWithExtendedAssetList.transferInternal: amount
14626: JUMPDEST | 14627: SWAP1 | 14628: PUSH2 0x3930 | 14631: PUSH2 0x0c31 | 14634: SWAP5 | 14635: SWAP4 | 14636: PUSH2 0x2faf | 14639: JUMP    ;; CometWithExtendedAssetList.transferInternal: safe128(amount)
14640: JUMPDEST | 14641: SWAP3 | 14642: PUSH2 0x3be1 | 14645: JUMP    ;; CometWithExtendedAssetList.transferInternal: safe128(amount)
14646: JUMPDEST | 14647: PUSH1 0x40 | 14649: MLOAD | 14650: PUSH4 0xe397a99b | 14655: PUSH1 0xe0 | 14657: SHL | 14658: DUP2 | 14659: MSTORE | 14660: PUSH1 0x04 | 14662: SWAP1 | 14663: REVERT    ;; CometWithExtendedAssetList.transferInternal: NoSelfTransfer()
14664: JUMPDEST | 14665: SWAP2 | 14666: SWAP1 | 14667: SWAP2 | 14668: PUSH2 0x3953 | 14671: PUSH2 0x1ece | 14674: JUMP    ;; CometWithExtendedAssetList.transferBase: function transferBase(address src, address dst, uint256 amount) interna…
14675: JUMPDEST | 14676: PUSH2 0x395e | 14679: DUP2 | 14680: PUSH1 0x05 | 14682: PUSH2 0x097c | 14685: JUMP    ;; CometWithExtendedAssetList.transferBase: userBasic[src]
14686: JUMPDEST | 14687: PUSH2 0x3967 | 14690: SWAP1 | 14691: PUSH2 0x1de7 | 14694: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
14695: JUMPDEST | 14696: PUSH2 0x3972 | 14699: DUP5 | 14700: PUSH1 0x05 | 14702: PUSH2 0x097c | 14705: JUMP    ;; CometWithExtendedAssetList.transferBase: userBasic[dst]
14706: JUMPDEST | 14707: PUSH2 0x397b | 14710: SWAP1 | 14711: PUSH2 0x1de7 | 14714: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
14715: JUMPDEST | 14716: SWAP3 | 14717: DUP2 | 14718: MLOAD | 14719: PUSH2 0x3988 | 14722: SWAP1 | 14723: PUSH1 0x0c | 14725: SIGNEXTEND | 14726: SWAP1 | 14727: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
14728: JUMPDEST | 14729: SWAP4 | 14730: DUP1 | 14731: MLOAD | 14732: PUSH2 0x3995 | 14735: SWAP1 | 14736: PUSH1 0x0c | 14738: SIGNEXTEND | 14739: SWAP1 | 14740: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
14741: JUMPDEST | 14742: SWAP3 | 14743: PUSH2 0x399f | 14746: DUP7 | 14747: PUSH2 0x29c0 | 14750: JUMP    ;; CometWithExtendedAssetList.transferBase: presentValue(srcPrincipal)
14751: JUMPDEST | 14752: PUSH2 0x39a8 | 14755: DUP5 | 14756: PUSH2 0x2791 | 14759: JUMP    ;; CometWithExtendedAssetList.transferBase: signed256(amount)
14760: JUMPDEST | 14761: PUSH2 0x39b1 | 14764: SWAP2 | 14765: PUSH2 0x25f1 | 14768: JUMP    ;; CometWithExtendedAssetList.transferBase: presentValue(srcPrincipal) - signed256(amount)
14769: JUMPDEST | 14770: SWAP3 | 14771: PUSH2 0x39bb | 14774: DUP6 | 14775: PUSH2 0x29c0 | 14778: JUMP    ;; CometWithExtendedAssetList.transferBase: presentValue(dstPrincipal)
14779: JUMPDEST | 14780: SWAP1 | 14781: PUSH2 0x39c5 | 14784: SWAP1 | 14785: PUSH2 0x2791 | 14788: JUMP    ;; CometWithExtendedAssetList.transferBase: signed256(amount)
14789: JUMPDEST | 14790: PUSH2 0x39ce | 14793: SWAP2 | 14794: PUSH2 0x2628 | 14797: JUMP    ;; CometWithExtendedAssetList.transferBase: presentValue(dstPrincipal) + signed256(amount)
14798: JUMPDEST | 14799: SWAP1 | 14800: PUSH2 0x39d8 | 14803: DUP5 | 14804: PUSH2 0x31c6 | 14807: JUMP    ;; CometWithExtendedAssetList.transferBase: principalValue(srcBalance)
14808: JUMPDEST | 14809: PUSH2 0x39e2 | 14812: DUP2 | 14813: SWAP4 | 14814: PUSH2 0x31c6 | 14817: JUMP    ;; CometWithExtendedAssetList.transferBase: principalValue(dstBalance)
14818: JUMPDEST | 14819: SWAP8 | 14820: DUP9 | 14821: SWAP4 | 14822: PUSH2 0x39ee | 14825: SWAP2 | 14826: PUSH2 0x3b7c | 14829: JUMP    ;; CometWithExtendedAssetList.transferBase: withdrawAndBorrowAmount(srcPrincipal, srcPrincipalNew)
14830: JUMPDEST | 14831: SWAP9 | 14832: PUSH2 0x39f9 | 14835: SWAP2 | 14836: SWAP8 | 14837: PUSH2 0x335c | 14840: JUMP    ;; CometWithExtendedAssetList.transferBase: repayAndSupplyAmount(dstPrincipal, dstPrincipalNew)
14841: JUMPDEST | 14842: SWAP9 | 14843: DUP8 | 14844: DUP11 | 14845: PUSH1 0x01 | 14847: SLOAD | 14848: PUSH2 0x3a08 | 14851: SWAP1 | 14852: PUSH2 0x1e6b | 14855: JUMP    ;; SLOAD ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
14856: JUMPDEST | 14857: SWAP1 | 14858: PUSH2 0x3a12 | 14861: SWAP2 | 14862: PUSH2 0x3005 | 14865: JUMP    ;; CometWithExtendedAssetList.transferBase: totalSupplyBase + supplyAmount
14866: JUMPDEST | 14867: SWAP1 | 14868: PUSH2 0x3a1c | 14871: SWAP2 | 14872: PUSH2 0x3041 | 14875: JUMP    ;; CometWithExtendedAssetList.transferBase: totalSupplyBase + supplyAmount - withdrawAmount
14876: JUMPDEST | 14877: PUSH2 0x3a27 | 14880: SWAP1 | 14881: PUSH1 0x01 | 14883: PUSH2 0x3022 | 14886: JUMP    ;; CometWithExtendedAssetList.transferBase: totalSupplyBase = totalSupplyBase + supplyAmount - withdrawAmount
14887: JUMPDEST | 14888: PUSH1 0x01 | 14890: SLOAD | 14891: PUSH2 0x3a33 | 14894: SWAP1 | 14895: PUSH2 0x1ebf | 14898: JUMP    ;; SLOAD ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
14899: JUMPDEST | 14900: SWAP1 | 14901: PUSH2 0x3a3d | 14904: SWAP2 | 14905: PUSH2 0x3005 | 14908: JUMP    ;; CometWithExtendedAssetList.transferBase: totalBorrowBase + borrowAmount
14909: JUMPDEST | 14910: SWAP1 | 14911: PUSH2 0x3a47 | 14914: SWAP2 | 14915: PUSH2 0x3041 | 14918: JUMP    ;; CometWithExtendedAssetList.transferBase: totalBorrowBase + borrowAmount - repayAmount
14919: JUMPDEST | 14920: PUSH2 0x3a52 | 14923: SWAP1 | 14924: PUSH1 0x01 | 14926: PUSH2 0x3059 | 14929: JUMP    ;; CometWithExtendedAssetList.transferBase: totalBorrowBase = totalBorrowBase + borrowAmount - repayAmount
14930: JUMPDEST | 14931: PUSH2 0x3a5c | 14934: SWAP2 | 14935: DUP8 | 14936: PUSH2 0x2db5 | 14939: JUMP    ;; CometWithExtendedAssetList.transferBase: srcPrincipalNew
14940: JUMPDEST | 14941: PUSH2 0x3a66 | 14944: SWAP2 | 14945: DUP8 | 14946: PUSH2 0x2db5 | 14949: JUMP    ;; CometWithExtendedAssetList.transferBase: dstPrincipalNew
14950: JUMPDEST | 14951: PUSH1 0x00 | 14953: DUP2 | 14954: SLT | 14955: PUSH2 0x3b13 | 14958: JUMPI    ;; CometWithExtendedAssetList.transferBase: srcBalance < 0
14959: JUMPDEST | 14960: POP | 14961: PUSH1 0x01 | 14963: PUSH1 0x01 | 14965: PUSH1 0x68 | 14967: SHL | 14968: SUB | 14969: SWAP2 | 14970: DUP2 | 14971: DUP4 | 14972: AND | 14973: PUSH2 0x3acb | 14976: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
14977: JUMPDEST | 14978: POP | 14979: POP | 14980: DUP2 | 14981: AND | 14982: PUSH2 0x3a8d | 14985: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
14986: POP | 14987: POP | 14988: JUMP    ;; CometWithExtendedAssetList.transferBase: function transferBase(address src, address dst, uint256 amount) interna…
14989: JUMPDEST | 14990: PUSH1 0x00 | 14992: DUP1 | 14993: MLOAD | 14994: PUSH1 0x20 | 14996: PUSH2 0x4832 | 14999: DUP4 | 15000: CODECOPY | 15001: DUP2 | 15002: MLOAD | 15003: SWAP2 | 15004: MSTORE | 15005: PUSH2 0x31c1 | 15008: PUSH2 0x3aaf | 15011: PUSH1 0x00 | 15013: SWAP4 | 15014: PUSH2 0x31ac | 15017: DUP6 | 15018: SLOAD | 15019: PUSH2 0x0b8f | 15022: JUMP    ;; SLOAD ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
15023: JUMPDEST | 15024: PUSH1 0x40 | 15026: MLOAD | 15027: SWAP1 | 15028: DUP2 | 15029: MSTORE | 15030: PUSH1 0x01 | 15032: PUSH1 0x01 | 15034: PUSH1 0xa0 | 15036: SHL | 15037: SUB | 15038: SWAP1 | 15039: SWAP5 | 15040: AND | 15041: SWAP4 | 15042: SWAP1 | 15043: DUP2 | 15044: SWAP1 | 15045: PUSH1 0x20 | 15047: DUP3 | 15048: ADD | 15049: SWAP1 | 15050: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
15051: JUMPDEST | 15052: PUSH1 0x00 | 15054: DUP1 | 15055: MLOAD | 15056: PUSH1 0x20 | 15058: PUSH2 0x4832 | 15061: DUP4 | 15062: CODECOPY | 15063: DUP2 | 15064: MLOAD | 15065: SWAP2 | 15066: MSTORE | 15067: PUSH2 0x3b09 | 15070: PUSH2 0x3aed | 15073: PUSH1 0x00 | 15075: SWAP5 | 15076: PUSH2 0x31ac | 15079: DUP7 | 15080: SLOAD | 15081: PUSH2 0x0b8f | 15084: JUMP    ;; SLOAD ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
15085: JUMPDEST | 15086: PUSH1 0x40 | 15088: MLOAD | 15089: SWAP1 | 15090: DUP2 | 15091: MSTORE | 15092: PUSH1 0x01 | 15094: PUSH1 0x01 | 15096: PUSH1 0xa0 | 15098: SHL | 15099: SUB | 15100: SWAP1 | 15101: SWAP4 | 15102: AND | 15103: SWAP3 | 15104: SWAP1 | 15105: DUP2 | 15106: SWAP1 | 15107: PUSH1 0x20 | 15109: DUP3 | 15110: ADD | 15111: SWAP1 | 15112: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
15113: JUMPDEST | 15114: SUB | 15115: SWAP1 | 15116: LOG3 | 15117: CODESIZE | 15118: DUP1 | 15119: PUSH2 0x3a81 | 15122: JUMP    ;; LOG3 ;; CometWithExtendedAssetList.transferBase: Transfer(src, address(0), presentValueSupply(baseSupplyIndex, withdrawA…
15123: JUMPDEST | 15124: PUSH2 0x3b1c | 15127: SWAP1 | 15128: PUSH2 0x29af | 15131: JUMP    ;; CometWithExtendedAssetList.transferBase: -srcBalance
15132: JUMPDEST | 15133: PUSH32 0x0000000000000000000000000000000000000000000000000000000000000000 | 15166: GT | 15167: PUSH2 0x3b6a | 15170: JUMPI    ;; CometWithExtendedAssetList.transferBase: if (uint256(-srcBalance) < baseBorrowMin) revert BorrowTooSmall()
15171: PUSH2 0x3b4e | 15174: PUSH2 0x2f40 | 15177: DUP4 | 15178: PUSH2 0x27b4 | 15181: JUMP    ;; CometWithExtendedAssetList.transferBase: isBorrowCollateralized(src)
15182: JUMPDEST | 15183: PUSH2 0x3b58 | 15186: JUMPI    ;; CometWithExtendedAssetList.transferBase: if (!isBorrowCollateralized(src)) revert NotCollateralized()
15187: CODESIZE | 15188: PUSH2 0x3a6f | 15191: JUMP    ;; CometWithExtendedAssetList.transferBase: if (srcBalance < 0) { if (uint256(-srcBalance) < baseBorrowMin) revert …
15192: JUMPDEST | 15193: PUSH1 0x40 | 15195: MLOAD | 15196: PUSH4 0x0a62fbdb | 15201: PUSH1 0xe1 | 15203: SHL | 15204: DUP2 | 15205: MSTORE | 15206: PUSH1 0x04 | 15208: SWAP1 | 15209: REVERT    ;; CometWithExtendedAssetList.transferBase: NotCollateralized()
15210: JUMPDEST | 15211: PUSH1 0x40 | 15213: MLOAD | 15214: PUSH4 0x7139da23 | 15219: PUSH1 0xe1 | 15221: SHL | 15222: DUP2 | 15223: MSTORE | 15224: PUSH1 0x04 | 15226: SWAP1 | 15227: REVERT    ;; CometWithExtendedAssetList.transferBase: BorrowTooSmall()
15228: JUMPDEST | 15229: SWAP2 | 15230: SWAP1 | 15231: DUP3 | 15232: PUSH1 0x0c | 15234: SIGNEXTEND | 15235: DUP2 | 15236: PUSH1 0x0c | 15238: SIGNEXTEND | 15239: DUP2 | 15240: DUP2 | 15241: SGT | 15242: PUSH2 0x33cb | 15245: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
15246: PUSH1 0x00 | 15248: SGT | 15249: PUSH2 0x3b9f | 15252: JUMPI    ;; CometWithExtendedAssetList.withdrawAndBorrowAmount: 0
15253: POP | 15254: PUSH2 0x3380 | 15257: SWAP2 | 15258: SWAP3 | 15259: PUSH2 0x331a | 15262: JUMP    ;; CometWithExtendedAssetList.withdrawAndBorrowAmount: oldPrincipal - newPrincipal
15263: JUMPDEST | 15264: PUSH1 0x00 | 15266: SLT | 15267: PUSH2 0x3bb0 | 15270: JUMPI    ;; CometWithExtendedAssetList.withdrawAndBorrowAmount: 0
15271: PUSH2 0x33a0 | 15274: SWAP2 | 15275: SWAP3 | 15276: PUSH2 0x331a | 15279: JUMP    ;; CometWithExtendedAssetList.withdrawAndBorrowAmount: oldPrincipal - newPrincipal
15280: JUMPDEST | 15281: PUSH2 0x3bb9 | 15284: SWAP1 | 15285: PUSH2 0x2989 | 15288: JUMP    ;; CometWithExtendedAssetList.withdrawAndBorrowAmount: -newPrincipal
15289: JUMPDEST | 15290: PUSH1 0x01 | 15292: PUSH1 0x01 | 15294: PUSH1 0x68 | 15296: SHL | 15297: SUB | 15298: SWAP3 | 15299: DUP4 | 15300: AND | 15301: SWAP3 | 15302: AND | 15303: SWAP1 | 15304: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
15305: JUMPDEST | 15306: PUSH1 0x01 | 15308: PUSH1 0x01 | 15310: PUSH1 0x80 | 15312: SHL | 15313: SUB | 15314: SWAP2 | 15315: DUP3 | 15316: AND | 15317: SWAP2 | 15318: AND | 15319: DUP2 | 15320: DUP2 | 15321: LT | 15322: PUSH2 0x1e5f | 15325: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
15326: SUB | 15327: SWAP1 | 15328: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
15329: JUMPDEST | 15330: PUSH1 0x01 | 15332: PUSH1 0x01 | 15334: PUSH1 0xa0 | 15336: SHL | 15337: SUB | 15338: DUP1 | 15339: DUP3 | 15340: AND | 15341: PUSH1 0x00 | 15343: DUP2 | 15344: DUP2 | 15345: MSTORE | 15346: PUSH1 0x06 | 15348: PUSH1 0x20 | 15350: MSTORE | 15351: PUSH1 0x40 | 15353: SWAP1 | 15354: KECCAK256 | 15355: PUSH1 0x01 | 15357: PUSH1 0x01 | 15359: PUSH1 0x80 | 15361: SHL | 15362: SUB | 15363: SWAP6 | 15364: SWAP2 | 15365: SWAP5 | 15366: SWAP2 | 15367: SWAP4 | 15368: SWAP2 | 15369: SWAP1 | 15370: DUP7 | 15371: SWAP1 | 15372: PUSH2 0x3c16 | 15375: SWAP1 | 15376: DUP7 | 15377: SWAP1 | 15378: PUSH2 0x097c | 15381: JUMP    ;; KECCAK256 ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
15382: JUMPDEST | 15383: SLOAD | 15384: AND | 15385: DUP4 | 15386: DUP3 | 15387: AND | 15388: SWAP7 | 15389: DUP8 | 15390: PUSH1 0x00 | 15392: MSTORE | 15393: PUSH1 0x06 | 15395: PUSH1 0x20 | 15397: MSTORE | 15398: DUP6 | 15399: PUSH1 0x40 | 15401: PUSH1 0x00 | 15403: KECCAK256 | 15404: SWAP1 | 15405: PUSH2 0x3c35 | 15408: SWAP2 | 15409: PUSH2 0x097c | 15412: JUMP    ;; SLOAD,KECCAK256 ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
15413: JUMPDEST | 15414: SLOAD | 15415: AND | 15416: PUSH2 0x3c41 | 15419: DUP10 | 15420: DUP4 | 15421: PUSH2 0x3bc9 | 15424: JUMP    ;; SLOAD ;; CometWithExtendedAssetList.transferCollateral: srcCollateral - amount
15425: JUMPDEST | 15426: PUSH2 0x3c4b | 15429: DUP11 | 15430: DUP4 | 15431: PUSH2 0x3579 | 15434: JUMP    ;; CometWithExtendedAssetList.transferCollateral: dstCollateral + amount
15435: JUMPDEST | 15436: SWAP3 | 15437: DUP2 | 15438: DUP9 | 15439: PUSH2 0x3c59 | 15442: DUP9 | 15443: PUSH1 0x06 | 15445: PUSH2 0x097c | 15448: JUMP    ;; CometWithExtendedAssetList.transferCollateral: userCollateral[src]
15449: JUMPDEST | 15450: SWAP1 | 15451: PUSH2 0x3c63 | 15454: SWAP2 | 15455: PUSH2 0x097c | 15458: JUMP    ;; CometWithExtendedAssetList.transferCollateral: userCollateral[src][asset]
15459: JUMPDEST | 15460: SWAP1 | 15461: PUSH2 0x3c6d | 15464: SWAP2 | 15465: PUSH2 0x3596 | 15468: JUMP    ;; CometWithExtendedAssetList.transferCollateral: userCollateral[src][asset].balance = srcCollateralNew
15469: JUMPDEST | 15470: DUP4 | 15471: DUP9 | 15472: PUSH2 0x3c7a | 15475: DUP8 | 15476: PUSH1 0x06 | 15478: PUSH2 0x097c | 15481: JUMP    ;; CometWithExtendedAssetList.transferCollateral: userCollateral[dst]
15482: JUMPDEST | 15483: SWAP1 | 15484: PUSH2 0x3c84 | 15487: SWAP2 | 15488: PUSH2 0x097c | 15491: JUMP    ;; CometWithExtendedAssetList.transferCollateral: userCollateral[dst][asset]
15492: JUMPDEST | 15493: SWAP1 | 15494: PUSH2 0x3c8e | 15497: SWAP2 | 15498: PUSH2 0x3596 | 15501: JUMP    ;; CometWithExtendedAssetList.transferCollateral: userCollateral[dst][asset].balance = dstCollateralNew
15502: JUMPDEST | 15503: PUSH2 0x3c97 | 15506: DUP9 | 15507: PUSH2 0x1d3a | 15510: JUMP    ;; CometWithExtendedAssetList.transferCollateral: getAssetInfoByAddress(asset)
15511: JUMPDEST | 15512: SWAP2 | 15513: PUSH2 0x3ca3 | 15516: SWAP2 | 15517: DUP4 | 15518: DUP9 | 15519: PUSH2 0x3734 | 15522: JUMP    ;; CometWithExtendedAssetList.transferCollateral: srcCollateralNew
15523: JUMPDEST | 15524: PUSH2 0x3cac | 15527: SWAP4 | 15528: PUSH2 0x3734 | 15531: JUMP    ;; CometWithExtendedAssetList.transferCollateral: dstCollateralNew
15532: JUMPDEST | 15533: PUSH2 0x3cb5 | 15536: SWAP1 | 15537: PUSH2 0x27b4 | 15540: JUMP    ;; CometWithExtendedAssetList.transferCollateral: isBorrowCollateralized(src)
15541: JUMPDEST | 15542: ISZERO | 15543: PUSH2 0x3b58 | 15546: JUMPI    ;; CometWithExtendedAssetList.transferCollateral: if (!isBorrowCollateralized(src)) revert NotCollateralized()
15547: PUSH32 0x29db89d45e1a802b4d55e202984fce9faf1d30aedf86503ff1ea0ed9ebb64201 | 15580: SWAP2 | 15581: PUSH2 0x371d | 15584: PUSH1 0x40 | 15586: MLOAD | 15587: SWAP3 | 15588: DUP4 | 15589: SWAP3 | 15590: AND | 15591: SWAP7 | 15592: DUP3 | 15593: PUSH2 0x35e9 | 15596: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
15597: JUMPDEST | 15598: SWAP4 | 15599: SWAP3 | 15600: SWAP1 | 15601: SWAP4 | 15602: PUSH1 0x04 | 15604: PUSH1 0x01 | 15606: SLOAD | 15607: PUSH1 0xf8 | 15609: SHR | 15610: AND | 15611: PUSH2 0x1a47 | 15614: JUMPI    ;; SLOAD ;; CometWithExtendedAssetList.withdrawInternal: function withdrawInternal(address operator, address src, address to, ad…
15615: PUSH2 0x2f40 | 15618: PUSH2 0x3d0b | 15621: SWAP2 | 15622: DUP7 | 15623: PUSH2 0x1b09 | 15626: JUMP    ;; CometWithExtendedAssetList.withdrawInternal: hasPermission(src, operator)
15627: JUMPDEST | 15628: PUSH2 0x0e62 | 15631: JUMPI    ;; CometWithExtendedAssetList.withdrawInternal: if (!hasPermission(src, operator)) revert Unauthorized()
15632: PUSH1 0x01 | 15634: PUSH1 0x01 | 15636: PUSH1 0xa0 | 15638: SHL | 15639: SUB | 15640: DUP2 | 15641: DUP2 | 15642: AND | 15643: PUSH32 0x0000000000000000000000000000000000000000000000000000000000000000 | 15676: SWAP1 | 15677: SWAP2 | 15678: AND | 15679: SUB | 15680: PUSH2 0x3d62 | 15683: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
15684: POP | 15685: PUSH2 0x0c31 | 15688: SWAP3 | 15689: PUSH1 0x00 | 15691: NOT | 15692: DUP4 | 15693: SUB | 15694: PUSH2 0x3d76 | 15697: JUMPI    ;; CometWithExtendedAssetList.withdrawInternal: amount
15698: SWAP2 | 15699: POP | 15700: PUSH2 0x3d5c | 15703: DUP3 | 15704: PUSH2 0x474c | 15707: JUMP    ;; CometWithExtendedAssetList.withdrawInternal: balanceOf(src)
15708: JUMPDEST | 15709: SWAP2 | 15710: PUSH2 0x3d76 | 15713: JUMP    ;; CometWithExtendedAssetList.withdrawInternal: amount
15714: JUMPDEST | 15715: SWAP1 | 15716: PUSH2 0x3d70 | 15719: PUSH2 0x0c31 | 15722: SWAP5 | 15723: SWAP4 | 15724: PUSH2 0x2faf | 15727: JUMP    ;; CometWithExtendedAssetList.withdrawInternal: safe128(amount)
15728: JUMPDEST | 15729: SWAP3 | 15730: PUSH2 0x3f99 | 15733: JUMP    ;; CometWithExtendedAssetList.withdrawInternal: safe128(amount)
15734: JUMPDEST | 15735: SWAP1 | 15736: SWAP2 | 15737: PUSH2 0x312f | 15740: SWAP3 | 15741: PUSH2 0x3d84 | 15744: PUSH2 0x1ece | 15747: JUMP    ;; CometWithExtendedAssetList.withdrawBase: function withdrawBase(address src, address to, uint256 amount) internal…
15748: JUMPDEST | 15749: PUSH2 0x3d92 | 15752: PUSH2 0x30ca | 15755: DUP5 | 15756: PUSH1 0x05 | 15758: PUSH2 0x097c | 15761: JUMP    ;; CometWithExtendedAssetList.withdrawBase: userBasic[src]
15762: JUMPDEST | 15763: PUSH2 0x3dec | 15766: PUSH2 0x3da0 | 15769: DUP3 | 15770: MLOAD | 15771: PUSH1 0x0c | 15773: SIGNEXTEND | 15774: SWAP1 | 15775: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
15776: JUMPDEST | 15777: PUSH2 0x3db5 | 15780: PUSH2 0x3dac | 15783: DUP3 | 15784: PUSH2 0x29c0 | 15787: JUMP    ;; CometWithExtendedAssetList.withdrawBase: presentValue(srcPrincipal)
15788: JUMPDEST | 15789: PUSH2 0x2740 | 15792: DUP8 | 15793: PUSH2 0x2791 | 15796: JUMP    ;; CometWithExtendedAssetList.withdrawBase: signed256(amount)
15797: JUMPDEST | 15798: SWAP3 | 15799: PUSH2 0x3136 | 15802: PUSH2 0x3dcc | 15805: PUSH2 0x3dc5 | 15808: DUP7 | 15809: PUSH2 0x31c6 | 15812: JUMP    ;; CometWithExtendedAssetList.withdrawBase: principalValue(srcBalance)
15813: JUMPDEST | 15814: DUP1 | 15815: SWAP5 | 15816: PUSH2 0x3b7c | 15819: JUMP    ;; CometWithExtendedAssetList.withdrawBase: withdrawAndBorrowAmount(srcPrincipal, srcPrincipalNew)
15820: JUMPDEST | 15821: PUSH2 0x3de1 | 15824: PUSH2 0x3118 | 15827: DUP4 | 15828: PUSH2 0x312a | 15831: PUSH1 0x01 | 15833: SWAP15 | 15834: SWAP6 | 15835: SWAP15 | 15836: SLOAD | 15837: PUSH2 0x1e6b | 15840: JUMP    ;; SLOAD ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
15841: JUMPDEST | 15842: PUSH2 0x3113 | 15845: PUSH1 0x01 | 15847: SLOAD | 15848: PUSH2 0x1ebf | 15851: JUMP    ;; SLOAD ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
15852: JUMPDEST | 15853: PUSH1 0x00 | 15855: DUP2 | 15856: SLT | 15857: PUSH2 0x3e91 | 15860: JUMPI    ;; CometWithExtendedAssetList.withdrawBase: srcBalance < 0
15861: JUMPDEST | 15862: POP | 15863: PUSH2 0x3e21 | 15866: DUP3 | 15867: DUP3 | 15868: PUSH32 0x0000000000000000000000000000000000000000000000000000000000000000 | 15901: PUSH2 0x3ef1 | 15904: JUMP    ;; CometWithExtendedAssetList.withdrawBase: baseToken
15905: JUMPDEST | 15906: PUSH1 0x40 | 15908: MLOAD | 15909: SWAP2 | 15910: DUP3 | 15911: MSTORE | 15912: PUSH1 0x01 | 15914: PUSH1 0x01 | 15916: PUSH1 0xa0 | 15918: SHL | 15919: SUB | 15920: SWAP3 | 15921: DUP4 | 15922: AND | 15923: SWAP3 | 15924: AND | 15925: SWAP1 | 15926: DUP3 | 15927: SWAP1 | 15928: PUSH32 0x9b1bfa7fa9ee420a16e124f794c35ac9f90472acc99140eb2f6447c714cad8eb | 15961: SWAP1 | 15962: PUSH1 0x20 | 15964: SWAP1 | 15965: LOG3 | 15966: PUSH1 0x01 | 15968: PUSH1 0x01 | 15970: PUSH1 0x68 | 15972: SHL | 15973: SUB | 15974: DUP3 | 15975: AND | 15976: PUSH2 0x3e6f | 15979: JUMPI    ;; LOG3 ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
15980: POP | 15981: POP | 15982: JUMP    ;; CometWithExtendedAssetList.withdrawBase: function withdrawBase(address src, address to, uint256 amount) internal…
15983: JUMPDEST | 15984: PUSH1 0x00 | 15986: DUP1 | 15987: MLOAD | 15988: PUSH1 0x20 | 15990: PUSH2 0x4832 | 15993: DUP4 | 15994: CODECOPY | 15995: DUP2 | 15996: MLOAD | 15997: SWAP2 | 15998: MSTORE | 15999: PUSH2 0x31c1 | 16002: PUSH2 0x31b1 | 16005: PUSH1 0x00 | 16007: SWAP5 | 16008: PUSH2 0x31ac | 16011: DUP7 | 16012: SLOAD | 16013: PUSH2 0x0b8f | 16016: JUMP    ;; SLOAD ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
16017: JUMPDEST | 16018: PUSH2 0x3e9a | 16021: SWAP1 | 16022: PUSH2 0x29af | 16025: JUMP    ;; CometWithExtendedAssetList.withdrawBase: -srcBalance
16026: JUMPDEST | 16027: PUSH32 0x0000000000000000000000000000000000000000000000000000000000000000 | 16060: GT | 16061: PUSH2 0x3b6a | 16064: JUMPI    ;; CometWithExtendedAssetList.withdrawBase: if (uint256(-srcBalance) < baseBorrowMin) revert BorrowTooSmall()
16065: PUSH2 0x3ecc | 16068: PUSH2 0x2f40 | 16071: DUP5 | 16072: PUSH2 0x27b4 | 16075: JUMP    ;; CometWithExtendedAssetList.withdrawBase: isBorrowCollateralized(src)
16076: JUMPDEST | 16077: PUSH2 0x3b58 | 16080: JUMPI    ;; CometWithExtendedAssetList.withdrawBase: if (!isBorrowCollateralized(src)) revert NotCollateralized()
16081: CODESIZE | 16082: PUSH2 0x3df5 | 16085: JUMP    ;; CometWithExtendedAssetList.withdrawBase: if (srcBalance < 0) { if (uint256(-srcBalance) < baseBorrowMin) revert …
16086: JUMPDEST | 16087: PUSH1 0x01 | 16089: PUSH1 0x01 | 16091: PUSH1 0xa0 | 16093: SHL | 16094: SUB | 16095: SWAP1 | 16096: SWAP2 | 16097: AND | 16098: DUP2 | 16099: MSTORE | 16100: PUSH1 0x20 | 16102: DUP2 | 16103: ADD | 16104: SWAP2 | 16105: SWAP1 | 16106: SWAP2 | 16107: MSTORE | 16108: PUSH1 0x40 | 16110: ADD | 16111: SWAP1 | 16112: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
16113: JUMPDEST | 16114: PUSH1 0x01 | 16116: PUSH1 0x01 | 16118: PUSH1 0xa0 | 16120: SHL | 16121: SUB | 16122: AND | 16123: SWAP3 | 16124: SWAP2 | 16125: DUP4 | 16126: EXTCODESIZE | 16127: ISZERO | 16128: PUSH2 0x0582 | 16131: JUMPI    ;; EXTCODESIZE ;; CometWithExtendedAssetList.doTransferOut: IERC20NonStandard(asset).transfer(to, amount)
16132: PUSH2 0x3f2b | 16135: SWAP1 | 16136: PUSH1 0x40 | 16138: MLOAD | 16139: DUP1 | 16140: SWAP6 | 16141: DUP2 | 16142: DUP1 | 16143: SWAP6 | 16144: PUSH4 0xa9059cbb | 16149: PUSH1 0xe0 | 16151: SHL | 16152: DUP3 | 16153: MSTORE | 16154: PUSH1 0x00 | 16156: SWAP9 | 16157: DUP10 | 16158: SWAP7 | 16159: DUP8 | 16160: SWAP7 | 16161: DUP8 | 16162: SWAP4 | 16163: PUSH1 0x04 | 16165: DUP5 | 16166: ADD | 16167: PUSH2 0x3ed6 | 16170: JUMP    ;; CometWithExtendedAssetList.doTransferOut: IERC20NonStandard(asset).transfer(to, amount)
16171: JUMPDEST | 16172: SUB | 16173: SWAP3 | 16174: GAS | 16175: CALL | 16176: DUP1 | 16177: ISZERO | 16178: PUSH2 0x3f8c | 16181: JUMPI    ;; CALL ;; CometWithExtendedAssetList.doTransferOut: IERC20NonStandard(asset).transfer(to, amount)
16182: JUMPDEST | 16183: PUSH2 0x3f7c | 16186: JUMPI    ;; CometWithExtendedAssetList.doTransferOut: IERC20NonStandard(asset).transfer(to, amount)
16187: JUMPDEST | 16188: POP | 16189: RETURNDATASIZE | 16190: SWAP1 | 16191: POP | 16192: DUP1 | 16193: ISZERO | 16194: PUSH2 0x3f71 | 16197: JUMPI    ;; CometWithExtendedAssetList.doTransferOut: assembly ("memory-safe") { switch returndatasize() case 0 { // This is …
16198: PUSH1 0x20 | 16200: EQ | 16201: PUSH2 0x3f50 | 16204: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
16205: POP | 16206: DUP1 | 16207: REVERT    ;; CometWithExtendedAssetList.doTransferOut: assembly ("memory-safe") { switch returndatasize() case 0 { // This is …
16208: JUMPDEST | 16209: SWAP1 | 16210: PUSH1 0x20 | 16212: DUP2 | 16213: DUP1 | 16214: RETURNDATACOPY | 16215: MLOAD    ;; CometWithExtendedAssetList.doTransferOut: assembly ("memory-safe") { switch returndatasize() case 0 { // This is …
16216: JUMPDEST | 16217: ISZERO | 16218: PUSH2 0x3f5f | 16221: JUMPI    ;; CometWithExtendedAssetList.doTransferOut: if (!success) revert TransferOutFailed()
16222: JUMP    ;; CometWithExtendedAssetList.doTransferOut: function doTransferOut(address asset, address to, uint amount) internal…
16223: JUMPDEST | 16224: PUSH1 0x40 | 16226: MLOAD | 16227: PUSH4 0xcefaffeb | 16232: PUSH1 0xe0 | 16234: SHL | 16235: DUP2 | 16236: MSTORE | 16237: PUSH1 0x04 | 16239: SWAP1 | 16240: REVERT    ;; CometWithExtendedAssetList.doTransferOut: TransferOutFailed()
16241: JUMPDEST | 16242: POP | 16243: SWAP1 | 16244: POP | 16245: PUSH1 0x00 | 16247: NOT | 16248: PUSH2 0x3f58 | 16251: JUMP    ;; CometWithExtendedAssetList.doTransferOut: assembly ("memory-safe") { switch returndatasize() case 0 { // This is …
16252: JUMPDEST | 16253: PUSH2 0x3f85 | 16256: SWAP2 | 16257: PUSH2 0x1b46 | 16260: JUMP    ;; CometWithExtendedAssetList.doTransferOut: IERC20NonStandard(asset).transfer(to, amount)
16261: JUMPDEST | 16262: CODESIZE | 16263: DUP3 | 16264: PUSH2 0x3f3b | 16267: JUMP    ;; CometWithExtendedAssetList.doTransferOut: IERC20NonStandard(asset).transfer(to, amount)
16268: JUMPDEST | 16269: PUSH2 0x3f94 | 16272: PUSH2 0x1bfe | 16275: JUMP    ;; CometWithExtendedAssetList.doTransferOut: IERC20NonStandard(asset).transfer(to, amount)
16276: JUMPDEST | 16277: PUSH2 0x3f36 | 16280: JUMP    ;; CometWithExtendedAssetList.doTransferOut: IERC20NonStandard(asset).transfer(to, amount)
16281: JUMPDEST | 16282: PUSH1 0x01 | 16284: PUSH1 0x01 | 16286: PUSH1 0xa0 | 16288: SHL | 16289: SUB | 16290: DUP1 | 16291: DUP3 | 16292: AND | 16293: PUSH1 0x00 | 16295: DUP2 | 16296: DUP2 | 16297: MSTORE | 16298: PUSH1 0x06 | 16300: PUSH1 0x20 | 16302: MSTORE | 16303: PUSH1 0x40 | 16305: DUP2 | 16306: KECCAK256 | 16307: SWAP1 | 16308: SWAP7 | 16309: SWAP6 | 16310: SWAP2 | 16311: SWAP5 | 16312: SWAP2 | 16313: SWAP4 | 16314: PUSH1 0x01 | 16316: PUSH1 0x01 | 16318: PUSH1 0x80 | 16320: SHL | 16321: SUB | 16322: SWAP2 | 16323: DUP3 | 16324: SWAP1 | 16325: PUSH2 0x3fcf | 16328: SWAP1 | 16329: DUP8 | 16330: SWAP1 | 16331: PUSH2 0x097c | 16334: JUMP    ;; KECCAK256 ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
16335: JUMPDEST | 16336: SLOAD | 16337: AND | 16338: PUSH2 0x3fdb | 16341: DUP9 | 16342: DUP3 | 16343: PUSH2 0x3bc9 | 16346: JUMP    ;; SLOAD ;; CometWithExtendedAssetList.withdrawCollateral: srcCollateral - amount
16347: JUMPDEST | 16348: DUP1 | 16349: DUP8 | 16350: DUP8 | 16351: DUP2 | 16352: AND | 16353: SWAP12 | 16354: DUP13 | 16355: DUP2 | 16356: MSTORE | 16357: PUSH1 0x02 | 16359: PUSH1 0x20 | 16361: MSTORE | 16362: PUSH1 0x40 | 16364: DUP2 | 16365: KECCAK256 | 16366: DUP13 | 16367: DUP9 | 16368: DUP3 | 16369: SLOAD | 16370: AND | 16371: SWAP1 | 16372: PUSH2 0x3ffc | 16375: SWAP2 | 16376: PUSH2 0x3bc9 | 16379: JUMP    ;; KECCAK256,SLOAD ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
16380: JUMPDEST | 16381: PUSH2 0x4005 | 16384: SWAP2 | 16385: PUSH2 0x3596 | 16388: JUMP    ;; CometWithExtendedAssetList.withdrawCollateral: totalsCollateral[asset].totalSupplyAsset -= amount
16389: JUMPDEST | 16390: DUP11 | 16391: DUP2 | 16392: MSTORE | 16393: PUSH1 0x06 | 16395: PUSH1 0x20 | 16397: MSTORE | 16398: PUSH1 0x40 | 16400: SWAP1 | 16401: KECCAK256 | 16402: SWAP1 | 16403: PUSH2 0x401b | 16406: SWAP2 | 16407: PUSH2 0x097c | 16410: JUMP    ;; KECCAK256 ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
16411: JUMPDEST | 16412: SWAP1 | 16413: PUSH2 0x4025 | 16416: SWAP2 | 16417: PUSH2 0x3596 | 16420: JUMP    ;; CometWithExtendedAssetList.withdrawCollateral: userCollateral[src][asset].balance = srcCollateralNew
16421: JUMPDEST | 16422: PUSH2 0x402e | 16425: DUP8 | 16426: PUSH2 0x1d3a | 16429: JUMP    ;; CometWithExtendedAssetList.withdrawCollateral: getAssetInfoByAddress(asset)
16430: JUMPDEST | 16431: SWAP2 | 16432: PUSH2 0x4039 | 16435: SWAP3 | 16436: DUP5 | 16437: PUSH2 0x3734 | 16440: JUMP    ;; CometWithExtendedAssetList.withdrawCollateral: srcCollateralNew
16441: JUMPDEST | 16442: PUSH2 0x4042 | 16445: SWAP1 | 16446: PUSH2 0x27b4 | 16449: JUMP    ;; CometWithExtendedAssetList.withdrawCollateral: isBorrowCollateralized(src)
16450: JUMPDEST | 16451: ISZERO | 16452: PUSH2 0x3b58 | 16455: JUMPI    ;; CometWithExtendedAssetList.withdrawCollateral: if (!isBorrowCollateralized(src)) revert NotCollateralized()
16456: PUSH32 0xd6d480d5b3068db003533b170d67561494d72e3bf9fa40a266471351ebba9e16 | 16489: SWAP4 | 16490: DUP3 | 16491: PUSH2 0x4076 | 16494: SWAP3 | 16495: DUP9 | 16496: AND | 16497: SWAP2 | 16498: PUSH2 0x3ef1 | 16501: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
16502: JUMPDEST | 16503: PUSH2 0x371d | 16506: PUSH1 0x40 | 16508: MLOAD | 16509: SWAP3 | 16510: DUP4 | 16511: SWAP3 | 16512: AND | 16513: SWAP6 | 16514: DUP3 | 16515: PUSH2 0x35e9 | 16518: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
16519: JUMPDEST | 16520: SWAP2 | 16521: SWAP1 | 16522: DUP2 | 16523: LT | 16524: ISZERO | 16525: PUSH2 0x4097 | 16528: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
16529: PUSH1 0x05 | 16531: SHL | 16532: ADD | 16533: SWAP1 | 16534: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
16535: JUMPDEST | 16536: PUSH4 0x4e487b71 | 16541: PUSH1 0xe0 | 16543: SHL | 16544: PUSH1 0x00 | 16546: MSTORE | 16547: PUSH1 0x32 | 16549: PUSH1 0x04 | 16551: MSTORE | 16552: PUSH1 0x24 | 16554: PUSH1 0x00 | 16556: REVERT    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
16557: JUMPDEST | 16558: CALLDATALOAD | 16559: PUSH2 0x0979 | 16562: DUP2 | 16563: PUSH2 0x0571 | 16566: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
16567: JUMPDEST | 16568: SWAP1 | 16569: PUSH1 0x40 | 16571: MLOAD | 16572: PUSH2 0x40c6 | 16575: PUSH1 0x80 | 16577: DUP3 | 16578: PUSH2 0x1b46 | 16581: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
16582: JUMPDEST | 16583: SWAP2 | 16584: SLOAD | 16585: PUSH4 0xffffffff | 16590: DUP2 | 16591: AND | 16592: DUP4 | 16593: MSTORE | 16594: PUSH1 0x20 | 16596: DUP2 | 16597: DUP2 | 16598: SHR | 16599: PUSH1 0x01 | 16601: PUSH1 0x01 | 16603: PUSH1 0x40 | 16605: SHL | 16606: SUB | 16607: AND | 16608: SWAP1 | 16609: DUP5 | 16610: ADD | 16611: MSTORE | 16612: PUSH1 0x60 | 16614: DUP2 | 16615: DUP2 | 16616: SHR | 16617: PUSH1 0x01 | 16619: PUSH1 0x01 | 16621: PUSH1 0x80 | 16623: SHL | 16624: SUB | 16625: AND | 16626: PUSH1 0x40 | 16628: DUP6 | 16629: ADD | 16630: MSTORE | 16631: PUSH1 0xe0 | 16633: SWAP2 | 16634: SWAP1 | 16635: SWAP2 | 16636: SHR | 16637: SWAP1 | 16638: DUP4 | 16639: ADD | 16640: MSTORE | 16641: JUMP    ;; SLOAD ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
16642: JUMPDEST | 16643: PUSH1 0x01 | 16645: SWAP1 | 16646: PUSH4 0xffffffff | 16651: DUP1 | 16652: SWAP2 | 16653: AND | 16654: SWAP1 | 16655: DUP2 | 16656: EQ | 16657: PUSH2 0x1eb3 | 16660: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
16661: ADD | 16662: SWAP1 | 16663: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
16664: JUMPDEST | 16665: SWAP3 | 16666: SWAP2 | 16667: SWAP1 | 16668: SWAP3 | 16669: PUSH1 0x01 | 16671: PUSH1 0x08 | 16673: DUP2 | 16674: SLOAD | 16675: PUSH1 0xf8 | 16677: SHR | 16678: AND | 16679: PUSH2 0x1a47 | 16682: JUMPI    ;; SLOAD ;; CometWithExtendedAssetList.absorb: function absorb(address absorber, address[] calldata accounts) override…
16683: GAS | 16684: SWAP5 | 16685: PUSH2 0x4134 | 16688: PUSH2 0x1ece | 16691: JUMP    ;; CometWithExtendedAssetList.absorb: uint startGas = gasleft()
16692: JUMPDEST | 16693: PUSH1 0x00    ;; CometWithExtendedAssetList.absorb: uint startGas = gasleft()
16695: JUMPDEST | 16696: DUP5 | 16697: DUP2 | 16698: LT | 16699: PUSH2 0x422e | 16702: JUMPI    ;; CometWithExtendedAssetList.absorb: i < accounts.length
16703: POP | 16704: POP | 16705: POP | 16706: PUSH2 0x41d9 | 16709: SWAP1 | 16710: PUSH2 0x41d2 | 16713: PUSH2 0x41b3 | 16716: PUSH2 0x3616 | 16719: PUSH2 0x415d | 16722: PUSH2 0x0c31 | 16725: SWAP8 | 16726: SWAP9 | 16727: GAS | 16728: SWAP1 | 16729: PUSH2 0x219b | 16732: JUMP    ;; CometWithExtendedAssetList.absorb: gasleft()
16733: JUMPDEST | 16734: PUSH2 0x41ac | 16737: PUSH2 0x419a | 16740: PUSH2 0x4176 | 16743: PUSH2 0x4171 | 16746: DUP9 | 16747: PUSH1 0x07 | 16749: PUSH2 0x097c | 16752: JUMP    ;; CometWithExtendedAssetList.absorb: liquidatorPoints[absorber]
16753: JUMPDEST | 16754: PUSH2 0x40b7 | 16757: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
16758: JUMPDEST | 16759: SWAP9 | 16760: PUSH2 0x2025 | 16763: PUSH2 0x4190 | 16766: PUSH2 0x418b | 16769: DUP13 | 16770: MLOAD | 16771: PUSH4 0xffffffff | 16776: AND | 16777: SWAP1 | 16778: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
16779: JUMPDEST | 16780: PUSH2 0x4102 | 16783: JUMP    ;; CometWithExtendedAssetList.absorb: points.numAbsorbs++
16784: JUMPDEST | 16785: PUSH4 0xffffffff | 16790: AND | 16791: DUP12 | 16792: MSTORE | 16793: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
16794: JUMPDEST | 16795: PUSH2 0x2e8e | 16798: PUSH1 0x20 | 16800: DUP11 | 16801: ADD | 16802: SWAP2 | 16803: PUSH2 0x2034 | 16806: DUP4 | 16807: MLOAD | 16808: PUSH2 0x0b8f | 16811: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
16812: JUMPDEST | 16813: BASEFEE | 16814: SWAP1 | 16815: PUSH2 0x1e77 | 16818: JUMP    ;; CometWithExtendedAssetList.absorb: gasUsed * block.basefee
16819: JUMPDEST | 16820: PUSH2 0x41c5 | 16823: PUSH1 0x40 | 16825: DUP7 | 16826: ADD | 16827: SWAP2 | 16828: PUSH2 0x364b | 16831: DUP4 | 16832: MLOAD | 16833: PUSH2 0x0993 | 16836: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
16837: JUMPDEST | 16838: PUSH1 0x01 | 16840: PUSH1 0x01 | 16842: PUSH1 0x80 | 16844: SHL | 16845: SUB | 16846: AND | 16847: SWAP1 | 16848: MSTORE | 16849: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
16850: JUMPDEST | 16851: PUSH1 0x07 | 16853: PUSH2 0x097c | 16856: JUMP    ;; CometWithExtendedAssetList.absorb: liquidatorPoints[absorber]
16857: JUMPDEST | 16858: DUP2 | 16859: MLOAD | 16860: PUSH1 0x20 | 16862: DUP1 | 16863: DUP5 | 16864: ADD | 16865: MLOAD | 16866: PUSH1 0x40 | 16868: DUP6 | 16869: ADD | 16870: MLOAD | 16871: PUSH1 0x60 | 16873: SWAP6 | 16874: DUP7 | 16875: ADD | 16876: MLOAD | 16877: PUSH1 0x01 | 16879: PUSH1 0x01 | 16881: PUSH1 0xe0 | 16883: SHL | 16884: SUB | 16885: NOT | 16886: PUSH1 0xe0 | 16888: SWAP2 | 16889: SWAP1 | 16890: SWAP2 | 16891: SHL | 16892: AND | 16893: PUSH1 0x01 | 16895: PUSH1 0x60 | 16897: SHL | 16898: PUSH1 0x01 | 16900: PUSH1 0xe0 | 16902: SHL | 16903: SUB | 16904: SWAP2 | 16905: SWAP1 | 16906: SWAP7 | 16907: SHL | 16908: AND | 16909: PUSH4 0xffffffff | 16914: SWAP1 | 16915: SWAP4 | 16916: AND | 16917: PUSH1 0x01 | 16919: PUSH1 0x20 | 16921: SHL | 16922: PUSH1 0x01 | 16924: PUSH1 0x60 | 16926: SHL | 16927: SUB | 16928: SWAP2 | 16929: SWAP1 | 16930: SWAP3 | 16931: SHL | 16932: AND | 16933: OR | 16934: OR | 16935: SWAP2 | 16936: SWAP1 | 16937: SWAP2 | 16938: OR | 16939: SWAP1 | 16940: SSTORE | 16941: JUMP    ;; SSTORE ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
16942: JUMPDEST | 16943: DUP1 | 16944: PUSH2 0x424c | 16947: PUSH2 0x4246 | 16950: PUSH2 0x4241 | 16953: DUP7 | 16954: SWAP5 | 16955: DUP10 | 16956: DUP8 | 16957: PUSH2 0x4087 | 16960: JUMP    ;; CometWithExtendedAssetList.absorb: accounts[i]
16961: JUMPDEST | 16962: PUSH2 0x40ad | 16965: JUMP    ;; CometWithExtendedAssetList.absorb: accounts[i]
16966: JUMPDEST | 16967: DUP7 | 16968: PUSH2 0x4252 | 16971: JUMP    ;; CometWithExtendedAssetList.absorb: accounts[i]
16972: JUMPDEST | 16973: ADD | 16974: PUSH2 0x4137 | 16977: JUMP    ;; CometWithExtendedAssetList.absorb: uint i = 0
16978: JUMPDEST | 16979: SWAP1 | 16980: PUSH2 0x425f | 16983: PUSH2 0x2f40 | 16986: DUP3 | 16987: PUSH2 0x2a35 | 16990: JUMP    ;; CometWithExtendedAssetList.absorbInternal: isLiquidatable(account)
16991: JUMPDEST | 16992: PUSH2 0x45e7 | 16995: JUMPI    ;; CometWithExtendedAssetList.absorbInternal: if (!isLiquidatable(account)) revert NotLiquidatable()
16996: PUSH2 0x4271 | 16999: PUSH2 0x30ca | 17002: DUP3 | 17003: PUSH1 0x05 | 17005: PUSH2 0x097c | 17008: JUMP    ;; CometWithExtendedAssetList.absorbInternal: userBasic[account]
17009: JUMPDEST | 17010: SWAP1 | 17011: PUSH2 0x427d | 17014: DUP3 | 17015: MLOAD | 17016: PUSH1 0x0c | 17018: SIGNEXTEND | 17019: SWAP1 | 17020: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
17021: JUMPDEST | 17022: SWAP1 | 17023: PUSH2 0x4287 | 17026: DUP3 | 17027: PUSH2 0x29c0 | 17030: JUMP    ;; CometWithExtendedAssetList.absorbInternal: presentValue(oldPrincipal)
17031: JUMPDEST | 17032: SWAP2 | 17033: PUSH2 0x4297 | 17036: PUSH1 0x60 | 17038: DUP6 | 17039: ADD | 17040: MLOAD | 17041: PUSH2 0xffff | 17044: AND | 17045: SWAP1 | 17046: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
17047: JUMPDEST | 17048: SWAP1 | 17049: PUSH2 0x42a6 | 17052: PUSH1 0x80 | 17054: DUP7 | 17055: ADD | 17056: MLOAD | 17057: PUSH1 0xff | 17059: AND | 17060: SWAP1 | 17061: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
17062: JUMPDEST | 17063: SWAP4 | 17064: PUSH2 0x42d0 | 17067: PUSH32 0x0000000000000000000000000000000000000000000000000000000000000000 | 17100: PUSH2 0x249f | 17103: JUMP    ;; CometWithExtendedAssetList.absorbInternal: getPrice(baseTokenPriceFeed)
17104: JUMPDEST | 17105: SWAP3 | 17106: PUSH1 0x00 | 17108: SWAP6 | 17109: DUP7    ;; CometWithExtendedAssetList.absorbInternal: uint8 i = 0
17110: JUMPDEST | 17111: PUSH1 0xff | 17113: PUSH32 0x0000000000000000000000000000000000000000000000000000000000000000 | 17146: AND | 17147: PUSH1 0xff | 17149: DUP3 | 17150: AND | 17151: LT | 17152: PUSH2 0x448f | 17155: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
17156: POP | 17157: POP | 17158: POP | 17159: PUSH2 0x434e | 17162: PUSH2 0x4348 | 17165: PUSH2 0x2966 | 17168: DUP6 | 17169: PUSH2 0x4343 | 17172: PUSH1 0x01 | 17174: DUP1 | 17175: PUSH1 0x40 | 17177: SHL | 17178: SUB | 17179: PUSH32 0x0000000000000000000000000000000000000000000000000000000000000000 | 17212: AND | 17213: DUP1 | 17214: SWAP11 | 17215: PUSH2 0x1e77 | 17218: JUMP    ;; CometCore helper: 1e15
17219: JUMPDEST | 17220: PUSH2 0x23d6 | 17223: JUMP    ;; CometWithExtendedAssetList.divPrice: n * toScale / price
17224: JUMPDEST | 17225: DUP3 | 17226: PUSH2 0x2628 | 17229: JUMP    ;; CometWithExtendedAssetList.absorbInternal: oldBalance + signed256(deltaBalance)
17230: JUMPDEST | 17231: SWAP2 | 17232: PUSH1 0x00 | 17234: DUP4 | 17235: SLT | 17236: PUSH2 0x4486 | 17239: JUMPI    ;; CometWithExtendedAssetList.absorbInternal: newBalance < 0
17240: JUMPDEST | 17241: PUSH2 0x4361 | 17244: DUP4 | 17245: PUSH2 0x31c6 | 17248: JUMP    ;; CometWithExtendedAssetList.absorbInternal: principalValue(newBalance)
17249: JUMPDEST | 17250: SWAP7 | 17251: DUP8 | 17252: PUSH2 0x436d | 17255: SWAP2 | 17256: DUP8 | 17257: PUSH2 0x2db5 | 17260: JUMP    ;; CometWithExtendedAssetList.absorbInternal: newPrincipal
17261: JUMPDEST | 17262: PUSH2 0x4378 | 17265: DUP6 | 17266: PUSH1 0x05 | 17268: PUSH2 0x097c | 17271: JUMP    ;; CometWithExtendedAssetList.absorbInternal: userBasic[account]
17272: JUMPDEST | 17273: PUSH1 0x00 | 17275: PUSH2 0x4383 | 17278: SWAP2 | 17279: PUSH2 0x2d1b | 17282: JUMP    ;; CometWithExtendedAssetList.absorbInternal: userBasic[account].assetsIn = 0
17283: JUMPDEST | 17284: DUP7 | 17285: PUSH2 0x438f | 17288: DUP7 | 17289: PUSH1 0x05 | 17291: PUSH2 0x097c | 17294: JUMP    ;; CometWithExtendedAssetList.absorbInternal: userBasic[account]
17295: JUMPDEST | 17296: PUSH1 0x00 | 17298: PUSH2 0x439a | 17301: SWAP2 | 17302: PUSH2 0x2b4b | 17305: JUMP    ;; CometWithExtendedAssetList.absorbInternal: userBasic[account]._reserved = 0
17306: JUMPDEST | 17307: PUSH2 0x43a3 | 17310: SWAP2 | 17311: PUSH2 0x335c | 17314: JUMP    ;; CometWithExtendedAssetList.absorbInternal: repayAndSupplyAmount(oldPrincipal, newPrincipal)
17315: JUMPDEST | 17316: PUSH1 0x01 | 17318: SLOAD | 17319: PUSH2 0x43af | 17322: SWAP1 | 17323: PUSH2 0x1e6b | 17326: JUMP    ;; SLOAD ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
17327: JUMPDEST | 17328: SWAP1 | 17329: PUSH2 0x43b9 | 17332: SWAP2 | 17333: PUSH2 0x3005 | 17336: JUMP    ;; CometWithExtendedAssetList.absorbInternal: totalSupplyBase += supplyAmount
17337: JUMPDEST | 17338: PUSH2 0x43c4 | 17341: SWAP1 | 17342: PUSH1 0x01 | 17344: PUSH2 0x3022 | 17347: JUMP    ;; CometWithExtendedAssetList.absorbInternal: totalSupplyBase += supplyAmount
17348: JUMPDEST | 17349: PUSH1 0x01 | 17351: SLOAD | 17352: PUSH2 0x43d0 | 17355: SWAP1 | 17356: PUSH2 0x1ebf | 17359: JUMP    ;; SLOAD ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
17360: JUMPDEST | 17361: SWAP1 | 17362: PUSH2 0x43da | 17365: SWAP2 | 17366: PUSH2 0x3041 | 17369: JUMP    ;; CometWithExtendedAssetList.absorbInternal: totalBorrowBase -= repayAmount
17370: JUMPDEST | 17371: PUSH2 0x43e5 | 17374: SWAP1 | 17375: PUSH1 0x01 | 17377: PUSH2 0x3059 | 17380: JUMP    ;; CometWithExtendedAssetList.absorbInternal: totalBorrowBase -= repayAmount
17381: JUMPDEST | 17382: PUSH2 0x43ee | 17385: SWAP2 | 17386: PUSH2 0x25f1 | 17389: JUMP    ;; CometWithExtendedAssetList.absorbInternal: newBalance - oldBalance
17390: JUMPDEST | 17391: PUSH2 0x43f7 | 17394: SWAP1 | 17395: PUSH2 0x4622 | 17398: JUMP    ;; CometWithExtendedAssetList.absorbInternal: unsigned256(newBalance - oldBalance)
17399: JUMPDEST | 17400: SWAP3 | 17401: PUSH2 0x4402 | 17404: SWAP2 | 17405: DUP5 | 17406: PUSH2 0x2bba | 17409: JUMP    ;; CometWithExtendedAssetList.absorbInternal: mulPrice(basePaidOut, basePrice, uint64(baseScale))
17410: JUMPDEST | 17411: PUSH1 0x40 | 17413: DUP1 | 17414: MLOAD | 17415: SWAP4 | 17416: DUP5 | 17417: MSTORE | 17418: PUSH1 0x20 | 17420: DUP5 | 17421: ADD | 17422: SWAP2 | 17423: SWAP1 | 17424: SWAP2 | 17425: MSTORE | 17426: PUSH1 0x01 | 17428: PUSH1 0x01 | 17430: PUSH1 0xa0 | 17432: SHL | 17433: SUB | 17434: SWAP2 | 17435: DUP3 | 17436: AND | 17437: SWAP5 | 17438: DUP6 | 17439: SWAP4 | 17440: SWAP3 | 17441: AND | 17442: SWAP2 | 17443: PUSH32 0x1547a878dc89ad3c367b6338b4be6a65a5dd74fb77ae044da1e8747ef1f4f62f | 17476: SWAP2 | 17477: SWAP1 | 17478: LOG3 | 17479: DUP1 | 17480: PUSH1 0x0c | 17482: SIGNEXTEND | 17483: PUSH1 0x00 | 17485: SLT | 17486: PUSH2 0x4455 | 17489: JUMPI    ;; LOG3 ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
17490: POP | 17491: POP | 17492: JUMP    ;; CometWithExtendedAssetList.absorbInternal: function absorbInternal(address absorber, address account) internal { i…
17493: JUMPDEST | 17494: PUSH1 0x00 | 17496: DUP1 | 17497: MLOAD | 17498: PUSH1 0x20 | 17500: PUSH2 0x4832 | 17503: DUP4 | 17504: CODECOPY | 17505: DUP2 | 17506: MLOAD | 17507: SWAP2 | 17508: MSTORE | 17509: PUSH2 0x31c1 | 17512: PUSH2 0x31b1 | 17515: PUSH1 0x00 | 17517: SWAP4 | 17518: PUSH2 0x4480 | 17521: PUSH2 0x447a | 17524: DUP7 | 17525: SLOAD | 17526: PUSH2 0x0b8f | 17529: JUMP    ;; SLOAD ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
17530: JUMPDEST | 17531: SWAP2 | 17532: PUSH2 0x45f9 | 17535: JUMP    ;; CometWithExtendedAssetList.absorbInternal: unsigned104(newPrincipal)
17536: JUMPDEST | 17537: SWAP1 | 17538: PUSH2 0x2466 | 17541: JUMP    ;; CometWithExtendedAssetList.absorbInternal: presentValueSupply(baseSupplyIndex, unsigned104(newPrincipal))
17542: JUMPDEST | 17543: PUSH1 0x00 | 17545: SWAP3 | 17546: POP | 17547: PUSH2 0x4358 | 17550: JUMP    ;; CometWithExtendedAssetList.absorbInternal: if (newBalance < 0) { newBalance = 0; }
17551: JUMPDEST | 17552: PUSH2 0x449a | 17555: DUP3 | 17556: DUP3 | 17557: DUP6 | 17558: PUSH2 0x2cc0 | 17561: JUMP    ;; CometWithExtendedAssetList.absorbInternal: isInAsset(assetsIn, i, _reserved)
17562: JUMPDEST | 17563: PUSH2 0x44aa | 17566: JUMPI    ;; CometWithExtendedAssetList.absorbInternal: if (isInAsset(assetsIn, i, _reserved)) { AssetInfo memory assetInfo = g…
17567: JUMPDEST | 17568: PUSH1 0x01 | 17570: ADD | 17571: PUSH1 0xff | 17573: AND | 17574: PUSH2 0x42d6 | 17577: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
17578: JUMPDEST | 17579: DUP7 | 17580: DUP11 | 17581: PUSH2 0x44b5 | 17584: DUP4 | 17585: PUSH2 0x1c0b | 17588: JUMP    ;; CometWithExtendedAssetList.absorbInternal: getAssetInfo(i)
17589: JUMPDEST | 17590: PUSH1 0x20 | 17592: DUP2 | 17593: ADD | 17594: MLOAD | 17595: DUP4 | 17596: SWAP1 | 17597: PUSH1 0x01 | 17599: PUSH1 0x01 | 17601: PUSH1 0xa0 | 17603: SHL | 17604: SUB | 17605: AND | 17606: SWAP12 | 17607: DUP13 | 17608: PUSH1 0x06 | 17610: DUP2 | 17611: PUSH2 0x44d4 | 17614: DUP6 | 17615: DUP4 | 17616: PUSH2 0x097c | 17619: JUMP    ;; CometWithExtendedAssetList.absorbInternal: userCollateral[account]
17620: JUMPDEST | 17621: SWAP1 | 17622: PUSH2 0x44de | 17625: SWAP2 | 17626: PUSH2 0x097c | 17629: JUMP    ;; CometWithExtendedAssetList.absorbInternal: userCollateral[account][asset]
17630: JUMPDEST | 17631: SLOAD | 17632: PUSH1 0x01 | 17634: PUSH1 0x01 | 17636: PUSH1 0x80 | 17638: SHL | 17639: SUB | 17640: AND | 17641: SWAP4 | 17642: PUSH2 0x44f2 | 17645: SWAP2 | 17646: PUSH2 0x097c | 17649: JUMP    ;; SLOAD ;; CometWithExtendedAssetList.absorbInternal: userCollateral[account]
17650: JUMPDEST | 17651: SWAP1 | 17652: PUSH2 0x44fc | 17655: SWAP2 | 17656: PUSH2 0x097c | 17659: JUMP    ;; CometWithExtendedAssetList.absorbInternal: userCollateral[account][asset]
17660: JUMPDEST | 17661: PUSH1 0x00 | 17663: PUSH2 0x4507 | 17666: SWAP2 | 17667: PUSH2 0x3596 | 17670: JUMP    ;; CometWithExtendedAssetList.absorbInternal: userCollateral[account][asset].balance = 0
17671: JUMPDEST | 17672: PUSH2 0x4512 | 17675: DUP14 | 17676: PUSH1 0x02 | 17678: PUSH2 0x097c | 17681: JUMP    ;; CometWithExtendedAssetList.absorbInternal: totalsCollateral[asset]
17682: JUMPDEST | 17683: DUP3 | 17684: DUP2 | 17685: SLOAD | 17686: PUSH2 0x451e | 17689: SWAP1 | 17690: PUSH2 0x0993 | 17693: JUMP    ;; SLOAD ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
17694: JUMPDEST | 17695: SWAP1 | 17696: PUSH2 0x4528 | 17699: SWAP2 | 17700: PUSH2 0x3bc9 | 17703: JUMP    ;; CometWithExtendedAssetList.absorbInternal: totalsCollateral[asset].totalSupplyAsset -= seizeAmount
17704: JUMPDEST | 17705: PUSH2 0x4531 | 17708: SWAP2 | 17709: PUSH2 0x3596 | 17712: JUMP    ;; CometWithExtendedAssetList.absorbInternal: totalsCollateral[asset].totalSupplyAsset -= seizeAmount
17713: JUMPDEST | 17714: PUSH1 0x40 | 17716: DUP4 | 17717: ADD | 17718: MLOAD | 17719: PUSH1 0x01 | 17721: PUSH1 0x01 | 17723: PUSH1 0xa0 | 17725: SHL | 17726: SUB | 17727: AND | 17728: PUSH2 0x4548 | 17731: SWAP1 | 17732: PUSH2 0x249f | 17735: JUMP    ;; CometWithExtendedAssetList.absorbInternal: getPrice(assetInfo.priceFeed)
17736: JUMPDEST | 17737: PUSH1 0x60 | 17739: DUP5 | 17740: ADD | 17741: MLOAD | 17742: PUSH2 0x4556 | 17745: SWAP1 | 17746: PUSH2 0x0b8f | 17749: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
17750: JUMPDEST | 17751: PUSH2 0x4569 | 17754: SWAP2 | 17755: PUSH1 0x01 | 17757: PUSH1 0x01 | 17759: PUSH1 0x80 | 17761: SHL | 17762: SUB | 17763: DUP6 | 17764: AND | 17765: PUSH2 0x2bba | 17768: JUMP    ;; CometWithExtendedAssetList.absorbInternal: mulPrice(seizeAmount, getPrice(assetInfo.priceFeed), assetInfo.scale)
17769: JUMPDEST | 17770: SWAP3 | 17771: PUSH1 0xc0 | 17773: ADD | 17774: MLOAD | 17775: PUSH2 0x4577 | 17778: SWAP1 | 17779: PUSH2 0x0b8f | 17782: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
17783: JUMPDEST | 17784: PUSH2 0x4580 | 17787: SWAP1 | 17788: PUSH2 0x0b8f | 17791: JUMP    ;; CometWithExtendedAssetList.absorbInternal: mulFactor(value, assetInfo.liquidationFactor)
17792: JUMPDEST | 17793: PUSH2 0x458a | 17796: SWAP1 | 17797: DUP5 | 17798: PUSH2 0x2b7c | 17801: JUMP    ;; CometWithExtendedAssetList.absorbInternal: mulFactor(value, assetInfo.liquidationFactor)
17802: JUMPDEST | 17803: PUSH2 0x4593 | 17806: SWAP2 | 17807: PUSH2 0x218f | 17810: JUMP    ;; CometWithExtendedAssetList.absorbInternal: deltaValue += mulFactor(value, assetInfo.liquidationFactor)
17811: JUMPDEST | 17812: PUSH1 0x40 | 17814: DUP1 | 17815: MLOAD | 17816: PUSH1 0x01 | 17818: PUSH1 0x01 | 17820: PUSH1 0x80 | 17822: SHL | 17823: SUB | 17824: SWAP4 | 17825: SWAP1 | 17826: SWAP4 | 17827: AND | 17828: DUP4 | 17829: MSTORE | 17830: PUSH1 0x20 | 17832: DUP4 | 17833: ADD | 17834: SWAP4 | 17835: SWAP1 | 17836: SWAP4 | 17837: MSTORE | 17838: SWAP12 | 17839: PUSH1 0x01 | 17841: PUSH1 0x01 | 17843: PUSH1 0xa0 | 17845: SHL | 17846: SUB | 17847: SWAP1 | 17848: DUP2 | 17849: AND | 17850: SWAP5 | 17851: DUP2 | 17852: AND | 17853: SWAP4 | 17854: AND | 17855: SWAP2 | 17856: PUSH32 0x9850ab1af75177e4a9201c65a2cf7976d5d28e40ef63494b44366f86b2f9412e | 17889: SWAP2 | 17890: LOG4 | 17891: PUSH2 0x449f | 17894: JUMP    ;; LOG4 ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
17895: JUMPDEST | 17896: PUSH1 0x40 | 17898: MLOAD | 17899: PUSH4 0x6ef5bcdd | 17904: PUSH1 0xe1 | 17906: SHL | 17907: DUP2 | 17908: MSTORE | 17909: PUSH1 0x04 | 17911: SWAP1 | 17912: REVERT    ;; CometWithExtendedAssetList.absorbInternal: NotLiquidatable()
17913: JUMPDEST | 17914: PUSH1 0x00 | 17916: DUP2 | 17917: PUSH1 0x0c | 17919: SIGNEXTEND | 17920: SLT | 17921: PUSH2 0x4610 | 17924: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
17925: PUSH1 0x01 | 17927: PUSH1 0x01 | 17929: PUSH1 0x68 | 17931: SHL | 17932: SUB | 17933: AND | 17934: SWAP1 | 17935: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
17936: JUMPDEST | 17937: PUSH1 0x40 | 17939: MLOAD | 17940: PUSH4 0x363b64b7 | 17945: PUSH1 0xe1 | 17947: SHL | 17948: DUP2 | 17949: MSTORE | 17950: PUSH1 0x04 | 17952: SWAP1 | 17953: REVERT    ;; CometMath.unsigned104: NegativeNumber()
17954: JUMPDEST | 17955: PUSH1 0x00 | 17957: DUP2 | 17958: SLT | 17959: PUSH2 0x4610 | 17962: JUMPI    ;; CometMath.unsigned256: n < 0
17963: SWAP1 | 17964: JUMP    ;; CometMath.unsigned256: function unsigned256(int256 n) internal pure returns (uint256) { if (n …
17965: JUMPDEST | 17966: SWAP1 | 17967: PUSH2 0x46f5 | 17970: PUSH2 0x463d | 17973: PUSH2 0x0979 | 17976: SWAP4 | 17977: PUSH2 0x1d3a | 17980: JUMP    ;; CometWithExtendedAssetList.quoteCollateral: function quoteCollateral(address asset, uint baseAmount) override publi…
17981: JUMPDEST | 17982: PUSH2 0x46c0 | 17985: PUSH1 0x60 | 17987: PUSH2 0x46eb | 17990: PUSH2 0x465a | 17993: PUSH1 0x01 | 17995: DUP1 | 17996: PUSH1 0xa0 | 17998: SHL | 17999: SUB | 18000: PUSH1 0x40 | 18002: DUP7 | 18003: ADD | 18004: MLOAD | 18005: AND | 18006: PUSH2 0x249f | 18009: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
18010: JUMPDEST | 18011: PUSH1 0xc0 | 18013: DUP6 | 18014: ADD | 18015: MLOAD | 18016: PUSH1 0x01 | 18018: PUSH1 0x01 | 18020: PUSH1 0x40 | 18022: SHL | 18023: SUB | 18024: SWAP5 | 18025: PUSH8 0x0de0b6b3a7640000 | 18034: SWAP3 | 18035: SWAP1 | 18036: SWAP2 | 18037: DUP4 | 18038: SWAP1 | 18039: PUSH2 0x46af | 18042: SWAP1 | 18043: DUP9 | 18044: SWAP1 | 18045: DUP2 | 18046: AND | 18047: DUP1 | 18048: DUP5 | 18049: LT | 18050: PUSH2 0x473f | 18053: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
18054: JUMPDEST | 18055: DUP4 | 18056: SUB | 18057: AND | 18058: PUSH32 0x0000000000000000000000000000000000000000000000000000000000000000 | 18091: PUSH2 0x1e77 | 18094: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
18095: JUMPDEST | 18096: DIV | 18097: DUP1 | 18098: DUP5 | 18099: LT | 18100: PUSH2 0x4732 | 18103: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
18104: JUMPDEST | 18105: DUP4 | 18106: SUB | 18107: SWAP1 | 18108: PUSH2 0x1e77 | 18111: JUMP    ;; CometWithExtendedAssetList.mulFactor: n * factor
18112: JUMPDEST | 18113: DIV | 18114: SWAP6 | 18115: PUSH2 0x2f19 | 18118: PUSH32 0x0000000000000000000000000000000000000000000000000000000000000000 | 18151: PUSH2 0x249f | 18154: JUMP    ;; CometWithExtendedAssetList.quoteCollateral: getPrice(baseTokenPriceFeed)
18155: JUMPDEST | 18156: SWAP3 | 18157: ADD | 18158: MLOAD | 18159: AND | 18160: SWAP1 | 18161: PUSH2 0x1e77 | 18164: JUMP    ;; CometWithExtendedAssetList.quoteCollateral: basePrice * baseAmount * assetInfo.scale
18165: JUMPDEST | 18166: SWAP1 | 18167: DUP1 | 18168: ISZERO | 18169: PUSH2 0x4725 | 18172: JUMPI    ;; CometCore helper: 1e18
18173: JUMPDEST | 18174: PUSH32 0x0000000000000000000000000000000000000000000000000000000000000000 | 18207: SWAP2 | 18208: DIV | 18209: PUSH2 0x23d6 | 18212: JUMP    ;; CometCore helper: 1e18
18213: JUMPDEST | 18214: PUSH2 0x472d | 18217: PUSH2 0x23bf | 18220: JUMP    ;; CometCore helper: 1e18
18221: JUMPDEST | 18222: PUSH2 0x46fd | 18225: JUMP    ;; CometCore helper: 1e18
18226: JUMPDEST | 18227: PUSH2 0x473a | 18230: PUSH2 0x1e32 | 18233: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
18234: JUMPDEST | 18235: PUSH2 0x46b8 | 18238: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
18239: JUMPDEST | 18240: PUSH2 0x4747 | 18243: PUSH2 0x1e32 | 18246: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
18247: JUMPDEST | 18248: PUSH2 0x4686 | 18251: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
18252: JUMPDEST | 18253: PUSH2 0x476f | 18256: PUSH2 0x4757 | 18259: PUSH2 0x1dbe | 18262: JUMP    ;; CometWithExtendedAssetList.balanceOf: getNowInternal()
18263: JUMPDEST | 18264: PUSH2 0x06ab | 18267: PUSH5 0xffffffffff | 18273: SWAP2 | 18274: DUP3 | 18275: PUSH1 0x01 | 18277: SLOAD | 18278: PUSH1 0xd0 | 18280: SHR | 18281: AND | 18282: SWAP1 | 18283: PUSH2 0x1e49 | 18286: JUMP    ;; SLOAD ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
18287: JUMPDEST | 18288: POP | 18289: PUSH1 0x01 | 18291: PUSH1 0x01 | 18293: PUSH1 0xa0 | 18295: SHL | 18296: SUB | 18297: SWAP1 | 18298: SWAP2 | 18299: AND | 18300: PUSH1 0x00 | 18302: SWAP1 | 18303: DUP2 | 18304: MSTORE | 18305: PUSH1 0x05 | 18307: PUSH1 0x20 | 18309: MSTORE | 18310: PUSH1 0x40 | 18312: DUP2 | 18313: KECCAK256 | 18314: SLOAD | 18315: PUSH1 0x0c | 18317: SIGNEXTEND | 18318: SWAP2 | 18319: SWAP1 | 18320: DUP1 | 18321: DUP4 | 18322: SGT | 18323: ISZERO | 18324: PUSH2 0x47a4 | 18327: JUMPI    ;; KECCAK256,SLOAD ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
18328: POP | 18329: PUSH2 0x4480 | 18332: PUSH2 0x0979 | 18335: SWAP3 | 18336: PUSH2 0x45f9 | 18339: JUMP    ;; CometWithExtendedAssetList.balanceOf: unsigned104(principal)
18340: JUMPDEST | 18341: SWAP2 | 18342: POP | 18343: POP | 18344: SWAP1 | 18345: JUMP    ;; CometWithExtendedAssetList.balanceOf: principal > 0 ? presentValueSupply(baseSupplyIndex_, unsigned104(princi…
18346: JUMPDEST | 18347: PUSH2 0x47b5 | 18350: PUSH2 0x4757 | 18353: PUSH2 0x1dbe | 18356: JUMP    ;; CometWithExtendedAssetList.borrowBalanceOf: getNowInternal()
18357: JUMPDEST | 18358: PUSH1 0x01 | 18360: PUSH1 0x01 | 18362: PUSH1 0xa0 | 18364: SHL | 18365: SUB | 18366: SWAP1 | 18367: SWAP3 | 18368: AND | 18369: PUSH1 0x00 | 18371: SWAP1 | 18372: DUP2 | 18373: MSTORE | 18374: PUSH1 0x05 | 18376: PUSH1 0x20 | 18378: MSTORE | 18379: PUSH1 0x40 | 18381: DUP2 | 18382: KECCAK256 | 18383: SLOAD | 18384: PUSH1 0x0c | 18386: SIGNEXTEND | 18387: SWAP3 | 18388: SWAP2 | 18389: POP | 18390: DUP1 | 18391: DUP4 | 18392: SLT | 18393: ISZERO | 18394: PUSH2 0x47a4 | 18397: JUMPI    ;; KECCAK256,SLOAD ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
18398: POP | 18399: PUSH2 0x4480 | 18402: PUSH2 0x47ed | 18405: PUSH2 0x0979 | 18408: SWAP4 | 18409: PUSH2 0x2989 | 18412: JUMP    ;; CometWithExtendedAssetList.borrowBalanceOf: -principal
18413: JUMPDEST | 18414: PUSH2 0x45f9 | 18417: JUMP    ;; CometWithExtendedAssetList.borrowBalanceOf: unsigned104(-principal)
18418: JUMPDEST | 18419: POP | 18420: PUSH1 0x00 | 18422: CALLDATASIZE | 18423: DUP2 | 18424: DUP1 | 18425: CALLDATACOPY | 18426: DUP1 | 18427: DUP1 | 18428: CALLDATASIZE | 18429: DUP2 | 18430: PUSH32 0x0000000000000000000000000000000000000000000000000000000000000000 | 18463: GAS | 18464: UNSUPPORTED_F4 | 18465: RETURNDATASIZE | 18466: DUP3 | 18467: DUP1 | 18468: RETURNDATACOPY | 18469: ISZERO | 18470: PUSH2 0x482d | 18473: JUMPI    ;; UNSUPPORTED_F4 ;; CometWithExtendedAssetList.fallback: assembly { calldatacopy(0, 0, calldatasize()) let result := delegatecal…
18474: RETURNDATASIZE | 18475: SWAP1 | 18476: RETURN    ;; CometWithExtendedAssetList.fallback: assembly { calldatacopy(0, 0, calldatasize()) let result := delegatecal…
18477: JUMPDEST | 18478: RETURNDATASIZE | 18479: SWAP1 | 18480: REVERT    ;; CometWithExtendedAssetList.fallback: assembly { calldatacopy(0, 0, calldatasize()) let result := delegatecal…
18481: INVALID    ;; INVALID
18482: UNSUPPORTED_DD | 18483: UNSUPPORTED_F2 | 18484: MSTORE | 18485: UNSUPPORTED_AD | 18486: SHL | 18487: UNSUPPORTED_E2 | 18488: UNSUPPORTED_C8 | 18489: SWAP12 | 18490: PUSH10 0xc2b068fc378daa952ba7 | 18501: CALL | 18502: PUSH4 0xc4a11628 | 18507: UNSUPPORTED_F5 | 18508: GAS | 18509: UNSUPPORTED_4D | 18510: UNSUPPORTED_F5 | 18511: UNSUPPORTED_23 | 18512: UNSUPPORTED_B3 | 18513: UNSUPPORTED_EF | 18514: UNSUPPORTED_C9 | 18515: DUP13 | 18516: PUSH24 0x30ba19013824f711a9ab74801459b27e6ff7685cb924587c | 18541: DUP10 | 18542: UNSUPPORTED_AE | 18543: UNSUPPORTED_DA | 18544: MSTORE8 | 18545: UNSUPPORTED_AC    ;; CALL,UNSUPPORTED_F5,UNSUPPORTED_F5
```

## Creation bytecode

- 977 jump destinations: 33, 99, 112, 130, 151, 172, 193, 214, 235, 256, 278, 301, 324, 347, 370, 393, 416, 439, 462, 485, 508, 531, 623, 664, 750, 888, 1308, 1358, 1410, 1994, 2007, 2022, 2043, 2050, 2054, 2063, 2075, 2211, 2226, 2241, 2265, 2273, 2276, 2285, 2303, 2317, 2332, 2357, 2365, 2374, 2392, 2410, 2428, 2442, 2457, 2478, 2485, 2494, 2524, 2535, 2551, 2570, 2589, 2608, 2627, 2684, 2689, 2711, 2747, 2768, 2789, 2810, 2840, 2848, 2850, 3611, 3616, 3625, 3634, 3643, 3652, 3661, 3670, 3679, 3688, 3697, 3706, 3715, 3724, 3733, 3742, 3751, 3760, 3769, 3778, 3787, 3796, 3805, 3814, 3823, 3832, 3841, 3850, 3859, 3868, 3877, 3886, 3895, 3904, 3913, 3922, 3931, 3940, 3949, 3958, 3967, 3976, 3985, 3994, 4003, 4012, 4021, 4030, 4039, 4048, 4057, 4066, 4075, 4084, 4093, 4102, 4111, 4120, 4129, 4138, 4147, 4156, 4165, 4174, 4183, 4192, 4201, 4210, 4219, 4236, 4241, 4276, 4281, 4291, 4302, 4330, 4338, 4376, 4395, 4465, 4504, 4533, 4539, 4564, 4573, 4633, 4687, 4747, 4764, 4767, 4827, 4849, 4866, 4872, 4892, 4902, 4942, 4971, 5041, 5064, 5079, 5096, 5116, 5128, 5134, 5154, 5214, 5239, 5251, 5254, 5277, 5289, 5315, 5338, 5368, 5396, 5400, 5460, 5490, 5522, 5582, 5645, 5705, 5740, 5745, 5780, 5785, 5797, 5893, 5947, 5949, 5985, 5990, 6002, 6037, 6042, 6062, 6071, 6078, 6098, 6107, 6114, 6174, 6187, 6215, 6225, 6235, 6246, 6257, 6309, 6369, 6383, 6397, 6412, 6427, 6442, 6450, 6503, 6508, 6525, 6570, 6640, 6670, 6726, 6786, 6825, 6860, 6865, 6925, 6960, 6969, 6997, 7057, 7096, 7125, 7154, 7193, 7213, 7225, 7231, 7291, 7351, 7411, 7471, 7502, 7520, 7555, 7560, 7584, 7613, 7625, 7664, 7727, 7787, 7820, 7828, 7873, 7933, 7950, 8047, 8058, 8064, 8079, 8085, 8093, 8098, 8131, 8139, 8179, 8242, 8253, 8273, 8285, 8291, 8311, 8320, 8327, 8357, 8428, 8498, 8528, 8608, 8619, 8655, 8660, 8682, 8688, 8727, 8758, 8788, 8873, 8943, 8973, 9034, 9046, 9128, 9142, 9160, 9170, 9178, 9208, 9221, 9229, 9250, 9262, 9312, 9323, 9342, 9401, 9406, 9413, 9448, 9474, 9492, 9510, 9553, 9571, 9641, 9674, 9682, 9694, 9727, 9735, 9747, 9776, 9803, 9808, 9843, 9865, 9881, 9930, 9941, 9952, 9972, 9992, 10005, 10013, 10098, 10110, 10123, 10133, 10161, 10170, 10184, 10201, 10218, 10235, 10252, 10269, 10280, 10288, 10295, 10303, 10308, 10317, 10361, 10388, 10397, 10431, 10440, 10463, 10481, 10496, 10556, 10579, 10601, 10609, 10613, 10625, 10644, 10652, 10656, 10685, 10693, 10697, 10712, 10720, 10746, 10752, 10762, 10772, 10788, 10859, 10870, 10923, 10938, 10943, 10952, 10995, 11050, 11055, 11060, 11070, 11075, 11107, 11115, 11170, 11189, 11227, 11233, 11253, 11271, 11302, 11308, 11346, 11353, 11360, 11385, 11391, 11397, 11403, 11409, 11417, 11429, 11440, 11538, 11577, 11644, 11653, 11692, 11699, 11707, 11712, 11810, 11849, 11916, 11925, 11964, 11972, 11977, 12000, 12010, 12018, 12022, 12072, 12088, 12101, 12131, 12139, 12144, 12181, 12201, 12244, 12252, 12265, 12283, 12295, 12308, 12326, 12344, 12351, 12359, 12367, 12372, 12387, 12433, 12441, 12478, 12494, 12504, 12512, 12519, 12526, 12534, 12539, 12560, 12581, 12589, 12594, 12619, 12638, 12646, 12651, 12662, 12692, 12697, 12729, 12783, 12791, 12848, 12861, 12868, 12874, 12880, 12886, 12929, 12942, 12950, 12955, 12972, 12990, 13004, 13011, 13040, 13051, 13072, 13079, 13085, 13126, 13174, 13217, 13237, 13248, 13253, 13263, 13316, 13324, 13344, 13357, 13380, 13393, 13405, 13413, 13418, 13424, 13429, 13438, 13451, 13459, 13478, 13484, 13492, 13497, 13514, 13572, 13578, 13611, 13626, 13631, 13645, 13674, 13695, 13738, 13757, 13768, 13773, 13783, 13836, 13859, 13872, 13885, 13894, 13904, 13909, 13944, 13958, 13977, 14020, 14030, 14052, 14063, 14094, 14120, 14138, 14149, 14171, 14187, 14195, 14199, 14207, 14212, 14220, 14225, 14233, 14238, 14246, 14251, 14259, 14264, 14282, 14313, 14330, 14349, 14373, 14404, 14518, 14527, 14546, 14619, 14627, 14633, 14648, 14687, 14726, 14744, 14757, 14783, 14799, 14806, 14811, 14824, 14829, 14877, 14883, 14888, 14893, 14922, 14926, 15007, 15013, 15027, 15033, 15053, 15071, 15101, 15119, 15148, 15179, 15203, 15244, 15291, 15299, 15316, 15321, 15348, 15357, 15362, 15369, 15389, 15394, 15401, 15412, 15417, 15424, 15430, 15508, 15542, 15547, 15563, 15568, 15601, 15606, 15639, 15670, 15676, 15685, 15692, 15699, 15704, 15712, 15717, 15725, 15730, 15738, 15743, 15773, 15790, 15797, 15805, 15810, 15818, 15823, 15843, 15861, 15890, 15908, 15940, 15961, 15969, 15974, 16010, 16025, 16042, 16060, 16069, 16085, 16098, 16145, 16158, 16166, 16235, 16240, 16260, 16269, 16302, 16314, 16322, 16329, 16351, 16358, 16366, 16371, 16389, 16398, 16413, 16419, 16427, 16432, 16456, 16463, 16471, 16476, 16491, 16515, 16544, 16575, 16599, 16627, 16646, 16672, 16677, 16687, 16702, 16707, 16725, 16730, 16743, 16753, 16770, 16854, 16859, 16866, 16880, 16885, 16892, 16897, 16903, 16935, 16940, 16958, 16981, 17000, 17035, 17050, 17058, 17075, 17082, 17096, 17116, 17128, 17140, 17147, 17155, 17165, 17205, 17213, 17230, 17237, 17251, 17274, 17281, 17293, 17300, 17311, 17322, 17352, 17446, 17452, 17466, 17472, 17490, 17501, 17512, 17521, 17532, 17541, 17554, 17567, 17577, 17586, 17595, 17605, 17615, 17624, 17634, 17644, 17656, 17667, 17682, 17692, 17702, 17713, 17725, 17735, 17745, 17756, 17766, 17776, 17785, 17803, 17815, 17849, 17877, 17911, 17939, 17949, 17958, 18008, 18018, 18036, 18054, 18089, 18106, 18115, 18131, 18155, 18208, 18239, 18251, 18261, 18275, 18285, 18295, 18308, 18318, 18328, 18337, 18349, 18358, 18367, 18423, 18453, 18534, 18540, 18554, 18560, 18574, 18588, 18602, 18614, 18623, 18639, 18646, 18667, 18678, 18687, 18731, 18809, 18843, 18852, 18902, 18912, 18939, 18997, 19008, 19013, 19034, 19042, 19049, 19067, 19078, 19087, 19094, 19102, 19107, 19161, 19173, 19206, 19215, 19237, 19247, 19256, 19267, 19276, 19328, 19345, 19361, 19383, 19393, 19408, 19468, 19490, 19518, 19521, 19559, 19579, 19584, 19605, 19610, 19620, 19638, 19645, 19663, 19676, 19683, 19768, 19787, 19792, 19798, 19804, 19817, 19835, 19847, 19857, 19873, 19888, 19930, 19936, 20045, 20050, 20056, 20066, 20075, 20087, 20098, 20109, 20121, 20132, 20141, 20153, 20163, 20174, 20186, 20196, 20207, 20216, 20225, 20236, 20319, 20356, 20362, 20368, 20377, 20388, 20393, 20404, 20415, 20446, 20456, 20476, 20486, 20497, 20508, 20520, 20530, 20539, 20562, 20576, 20595, 20609, 20618, 20628, 20637, 20721, 20739, 20762, 20780, 20791, 20807, 20836, 20880, 20921, 20930, 20938, 20981, 20991, 20999, 21039, 21047, 21052, 21060, 21065, 21073, 21078, 21089, 21113, 21166, 21172, 21183, 21239, 21244, 21303
- CODECOPY sites: 35, 1427, 4955, 5147, 9467, 15082, 15519, 17826, 17888, 18820, 20330

```text
0: PUSH2 0x03a0 | 3: DUP1 | 4: PUSH1 0x40 | 6: MSTORE | 7: CALLVALUE | 8: PUSH3 0x000a7c | 12: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
13: PUSH3 0x0053b1 | 17: DUP1 | 18: CODESIZE | 19: SUB | 20: DUP1 | 21: SWAP2 | 22: PUSH3 0x000021 | 26: DUP3 | 27: DUP6 | 28: PUSH3 0x000a97 | 32: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
33: JUMPDEST | 34: DUP4 | 35: CODECOPY | 36: PUSH1 0x20 | 38: DUP3 | 39: DUP3 | 40: DUP2 | 41: ADD | 42: SUB | 43: SLT | 44: PUSH3 0x000a7c | 48: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
49: DUP2 | 50: MLOAD | 51: PUSH1 0x01 | 53: PUSH1 0x01 | 55: PUSH1 0x40 | 57: SHL | 58: SUB | 59: DUP2 | 60: GT | 61: PUSH3 0x000a7c | 65: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
66: PUSH2 0x02a0 | 69: DUP2 | 70: DUP5 | 71: ADD | 72: DUP4 | 73: DUP6 | 74: ADD | 75: SUB | 76: SLT | 77: PUSH3 0x000a7c | 81: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
82: PUSH1 0x40 | 84: MLOAD | 85: SWAP3 | 86: PUSH3 0x000063 | 90: PUSH2 0x02a0 | 93: DUP6 | 94: PUSH3 0x000a97 | 98: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
99: JUMPDEST | 100: PUSH3 0x000070 | 104: DUP3 | 105: DUP3 | 106: ADD | 107: PUSH3 0x000abb | 111: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
112: JUMPDEST | 113: DUP5 | 114: MSTORE | 115: PUSH3 0x000082 | 119: PUSH1 0x20 | 121: DUP4 | 122: DUP4 | 123: ADD | 124: ADD | 125: PUSH3 0x000abb | 129: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
130: JUMPDEST | 131: PUSH1 0x20 | 133: DUP6 | 134: ADD | 135: MSTORE | 136: PUSH3 0x000097 | 140: PUSH1 0x40 | 142: DUP4 | 143: DUP4 | 144: ADD | 145: ADD | 146: PUSH3 0x000abb | 150: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
151: JUMPDEST | 152: PUSH1 0x40 | 154: DUP6 | 155: ADD | 156: MSTORE | 157: PUSH3 0x0000ac | 161: PUSH1 0x60 | 163: DUP4 | 164: DUP4 | 165: ADD | 166: ADD | 167: PUSH3 0x000abb | 171: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
172: JUMPDEST | 173: PUSH1 0x60 | 175: DUP6 | 176: ADD | 177: MSTORE | 178: PUSH3 0x0000c1 | 182: PUSH1 0x80 | 184: DUP4 | 185: DUP4 | 186: ADD | 187: ADD | 188: PUSH3 0x000abb | 192: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
193: JUMPDEST | 194: PUSH1 0x80 | 196: DUP6 | 197: ADD | 198: MSTORE | 199: PUSH3 0x0000d6 | 203: PUSH1 0xa0 | 205: DUP4 | 206: DUP4 | 207: ADD | 208: ADD | 209: PUSH3 0x000ad0 | 213: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
214: JUMPDEST | 215: PUSH1 0xa0 | 217: DUP6 | 218: ADD | 219: MSTORE | 220: PUSH3 0x0000eb | 224: PUSH1 0xc0 | 226: DUP4 | 227: DUP4 | 228: ADD | 229: ADD | 230: PUSH3 0x000ad0 | 234: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
235: JUMPDEST | 236: PUSH1 0xc0 | 238: DUP6 | 239: ADD | 240: MSTORE | 241: PUSH3 0x000100 | 245: PUSH1 0xe0 | 247: DUP4 | 248: DUP4 | 249: ADD | 250: ADD | 251: PUSH3 0x000ad0 | 255: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
256: JUMPDEST | 257: PUSH1 0xe0 | 259: DUP6 | 260: ADD | 261: MSTORE | 262: PUSH3 0x000116 | 266: PUSH2 0x0100 | 269: DUP4 | 270: DUP4 | 271: ADD | 272: ADD | 273: PUSH3 0x000ad0 | 277: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
278: JUMPDEST | 279: PUSH2 0x0100 | 282: DUP6 | 283: ADD | 284: MSTORE | 285: PUSH3 0x00012d | 289: PUSH2 0x0120 | 292: DUP4 | 293: DUP4 | 294: ADD | 295: ADD | 296: PUSH3 0x000ad0 | 300: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
301: JUMPDEST | 302: PUSH2 0x0120 | 305: DUP6 | 306: ADD | 307: MSTORE | 308: PUSH3 0x000144 | 312: PUSH2 0x0140 | 315: DUP4 | 316: DUP4 | 317: ADD | 318: ADD | 319: PUSH3 0x000ad0 | 323: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
324: JUMPDEST | 325: PUSH2 0x0140 | 328: DUP6 | 329: ADD | 330: MSTORE | 331: PUSH3 0x00015b | 335: PUSH2 0x0160 | 338: DUP4 | 339: DUP4 | 340: ADD | 341: ADD | 342: PUSH3 0x000ad0 | 346: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
347: JUMPDEST | 348: PUSH2 0x0160 | 351: DUP6 | 352: ADD | 353: MSTORE | 354: PUSH3 0x000172 | 358: PUSH2 0x0180 | 361: DUP4 | 362: DUP4 | 363: ADD | 364: ADD | 365: PUSH3 0x000ad0 | 369: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
370: JUMPDEST | 371: PUSH2 0x0180 | 374: DUP6 | 375: ADD | 376: MSTORE | 377: PUSH3 0x000189 | 381: PUSH2 0x01a0 | 384: DUP4 | 385: DUP4 | 386: ADD | 387: ADD | 388: PUSH3 0x000ad0 | 392: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
393: JUMPDEST | 394: PUSH2 0x01a0 | 397: DUP6 | 398: ADD | 399: MSTORE | 400: PUSH3 0x0001a0 | 404: PUSH2 0x01c0 | 407: DUP4 | 408: DUP4 | 409: ADD | 410: ADD | 411: PUSH3 0x000ad0 | 415: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
416: JUMPDEST | 417: PUSH2 0x01c0 | 420: DUP6 | 421: ADD | 422: MSTORE | 423: PUSH3 0x0001b7 | 427: PUSH2 0x01e0 | 430: DUP4 | 431: DUP4 | 432: ADD | 433: ADD | 434: PUSH3 0x000ad0 | 438: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
439: JUMPDEST | 440: PUSH2 0x01e0 | 443: DUP6 | 444: ADD | 445: MSTORE | 446: PUSH3 0x0001ce | 450: PUSH2 0x0200 | 453: DUP4 | 454: DUP4 | 455: ADD | 456: ADD | 457: PUSH3 0x000ad0 | 461: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
462: JUMPDEST | 463: PUSH2 0x0200 | 466: DUP6 | 467: ADD | 468: MSTORE | 469: PUSH3 0x0001e5 | 473: PUSH2 0x0220 | 476: DUP4 | 477: DUP4 | 478: ADD | 479: ADD | 480: PUSH3 0x000ae5 | 484: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
485: JUMPDEST | 486: PUSH2 0x0220 | 489: DUP6 | 490: ADD | 491: MSTORE | 492: PUSH3 0x0001fc | 496: PUSH2 0x0240 | 499: DUP4 | 500: DUP4 | 501: ADD | 502: ADD | 503: PUSH3 0x000ae5 | 507: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
508: JUMPDEST | 509: PUSH2 0x0240 | 512: DUP6 | 513: ADD | 514: MSTORE | 515: PUSH3 0x000213 | 519: PUSH2 0x0260 | 522: DUP4 | 523: DUP4 | 524: ADD | 525: ADD | 526: PUSH3 0x000ae5 | 530: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
531: JUMPDEST | 532: PUSH2 0x0260 | 535: DUP6 | 536: ADD | 537: MSTORE | 538: DUP1 | 539: DUP3 | 540: ADD | 541: PUSH2 0x0280 | 544: ADD | 545: MLOAD | 546: SWAP3 | 547: PUSH1 0x01 | 549: PUSH1 0x01 | 551: PUSH1 0x40 | 553: SHL | 554: SUB | 555: DUP5 | 556: GT | 557: PUSH3 0x000a7c | 561: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
562: DUP1 | 563: DUP3 | 564: ADD | 565: PUSH1 0x1f | 567: DUP6 | 568: DUP6 | 569: DUP6 | 570: ADD | 571: ADD | 572: ADD | 573: SLT | 574: ISZERO | 575: PUSH3 0x000a7c | 579: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
580: DUP2 | 581: DUP4 | 582: ADD | 583: DUP5 | 584: ADD | 585: MLOAD | 586: SWAP2 | 587: PUSH1 0x01 | 589: PUSH1 0x01 | 591: PUSH1 0x40 | 593: SHL | 594: SUB | 595: DUP4 | 596: GT | 597: PUSH3 0x000a81 | 601: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
602: PUSH1 0x40 | 604: MLOAD | 605: SWAP5 | 606: PUSH3 0x00026f | 610: PUSH1 0x20 | 612: DUP6 | 613: PUSH1 0x05 | 615: SHL | 616: ADD | 617: DUP8 | 618: PUSH3 0x000a97 | 622: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
623: JUMPDEST | 624: DUP4 | 625: DUP7 | 626: MSTORE | 627: PUSH1 0x20 | 629: DUP7 | 630: ADD | 631: SWAP5 | 632: DUP4 | 633: DUP4 | 634: ADD | 635: PUSH1 0x20 | 637: PUSH1 0xe0 | 639: DUP8 | 640: MUL | 641: DUP5 | 642: DUP5 | 643: DUP8 | 644: ADD | 645: ADD | 646: ADD | 647: ADD | 648: GT | 649: PUSH3 0x000a7c | 653: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
654: DUP3 | 655: DUP2 | 656: ADD | 657: DUP3 | 658: ADD | 659: PUSH1 0x20 | 661: ADD | 662: SWAP6 | 663: SWAP2    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
664: JUMPDEST | 665: PUSH1 0x20 | 667: PUSH1 0xe0 | 669: DUP8 | 670: MUL | 671: DUP3 | 672: DUP5 | 673: DUP8 | 674: ADD | 675: ADD | 676: ADD | 677: ADD | 678: DUP8 | 679: LT | 680: PUSH3 0x0009be | 684: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
685: PUSH2 0x0280 | 688: DUP10 | 689: ADD | 690: DUP9 | 691: SWAP1 | 692: MSTORE | 693: PUSH1 0x40 | 695: DUP1 | 696: DUP11 | 697: ADD | 698: MLOAD | 699: SWAP1 | 700: MLOAD | 701: PUSH4 0x313ce567 | 706: PUSH1 0xe0 | 708: SHL | 709: DUP2 | 710: MSTORE | 711: DUP11 | 712: SWAP2 | 713: PUSH1 0x20 | 715: SWAP1 | 716: DUP3 | 717: SWAP1 | 718: PUSH1 0x04 | 720: SWAP1 | 721: DUP3 | 722: SWAP1 | 723: PUSH1 0x01 | 725: PUSH1 0x01 | 727: PUSH1 0xa0 | 729: SHL | 730: SUB | 731: AND | 732: GAS | 733: STATICCALL | 734: SWAP1 | 735: DUP2 | 736: ISZERO | 737: PUSH3 0x00080f | 741: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
742: PUSH1 0x00 | 744: SWAP2 | 745: PUSH3 0x00097c | 749: JUMPI    ;; CometWithExtendedAssetList.constructor: IERC20NonStandard(config.baseToken).decimals()
750: JUMPDEST | 751: POP | 752: PUSH1 0x12 | 754: PUSH1 0xff | 756: DUP3 | 757: AND | 758: GT | 759: PUSH3 0x0008ed | 763: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
764: PUSH2 0x01a0 | 767: DUP3 | 768: ADD | 769: MLOAD | 770: PUSH8 0x0de0b6b3a7640000 | 779: PUSH1 0x01 | 781: PUSH1 0x01 | 783: PUSH1 0x40 | 785: SHL | 786: SUB | 787: SWAP1 | 788: SWAP2 | 789: AND | 790: GT | 791: PUSH3 0x00096a | 795: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
796: PUSH1 0x18 | 798: PUSH2 0x0280 | 801: DUP4 | 802: ADD | 803: MLOAD | 804: MLOAD | 805: GT | 806: PUSH3 0x000958 | 810: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
811: PUSH2 0x0220 | 814: DUP3 | 815: ADD | 816: MLOAD | 817: PUSH1 0x01 | 819: PUSH1 0x01 | 821: PUSH1 0x68 | 823: SHL | 824: SUB | 825: AND | 826: ISZERO | 827: PUSH3 0x000946 | 831: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
832: PUSH1 0x60 | 834: DUP3 | 835: ADD | 836: MLOAD | 837: PUSH1 0x40 | 839: MLOAD | 840: PUSH4 0x313ce567 | 845: PUSH1 0xe0 | 847: SHL | 848: DUP2 | 849: MSTORE | 850: SWAP1 | 851: PUSH1 0x20 | 853: SWAP1 | 854: DUP3 | 855: SWAP1 | 856: PUSH1 0x04 | 858: SWAP1 | 859: DUP3 | 860: SWAP1 | 861: PUSH1 0x01 | 863: PUSH1 0x01 | 865: PUSH1 0xa0 | 867: SHL | 868: SUB | 869: AND | 870: GAS | 871: STATICCALL | 872: SWAP1 | 873: DUP2 | 874: ISZERO | 875: PUSH3 0x00080f | 879: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
880: PUSH1 0x00 | 882: SWAP2 | 883: PUSH3 0x0008ff | 887: JUMPI    ;; CometWithExtendedAssetList.constructor: IPriceFeed(config.baseTokenPriceFeed).decimals()
888: JUMPDEST | 889: POP | 890: PUSH1 0xff | 892: PUSH1 0x08 | 894: SWAP2 | 895: AND | 896: SUB | 897: PUSH3 0x0008ed | 901: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
902: DUP2 | 903: MLOAD | 904: PUSH1 0x01 | 906: PUSH1 0x01 | 908: PUSH1 0xa0 | 910: SHL | 911: SUB | 912: SWAP1 | 913: DUP2 | 914: AND | 915: PUSH1 0x80 | 917: SWAP1 | 918: DUP2 | 919: MSTORE | 920: PUSH1 0x20 | 922: DUP5 | 923: ADD | 924: MLOAD | 925: DUP3 | 926: AND | 927: PUSH1 0xa0 | 929: MSTORE | 930: PUSH1 0x40 | 932: DUP5 | 933: ADD | 934: MLOAD | 935: DUP3 | 936: AND | 937: PUSH1 0xc0 | 939: MSTORE | 940: PUSH1 0x60 | 942: DUP5 | 943: ADD | 944: MLOAD | 945: DUP3 | 946: AND | 947: PUSH1 0xe0 | 949: MSTORE | 950: DUP4 | 951: ADD | 952: MLOAD | 953: AND | 954: PUSH2 0x0100 | 957: MSTORE | 958: PUSH2 0x01a0 | 961: DUP3 | 962: ADD | 963: MLOAD | 964: PUSH1 0x01 | 966: PUSH1 0x01 | 968: PUSH1 0x40 | 970: SHL | 971: SUB | 972: SWAP1 | 973: DUP2 | 974: AND | 975: PUSH2 0x0220 | 978: MSTORE | 979: PUSH2 0x0320 | 982: DUP3 | 983: SWAP1 | 984: MSTORE | 985: PUSH1 0xff | 987: SWAP1 | 988: SWAP2 | 989: AND | 990: PUSH1 0x0a | 992: EXP | 993: DUP2 | 994: AND | 995: PUSH2 0x0240 | 998: DUP2 | 999: SWAP1 | 1000: MSTORE | 1001: PUSH2 0x01c0 | 1004: DUP4 | 1005: ADD | 1006: MLOAD | 1007: SWAP1 | 1008: SWAP2 | 1009: AND | 1010: PUSH2 0x0260 | 1013: MSTORE | 1014: PUSH3 0x0f4240 | 1018: GT | 1019: PUSH3 0x0008ed | 1023: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
1024: PUSH2 0x0240 | 1027: DUP1 | 1028: MLOAD | 1029: PUSH3 0x0f4240 | 1033: SWAP1 | 1034: DIV | 1035: PUSH2 0x0360 | 1038: MSTORE | 1039: PUSH2 0x0220 | 1042: DUP3 | 1043: ADD | 1044: MLOAD | 1045: PUSH1 0x01 | 1047: PUSH1 0x01 | 1049: PUSH1 0x68 | 1051: SHL | 1052: SUB | 1053: SWAP1 | 1054: DUP2 | 1055: AND | 1056: PUSH2 0x02c0 | 1059: MSTORE | 1060: PUSH2 0x01e0 | 1063: DUP1 | 1064: DUP5 | 1065: ADD | 1066: MLOAD | 1067: PUSH1 0x01 | 1069: PUSH1 0x01 | 1071: PUSH1 0x40 | 1073: SHL | 1074: SUB | 1075: SWAP1 | 1076: DUP2 | 1077: AND | 1078: PUSH2 0x0280 | 1081: SWAP1 | 1082: DUP2 | 1083: MSTORE | 1084: PUSH2 0x0200 | 1087: DUP1 | 1088: DUP8 | 1089: ADD | 1090: MLOAD | 1091: DUP4 | 1092: AND | 1093: PUSH2 0x02a0 | 1096: MSTORE | 1097: SWAP5 | 1098: DUP7 | 1099: ADD | 1100: MLOAD | 1101: DUP5 | 1102: AND | 1103: PUSH2 0x02e0 | 1106: MSTORE | 1107: PUSH2 0x0260 | 1110: DUP7 | 1111: ADD | 1112: MLOAD | 1113: SWAP1 | 1114: SWAP4 | 1115: AND | 1116: PUSH2 0x0300 | 1119: MSTORE | 1120: PUSH1 0xa0 | 1122: DUP6 | 1123: ADD | 1124: MLOAD | 1125: DUP2 | 1126: AND | 1127: PUSH2 0x0120 | 1130: SWAP1 | 1131: DUP2 | 1132: MSTORE | 1133: PUSH1 0xc0 | 1135: DUP7 | 1136: ADD | 1137: MLOAD | 1138: PUSH4 0x01e13380 | 1143: SWAP1 | 1144: DUP4 | 1145: AND | 1146: DUP2 | 1147: SWAP1 | 1148: DIV | 1149: DUP4 | 1150: AND | 1151: PUSH2 0x0140 | 1154: SWAP1 | 1155: DUP2 | 1156: MSTORE | 1157: PUSH1 0xe0 | 1159: DUP9 | 1160: ADD | 1161: MLOAD | 1162: DUP5 | 1163: AND | 1164: DUP3 | 1165: SWAP1 | 1166: DIV | 1167: DUP5 | 1168: AND | 1169: PUSH2 0x0160 | 1172: SWAP1 | 1173: DUP2 | 1174: MSTORE | 1175: PUSH2 0x0100 | 1178: DUP1 | 1179: DUP11 | 1180: ADD | 1181: MLOAD | 1182: DUP7 | 1183: AND | 1184: DUP5 | 1185: SWAP1 | 1186: DIV | 1187: DUP7 | 1188: AND | 1189: PUSH2 0x0180 | 1192: SWAP1 | 1193: DUP2 | 1194: MSTORE | 1195: SWAP5 | 1196: DUP11 | 1197: ADD | 1198: MLOAD | 1199: DUP7 | 1200: AND | 1201: PUSH2 0x01a0 | 1204: MSTORE | 1205: SWAP2 | 1206: DUP10 | 1207: ADD | 1208: MLOAD | 1209: DUP6 | 1210: AND | 1211: DUP4 | 1212: SWAP1 | 1213: DIV | 1214: DUP6 | 1215: AND | 1216: PUSH2 0x01c0 | 1219: MSTORE | 1220: DUP9 | 1221: ADD | 1222: MLOAD | 1223: DUP5 | 1224: AND | 1225: DUP3 | 1226: SWAP1 | 1227: DIV | 1228: DUP5 | 1229: AND | 1230: SWAP1 | 1231: SWAP5 | 1232: MSTORE | 1233: SWAP1 | 1234: DUP7 | 1235: ADD | 1236: MLOAD | 1237: DUP3 | 1238: AND | 1239: DIV | 1240: AND | 1241: SWAP1 | 1242: SWAP3 | 1243: MSTORE | 1244: DUP3 | 1245: ADD | 1246: MLOAD | 1247: MLOAD | 1248: PUSH1 0xff | 1250: AND | 1251: PUSH2 0x0340 | 1254: MSTORE | 1255: MLOAD | 1256: PUSH1 0x40 | 1258: MLOAD | 1259: PUSH4 0x0e085c5b | 1264: PUSH1 0xe3 | 1266: SHL | 1267: DUP2 | 1268: MSTORE | 1269: SWAP2 | 1270: SWAP1 | 1271: PUSH1 0x20 | 1273: SWAP1 | 1274: DUP4 | 1275: SWAP1 | 1276: PUSH1 0x04 | 1278: SWAP1 | 1279: DUP3 | 1280: SWAP1 | 1281: PUSH1 0x01 | 1283: PUSH1 0x01 | 1285: PUSH1 0xa0 | 1287: SHL | 1288: SUB | 1289: AND | 1290: GAS | 1291: STATICCALL | 1292: SWAP2 | 1293: DUP3 | 1294: ISZERO | 1295: PUSH3 0x00080f | 1299: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
1300: PUSH1 0x00 | 1302: SWAP3 | 1303: PUSH3 0x0008a3 | 1307: JUMPI    ;; CometWithExtendedAssetList.constructor: IAssetListFactoryHolder(extensionDelegate).assetListFactory()
1308: JUMPDEST | 1309: POP | 1310: PUSH2 0x0280 | 1313: ADD | 1314: MLOAD | 1315: SWAP1 | 1316: PUSH1 0x40 | 1318: MLOAD | 1319: DUP1 | 1320: SWAP3 | 1321: PUSH4 0xba15b9d1 | 1326: PUSH1 0xe0 | 1328: SHL | 1329: DUP3 | 1330: MSTORE | 1331: PUSH1 0x24 | 1333: DUP3 | 1334: ADD | 1335: PUSH1 0x20 | 1337: PUSH1 0x04 | 1339: DUP5 | 1340: ADD | 1341: MSTORE | 1342: DUP2 | 1343: MLOAD | 1344: DUP1 | 1345: SWAP2 | 1346: MSTORE | 1347: PUSH1 0x20 | 1349: PUSH1 0x44 | 1351: DUP5 | 1352: ADD | 1353: SWAP3 | 1354: ADD | 1355: SWAP1 | 1356: PUSH1 0x00    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
1358: JUMPDEST | 1359: DUP2 | 1360: DUP2 | 1361: LT | 1362: PUSH3 0x00081b | 1366: JUMPI    ;; CometCore helper: 31_536_000
1367: POP | 1368: PUSH1 0x20 | 1370: SWAP5 | 1371: SWAP3 | 1372: DUP5 | 1373: SWAP1 | 1374: SUB | 1375: SWAP3 | 1376: DUP5 | 1377: SWAP3 | 1378: POP | 1379: PUSH1 0x00 | 1381: SWAP2 | 1382: POP | 1383: PUSH1 0x01 | 1385: PUSH1 0x01 | 1387: PUSH1 0xa0 | 1389: SHL | 1390: SUB | 1391: AND | 1392: GAS | 1393: CALL | 1394: SWAP1 | 1395: DUP2 | 1396: ISZERO | 1397: PUSH3 0x00080f | 1401: JUMPI    ;; CometWithExtendedAssetList.constructor: IAssetListFactory(IAssetListFactoryHolder(extensionDelegate).assetListF…
1402: PUSH1 0x00 | 1404: SWAP2 | 1405: PUSH3 0x0007ca | 1409: JUMPI    ;; CometWithExtendedAssetList.constructor: IAssetListFactory(IAssetListFactoryHolder(extensionDelegate).assetListF…
1410: JUMPDEST | 1411: POP | 1412: PUSH2 0x0380 | 1415: MSTORE | 1416: PUSH1 0x40 | 1418: MLOAD | 1419: PUSH2 0x48a7 | 1422: PUSH3 0x000b0a | 1426: DUP3 | 1427: CODECOPY | 1428: PUSH1 0x80 | 1430: MLOAD | 1431: DUP2 | 1432: DUP2 | 1433: DUP2 | 1434: PUSH2 0x0638 | 1437: ADD | 1438: MSTORE | 1439: DUP2 | 1440: DUP2 | 1441: PUSH2 0x0d71 | 1444: ADD | 1445: MSTORE | 1446: DUP2 | 1447: DUP2 | 1448: PUSH2 0x1411 | 1451: ADD | 1452: MSTORE | 1453: PUSH2 0x1811 | 1456: ADD | 1457: MSTORE | 1458: PUSH1 0xa0 | 1460: MLOAD | 1461: DUP2 | 1462: DUP2 | 1463: DUP2 | 1464: PUSH2 0x0878 | 1467: ADD | 1468: MSTORE | 1469: PUSH2 0x0e77 | 1472: ADD | 1473: MSTORE | 1474: PUSH1 0xc0 | 1476: MLOAD | 1477: DUP2 | 1478: DUP2 | 1479: DUP2 | 1480: PUSH2 0x081e | 1483: ADD | 1484: MSTORE | 1485: DUP2 | 1486: DUP2 | 1487: PUSH2 0x1390 | 1490: ADD | 1491: MSTORE | 1492: DUP2 | 1493: DUP2 | 1494: PUSH2 0x15f9 | 1497: ADD | 1498: MSTORE | 1499: DUP2 | 1500: DUP2 | 1501: PUSH2 0x187a | 1504: ADD | 1505: MSTORE | 1506: DUP2 | 1507: DUP2 | 1508: PUSH2 0x1932 | 1511: ADD | 1512: MSTORE | 1513: DUP2 | 1514: DUP2 | 1515: PUSH2 0x26b3 | 1518: ADD | 1519: MSTORE | 1520: DUP2 | 1521: DUP2 | 1522: PUSH2 0x2f55 | 1525: ADD | 1526: MSTORE | 1527: DUP2 | 1528: DUP2 | 1529: PUSH2 0x308d | 1532: ADD | 1533: MSTORE | 1534: DUP2 | 1535: DUP2 | 1536: PUSH2 0x38d8 | 1539: ADD | 1540: MSTORE | 1541: DUP2 | 1542: DUP2 | 1543: PUSH2 0x3d1c | 1546: ADD | 1547: MSTORE | 1548: PUSH2 0x3dfd | 1551: ADD | 1552: MSTORE | 1553: PUSH1 0xe0 | 1555: MLOAD | 1556: DUP2 | 1557: DUP2 | 1558: DUP2 | 1559: PUSH2 0x1a70 | 1562: ADD | 1563: MSTORE | 1564: DUP2 | 1565: DUP2 | 1566: PUSH2 0x2818 | 1569: ADD | 1570: MSTORE | 1571: DUP2 | 1572: DUP2 | 1573: PUSH2 0x42ac | 1576: ADD | 1577: MSTORE | 1578: PUSH2 0x46c7 | 1581: ADD | 1582: MSTORE | 1583: PUSH2 0x0100 | 1586: MLOAD | 1587: DUP2 | 1588: DUP2 | 1589: DUP2 | 1590: PUSH2 0x0eb7 | 1593: ADD | 1594: MSTORE | 1595: PUSH2 0x47ff | 1598: ADD | 1599: MSTORE | 1600: PUSH2 0x0120 | 1603: MLOAD | 1604: DUP2 | 1605: DUP2 | 1606: DUP2 | 1607: PUSH2 0x133e | 1610: ADD | 1611: MSTORE | 1612: PUSH2 0x21a8 | 1615: ADD | 1616: MSTORE | 1617: PUSH2 0x0140 | 1620: MLOAD | 1621: DUP2 | 1622: DUP2 | 1623: DUP2 | 1624: PUSH2 0x0f55 | 1627: ADD | 1628: MSTORE | 1629: DUP2 | 1630: DUP2 | 1631: PUSH2 0x21e4 | 1634: ADD | 1635: MSTORE | 1636: PUSH2 0x224e | 1639: ADD | 1640: MSTORE | 1641: PUSH2 0x0160 | 1644: MLOAD | 1645: DUP2 | 1646: DUP2 | 1647: DUP2 | 1648: PUSH2 0x1064 | 1651: ADD | 1652: MSTORE | 1653: PUSH2 0x227e | 1656: ADD | 1657: MSTORE | 1658: PUSH2 0x0180 | 1661: MLOAD | 1662: DUP2 | 1663: DUP2 | 1664: DUP2 | 1665: PUSH2 0x11c6 | 1668: ADD | 1669: MSTORE | 1670: PUSH2 0x220b | 1673: ADD | 1674: MSTORE | 1675: PUSH2 0x01a0 | 1678: MLOAD | 1679: DUP2 | 1680: DUP2 | 1681: DUP2 | 1682: PUSH2 0x114e | 1685: ADD | 1686: MSTORE | 1687: PUSH2 0x22b8 | 1690: ADD | 1691: MSTORE | 1692: PUSH2 0x01c0 | 1695: MLOAD | 1696: DUP2 | 1697: DUP2 | 1698: DUP2 | 1699: PUSH2 0x0a27 | 1702: ADD | 1703: MSTORE | 1704: DUP2 | 1705: DUP2 | 1706: PUSH2 0x22f4 | 1709: ADD | 1710: MSTORE | 1711: PUSH2 0x235e | 1714: ADD | 1715: MSTORE | 1716: PUSH2 0x01e0 | 1719: MLOAD | 1720: DUP2 | 1721: DUP2 | 1722: DUP2 | 1723: PUSH2 0x0931 | 1726: ADD | 1727: MSTORE | 1728: PUSH2 0x238e | 1731: ADD | 1732: MSTORE | 1733: PUSH2 0x0200 | 1736: MLOAD | 1737: DUP2 | 1738: DUP2 | 1739: DUP2 | 1740: PUSH2 0x0fe0 | 1743: ADD | 1744: MSTORE | 1745: PUSH2 0x231b | 1748: ADD | 1749: MSTORE | 1750: PUSH2 0x0220 | 1753: MLOAD | 1754: DUP2 | 1755: DUP2 | 1756: DUP2 | 1757: PUSH2 0x07ae | 1760: ADD | 1761: MSTORE | 1762: PUSH2 0x468b | 1765: ADD | 1766: MSTORE | 1767: PUSH2 0x0240 | 1770: MLOAD | 1771: DUP2 | 1772: DUP2 | 1773: DUP2 | 1774: PUSH2 0x0cf1 | 1777: ADD | 1778: MSTORE | 1779: DUP2 | 1780: DUP2 | 1781: PUSH2 0x283e | 1784: ADD | 1785: MSTORE | 1786: DUP2 | 1787: DUP2 | 1788: PUSH2 0x2b95 | 1791: ADD | 1792: MSTORE | 1793: DUP2 | 1794: DUP2 | 1795: PUSH2 0x431c | 1798: ADD | 1799: MSTORE | 1800: PUSH2 0x46ff | 1803: ADD | 1804: MSTORE | 1805: PUSH2 0x0260 | 1808: MLOAD | 1809: DUP2 | 1810: DUP2 | 1811: DUP2 | 1812: PUSH2 0x13d0 | 1815: ADD | 1816: MSTORE | 1817: PUSH2 0x2e30 | 1820: ADD | 1821: MSTORE | 1822: PUSH2 0x0280 | 1825: MLOAD | 1826: DUP2 | 1827: DUP2 | 1828: DUP2 | 1829: PUSH2 0x06ec | 1832: ADD | 1833: MSTORE | 1834: PUSH2 0x2074 | 1837: ADD | 1838: MSTORE | 1839: PUSH2 0x02a0 | 1842: MLOAD | 1843: DUP2 | 1844: DUP2 | 1845: DUP2 | 1846: PUSH2 0x1202 | 1849: ADD | 1850: MSTORE | 1851: PUSH2 0x1ffc | 1854: ADD | 1855: MSTORE | 1856: PUSH2 0x02c0 | 1859: MLOAD | 1860: DUP2 | 1861: DUP2 | 1862: DUP2 | 1863: PUSH2 0x118a | 1866: ADD | 1867: MSTORE | 1868: PUSH2 0x1f6e | 1871: ADD | 1872: MSTORE | 1873: PUSH2 0x02e0 | 1876: MLOAD | 1877: DUP2 | 1878: DUP2 | 1879: DUP2 | 1880: PUSH2 0x0aa1 | 1883: ADD | 1884: MSTORE | 1885: DUP2 | 1886: DUP2 | 1887: PUSH2 0x3b1e | 1890: ADD | 1891: MSTORE | 1892: PUSH2 0x3e9c | 1895: ADD | 1896: MSTORE | 1897: PUSH2 0x0300 | 1900: MLOAD | 1901: DUP2 | 1902: DUP2 | 1903: DUP2 | 1904: PUSH2 0x0b1c | 1907: ADD | 1908: MSTORE | 1909: PUSH2 0x1a20 | 1912: ADD | 1913: MSTORE | 1914: PUSH2 0x0320 | 1917: MLOAD | 1918: DUP2 | 1919: PUSH2 0x0adf | 1922: ADD | 1923: MSTORE | 1924: PUSH2 0x0340 | 1927: MLOAD | 1928: DUP2 | 1929: DUP2 | 1930: DUP2 | 1931: PUSH2 0x1301 | 1934: ADD | 1935: MSTORE | 1936: DUP2 | 1937: DUP2 | 1938: PUSH2 0x1d4d | 1941: ADD | 1942: MSTORE | 1943: DUP2 | 1944: DUP2 | 1945: PUSH2 0x2875 | 1948: ADD | 1949: MSTORE | 1950: DUP2 | 1951: DUP2 | 1952: PUSH2 0x2a7e | 1955: ADD | 1956: MSTORE | 1957: PUSH2 0x42da | 1960: ADD | 1961: MSTORE | 1962: PUSH2 0x0360 | 1965: MLOAD | 1966: DUP2 | 1967: PUSH2 0x2e57 | 1970: ADD | 1971: MSTORE | 1972: PUSH2 0x0380 | 1975: MLOAD | 1976: DUP2 | 1977: DUP2 | 1978: DUP2 | 1979: PUSH2 0x17b6 | 1982: ADD | 1983: MSTORE | 1984: PUSH2 0x1c36 | 1987: ADD | 1988: MSTORE | 1989: PUSH2 0x48a7 | 1992: SWAP1 | 1993: RETURN    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
1994: JUMPDEST | 1995: PUSH1 0x20 | 1997: DUP2 | 1998: RETURNDATASIZE | 1999: PUSH1 0x20 | 2001: GT | 2002: PUSH3 0x000806 | 2006: JUMPI    ;; CometWithExtendedAssetList.constructor: IAssetListFactory(IAssetListFactoryHolder(extensionDelegate).assetListF…
2007: JUMPDEST | 2008: DUP2 | 2009: PUSH3 0x0007e6 | 2013: PUSH1 0x20 | 2015: SWAP4 | 2016: DUP4 | 2017: PUSH3 0x000a97 | 2021: JUMP    ;; CometWithExtendedAssetList.constructor: IAssetListFactory(IAssetListFactoryHolder(extensionDelegate).assetListF…
2022: JUMPDEST | 2023: DUP2 | 2024: ADD | 2025: SUB | 2026: SLT | 2027: PUSH3 0x000802 | 2031: JUMPI    ;; CometCore helper: 31_536_000
2032: PUSH3 0x0007fb | 2036: SWAP2 | 2037: POP | 2038: PUSH3 0x000abb | 2042: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
2043: JUMPDEST | 2044: DUP2 | 2045: PUSH3 0x000582 | 2049: JUMP    ;; CometWithExtendedAssetList.constructor: IAssetListFactory(IAssetListFactoryHolder(extensionDelegate).assetListF…
2050: JUMPDEST | 2051: POP | 2052: DUP1 | 2053: REVERT    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
2054: JUMPDEST | 2055: RETURNDATASIZE | 2056: SWAP2 | 2057: POP | 2058: PUSH3 0x0007d7 | 2062: JUMP    ;; CometWithExtendedAssetList.constructor: IAssetListFactory(IAssetListFactoryHolder(extensionDelegate).assetListF…
2063: JUMPDEST | 2064: PUSH1 0x40 | 2066: MLOAD | 2067: RETURNDATASIZE | 2068: PUSH1 0x00 | 2070: DUP3 | 2071: RETURNDATACOPY | 2072: RETURNDATASIZE | 2073: SWAP1 | 2074: REVERT    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
2075: JUMPDEST | 2076: DUP3 | 2077: MLOAD | 2078: DUP1 | 2079: MLOAD | 2080: PUSH1 0x01 | 2082: PUSH1 0x01 | 2084: PUSH1 0xa0 | 2086: SHL | 2087: SUB | 2088: SWAP1 | 2089: DUP2 | 2090: AND | 2091: DUP7 | 2092: MSTORE | 2093: PUSH1 0x20 | 2095: DUP3 | 2096: DUP2 | 2097: ADD | 2098: MLOAD | 2099: SWAP1 | 2100: SWAP2 | 2101: AND | 2102: DUP2 | 2103: DUP8 | 2104: ADD | 2105: MSTORE | 2106: PUSH1 0x40 | 2108: DUP1 | 2109: DUP4 | 2110: ADD | 2111: MLOAD | 2112: PUSH1 0xff | 2114: AND | 2115: SWAP1 | 2116: DUP8 | 2117: ADD | 2118: MSTORE | 2119: PUSH1 0x60 | 2121: DUP1 | 2122: DUP4 | 2123: ADD | 2124: MLOAD | 2125: PUSH1 0x01 | 2127: PUSH1 0x01 | 2129: PUSH1 0x40 | 2131: SHL | 2132: SUB | 2133: SWAP1 | 2134: DUP2 | 2135: AND | 2136: SWAP2 | 2137: DUP9 | 2138: ADD | 2139: SWAP2 | 2140: SWAP1 | 2141: SWAP2 | 2142: MSTORE | 2143: PUSH1 0x80 | 2145: DUP1 | 2146: DUP5 | 2147: ADD | 2148: MLOAD | 2149: DUP3 | 2150: AND | 2151: SWAP1 | 2152: DUP9 | 2153: ADD | 2154: MSTORE | 2155: PUSH1 0xa0 | 2157: DUP1 | 2158: DUP5 | 2159: ADD | 2160: MLOAD | 2161: SWAP1 | 2162: SWAP2 | 2163: AND | 2164: SWAP1 | 2165: DUP8 | 2166: ADD | 2167: MSTORE | 2168: PUSH1 0xc0 | 2170: SWAP2 | 2171: DUP3 | 2172: ADD | 2173: MLOAD | 2174: PUSH1 0x01 | 2176: PUSH1 0x01 | 2178: PUSH1 0x80 | 2180: SHL | 2181: SUB | 2182: AND | 2183: SWAP2 | 2184: DUP7 | 2185: ADD | 2186: SWAP2 | 2187: SWAP1 | 2188: SWAP2 | 2189: MSTORE | 2190: DUP8 | 2191: SWAP6 | 2192: POP | 2193: PUSH1 0xe0 | 2195: SWAP1 | 2196: SWAP5 | 2197: ADD | 2198: SWAP4 | 2199: SWAP1 | 2200: SWAP3 | 2201: ADD | 2202: SWAP2 | 2203: PUSH1 0x01 | 2205: ADD | 2206: PUSH3 0x00054e | 2210: JUMP    ;; CometCore helper: 31_536_000
2211: JUMPDEST | 2212: SWAP1 | 2213: SWAP2 | 2214: PUSH1 0x20 | 2216: DUP3 | 2217: RETURNDATASIZE | 2218: PUSH1 0x20 | 2220: GT | 2221: PUSH3 0x0008e4 | 2225: JUMPI    ;; CometWithExtendedAssetList.constructor: IAssetListFactoryHolder(extensionDelegate).assetListFactory()
2226: JUMPDEST | 2227: DUP2 | 2228: PUSH3 0x0008c1 | 2232: PUSH1 0x20 | 2234: SWAP4 | 2235: DUP4 | 2236: PUSH3 0x000a97 | 2240: JUMP    ;; CometWithExtendedAssetList.constructor: IAssetListFactoryHolder(extensionDelegate).assetListFactory()
2241: JUMPDEST | 2242: DUP2 | 2243: ADD | 2244: SUB | 2245: SLT | 2246: PUSH3 0x0008e1 | 2250: JUMPI    ;; CometCore helper: 31_536_000
2251: POP | 2252: PUSH3 0x0008d9 | 2256: PUSH2 0x0280 | 2259: SWAP2 | 2260: PUSH3 0x000abb | 2264: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
2265: JUMPDEST | 2266: SWAP2 | 2267: SWAP1 | 2268: PUSH3 0x00051c | 2272: JUMP    ;; CometWithExtendedAssetList.constructor: IAssetListFactoryHolder(extensionDelegate).assetListFactory()
2273: JUMPDEST | 2274: DUP1 | 2275: REVERT    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
2276: JUMPDEST | 2277: RETURNDATASIZE | 2278: SWAP2 | 2279: POP | 2280: PUSH3 0x0008b2 | 2284: JUMP    ;; CometWithExtendedAssetList.constructor: IAssetListFactoryHolder(extensionDelegate).assetListFactory()
2285: JUMPDEST | 2286: PUSH1 0x40 | 2288: MLOAD | 2289: PUSH4 0x0456c659 | 2294: PUSH1 0xe5 | 2296: SHL | 2297: DUP2 | 2298: MSTORE | 2299: PUSH1 0x04 | 2301: SWAP1 | 2302: REVERT    ;; CometWithExtendedAssetList.constructor: BadDecimals()
2303: JUMPDEST | 2304: SWAP1 | 2305: PUSH1 0x20 | 2307: DUP3 | 2308: RETURNDATASIZE | 2309: PUSH1 0x20 | 2311: GT | 2312: PUSH3 0x00093d | 2316: JUMPI    ;; CometWithExtendedAssetList.constructor: IPriceFeed(config.baseTokenPriceFeed).decimals()
2317: JUMPDEST | 2318: DUP2 | 2319: PUSH3 0x00091c | 2323: PUSH1 0x20 | 2325: SWAP4 | 2326: DUP4 | 2327: PUSH3 0x000a97 | 2331: JUMP    ;; CometWithExtendedAssetList.constructor: IPriceFeed(config.baseTokenPriceFeed).decimals()
2332: JUMPDEST | 2333: DUP2 | 2334: ADD | 2335: SUB | 2336: SLT | 2337: PUSH3 0x0008e1 | 2341: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
2342: POP | 2343: PUSH1 0xff | 2345: PUSH3 0x000935 | 2349: PUSH1 0x08 | 2351: SWAP3 | 2352: PUSH3 0x000afa | 2356: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
2357: JUMPDEST | 2358: SWAP2 | 2359: POP | 2360: PUSH3 0x000378 | 2364: JUMP    ;; CometWithExtendedAssetList.constructor: IPriceFeed(config.baseTokenPriceFeed).decimals()
2365: JUMPDEST | 2366: RETURNDATASIZE | 2367: SWAP2 | 2368: POP | 2369: PUSH3 0x00090d | 2373: JUMP    ;; CometWithExtendedAssetList.constructor: IPriceFeed(config.baseTokenPriceFeed).decimals()
2374: JUMPDEST | 2375: PUSH1 0x40 | 2377: MLOAD | 2378: PUSH4 0x6e772475 | 2383: PUSH1 0xe0 | 2385: SHL | 2386: DUP2 | 2387: MSTORE | 2388: PUSH1 0x04 | 2390: SWAP1 | 2391: REVERT    ;; CometWithExtendedAssetList.constructor: BadMinimum()
2392: JUMPDEST | 2393: PUSH1 0x40 | 2395: MLOAD | 2396: PUSH4 0xdf8153c7 | 2401: PUSH1 0xe0 | 2403: SHL | 2404: DUP2 | 2405: MSTORE | 2406: PUSH1 0x04 | 2408: SWAP1 | 2409: REVERT    ;; CometWithExtendedAssetList.constructor: TooManyAssets()
2410: JUMPDEST | 2411: PUSH1 0x40 | 2413: MLOAD | 2414: PUSH4 0x24dc918f | 2419: PUSH1 0xe1 | 2421: SHL | 2422: DUP2 | 2423: MSTORE | 2424: PUSH1 0x04 | 2426: SWAP1 | 2427: REVERT    ;; CometWithExtendedAssetList.constructor: BadDiscount()
2428: JUMPDEST | 2429: SWAP1 | 2430: PUSH1 0x20 | 2432: DUP3 | 2433: RETURNDATASIZE | 2434: PUSH1 0x20 | 2436: GT | 2437: PUSH3 0x0009b5 | 2441: JUMPI    ;; CometWithExtendedAssetList.constructor: IERC20NonStandard(config.baseToken).decimals()
2442: JUMPDEST | 2443: DUP2 | 2444: PUSH3 0x000999 | 2448: PUSH1 0x20 | 2450: SWAP4 | 2451: DUP4 | 2452: PUSH3 0x000a97 | 2456: JUMP    ;; CometWithExtendedAssetList.constructor: IERC20NonStandard(config.baseToken).decimals()
2457: JUMPDEST | 2458: DUP2 | 2459: ADD | 2460: SUB | 2461: SLT | 2462: PUSH3 0x0008e1 | 2466: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
2467: POP | 2468: PUSH3 0x0009ae | 2472: SWAP1 | 2473: PUSH3 0x000afa | 2477: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
2478: JUMPDEST | 2479: DUP3 | 2480: PUSH3 0x0002ee | 2484: JUMP    ;; CometWithExtendedAssetList.constructor: IERC20NonStandard(config.baseToken).decimals()
2485: JUMPDEST | 2486: RETURNDATASIZE | 2487: SWAP2 | 2488: POP | 2489: PUSH3 0x00098a | 2493: JUMP    ;; CometWithExtendedAssetList.constructor: IERC20NonStandard(config.baseToken).decimals()
2494: JUMPDEST | 2495: PUSH1 0xe0 | 2497: DUP8 | 2498: DUP7 | 2499: DUP7 | 2500: ADD | 2501: SUB | 2502: SLT | 2503: PUSH3 0x000a7c | 2507: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
2508: PUSH1 0x40 | 2510: MLOAD | 2511: SWAP3 | 2512: PUSH3 0x0009dc | 2516: PUSH1 0xe0 | 2518: DUP6 | 2519: PUSH3 0x000a97 | 2523: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
2524: JUMPDEST | 2525: PUSH3 0x0009e7 | 2529: DUP9 | 2530: PUSH3 0x000abb | 2534: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
2535: JUMPDEST | 2536: DUP5 | 2537: MSTORE | 2538: PUSH3 0x0009f7 | 2542: PUSH1 0x20 | 2544: DUP10 | 2545: ADD | 2546: PUSH3 0x000abb | 2550: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
2551: JUMPDEST | 2552: PUSH1 0x20 | 2554: DUP6 | 2555: ADD | 2556: MSTORE | 2557: PUSH3 0x000a0a | 2561: PUSH1 0x40 | 2563: DUP10 | 2564: ADD | 2565: PUSH3 0x000afa | 2569: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
2570: JUMPDEST | 2571: PUSH1 0x40 | 2573: DUP6 | 2574: ADD | 2575: MSTORE | 2576: PUSH3 0x000a1d | 2580: PUSH1 0x60 | 2582: DUP10 | 2583: ADD | 2584: PUSH3 0x000ad0 | 2588: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
2589: JUMPDEST | 2590: PUSH1 0x60 | 2592: DUP6 | 2593: ADD | 2594: MSTORE | 2595: PUSH3 0x000a30 | 2599: PUSH1 0x80 | 2601: DUP10 | 2602: ADD | 2603: PUSH3 0x000ad0 | 2607: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
2608: JUMPDEST | 2609: PUSH1 0x80 | 2611: DUP6 | 2612: ADD | 2613: MSTORE | 2614: PUSH3 0x000a43 | 2618: PUSH1 0xa0 | 2620: DUP10 | 2621: ADD | 2622: PUSH3 0x000ad0 | 2626: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
2627: JUMPDEST | 2628: PUSH1 0xa0 | 2630: DUP6 | 2631: ADD | 2632: MSTORE | 2633: PUSH1 0xc0 | 2635: DUP9 | 2636: ADD | 2637: MLOAD | 2638: SWAP4 | 2639: PUSH1 0x01 | 2641: PUSH1 0x01 | 2643: PUSH1 0x80 | 2645: SHL | 2646: SUB | 2647: DUP6 | 2648: AND | 2649: DUP6 | 2650: SUB | 2651: PUSH3 0x000a7c | 2655: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
2656: PUSH1 0x20 | 2658: PUSH1 0xe0 | 2660: SWAP3 | 2661: DUP3 | 2662: DUP3 | 2663: SWAP8 | 2664: PUSH1 0xc0 | 2666: DUP7 | 2667: SWAP6 | 2668: ADD | 2669: MSTORE | 2670: DUP2 | 2671: MSTORE | 2672: ADD | 2673: SWAP9 | 2674: ADD | 2675: SWAP8 | 2676: SWAP4 | 2677: POP | 2678: POP | 2679: PUSH3 0x000298 | 2683: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
2684: JUMPDEST | 2685: PUSH1 0x00 | 2687: DUP1 | 2688: REVERT    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
2689: JUMPDEST | 2690: PUSH4 0x4e487b71 | 2695: PUSH1 0xe0 | 2697: SHL | 2698: PUSH1 0x00 | 2700: MSTORE | 2701: PUSH1 0x41 | 2703: PUSH1 0x04 | 2705: MSTORE | 2706: PUSH1 0x24 | 2708: PUSH1 0x00 | 2710: REVERT    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
2711: JUMPDEST | 2712: PUSH1 0x1f | 2714: SWAP1 | 2715: SWAP2 | 2716: ADD | 2717: PUSH1 0x1f | 2719: NOT | 2720: AND | 2721: DUP2 | 2722: ADD | 2723: SWAP1 | 2724: PUSH1 0x01 | 2726: PUSH1 0x01 | 2728: PUSH1 0x40 | 2730: SHL | 2731: SUB | 2732: DUP3 | 2733: GT | 2734: SWAP1 | 2735: DUP3 | 2736: LT | 2737: OR | 2738: PUSH3 0x000a81 | 2742: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
2743: PUSH1 0x40 | 2745: MSTORE | 2746: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
2747: JUMPDEST | 2748: MLOAD | 2749: SWAP1 | 2750: PUSH1 0x01 | 2752: PUSH1 0x01 | 2754: PUSH1 0xa0 | 2756: SHL | 2757: SUB | 2758: DUP3 | 2759: AND | 2760: DUP3 | 2761: SUB | 2762: PUSH3 0x000a7c | 2766: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
2767: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
2768: JUMPDEST | 2769: MLOAD | 2770: SWAP1 | 2771: PUSH1 0x01 | 2773: PUSH1 0x01 | 2775: PUSH1 0x40 | 2777: SHL | 2778: SUB | 2779: DUP3 | 2780: AND | 2781: DUP3 | 2782: SUB | 2783: PUSH3 0x000a7c | 2787: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
2788: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
2789: JUMPDEST | 2790: MLOAD | 2791: SWAP1 | 2792: PUSH1 0x01 | 2794: PUSH1 0x01 | 2796: PUSH1 0x68 | 2798: SHL | 2799: SUB | 2800: DUP3 | 2801: AND | 2802: DUP3 | 2803: SUB | 2804: PUSH3 0x000a7c | 2808: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
2809: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
2810: JUMPDEST | 2811: MLOAD | 2812: SWAP1 | 2813: PUSH1 0xff | 2815: DUP3 | 2816: AND | 2817: DUP3 | 2818: SUB | 2819: PUSH3 0x000a7c | 2823: JUMPI    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
2824: JUMP    ;; CometWithExtendedAssetList helper: contract CometWithExtendedAssetList is CometMainInterface { /** General…
2825: INVALID
2826: PUSH1 0x80 | 2828: PUSH1 0x40 | 2830: MSTORE | 2831: PUSH1 0x04 | 2833: CALLDATASIZE | 2834: LT | 2835: ISZERO | 2836: PUSH2 0x0018 | 2839: JUMPI
2840: JUMPDEST | 2841: PUSH2 0x0016 | 2844: PUSH2 0x47f2 | 2847: JUMP
2848: JUMPDEST | 2849: STOP
2850: JUMPDEST | 2851: PUSH1 0x00 | 2853: CALLDATALOAD | 2854: PUSH1 0xe0 | 2856: SHR | 2857: DUP1 | 2858: PUSH4 0x042e02cf | 2863: EQ | 2864: PUSH2 0x0568 | 2867: JUMPI
2868: DUP1 | 2869: PUSH4 0x0902f1ac | 2874: EQ | 2875: PUSH2 0x055f | 2878: JUMPI
2879: DUP1 | 2880: PUSH4 0x0bc47ad1 | 2885: EQ | 2886: PUSH2 0x0556 | 2889: JUMPI
2890: DUP1 | 2891: PUSH4 0x0c340a24 | 2896: EQ | 2897: PUSH2 0x054d | 2900: JUMPI
2901: DUP1 | 2902: PUSH4 0x18160ddd | 2907: EQ | 2908: PUSH2 0x0544 | 2911: JUMPI
2912: DUP1 | 2913: PUSH4 0x189bb2f1 | 2918: EQ | 2919: PUSH2 0x053b | 2922: JUMPI
2923: DUP1 | 2924: PUSH4 0x1c9f7fb9 | 2929: EQ | 2930: PUSH2 0x0532 | 2933: JUMPI
2934: DUP1 | 2935: PUSH4 0x1f5954bd | 2940: EQ | 2941: PUSH2 0x0529 | 2944: JUMPI
2945: DUP1 | 2946: PUSH4 0x23b872dd | 2951: EQ | 2952: PUSH2 0x0520 | 2955: JUMPI
2956: DUP1 | 2957: PUSH4 0x24a3d622 | 2962: EQ | 2963: PUSH2 0x0517 | 2966: JUMPI
2967: DUP1 | 2968: PUSH4 0x26441318 | 2973: EQ | 2974: PUSH2 0x050e | 2977: JUMPI
2978: DUP1 | 2979: PUSH4 0x2a48cf12 | 2984: EQ | 2985: PUSH2 0x0505 | 2988: JUMPI
2989: DUP1 | 2990: PUSH4 0x2b92a07d | 2995: EQ | 2996: PUSH2 0x04fc | 2999: JUMPI
3000: DUP1 | 3001: PUSH4 0x2d05670b | 3006: EQ | 3007: PUSH2 0x04f3 | 3010: JUMPI
3011: DUP1 | 3012: PUSH4 0x2e04b8e7 | 3017: EQ | 3018: PUSH2 0x04ea | 3021: JUMPI
3022: DUP1 | 3023: PUSH4 0x300e6beb | 3028: EQ | 3029: PUSH2 0x04e1 | 3032: JUMPI
3033: DUP1 | 3034: PUSH4 0x313ce567 | 3039: EQ | 3040: PUSH2 0x04d8 | 3043: JUMPI
3044: DUP1 | 3045: PUSH4 0x32176c49 | 3050: EQ | 3051: PUSH2 0x04cf | 3054: JUMPI
3055: DUP1 | 3056: PUSH4 0x374c49b4 | 3061: EQ | 3062: PUSH2 0x04c6 | 3065: JUMPI
3066: DUP1 | 3067: PUSH4 0x38aa813f | 3072: EQ | 3073: PUSH2 0x04bd | 3076: JUMPI
3077: DUP1 | 3078: PUSH4 0x3b3bec2e | 3083: EQ | 3084: PUSH2 0x04b4 | 3087: JUMPI
3088: DUP1 | 3089: PUSH4 0x41976e09 | 3094: EQ | 3095: PUSH2 0x04ab | 3098: JUMPI
3099: DUP1 | 3100: PUSH4 0x4232cd63 | 3105: EQ | 3106: PUSH2 0x04a2 | 3109: JUMPI
3110: DUP1 | 3111: PUSH4 0x439e2e45 | 3116: EQ | 3117: PUSH2 0x0499 | 3120: JUMPI
3121: DUP1 | 3122: PUSH4 0x44c1e5eb | 3127: EQ | 3128: PUSH2 0x0490 | 3131: JUMPI
3132: DUP1 | 3133: PUSH4 0x44c35d07 | 3138: EQ | 3139: PUSH2 0x0487 | 3142: JUMPI
3143: DUP1 | 3144: PUSH4 0x44ff241d | 3149: EQ | 3150: PUSH2 0x047e | 3153: JUMPI
3154: DUP1 | 3155: PUSH4 0x59e017bd | 3160: EQ | 3161: PUSH2 0x0475 | 3164: JUMPI
3165: DUP1 | 3166: PUSH4 0x5a94b8d1 | 3171: EQ | 3172: PUSH2 0x046c | 3175: JUMPI
3176: DUP1 | 3177: PUSH4 0x67800b5f | 3182: EQ | 3183: PUSH2 0x0463 | 3186: JUMPI
3187: DUP1 | 3188: PUSH4 0x70a08231 | 3193: EQ | 3194: PUSH2 0x045a | 3197: JUMPI
3198: DUP1 | 3199: PUSH4 0x7914acc7 | 3204: EQ | 3205: PUSH2 0x0451 | 3208: JUMPI
3209: DUP1 | 3210: PUSH4 0x7ac88ed1 | 3215: EQ | 3216: PUSH2 0x0448 | 3219: JUMPI
3220: DUP1 | 3221: PUSH4 0x7eb71131 | 3226: EQ | 3227: PUSH2 0x043f | 3230: JUMPI
3231: DUP1 | 3232: PUSH4 0x804de71f | 3237: EQ | 3238: PUSH2 0x0436 | 3241: JUMPI
3242: DUP1 | 3243: PUSH4 0x8285ef40 | 3248: EQ | 3249: PUSH2 0x042d | 3252: JUMPI
3253: DUP1 | 3254: PUSH4 0x8d5d814c | 3259: EQ | 3260: PUSH2 0x0424 | 3263: JUMPI
3264: DUP1 | 3265: PUSH4 0x90323177 | 3270: EQ | 3271: PUSH2 0x041b | 3274: JUMPI
3275: DUP1 | 3276: PUSH4 0x9241a561 | 3281: EQ | 3282: PUSH2 0x0412 | 3285: JUMPI
3286: DUP1 | 3287: PUSH4 0x9364e18a | 3292: EQ | 3293: PUSH2 0x0409 | 3296: JUMPI
3297: DUP1 | 3298: PUSH4 0x94920cca | 3303: EQ | 3304: PUSH2 0x0400 | 3307: JUMPI
3308: DUP1 | 3309: PUSH4 0x9ea99a5a | 3314: EQ | 3315: PUSH2 0x03f7 | 3318: JUMPI
3319: DUP1 | 3320: PUSH4 0x9fa83b5a | 3325: EQ | 3326: PUSH2 0x03ee | 3329: JUMPI
3330: DUP1 | 3331: PUSH4 0x9ff567f8 | 3336: EQ | 3337: PUSH2 0x03e5 | 3340: JUMPI
3341: DUP1 | 3342: PUSH4 0xa1654379 | 3347: EQ | 3348: PUSH2 0x03dc | 3351: JUMPI
3352: DUP1 | 3353: PUSH4 0xa1a1ef43 | 3358: EQ | 3359: PUSH2 0x03d3 | 3362: JUMPI
3363: DUP1 | 3364: PUSH4 0xa46fe83b | 3369: EQ | 3370: PUSH2 0x03ca | 3373: JUMPI
3374: DUP1 | 3375: PUSH4 0xa5b4ff79 | 3380: EQ | 3381: PUSH2 0x03c1 | 3384: JUMPI
3385: DUP1 | 3386: PUSH4 0xa9059cbb | 3391: EQ | 3392: PUSH2 0x03b8 | 3395: JUMPI
3396: DUP1 | 3397: PUSH4 0xaba7f15e | 3402: EQ | 3403: PUSH2 0x03af | 3406: JUMPI
3407: DUP1 | 3408: PUSH4 0xad14777c | 3413: EQ | 3414: PUSH2 0x03a6 | 3417: JUMPI
3418: DUP1 | 3419: PUSH4 0xbfe69c8d | 3424: EQ | 3425: PUSH2 0x039d | 3428: JUMPI
3429: DUP1 | 3430: PUSH4 0xc1ee2c18 | 3435: EQ | 3436: PUSH2 0x0394 | 3439: JUMPI
3440: DUP1 | 3441: PUSH4 0xc3b35a7e | 3446: EQ | 3447: PUSH2 0x038b | 3450: JUMPI
3451: DUP1 | 3452: PUSH4 0xc3cecfd2 | 3457: EQ | 3458: PUSH2 0x0382 | 3461: JUMPI
3462: DUP1 | 3463: PUSH4 0xc55dae63 | 3468: EQ | 3469: PUSH2 0x0379 | 3472: JUMPI
3473: DUP1 | 3474: PUSH4 0xc5fa15cf | 3479: EQ | 3480: PUSH2 0x0370 | 3483: JUMPI
3484: DUP1 | 3485: PUSH4 0xc8c7fe6b | 3490: EQ | 3491: PUSH2 0x0367 | 3494: JUMPI
3495: DUP1 | 3496: PUSH4 0xcde68041 | 3501: EQ | 3502: PUSH2 0x035e | 3505: JUMPI
3506: DUP1 | 3507: PUSH4 0xd8e5f611 | 3512: EQ | 3513: PUSH2 0x0355 | 3516: JUMPI
3517: DUP1 | 3518: PUSH4 0xd955759d | 3523: EQ | 3524: PUSH2 0x034c | 3527: JUMPI
3528: DUP1 | 3529: PUSH4 0xdc4abafd | 3534: EQ | 3535: PUSH2 0x0343 | 3538: JUMPI
3539: DUP1 | 3540: PUSH4 0xe372f03a | 3545: EQ | 3546: PUSH2 0x033a | 3549: JUMPI
3550: DUP1 | 3551: PUSH4 0xe478795d | 3556: EQ | 3557: PUSH2 0x0331 | 3560: JUMPI
3561: DUP1 | 3562: PUSH4 0xe4e6e779 | 3567: EQ | 3568: PUSH2 0x0328 | 3571: JUMPI
3572: DUP1 | 3573: PUSH4 0xe7dad6bd | 3578: EQ | 3579: PUSH2 0x031f | 3582: JUMPI
3583: DUP1 | 3584: PUSH4 0xf2b9fdb8 | 3589: EQ | 3590: PUSH2 0x0316 | 3593: JUMPI
3594: PUSH4 0xf3fef3a3 | 3599: SUB | 3600: PUSH2 0x000e | 3603: JUMPI
3604: PUSH2 0x0311 | 3607: PUSH2 0x1ad4 | 3610: JUMP
3611: JUMPDEST | 3612: PUSH2 0x000e | 3615: JUMP
3616: JUMPDEST | 3617: POP | 3618: PUSH2 0x0311 | 3621: PUSH2 0x1a9f | 3624: JUMP
3625: JUMPDEST | 3626: POP | 3627: PUSH2 0x0311 | 3630: PUSH2 0x1a59 | 3633: JUMP
3634: JUMPDEST | 3635: POP | 3636: PUSH2 0x0311 | 3639: PUSH2 0x18d0 | 3642: JUMP
3643: JUMPDEST | 3644: POP | 3645: PUSH2 0x0311 | 3648: PUSH2 0x17e5 | 3651: JUMP
3652: JUMPDEST | 3653: POP | 3654: PUSH2 0x0311 | 3657: PUSH2 0x179f | 3660: JUMP
3661: JUMPDEST | 3662: POP | 3663: PUSH2 0x0311 | 3666: PUSH2 0x172c | 3669: JUMP
3670: JUMPDEST | 3671: POP | 3672: PUSH2 0x0311 | 3675: PUSH2 0x170d | 3678: JUMP
3679: JUMPDEST | 3680: POP | 3681: PUSH2 0x0311 | 3684: PUSH2 0x16e6 | 3687: JUMP
3688: JUMPDEST | 3689: POP | 3690: PUSH2 0x0311 | 3693: PUSH2 0x16ca | 3696: JUMP
3697: JUMPDEST | 3698: POP | 3699: PUSH2 0x0311 | 3702: PUSH2 0x16a1 | 3705: JUMP
3706: JUMPDEST | 3707: POP | 3708: PUSH2 0x0311 | 3711: PUSH2 0x1628 | 3714: JUMP
3715: JUMPDEST | 3716: POP | 3717: PUSH2 0x0311 | 3720: PUSH2 0x15e2 | 3723: JUMP
3724: JUMPDEST | 3725: POP | 3726: PUSH2 0x0311 | 3729: PUSH2 0x157d | 3732: JUMP
3733: JUMPDEST | 3734: POP | 3735: PUSH2 0x0311 | 3738: PUSH2 0x1559 | 3741: JUMP
3742: JUMPDEST | 3743: POP | 3744: PUSH2 0x0311 | 3747: PUSH2 0x1533 | 3750: JUMP
3751: JUMPDEST | 3752: POP | 3753: PUSH2 0x0311 | 3756: PUSH2 0x1498 | 3759: JUMP
3760: JUMPDEST | 3761: POP | 3762: PUSH2 0x0311 | 3765: PUSH2 0x13f3 | 3768: JUMP
3769: JUMPDEST | 3770: POP | 3771: PUSH2 0x0311 | 3774: PUSH2 0x13b7 | 3777: JUMP
3778: JUMPDEST | 3779: POP | 3780: PUSH2 0x0311 | 3783: PUSH2 0x1361 | 3786: JUMP
3787: JUMPDEST | 3788: POP | 3789: PUSH2 0x0311 | 3792: PUSH2 0x1325 | 3795: JUMP
3796: JUMPDEST | 3797: POP | 3798: PUSH2 0x0311 | 3801: PUSH2 0x12e6 | 3804: JUMP
3805: JUMPDEST | 3806: POP | 3807: PUSH2 0x0311 | 3810: PUSH2 0x12bf | 3813: JUMP
3814: JUMPDEST | 3815: POP | 3816: PUSH2 0x0311 | 3819: PUSH2 0x127e | 3822: JUMP
3823: JUMPDEST | 3824: POP | 3825: PUSH2 0x0311 | 3828: PUSH2 0x1256 | 3831: JUMP
3832: JUMPDEST | 3833: POP | 3834: PUSH2 0x0311 | 3837: PUSH2 0x1225 | 3840: JUMP
3841: JUMPDEST | 3842: POP | 3843: PUSH2 0x0311 | 3846: PUSH2 0x11e9 | 3849: JUMP
3850: JUMPDEST | 3851: POP | 3852: PUSH2 0x0311 | 3855: PUSH2 0x11ad | 3858: JUMP
3859: JUMPDEST | 3860: POP | 3861: PUSH2 0x0311 | 3864: PUSH2 0x1171 | 3867: JUMP
3868: JUMPDEST | 3869: POP | 3870: PUSH2 0x0311 | 3873: PUSH2 0x1135 | 3876: JUMP
3877: JUMPDEST | 3878: POP | 3879: PUSH2 0x0311 | 3882: PUSH2 0x110f | 3885: JUMP
3886: JUMPDEST | 3887: POP | 3888: PUSH2 0x0311 | 3891: PUSH2 0x10e8 | 3894: JUMP
3895: JUMPDEST | 3896: POP | 3897: PUSH2 0x0311 | 3900: PUSH2 0x1087 | 3903: JUMP
3904: JUMPDEST | 3905: POP | 3906: PUSH2 0x0311 | 3909: PUSH2 0x104b | 3912: JUMP
3913: JUMPDEST | 3914: POP | 3915: PUSH2 0x0311 | 3918: PUSH2 0x102f | 3921: JUMP
3922: JUMPDEST | 3923: POP | 3924: PUSH2 0x0311 | 3927: PUSH2 0x1003 | 3930: JUMP
3931: JUMPDEST | 3932: POP | 3933: PUSH2 0x0311 | 3936: PUSH2 0x0fc7 | 3939: JUMP
3940: JUMPDEST | 3941: POP | 3942: PUSH2 0x0311 | 3945: PUSH2 0x0f9f | 3948: JUMP
3949: JUMPDEST | 3950: POP | 3951: PUSH2 0x0311 | 3954: PUSH2 0x0f78 | 3957: JUMP
3958: JUMPDEST | 3959: POP | 3960: PUSH2 0x0311 | 3963: PUSH2 0x0f3c | 3966: JUMP
3967: JUMPDEST | 3968: POP | 3969: PUSH2 0x0311 | 3972: PUSH2 0x0ee6 | 3975: JUMP
3976: JUMPDEST | 3977: POP | 3978: PUSH2 0x0311 | 3981: PUSH2 0x0ea0 | 3984: JUMP
3985: JUMPDEST | 3986: POP | 3987: PUSH2 0x0311 | 3990: PUSH2 0x0d21 | 3993: JUMP
3994: JUMPDEST | 3995: POP | 3996: PUSH2 0x0311 | 3999: PUSH2 0x0cd8 | 4002: JUMP
4003: JUMPDEST | 4004: POP | 4005: PUSH2 0x0311 | 4008: PUSH2 0x0cb4 | 4011: JUMP
4012: JUMPDEST | 4013: POP | 4014: PUSH2 0x0311 | 4017: PUSH2 0x0c90 | 4020: JUMP
4021: JUMPDEST | 4022: POP | 4023: PUSH2 0x0311 | 4026: PUSH2 0x0c68 | 4029: JUMP
4030: JUMPDEST | 4031: POP | 4032: PUSH2 0x0311 | 4035: PUSH2 0x0c33 | 4038: JUMP
4039: JUMPDEST | 4040: POP | 4041: PUSH2 0x0311 | 4044: PUSH2 0x0b67 | 4047: JUMP
4048: JUMPDEST | 4049: POP | 4050: PUSH2 0x0311 | 4053: PUSH2 0x0b3f | 4056: JUMP
4057: JUMPDEST | 4058: POP | 4059: PUSH2 0x0311 | 4062: PUSH2 0x0b03 | 4065: JUMP
4066: JUMPDEST | 4067: POP | 4068: PUSH2 0x0311 | 4071: PUSH2 0x0ac4 | 4074: JUMP
4075: JUMPDEST | 4076: POP | 4077: PUSH2 0x0311 | 4080: PUSH2 0x0a88 | 4083: JUMP
4084: JUMPDEST | 4085: POP | 4086: PUSH2 0x0311 | 4089: PUSH2 0x0a4a | 4092: JUMP
4093: JUMPDEST | 4094: POP | 4095: PUSH2 0x0311 | 4098: PUSH2 0x0a0e | 4101: JUMP
4102: JUMPDEST | 4103: POP | 4104: PUSH2 0x0311 | 4107: PUSH2 0x09b9 | 4110: JUMP
4111: JUMPDEST | 4112: POP | 4113: PUSH2 0x0311 | 4116: PUSH2 0x0918 | 4119: JUMP
4120: JUMPDEST | 4121: POP | 4122: PUSH2 0x0311 | 4125: PUSH2 0x08de | 4128: JUMP
4129: JUMPDEST | 4130: POP | 4131: PUSH2 0x0311 | 4134: PUSH2 0x0861 | 4137: JUMP
4138: JUMPDEST | 4139: POP | 4140: PUSH2 0x0311 | 4143: PUSH2 0x07fe | 4146: JUMP
4147: JUMPDEST | 4148: POP | 4149: PUSH2 0x0311 | 4152: PUSH2 0x0795 | 4155: JUMP
4156: JUMPDEST | 4157: POP | 4158: PUSH2 0x0311 | 4161: PUSH2 0x070f | 4164: JUMP
4165: JUMPDEST | 4166: POP | 4167: PUSH2 0x0311 | 4170: PUSH2 0x06d3 | 4173: JUMP
4174: JUMPDEST | 4175: POP | 4176: PUSH2 0x0311 | 4179: PUSH2 0x0667 | 4182: JUMP
4183: JUMPDEST | 4184: POP | 4185: PUSH2 0x0311 | 4188: PUSH2 0x0621 | 4191: JUMP
4192: JUMPDEST | 4193: POP | 4194: PUSH2 0x0311 | 4197: PUSH2 0x05e8 | 4200: JUMP
4201: JUMPDEST | 4202: POP | 4203: PUSH2 0x0311 | 4206: PUSH2 0x05c4 | 4209: JUMP
4210: JUMPDEST | 4211: POP | 4212: PUSH2 0x0311 | 4215: PUSH2 0x0587 | 4218: JUMP
4219: JUMPDEST | 4220: PUSH1 0x01 | 4222: PUSH1 0x01 | 4224: PUSH1 0xa0 | 4226: SHL | 4227: SUB | 4228: DUP2 | 4229: AND | 4230: SUB | 4231: PUSH2 0x0582 | 4234: JUMPI
4235: JUMP
4236: JUMPDEST | 4237: PUSH1 0x00 | 4239: DUP1 | 4240: REVERT
4241: JUMPDEST | 4242: POP | 4243: CALLVALUE | 4244: PUSH2 0x0582 | 4247: JUMPI
4248: PUSH1 0x20 | 4250: CALLDATASIZE | 4251: PUSH1 0x03 | 4253: NOT | 4254: ADD | 4255: SLT | 4256: PUSH2 0x0582 | 4259: JUMPI
4260: PUSH1 0x20 | 4262: PUSH2 0x05af | 4265: PUSH1 0x04 | 4267: CALLDATALOAD | 4268: PUSH2 0x05aa | 4271: DUP2 | 4272: PUSH2 0x0571 | 4275: JUMP
4276: JUMPDEST | 4277: PUSH2 0x2a35 | 4280: JUMP
4281: JUMPDEST | 4282: PUSH1 0x40 | 4284: MLOAD | 4285: SWAP1 | 4286: ISZERO | 4287: ISZERO | 4288: DUP2 | 4289: MSTORE | 4290: RETURN
4291: JUMPDEST | 4292: PUSH1 0x00 | 4294: SWAP2 | 4295: SUB | 4296: SLT | 4297: PUSH2 0x0582 | 4300: JUMPI
4301: JUMP
4302: JUMPDEST | 4303: POP | 4304: CALLVALUE | 4305: PUSH2 0x0582 | 4308: JUMPI
4309: PUSH1 0x00 | 4311: CALLDATASIZE | 4312: PUSH1 0x03 | 4314: NOT | 4315: ADD | 4316: SLT | 4317: PUSH2 0x0582 | 4320: JUMPI
4321: PUSH1 0x20 | 4323: PUSH2 0x05e0 | 4326: PUSH2 0x2661 | 4329: JUMP
4330: JUMPDEST | 4331: PUSH1 0x40 | 4333: MLOAD | 4334: SWAP1 | 4335: DUP2 | 4336: MSTORE | 4337: RETURN
4338: JUMPDEST | 4339: POP | 4340: CALLVALUE | 4341: PUSH2 0x0582 | 4344: JUMPI
4345: PUSH1 0x00 | 4347: CALLDATASIZE | 4348: PUSH1 0x03 | 4350: NOT | 4351: ADD | 4352: SLT | 4353: PUSH2 0x0582 | 4356: JUMPI
4357: PUSH1 0x20 | 4359: PUSH1 0x01 | 4361: DUP1 | 4362: SLOAD | 4363: PUSH1 0xf8 | 4365: SHR | 4366: AND | 4367: ISZERO | 4368: ISZERO | 4369: PUSH1 0x40 | 4371: MLOAD | 4372: SWAP1 | 4373: DUP2 | 4374: MSTORE | 4375: RETURN
4376: JUMPDEST | 4377: PUSH1 0x01 | 4379: PUSH1 0x01 | 4381: PUSH1 0xa0 | 4383: SHL | 4384: SUB | 4385: SWAP1 | 4386: SWAP2 | 4387: AND | 4388: DUP2 | 4389: MSTORE | 4390: PUSH1 0x20 | 4392: ADD | 4393: SWAP1 | 4394: JUMP
4395: JUMPDEST | 4396: POP | 4397: CALLVALUE | 4398: PUSH2 0x0582 | 4401: JUMPI
4402: PUSH1 0x00 | 4404: CALLDATASIZE | 4405: PUSH1 0x03 | 4407: NOT | 4408: ADD | 4409: SLT | 4410: PUSH2 0x0582 | 4413: JUMPI
4414: PUSH1 0x40 | 4416: MLOAD | 4417: PUSH32 0x0000000000000000000000000000000000000000000000000000000000000000 | 4450: PUSH1 0x01 | 4452: PUSH1 0x01 | 4454: PUSH1 0xa0 | 4456: SHL | 4457: SUB | 4458: AND | 4459: DUP2 | 4460: MSTORE | 4461: PUSH1 0x20 | 4463: SWAP1 | 4464: RETURN
4465: JUMPDEST | 4466: POP | 4467: CALLVALUE | 4468: PUSH2 0x0582 | 4471: JUMPI
4472: PUSH1 0x00 | 4474: CALLDATASIZE | 4475: PUSH1 0x03 | 4477: NOT | 4478: ADD | 4479: SLT | 4480: PUSH2 0x0582 | 4483: JUMPI
4484: PUSH1 0x20 | 4486: PUSH7 0x038d7ea4c68000 | 4494: PUSH2 0x06ca | 4497: PUSH2 0x068e | 4500: PUSH2 0x1dbe | 4503: JUMP
4504: JUMPDEST | 4505: PUSH2 0x06b1 | 4508: PUSH1 0x01 | 4510: SLOAD | 4511: SWAP2 | 4512: PUSH2 0x06ab | 4515: PUSH5 0xffffffffff | 4521: SWAP2 | 4522: DUP3 | 4523: DUP6 | 4524: PUSH1 0xd0 | 4526: SHR | 4527: AND | 4528: SWAP1 | 4529: PUSH2 0x1e49 | 4532: JUMP
4533: JUMPDEST | 4534: AND | 4535: PUSH2 0x20fd | 4538: JUMP
4539: JUMPDEST | 4540: POP | 4541: PUSH1 0x01 | 4543: PUSH1 0x01 | 4545: PUSH1 0x40 | 4547: SHL | 4548: SUB | 4549: AND | 4550: SWAP1 | 4551: PUSH1 0x01 | 4553: PUSH1 0x01 | 4555: PUSH1 0x68 | 4557: SHL | 4558: SUB | 4559: AND | 4560: PUSH2 0x1e77 | 4563: JUMP
4564: JUMPDEST | 4565: DIV | 4566: PUSH1 0x40 | 4568: MLOAD | 4569: SWAP1 | 4570: DUP2 | 4571: MSTORE | 4572: RETURN
4573: JUMPDEST | 4574: POP | 4575: CALLVALUE | 4576: PUSH2 0x0582 | 4579: JUMPI
4580: PUSH1 0x00 | 4582: CALLDATASIZE | 4583: PUSH1 0x03 | 4585: NOT | 4586: ADD | 4587: SLT | 4588: PUSH2 0x0582 | 4591: JUMPI
4592: PUSH1 0x20 | 4594: PUSH1 0x40 | 4596: MLOAD | 4597: PUSH32 0x0000000000000000000000000000000000000000000000000000000000000000 | 4630: DUP2 | 4631: MSTORE | 4632: RETURN
4633: JUMPDEST | 4634: POP | 4635: CALLVALUE | 4636: PUSH2 0x0582 | 4639: JUMPI
4640: PUSH1 0x00 | 4642: DUP1 | 4643: PUSH1 0x03 | 4645: NOT | 4646: CALLDATASIZE | 4647: ADD | 4648: SLT | 4649: PUSH2 0x0792 | 4652: JUMPI
4653: PUSH1 0x01 | 4655: SLOAD | 4656: PUSH5 0xffffffffff | 4662: DUP2 | 4663: PUSH1 0xd0 | 4665: SHR | 4666: AND | 4667: PUSH2 0x0781 | 4670: JUMPI
4671: PUSH5 0xffffffffff | 4677: PUSH1 0xd0 | 4679: SHL | 4680: PUSH2 0x0745 | 4683: PUSH2 0x1dbe | 4686: JUMP
4687: JUMPDEST | 4688: PUSH5 0xffffffffff | 4694: PUSH1 0xd0 | 4696: SHL | 4697: NOT | 4698: SWAP1 | 4699: SWAP3 | 4700: AND | 4701: PUSH1 0xd0 | 4703: SWAP3 | 4704: SWAP1 | 4705: SWAP3 | 4706: SHL | 4707: AND | 4708: OR | 4709: PUSH1 0x01 | 4711: SSTORE | 4712: DUP1 | 4713: SLOAD | 4714: PUSH1 0x01 | 4716: PUSH1 0x01 | 4718: PUSH1 0x80 | 4720: SHL | 4721: SUB | 4722: NOT | 4723: AND | 4724: PUSH15 0x038d7ea4c6800000038d7ea4c68000 | 4740: OR | 4741: DUP2 | 4742: SSTORE | 4743: PUSH1 0x40 | 4745: MLOAD | 4746: RETURN
4747: JUMPDEST | 4748: PUSH1 0x40 | 4750: MLOAD | 4751: PUSH3 0xdc149f | 4755: PUSH1 0xe4 | 4757: SHL | 4758: DUP2 | 4759: MSTORE | 4760: PUSH1 0x04 | 4762: SWAP1 | 4763: REVERT
4764: JUMPDEST | 4765: DUP1 | 4766: REVERT
4767: JUMPDEST | 4768: POP | 4769: CALLVALUE | 4770: PUSH2 0x0582 | 4773: JUMPI
4774: PUSH1 0x00 | 4776: CALLDATASIZE | 4777: PUSH1 0x03 | 4779: NOT | 4780: ADD | 4781: SLT | 4782: PUSH2 0x0582 | 4785: JUMPI
4786: PUSH1 0x20 | 4788: PUSH1 0x40 | 4790: MLOAD | 4791: PUSH32 0x0000000000000000000000000000000000000000000000000000000000000000 | 4824: DUP2 | 4825: MSTORE | 4826: RETURN
4827: JUMPDEST | 4828: SWAP1 | 4829: DUP2 | 4830: PUSH1 0x60 | 4832: SWAP2 | 4833: SUB | 4834: SLT | 4835: PUSH2 0x0582 | 4838: JUMPI
4839: DUP1 | 4840: CALLDATALOAD | 4841: PUSH2 0x07e7 | 4844: DUP2 | 4845: PUSH2 0x0571 | 4848: JUMP
4849: JUMPDEST | 4850: SWAP2 | 4851: PUSH1 0x40 | 4853: PUSH1 0x20 | 4855: DUP4 | 4856: ADD | 4857: CALLDATALOAD | 4858: PUSH2 0x07f8 | 4861: DUP2 | 4862: PUSH2 0x0571 | 4865: JUMP
4866: JUMPDEST | 4867: SWAP3 | 4868: ADD | 4869: CALLDATALOAD | 4870: SWAP1 | 4871: JUMP
4872: JUMPDEST | 4873: POP | 4874: CALLVALUE | 4875: PUSH2 0x0582 | 4878: JUMPI
4879: PUSH2 0x0844 | 4882: PUSH2 0x0812 | 4885: CALLDATASIZE | 4886: PUSH1 0x04 | 4888: PUSH2 0x07d1 | 4891: JUMP
4892: JUMPDEST | 4893: SWAP2 | 4894: SWAP1 | 4895: PUSH2 0x081c | 4898: PUSH2 0x2fd5 | 4901: JUMP
4902: JUMPDEST | 4903: PUSH32 0x0000000000000000000000000000000000000000000000000000000000000000 | 4936: SWAP2 | 4937: CALLER | 4938: PUSH2 0x38a0 | 4941: JUMP
4942: JUMPDEST | 4943: PUSH1 0x00 | 4945: PUSH1 0x00 | 4947: DUP1 | 4948: MLOAD | 4949: PUSH1 0x20 | 4951: PUSH2 0x4852 | 4954: DUP4 | 4955: CODECOPY | 4956: DUP2 | 4957: MLOAD | 4958: SWAP2 | 4959: MSTORE | 4960: SSTORE | 4961: PUSH1 0x20 | 4963: PUSH1 0x40 | 4965: MLOAD | 4966: PUSH1 0x01 | 4968: DUP2 | 4969: MSTORE | 4970: RETURN
4971: JUMPDEST | 4972: POP | 4973: CALLVALUE | 4974: PUSH2 0x0582 | 4977: JUMPI
4978: PUSH1 0x00 | 4980: CALLDATASIZE | 4981: PUSH1 0x03 | 4983: NOT | 4984: ADD | 4985: SLT | 4986: PUSH2 0x0582 | 4989: JUMPI
4990: PUSH1 0x40 | 4992: MLOAD | 4993: PUSH32 0x0000000000000000000000000000000000000000000000000000000000000000 | 5026: PUSH1 0x01 | 5028: PUSH1 0x01 | 5030: PUSH1 0xa0 | 5032: SHL | 5033: SUB | 5034: AND | 5035: DUP2 | 5036: MSTORE | 5037: PUSH1 0x20 | 5039: SWAP1 | 5040: RETURN
5041: JUMPDEST | 5042: SWAP2 | 5043: SWAP1 | 5044: DUP3 | 5045: PUSH1 0x80 | 5047: SWAP2 | 5048: SUB | 5049: SLT | 5050: PUSH2 0x0582 | 5053: JUMPI
5054: DUP2 | 5055: CALLDATALOAD | 5056: PUSH2 0x08be | 5059: DUP2 | 5060: PUSH2 0x0571 | 5063: JUMP
5064: JUMPDEST | 5065: SWAP2 | 5066: PUSH1 0x20 | 5068: DUP2 | 5069: ADD | 5070: CALLDATALOAD | 5071: PUSH2 0x08cd | 5074: DUP2 | 5075: PUSH2 0x0571 | 5078: JUMP
5079: JUMPDEST | 5080: SWAP2 | 5081: PUSH1 0x60 | 5083: PUSH1 0x40 | 5085: DUP4 | 5086: ADD | 5087: CALLDATALOAD | 5088: PUSH2 0x07f8 | 5091: DUP2 | 5092: PUSH2 0x0571 | 5095: JUMP
5096: JUMPDEST | 5097: POP | 5098: CALLVALUE | 5099: PUSH2 0x0582 | 5102: JUMPI
5103: PUSH2 0x0904 | 5106: PUSH2 0x08f2 | 5109: CALLDATASIZE | 5110: PUSH1 0x04 | 5112: PUSH2 0x08a7 | 5115: JUMP
5116: JUMPDEST | 5117: SWAP3 | 5118: PUSH2 0x08fe | 5121: SWAP3 | 5122: SWAP2 | 5123: SWAP3 | 5124: PUSH2 0x2fd5 | 5127: JUMP
5128: JUMPDEST | 5129: CALLER | 5130: PUSH2 0x3ced | 5133: JUMP
5134: JUMPDEST | 5135: PUSH1 0x00 | 5137: PUSH1 0x00 | 5139: DUP1 | 5140: MLOAD | 5141: PUSH1 0x20 | 5143: PUSH2 0x4852 | 5146: DUP4 | 5147: CODECOPY | 5148: DUP2 | 5149: MLOAD | 5150: SWAP2 | 5151: MSTORE | 5152: SSTORE | 5153: STOP
5154: JUMPDEST | 5155: POP | 5156: CALLVALUE | 5157: PUSH2 0x0582 | 5160: JUMPI
5161: PUSH1 0x00 | 5163: CALLDATASIZE | 5164: PUSH1 0x03 | 5166: NOT | 5167: ADD | 5168: SLT | 5169: PUSH2 0x0582 | 5172: JUMPI
5173: PUSH1 0x20 | 5175: PUSH1 0x40 | 5177: MLOAD | 5178: PUSH32 0x0000000000000000000000000000000000000000000000000000000000000000 | 5211: DUP2 | 5212: MSTORE | 5213: RETURN
5214: JUMPDEST | 5215: SWAP2 | 5216: SWAP1 | 5217: DUP3 | 5218: PUSH1 0x40 | 5220: SWAP2 | 5221: SUB | 5222: SLT | 5223: PUSH2 0x0582 | 5226: JUMPI
5227: PUSH1 0x20 | 5229: DUP3 | 5230: CALLDATALOAD | 5231: PUSH2 0x096d | 5234: DUP2 | 5235: PUSH2 0x0571 | 5238: JUMP
5239: JUMPDEST | 5240: SWAP3 | 5241: ADD | 5242: CALLDATALOAD | 5243: PUSH2 0x0979 | 5246: DUP2 | 5247: PUSH2 0x0571 | 5250: JUMP
5251: JUMPDEST | 5252: SWAP1 | 5253: JUMP
5254: JUMPDEST | 5255: SWAP1 | 5256: PUSH1 0x01 | 5258: DUP1 | 5259: PUSH1 0xa0 | 5261: SHL | 5262: SUB | 5263: AND | 5264: PUSH1 0x00 | 5266: MSTORE | 5267: PUSH1 0x20 | 5269: MSTORE | 5270: PUSH1 0x40 | 5272: PUSH1 0x00 | 5274: KECCAK256 | 5275: SWAP1 | 5276: JUMP
5277: JUMPDEST | 5278: PUSH1 0x01 | 5280: PUSH1 0x01 | 5282: PUSH1 0x80 | 5284: SHL | 5285: SUB | 5286: AND | 5287: SWAP1 | 5288: JUMP
5289: JUMPDEST | 5290: PUSH1 0x01 | 5292: PUSH1 0x01 | 5294: PUSH1 0x80 | 5296: SHL | 5297: SUB | 5298: SWAP2 | 5299: DUP3 | 5300: AND | 5301: DUP2 | 5302: MSTORE | 5303: SWAP2 | 5304: AND | 5305: PUSH1 0x20 | 5307: DUP3 | 5308: ADD | 5309: MSTORE | 5310: PUSH1 0x40 | 5312: ADD | 5313: SWAP1 | 5314: JUMP
5315: JUMPDEST | 5316: POP | 5317: CALLVALUE | 5318: PUSH2 0x0582 | 5321: JUMPI
5322: PUSH2 0x0a0a | 5325: PUSH2 0x09ee | 5328: PUSH2 0x09d0 | 5331: CALLDATASIZE | 5332: PUSH1 0x04 | 5334: PUSH2 0x0954 | 5337: JUMP
5338: JUMPDEST | 5339: PUSH1 0x01 | 5341: PUSH1 0x01 | 5343: PUSH1 0xa0 | 5345: SHL | 5346: SUB | 5347: SWAP1 | 5348: SWAP2 | 5349: AND | 5350: PUSH1 0x00 | 5352: SWAP1 | 5353: DUP2 | 5354: MSTORE | 5355: PUSH1 0x06 | 5357: PUSH1 0x20 | 5359: MSTORE | 5360: PUSH1 0x40 | 5362: SWAP1 | 5363: KECCAK256 | 5364: PUSH2 0x097c | 5367: JUMP
5368: JUMPDEST | 5369: SLOAD | 5370: PUSH1 0x40 | 5372: MLOAD | 5373: SWAP2 | 5374: DUP3 | 5375: SWAP2 | 5376: PUSH1 0x80 | 5378: DUP2 | 5379: SWAP1 | 5380: SHR | 5381: SWAP1 | 5382: PUSH1 0x01 | 5384: PUSH1 0x01 | 5386: PUSH1 0x80 | 5388: SHL | 5389: SUB | 5390: AND | 5391: DUP4 | 5392: PUSH2 0x099f | 5395: JUMP
5396: JUMPDEST | 5397: SUB | 5398: SWAP1 | 5399: RETURN
5400: JUMPDEST | 5401: POP | 5402: CALLVALUE | 5403: PUSH2 0x0582 | 5406: JUMPI
5407: PUSH1 0x00 | 5409: CALLDATASIZE | 5410: PUSH1 0x03 | 5412: NOT | 5413: ADD | 5414: SLT | 5415: PUSH2 0x0582 | 5418: JUMPI
5419: PUSH1 0x20 | 5421: PUSH1 0x40 | 5423: MLOAD | 5424: PUSH32 0x0000000000000000000000000000000000000000000000000000000000000000 | 5457: DUP2 | 5458: MSTORE | 5459: RETURN
5460: JUMPDEST | 5461: POP | 5462: CALLVALUE | 5463: PUSH2 0x0582 | 5466: JUMPI
5467: PUSH1 0x20 | 5469: CALLDATASIZE | 5470: PUSH1 0x03 | 5472: NOT | 5473: ADD | 5474: SLT | 5475: PUSH2 0x0582 | 5478: JUMPI
5479: PUSH1 0x04 | 5481: CALLDATALOAD | 5482: PUSH2 0x0a68 | 5485: DUP2 | 5486: PUSH2 0x0571 | 5489: JUMP
5490: JUMPDEST | 5491: PUSH1 0x01 | 5493: DUP1 | 5494: PUSH1 0xa0 | 5496: SHL | 5497: SUB | 5498: AND | 5499: PUSH1 0x00 | 5501: MSTORE | 5502: PUSH1 0x04 | 5504: PUSH1 0x20 | 5506: MSTORE | 5507: PUSH1 0x20 | 5509: PUSH1 0x40 | 5511: PUSH1 0x00 | 5513: KECCAK256 | 5514: SLOAD | 5515: PUSH1 0x40 | 5517: MLOAD | 5518: SWAP1 | 5519: DUP2 | 5520: MSTORE | 5521: RETURN
5522: JUMPDEST | 5523: POP | 5524: CALLVALUE | 5525: PUSH2 0x0582 | 5528: JUMPI
5529: PUSH1 0x00 | 5531: CALLDATASIZE | 5532: PUSH1 0x03 | 5534: NOT | 5535: ADD | 5536: SLT | 5537: PUSH2 0x0582 | 5540: JUMPI
5541: PUSH1 0x20 | 5543: PUSH1 0x40 | 5545: MLOAD | 5546: PUSH32 0x0000000000000000000000000000000000000000000000000000000000000000 | 5579: DUP2 | 5580: MSTORE | 5581: RETURN
5582: JUMPDEST | 5583: POP | 5584: CALLVALUE | 5585: PUSH2 0x0582 | 5588: JUMPI
5589: PUSH1 0x00 | 5591: CALLDATASIZE | 5592: PUSH1 0x03 | 5594: NOT | 5595: ADD | 5596: SLT | 5597: PUSH2 0x0582 | 5600: JUMPI
5601: PUSH1 0x20 | 5603: PUSH1 0x40 | 5605: MLOAD | 5606: PUSH1 0xff | 5608: PUSH32 0x0000000000000000000000000000000000000000000000000000000000000000 | 5641: AND | 5642: DUP2 | 5643: MSTORE | 5644: RETURN
5645: JUMPDEST | 5646: POP | 5647: CALLVALUE | 5648: PUSH2 0x0582 | 5651: JUMPI
5652: PUSH1 0x00 | 5654: CALLDATASIZE | 5655: PUSH1 0x03 | 5657: NOT | 5658: ADD | 5659: SLT | 5660: PUSH2 0x0582 | 5663: JUMPI
5664: PUSH1 0x20 | 5666: PUSH1 0x40 | 5668: MLOAD | 5669: PUSH32 0x0000000000000000000000000000000000000000000000000000000000000000 | 5702: DUP2 | 5703: MSTORE | 5704: RETURN
5705: JUMPDEST | 5706: POP | 5707: CALLVALUE | 5708: PUSH2 0x0582 | 5711: JUMPI
5712: PUSH1 0x20 | 5714: CALLDATASIZE | 5715: PUSH1 0x03 | 5717: NOT | 5718: ADD | 5719: SLT | 5720: PUSH2 0x0582 | 5723: JUMPI
5724: PUSH1 0x20 | 5726: PUSH2 0x05e0 | 5729: PUSH1 0x04 | 5731: CALLDATALOAD | 5732: PUSH2 0x0b62 | 5735: DUP2 | 5736: PUSH2 0x0571 | 5739: JUMP
5740: JUMPDEST | 5741: PUSH2 0x47aa | 5744: JUMP
5745: JUMPDEST | 5746: POP | 5747: CALLVALUE | 5748: PUSH2 0x0582 | 5751: JUMPI
5752: PUSH1 0x20 | 5754: CALLDATASIZE | 5755: PUSH1 0x03 | 5757: NOT | 5758: ADD | 5759: SLT | 5760: PUSH2 0x0582 | 5763: JUMPI
5764: PUSH1 0x20 | 5766: PUSH2 0x05af | 5769: PUSH1 0x04 | 5771: CALLDATALOAD | 5772: PUSH2 0x0b8a | 5775: DUP2 | 5776: PUSH2 0x0571 | 5779: JUMP
5780: JUMPDEST | 5781: PUSH2 0x27b4 | 5784: JUMP
5785: JUMPDEST | 5786: PUSH1 0x01 | 5788: PUSH1 0x01 | 5790: PUSH1 0x40 | 5792: SHL | 5793: SUB | 5794: AND | 5795: SWAP1 | 5796: JUMP
5797: JUMPDEST | 5798: PUSH2 0x0c31 | 5801: SWAP1 | 5802: SWAP3 | 5803: SWAP2 | 5804: SWAP3 | 5805: PUSH1 0xe0 | 5807: DUP1 | 5808: PUSH2 0x0100 | 5811: DUP4 | 5812: ADD | 5813: SWAP6 | 5814: PUSH1 0xff | 5816: DUP2 | 5817: MLOAD | 5818: AND | 5819: DUP5 | 5820: MSTORE | 5821: PUSH1 0x01 | 5823: DUP1 | 5824: PUSH1 0xa0 | 5826: SHL | 5827: SUB | 5828: DUP1 | 5829: PUSH1 0x20 | 5831: DUP4 | 5832: ADD | 5833: MLOAD | 5834: AND | 5835: PUSH1 0x20 | 5837: DUP7 | 5838: ADD | 5839: MSTORE | 5840: PUSH1 0x40 | 5842: DUP3 | 5843: ADD | 5844: MLOAD | 5845: AND | 5846: PUSH1 0x40 | 5848: DUP6 | 5849: ADD | 5850: MSTORE | 5851: PUSH1 0x01 | 5853: DUP1 | 5854: PUSH1 0x40 | 5856: SHL | 5857: SUB | 5858: PUSH1 0x60 | 5860: DUP3 | 5861: ADD | 5862: MLOAD | 5863: AND | 5864: PUSH1 0x60 | 5866: DUP6 | 5867: ADD | 5868: MSTORE | 5869: PUSH2 0x0bfb | 5872: PUSH1 0x80 | 5874: DUP3 | 5875: ADD | 5876: MLOAD | 5877: PUSH1 0x80 | 5879: DUP7 | 5880: ADD | 5881: SWAP1 | 5882: PUSH1 0x01 | 5884: DUP1 | 5885: PUSH1 0x40 | 5887: SHL | 5888: SUB | 5889: AND | 5890: SWAP1 | 5891: MSTORE | 5892: JUMP
5893: JUMPDEST | 5894: PUSH1 0xa0 | 5896: DUP2 | 5897: DUP2 | 5898: ADD | 5899: MLOAD | 5900: PUSH1 0x01 | 5902: PUSH1 0x01 | 5904: PUSH1 0x40 | 5906: SHL | 5907: SUB | 5908: AND | 5909: SWAP1 | 5910: DUP6 | 5911: ADD | 5912: MSTORE | 5913: PUSH1 0xc0 | 5915: DUP2 | 5916: DUP2 | 5917: ADD | 5918: MLOAD | 5919: PUSH1 0x01 | 5921: PUSH1 0x01 | 5923: PUSH1 0x40 | 5925: SHL | 5926: SUB | 5927: AND | 5928: SWAP1 | 5929: DUP6 | 5930: ADD | 5931: MSTORE | 5932: ADD | 5933: MLOAD | 5934: PUSH1 0x01 | 5936: PUSH1 0x01 | 5938: PUSH1 0x80 | 5940: SHL | 5941: SUB | 5942: AND | 5943: SWAP2 | 5944: ADD | 5945: MSTORE | 5946: JUMP
5947: JUMPDEST | 5948: JUMP
5949: JUMPDEST | 5950: POP | 5951: CALLVALUE | 5952: PUSH2 0x0582 | 5955: JUMPI
5956: PUSH1 0x20 | 5958: CALLDATASIZE | 5959: PUSH1 0x03 | 5961: NOT | 5962: ADD | 5963: SLT | 5964: PUSH2 0x0582 | 5967: JUMPI
5968: PUSH2 0x0a0a | 5971: PUSH2 0x0c5c | 5974: PUSH1 0x04 | 5976: CALLDATALOAD | 5977: PUSH2 0x0c57 | 5980: DUP2 | 5981: PUSH2 0x0571 | 5984: JUMP
5985: JUMPDEST | 5986: PUSH2 0x1d3a | 5989: JUMP
5990: JUMPDEST | 5991: PUSH1 0x40 | 5993: MLOAD | 5994: SWAP2 | 5995: DUP3 | 5996: SWAP2 | 5997: DUP3 | 5998: PUSH2 0x0b9b | 6001: JUMP
6002: JUMPDEST | 6003: POP | 6004: CALLVALUE | 6005: PUSH2 0x0582 | 6008: JUMPI
6009: PUSH1 0x20 | 6011: CALLDATASIZE | 6012: PUSH1 0x03 | 6014: NOT | 6015: ADD | 6016: SLT | 6017: PUSH2 0x0582 | 6020: JUMPI
6021: PUSH1 0x20 | 6023: PUSH2 0x05e0 | 6026: PUSH1 0x04 | 6028: CALLDATALOAD | 6029: PUSH2 0x0c8b | 6032: DUP2 | 6033: PUSH2 0x0571 | 6036: JUMP
6037: JUMPDEST | 6038: PUSH2 0x249f | 6041: JUMP
6042: JUMPDEST | 6043: POP | 6044: CALLVALUE | 6045: PUSH2 0x0582 | 6048: JUMPI
6049: PUSH2 0x0904 | 6052: PUSH2 0x0ca4 | 6055: CALLDATASIZE | 6056: PUSH1 0x04 | 6058: PUSH2 0x07d1 | 6061: JUMP
6062: JUMPDEST | 6063: SWAP2 | 6064: PUSH2 0x0cad | 6067: PUSH2 0x2fd5 | 6070: JUMP
6071: JUMPDEST | 6072: CALLER | 6073: CALLER | 6074: PUSH2 0x2f23 | 6077: JUMP
6078: JUMPDEST | 6079: POP | 6080: CALLVALUE | 6081: PUSH2 0x0582 | 6084: JUMPI
6085: PUSH2 0x0904 | 6088: PUSH2 0x0cc8 | 6091: CALLDATASIZE | 6092: PUSH1 0x04 | 6094: PUSH2 0x07d1 | 6097: JUMP
6098: JUMPDEST | 6099: SWAP2 | 6100: PUSH2 0x0cd1 | 6103: PUSH2 0x2fd5 | 6106: JUMP
6107: JUMPDEST | 6108: CALLER | 6109: CALLER | 6110: PUSH2 0x38a0 | 6113: JUMP
6114: JUMPDEST | 6115: POP | 6116: CALLVALUE | 6117: PUSH2 0x0582 | 6120: JUMPI
6121: PUSH1 0x00 | 6123: CALLDATASIZE | 6124: PUSH1 0x03 | 6126: NOT | 6127: ADD | 6128: SLT | 6129: PUSH2 0x0582 | 6132: JUMPI
6133: PUSH1 0x20 | 6135: PUSH1 0x40 | 6137: MLOAD | 6138: PUSH32 0x0000000000000000000000000000000000000000000000000000000000000000 | 6171: DUP2 | 6172: MSTORE | 6173: RETURN
6174: JUMPDEST | 6175: CALLDATALOAD | 6176: SWAP1 | 6177: DUP2 | 6178: ISZERO | 6179: ISZERO | 6180: DUP3 | 6181: SUB | 6182: PUSH2 0x0582 | 6185: JUMPI
6186: JUMP
6187: JUMPDEST | 6188: POP | 6189: CALLVALUE | 6190: PUSH2 0x0582 | 6193: JUMPI
6194: PUSH1 0xa0 | 6196: CALLDATASIZE | 6197: PUSH1 0x03 | 6199: NOT | 6200: ADD | 6201: SLT | 6202: PUSH2 0x0582 | 6205: JUMPI
6206: PUSH2 0x0d3d | 6209: PUSH1 0x04 | 6211: PUSH2 0x0d14 | 6214: JUMP
6215: JUMPDEST | 6216: PUSH2 0x0d47 | 6219: PUSH1 0x24 | 6221: PUSH2 0x0d14 | 6224: JUMP
6225: JUMPDEST | 6226: PUSH2 0x0d51 | 6229: PUSH1 0x44 | 6231: PUSH2 0x0d14 | 6234: JUMP
6235: JUMPDEST | 6236: SWAP2 | 6237: PUSH2 0x0d5c | 6240: PUSH1 0x64 | 6242: PUSH2 0x0d14 | 6245: JUMP
6246: JUMPDEST | 6247: SWAP3 | 6248: PUSH2 0x0d67 | 6251: PUSH1 0x84 | 6253: PUSH2 0x0d14 | 6256: JUMP
6257: JUMPDEST | 6258: PUSH1 0x01 | 6260: DUP1 | 6261: PUSH1 0xa0 | 6263: SHL | 6264: SUB | 6265: DUP1 | 6266: PUSH32 0x0000000000000000000000000000000000000000000000000000000000000000 | 6299: AND | 6300: CALLER | 6301: EQ | 6302: ISZERO | 6303: SWAP1 | 6304: DUP2 | 6305: PUSH2 0x0e73 | 6308: JUMPI
6309: JUMPDEST | 6310: POP | 6311: PUSH2 0x0e62 | 6314: JUMPI
6315: PUSH32 0x3be39979091ae7ca962aa1c44e645f2df3c221b79f324afa5f44aedc8d2f690d | 6348: SWAP5 | 6349: PUSH2 0x0e5d | 6352: SWAP3 | 6353: PUSH2 0x0e28 | 6356: PUSH2 0x0de5 | 6359: PUSH1 0x00 | 6361: PUSH2 0x0dd7 | 6364: DUP9 | 6365: PUSH2 0x2b6e | 6368: JUMP
6369: JUMPDEST | 6370: SWAP1 | 6371: PUSH1 0xff | 6373: DUP1 | 6374: DUP1 | 6375: SWAP4 | 6376: AND | 6377: SWAP2 | 6378: AND | 6379: SHL | 6380: AND | 6381: SWAP1 | 6382: JUMP
6383: JUMPDEST | 6384: PUSH2 0x0df3 | 6387: PUSH1 0x01 | 6389: PUSH2 0x0dd7 | 6392: DUP11 | 6393: PUSH2 0x2b6e | 6396: JUMP
6397: JUMPDEST | 6398: OR | 6399: PUSH2 0x0e02 | 6402: PUSH1 0x02 | 6404: PUSH2 0x0dd7 | 6407: DUP6 | 6408: PUSH2 0x2b6e | 6411: JUMP
6412: JUMPDEST | 6413: OR | 6414: PUSH2 0x0e11 | 6417: PUSH1 0x03 | 6419: PUSH2 0x0dd7 | 6422: DUP7 | 6423: PUSH2 0x2b6e | 6426: JUMP
6427: JUMPDEST | 6428: OR | 6429: PUSH2 0x0e20 | 6432: PUSH1 0x04 | 6434: PUSH2 0x0dd7 | 6437: DUP8 | 6438: PUSH2 0x2b6e | 6441: JUMP
6442: JUMPDEST | 6443: OR | 6444: PUSH1 0x01 | 6446: PUSH2 0x2b4b | 6449: JUMP
6450: JUMPDEST | 6451: PUSH1 0x40 | 6453: MLOAD | 6454: SWAP6 | 6455: DUP7 | 6456: SWAP6 | 6457: DUP7 | 6458: SWAP4 | 6459: SWAP1 | 6460: SWAP6 | 6461: SWAP5 | 6462: SWAP2 | 6463: SWAP3 | 6464: PUSH1 0x80 | 6466: SWAP4 | 6467: PUSH1 0xa0 | 6469: DUP7 | 6470: ADD | 6471: SWAP8 | 6472: ISZERO | 6473: ISZERO | 6474: DUP7 | 6475: MSTORE | 6476: ISZERO | 6477: ISZERO | 6478: PUSH1 0x20 | 6480: DUP7 | 6481: ADD | 6482: MSTORE | 6483: ISZERO | 6484: ISZERO | 6485: PUSH1 0x40 | 6487: DUP6 | 6488: ADD | 6489: MSTORE | 6490: ISZERO | 6491: ISZERO | 6492: PUSH1 0x60 | 6494: DUP5 | 6495: ADD | 6496: MSTORE | 6497: ISZERO | 6498: ISZERO | 6499: SWAP2 | 6500: ADD | 6501: MSTORE | 6502: JUMP
6503: JUMPDEST | 6504: SUB | 6505: SWAP1 | 6506: LOG1 | 6507: STOP
6508: JUMPDEST | 6509: PUSH1 0x40 | 6511: MLOAD | 6512: PUSH3 0x82b429 | 6516: PUSH1 0xe8 | 6518: SHL | 6519: DUP2 | 6520: MSTORE | 6521: PUSH1 0x04 | 6523: SWAP1 | 6524: REVERT
6525: JUMPDEST | 6526: SWAP1 | 6527: POP | 6528: PUSH32 0x0000000000000000000000000000000000000000000000000000000000000000 | 6561: AND | 6562: CALLER | 6563: EQ | 6564: ISZERO | 6565: CODESIZE | 6566: PUSH2 0x0d9b | 6569: JUMP
6570: JUMPDEST | 6571: POP | 6572: CALLVALUE | 6573: PUSH2 0x0582 | 6576: JUMPI
6577: PUSH1 0x00 | 6579: CALLDATASIZE | 6580: PUSH1 0x03 | 6582: NOT | 6583: ADD | 6584: SLT | 6585: PUSH2 0x0582 | 6588: JUMPI
6589: PUSH1 0x40 | 6591: MLOAD | 6592: PUSH32 0x0000000000000000000000000000000000000000000000000000000000000000 | 6625: PUSH1 0x01 | 6627: PUSH1 0x01 | 6629: PUSH1 0xa0 | 6631: SHL | 6632: SUB | 6633: AND | 6634: DUP2 | 6635: MSTORE | 6636: PUSH1 0x20 | 6638: SWAP1 | 6639: RETURN
6640: JUMPDEST | 6641: POP | 6642: CALLVALUE | 6643: PUSH2 0x0582 | 6646: JUMPI
6647: PUSH1 0x20 | 6649: CALLDATASIZE | 6650: PUSH1 0x03 | 6652: NOT | 6653: ADD | 6654: SLT | 6655: PUSH2 0x0582 | 6658: JUMPI
6659: PUSH1 0x04 | 6661: CALLDATALOAD | 6662: PUSH2 0x0f04 | 6665: DUP2 | 6666: PUSH2 0x0571 | 6669: JUMP
6670: JUMPDEST | 6671: PUSH1 0x01 | 6673: PUSH1 0x01 | 6675: PUSH1 0xa0 | 6677: SHL | 6678: SUB | 6679: AND | 6680: PUSH1 0x00 | 6682: SWAP1 | 6683: DUP2 | 6684: MSTORE | 6685: PUSH1 0x02 | 6687: PUSH1 0x20 | 6689: MSTORE | 6690: PUSH1 0x40 | 6692: SWAP1 | 6693: DUP2 | 6694: SWAP1 | 6695: KECCAK256 | 6696: SLOAD | 6697: SWAP1 | 6698: MLOAD | 6699: SWAP1 | 6700: DUP2 | 6701: SWAP1 | 6702: PUSH2 0x0a0a | 6705: SWAP1 | 6706: PUSH1 0x80 | 6708: DUP2 | 6709: SWAP1 | 6710: SHR | 6711: SWAP1 | 6712: PUSH1 0x01 | 6714: PUSH1 0x01 | 6716: PUSH1 0x80 | 6718: SHL | 6719: SUB | 6720: AND | 6721: DUP4 | 6722: PUSH2 0x099f | 6725: JUMP
6726: JUMPDEST | 6727: POP | 6728: CALLVALUE | 6729: PUSH2 0x0582 | 6732: JUMPI
6733: PUSH1 0x00 | 6735: CALLDATASIZE | 6736: PUSH1 0x03 | 6738: NOT | 6739: ADD | 6740: SLT | 6741: PUSH2 0x0582 | 6744: JUMPI
6745: PUSH1 0x20 | 6747: PUSH1 0x40 | 6749: MLOAD | 6750: PUSH32 0x0000000000000000000000000000000000000000000000000000000000000000 | 6783: DUP2 | 6784: MSTORE | 6785: RETURN
6786: JUMPDEST | 6787: POP | 6788: CALLVALUE | 6789: PUSH2 0x0582 | 6792: JUMPI
6793: PUSH1 0x00 | 6795: CALLDATASIZE | 6796: PUSH1 0x03 | 6798: NOT | 6799: ADD | 6800: SLT | 6801: PUSH2 0x0582 | 6804: JUMPI
6805: PUSH1 0x20 | 6807: PUSH1 0x04 | 6809: PUSH1 0x01 | 6811: SLOAD | 6812: PUSH1 0xf8 | 6814: SHR | 6815: AND | 6816: ISZERO | 6817: ISZERO | 6818: PUSH1 0x40 | 6820: MLOAD | 6821: SWAP1 | 6822: DUP2 | 6823: MSTORE | 6824: RETURN
6825: JUMPDEST | 6826: POP | 6827: CALLVALUE | 6828: PUSH2 0x0582 | 6831: JUMPI
6832: PUSH1 0x20 | 6834: CALLDATASIZE | 6835: PUSH1 0x03 | 6837: NOT | 6838: ADD | 6839: SLT | 6840: PUSH2 0x0582 | 6843: JUMPI
6844: PUSH1 0x20 | 6846: PUSH2 0x05e0 | 6849: PUSH1 0x04 | 6851: CALLDATALOAD | 6852: PUSH2 0x0fc2 | 6855: DUP2 | 6856: PUSH2 0x0571 | 6859: JUMP
6860: JUMPDEST | 6861: PUSH2 0x474c | 6864: JUMP
6865: JUMPDEST | 6866: POP | 6867: CALLVALUE | 6868: PUSH2 0x0582 | 6871: JUMPI
6872: PUSH1 0x00 | 6874: CALLDATASIZE | 6875: PUSH1 0x03 | 6877: NOT | 6878: ADD | 6879: SLT | 6880: PUSH2 0x0582 | 6883: JUMPI
6884: PUSH1 0x20 | 6886: PUSH1 0x40 | 6888: MLOAD | 6889: PUSH32 0x0000000000000000000000000000000000000000000000000000000000000000 | 6922: DUP2 | 6923: MSTORE | 6924: RETURN
6925: JUMPDEST | 6926: POP | 6927: CALLVALUE | 6928: PUSH2 0x0582 | 6931: JUMPI
6932: PUSH1 0x40 | 6934: CALLDATASIZE | 6935: PUSH1 0x03 | 6937: NOT | 6938: ADD | 6939: SLT | 6940: PUSH2 0x0582 | 6943: JUMPI
6944: PUSH1 0x20 | 6946: PUSH2 0x05e0 | 6949: PUSH1 0x04 | 6951: CALLDATALOAD | 6952: PUSH2 0x1026 | 6955: DUP2 | 6956: PUSH2 0x0571 | 6959: JUMP
6960: JUMPDEST | 6961: PUSH1 0x24 | 6963: CALLDATALOAD | 6964: SWAP1 | 6965: PUSH2 0x462d | 6968: JUMP
6969: JUMPDEST | 6970: POP | 6971: CALLVALUE | 6972: PUSH2 0x0582 | 6975: JUMPI
6976: PUSH1 0x00 | 6978: CALLDATASIZE | 6979: PUSH1 0x03 | 6981: NOT | 6982: ADD | 6983: SLT | 6984: PUSH2 0x0582 | 6987: JUMPI
6988: PUSH1 0x20 | 6990: PUSH2 0x05e0 | 6993: PUSH2 0x23ec | 6996: JUMP
6997: JUMPDEST | 6998: POP | 6999: CALLVALUE | 7000: PUSH2 0x0582 | 7003: JUMPI
7004: PUSH1 0x00 | 7006: CALLDATASIZE | 7007: PUSH1 0x03 | 7009: NOT | 7010: ADD | 7011: SLT | 7012: PUSH2 0x0582 | 7015: JUMPI
7016: PUSH1 0x20 | 7018: PUSH1 0x40 | 7020: MLOAD | 7021: PUSH32 0x0000000000000000000000000000000000000000000000000000000000000000 | 7054: DUP2 | 7055: MSTORE | 7056: RETURN
7057: JUMPDEST | 7058: POP | 7059: CALLVALUE | 7060: PUSH2 0x0582 | 7063: JUMPI
7064: PUSH1 0x00 | 7066: CALLDATASIZE | 7067: PUSH1 0x03 | 7069: NOT | 7070: ADD | 7071: SLT | 7072: PUSH2 0x0582 | 7075: JUMPI
7076: PUSH1 0x20 | 7078: PUSH7 0x038d7ea4c68000 | 7086: PUSH2 0x06ca | 7089: PUSH2 0x10ae | 7092: PUSH2 0x1dbe | 7095: JUMP
7096: JUMPDEST | 7097: PUSH2 0x10cb | 7100: PUSH1 0x01 | 7102: SLOAD | 7103: SWAP2 | 7104: PUSH2 0x06ab | 7107: PUSH5 0xffffffffff | 7113: SWAP2 | 7114: DUP3 | 7115: DUP6 | 7116: PUSH1 0xd0 | 7118: SHR | 7119: AND | 7120: SWAP1 | 7121: PUSH2 0x1e49 | 7124: JUMP
7125: JUMPDEST | 7126: PUSH1 0x01 | 7128: PUSH1 0x01 | 7130: PUSH1 0x40 | 7132: SHL | 7133: SUB | 7134: AND | 7135: SWAP2 | 7136: PUSH1 0x68 | 7138: SHR | 7139: PUSH1 0x01 | 7141: PUSH1 0x01 | 7143: PUSH1 0x68 | 7145: SHL | 7146: SUB | 7147: AND | 7148: SWAP1 | 7149: POP | 7150: PUSH2 0x1e77 | 7153: JUMP
7154: JUMPDEST | 7155: POP | 7156: CALLVALUE | 7157: PUSH2 0x0582 | 7160: JUMPI
7161: PUSH1 0x00 | 7163: CALLDATASIZE | 7164: PUSH1 0x03 | 7166: NOT | 7167: ADD | 7168: SLT | 7169: PUSH2 0x0582 | 7172: JUMPI
7173: PUSH1 0x20 | 7175: PUSH1 0x08 | 7177: PUSH1 0x01 | 7179: SLOAD | 7180: PUSH1 0xf8 | 7182: SHR | 7183: AND | 7184: ISZERO | 7185: ISZERO | 7186: PUSH1 0x40 | 7188: MLOAD | 7189: SWAP1 | 7190: DUP2 | 7191: MSTORE | 7192: RETURN
7193: JUMPDEST | 7194: POP | 7195: CALLVALUE | 7196: PUSH2 0x0582 | 7199: JUMPI
7200: PUSH2 0x0904 | 7203: PUSH2 0x1123 | 7206: CALLDATASIZE | 7207: PUSH1 0x04 | 7209: PUSH2 0x08a7 | 7212: JUMP
7213: JUMPDEST | 7214: SWAP3 | 7215: PUSH2 0x112f | 7218: SWAP3 | 7219: SWAP2 | 7220: SWAP3 | 7221: PUSH2 0x2fd5 | 7224: JUMP
7225: JUMPDEST | 7226: CALLER | 7227: PUSH2 0x2f23 | 7230: JUMP
7231: JUMPDEST | 7232: POP | 7233: CALLVALUE | 7234: PUSH2 0x0582 | 7237: JUMPI
7238: PUSH1 0x00 | 7240: CALLDATASIZE | 7241: PUSH1 0x03 | 7243: NOT | 7244: ADD | 7245: SLT | 7246: PUSH2 0x0582 | 7249: JUMPI
7250: PUSH1 0x20 | 7252: PUSH1 0x40 | 7254: MLOAD | 7255: PUSH32 0x0000000000000000000000000000000000000000000000000000000000000000 | 7288: DUP2 | 7289: MSTORE | 7290: RETURN
7291: JUMPDEST | 7292: POP | 7293: CALLVALUE | 7294: PUSH2 0x0582 | 7297: JUMPI
7298: PUSH1 0x00 | 7300: CALLDATASIZE | 7301: PUSH1 0x03 | 7303: NOT | 7304: ADD | 7305: SLT | 7306: PUSH2 0x0582 | 7309: JUMPI
7310: PUSH1 0x20 | 7312: PUSH1 0x40 | 7314: MLOAD | 7315: PUSH32 0x0000000000000000000000000000000000000000000000000000000000000000 | 7348: DUP2 | 7349: MSTORE | 7350: RETURN
7351: JUMPDEST | 7352: POP | 7353: CALLVALUE | 7354: PUSH2 0x0582 | 7357: JUMPI
7358: PUSH1 0x00 | 7360: CALLDATASIZE | 7361: PUSH1 0x03 | 7363: NOT | 7364: ADD | 7365: SLT | 7366: PUSH2 0x0582 | 7369: JUMPI
7370: PUSH1 0x20 | 7372: PUSH1 0x40 | 7374: MLOAD | 7375: PUSH32 0x0000000000000000000000000000000000000000000000000000000000000000 | 7408: DUP2 | 7409: MSTORE | 7410: RETURN
7411: JUMPDEST | 7412: POP | 7413: CALLVALUE | 7414: PUSH2 0x0582 | 7417: JUMPI
7418: PUSH1 0x00 | 7420: CALLDATASIZE | 7421: PUSH1 0x03 | 7423: NOT | 7424: ADD | 7425: SLT | 7426: PUSH2 0x0582 | 7429: JUMPI
7430: PUSH1 0x20 | 7432: PUSH1 0x40 | 7434: MLOAD | 7435: PUSH32 0x0000000000000000000000000000000000000000000000000000000000000000 | 7468: DUP2 | 7469: MSTORE | 7470: RETURN
7471: JUMPDEST | 7472: POP | 7473: CALLVALUE | 7474: PUSH2 0x0582 | 7477: JUMPI
7478: PUSH1 0x20 | 7480: CALLDATASIZE | 7481: PUSH1 0x03 | 7483: NOT | 7484: ADD | 7485: SLT | 7486: PUSH2 0x0582 | 7489: JUMPI
7490: PUSH1 0x20 | 7492: PUSH2 0x1244 | 7495: PUSH1 0x04 | 7497: CALLDATALOAD | 7498: PUSH2 0x22b6 | 7501: JUMP
7502: JUMPDEST | 7503: PUSH1 0x40 | 7505: MLOAD | 7506: PUSH1 0x01 | 7508: PUSH1 0x01 | 7510: PUSH1 0x40 | 7512: SHL | 7513: SUB | 7514: SWAP1 | 7515: SWAP2 | 7516: AND | 7517: DUP2 | 7518: MSTORE | 7519: RETURN
7520: JUMPDEST | 7521: POP | 7522: CALLVALUE | 7523: PUSH2 0x0582 | 7526: JUMPI
7527: PUSH1 0x20 | 7529: CALLDATASIZE | 7530: PUSH1 0x03 | 7532: NOT | 7533: ADD | 7534: SLT | 7535: PUSH2 0x0582 | 7538: JUMPI
7539: PUSH1 0x20 | 7541: PUSH2 0x05e0 | 7544: PUSH1 0x04 | 7546: CALLDATALOAD | 7547: PUSH2 0x1279 | 7550: DUP2 | 7551: PUSH2 0x0571 | 7554: JUMP
7555: JUMPDEST | 7556: PUSH2 0x2559 | 7559: JUMP
7560: JUMPDEST | 7561: POP | 7562: CALLVALUE | 7563: PUSH2 0x0582 | 7566: JUMPI
7567: PUSH1 0x20 | 7569: PUSH1 0xff | 7571: PUSH2 0x12b3 | 7574: PUSH2 0x1296 | 7577: CALLDATASIZE | 7578: PUSH1 0x04 | 7580: PUSH2 0x0954 | 7583: JUMP
7584: JUMPDEST | 7585: PUSH1 0x01 | 7587: PUSH1 0x01 | 7589: PUSH1 0xa0 | 7591: SHL | 7592: SUB | 7593: SWAP1 | 7594: SWAP2 | 7595: AND | 7596: PUSH1 0x00 | 7598: SWAP1 | 7599: DUP2 | 7600: MSTORE | 7601: PUSH1 0x03 | 7603: DUP6 | 7604: MSTORE | 7605: PUSH1 0x40 | 7607: SWAP1 | 7608: KECCAK256 | 7609: PUSH2 0x097c | 7612: JUMP
7613: JUMPDEST | 7614: SLOAD | 7615: AND | 7616: PUSH1 0x40 | 7618: MLOAD | 7619: SWAP1 | 7620: ISZERO | 7621: ISZERO | 7622: DUP2 | 7623: MSTORE | 7624: RETURN
7625: JUMPDEST | 7626: POP | 7627: CALLVALUE | 7628: PUSH2 0x0582 | 7631: JUMPI
7632: PUSH1 0x00 | 7634: CALLDATASIZE | 7635: PUSH1 0x03 | 7637: NOT | 7638: ADD | 7639: SLT | 7640: PUSH2 0x0582 | 7643: JUMPI
7644: PUSH1 0x20 | 7646: PUSH1 0x02 | 7648: PUSH1 0x01 | 7650: SLOAD | 7651: PUSH1 0xf8 | 7653: SHR | 7654: AND | 7655: ISZERO | 7656: ISZERO | 7657: PUSH1 0x40 | 7659: MLOAD | 7660: SWAP1 | 7661: DUP2 | 7662: MSTORE | 7663: RETURN
7664: JUMPDEST | 7665: POP | 7666: CALLVALUE | 7667: PUSH2 0x0582 | 7670: JUMPI
7671: PUSH1 0x00 | 7673: CALLDATASIZE | 7674: PUSH1 0x03 | 7676: NOT | 7677: ADD | 7678: SLT | 7679: PUSH2 0x0582 | 7682: JUMPI
7683: PUSH1 0x20 | 7685: PUSH1 0x40 | 7687: MLOAD | 7688: PUSH1 0xff | 7690: PUSH32 0x0000000000000000000000000000000000000000000000000000000000000000 | 7723: AND | 7724: DUP2 | 7725: MSTORE | 7726: RETURN
7727: JUMPDEST | 7728: POP | 7729: CALLVALUE | 7730: PUSH2 0x0582 | 7733: JUMPI
7734: PUSH1 0x00 | 7736: CALLDATASIZE | 7737: PUSH1 0x03 | 7739: NOT | 7740: ADD | 7741: SLT | 7742: PUSH2 0x0582 | 7745: JUMPI
7746: PUSH1 0x20 | 7748: PUSH1 0x40 | 7750: MLOAD | 7751: PUSH32 0x0000000000000000000000000000000000000000000000000000000000000000 | 7784: DUP2 | 7785: MSTORE | 7786: RETURN
7787: JUMPDEST | 7788: POP | 7789: CALLVALUE | 7790: PUSH2 0x0582 | 7793: JUMPI
7794: PUSH1 0x40 | 7796: CALLDATASIZE | 7797: PUSH1 0x03 | 7799: NOT | 7800: ADD | 7801: SLT | 7802: PUSH2 0x0582 | 7805: JUMPI
7806: PUSH2 0x0844 | 7809: PUSH1 0x04 | 7811: CALLDATALOAD | 7812: PUSH2 0x1382 | 7815: DUP2 | 7816: PUSH2 0x0571 | 7819: JUMP
7820: JUMPDEST | 7821: PUSH2 0x138a | 7824: PUSH2 0x2fd5 | 7827: JUMP
7828: JUMPDEST | 7829: PUSH1 0x24 | 7831: CALLDATALOAD | 7832: SWAP1 | 7833: PUSH32 0x0000000000000000000000000000000000000000000000000000000000000000 | 7866: SWAP1 | 7867: CALLER | 7868: CALLER | 7869: PUSH2 0x38a0 | 7872: JUMP
7873: JUMPDEST | 7874: POP | 7875: CALLVALUE | 7876: PUSH2 0x0582 | 7879: JUMPI
7880: PUSH1 0x00 | 7882: CALLDATASIZE | 7883: PUSH1 0x03 | 7885: NOT | 7886: ADD | 7887: SLT | 7888: PUSH2 0x0582 | 7891: JUMPI
7892: PUSH1 0x20 | 7894: PUSH1 0x40 | 7896: MLOAD | 7897: PUSH32 0x0000000000000000000000000000000000000000000000000000000000000000 | 7930: DUP2 | 7931: MSTORE | 7932: RETURN
7933: JUMPDEST | 7934: POP | 7935: CALLVALUE | 7936: PUSH2 0x0582 | 7939: JUMPI
7940: PUSH2 0x1404 | 7943: CALLDATASIZE | 7944: PUSH1 0x04 | 7946: PUSH2 0x07d1 | 7949: JUMP
7950: JUMPDEST | 7951: SWAP2 | 7952: SWAP1 | 7953: PUSH1 0x01 | 7955: PUSH1 0x01 | 7957: PUSH1 0xa0 | 7959: SHL | 7960: SUB | 7961: SWAP1 | 7962: PUSH32 0x0000000000000000000000000000000000000000000000000000000000000000 | 7995: DUP3 | 7996: AND | 7997: CALLER | 7998: SUB | 7999: PUSH2 0x0e62 | 8002: JUMPI
8003: AND | 8004: SWAP2 | 8005: DUP3 | 8006: EXTCODESIZE | 8007: ISZERO | 8008: PUSH2 0x0582 | 8011: JUMPI
8012: PUSH2 0x1465 | 8015: SWAP3 | 8016: PUSH1 0x00 | 8018: SWAP3 | 8019: DUP4 | 8020: PUSH1 0x40 | 8022: MLOAD | 8023: DUP1 | 8024: SWAP7 | 8025: DUP2 | 8026: SWAP6 | 8027: DUP3 | 8028: SWAP5 | 8029: PUSH4 0x095ea7b3 | 8034: PUSH1 0xe0 | 8036: SHL | 8037: DUP5 | 8038: MSTORE | 8039: PUSH1 0x04 | 8041: DUP5 | 8042: ADD | 8043: PUSH2 0x3ed6 | 8046: JUMP
8047: JUMPDEST | 8048: SUB | 8049: SWAP3 | 8050: GAS | 8051: CALL | 8052: DUP1 | 8053: ISZERO | 8054: PUSH2 0x148b | 8057: JUMPI
8058: JUMPDEST | 8059: PUSH2 0x1476 | 8062: JUMPI
8063: STOP
8064: JUMPDEST | 8065: DUP1 | 8066: PUSH2 0x1485 | 8069: PUSH1 0x00 | 8071: PUSH2 0x0016 | 8074: SWAP4 | 8075: PUSH2 0x1b46 | 8078: JUMP
8079: JUMPDEST | 8080: DUP1 | 8081: PUSH2 0x05b9 | 8084: JUMP
8085: JUMPDEST | 8086: PUSH2 0x1493 | 8089: PUSH2 0x1bfe | 8092: JUMP
8093: JUMPDEST | 8094: PUSH2 0x1470 | 8097: JUMP
8098: JUMPDEST | 8099: POP | 8100: CALLVALUE | 8101: PUSH2 0x0582 | 8104: JUMPI
8105: PUSH1 0x20 | 8107: CALLDATASIZE | 8108: PUSH1 0x03 | 8110: NOT | 8111: ADD | 8112: SLT | 8113: PUSH2 0x0582 | 8116: JUMPI
8117: PUSH2 0x0016 | 8120: PUSH1 0x04 | 8122: CALLDATALOAD | 8123: PUSH2 0x14b9 | 8126: DUP2 | 8127: PUSH2 0x0571 | 8130: JUMP
8131: JUMPDEST | 8132: PUSH2 0x14c1 | 8135: PUSH2 0x1ece | 8138: JUMP
8139: JUMPDEST | 8140: PUSH1 0x01 | 8142: DUP1 | 8143: PUSH1 0xa0 | 8145: SHL | 8146: SUB | 8147: DUP2 | 8148: AND | 8149: PUSH1 0x00 | 8151: MSTORE | 8152: PUSH1 0x05 | 8154: PUSH1 0x20 | 8156: MSTORE | 8157: PUSH1 0x40 | 8159: PUSH1 0x00 | 8161: KECCAK256 | 8162: PUSH2 0x1528 | 8165: PUSH1 0x40 | 8167: MLOAD | 8168: SWAP2 | 8169: PUSH2 0x14e9 | 8172: PUSH1 0xa0 | 8174: DUP5 | 8175: PUSH2 0x1b46 | 8178: JUMP
8179: JUMPDEST | 8180: SLOAD | 8181: PUSH1 0x0c | 8183: DUP2 | 8184: SWAP1 | 8185: SIGNEXTEND | 8186: DUP4 | 8187: MSTORE | 8188: PUSH1 0x01 | 8190: PUSH1 0x01 | 8192: PUSH1 0x40 | 8194: SHL | 8195: SUB | 8196: PUSH1 0x68 | 8198: DUP3 | 8199: SWAP1 | 8200: SHR | 8201: DUP2 | 8202: AND | 8203: PUSH1 0x20 | 8205: DUP6 | 8206: ADD | 8207: MSTORE | 8208: PUSH1 0xa8 | 8210: DUP3 | 8211: SWAP1 | 8212: SHR | 8213: AND | 8214: PUSH1 0x40 | 8216: DUP5 | 8217: ADD | 8218: MSTORE | 8219: PUSH2 0xffff | 8222: PUSH1 0xe8 | 8224: DUP3 | 8225: SWAP1 | 8226: SHR | 8227: AND | 8228: PUSH1 0x60 | 8230: DUP5 | 8231: ADD | 8232: MSTORE | 8233: PUSH1 0xf8 | 8235: SHR | 8236: PUSH1 0x80 | 8238: DUP4 | 8239: ADD | 8240: MSTORE | 8241: JUMP
8242: JUMPDEST | 8243: DUP1 | 8244: MLOAD | 8245: PUSH1 0x0c | 8247: SIGNEXTEND | 8248: SWAP2 | 8249: PUSH2 0x2db5 | 8252: JUMP
8253: JUMPDEST | 8254: POP | 8255: CALLVALUE | 8256: PUSH2 0x0582 | 8259: JUMPI
8260: PUSH2 0x0904 | 8263: PUSH2 0x1547 | 8266: CALLDATASIZE | 8267: PUSH1 0x04 | 8269: PUSH2 0x08a7 | 8272: JUMP
8273: JUMPDEST | 8274: SWAP3 | 8275: PUSH2 0x1553 | 8278: SWAP3 | 8279: SWAP2 | 8280: SWAP3 | 8281: PUSH2 0x2fd5 | 8284: JUMP
8285: JUMPDEST | 8286: CALLER | 8287: PUSH2 0x38a0 | 8290: JUMP
8291: JUMPDEST | 8292: POP | 8293: CALLVALUE | 8294: PUSH2 0x0582 | 8297: JUMPI
8298: PUSH2 0x0904 | 8301: PUSH2 0x156d | 8304: CALLDATASIZE | 8305: PUSH1 0x04 | 8307: PUSH2 0x07d1 | 8310: JUMP
8311: JUMPDEST | 8312: SWAP2 | 8313: PUSH2 0x1576 | 8316: PUSH2 0x2fd5 | 8319: JUMP
8320: JUMPDEST | 8321: CALLER | 8322: CALLER | 8323: PUSH2 0x3ced | 8326: JUMP
8327: JUMPDEST | 8328: POP | 8329: CALLVALUE | 8330: PUSH2 0x0582 | 8333: JUMPI
8334: PUSH1 0x40 | 8336: CALLDATASIZE | 8337: PUSH1 0x03 | 8339: NOT | 8340: ADD | 8341: SLT | 8342: PUSH2 0x0582 | 8345: JUMPI
8346: PUSH1 0x04 | 8348: CALLDATALOAD | 8349: PUSH2 0x159b | 8352: DUP2 | 8353: PUSH2 0x0571 | 8356: JUMP
8357: JUMPDEST | 8358: PUSH1 0x24 | 8360: CALLDATALOAD | 8361: SWAP1 | 8362: PUSH1 0x01 | 8364: PUSH1 0x01 | 8366: PUSH1 0x40 | 8368: SHL | 8369: SUB | 8370: SWAP1 | 8371: DUP2 | 8372: DUP4 | 8373: GT | 8374: PUSH2 0x0582 | 8377: JUMPI
8378: CALLDATASIZE | 8379: PUSH1 0x23 | 8381: DUP5 | 8382: ADD | 8383: SLT | 8384: ISZERO | 8385: PUSH2 0x0582 | 8388: JUMPI
8389: DUP3 | 8390: PUSH1 0x04 | 8392: ADD | 8393: CALLDATALOAD | 8394: SWAP2 | 8395: DUP3 | 8396: GT | 8397: PUSH2 0x0582 | 8400: JUMPI
8401: CALLDATASIZE | 8402: PUSH1 0x24 | 8404: DUP4 | 8405: PUSH1 0x05 | 8407: SHL | 8408: DUP6 | 8409: ADD | 8410: ADD | 8411: GT | 8412: PUSH2 0x0582 | 8415: JUMPI
8416: PUSH1 0x24 | 8418: PUSH2 0x0016 | 8421: SWAP4 | 8422: ADD | 8423: SWAP1 | 8424: PUSH2 0x4118 | 8427: JUMP
8428: JUMPDEST | 8429: POP | 8430: CALLVALUE | 8431: PUSH2 0x0582 | 8434: JUMPI
8435: PUSH1 0x00 | 8437: CALLDATASIZE | 8438: PUSH1 0x03 | 8440: NOT | 8441: ADD | 8442: SLT | 8443: PUSH2 0x0582 | 8446: JUMPI
8447: PUSH1 0x40 | 8449: MLOAD | 8450: PUSH32 0x0000000000000000000000000000000000000000000000000000000000000000 | 8483: PUSH1 0x01 | 8485: PUSH1 0x01 | 8487: PUSH1 0xa0 | 8489: SHL | 8490: SUB | 8491: AND | 8492: DUP2 | 8493: MSTORE | 8494: PUSH1 0x20 | 8496: SWAP1 | 8497: RETURN
8498: JUMPDEST | 8499: POP | 8500: CALLVALUE | 8501: PUSH2 0x0582 | 8504: JUMPI
8505: PUSH1 0x20 | 8507: CALLDATASIZE | 8508: PUSH1 0x03 | 8510: NOT | 8511: ADD | 8512: SLT | 8513: PUSH2 0x0582 | 8516: JUMPI
8517: PUSH1 0x04 | 8519: CALLDATALOAD | 8520: PUSH2 0x1646 | 8523: DUP2 | 8524: PUSH2 0x0571 | 8527: JUMP
8528: JUMPDEST | 8529: PUSH1 0x01 | 8531: DUP1 | 8532: PUSH1 0xa0 | 8534: SHL | 8535: SUB | 8536: AND | 8537: PUSH1 0x00 | 8539: MSTORE | 8540: PUSH1 0x07 | 8542: PUSH1 0x20 | 8544: MSTORE | 8545: PUSH1 0x80 | 8547: PUSH1 0x40 | 8549: PUSH1 0x00 | 8551: KECCAK256 | 8552: SLOAD | 8553: PUSH1 0x40 | 8555: MLOAD | 8556: SWAP1 | 8557: PUSH4 0xffffffff | 8562: DUP2 | 8563: AND | 8564: DUP3 | 8565: MSTORE | 8566: PUSH1 0x01 | 8568: DUP1 | 8569: PUSH1 0x40 | 8571: SHL | 8572: SUB | 8573: DUP2 | 8574: PUSH1 0x20 | 8576: SHR | 8577: AND | 8578: PUSH1 0x20 | 8580: DUP4 | 8581: ADD | 8582: MSTORE | 8583: PUSH1 0x01 | 8585: DUP1 | 8586: DUP5 | 8587: SHL | 8588: SUB | 8589: DUP2 | 8590: PUSH1 0x60 | 8592: SHR | 8593: AND | 8594: PUSH1 0x40 | 8596: DUP4 | 8597: ADD | 8598: MSTORE | 8599: PUSH1 0xe0 | 8601: SHR | 8602: PUSH1 0x60 | 8604: DUP3 | 8605: ADD | 8606: MSTORE | 8607: RETURN
8608: JUMPDEST | 8609: PUSH1 0xff | 8611: DUP2 | 8612: AND | 8613: SUB | 8614: PUSH2 0x0582 | 8617: JUMPI
8618: JUMP
8619: JUMPDEST | 8620: POP | 8621: CALLVALUE | 8622: PUSH2 0x0582 | 8625: JUMPI
8626: PUSH1 0x20 | 8628: CALLDATASIZE | 8629: PUSH1 0x03 | 8631: NOT | 8632: ADD | 8633: SLT | 8634: PUSH2 0x0582 | 8637: JUMPI
8638: PUSH2 0x0a0a | 8641: PUSH2 0x0c5c | 8644: PUSH1 0x04 | 8646: CALLDATALOAD | 8647: PUSH2 0x16c5 | 8650: DUP2 | 8651: PUSH2 0x1696 | 8654: JUMP
8655: JUMPDEST | 8656: PUSH2 0x1c0b | 8659: JUMP
8660: JUMPDEST | 8661: POP | 8662: CALLVALUE | 8663: PUSH2 0x0582 | 8666: JUMPI
8667: PUSH1 0x20 | 8669: PUSH2 0x05af | 8672: PUSH2 0x16e0 | 8675: CALLDATASIZE | 8676: PUSH1 0x04 | 8678: PUSH2 0x0954 | 8681: JUMP
8682: JUMPDEST | 8683: SWAP1 | 8684: PUSH2 0x1b09 | 8687: JUMP
8688: JUMPDEST | 8689: POP | 8690: CALLVALUE | 8691: PUSH2 0x0582 | 8694: JUMPI
8695: PUSH1 0x00 | 8697: CALLDATASIZE | 8698: PUSH1 0x03 | 8700: NOT | 8701: ADD | 8702: SLT | 8703: PUSH2 0x0582 | 8706: JUMPI
8707: PUSH1 0x20 | 8709: PUSH1 0x10 | 8711: PUSH1 0x01 | 8713: SLOAD | 8714: PUSH1 0xf8 | 8716: SHR | 8717: AND | 8718: ISZERO | 8719: ISZERO | 8720: PUSH1 0x40 | 8722: MLOAD | 8723: SWAP1 | 8724: DUP2 | 8725: MSTORE | 8726: RETURN
8727: JUMPDEST | 8728: POP | 8729: CALLVALUE | 8730: PUSH2 0x0582 | 8733: JUMPI
8734: PUSH1 0x20 | 8736: CALLDATASIZE | 8737: PUSH1 0x03 | 8739: NOT | 8740: ADD | 8741: SLT | 8742: PUSH2 0x0582 | 8745: JUMPI
8746: PUSH1 0x20 | 8748: PUSH2 0x1244 | 8751: PUSH1 0x04 | 8753: CALLDATALOAD | 8754: PUSH2 0x21a6 | 8757: JUMP
8758: JUMPDEST | 8759: POP | 8760: CALLVALUE | 8761: PUSH2 0x0582 | 8764: JUMPI
8765: PUSH1 0x20 | 8767: CALLDATASIZE | 8768: PUSH1 0x03 | 8770: NOT | 8771: ADD | 8772: SLT | 8773: PUSH2 0x0582 | 8776: JUMPI
8777: PUSH1 0x04 | 8779: CALLDATALOAD | 8780: PUSH2 0x174a | 8783: DUP2 | 8784: PUSH2 0x0571 | 8787: JUMP
8788: JUMPDEST | 8789: PUSH1 0x01 | 8791: DUP1 | 8792: PUSH1 0xa0 | 8794: SHL | 8795: SUB | 8796: AND | 8797: PUSH1 0x00 | 8799: MSTORE | 8800: PUSH1 0x05 | 8802: PUSH1 0x20 | 8804: MSTORE | 8805: PUSH1 0xa0 | 8807: PUSH1 0x40 | 8809: PUSH1 0x00 | 8811: KECCAK256 | 8812: SLOAD | 8813: PUSH1 0x40 | 8815: MLOAD | 8816: SWAP1 | 8817: DUP1 | 8818: PUSH1 0x0c | 8820: SIGNEXTEND | 8821: DUP3 | 8822: MSTORE | 8823: PUSH1 0x01 | 8825: DUP1 | 8826: PUSH1 0x40 | 8828: SHL | 8829: SUB | 8830: DUP1 | 8831: DUP3 | 8832: PUSH1 0x68 | 8834: SHR | 8835: AND | 8836: PUSH1 0x20 | 8838: DUP5 | 8839: ADD | 8840: MSTORE | 8841: DUP2 | 8842: PUSH1 0xa8 | 8844: SHR | 8845: AND | 8846: PUSH1 0x40 | 8848: DUP4 | 8849: ADD | 8850: MSTORE | 8851: PUSH2 0xffff | 8854: DUP2 | 8855: PUSH1 0xe8 | 8857: SHR | 8858: AND | 8859: PUSH1 0x60 | 8861: DUP4 | 8862: ADD | 8863: MSTORE | 8864: PUSH1 0xf8 | 8866: SHR | 8867: PUSH1 0x80 | 8869: DUP3 | 8870: ADD | 8871: MSTORE | 8872: RETURN
8873: JUMPDEST | 8874: POP | 8875: CALLVALUE | 8876: PUSH2 0x0582 | 8879: JUMPI
8880: PUSH1 0x00 | 8882: CALLDATASIZE | 8883: PUSH1 0x03 | 8885: NOT | 8886: ADD | 8887: SLT | 8888: PUSH2 0x0582 | 8891: JUMPI
8892: PUSH1 0x40 | 8894: MLOAD | 8895: PUSH32 0x0000000000000000000000000000000000000000000000000000000000000000 | 8928: PUSH1 0x01 | 8930: PUSH1 0x01 | 8932: PUSH1 0xa0 | 8934: SHL | 8935: SUB | 8936: AND | 8937: DUP2 | 8938: MSTORE | 8939: PUSH1 0x20 | 8941: SWAP1 | 8942: RETURN
8943: JUMPDEST | 8944: POP | 8945: CALLVALUE | 8946: PUSH2 0x0582 | 8949: JUMPI
8950: PUSH1 0x40 | 8952: CALLDATASIZE | 8953: PUSH1 0x03 | 8955: NOT | 8956: ADD | 8957: SLT | 8958: PUSH2 0x0582 | 8961: JUMPI
8962: PUSH1 0x04 | 8964: CALLDATALOAD | 8965: PUSH2 0x1803 | 8968: DUP2 | 8969: PUSH2 0x0571 | 8972: JUMP
8973: JUMPDEST | 8974: PUSH1 0x24 | 8976: CALLDATALOAD | 8977: SWAP1 | 8978: PUSH1 0x01 | 8980: PUSH1 0x01 | 8982: PUSH1 0xa0 | 8984: SHL | 8985: SUB | 8986: PUSH32 0x0000000000000000000000000000000000000000000000000000000000000000 | 9019: DUP2 | 9020: AND | 9021: CALLER | 9022: SUB | 9023: PUSH2 0x0e62 | 9026: JUMPI
9027: PUSH2 0x1840 | 9030: PUSH2 0x2661 | 9033: JUMP
9034: JUMPDEST | 9035: PUSH1 0x00 | 9037: DUP2 | 9038: SLT | 9039: SWAP1 | 9040: DUP2 | 9041: ISZERO | 9042: PUSH2 0x18be | 9045: JUMPI
9046: JUMPDEST | 9047: POP | 9048: PUSH2 0x18ac | 9051: JUMPI
9052: DUP2 | 9053: PUSH2 0x189e | 9056: DUP5 | 9057: PUSH32 0xec4431f2ba1a9382f6b0c4352b888cba6f7db91667d9f776abe5ad8ddc5401b6 | 9090: SWAP5 | 9091: PUSH32 0x0000000000000000000000000000000000000000000000000000000000000000 | 9124: PUSH2 0x3ef1 | 9127: JUMP
9128: JUMPDEST | 9129: PUSH1 0x40 | 9131: MLOAD | 9132: SWAP4 | 9133: DUP5 | 9134: MSTORE | 9135: AND | 9136: SWAP2 | 9137: PUSH1 0x20 | 9139: SWAP1 | 9140: LOG2 | 9141: STOP
9142: JUMPDEST | 9143: PUSH1 0x40 | 9145: MLOAD | 9146: PUSH4 0x128bd24d | 9151: PUSH1 0xe3 | 9153: SHL | 9154: DUP2 | 9155: MSTORE | 9156: PUSH1 0x04 | 9158: SWAP1 | 9159: REVERT
9160: JUMPDEST | 9161: PUSH2 0x18c8 | 9164: SWAP2 | 9165: POP | 9166: PUSH2 0x4622 | 9169: JUMP
9170: JUMPDEST | 9171: DUP4 | 9172: GT | 9173: CODESIZE | 9174: PUSH2 0x184c | 9177: JUMP
9178: JUMPDEST | 9179: POP | 9180: CALLVALUE | 9181: PUSH2 0x0582 | 9184: JUMPI
9185: PUSH1 0x80 | 9187: CALLDATASIZE | 9188: PUSH1 0x03 | 9190: NOT | 9191: ADD | 9192: SLT | 9193: PUSH2 0x0582 | 9196: JUMPI
9197: PUSH1 0x04 | 9199: CALLDATALOAD | 9200: PUSH2 0x18ee | 9203: DUP2 | 9204: PUSH2 0x0571 | 9207: JUMP
9208: JUMPDEST | 9209: PUSH1 0x64 | 9211: CALLDATALOAD | 9212: SWAP1 | 9213: PUSH2 0x18fb | 9216: DUP3 | 9217: PUSH2 0x0571 | 9220: JUMP
9221: JUMPDEST | 9222: PUSH2 0x1903 | 9225: PUSH2 0x2fd5 | 9228: JUMP
9229: JUMPDEST | 9230: PUSH1 0x10 | 9232: PUSH1 0x01 | 9234: SLOAD | 9235: PUSH1 0xf8 | 9237: SHR | 9238: AND | 9239: PUSH2 0x1a47 | 9242: JUMPI
9243: PUSH2 0x1918 | 9246: PUSH2 0x2661 | 9249: JUMP
9250: JUMPDEST | 9251: PUSH1 0x00 | 9253: DUP2 | 9254: SLT | 9255: ISZERO | 9256: SWAP1 | 9257: DUP2 | 9258: PUSH2 0x1a1c | 9261: JUMPI
9262: JUMPDEST | 9263: POP | 9264: PUSH2 0x1a0a | 9267: JUMPI
9268: PUSH2 0x1956 | 9271: PUSH1 0x44 | 9273: CALLDATALOAD | 9274: CALLER | 9275: PUSH32 0x0000000000000000000000000000000000000000000000000000000000000000 | 9308: PUSH2 0x33d8 | 9311: JUMP
9312: JUMPDEST | 9313: SWAP1 | 9314: PUSH2 0x1961 | 9317: DUP3 | 9318: DUP3 | 9319: PUSH2 0x462d | 9322: JUMP
9323: JUMPDEST | 9324: SWAP3 | 9325: PUSH1 0x24 | 9327: CALLDATALOAD | 9328: DUP5 | 9329: LT | 9330: PUSH2 0x19f8 | 9333: JUMPI
9334: PUSH2 0x1974 | 9337: DUP3 | 9338: PUSH2 0x2559 | 9341: JUMP
9342: JUMPDEST | 9343: DUP5 | 9344: GT | 9345: PUSH2 0x18ac | 9348: JUMPI
9349: PUSH32 0xf891b2a411b0e66a5f0a6ff1368670fefa287a13f541eb633a386a1a9cc7046b | 9382: SWAP2 | 9383: PUSH2 0x19bb | 9386: PUSH2 0x19de | 9389: SWAP3 | 9390: PUSH2 0x19b4 | 9393: PUSH2 0x19af | 9396: DUP9 | 9397: PUSH2 0x2faf | 9400: JUMP
9401: JUMPDEST | 9402: PUSH2 0x0993 | 9405: JUMP
9406: JUMPDEST | 9407: SWAP1 | 9408: DUP4 | 9409: PUSH2 0x3ef1 | 9412: JUMP
9413: JUMPDEST | 9414: PUSH1 0x40 | 9416: DUP1 | 9417: MLOAD | 9418: SWAP5 | 9419: DUP6 | 9420: MSTORE | 9421: PUSH1 0x20 | 9423: DUP6 | 9424: ADD | 9425: SWAP6 | 9426: SWAP1 | 9427: SWAP6 | 9428: MSTORE | 9429: PUSH1 0x01 | 9431: PUSH1 0x01 | 9433: PUSH1 0xa0 | 9435: SHL | 9436: SUB | 9437: AND | 9438: SWAP4 | 9439: CALLER | 9440: SWAP4 | 9441: SWAP2 | 9442: DUP3 | 9443: SWAP2 | 9444: DUP3 | 9445: ADD | 9446: SWAP1 | 9447: JUMP
9448: JUMPDEST | 9449: SUB | 9450: SWAP1 | 9451: LOG3 | 9452: PUSH2 0x0016 | 9455: PUSH1 0x00 | 9457: PUSH1 0x00 | 9459: DUP1 | 9460: MLOAD | 9461: PUSH1 0x20 | 9463: PUSH2 0x4852 | 9466: DUP4 | 9467: CODECOPY | 9468: DUP2 | 9469: MLOAD | 9470: SWAP2 | 9471: MSTORE | 9472: SSTORE | 9473: JUMP
9474: JUMPDEST | 9475: PUSH1 0x40 | 9477: MLOAD | 9478: PUSH4 0xfa6ad355 | 9483: PUSH1 0xe0 | 9485: SHL | 9486: DUP2 | 9487: MSTORE | 9488: PUSH1 0x04 | 9490: SWAP1 | 9491: REVERT
9492: JUMPDEST | 9493: PUSH1 0x40 | 9495: MLOAD | 9496: PUSH4 0x1d99ddbf | 9501: PUSH1 0xe0 | 9503: SHL | 9504: DUP2 | 9505: MSTORE | 9506: PUSH1 0x04 | 9508: SWAP1 | 9509: REVERT
9510: JUMPDEST | 9511: SWAP1 | 9512: POP | 9513: PUSH32 0x0000000000000000000000000000000000000000000000000000000000000000 | 9546: GT | 9547: ISZERO | 9548: CODESIZE | 9549: PUSH2 0x1924 | 9552: JUMP
9553: JUMPDEST | 9554: PUSH1 0x40 | 9556: MLOAD | 9557: PUSH4 0x13d0ff59 | 9562: PUSH1 0xe3 | 9564: SHL | 9565: DUP2 | 9566: MSTORE | 9567: PUSH1 0x04 | 9569: SWAP1 | 9570: REVERT
9571: JUMPDEST | 9572: POP | 9573: CALLVALUE | 9574: PUSH2 0x0582 | 9577: JUMPI
9578: PUSH1 0x00 | 9580: CALLDATASIZE | 9581: PUSH1 0x03 | 9583: NOT | 9584: ADD | 9585: SLT | 9586: PUSH2 0x0582 | 9589: JUMPI
9590: PUSH1 0x40 | 9592: MLOAD | 9593: PUSH32 0x0000000000000000000000000000000000000000000000000000000000000000 | 9626: PUSH1 0x01 | 9628: PUSH1 0x01 | 9630: PUSH1 0xa0 | 9632: SHL | 9633: SUB | 9634: AND | 9635: DUP2 | 9636: MSTORE | 9637: PUSH1 0x20 | 9639: SWAP1 | 9640: RETURN
9641: JUMPDEST | 9642: POP | 9643: CALLVALUE | 9644: PUSH2 0x0582 | 9647: JUMPI
9648: PUSH1 0x40 | 9650: CALLDATASIZE | 9651: PUSH1 0x03 | 9653: NOT | 9654: ADD | 9655: SLT | 9656: PUSH2 0x0582 | 9659: JUMPI
9660: PUSH2 0x0904 | 9663: PUSH1 0x04 | 9665: CALLDATALOAD | 9666: PUSH2 0x1ac0 | 9669: DUP2 | 9670: PUSH2 0x0571 | 9673: JUMP
9674: JUMPDEST | 9675: PUSH2 0x1ac8 | 9678: PUSH2 0x2fd5 | 9681: JUMP
9682: JUMPDEST | 9683: PUSH1 0x24 | 9685: CALLDATALOAD | 9686: SWAP1 | 9687: CALLER | 9688: CALLER | 9689: CALLER | 9690: PUSH2 0x2f23 | 9693: JUMP
9694: JUMPDEST | 9695: POP | 9696: CALLVALUE | 9697: PUSH2 0x0582 | 9700: JUMPI
9701: PUSH1 0x40 | 9703: CALLDATASIZE | 9704: PUSH1 0x03 | 9706: NOT | 9707: ADD | 9708: SLT | 9709: PUSH2 0x0582 | 9712: JUMPI
9713: PUSH2 0x0904 | 9716: PUSH1 0x04 | 9718: CALLDATALOAD | 9719: PUSH2 0x1af5 | 9722: DUP2 | 9723: PUSH2 0x0571 | 9726: JUMP
9727: JUMPDEST | 9728: PUSH2 0x1afd | 9731: PUSH2 0x2fd5 | 9734: JUMP
9735: JUMPDEST | 9736: PUSH1 0x24 | 9738: CALLDATALOAD | 9739: SWAP1 | 9740: CALLER | 9741: CALLER | 9742: CALLER | 9743: PUSH2 0x3ced | 9746: JUMP
9747: JUMPDEST | 9748: PUSH1 0x01 | 9750: PUSH1 0x01 | 9752: PUSH1 0xa0 | 9754: SHL | 9755: SUB | 9756: DUP1 | 9757: DUP4 | 9758: AND | 9759: SWAP2 | 9760: AND | 9761: SWAP1 | 9762: DUP2 | 9763: EQ | 9764: SWAP2 | 9765: SWAP1 | 9766: DUP3 | 9767: ISZERO | 9768: PUSH2 0x1b26 | 9771: JUMPI
9772: POP | 9773: POP | 9774: SWAP1 | 9775: JUMP
9776: JUMPDEST | 9777: PUSH1 0xff | 9779: SWAP3 | 9780: POP | 9781: SWAP1 | 9782: PUSH2 0x1b41 | 9785: SWAP2 | 9786: PUSH1 0x00 | 9788: MSTORE | 9789: PUSH1 0x03 | 9791: PUSH1 0x20 | 9793: MSTORE | 9794: PUSH1 0x40 | 9796: PUSH1 0x00 | 9798: KECCAK256 | 9799: PUSH2 0x097c | 9802: JUMP
9803: JUMPDEST | 9804: SLOAD | 9805: AND | 9806: SWAP1 | 9807: JUMP
9808: JUMPDEST | 9809: PUSH1 0x1f | 9811: SWAP1 | 9812: SWAP2 | 9813: ADD | 9814: PUSH1 0x1f | 9816: NOT | 9817: AND | 9818: DUP2 | 9819: ADD | 9820: SWAP1 | 9821: PUSH1 0x01 | 9823: PUSH1 0x01 | 9825: PUSH1 0x40 | 9827: SHL | 9828: SUB | 9829: DUP3 | 9830: GT | 9831: SWAP1 | 9832: DUP3 | 9833: LT | 9834: OR | 9835: PUSH2 0x1b69 | 9838: JUMPI
9839: PUSH1 0x40 | 9841: MSTORE | 9842: JUMP
9843: JUMPDEST | 9844: PUSH4 0x4e487b71 | 9849: PUSH1 0xe0 | 9851: SHL | 9852: PUSH1 0x00 | 9854: MSTORE | 9855: PUSH1 0x41 | 9857: PUSH1 0x04 | 9859: MSTORE | 9860: PUSH1 0x24 | 9862: PUSH1 0x00 | 9864: REVERT
9865: JUMPDEST | 9866: PUSH1 0x40 | 9868: MLOAD | 9869: SWAP1 | 9870: PUSH2 0x1b8f | 9873: PUSH2 0x0100 | 9876: DUP4 | 9877: PUSH2 0x1b46 | 9880: JUMP
9881: JUMPDEST | 9882: DUP2 | 9883: PUSH1 0xe0 | 9885: PUSH1 0x00 | 9887: SWAP2 | 9888: DUP3 | 9889: DUP2 | 9890: MSTORE | 9891: DUP3 | 9892: PUSH1 0x20 | 9894: DUP3 | 9895: ADD | 9896: MSTORE | 9897: DUP3 | 9898: PUSH1 0x40 | 9900: DUP3 | 9901: ADD | 9902: MSTORE | 9903: DUP3 | 9904: PUSH1 0x60 | 9906: DUP3 | 9907: ADD | 9908: MSTORE | 9909: DUP3 | 9910: PUSH1 0x80 | 9912: DUP3 | 9913: ADD | 9914: MSTORE | 9915: DUP3 | 9916: PUSH1 0xa0 | 9918: DUP3 | 9919: ADD | 9920: MSTORE | 9921: DUP3 | 9922: PUSH1 0xc0 | 9924: DUP3 | 9925: ADD | 9926: MSTORE | 9927: ADD | 9928: MSTORE | 9929: JUMP
9930: JUMPDEST | 9931: MLOAD | 9932: SWAP1 | 9933: PUSH2 0x0c31 | 9936: DUP3 | 9937: PUSH2 0x1696 | 9940: JUMP
9941: JUMPDEST | 9942: MLOAD | 9943: SWAP1 | 9944: PUSH2 0x0c31 | 9947: DUP3 | 9948: PUSH2 0x0571 | 9951: JUMP
9952: JUMPDEST | 9953: MLOAD | 9954: SWAP1 | 9955: PUSH1 0x01 | 9957: PUSH1 0x01 | 9959: PUSH1 0x40 | 9961: SHL | 9962: SUB | 9963: DUP3 | 9964: AND | 9965: DUP3 | 9966: SUB | 9967: PUSH2 0x0582 | 9970: JUMPI
9971: JUMP
9972: JUMPDEST | 9973: MLOAD | 9974: SWAP1 | 9975: PUSH1 0x01 | 9977: PUSH1 0x01 | 9979: PUSH1 0x80 | 9981: SHL | 9982: SUB | 9983: DUP3 | 9984: AND | 9985: DUP3 | 9986: SUB | 9987: PUSH2 0x0582 | 9990: JUMPI
9991: JUMP
9992: JUMPDEST | 9993: POP | 9994: PUSH1 0x40 | 9996: MLOAD | 9997: RETURNDATASIZE | 9998: PUSH1 0x00 | 10000: DUP3 | 10001: RETURNDATACOPY | 10002: RETURNDATASIZE | 10003: SWAP1 | 10004: REVERT
10005: JUMPDEST | 10006: PUSH2 0x1c13 | 10009: PUSH2 0x1b7f | 10012: JUMP
10013: JUMPDEST | 10014: POP | 10015: PUSH1 0x40 | 10017: MLOAD | 10018: PUSH4 0xc8c7fe6b | 10023: PUSH1 0xe0 | 10025: SHL | 10026: DUP2 | 10027: MSTORE | 10028: PUSH1 0xff | 10030: SWAP2 | 10031: SWAP1 | 10032: SWAP2 | 10033: AND | 10034: PUSH1 0x04 | 10036: DUP3 | 10037: ADD | 10038: MSTORE | 10039: PUSH2 0x0100 | 10042: DUP1 | 10043: DUP3 | 10044: PUSH1 0x24 | 10046: DUP2 | 10047: PUSH32 0x0000000000000000000000000000000000000000000000000000000000000000 | 10080: PUSH1 0x01 | 10082: PUSH1 0x01 | 10084: PUSH1 0xa0 | 10086: SHL | 10087: SUB | 10088: AND | 10089: GAS | 10090: STATICCALL | 10091: SWAP2 | 10092: DUP3 | 10093: ISZERO | 10094: PUSH2 0x1d2d | 10097: JUMPI
10098: JUMPDEST | 10099: PUSH1 0x00 | 10101: SWAP3 | 10102: PUSH2 0x1c74 | 10105: JUMPI
10106: POP | 10107: POP | 10108: SWAP1 | 10109: JUMP
10110: JUMPDEST | 10111: SWAP1 | 10112: SWAP2 | 10113: DUP3 | 10114: DUP3 | 10115: DUP2 | 10116: RETURNDATASIZE | 10117: DUP4 | 10118: GT | 10119: PUSH2 0x1d26 | 10122: JUMPI
10123: JUMPDEST | 10124: PUSH2 0x1c8b | 10127: DUP2 | 10128: DUP4 | 10129: PUSH2 0x1b46 | 10132: JUMP
10133: JUMPDEST | 10134: DUP2 | 10135: ADD | 10136: SUB | 10137: SLT | 10138: PUSH2 0x0792 | 10141: JUMPI
10142: POP | 10143: PUSH1 0xe0 | 10145: PUSH2 0x1d1e | 10148: SWAP2 | 10149: PUSH2 0x1ca7 | 10152: PUSH1 0x40 | 10154: MLOAD | 10155: SWAP5 | 10156: DUP6 | 10157: PUSH2 0x1b46 | 10160: JUMP
10161: JUMPDEST | 10162: PUSH2 0x1cb0 | 10165: DUP2 | 10166: PUSH2 0x1bc0 | 10169: JUMP
10170: JUMPDEST | 10171: DUP5 | 10172: MSTORE | 10173: PUSH2 0x1cbe | 10176: PUSH1 0x20 | 10178: DUP3 | 10179: ADD | 10180: PUSH2 0x1bcb | 10183: JUMP
10184: JUMPDEST | 10185: PUSH1 0x20 | 10187: DUP6 | 10188: ADD | 10189: MSTORE | 10190: PUSH2 0x1ccf | 10193: PUSH1 0x40 | 10195: DUP3 | 10196: ADD | 10197: PUSH2 0x1bcb | 10200: JUMP
10201: JUMPDEST | 10202: PUSH1 0x40 | 10204: DUP6 | 10205: ADD | 10206: MSTORE | 10207: PUSH2 0x1ce0 | 10210: PUSH1 0x60 | 10212: DUP3 | 10213: ADD | 10214: PUSH2 0x1bd6 | 10217: JUMP
10218: JUMPDEST | 10219: PUSH1 0x60 | 10221: DUP6 | 10222: ADD | 10223: MSTORE | 10224: PUSH2 0x1cf1 | 10227: PUSH1 0x80 | 10229: DUP3 | 10230: ADD | 10231: PUSH2 0x1bd6 | 10234: JUMP
10235: JUMPDEST | 10236: PUSH1 0x80 | 10238: DUP6 | 10239: ADD | 10240: MSTORE | 10241: PUSH2 0x1d02 | 10244: PUSH1 0xa0 | 10246: DUP3 | 10247: ADD | 10248: PUSH2 0x1bd6 | 10251: JUMP
10252: JUMPDEST | 10253: PUSH1 0xa0 | 10255: DUP6 | 10256: ADD | 10257: MSTORE | 10258: PUSH2 0x1d13 | 10261: PUSH1 0xc0 | 10263: DUP3 | 10264: ADD | 10265: PUSH2 0x1bd6 | 10268: JUMP
10269: JUMPDEST | 10270: PUSH1 0xc0 | 10272: DUP6 | 10273: ADD | 10274: MSTORE | 10275: ADD | 10276: PUSH2 0x1bea | 10279: JUMP
10280: JUMPDEST | 10281: PUSH1 0xe0 | 10283: DUP3 | 10284: ADD | 10285: MSTORE | 10286: SWAP1 | 10287: JUMP
10288: JUMPDEST | 10289: POP | 10290: RETURNDATASIZE | 10291: PUSH2 0x1c81 | 10294: JUMP
10295: JUMPDEST | 10296: PUSH2 0x1d35 | 10299: PUSH2 0x1bfe | 10302: JUMP
10303: JUMPDEST | 10304: PUSH2 0x1c68 | 10307: JUMP
10308: JUMPDEST | 10309: SWAP1 | 10310: PUSH2 0x1d43 | 10313: PUSH2 0x1b7f | 10316: JUMP
10317: JUMPDEST | 10318: POP | 10319: PUSH1 0x00 | 10321: SWAP1 | 10322: PUSH1 0xff | 10324: SWAP3 | 10325: DUP4 | 10326: PUSH32 0x0000000000000000000000000000000000000000000000000000000000000000 | 10359: AND | 10360: SWAP3
10361: JUMPDEST | 10362: DUP4 | 10363: DUP6 | 10364: DUP3 | 10365: AND | 10366: LT | 10367: PUSH2 0x1d8a | 10370: JUMPI
10371: PUSH1 0x40 | 10373: MLOAD | 10374: PUSH4 0x36405305 | 10379: PUSH1 0xe0 | 10381: SHL | 10382: DUP2 | 10383: MSTORE | 10384: PUSH1 0x04 | 10386: SWAP1 | 10387: REVERT
10388: JUMPDEST | 10389: PUSH2 0x1d93 | 10392: DUP2 | 10393: PUSH2 0x1c0b | 10396: JUMP
10397: JUMPDEST | 10398: PUSH1 0x20 | 10400: DUP2 | 10401: ADD | 10402: MLOAD | 10403: PUSH1 0x01 | 10405: PUSH1 0x01 | 10407: PUSH1 0xa0 | 10409: SHL | 10410: SUB | 10411: DUP5 | 10412: DUP2 | 10413: AND | 10414: SWAP2 | 10415: AND | 10416: EQ | 10417: PUSH2 0x1db5 | 10420: JUMPI
10421: POP | 10422: PUSH1 0x01 | 10424: ADD | 10425: DUP5 | 10426: AND | 10427: PUSH2 0x1d6f | 10430: JUMP
10431: JUMPDEST | 10432: SWAP4 | 10433: POP | 10434: POP | 10435: POP | 10436: SWAP2 | 10437: POP | 10438: SWAP1 | 10439: JUMP
10440: JUMPDEST | 10441: PUSH1 0x01 | 10443: PUSH1 0x28 | 10445: SHL | 10446: TIMESTAMP | 10447: LT | 10448: ISZERO | 10449: PUSH2 0x1dd5 | 10452: JUMPI
10453: PUSH5 0xffffffffff | 10459: TIMESTAMP | 10460: AND | 10461: SWAP1 | 10462: JUMP
10463: JUMPDEST | 10464: PUSH1 0x40 | 10466: MLOAD | 10467: PUSH4 0x3d32ffdb | 10472: PUSH1 0xe0 | 10474: SHL | 10475: DUP2 | 10476: MSTORE | 10477: PUSH1 0x04 | 10479: SWAP1 | 10480: REVERT
10481: JUMPDEST | 10482: SWAP1 | 10483: PUSH1 0x40 | 10485: MLOAD | 10486: PUSH2 0x1df6 | 10489: PUSH1 0xa0 | 10491: DUP3 | 10492: PUSH2 0x1b46 | 10495: JUMP
10496: JUMPDEST | 10497: PUSH1 0x80 | 10499: DUP2 | 10500: SWAP4 | 10501: SLOAD | 10502: DUP1 | 10503: PUSH1 0x0c | 10505: SIGNEXTEND | 10506: DUP4 | 10507: MSTORE | 10508: PUSH1 0x01 | 10510: DUP1 | 10511: PUSH1 0x40 | 10513: SHL | 10514: SUB | 10515: DUP1 | 10516: DUP3 | 10517: PUSH1 0x68 | 10519: SHR | 10520: AND | 10521: PUSH1 0x20 | 10523: DUP6 | 10524: ADD | 10525: MSTORE | 10526: DUP2 | 10527: PUSH1 0xa8 | 10529: SHR | 10530: AND | 10531: PUSH1 0x40 | 10533: DUP5 | 10534: ADD | 10535: MSTORE | 10536: PUSH2 0xffff | 10539: DUP2 | 10540: PUSH1 0xe8 | 10542: SHR | 10543: AND | 10544: PUSH1 0x60 | 10546: DUP5 | 10547: ADD | 10548: MSTORE | 10549: PUSH1 0xf8 | 10551: SHR | 10552: SWAP2 | 10553: ADD | 10554: MSTORE | 10555: JUMP
10556: JUMPDEST | 10557: POP | 10558: PUSH4 0x4e487b71 | 10563: PUSH1 0xe0 | 10565: SHL | 10566: PUSH1 0x00 | 10568: MSTORE | 10569: PUSH1 0x11 | 10571: PUSH1 0x04 | 10573: MSTORE | 10574: PUSH1 0x24 | 10576: PUSH1 0x00 | 10578: REVERT
10579: JUMPDEST | 10580: PUSH5 0xffffffffff | 10586: SWAP2 | 10587: DUP3 | 10588: AND | 10589: SWAP2 | 10590: AND | 10591: DUP2 | 10592: DUP2 | 10593: LT | 10594: PUSH2 0x1e5f | 10597: JUMPI
10598: SUB | 10599: SWAP1 | 10600: JUMP
10601: JUMPDEST | 10602: PUSH2 0x1e67 | 10605: PUSH2 0x1e32 | 10608: JUMP
10609: JUMPDEST | 10610: SUB | 10611: SWAP1 | 10612: JUMP
10613: JUMPDEST | 10614: PUSH1 0x01 | 10616: PUSH1 0x01 | 10618: PUSH1 0x68 | 10620: SHL | 10621: SUB | 10622: AND | 10623: SWAP1 | 10624: JUMP
10625: JUMPDEST | 10626: DUP1 | 10627: PUSH1 0x00 | 10629: NOT | 10630: DIV | 10631: DUP3 | 10632: GT | 10633: DUP2 | 10634: ISZERO | 10635: ISZERO | 10636: AND | 10637: PUSH2 0x1e8a | 10640: JUMPI
10641: MUL | 10642: SWAP1 | 10643: JUMP
10644: JUMPDEST | 10645: PUSH2 0x1e92 | 10648: PUSH2 0x1e32 | 10651: JUMP
10652: JUMPDEST | 10653: MUL | 10654: SWAP1 | 10655: JUMP
10656: JUMPDEST | 10657: PUSH1 0x01 | 10659: PUSH1 0x01 | 10661: PUSH1 0x40 | 10663: SHL | 10664: SUB | 10665: SWAP2 | 10666: DUP3 | 10667: AND | 10668: SWAP2 | 10669: SWAP1 | 10670: DUP2 | 10671: AND | 10672: SWAP1 | 10673: DUP3 | 10674: SWAP1 | 10675: SUB | 10676: DUP2 | 10677: GT | 10678: PUSH2 0x1eb3 | 10681: JUMPI
10682: ADD | 10683: SWAP1 | 10684: JUMP
10685: JUMPDEST | 10686: PUSH2 0x1ebb | 10689: PUSH2 0x1e32 | 10692: JUMP
10693: JUMPDEST | 10694: ADD | 10695: SWAP1 | 10696: JUMP
10697: JUMPDEST | 10698: PUSH1 0x68 | 10700: SHR | 10701: PUSH1 0x01 | 10703: PUSH1 0x01 | 10705: PUSH1 0x68 | 10707: SHL | 10708: SUB | 10709: AND | 10710: SWAP1 | 10711: JUMP
10712: JUMPDEST | 10713: PUSH2 0x1ed6 | 10716: PUSH2 0x1dbe | 10719: JUMP
10720: JUMPDEST | 10721: PUSH2 0x1f00 | 10724: PUSH2 0x1ef6 | 10727: PUSH2 0x1ef0 | 10730: PUSH1 0x01 | 10732: SLOAD | 10733: PUSH5 0xffffffffff | 10739: SWAP1 | 10740: PUSH1 0xd0 | 10742: SHR | 10743: AND | 10744: SWAP1 | 10745: JUMP
10746: JUMPDEST | 10747: DUP4 | 10748: PUSH2 0x1e49 | 10751: JUMP
10752: JUMPDEST | 10753: PUSH5 0xffffffffff | 10759: AND | 10760: SWAP1 | 10761: JUMP
10762: JUMPDEST | 10763: SWAP1 | 10764: DUP2 | 10765: PUSH2 0x1f0a | 10768: JUMPI
10769: POP | 10770: POP | 10771: JUMP
10772: JUMPDEST | 10773: DUP2 | 10774: PUSH2 0x1f61 | 10777: PUSH2 0x1f1a | 10780: PUSH2 0x0c31 | 10783: SWAP5 | 10784: PUSH2 0x20fd | 10787: JUMP
10788: JUMPDEST | 10789: PUSH1 0x00 | 10791: DUP1 | 10792: SLOAD | 10793: PUSH1 0x01 | 10795: PUSH1 0x40 | 10797: SHL | 10798: PUSH1 0x01 | 10800: PUSH1 0x80 | 10802: SHL | 10803: SUB | 10804: NOT | 10805: AND | 10806: PUSH1 0x40 | 10808: SWAP3 | 10809: SWAP1 | 10810: SWAP3 | 10811: SHL | 10812: PUSH1 0x01 | 10814: PUSH1 0x40 | 10816: SHL | 10817: PUSH1 0x01 | 10819: PUSH1 0x80 | 10821: SHL | 10822: SUB | 10823: AND | 10824: SWAP2 | 10825: SWAP1 | 10826: SWAP2 | 10827: OR | 10828: DUP2 | 10829: SSTORE | 10830: SWAP2 | 10831: SWAP1 | 10832: DUP3 | 10833: SLOAD | 10834: PUSH1 0x01 | 10836: PUSH1 0x01 | 10838: PUSH1 0x40 | 10840: SHL | 10841: SUB | 10842: NOT | 10843: AND | 10844: PUSH1 0x01 | 10846: PUSH1 0x01 | 10848: PUSH1 0x40 | 10850: SHL | 10851: SUB | 10852: SWAP1 | 10853: SWAP2 | 10854: AND | 10855: OR | 10856: DUP3 | 10857: SSTORE | 10858: JUMP
10859: JUMPDEST | 10860: PUSH2 0x1f6c | 10863: PUSH1 0x01 | 10865: SLOAD | 10866: PUSH2 0x1e6b | 10869: JUMP
10870: JUMPDEST | 10871: PUSH32 0x0000000000000000000000000000000000000000000000000000000000000000 | 10904: SWAP3 | 10905: SWAP1 | 10906: PUSH1 0x01 | 10908: PUSH1 0x01 | 10910: PUSH1 0x68 | 10912: SHL | 10913: SUB | 10914: AND | 10915: DUP4 | 10916: DUP2 | 10917: LT | 10918: ISZERO | 10919: PUSH2 0x2061 | 10922: JUMPI
10923: JUMPDEST | 10924: POP | 10925: PUSH2 0x1fb5 | 10928: PUSH2 0x1fb0 | 10931: PUSH1 0x01 | 10933: SLOAD | 10934: PUSH2 0x1ebf | 10937: JUMP
10938: JUMPDEST | 10939: PUSH2 0x1e6b | 10942: JUMP
10943: JUMPDEST | 10944: SWAP3 | 10945: DUP4 | 10946: LT | 10947: ISZERO | 10948: PUSH2 0x1fe9 | 10951: JUMPI
10952: JUMPDEST | 10953: POP | 10954: POP | 10955: PUSH1 0x01 | 10957: DUP1 | 10958: SLOAD | 10959: PUSH5 0xffffffffff | 10965: PUSH1 0xd0 | 10967: SHL | 10968: NOT | 10969: AND | 10970: PUSH1 0xd0 | 10972: SWAP4 | 10973: SWAP1 | 10974: SWAP4 | 10975: SHL | 10976: PUSH5 0xffffffffff | 10982: PUSH1 0xd0 | 10984: SHL | 10985: AND | 10986: SWAP3 | 10987: SWAP1 | 10988: SWAP3 | 10989: OR | 10990: SWAP1 | 10991: SWAP2 | 10992: SSTORE | 10993: POP | 10994: JUMP
10995: JUMPDEST | 10996: PUSH2 0x202a | 10999: PUSH2 0x2025 | 11002: PUSH2 0x2059 | 11005: SWAP5 | 11006: PUSH2 0x2020 | 11009: PUSH2 0x2039 | 11012: SWAP5 | 11013: PUSH32 0x0000000000000000000000000000000000000000000000000000000000000000 | 11046: PUSH2 0x1e77 | 11049: JUMP
11050: JUMPDEST | 11051: PUSH2 0x2b8f | 11054: JUMP
11055: JUMPDEST | 11056: PUSH2 0x20d7 | 11059: JUMP
11060: JUMPDEST | 11061: DUP3 | 11062: SLOAD | 11063: PUSH1 0xc0 | 11065: SHR | 11066: PUSH2 0x1e96 | 11069: JUMP
11070: JUMPDEST | 11071: PUSH2 0x1e96 | 11074: JUMP
11075: JUMPDEST | 11076: DUP2 | 11077: SLOAD | 11078: PUSH1 0x01 | 11080: PUSH1 0x01 | 11082: PUSH1 0xc0 | 11084: SHL | 11085: SUB | 11086: AND | 11087: PUSH1 0xc0 | 11089: SWAP2 | 11090: SWAP1 | 11091: SWAP2 | 11092: SHL | 11093: PUSH1 0x01 | 11095: PUSH1 0x01 | 11097: PUSH1 0xc0 | 11099: SHL | 11100: SUB | 11101: NOT | 11102: AND | 11103: OR | 11104: SWAP1 | 11105: SSTORE | 11106: JUMP
11107: JUMPDEST | 11108: CODESIZE | 11109: DUP1 | 11110: DUP1 | 11111: PUSH2 0x1fbe | 11114: JUMP
11115: JUMPDEST | 11116: PUSH2 0x20ab | 11119: PUSH2 0x2098 | 11122: PUSH2 0x2025 | 11125: PUSH2 0x20d1 | 11128: SWAP4 | 11129: PUSH2 0x2020 | 11132: DUP7 | 11133: PUSH32 0x0000000000000000000000000000000000000000000000000000000000000000 | 11166: PUSH2 0x1e77 | 11169: JUMP
11170: JUMPDEST | 11171: DUP5 | 11172: SLOAD | 11173: PUSH1 0x80 | 11175: SHR | 11176: PUSH1 0x01 | 11178: PUSH1 0x01 | 11180: PUSH1 0x40 | 11182: SHL | 11183: SUB | 11184: AND | 11185: PUSH2 0x1e96 | 11188: JUMP
11189: JUMPDEST | 11190: DUP4 | 11191: SLOAD | 11192: PUSH1 0x01 | 11194: PUSH1 0x80 | 11196: SHL | 11197: PUSH1 0x01 | 11199: PUSH1 0xc0 | 11201: SHL | 11202: SUB | 11203: NOT | 11204: AND | 11205: PUSH1 0x80 | 11207: SWAP2 | 11208: SWAP1 | 11209: SWAP2 | 11210: SHL | 11211: PUSH1 0x01 | 11213: PUSH1 0x80 | 11215: SHL | 11216: PUSH1 0x01 | 11218: PUSH1 0xc0 | 11220: SHL | 11221: SUB | 11222: AND | 11223: OR | 11224: DUP4 | 11225: SSTORE | 11226: JUMP
11227: JUMPDEST | 11228: CODESIZE | 11229: PUSH2 0x1fa1 | 11232: JUMP
11233: JUMPDEST | 11234: PUSH1 0x01 | 11236: PUSH1 0x01 | 11238: PUSH1 0x40 | 11240: SHL | 11241: SUB | 11242: SWAP1 | 11243: DUP2 | 11244: DUP2 | 11245: GT | 11246: PUSH2 0x20eb | 11249: JUMPI
11250: AND | 11251: SWAP1 | 11252: JUMP
11253: JUMPDEST | 11254: PUSH1 0x40 | 11256: MLOAD | 11257: PUSH4 0x72a1cb51 | 11262: PUSH1 0xe1 | 11264: SHL | 11265: DUP2 | 11266: MSTORE | 11267: PUSH1 0x04 | 11269: SWAP1 | 11270: REVERT
11271: JUMPDEST | 11272: PUSH1 0x00 | 11274: SLOAD | 11275: PUSH1 0x01 | 11277: PUSH1 0x01 | 11279: PUSH1 0x40 | 11281: SHL | 11282: SUB | 11283: PUSH1 0x40 | 11285: DUP3 | 11286: SWAP1 | 11287: SHR | 11288: DUP2 | 11289: AND | 11290: SWAP4 | 11291: SWAP3 | 11292: SWAP2 | 11293: DUP2 | 11294: AND | 11295: SWAP2 | 11296: SWAP1 | 11297: DUP2 | 11298: PUSH2 0x2122 | 11301: JUMPI
11302: JUMPDEST | 11303: POP | 11304: POP | 11305: SWAP2 | 11306: SWAP1 | 11307: JUMP
11308: JUMPDEST | 11309: DUP2 | 11310: PUSH2 0x2175 | 11313: PUSH2 0x216f | 11316: PUSH2 0x214f | 11319: SWAP8 | 11320: SWAP5 | 11321: PUSH2 0x2181 | 11324: PUSH2 0x2187 | 11327: SWAP8 | 11328: PUSH2 0x217b | 11331: DUP8 | 11332: PUSH2 0x2156 | 11335: PUSH2 0x217b | 11338: SWAP10 | 11339: PUSH2 0x2148 | 11342: PUSH2 0x23ec | 11345: JUMP
11346: JUMPDEST | 11347: SWAP15 | 11348: DUP16 | 11349: PUSH2 0x21a6 | 11352: JUMP
11353: JUMPDEST | 11354: AND | 11355: SWAP14 | 11356: PUSH2 0x22b6 | 11359: JUMP
11360: JUMPDEST | 11361: AND | 11362: SWAP12 | 11363: PUSH2 0x2175 | 11366: PUSH2 0x216f | 11369: PUSH8 0x0de0b6b3a7640000 | 11378: SWAP10 | 11379: DUP11 | 11380: SWAP4 | 11381: PUSH2 0x1e77 | 11384: JUMP
11385: JUMPDEST | 11386: DUP5 | 11387: PUSH2 0x1e77 | 11390: JUMP
11391: JUMPDEST | 11392: DIV | 11393: PUSH2 0x20d7 | 11396: JUMP
11397: JUMPDEST | 11398: SWAP1 | 11399: PUSH2 0x1e96 | 11402: JUMP
11403: JUMPDEST | 11404: SWAP9 | 11405: PUSH2 0x1e77 | 11408: JUMP
11409: JUMPDEST | 11410: SWAP2 | 11411: CODESIZE | 11412: DUP1 | 11413: PUSH2 0x211c | 11416: JUMP
11417: JUMPDEST | 11418: DUP2 | 11419: NOT | 11420: DUP2 | 11421: GT | 11422: PUSH2 0x1eb3 | 11425: JUMPI
11426: ADD | 11427: SWAP1 | 11428: JUMP
11429: JUMPDEST | 11430: DUP2 | 11431: DUP2 | 11432: LT | 11433: PUSH2 0x1e5f | 11436: JUMPI
11437: SUB | 11438: SWAP1 | 11439: JUMP
11440: JUMPDEST | 11441: PUSH32 0x0000000000000000000000000000000000000000000000000000000000000000 | 11474: DUP1 | 11475: DUP3 | 11476: GT | 11477: PUSH2 0x222f | 11480: JUMPI
11481: POP | 11482: PUSH2 0x2025 | 11485: PUSH8 0x0de0b6b3a7640000 | 11494: PUSH2 0x2208 | 11497: PUSH2 0x0979 | 11500: SWAP4 | 11501: PUSH32 0x0000000000000000000000000000000000000000000000000000000000000000 | 11534: PUSH2 0x1e77 | 11537: JUMP
11538: JUMPDEST | 11539: DIV | 11540: PUSH32 0x0000000000000000000000000000000000000000000000000000000000000000 | 11573: PUSH2 0x218f | 11576: JUMP
11577: JUMPDEST | 11578: PUSH2 0x0979 | 11581: SWAP2 | 11582: PUSH2 0x2025 | 11585: SWAP2 | 11586: PUSH2 0x22a2 | 11589: PUSH8 0x0de0b6b3a7640000 | 11598: SWAP2 | 11599: PUSH2 0x2272 | 11602: DUP4 | 11603: PUSH2 0x2208 | 11606: DUP4 | 11607: PUSH32 0x0000000000000000000000000000000000000000000000000000000000000000 | 11640: PUSH2 0x1e77 | 11643: JUMP
11644: JUMPDEST | 11645: SWAP4 | 11646: DUP2 | 11647: DUP2 | 11648: LT | 11649: PUSH2 0x22a9 | 11652: JUMPI
11653: JUMPDEST | 11654: SUB | 11655: PUSH32 0x0000000000000000000000000000000000000000000000000000000000000000 | 11688: PUSH2 0x1e77 | 11691: JUMP
11692: JUMPDEST | 11693: DIV | 11694: SWAP1 | 11695: PUSH2 0x218f | 11698: JUMP
11699: JUMPDEST | 11700: PUSH2 0x22b1 | 11703: PUSH2 0x1e32 | 11706: JUMP
11707: JUMPDEST | 11708: PUSH2 0x227b | 11711: JUMP
11712: JUMPDEST | 11713: PUSH32 0x0000000000000000000000000000000000000000000000000000000000000000 | 11746: DUP1 | 11747: DUP3 | 11748: GT | 11749: PUSH2 0x233f | 11752: JUMPI
11753: POP | 11754: PUSH2 0x2025 | 11757: PUSH8 0x0de0b6b3a7640000 | 11766: PUSH2 0x2318 | 11769: PUSH2 0x0979 | 11772: SWAP4 | 11773: PUSH32 0x0000000000000000000000000000000000000000000000000000000000000000 | 11806: PUSH2 0x1e77 | 11809: JUMP
11810: JUMPDEST | 11811: DIV | 11812: PUSH32 0x0000000000000000000000000000000000000000000000000000000000000000 | 11845: PUSH2 0x218f | 11848: JUMP
11849: JUMPDEST | 11850: PUSH2 0x0979 | 11853: SWAP2 | 11854: PUSH2 0x2025 | 11857: SWAP2 | 11858: PUSH2 0x22a2 | 11861: PUSH8 0x0de0b6b3a7640000 | 11870: SWAP2 | 11871: PUSH2 0x2382 | 11874: DUP4 | 11875: PUSH2 0x2318 | 11878: DUP4 | 11879: PUSH32 0x0000000000000000000000000000000000000000000000000000000000000000 | 11912: PUSH2 0x1e77 | 11915: JUMP
11916: JUMPDEST | 11917: SWAP4 | 11918: DUP2 | 11919: DUP2 | 11920: LT | 11921: PUSH2 0x23b2 | 11924: JUMPI
11925: JUMPDEST | 11926: SUB | 11927: PUSH32 0x0000000000000000000000000000000000000000000000000000000000000000 | 11960: PUSH2 0x1e77 | 11963: JUMP
11964: JUMPDEST | 11965: PUSH2 0x23ba | 11968: PUSH2 0x1e32 | 11971: JUMP
11972: JUMPDEST | 11973: PUSH2 0x238b | 11976: JUMP
11977: JUMPDEST | 11978: POP | 11979: PUSH4 0x4e487b71 | 11984: PUSH1 0xe0 | 11986: SHL | 11987: PUSH1 0x00 | 11989: MSTORE | 11990: PUSH1 0x12 | 11992: PUSH1 0x04 | 11994: MSTORE | 11995: PUSH1 0x24 | 11997: PUSH1 0x00 | 11999: REVERT
12000: JUMPDEST | 12001: DUP2 | 12002: ISZERO | 12003: PUSH2 0x23e0 | 12006: JUMPI
12007: DIV | 12008: SWAP1 | 12009: JUMP
12010: JUMPDEST | 12011: PUSH2 0x23e8 | 12014: PUSH2 0x23bf | 12017: JUMP
12018: JUMPDEST | 12019: DIV | 12020: SWAP1 | 12021: JUMP
12022: JUMPDEST | 12023: PUSH1 0x00 | 12025: SLOAD | 12026: PUSH1 0x01 | 12028: SLOAD | 12029: PUSH7 0x038d7ea4c68000 | 12037: SWAP1 | 12038: PUSH2 0x242e | 12041: SWAP1 | 12042: PUSH1 0x01 | 12044: PUSH1 0x01 | 12046: PUSH1 0x68 | 12048: SHL | 12049: SUB | 12050: PUSH1 0x01 | 12052: PUSH1 0x01 | 12054: PUSH1 0x40 | 12056: SHL | 12057: SUB | 12058: DUP5 | 12059: PUSH2 0x241e | 12062: DUP3 | 12063: DUP9 | 12064: AND | 12065: DUP5 | 12066: DUP7 | 12067: AND | 12068: PUSH2 0x1e77 | 12071: JUMP
12072: JUMPDEST | 12073: DIV | 12074: SWAP6 | 12075: PUSH1 0x40 | 12077: SHR | 12078: AND | 12079: SWAP2 | 12080: PUSH1 0x68 | 12082: SHR | 12083: AND | 12084: PUSH2 0x1e77 | 12087: JUMP
12088: JUMPDEST | 12089: DIV | 12090: DUP2 | 12091: PUSH2 0x243b | 12094: JUMPI
12095: POP | 12096: POP | 12097: PUSH1 0x00 | 12099: SWAP1 | 12100: JUMP
12101: JUMPDEST | 12102: PUSH8 0x0de0b6b3a7640000 | 12111: SWAP1 | 12112: DUP1 | 12113: PUSH1 0x00 | 12115: NOT | 12116: DIV | 12117: DUP3 | 12118: GT | 12119: DUP2 | 12120: ISZERO | 12121: ISZERO | 12122: AND | 12123: PUSH2 0x2459 | 12126: JUMPI
12127: MUL | 12128: DIV | 12129: SWAP1 | 12130: JUMP
12131: JUMPDEST | 12132: PUSH2 0x2461 | 12135: PUSH2 0x1e32 | 12138: JUMP
12139: JUMPDEST | 12140: MUL | 12141: DIV | 12142: SWAP1 | 12143: JUMP
12144: JUMPDEST | 12145: PUSH7 0x038d7ea4c68000 | 12153: SWAP2 | 12154: PUSH2 0x23e8 | 12157: SWAP2 | 12158: PUSH1 0x01 | 12160: PUSH1 0x01 | 12162: PUSH1 0x40 | 12164: SHL | 12165: SUB | 12166: AND | 12167: SWAP1 | 12168: PUSH1 0x01 | 12170: PUSH1 0x01 | 12172: PUSH1 0x68 | 12174: SHL | 12175: SUB | 12176: AND | 12177: PUSH2 0x1e77 | 12180: JUMP
12181: JUMPDEST | 12182: MLOAD | 12183: SWAP1 | 12184: PUSH1 0x01 | 12186: PUSH1 0x01 | 12188: PUSH1 0x50 | 12190: SHL | 12191: SUB | 12192: DUP3 | 12193: AND | 12194: DUP3 | 12195: SUB | 12196: PUSH2 0x0582 | 12199: JUMPI
12200: JUMP
12201: JUMPDEST | 12202: PUSH1 0x40 | 12204: MLOAD | 12205: PUSH4 0x3fabe5a3 | 12210: PUSH1 0xe2 | 12212: SHL | 12213: DUP2 | 12214: MSTORE | 12215: SWAP1 | 12216: PUSH1 0xa0 | 12218: SWAP1 | 12219: DUP3 | 12220: SWAP1 | 12221: PUSH1 0x04 | 12223: SWAP1 | 12224: DUP3 | 12225: SWAP1 | 12226: PUSH1 0x01 | 12228: PUSH1 0x01 | 12230: PUSH1 0xa0 | 12232: SHL | 12233: SUB | 12234: AND | 12235: GAS | 12236: STATICCALL | 12237: SWAP1 | 12238: DUP2 | 12239: ISZERO | 12240: PUSH2 0x253d | 12243: JUMPI
12244: JUMPDEST | 12245: PUSH1 0x00 | 12247: SWAP2 | 12248: PUSH2 0x24f1 | 12251: JUMPI
12252: JUMPDEST | 12253: POP | 12254: PUSH1 0x00 | 12256: DUP2 | 12257: SGT | 12258: ISZERO | 12259: PUSH2 0x24df | 12262: JUMPI
12263: SWAP1 | 12264: JUMP
12265: JUMPDEST | 12266: PUSH1 0x40 | 12268: MLOAD | 12269: PUSH4 0xfd1ee349 | 12274: PUSH1 0xe0 | 12276: SHL | 12277: DUP2 | 12278: MSTORE | 12279: PUSH1 0x04 | 12281: SWAP1 | 12282: REVERT
12283: JUMPDEST | 12284: SWAP1 | 12285: PUSH1 0xa0 | 12287: DUP3 | 12288: RETURNDATASIZE | 12289: DUP3 | 12290: GT | 12291: PUSH2 0x2535 | 12294: JUMPI
12295: JUMPDEST | 12296: DUP2 | 12297: PUSH2 0x250a | 12300: PUSH1 0xa0 | 12302: SWAP4 | 12303: DUP4 | 12304: PUSH2 0x1b46 | 12307: JUMP
12308: JUMPDEST | 12309: DUP2 | 12310: ADD | 12311: SUB | 12312: SLT | 12313: PUSH2 0x0792 | 12316: JUMPI
12317: POP | 12318: PUSH2 0x251c | 12321: DUP2 | 12322: PUSH2 0x248b | 12325: JUMP
12326: JUMPDEST | 12327: POP | 12328: PUSH2 0x252e | 12331: PUSH1 0x80 | 12333: PUSH1 0x20 | 12335: DUP4 | 12336: ADD | 12337: MLOAD | 12338: SWAP3 | 12339: ADD | 12340: PUSH2 0x248b | 12343: JUMP
12344: JUMPDEST | 12345: POP | 12346: CODESIZE | 12347: PUSH2 0x24d2 | 12350: JUMP
12351: JUMPDEST | 12352: RETURNDATASIZE | 12353: SWAP2 | 12354: POP | 12355: PUSH2 0x24fd | 12358: JUMP
12359: JUMPDEST | 12360: PUSH2 0x2545 | 12363: PUSH2 0x1bfe | 12366: JUMP
12367: JUMPDEST | 12368: PUSH2 0x24ca | 12371: JUMP
12372: JUMPDEST | 12373: SWAP1 | 12374: DUP2 | 12375: PUSH1 0x20 | 12377: SWAP2 | 12378: SUB | 12379: SLT | 12380: PUSH2 0x0582 | 12383: JUMPI
12384: MLOAD | 12385: SWAP1 | 12386: JUMP
12387: JUMPDEST | 12388: PUSH1 0x40 | 12390: MLOAD | 12391: PUSH4 0x70a08231 | 12396: PUSH1 0xe0 | 12398: SHL | 12399: DUP2 | 12400: MSTORE | 12401: ADDRESS | 12402: PUSH1 0x04 | 12404: DUP3 | 12405: ADD | 12406: MSTORE | 12407: SWAP1 | 12408: PUSH1 0x01 | 12410: PUSH1 0x01 | 12412: PUSH1 0xa0 | 12414: SHL | 12415: SUB | 12416: AND | 12417: PUSH1 0x20 | 12419: DUP3 | 12420: PUSH1 0x24 | 12422: DUP2 | 12423: DUP5 | 12424: GAS | 12425: STATICCALL | 12426: SWAP2 | 12427: DUP3 | 12428: ISZERO | 12429: PUSH2 0x25e4 | 12432: JUMPI
12433: JUMPDEST | 12434: PUSH1 0x00 | 12436: SWAP3 | 12437: PUSH2 0x25b4 | 12440: JUMPI
12441: JUMPDEST | 12442: POP | 12443: PUSH1 0x00 | 12445: SWAP1 | 12446: DUP2 | 12447: MSTORE | 12448: PUSH1 0x02 | 12450: PUSH1 0x20 | 12452: MSTORE | 12453: PUSH1 0x40 | 12455: SWAP1 | 12456: KECCAK256 | 12457: SLOAD | 12458: PUSH1 0x01 | 12460: PUSH1 0x01 | 12462: PUSH1 0x80 | 12464: SHL | 12465: SUB | 12466: AND | 12467: SWAP1 | 12468: DUP2 | 12469: DUP2 | 12470: LT | 12471: PUSH2 0x1e5f | 12474: JUMPI
12475: SUB | 12476: SWAP1 | 12477: JUMP
12478: JUMPDEST | 12479: PUSH2 0x25d6 | 12482: SWAP2 | 12483: SWAP3 | 12484: POP | 12485: PUSH1 0x20 | 12487: RETURNDATASIZE | 12488: DUP2 | 12489: GT | 12490: PUSH2 0x25dd | 12493: JUMPI
12494: JUMPDEST | 12495: PUSH2 0x25ce | 12498: DUP2 | 12499: DUP4 | 12500: PUSH2 0x1b46 | 12503: JUMP
12504: JUMPDEST | 12505: DUP2 | 12506: ADD | 12507: SWAP1 | 12508: PUSH2 0x254a | 12511: JUMP
12512: JUMPDEST | 12513: SWAP1 | 12514: CODESIZE | 12515: PUSH2 0x258f | 12518: JUMP
12519: JUMPDEST | 12520: POP | 12521: RETURNDATASIZE | 12522: PUSH2 0x25c4 | 12525: JUMP
12526: JUMPDEST | 12527: PUSH2 0x25ec | 12530: PUSH2 0x1bfe | 12533: JUMP
12534: JUMPDEST | 12535: PUSH2 0x2587 | 12538: JUMP
12539: JUMPDEST | 12540: PUSH1 0x00 | 12542: DUP3 | 12543: SLT | 12544: DUP1 | 12545: ISZERO | 12546: PUSH1 0x01 | 12548: PUSH1 0xff | 12550: SHL | 12551: DUP5 | 12552: ADD | 12553: DUP4 | 12554: SLT | 12555: AND | 12556: PUSH2 0x261b | 12559: JUMPI
12560: JUMPDEST | 12561: PUSH1 0x01 | 12563: PUSH1 0x01 | 12565: PUSH1 0xff | 12567: SHL | 12568: SUB | 12569: DUP4 | 12570: ADD | 12571: DUP3 | 12572: SGT | 12573: AND | 12574: PUSH2 0x1e5f | 12577: JUMPI
12578: SUB | 12579: SWAP1 | 12580: JUMP
12581: JUMPDEST | 12582: PUSH2 0x2623 | 12585: PUSH2 0x1e32 | 12588: JUMP
12589: JUMPDEST | 12590: PUSH2 0x2606 | 12593: JUMP
12594: JUMPDEST | 12595: PUSH1 0x00 | 12597: DUP2 | 12598: SLT | 12599: DUP1 | 12600: ISZERO | 12601: PUSH1 0x01 | 12603: PUSH1 0x01 | 12605: PUSH1 0xff | 12607: SHL | 12608: SUB | 12609: DUP4 | 12610: SWAP1 | 12611: SUB | 12612: DUP5 | 12613: SGT | 12614: AND | 12615: PUSH2 0x2654 | 12618: JUMPI
12619: JUMPDEST | 12620: PUSH1 0x01 | 12622: PUSH1 0xff | 12624: SHL | 12625: DUP3 | 12626: SWAP1 | 12627: SUB | 12628: DUP4 | 12629: SLT | 12630: AND | 12631: PUSH2 0x1eb3 | 12634: JUMPI
12635: ADD | 12636: SWAP1 | 12637: JUMP
12638: JUMPDEST | 12639: PUSH2 0x265c | 12642: PUSH2 0x1e32 | 12645: JUMP
12646: JUMPDEST | 12647: PUSH2 0x2641 | 12650: JUMP
12651: JUMPDEST | 12652: PUSH2 0x0979 | 12655: PUSH2 0x266c | 12658: PUSH2 0x1dbe | 12661: JUMP
12662: JUMPDEST | 12663: PUSH2 0x268f | 12666: PUSH2 0x268a | 12669: PUSH2 0x1ef6 | 12672: PUSH1 0x01 | 12674: SLOAD | 12675: SWAP4 | 12676: PUSH5 0xffffffffff | 12682: DUP6 | 12683: PUSH1 0xd0 | 12685: SHR | 12686: AND | 12687: SWAP1 | 12688: PUSH2 0x1e49 | 12691: JUMP
12692: JUMPDEST | 12693: PUSH2 0x20fd | 12696: JUMP
12697: JUMPDEST | 12698: SWAP1 | 12699: PUSH1 0x40 | 12701: MLOAD | 12702: SWAP3 | 12703: PUSH4 0x70a08231 | 12708: PUSH1 0xe0 | 12710: SHL | 12711: DUP5 | 12712: MSTORE | 12713: PUSH1 0x20 | 12715: DUP5 | 12716: DUP1 | 12717: PUSH2 0x26af | 12720: ADDRESS | 12721: PUSH1 0x04 | 12723: DUP4 | 12724: ADD | 12725: PUSH2 0x060e | 12728: JUMP
12729: JUMPDEST | 12730: SUB | 12731: DUP2 | 12732: PUSH32 0x0000000000000000000000000000000000000000000000000000000000000000 | 12765: PUSH1 0x01 | 12767: PUSH1 0x01 | 12769: PUSH1 0xa0 | 12771: SHL | 12772: SUB | 12773: AND | 12774: GAS | 12775: STATICCALL | 12776: SWAP4 | 12777: DUP5 | 12778: ISZERO | 12779: PUSH2 0x2784 | 12782: JUMPI
12783: JUMPDEST | 12784: PUSH1 0x00 | 12786: SWAP5 | 12787: PUSH2 0x274c | 12790: JUMPI
12791: JUMPDEST | 12792: POP | 12793: SWAP2 | 12794: PUSH2 0x2740 | 12797: PUSH2 0x273a | 12800: PUSH2 0x273a | 12803: SWAP4 | 12804: PUSH2 0x2733 | 12807: PUSH2 0x2746 | 12810: SWAP7 | 12811: PUSH7 0x038d7ea4c68000 | 12819: SWAP3 | 12820: PUSH1 0x01 | 12822: DUP1 | 12823: PUSH1 0x40 | 12825: SHL | 12826: SUB | 12827: DUP5 | 12828: PUSH2 0x2726 | 12831: DUP3 | 12832: PUSH1 0x01 | 12834: DUP1 | 12835: PUSH1 0x68 | 12837: SHL | 12838: SUB | 12839: SWAP5 | 12840: AND | 12841: DUP5 | 12842: DUP7 | 12843: AND | 12844: PUSH2 0x1e77 | 12847: JUMP
12848: JUMPDEST | 12849: DIV | 12850: SWAP8 | 12851: AND | 12852: SWAP2 | 12853: PUSH1 0x68 | 12855: SHR | 12856: AND | 12857: PUSH2 0x1e77 | 12860: JUMP
12861: JUMPDEST | 12862: DIV | 12863: SWAP6 | 12864: PUSH2 0x2791 | 12867: JUMP
12868: JUMPDEST | 12869: SWAP2 | 12870: PUSH2 0x2791 | 12873: JUMP
12874: JUMPDEST | 12875: SWAP1 | 12876: PUSH2 0x25f1 | 12879: JUMP
12880: JUMPDEST | 12881: SWAP1 | 12882: PUSH2 0x2628 | 12885: JUMP
12886: JUMPDEST | 12887: PUSH2 0x2746 | 12890: SWAP4 | 12891: SWAP2 | 12892: SWAP5 | 12893: POP | 12894: PUSH2 0x273a | 12897: PUSH2 0x273a | 12900: SWAP4 | 12901: PUSH2 0x2733 | 12904: PUSH2 0x2777 | 12907: PUSH2 0x2740 | 12910: SWAP5 | 12911: PUSH1 0x20 | 12913: RETURNDATASIZE | 12914: DUP2 | 12915: GT | 12916: PUSH2 0x25dd | 12919: JUMPI
12920: PUSH2 0x25ce | 12923: DUP2 | 12924: DUP4 | 12925: PUSH2 0x1b46 | 12928: JUMP
12929: JUMPDEST | 12930: SWAP8 | 12931: SWAP5 | 12932: SWAP7 | 12933: POP | 12934: POP | 12935: SWAP4 | 12936: POP | 12937: POP | 12938: PUSH2 0x26ed | 12941: JUMP
12942: JUMPDEST | 12943: PUSH2 0x278c | 12946: PUSH2 0x1bfe | 12949: JUMP
12950: JUMPDEST | 12951: PUSH2 0x26e5 | 12954: JUMP
12955: JUMPDEST | 12956: PUSH1 0x01 | 12958: PUSH1 0x01 | 12960: PUSH1 0xff | 12962: SHL | 12963: SUB | 12964: DUP2 | 12965: GT | 12966: PUSH2 0x27a2 | 12969: JUMPI
12970: SWAP1 | 12971: JUMP
12972: JUMPDEST | 12973: PUSH1 0x40 | 12975: MLOAD | 12976: PUSH4 0xe7e828ad | 12981: PUSH1 0xe0 | 12983: SHL | 12984: DUP2 | 12985: MSTORE | 12986: PUSH1 0x04 | 12988: SWAP1 | 12989: REVERT
12990: JUMPDEST | 12991: PUSH2 0x27c9 | 12994: PUSH2 0x27c2 | 12997: DUP3 | 12998: PUSH1 0x05 | 13000: PUSH2 0x097c | 13003: JUMP
13004: JUMPDEST | 13005: SLOAD | 13006: PUSH1 0x0c | 13008: SIGNEXTEND | 13009: SWAP1 | 13010: JUMP
13011: JUMPDEST | 13012: SWAP1 | 13013: PUSH1 0x00 | 13015: SWAP2 | 13016: DUP3 | 13017: DUP2 | 13018: PUSH1 0x0c | 13020: SIGNEXTEND | 13021: SLT | 13022: ISZERO | 13023: PUSH2 0x2981 | 13026: JUMPI
13027: PUSH2 0x27f1 | 13030: PUSH2 0x27e6 | 13033: DUP4 | 13034: PUSH1 0x05 | 13036: PUSH2 0x097c | 13039: JUMP
13040: JUMPDEST | 13041: SLOAD | 13042: PUSH1 0xe8 | 13044: SHR | 13045: PUSH2 0xffff | 13048: AND | 13049: SWAP1 | 13050: JUMP
13051: JUMPDEST | 13052: SWAP1 | 13053: PUSH2 0x286c | 13056: PUSH2 0x2813 | 13059: PUSH2 0x280d | 13062: PUSH2 0x2806 | 13065: DUP7 | 13066: PUSH1 0x05 | 13068: PUSH2 0x097c | 13071: JUMP
13072: JUMPDEST | 13073: SLOAD | 13074: PUSH1 0xf8 | 13076: SHR | 13077: SWAP1 | 13078: JUMP
13079: JUMPDEST | 13080: SWAP3 | 13081: PUSH2 0x29c0 | 13084: JUMP
13085: JUMPDEST | 13086: PUSH2 0x283c | 13089: PUSH32 0x0000000000000000000000000000000000000000000000000000000000000000 | 13122: PUSH2 0x249f | 13125: JUMP
13126: JUMPDEST | 13127: PUSH32 0x0000000000000000000000000000000000000000000000000000000000000000 | 13160: PUSH1 0x01 | 13162: PUSH1 0x01 | 13164: PUSH1 0x40 | 13166: SHL | 13167: SUB | 13168: AND | 13169: SWAP2 | 13170: PUSH2 0x2bda | 13173: JUMP
13174: JUMPDEST | 13175: SWAP3 | 13176: DUP5 | 13177: SWAP2 | 13178: PUSH1 0xff | 13180: SWAP4 | 13181: DUP5 | 13182: PUSH32 0x0000000000000000000000000000000000000000000000000000000000000000 | 13215: AND | 13216: SWAP4
13217: JUMPDEST | 13218: DUP5 | 13219: DUP7 | 13220: DUP3 | 13221: AND | 13222: LT | 13223: PUSH2 0x28ab | 13226: JUMPI
13227: POP | 13228: POP | 13229: POP | 13230: POP | 13231: POP | 13232: POP | 13233: SLT | 13234: ISZERO | 13235: SWAP1 | 13236: JUMP
13237: JUMPDEST | 13238: PUSH2 0x28b6 | 13241: DUP4 | 13242: DUP3 | 13243: DUP5 | 13244: PUSH2 0x2cc0 | 13247: JUMP
13248: JUMPDEST | 13249: PUSH2 0x28c5 | 13252: JUMPI
13253: JUMPDEST | 13254: PUSH1 0x01 | 13256: ADD | 13257: DUP6 | 13258: AND | 13259: PUSH2 0x2897 | 13262: JUMP
13263: JUMPDEST | 13264: SWAP6 | 13265: DUP8 | 13266: DUP2 | 13267: SLT | 13268: ISZERO | 13269: PUSH2 0x2974 | 13272: JUMPI
13273: PUSH1 0x01 | 13275: PUSH2 0x296b | 13278: DUP8 | 13279: SWAP3 | 13280: PUSH2 0x2746 | 13283: PUSH2 0x2966 | 13286: DUP9 | 13287: PUSH2 0x2960 | 13290: PUSH2 0x295b | 13293: PUSH1 0x80 | 13295: DUP16 | 13296: PUSH2 0x2923 | 13299: PUSH2 0x2916 | 13302: PUSH2 0x2902 | 13305: PUSH2 0x28fa | 13308: PUSH2 0x2953 | 13311: SWAP5 | 13312: PUSH2 0x1c0b | 13315: JUMP
13316: JUMPDEST | 13317: SWAP8 | 13318: PUSH1 0x06 | 13320: PUSH2 0x097c | 13323: JUMP
13324: JUMPDEST | 13325: PUSH1 0x20 | 13327: DUP9 | 13328: ADD | 13329: MLOAD | 13330: PUSH1 0x01 | 13332: PUSH1 0x01 | 13334: PUSH1 0xa0 | 13336: SHL | 13337: SUB | 13338: AND | 13339: SWAP1 | 13340: PUSH2 0x097c | 13343: JUMP
13344: JUMPDEST | 13345: SLOAD | 13346: PUSH1 0x01 | 13348: PUSH1 0x01 | 13350: PUSH1 0x80 | 13352: SHL | 13353: SUB | 13354: AND | 13355: SWAP1 | 13356: JUMP
13357: JUMPDEST | 13358: PUSH1 0x40 | 13360: DUP7 | 13361: ADD | 13362: MLOAD | 13363: PUSH2 0x293a | 13366: SWAP1 | 13367: PUSH1 0x01 | 13369: PUSH1 0x01 | 13371: PUSH1 0xa0 | 13373: SHL | 13374: SUB | 13375: AND | 13376: PUSH2 0x249f | 13379: JUMP
13380: JUMPDEST | 13381: PUSH2 0x2947 | 13384: PUSH1 0x60 | 13386: DUP9 | 13387: ADD | 13388: MLOAD | 13389: PUSH2 0x0b8f | 13392: JUMP
13393: JUMPDEST | 13394: SWAP2 | 13395: DUP13 | 13396: DUP1 | 13397: DUP7 | 13398: SHL | 13399: SUB | 13400: AND | 13401: PUSH2 0x2bba | 13404: JUMP
13405: JUMPDEST | 13406: SWAP4 | 13407: ADD | 13408: MLOAD | 13409: PUSH2 0x0b8f | 13412: JUMP
13413: JUMPDEST | 13414: PUSH2 0x0b8f | 13417: JUMP
13418: JUMPDEST | 13419: SWAP1 | 13420: PUSH2 0x2b7c | 13423: JUMP
13424: JUMPDEST | 13425: PUSH2 0x2791 | 13428: JUMP
13429: JUMPDEST | 13430: SWAP8 | 13431: SWAP2 | 13432: POP | 13433: POP | 13434: PUSH2 0x28bb | 13437: JUMP
13438: JUMPDEST | 13439: POP | 13440: POP | 13441: POP | 13442: POP | 13443: POP | 13444: POP | 13445: POP | 13446: POP | 13447: PUSH1 0x01 | 13449: SWAP1 | 13450: JUMP
13451: JUMPDEST | 13452: POP | 13453: POP | 13454: POP | 13455: PUSH1 0x01 | 13457: SWAP1 | 13458: JUMP
13459: JUMPDEST | 13460: PUSH1 0x0c | 13462: SIGNEXTEND | 13463: PUSH1 0x01 | 13465: PUSH1 0x01 | 13467: PUSH1 0x67 | 13469: SHL | 13470: SUB | 13471: NOT | 13472: DUP2 | 13473: EQ | 13474: PUSH2 0x29a2 | 13477: JUMPI
13478: JUMPDEST | 13479: PUSH1 0x00 | 13481: SUB | 13482: SWAP1 | 13483: JUMP
13484: JUMPDEST | 13485: PUSH2 0x29aa | 13488: PUSH2 0x1e32 | 13491: JUMP
13492: JUMPDEST | 13493: PUSH2 0x299c | 13496: JUMP
13497: JUMPDEST | 13498: PUSH1 0x01 | 13500: PUSH1 0xff | 13502: SHL | 13503: DUP2 | 13504: EQ | 13505: PUSH2 0x29a2 | 13508: JUMPI
13509: PUSH1 0x00 | 13511: SUB | 13512: SWAP1 | 13513: JUMP
13514: JUMPDEST | 13515: PUSH1 0x00 | 13517: PUSH1 0x0c | 13519: DUP3 | 13520: SWAP1 | 13521: SIGNEXTEND | 13522: SLT | 13523: PUSH2 0x2a00 | 13526: JUMPI
13527: PUSH1 0x00 | 13529: SLOAD | 13530: PUSH2 0x0979 | 13533: SWAP2 | 13534: PUSH7 0x038d7ea4c68000 | 13542: SWAP2 | 13543: PUSH2 0x29fa | 13546: SWAP2 | 13547: PUSH1 0x01 | 13549: PUSH1 0x01 | 13551: PUSH1 0x40 | 13553: SHL | 13554: SUB | 13555: SWAP1 | 13556: SWAP2 | 13557: AND | 13558: SWAP1 | 13559: PUSH1 0x01 | 13561: PUSH1 0x01 | 13563: PUSH1 0x68 | 13565: SHL | 13566: SUB | 13567: AND | 13568: PUSH2 0x1e77 | 13571: JUMP
13572: JUMPDEST | 13573: DIV | 13574: PUSH2 0x2791 | 13577: JUMP
13578: JUMPDEST | 13579: PUSH2 0x2a30 | 13582: PUSH2 0x2966 | 13585: PUSH2 0x0979 | 13588: SWAP3 | 13589: PUSH2 0x2a21 | 13592: PUSH1 0x01 | 13594: DUP1 | 13595: PUSH1 0x40 | 13597: SHL | 13598: SUB | 13599: PUSH1 0x00 | 13601: SLOAD | 13602: PUSH1 0x40 | 13604: SHR | 13605: AND | 13606: SWAP2 | 13607: PUSH2 0x2989 | 13610: JUMP
13611: JUMPDEST | 13612: PUSH1 0x01 | 13614: PUSH1 0x01 | 13616: PUSH1 0x68 | 13618: SHL | 13619: SUB | 13620: AND | 13621: SWAP1 | 13622: PUSH2 0x2466 | 13625: JUMP
13626: JUMPDEST | 13627: PUSH2 0x29af | 13630: JUMP
13631: JUMPDEST | 13632: PUSH2 0x2a43 | 13635: PUSH2 0x27c2 | 13638: DUP3 | 13639: PUSH1 0x05 | 13641: PUSH2 0x097c | 13644: JUMP
13645: JUMPDEST | 13646: SWAP1 | 13647: PUSH1 0x00 | 13649: SWAP2 | 13650: DUP3 | 13651: DUP2 | 13652: PUSH1 0x0c | 13654: SIGNEXTEND | 13655: SLT | 13656: ISZERO | 13657: PUSH2 0x2b46 | 13660: JUMPI
13661: PUSH2 0x2a60 | 13664: PUSH2 0x27e6 | 13667: DUP4 | 13668: PUSH1 0x05 | 13670: PUSH2 0x097c | 13673: JUMP
13674: JUMPDEST | 13675: SWAP1 | 13676: PUSH2 0x2a75 | 13679: PUSH2 0x2813 | 13682: PUSH2 0x280d | 13685: PUSH2 0x2806 | 13688: DUP7 | 13689: PUSH1 0x05 | 13691: PUSH2 0x097c | 13694: JUMP
13695: JUMPDEST | 13696: SWAP3 | 13697: DUP5 | 13698: SWAP2 | 13699: PUSH1 0xff | 13701: SWAP4 | 13702: DUP5 | 13703: PUSH32 0x0000000000000000000000000000000000000000000000000000000000000000 | 13736: AND | 13737: SWAP4
13738: JUMPDEST | 13739: DUP5 | 13740: DUP7 | 13741: DUP3 | 13742: AND | 13743: LT | 13744: PUSH2 0x2ab3 | 13747: JUMPI
13748: POP | 13749: POP | 13750: POP | 13751: POP | 13752: POP | 13753: POP | 13754: SLT | 13755: SWAP1 | 13756: JUMP
13757: JUMPDEST | 13758: PUSH2 0x2abe | 13761: DUP4 | 13762: DUP3 | 13763: DUP5 | 13764: PUSH2 0x2cc0 | 13767: JUMP
13768: JUMPDEST | 13769: PUSH2 0x2acd | 13772: JUMPI
13773: JUMPDEST | 13774: PUSH1 0x01 | 13776: ADD | 13777: DUP6 | 13778: AND | 13779: PUSH2 0x2aa0 | 13782: JUMP
13783: JUMPDEST | 13784: SWAP6 | 13785: DUP8 | 13786: DUP2 | 13787: SLT | 13788: ISZERO | 13789: PUSH2 0x2b3c | 13792: JUMPI
13793: PUSH1 0x01 | 13795: PUSH2 0x2b33 | 13798: DUP8 | 13799: SWAP3 | 13800: PUSH2 0x2746 | 13803: PUSH2 0x2966 | 13806: DUP9 | 13807: PUSH2 0x2960 | 13810: PUSH2 0x295b | 13813: PUSH1 0xa0 | 13815: DUP16 | 13816: PUSH2 0x2b02 | 13819: PUSH2 0x2916 | 13822: PUSH2 0x2902 | 13825: PUSH2 0x28fa | 13828: PUSH2 0x2953 | 13831: SWAP5 | 13832: PUSH2 0x1c0b | 13835: JUMP
13836: JUMPDEST | 13837: PUSH1 0x40 | 13839: DUP7 | 13840: ADD | 13841: MLOAD | 13842: PUSH2 0x2b19 | 13845: SWAP1 | 13846: PUSH1 0x01 | 13848: PUSH1 0x01 | 13850: PUSH1 0xa0 | 13852: SHL | 13853: SUB | 13854: AND | 13855: PUSH2 0x249f | 13858: JUMP
13859: JUMPDEST | 13860: PUSH2 0x2b26 | 13863: PUSH1 0x60 | 13865: DUP9 | 13866: ADD | 13867: MLOAD | 13868: PUSH2 0x0b8f | 13871: JUMP
13872: JUMPDEST | 13873: SWAP2 | 13874: DUP13 | 13875: DUP1 | 13876: PUSH1 0x80 | 13878: SHL | 13879: SUB | 13880: AND | 13881: PUSH2 0x2bba | 13884: JUMP
13885: JUMPDEST | 13886: SWAP8 | 13887: SWAP2 | 13888: POP | 13889: POP | 13890: PUSH2 0x2ac3 | 13893: JUMP
13894: JUMPDEST | 13895: POP | 13896: POP | 13897: POP | 13898: POP | 13899: POP | 13900: POP | 13901: POP | 13902: SWAP1 | 13903: JUMP
13904: JUMPDEST | 13905: POP | 13906: POP | 13907: SWAP1 | 13908: JUMP
13909: JUMPDEST | 13910: DUP1 | 13911: SLOAD | 13912: PUSH1 0x01 | 13914: PUSH1 0x01 | 13916: PUSH1 0xf8 | 13918: SHL | 13919: SUB | 13920: AND | 13921: PUSH1 0xf8 | 13923: SWAP3 | 13924: SWAP1 | 13925: SWAP3 | 13926: SHL | 13927: PUSH1 0x01 | 13929: PUSH1 0x01 | 13931: PUSH1 0xf8 | 13933: SHL | 13934: SUB | 13935: NOT | 13936: AND | 13937: SWAP2 | 13938: SWAP1 | 13939: SWAP2 | 13940: OR | 13941: SWAP1 | 13942: SSTORE | 13943: JUMP
13944: JUMPDEST | 13945: PUSH1 0x00 | 13947: SWAP1 | 13948: ISZERO | 13949: PUSH2 0x0979 | 13952: JUMPI
13953: POP | 13954: PUSH1 0x01 | 13956: SWAP1 | 13957: JUMP
13958: JUMPDEST | 13959: PUSH8 0x0de0b6b3a7640000 | 13968: SWAP2 | 13969: PUSH2 0x23e8 | 13972: SWAP2 | 13973: PUSH2 0x1e77 | 13976: JUMP
13977: JUMPDEST | 13978: PUSH2 0x23d6 | 13981: SWAP1 | 13982: PUSH32 0x0000000000000000000000000000000000000000000000000000000000000000 | 14015: SWAP1 | 14016: PUSH2 0x1e77 | 14019: JUMP
14020: JUMPDEST | 14021: SWAP1 | 14022: PUSH2 0x2bc4 | 14025: SWAP2 | 14026: PUSH2 0x1e77 | 14029: JUMP
14030: JUMPDEST | 14031: PUSH1 0x01 | 14033: PUSH1 0x01 | 14035: PUSH1 0x40 | 14037: SHL | 14038: SUB | 14039: SWAP1 | 14040: SWAP2 | 14041: AND | 14042: SWAP1 | 14043: DUP2 | 14044: ISZERO | 14045: PUSH2 0x23e0 | 14048: JUMPI
14049: DIV | 14050: SWAP1 | 14051: JUMP
14052: JUMPDEST | 14053: SWAP2 | 14054: SWAP1 | 14055: PUSH2 0x2be5 | 14058: SWAP1 | 14059: PUSH2 0x2791 | 14062: JUMP
14063: JUMPDEST | 14064: PUSH1 0x00 | 14066: DUP1 | 14067: DUP5 | 14068: SGT | 14069: SWAP4 | 14070: SWAP1 | 14071: DUP3 | 14072: SGT | 14073: PUSH1 0x01 | 14075: PUSH1 0x01 | 14077: PUSH1 0xff | 14079: SHL | 14080: SUB | 14081: DUP6 | 14082: DUP3 | 14083: AND | 14084: DUP5 | 14085: DUP3 | 14086: DIV | 14087: DUP5 | 14088: GT | 14089: AND | 14090: PUSH2 0x2ca1 | 14093: JUMPI
14094: JUMPDEST | 14095: PUSH1 0x01 | 14097: PUSH1 0xff | 14099: SHL | 14100: SWAP6 | 14101: PUSH1 0x00 | 14103: DUP6 | 14104: SLT | 14105: SWAP2 | 14106: DUP6 | 14107: SWAP2 | 14108: DUP4 | 14109: AND | 14110: DUP6 | 14111: DUP10 | 14112: SDIV | 14113: DUP4 | 14114: SLT | 14115: AND | 14116: PUSH2 0x2c94 | 14119: JUMPI
14120: JUMPDEST | 14121: PUSH1 0x00 | 14123: DUP6 | 14124: SLT | 14125: SWAP4 | 14126: DUP5 | 14127: AND | 14128: DUP3 | 14129: DUP10 | 14130: SDIV | 14131: DUP7 | 14132: SLT | 14133: AND | 14134: PUSH2 0x2c87 | 14137: JUMPI
14138: JUMPDEST | 14139: SDIV | 14140: DUP4 | 14141: SLT | 14142: SWAP2 | 14143: AND | 14144: AND | 14145: PUSH2 0x2c7a | 14148: JUMPI
14149: JUMPDEST | 14150: PUSH1 0x01 | 14152: PUSH1 0x01 | 14154: PUSH1 0x40 | 14156: SHL | 14157: SUB | 14158: SWAP1 | 14159: SWAP3 | 14160: AND | 14161: SWAP3 | 14162: SWAP2 | 14163: MUL | 14164: SWAP1 | 14165: DUP3 | 14166: ISZERO | 14167: PUSH2 0x2c6d | 14170: JUMPI
14171: JUMPDEST | 14172: DUP2 | 14173: EQ | 14174: PUSH1 0x00 | 14176: NOT | 14177: DUP4 | 14178: EQ | 14179: AND | 14180: PUSH2 0x2c61 | 14183: JUMPI
14184: SDIV | 14185: SWAP1 | 14186: JUMP
14187: JUMPDEST | 14188: PUSH2 0x2c69 | 14191: PUSH2 0x1e32 | 14194: JUMP
14195: JUMPDEST | 14196: SDIV | 14197: SWAP1 | 14198: JUMP
14199: JUMPDEST | 14200: PUSH2 0x2c75 | 14203: PUSH2 0x23bf | 14206: JUMP
14207: JUMPDEST | 14208: PUSH2 0x2c51 | 14211: JUMP
14212: JUMPDEST | 14213: PUSH2 0x2c82 | 14216: PUSH2 0x1e32 | 14219: JUMP
14220: JUMPDEST | 14221: PUSH2 0x2c3b | 14224: JUMP
14225: JUMPDEST | 14226: PUSH2 0x2c8f | 14229: PUSH2 0x1e32 | 14232: JUMP
14233: JUMPDEST | 14234: PUSH2 0x2c30 | 14237: JUMP
14238: JUMPDEST | 14239: PUSH2 0x2c9c | 14242: PUSH2 0x1e32 | 14245: JUMP
14246: JUMPDEST | 14247: PUSH2 0x2c1e | 14250: JUMP
14251: JUMPDEST | 14252: PUSH2 0x2ca9 | 14255: PUSH2 0x1e32 | 14258: JUMP
14259: JUMPDEST | 14260: PUSH2 0x2c04 | 14263: JUMP
14264: JUMPDEST | 14265: PUSH1 0xff | 14267: SWAP2 | 14268: DUP3 | 14269: AND | 14270: SWAP2 | 14271: AND | 14272: DUP2 | 14273: DUP2 | 14274: LT | 14275: PUSH2 0x1e5f | 14278: JUMPI
14279: SUB | 14280: SWAP1 | 14281: JUMP
14282: JUMPDEST | 14283: SWAP1 | 14284: PUSH1 0xff | 14286: AND | 14287: SWAP2 | 14288: PUSH1 0x10 | 14290: DUP4 | 14291: LT | 14292: PUSH1 0x00 | 14294: EQ | 14295: PUSH2 0x2cdf | 14298: JUMPI
14299: POP | 14300: PUSH1 0x01 | 14302: PUSH2 0xffff | 14305: SWAP3 | 14306: SHL | 14307: AND | 14308: AND | 14309: ISZERO | 14310: ISZERO | 14311: SWAP1 | 14312: JUMP
14313: JUMPDEST | 14314: SWAP1 | 14315: POP | 14316: PUSH1 0x18 | 14318: DUP3 | 14319: LT | 14320: PUSH2 0x2cf0 | 14323: JUMPI
14324: POP | 14325: POP | 14326: PUSH1 0x00 | 14328: SWAP1 | 14329: JUMP
14330: JUMPDEST | 14331: PUSH1 0x01 | 14333: PUSH1 0xff | 14335: DUP1 | 14336: SWAP4 | 14337: PUSH1 0x0f | 14339: NOT | 14340: ADD | 14341: AND | 14342: SHL | 14343: AND | 14344: AND | 14345: ISZERO | 14346: ISZERO | 14347: SWAP1 | 14348: JUMP
14349: JUMPDEST | 14350: PUSH1 0x01 | 14352: PUSH1 0x01 | 14354: PUSH1 0x40 | 14356: SHL | 14357: SUB | 14358: SWAP2 | 14359: DUP3 | 14360: AND | 14361: SWAP2 | 14362: AND | 14363: DUP2 | 14364: DUP2 | 14365: LT | 14366: PUSH2 0x1e5f | 14369: JUMPI
14370: SUB | 14371: SWAP1 | 14372: JUMP
14373: JUMPDEST | 14374: DUP1 | 14375: SLOAD | 14376: PUSH2 0xffff | 14379: PUSH1 0xe8 | 14381: SHL | 14382: NOT | 14383: AND | 14384: PUSH1 0xe8 | 14386: SWAP3 | 14387: SWAP1 | 14388: SWAP3 | 14389: SHL | 14390: PUSH2 0xffff | 14393: PUSH1 0xe8 | 14395: SHL | 14396: AND | 14397: SWAP2 | 14398: SWAP1 | 14399: SWAP2 | 14400: OR | 14401: SWAP1 | 14402: SSTORE | 14403: JUMP
14404: JUMPDEST | 14405: DUP2 | 14406: MLOAD | 14407: DUP2 | 14408: SLOAD | 14409: PUSH1 0x20 | 14411: DUP5 | 14412: ADD | 14413: MLOAD | 14414: PUSH1 0x40 | 14416: DUP6 | 14417: ADD | 14418: MLOAD | 14419: PUSH1 0x01 | 14421: PUSH1 0x01 | 14423: PUSH1 0xe8 | 14425: SHL | 14426: SUB | 14427: NOT | 14428: SWAP1 | 14429: SWAP3 | 14430: AND | 14431: PUSH1 0x01 | 14433: PUSH1 0x01 | 14435: PUSH1 0x68 | 14437: SHL | 14438: SUB | 14439: SWAP1 | 14440: SWAP4 | 14441: AND | 14442: SWAP3 | 14443: SWAP1 | 14444: SWAP3 | 14445: OR | 14446: PUSH1 0x68 | 14448: SWAP3 | 14449: SWAP1 | 14450: SWAP3 | 14451: SHL | 14452: PUSH1 0x01 | 14454: PUSH1 0x68 | 14456: SHL | 14457: PUSH1 0x01 | 14459: PUSH1 0xa8 | 14461: SHL | 14462: SUB | 14463: AND | 14464: SWAP2 | 14465: SWAP1 | 14466: SWAP2 | 14467: OR | 14468: PUSH1 0xa8 | 14470: SWAP2 | 14471: SWAP1 | 14472: SWAP2 | 14473: SHL | 14474: PUSH1 0x01 | 14476: PUSH1 0xa8 | 14478: SHL | 14479: PUSH1 0x01 | 14481: PUSH1 0xe8 | 14483: SHL | 14484: SUB | 14485: AND | 14486: OR | 14487: DUP2 | 14488: SSTORE | 14489: PUSH1 0x60 | 14491: DUP3 | 14492: ADD | 14493: MLOAD | 14494: PUSH2 0x0c31 | 14497: SWAP3 | 14498: PUSH1 0xff | 14500: SWAP2 | 14501: PUSH1 0x80 | 14503: SWAP2 | 14504: SWAP1 | 14505: PUSH2 0x2dac | 14508: SWAP1 | 14509: PUSH2 0xffff | 14512: AND | 14513: DUP6 | 14514: PUSH2 0x2d1b | 14517: JUMP
14518: JUMPDEST | 14519: ADD | 14520: MLOAD | 14521: AND | 14522: SWAP1 | 14523: PUSH2 0x2b4b | 14526: JUMP
14527: JUMPDEST | 14528: PUSH2 0x2ecc | 14531: SWAP1 | 14532: PUSH2 0x0c31 | 14535: SWAP4 | 14536: PUSH2 0x2dc8 | 14539: DUP5 | 14540: MLOAD | 14541: PUSH1 0x0c | 14543: SIGNEXTEND | 14544: SWAP1 | 14545: JUMP
14546: JUMPDEST | 14547: PUSH1 0x0c | 14549: DUP3 | 14550: SWAP1 | 14551: SIGNEXTEND | 14552: DUP6 | 14553: MSTORE | 14554: PUSH1 0x00 | 14556: SWAP2 | 14557: DUP3 | 14558: SWAP2 | 14559: DUP7 | 14560: DUP4 | 14561: PUSH1 0x0c | 14563: DUP4 | 14564: SWAP1 | 14565: SIGNEXTEND | 14566: DUP2 | 14567: SGT | 14568: PUSH2 0x2ee3 | 14571: JUMPI
14572: PUSH2 0x2e55 | 14575: PUSH2 0x2e2e | 14578: PUSH2 0x2e9b | 14581: SWAP5 | 14582: PUSH2 0x2e1f | 14585: PUSH2 0x295b | 14588: PUSH2 0x2e7c | 14591: SWAP7 | 14592: PUSH2 0x2e19 | 14595: PUSH1 0x20 | 14597: PUSH2 0x2e11 | 14600: PUSH2 0x2025 | 14603: SWAP10 | 14604: SLOAD | 14605: PUSH1 0x01 | 14607: DUP1 | 14608: PUSH1 0x40 | 14610: SHL | 14611: SUB | 14612: SWAP1 | 14613: PUSH1 0x80 | 14615: SHR | 14616: AND | 14617: SWAP1 | 14618: JUMP
14619: JUMPDEST | 14620: SWAP3 | 14621: ADD | 14622: MLOAD | 14623: PUSH2 0x0b8f | 14626: JUMP
14627: JUMPDEST | 14628: SWAP1 | 14629: PUSH2 0x2d03 | 14632: JUMP
14633: JUMPDEST | 14634: SWAP1 | 14635: PUSH1 0x01 | 14637: PUSH1 0x01 | 14639: PUSH1 0x68 | 14641: SHL | 14642: SUB | 14643: AND | 14644: PUSH2 0x1e77 | 14647: JUMP
14648: JUMPDEST | 14649: PUSH32 0x0000000000000000000000000000000000000000000000000000000000000000 | 14682: SWAP1 | 14683: PUSH2 0x23d6 | 14686: JUMP
14687: JUMPDEST | 14688: PUSH32 0x0000000000000000000000000000000000000000000000000000000000000000 | 14721: SWAP1 | 14722: PUSH2 0x23d6 | 14725: JUMP
14726: JUMPDEST | 14727: PUSH2 0x2e8e | 14730: PUSH1 0x40 | 14732: DUP10 | 14733: ADD | 14734: SWAP2 | 14735: PUSH2 0x2034 | 14738: DUP4 | 14739: MLOAD | 14740: PUSH2 0x0b8f | 14743: JUMP
14744: JUMPDEST | 14745: PUSH1 0x01 | 14747: PUSH1 0x01 | 14749: PUSH1 0x40 | 14751: SHL | 14752: SUB | 14753: AND | 14754: SWAP1 | 14755: MSTORE | 14756: JUMP
14757: JUMPDEST | 14758: PUSH1 0x0c | 14760: SIGNEXTEND | 14761: SLT | 14762: PUSH2 0x2ed1 | 14765: JUMPI
14766: SLOAD | 14767: PUSH2 0x2ec5 | 14770: SWAP1 | 14771: PUSH1 0x80 | 14773: SHR | 14774: PUSH1 0x01 | 14776: PUSH1 0x01 | 14778: PUSH1 0x40 | 14780: SHL | 14781: SUB | 14782: AND
14783: JUMPDEST | 14784: PUSH1 0x01 | 14786: PUSH1 0x01 | 14788: PUSH1 0x40 | 14790: SHL | 14791: SUB | 14792: AND | 14793: PUSH1 0x20 | 14795: DUP6 | 14796: ADD | 14797: MSTORE | 14798: JUMP
14799: JUMPDEST | 14800: PUSH1 0x05 | 14802: PUSH2 0x097c | 14805: JUMP
14806: JUMPDEST | 14807: PUSH2 0x2d3a | 14810: JUMP
14811: JUMPDEST | 14812: SLOAD | 14813: PUSH2 0x2ede | 14816: SWAP1 | 14817: PUSH1 0xc0 | 14819: SHR | 14820: PUSH2 0x2eb5 | 14823: JUMP
14824: JUMPDEST | 14825: PUSH2 0x2ec5 | 14828: JUMP
14829: JUMPDEST | 14830: PUSH2 0x2e55 | 14833: PUSH2 0x2e2e | 14836: PUSH2 0x2f1e | 14839: SWAP5 | 14840: PUSH2 0x2f19 | 14843: PUSH2 0x1fb0 | 14846: PUSH2 0x1e6b | 14849: PUSH2 0x2f13 | 14852: PUSH2 0x295b | 14855: PUSH2 0x2e7c | 14858: SWAP10 | 14859: PUSH2 0x2e19 | 14862: PUSH1 0x20 | 14864: PUSH2 0x2e11 | 14867: PUSH2 0x2025 | 14870: SWAP13 | 14871: SLOAD | 14872: PUSH1 0xc0 | 14874: SHR | 14875: SWAP1 | 14876: JUMP
14877: JUMPDEST | 14878: SWAP4 | 14879: PUSH2 0x2989 | 14882: JUMP
14883: JUMPDEST | 14884: PUSH2 0x1e77 | 14887: JUMP
14888: JUMPDEST | 14889: PUSH2 0x2e9b | 14892: JUMP
14893: JUMPDEST | 14894: SWAP4 | 14895: SWAP3 | 14896: SWAP1 | 14897: SWAP4 | 14898: PUSH1 0x01 | 14900: DUP1 | 14901: SLOAD | 14902: PUSH1 0xf8 | 14904: SHR | 14905: AND | 14906: PUSH2 0x1a47 | 14909: JUMPI
14910: PUSH2 0x2f40 | 14913: PUSH2 0x2f44 | 14916: SWAP2 | 14917: DUP7 | 14918: PUSH2 0x1b09 | 14921: JUMP
14922: JUMPDEST | 14923: ISZERO | 14924: SWAP1 | 14925: JUMP
14926: JUMPDEST | 14927: PUSH2 0x0e62 | 14930: JUMPI
14931: PUSH1 0x01 | 14933: PUSH1 0x01 | 14935: PUSH1 0xa0 | 14937: SHL | 14938: SUB | 14939: DUP2 | 14940: DUP2 | 14941: AND | 14942: PUSH32 0x0000000000000000000000000000000000000000000000000000000000000000 | 14975: SWAP1 | 14976: SWAP2 | 14977: AND | 14978: SUB | 14979: PUSH2 0x2f9b | 14982: JUMPI
14983: POP | 14984: PUSH2 0x0c31 | 14987: SWAP3 | 14988: PUSH1 0x00 | 14990: NOT | 14991: DUP4 | 14992: SUB | 14993: PUSH2 0x3082 | 14996: JUMPI
14997: SWAP2 | 14998: POP | 14999: PUSH2 0x2f95 | 15002: DUP2 | 15003: PUSH2 0x47aa | 15006: JUMP
15007: JUMPDEST | 15008: SWAP2 | 15009: PUSH2 0x3082 | 15012: JUMP
15013: JUMPDEST | 15014: SWAP1 | 15015: PUSH2 0x2fa9 | 15018: PUSH2 0x0c31 | 15021: SWAP5 | 15022: SWAP4 | 15023: PUSH2 0x2faf | 15026: JUMP
15027: JUMPDEST | 15028: SWAP3 | 15029: PUSH2 0x35fc | 15032: JUMP
15033: JUMPDEST | 15034: PUSH1 0x01 | 15036: PUSH1 0x01 | 15038: PUSH1 0x80 | 15040: SHL | 15041: SUB | 15042: SWAP1 | 15043: DUP2 | 15044: DUP2 | 15045: GT | 15046: PUSH2 0x2fc3 | 15049: JUMPI
15050: AND | 15051: SWAP1 | 15052: JUMP
15053: JUMPDEST | 15054: PUSH1 0x40 | 15056: MLOAD | 15057: PUSH4 0x762ea711 | 15062: PUSH1 0xe1 | 15064: SHL | 15065: DUP2 | 15066: MSTORE | 15067: PUSH1 0x04 | 15069: SWAP1 | 15070: REVERT
15071: JUMPDEST | 15072: PUSH1 0x00 | 15074: DUP1 | 15075: MLOAD | 15076: PUSH1 0x20 | 15078: PUSH2 0x4852 | 15081: DUP4 | 15082: CODECOPY | 15083: DUP2 | 15084: MLOAD | 15085: SWAP2 | 15086: MSTORE | 15087: PUSH1 0x01 | 15089: DUP2 | 15090: SLOAD | 15091: EQ | 15092: PUSH2 0x2ff3 | 15095: JUMPI
15096: PUSH1 0x01 | 15098: SWAP1 | 15099: SSTORE | 15100: JUMP
15101: JUMPDEST | 15102: PUSH1 0x40 | 15104: MLOAD | 15105: PUSH4 0x139b6435 | 15110: PUSH1 0xe2 | 15112: SHL | 15113: DUP2 | 15114: MSTORE | 15115: PUSH1 0x04 | 15117: SWAP1 | 15118: REVERT
15119: JUMPDEST | 15120: PUSH1 0x01 | 15122: PUSH1 0x01 | 15124: PUSH1 0x68 | 15126: SHL | 15127: SUB | 15128: SWAP2 | 15129: DUP3 | 15130: AND | 15131: SWAP2 | 15132: SWAP1 | 15133: DUP2 | 15134: AND | 15135: SWAP1 | 15136: DUP3 | 15137: SWAP1 | 15138: SUB | 15139: DUP2 | 15140: GT | 15141: PUSH2 0x1eb3 | 15144: JUMPI
15145: ADD | 15146: SWAP1 | 15147: JUMP
15148: JUMPDEST | 15149: DUP1 | 15150: SLOAD | 15151: PUSH1 0x01 | 15153: PUSH1 0x01 | 15155: PUSH1 0x68 | 15157: SHL | 15158: SUB | 15159: NOT | 15160: AND | 15161: PUSH1 0x01 | 15163: PUSH1 0x01 | 15165: PUSH1 0x68 | 15167: SHL | 15168: SUB | 15169: SWAP1 | 15170: SWAP3 | 15171: AND | 15172: SWAP2 | 15173: SWAP1 | 15174: SWAP2 | 15175: OR | 15176: SWAP1 | 15177: SSTORE | 15178: JUMP
15179: JUMPDEST | 15180: PUSH1 0x01 | 15182: PUSH1 0x01 | 15184: PUSH1 0x68 | 15186: SHL | 15187: SUB | 15188: SWAP2 | 15189: DUP3 | 15190: AND | 15191: SWAP2 | 15192: AND | 15193: DUP2 | 15194: DUP2 | 15195: LT | 15196: PUSH2 0x1e5f | 15199: JUMPI
15200: SUB | 15201: SWAP1 | 15202: JUMP
15203: JUMPDEST | 15204: DUP1 | 15205: SLOAD | 15206: PUSH1 0x01 | 15208: PUSH1 0x68 | 15210: SHL | 15211: PUSH1 0x01 | 15213: PUSH1 0xd0 | 15215: SHL | 15216: SUB | 15217: NOT | 15218: AND | 15219: PUSH1 0x68 | 15221: SWAP3 | 15222: SWAP1 | 15223: SWAP3 | 15224: SHL | 15225: PUSH1 0x01 | 15227: PUSH1 0x68 | 15229: SHL | 15230: PUSH1 0x01 | 15232: PUSH1 0xd0 | 15234: SHL | 15235: SUB | 15236: AND | 15237: SWAP2 | 15238: SWAP1 | 15239: SWAP2 | 15240: OR | 15241: SWAP1 | 15242: SSTORE | 15243: JUMP
15244: JUMPDEST | 15245: PUSH2 0x30b1 | 15248: PUSH2 0x312f | 15251: SWAP3 | 15252: SWAP4 | 15253: DUP3 | 15254: PUSH32 0x0000000000000000000000000000000000000000000000000000000000000000 | 15287: PUSH2 0x33d8 | 15290: JUMP
15291: JUMPDEST | 15292: PUSH2 0x30b9 | 15295: PUSH2 0x1ece | 15298: JUMP
15299: JUMPDEST | 15300: PUSH2 0x313c | 15303: PUSH2 0x30cf | 15306: PUSH2 0x30ca | 15309: DUP7 | 15310: PUSH1 0x05 | 15312: PUSH2 0x097c | 15315: JUMP
15316: JUMPDEST | 15317: PUSH2 0x1de7 | 15320: JUMP
15321: JUMPDEST | 15322: DUP1 | 15323: MLOAD | 15324: PUSH1 0x0c | 15326: SIGNEXTEND | 15327: SWAP1 | 15328: PUSH2 0x3136 | 15331: PUSH2 0x30ff | 15334: PUSH2 0x30f8 | 15337: PUSH2 0x30f3 | 15340: PUSH2 0x30ea | 15343: DUP7 | 15344: PUSH2 0x29c0 | 15347: JUMP
15348: JUMPDEST | 15349: PUSH2 0x2746 | 15352: DUP10 | 15353: PUSH2 0x2791 | 15356: JUMP
15357: JUMPDEST | 15358: PUSH2 0x31c6 | 15361: JUMP
15362: JUMPDEST | 15363: DUP1 | 15364: SWAP5 | 15365: PUSH2 0x335c | 15368: JUMP
15369: JUMPDEST | 15370: SWAP8 | 15371: SWAP1 | 15372: PUSH2 0x311f | 15375: PUSH2 0x3118 | 15378: DUP11 | 15379: PUSH2 0x3113 | 15382: PUSH1 0x01 | 15384: SLOAD | 15385: PUSH2 0x1e6b | 15388: JUMP
15389: JUMPDEST | 15390: PUSH2 0x3005 | 15393: JUMP
15394: JUMPDEST | 15395: PUSH1 0x01 | 15397: PUSH2 0x3022 | 15400: JUMP
15401: JUMPDEST | 15402: PUSH2 0x312a | 15405: PUSH1 0x01 | 15407: SLOAD | 15408: PUSH2 0x1ebf | 15411: JUMP
15412: JUMPDEST | 15413: PUSH2 0x3041 | 15416: JUMP
15417: JUMPDEST | 15418: PUSH1 0x01 | 15420: PUSH2 0x3059 | 15423: JUMP
15424: JUMPDEST | 15425: DUP7 | 15426: PUSH2 0x2db5 | 15429: JUMP
15430: JUMPDEST | 15431: PUSH1 0x40 | 15433: MLOAD | 15434: SWAP1 | 15435: DUP2 | 15436: MSTORE | 15437: PUSH1 0x01 | 15439: PUSH1 0x01 | 15441: PUSH1 0xa0 | 15443: SHL | 15444: SUB | 15445: SWAP4 | 15446: DUP5 | 15447: AND | 15448: SWAP4 | 15449: DUP5 | 15450: SWAP3 | 15451: AND | 15452: SWAP1 | 15453: PUSH32 0xd1cf3d156d5f8f0d50f6c122ed609cec09d35c9b9fb3fff6ea0959134dae424e | 15486: SWAP1 | 15487: PUSH1 0x20 | 15489: SWAP1 | 15490: LOG3 | 15491: PUSH1 0x01 | 15493: PUSH1 0x01 | 15495: PUSH1 0x68 | 15497: SHL | 15498: SUB | 15499: DUP2 | 15500: AND | 15501: PUSH2 0x318a | 15504: JUMPI
15505: POP | 15506: POP | 15507: JUMP
15508: JUMPDEST | 15509: PUSH1 0x00 | 15511: DUP1 | 15512: MLOAD | 15513: PUSH1 0x20 | 15515: PUSH2 0x4832 | 15518: DUP4 | 15519: CODECOPY | 15520: DUP2 | 15521: MLOAD | 15522: SWAP2 | 15523: MSTORE | 15524: PUSH2 0x31c1 | 15527: PUSH2 0x31b1 | 15530: PUSH1 0x00 | 15532: SWAP4 | 15533: PUSH2 0x31ac | 15536: DUP6 | 15537: SLOAD | 15538: PUSH2 0x0b8f | 15541: JUMP
15542: JUMPDEST | 15543: PUSH2 0x2466 | 15546: JUMP
15547: JUMPDEST | 15548: PUSH1 0x40 | 15550: MLOAD | 15551: SWAP1 | 15552: DUP2 | 15553: MSTORE | 15554: SWAP1 | 15555: DUP2 | 15556: SWAP1 | 15557: PUSH1 0x20 | 15559: DUP3 | 15560: ADD | 15561: SWAP1 | 15562: JUMP
15563: JUMPDEST | 15564: SUB | 15565: SWAP1 | 15566: LOG3 | 15567: JUMP
15568: JUMPDEST | 15569: PUSH1 0x00 | 15571: DUP2 | 15572: SLT | 15573: PUSH2 0x31ec | 15576: JUMPI
15577: PUSH1 0x00 | 15579: SLOAD | 15580: PUSH2 0x0979 | 15583: SWAP2 | 15584: PUSH2 0x31e7 | 15587: SWAP2 | 15588: PUSH1 0x01 | 15590: PUSH1 0x01 | 15592: PUSH1 0x40 | 15594: SHL | 15595: SUB | 15596: AND | 15597: PUSH2 0x3275 | 15600: JUMP
15601: JUMPDEST | 15602: PUSH2 0x32eb | 15605: JUMP
15606: JUMPDEST | 15607: PUSH2 0x3249 | 15610: PUSH2 0x31e7 | 15613: PUSH2 0x0979 | 15616: SWAP3 | 15617: PUSH2 0x320d | 15620: PUSH1 0x01 | 15622: DUP1 | 15623: PUSH1 0x40 | 15625: SHL | 15626: SUB | 15627: PUSH1 0x00 | 15629: SLOAD | 15630: PUSH1 0x40 | 15632: SHR | 15633: AND | 15634: SWAP2 | 15635: PUSH2 0x29af | 15638: JUMP
15639: JUMPDEST | 15640: PUSH2 0x3232 | 15643: DUP3 | 15644: PUSH1 0x00 | 15646: NOT | 15647: SWAP3 | 15648: PUSH7 0x038d7ea4c68000 | 15656: SWAP1 | 15657: DUP1 | 15658: DUP6 | 15659: DIV | 15660: DUP3 | 15661: GT | 15662: DUP2 | 15663: ISZERO | 15664: ISZERO | 15665: AND | 15666: PUSH2 0x3268 | 15669: JUMPI
15670: JUMPDEST | 15671: MUL | 15672: PUSH2 0x218f | 15675: JUMP
15676: JUMPDEST | 15677: PUSH1 0x01 | 15679: DUP2 | 15680: LT | 15681: PUSH2 0x325b | 15684: JUMPI
15685: JUMPDEST | 15686: DUP3 | 15687: ISZERO | 15688: PUSH2 0x324e | 15691: JUMPI
15692: JUMPDEST | 15693: ADD | 15694: DIV | 15695: PUSH2 0x32c5 | 15698: JUMP
15699: JUMPDEST | 15700: PUSH2 0x2989 | 15703: JUMP
15704: JUMPDEST | 15705: PUSH2 0x3256 | 15708: PUSH2 0x23bf | 15711: JUMP
15712: JUMPDEST | 15713: PUSH2 0x3242 | 15716: JUMP
15717: JUMPDEST | 15718: PUSH2 0x3263 | 15721: PUSH2 0x1e32 | 15724: JUMP
15725: JUMPDEST | 15726: PUSH2 0x323b | 15729: JUMP
15730: JUMPDEST | 15731: PUSH2 0x3270 | 15734: PUSH2 0x1e32 | 15737: JUMP
15738: JUMPDEST | 15739: PUSH2 0x322c | 15742: JUMP
15743: JUMPDEST | 15744: SWAP1 | 15745: PUSH2 0x0979 | 15748: SWAP2 | 15749: PUSH7 0x038d7ea4c68000 | 15757: SWAP1 | 15758: DUP3 | 15759: PUSH1 0x00 | 15761: NOT | 15762: DIV | 15763: DUP3 | 15764: GT | 15765: DUP4 | 15766: ISZERO | 15767: ISZERO | 15768: AND | 15769: PUSH2 0x32b8 | 15772: JUMPI
15773: JUMPDEST | 15774: PUSH1 0x01 | 15776: PUSH1 0x01 | 15778: PUSH1 0x40 | 15780: SHL | 15781: SUB | 15782: AND | 15783: SWAP2 | 15784: DUP3 | 15785: ISZERO | 15786: PUSH2 0x32ab | 15789: JUMPI
15790: JUMPDEST | 15791: MUL | 15792: DIV | 15793: PUSH2 0x32c5 | 15796: JUMP
15797: JUMPDEST | 15798: PUSH2 0x32b3 | 15801: PUSH2 0x23bf | 15804: JUMP
15805: JUMPDEST | 15806: PUSH2 0x32a4 | 15809: JUMP
15810: JUMPDEST | 15811: PUSH2 0x32c0 | 15814: PUSH2 0x1e32 | 15817: JUMP
15818: JUMPDEST | 15819: PUSH2 0x3293 | 15822: JUMP
15823: JUMPDEST | 15824: PUSH1 0x01 | 15826: PUSH1 0x01 | 15828: PUSH1 0x68 | 15830: SHL | 15831: SUB | 15832: SWAP1 | 15833: DUP2 | 15834: DUP2 | 15835: GT | 15836: PUSH2 0x32d9 | 15839: JUMPI
15840: AND | 15841: SWAP1 | 15842: JUMP
15843: JUMPDEST | 15844: PUSH1 0x40 | 15846: MLOAD | 15847: PUSH4 0x0dc79255 | 15852: PUSH1 0xe1 | 15854: SHL | 15855: DUP2 | 15856: MSTORE | 15857: PUSH1 0x04 | 15859: SWAP1 | 15860: REVERT
15861: JUMPDEST | 15862: PUSH1 0x01 | 15864: PUSH1 0x01 | 15866: PUSH1 0x68 | 15868: SHL | 15869: SUB | 15870: AND | 15871: PUSH1 0x01 | 15873: PUSH1 0x01 | 15875: PUSH1 0x67 | 15877: SHL | 15878: SUB | 15879: DUP2 | 15880: GT | 15881: PUSH2 0x3308 | 15884: JUMPI
15885: PUSH1 0x0c | 15887: SIGNEXTEND | 15888: SWAP1 | 15889: JUMP
15890: JUMPDEST | 15891: PUSH1 0x40 | 15893: MLOAD | 15894: PUSH4 0x9369ae35 | 15899: PUSH1 0xe0 | 15901: SHL | 15902: DUP2 | 15903: MSTORE | 15904: PUSH1 0x04 | 15906: SWAP1 | 15907: REVERT
15908: JUMPDEST | 15909: PUSH1 0x0c | 15911: SWAP2 | 15912: DUP3 | 15913: SIGNEXTEND | 15914: SWAP2 | 15915: SIGNEXTEND | 15916: PUSH1 0x00 | 15918: DUP3 | 15919: SLT | 15920: DUP1 | 15921: ISZERO | 15922: PUSH1 0x01 | 15924: PUSH1 0x01 | 15926: PUSH1 0x67 | 15928: SHL | 15929: SUB | 15930: NOT | 15931: DUP5 | 15932: ADD | 15933: DUP4 | 15934: SLT | 15935: AND | 15936: PUSH2 0x334f | 15939: JUMPI
15940: JUMPDEST | 15941: PUSH1 0x01 | 15943: PUSH1 0x01 | 15945: PUSH1 0x67 | 15947: SHL | 15948: SUB | 15949: DUP4 | 15950: ADD | 15951: DUP3 | 15952: SGT | 15953: AND | 15954: PUSH2 0x1e5f | 15957: JUMPI
15958: SUB | 15959: SWAP1 | 15960: JUMP
15961: JUMPDEST | 15962: PUSH2 0x3357 | 15965: PUSH2 0x1e32 | 15968: JUMP
15969: JUMPDEST | 15970: PUSH2 0x333a | 15973: JUMP
15974: JUMPDEST | 15975: SWAP2 | 15976: SWAP1 | 15977: SWAP2 | 15978: DUP1 | 15979: PUSH1 0x0c | 15981: SIGNEXTEND | 15982: DUP4 | 15983: PUSH1 0x0c | 15985: SIGNEXTEND | 15986: DUP2 | 15987: DUP2 | 15988: SLT | 15989: PUSH2 0x33cb | 15992: JUMPI
15993: PUSH1 0x00 | 15995: SLT | 15996: PUSH2 0x338f | 15999: JUMPI
16000: POP | 16001: PUSH2 0x3380 | 16004: SWAP2 | 16005: SWAP3 | 16006: PUSH2 0x331a | 16009: JUMP
16010: JUMPDEST | 16011: PUSH1 0x01 | 16013: PUSH1 0x01 | 16015: PUSH1 0x68 | 16017: SHL | 16018: SUB | 16019: AND | 16020: SWAP1 | 16021: PUSH1 0x00 | 16023: SWAP1 | 16024: JUMP
16025: JUMPDEST | 16026: PUSH1 0x00 | 16028: SGT | 16029: PUSH2 0x33b2 | 16032: JUMPI
16033: PUSH2 0x33a0 | 16036: SWAP2 | 16037: SWAP3 | 16038: PUSH2 0x331a | 16041: JUMP
16042: JUMPDEST | 16043: PUSH1 0x00 | 16045: SWAP2 | 16046: PUSH1 0x01 | 16048: PUSH1 0x01 | 16050: PUSH1 0x68 | 16052: SHL | 16053: SUB | 16054: SWAP2 | 16055: SWAP1 | 16056: SWAP2 | 16057: AND | 16058: SWAP1 | 16059: JUMP
16060: JUMPDEST | 16061: PUSH2 0x33bb | 16064: SWAP1 | 16065: PUSH2 0x2989 | 16068: JUMP
16069: JUMPDEST | 16070: PUSH1 0x01 | 16072: PUSH1 0x01 | 16074: PUSH1 0x68 | 16076: SHL | 16077: SUB | 16078: SWAP1 | 16079: DUP2 | 16080: AND | 16081: SWAP3 | 16082: AND | 16083: SWAP1 | 16084: JUMP
16085: JUMPDEST | 16086: POP | 16087: POP | 16088: POP | 16089: SWAP1 | 16090: POP | 16091: PUSH1 0x00 | 16093: SWAP1 | 16094: PUSH1 0x00 | 16096: SWAP1 | 16097: JUMP
16098: JUMPDEST | 16099: PUSH1 0x40 | 16101: MLOAD | 16102: PUSH4 0x70a08231 | 16107: PUSH1 0xe0 | 16109: SHL | 16110: DUP1 | 16111: DUP3 | 16112: MSTORE | 16113: SWAP4 | 16114: SWAP1 | 16115: SWAP3 | 16116: PUSH1 0x20 | 16118: SWAP3 | 16119: PUSH1 0x01 | 16121: PUSH1 0x01 | 16123: PUSH1 0xa0 | 16125: SHL | 16126: SUB | 16127: AND | 16128: SWAP2 | 16129: SWAP1 | 16130: DUP4 | 16131: DUP6 | 16132: DUP1 | 16133: PUSH2 0x3407 | 16136: ADDRESS | 16137: PUSH1 0x04 | 16139: DUP4 | 16140: ADD | 16141: PUSH2 0x060e | 16144: JUMP
16145: JUMPDEST | 16146: SUB | 16147: DUP2 | 16148: DUP7 | 16149: GAS | 16150: STATICCALL | 16151: SWAP5 | 16152: DUP6 | 16153: ISZERO | 16154: PUSH2 0x3545 | 16157: JUMPI
16158: JUMPDEST | 16159: PUSH1 0x00 | 16161: SWAP6 | 16162: PUSH2 0x3526 | 16165: JUMPI
16166: JUMPDEST | 16167: POP | 16168: DUP3 | 16169: EXTCODESIZE | 16170: ISZERO | 16171: PUSH2 0x0582 | 16174: JUMPI
16175: PUSH1 0x40 | 16177: MLOAD | 16178: PUSH4 0x23b872dd | 16183: PUSH1 0xe0 | 16185: SHL | 16186: DUP2 | 16187: MSTORE | 16188: PUSH1 0x01 | 16190: PUSH1 0x01 | 16192: PUSH1 0xa0 | 16194: SHL | 16195: SUB | 16196: SWAP2 | 16197: SWAP1 | 16198: SWAP2 | 16199: AND | 16200: PUSH1 0x04 | 16202: DUP3 | 16203: ADD | 16204: MSTORE | 16205: ADDRESS | 16206: PUSH1 0x24 | 16208: DUP3 | 16209: ADD | 16210: MSTORE | 16211: PUSH1 0x44 | 16213: DUP2 | 16214: ADD | 16215: SWAP2 | 16216: SWAP1 | 16217: SWAP2 | 16218: MSTORE | 16219: PUSH1 0x00 | 16221: DUP2 | 16222: PUSH1 0x64 | 16224: DUP2 | 16225: DUP4 | 16226: DUP7 | 16227: GAS | 16228: CALL | 16229: DUP1 | 16230: ISZERO | 16231: PUSH2 0x3519 | 16234: JUMPI
16235: JUMPDEST | 16236: PUSH2 0x3504 | 16239: JUMPI
16240: JUMPDEST | 16241: POP | 16242: RETURNDATASIZE | 16243: DUP1 | 16244: ISZERO | 16245: PUSH2 0x34fb | 16248: JUMPI
16249: PUSH1 0x20 | 16251: EQ | 16252: PUSH2 0x347a | 16255: JUMPI
16256: PUSH1 0x00 | 16258: DUP1 | 16259: REVERT
16260: JUMPDEST | 16261: DUP2 | 16262: PUSH1 0x00 | 16264: DUP1 | 16265: RETURNDATACOPY | 16266: PUSH1 0x00 | 16268: MLOAD
16269: JUMPDEST | 16270: ISZERO | 16271: PUSH2 0x34e9 | 16274: JUMPI
16275: DUP2 | 16276: PUSH2 0x0979 | 16279: SWAP5 | 16280: PUSH1 0x40 | 16282: MLOAD | 16283: SWAP3 | 16284: DUP4 | 16285: SWAP2 | 16286: DUP3 | 16287: MSTORE | 16288: DUP2 | 16289: DUP1 | 16290: PUSH2 0x34a4 | 16293: ADDRESS | 16294: PUSH1 0x04 | 16296: DUP4 | 16297: ADD | 16298: PUSH2 0x060e | 16301: JUMP
16302: JUMPDEST | 16303: SUB | 16304: SWAP2 | 16305: GAS | 16306: STATICCALL | 16307: SWAP2 | 16308: DUP3 | 16309: ISZERO | 16310: PUSH2 0x34dc | 16313: JUMPI
16314: JUMPDEST | 16315: PUSH1 0x00 | 16317: SWAP3 | 16318: PUSH2 0x34bf | 16321: JUMPI
16322: JUMPDEST | 16323: POP | 16324: POP | 16325: PUSH2 0x219b | 16328: JUMP
16329: JUMPDEST | 16330: PUSH2 0x34d5 | 16333: SWAP3 | 16334: POP | 16335: DUP1 | 16336: RETURNDATASIZE | 16337: LT | 16338: PUSH2 0x25dd | 16341: JUMPI
16342: PUSH2 0x25ce | 16345: DUP2 | 16346: DUP4 | 16347: PUSH2 0x1b46 | 16350: JUMP
16351: JUMPDEST | 16352: CODESIZE | 16353: DUP1 | 16354: PUSH2 0x34b8 | 16357: JUMP
16358: JUMPDEST | 16359: PUSH2 0x34e4 | 16362: PUSH2 0x1bfe | 16365: JUMP
16366: JUMPDEST | 16367: PUSH2 0x34b0 | 16370: JUMP
16371: JUMPDEST | 16372: PUSH1 0x40 | 16374: MLOAD | 16375: PUSH4 0x073d1efd | 16380: PUSH1 0xe5 | 16382: SHL | 16383: DUP2 | 16384: MSTORE | 16385: PUSH1 0x04 | 16387: SWAP1 | 16388: REVERT
16389: JUMPDEST | 16390: POP | 16391: PUSH1 0x00 | 16393: NOT | 16394: PUSH2 0x3483 | 16397: JUMP
16398: JUMPDEST | 16399: DUP1 | 16400: PUSH2 0x1485 | 16403: PUSH1 0x00 | 16405: PUSH2 0x3513 | 16408: SWAP4 | 16409: PUSH2 0x1b46 | 16412: JUMP
16413: JUMPDEST | 16414: CODESIZE | 16415: PUSH2 0x3466 | 16418: JUMP
16419: JUMPDEST | 16420: PUSH2 0x3521 | 16423: PUSH2 0x1bfe | 16426: JUMP
16427: JUMPDEST | 16428: PUSH2 0x3461 | 16431: JUMP
16432: JUMPDEST | 16433: PUSH2 0x353e | 16436: SWAP2 | 16437: SWAP6 | 16438: POP | 16439: DUP5 | 16440: RETURNDATASIZE | 16441: DUP7 | 16442: GT | 16443: PUSH2 0x25dd | 16446: JUMPI
16447: PUSH2 0x25ce | 16450: DUP2 | 16451: DUP4 | 16452: PUSH2 0x1b46 | 16455: JUMP
16456: JUMPDEST | 16457: SWAP4 | 16458: CODESIZE | 16459: PUSH2 0x341c | 16462: JUMP
16463: JUMPDEST | 16464: PUSH2 0x354d | 16467: PUSH2 0x1bfe | 16470: JUMP
16471: JUMPDEST | 16472: PUSH2 0x3414 | 16475: JUMP
16476: JUMPDEST | 16477: SWAP1 | 16478: PUSH1 0x40 | 16480: MLOAD | 16481: PUSH2 0x3561 | 16484: PUSH1 0x40 | 16486: DUP3 | 16487: PUSH2 0x1b46 | 16490: JUMP
16491: JUMPDEST | 16492: SWAP2 | 16493: SLOAD | 16494: PUSH1 0x01 | 16496: PUSH1 0x01 | 16498: PUSH1 0x80 | 16500: SHL | 16501: SUB | 16502: DUP2 | 16503: AND | 16504: DUP4 | 16505: MSTORE | 16506: PUSH1 0x80 | 16508: SHR | 16509: PUSH1 0x20 | 16511: DUP4 | 16512: ADD | 16513: MSTORE | 16514: JUMP
16515: JUMPDEST | 16516: PUSH1 0x01 | 16518: PUSH1 0x01 | 16520: PUSH1 0x80 | 16522: SHL | 16523: SUB | 16524: SWAP2 | 16525: DUP3 | 16526: AND | 16527: SWAP2 | 16528: SWAP1 | 16529: DUP2 | 16530: AND | 16531: SWAP1 | 16532: DUP3 | 16533: SWAP1 | 16534: SUB | 16535: DUP2 | 16536: GT | 16537: PUSH2 0x1eb3 | 16540: JUMPI
16541: ADD | 16542: SWAP1 | 16543: JUMP
16544: JUMPDEST | 16545: DUP1 | 16546: SLOAD | 16547: PUSH1 0x01 | 16549: PUSH1 0x01 | 16551: PUSH1 0x80 | 16553: SHL | 16554: SUB | 16555: NOT | 16556: AND | 16557: PUSH1 0x01 | 16559: PUSH1 0x01 | 16561: PUSH1 0x80 | 16563: SHL | 16564: SUB | 16565: SWAP1 | 16566: SWAP3 | 16567: AND | 16568: SWAP2 | 16569: SWAP1 | 16570: SWAP2 | 16571: OR | 16572: SWAP1 | 16573: SSTORE | 16574: JUMP
16575: JUMPDEST | 16576: SWAP1 | 16577: PUSH1 0x20 | 16579: PUSH1 0x01 | 16581: DUP1 | 16582: PUSH1 0x80 | 16584: SHL | 16585: SUB | 16586: SWAP2 | 16587: PUSH2 0x35cd | 16590: DUP4 | 16591: DUP3 | 16592: MLOAD | 16593: AND | 16594: DUP6 | 16595: PUSH2 0x3596 | 16598: JUMP
16599: JUMPDEST | 16600: ADD | 16601: MLOAD | 16602: DUP3 | 16603: SLOAD | 16604: SWAP1 | 16605: SWAP2 | 16606: AND | 16607: PUSH1 0x80 | 16609: SWAP2 | 16610: SWAP1 | 16611: SWAP2 | 16612: SHL | 16613: PUSH1 0x01 | 16615: PUSH1 0x01 | 16617: PUSH1 0x80 | 16619: SHL | 16620: SUB | 16621: NOT | 16622: AND | 16623: OR | 16624: SWAP1 | 16625: SSTORE | 16626: JUMP
16627: JUMPDEST | 16628: PUSH1 0x01 | 16630: PUSH1 0x01 | 16632: PUSH1 0x80 | 16634: SHL | 16635: SUB | 16636: SWAP1 | 16637: SWAP2 | 16638: AND | 16639: DUP2 | 16640: MSTORE | 16641: PUSH1 0x20 | 16643: ADD | 16644: SWAP1 | 16645: JUMP
16646: JUMPDEST | 16647: SWAP2 | 16648: SWAP1 | 16649: SWAP3 | 16650: PUSH2 0x361b | 16653: PUSH2 0x3616 | 16656: PUSH1 0x01 | 16658: DUP1 | 16659: PUSH1 0x80 | 16661: SHL | 16662: SUB | 16663: DUP1 | 16664: SWAP4 | 16665: AND | 16666: DUP6 | 16667: DUP6 | 16668: PUSH2 0x33d8 | 16671: JUMP
16672: JUMPDEST | 16673: PUSH2 0x2faf | 16676: JUMP
16677: JUMPDEST | 16678: SWAP2 | 16679: PUSH2 0x3625 | 16682: DUP2 | 16683: PUSH2 0x1d3a | 16686: JUMP
16687: JUMPDEST | 16688: SWAP1 | 16689: PUSH2 0x3639 | 16692: PUSH2 0x3634 | 16695: DUP3 | 16696: PUSH1 0x02 | 16698: PUSH2 0x097c | 16701: JUMP
16702: JUMPDEST | 16703: PUSH2 0x3552 | 16706: JUMP
16707: JUMPDEST | 16708: SWAP3 | 16709: PUSH2 0x365d | 16712: PUSH2 0x3650 | 16715: DUP7 | 16716: PUSH2 0x364b | 16719: DUP8 | 16720: MLOAD | 16721: PUSH2 0x0993 | 16724: JUMP
16725: JUMPDEST | 16726: PUSH2 0x3579 | 16729: JUMP
16730: JUMPDEST | 16731: PUSH1 0x01 | 16733: PUSH1 0x01 | 16735: PUSH1 0x80 | 16737: SHL | 16738: SUB | 16739: AND | 16740: DUP6 | 16741: MSTORE | 16742: JUMP
16743: JUMPDEST | 16744: PUSH2 0x3667 | 16747: DUP5 | 16748: MLOAD | 16749: PUSH2 0x0993 | 16752: JUMP
16753: JUMPDEST | 16754: SWAP1 | 16755: PUSH2 0x3678 | 16758: PUSH2 0x19af | 16761: PUSH1 0xe0 | 16763: DUP7 | 16764: ADD | 16765: MLOAD | 16766: PUSH2 0x0993 | 16769: JUMP
16770: JUMPDEST | 16771: SWAP2 | 16772: AND | 16773: GT | 16774: PUSH2 0x3722 | 16777: JUMPI
16778: PUSH2 0x36fd | 16781: PUSH2 0x36eb | 16784: DUP6 | 16785: PUSH2 0x371d | 16788: SWAP5 | 16789: PUSH2 0x36f7 | 16792: PUSH32 0xfa56f7b24f17183d81894d3ac2ee654e3c26388d17a28dbd9549b8114304e1f4 | 16825: SWAP8 | 16826: PUSH2 0x36f2 | 16829: DUP8 | 16830: PUSH2 0x36cc | 16833: DUP15 | 16834: PUSH2 0x36d8 | 16837: PUSH2 0x36d1 | 16840: PUSH2 0x2916 | 16843: DUP6 | 16844: PUSH2 0x36cc | 16847: DUP6 | 16848: PUSH1 0x06 | 16850: PUSH2 0x097c | 16853: JUMP
16854: JUMPDEST | 16855: PUSH2 0x097c | 16858: JUMP
16859: JUMPDEST | 16860: SWAP9 | 16861: DUP10 | 16862: PUSH2 0x3579 | 16865: JUMP
16866: JUMPDEST | 16867: SWAP9 | 16868: DUP10 | 16869: SWAP6 | 16870: PUSH2 0x36e6 | 16873: DUP6 | 16874: PUSH1 0x02 | 16876: PUSH2 0x097c | 16879: JUMP
16880: JUMPDEST | 16881: PUSH2 0x35b5 | 16884: JUMP
16885: JUMPDEST | 16886: PUSH1 0x06 | 16888: PUSH2 0x097c | 16891: JUMP
16892: JUMPDEST | 16893: PUSH2 0x3596 | 16896: JUMP
16897: JUMPDEST | 16898: DUP10 | 16899: PUSH2 0x3734 | 16902: JUMP
16903: JUMPDEST | 16904: PUSH1 0x40 | 16906: MLOAD | 16907: PUSH1 0x01 | 16909: PUSH1 0x01 | 16911: PUSH1 0xa0 | 16913: SHL | 16914: SUB | 16915: SWAP2 | 16916: DUP3 | 16917: AND | 16918: SWAP7 | 16919: DUP3 | 16920: AND | 16921: SWAP6 | 16922: SWAP1 | 16923: SWAP2 | 16924: AND | 16925: SWAP4 | 16926: SWAP1 | 16927: SWAP2 | 16928: DUP3 | 16929: SWAP2 | 16930: DUP3 | 16931: PUSH2 0x35e9 | 16934: JUMP
16935: JUMPDEST | 16936: SUB | 16937: SWAP1 | 16938: LOG4 | 16939: JUMP
16940: JUMPDEST | 16941: PUSH1 0x40 | 16943: MLOAD | 16944: PUSH4 0x7ac7b99d | 16949: PUSH1 0xe1 | 16951: SHL | 16952: DUP2 | 16953: MSTORE | 16954: PUSH1 0x04 | 16956: SWAP1 | 16957: REVERT
16958: JUMPDEST | 16959: SWAP1 | 16960: SWAP3 | 16961: SWAP1 | 16962: SWAP2 | 16963: PUSH1 0x01 | 16965: PUSH1 0x01 | 16967: PUSH1 0x80 | 16969: SHL | 16970: SUB | 16971: SWAP1 | 16972: DUP2 | 16973: AND | 16974: ISZERO | 16975: DUP1 | 16976: DUP1 | 16977: PUSH2 0x3895 | 16980: JUMPI
16981: JUMPDEST | 16982: ISZERO | 16983: PUSH2 0x37f1 | 16986: JUMPI
16987: POP | 16988: POP | 16989: POP | 16990: PUSH2 0x375e | 16993: DUP3 | 16994: MLOAD | 16995: PUSH1 0xff | 16997: AND | 16998: SWAP1 | 16999: JUMP
17000: JUMPDEST | 17001: PUSH1 0xff | 17003: DUP2 | 17004: AND | 17005: PUSH1 0x10 | 17007: DUP2 | 17008: LT | 17009: ISZERO | 17010: PUSH2 0x37b0 | 17013: JUMPI
17014: POP | 17015: POP | 17016: PUSH2 0x3798 | 17019: PUSH2 0x3790 | 17022: PUSH2 0x3781 | 17025: PUSH2 0x0c31 | 17028: SWAP5 | 17029: MLOAD | 17030: PUSH1 0xff | 17032: AND | 17033: SWAP1 | 17034: JUMP
17035: JUMPDEST | 17036: PUSH1 0x01 | 17038: PUSH1 0xff | 17040: SWAP1 | 17041: SWAP2 | 17042: AND | 17043: SHL | 17044: PUSH2 0xffff | 17047: AND | 17048: SWAP1 | 17049: JUMP
17050: JUMPDEST | 17051: SWAP2 | 17052: PUSH1 0x05 | 17054: PUSH2 0x097c | 17057: JUMP
17058: JUMPDEST | 17059: SWAP1 | 17060: PUSH2 0x37a9 | 17063: DUP3 | 17064: SLOAD | 17065: PUSH2 0xffff | 17068: SWAP1 | 17069: PUSH1 0xe8 | 17071: SHR | 17072: AND | 17073: SWAP1 | 17074: JUMP
17075: JUMPDEST | 17076: OR | 17077: SWAP1 | 17078: PUSH2 0x2d1b | 17081: JUMP
17082: JUMPDEST | 17083: PUSH1 0x18 | 17085: SWAP2 | 17086: SWAP4 | 17087: POP | 17088: LT | 17089: PUSH2 0x37be | 17092: JUMPI
17093: POP | 17094: POP | 17095: JUMP
17096: JUMPDEST | 17097: PUSH2 0x37de | 17100: PUSH2 0x3790 | 17103: PUSH2 0x37d2 | 17106: PUSH1 0x10 | 17108: PUSH2 0x0c31 | 17111: SWAP6 | 17112: PUSH2 0x2cae | 17115: JUMP
17116: JUMPDEST | 17117: PUSH1 0x01 | 17119: PUSH1 0xff | 17121: SWAP2 | 17122: DUP3 | 17123: AND | 17124: SHL | 17125: AND | 17126: SWAP1 | 17127: JUMP
17128: JUMPDEST | 17129: SWAP1 | 17130: PUSH2 0x37ea | 17133: DUP3 | 17134: SLOAD | 17135: PUSH1 0xf8 | 17137: SHR | 17138: SWAP1 | 17139: JUMP
17140: JUMPDEST | 17141: OR | 17142: SWAP1 | 17143: PUSH2 0x2b4b | 17146: JUMP
17147: JUMPDEST | 17148: ISZERO | 17149: SWAP2 | 17150: DUP3 | 17151: PUSH2 0x388a | 17154: JUMPI
17155: JUMPDEST | 17156: POP | 17157: POP | 17158: PUSH2 0x3803 | 17161: JUMPI
17162: POP | 17163: POP | 17164: JUMP
17165: JUMPDEST | 17166: DUP2 | 17167: MLOAD | 17168: PUSH1 0xff | 17170: AND | 17171: DUP1 | 17172: PUSH1 0x10 | 17174: DUP2 | 17175: LT | 17176: ISZERO | 17177: PUSH2 0x384b | 17180: JUMPI
17181: POP | 17182: POP | 17183: PUSH2 0x3833 | 17186: PUSH2 0x3790 | 17189: PUSH2 0x382b | 17192: PUSH2 0x3781 | 17195: PUSH2 0x0c31 | 17198: SWAP6 | 17199: MLOAD | 17200: PUSH1 0xff | 17202: AND | 17203: SWAP1 | 17204: JUMP
17205: JUMPDEST | 17206: NOT | 17207: PUSH2 0xffff | 17210: AND | 17211: SWAP1 | 17212: JUMP
17213: JUMPDEST | 17214: SWAP1 | 17215: PUSH2 0x3844 | 17218: DUP3 | 17219: SLOAD | 17220: PUSH2 0xffff | 17223: SWAP1 | 17224: PUSH1 0xe8 | 17226: SHR | 17227: AND | 17228: SWAP1 | 17229: JUMP
17230: JUMPDEST | 17231: AND | 17232: SWAP1 | 17233: PUSH2 0x2d1b | 17236: JUMP
17237: JUMPDEST | 17238: PUSH1 0x18 | 17240: SWAP2 | 17241: SWAP4 | 17242: POP | 17243: LT | 17244: PUSH2 0x3859 | 17247: JUMPI
17248: POP | 17249: POP | 17250: JUMP
17251: JUMPDEST | 17252: PUSH2 0x3877 | 17255: PUSH2 0x3790 | 17258: PUSH2 0x3870 | 17261: PUSH2 0x37d2 | 17264: PUSH1 0x10 | 17266: PUSH2 0x0c31 | 17269: SWAP7 | 17270: PUSH2 0x2cae | 17273: JUMP
17274: JUMPDEST | 17275: NOT | 17276: PUSH1 0xff | 17278: AND | 17279: SWAP1 | 17280: JUMP
17281: JUMPDEST | 17282: SWAP1 | 17283: PUSH2 0x3883 | 17286: DUP3 | 17287: SLOAD | 17288: PUSH1 0xf8 | 17290: SHR | 17291: SWAP1 | 17292: JUMP
17293: JUMPDEST | 17294: AND | 17295: SWAP1 | 17296: PUSH2 0x2b4b | 17299: JUMP
17300: JUMPDEST | 17301: AND | 17302: ISZERO | 17303: SWAP1 | 17304: POP | 17305: CODESIZE | 17306: DUP1 | 17307: PUSH2 0x37f9 | 17310: JUMP
17311: JUMPDEST | 17312: POP | 17313: DUP2 | 17314: DUP4 | 17315: AND | 17316: ISZERO | 17317: ISZERO | 17318: PUSH2 0x374b | 17321: JUMP
17322: JUMPDEST | 17323: SWAP4 | 17324: SWAP3 | 17325: SWAP1 | 17326: SWAP4 | 17327: PUSH1 0x02 | 17329: PUSH1 0x01 | 17331: SLOAD | 17332: PUSH1 0xf8 | 17334: SHR | 17335: AND | 17336: PUSH2 0x1a47 | 17339: JUMPI
17340: PUSH2 0x2f40 | 17343: PUSH2 0x38be | 17346: SWAP2 | 17347: DUP7 | 17348: PUSH2 0x1b09 | 17351: JUMP
17352: JUMPDEST | 17353: PUSH2 0x0e62 | 17356: JUMPI
17357: PUSH1 0x01 | 17359: PUSH1 0x01 | 17361: PUSH1 0xa0 | 17363: SHL | 17364: SUB | 17365: DUP5 | 17366: DUP2 | 17367: AND | 17368: DUP4 | 17369: DUP3 | 17370: AND | 17371: EQ | 17372: PUSH2 0x3936 | 17375: JUMPI
17376: DUP1 | 17377: PUSH32 0x0000000000000000000000000000000000000000000000000000000000000000 | 17410: AND | 17411: SWAP1 | 17412: DUP3 | 17413: AND | 17414: EQ | 17415: PUSH1 0x00 | 17417: EQ | 17418: PUSH2 0x3922 | 17421: JUMPI
17422: POP | 17423: PUSH2 0x0c31 | 17426: SWAP3 | 17427: PUSH1 0x00 | 17429: NOT | 17430: DUP4 | 17431: SUB | 17432: PUSH2 0x3948 | 17435: JUMPI
17436: SWAP2 | 17437: POP | 17438: PUSH2 0x391c | 17441: DUP3 | 17442: PUSH2 0x474c | 17445: JUMP
17446: JUMPDEST | 17447: SWAP2 | 17448: PUSH2 0x3948 | 17451: JUMP
17452: JUMPDEST | 17453: SWAP1 | 17454: PUSH2 0x3930 | 17457: PUSH2 0x0c31 | 17460: SWAP5 | 17461: SWAP4 | 17462: PUSH2 0x2faf | 17465: JUMP
17466: JUMPDEST | 17467: SWAP3 | 17468: PUSH2 0x3be1 | 17471: JUMP
17472: JUMPDEST | 17473: PUSH1 0x40 | 17475: MLOAD | 17476: PUSH4 0xe397a99b | 17481: PUSH1 0xe0 | 17483: SHL | 17484: DUP2 | 17485: MSTORE | 17486: PUSH1 0x04 | 17488: SWAP1 | 17489: REVERT
17490: JUMPDEST | 17491: SWAP2 | 17492: SWAP1 | 17493: SWAP2 | 17494: PUSH2 0x3953 | 17497: PUSH2 0x1ece | 17500: JUMP
17501: JUMPDEST | 17502: PUSH2 0x395e | 17505: DUP2 | 17506: PUSH1 0x05 | 17508: PUSH2 0x097c | 17511: JUMP
17512: JUMPDEST | 17513: PUSH2 0x3967 | 17516: SWAP1 | 17517: PUSH2 0x1de7 | 17520: JUMP
17521: JUMPDEST | 17522: PUSH2 0x3972 | 17525: DUP5 | 17526: PUSH1 0x05 | 17528: PUSH2 0x097c | 17531: JUMP
17532: JUMPDEST | 17533: PUSH2 0x397b | 17536: SWAP1 | 17537: PUSH2 0x1de7 | 17540: JUMP
17541: JUMPDEST | 17542: SWAP3 | 17543: DUP2 | 17544: MLOAD | 17545: PUSH2 0x3988 | 17548: SWAP1 | 17549: PUSH1 0x0c | 17551: SIGNEXTEND | 17552: SWAP1 | 17553: JUMP
17554: JUMPDEST | 17555: SWAP4 | 17556: DUP1 | 17557: MLOAD | 17558: PUSH2 0x3995 | 17561: SWAP1 | 17562: PUSH1 0x0c | 17564: SIGNEXTEND | 17565: SWAP1 | 17566: JUMP
17567: JUMPDEST | 17568: SWAP3 | 17569: PUSH2 0x399f | 17572: DUP7 | 17573: PUSH2 0x29c0 | 17576: JUMP
17577: JUMPDEST | 17578: PUSH2 0x39a8 | 17581: DUP5 | 17582: PUSH2 0x2791 | 17585: JUMP
17586: JUMPDEST | 17587: PUSH2 0x39b1 | 17590: SWAP2 | 17591: PUSH2 0x25f1 | 17594: JUMP
17595: JUMPDEST | 17596: SWAP3 | 17597: PUSH2 0x39bb | 17600: DUP6 | 17601: PUSH2 0x29c0 | 17604: JUMP
17605: JUMPDEST | 17606: SWAP1 | 17607: PUSH2 0x39c5 | 17610: SWAP1 | 17611: PUSH2 0x2791 | 17614: JUMP
17615: JUMPDEST | 17616: PUSH2 0x39ce | 17619: SWAP2 | 17620: PUSH2 0x2628 | 17623: JUMP
17624: JUMPDEST | 17625: SWAP1 | 17626: PUSH2 0x39d8 | 17629: DUP5 | 17630: PUSH2 0x31c6 | 17633: JUMP
17634: JUMPDEST | 17635: PUSH2 0x39e2 | 17638: DUP2 | 17639: SWAP4 | 17640: PUSH2 0x31c6 | 17643: JUMP
17644: JUMPDEST | 17645: SWAP8 | 17646: DUP9 | 17647: SWAP4 | 17648: PUSH2 0x39ee | 17651: SWAP2 | 17652: PUSH2 0x3b7c | 17655: JUMP
17656: JUMPDEST | 17657: SWAP9 | 17658: PUSH2 0x39f9 | 17661: SWAP2 | 17662: SWAP8 | 17663: PUSH2 0x335c | 17666: JUMP
17667: JUMPDEST | 17668: SWAP9 | 17669: DUP8 | 17670: DUP11 | 17671: PUSH1 0x01 | 17673: SLOAD | 17674: PUSH2 0x3a08 | 17677: SWAP1 | 17678: PUSH2 0x1e6b | 17681: JUMP
17682: JUMPDEST | 17683: SWAP1 | 17684: PUSH2 0x3a12 | 17687: SWAP2 | 17688: PUSH2 0x3005 | 17691: JUMP
17692: JUMPDEST | 17693: SWAP1 | 17694: PUSH2 0x3a1c | 17697: SWAP2 | 17698: PUSH2 0x3041 | 17701: JUMP
17702: JUMPDEST | 17703: PUSH2 0x3a27 | 17706: SWAP1 | 17707: PUSH1 0x01 | 17709: PUSH2 0x3022 | 17712: JUMP
17713: JUMPDEST | 17714: PUSH1 0x01 | 17716: SLOAD | 17717: PUSH2 0x3a33 | 17720: SWAP1 | 17721: PUSH2 0x1ebf | 17724: JUMP
17725: JUMPDEST | 17726: SWAP1 | 17727: PUSH2 0x3a3d | 17730: SWAP2 | 17731: PUSH2 0x3005 | 17734: JUMP
17735: JUMPDEST | 17736: SWAP1 | 17737: PUSH2 0x3a47 | 17740: SWAP2 | 17741: PUSH2 0x3041 | 17744: JUMP
17745: JUMPDEST | 17746: PUSH2 0x3a52 | 17749: SWAP1 | 17750: PUSH1 0x01 | 17752: PUSH2 0x3059 | 17755: JUMP
17756: JUMPDEST | 17757: PUSH2 0x3a5c | 17760: SWAP2 | 17761: DUP8 | 17762: PUSH2 0x2db5 | 17765: JUMP
17766: JUMPDEST | 17767: PUSH2 0x3a66 | 17770: SWAP2 | 17771: DUP8 | 17772: PUSH2 0x2db5 | 17775: JUMP
17776: JUMPDEST | 17777: PUSH1 0x00 | 17779: DUP2 | 17780: SLT | 17781: PUSH2 0x3b13 | 17784: JUMPI
17785: JUMPDEST | 17786: POP | 17787: PUSH1 0x01 | 17789: PUSH1 0x01 | 17791: PUSH1 0x68 | 17793: SHL | 17794: SUB | 17795: SWAP2 | 17796: DUP2 | 17797: DUP4 | 17798: AND | 17799: PUSH2 0x3acb | 17802: JUMPI
17803: JUMPDEST | 17804: POP | 17805: POP | 17806: DUP2 | 17807: AND | 17808: PUSH2 0x3a8d | 17811: JUMPI
17812: POP | 17813: POP | 17814: JUMP
17815: JUMPDEST | 17816: PUSH1 0x00 | 17818: DUP1 | 17819: MLOAD | 17820: PUSH1 0x20 | 17822: PUSH2 0x4832 | 17825: DUP4 | 17826: CODECOPY | 17827: DUP2 | 17828: MLOAD | 17829: SWAP2 | 17830: MSTORE | 17831: PUSH2 0x31c1 | 17834: PUSH2 0x3aaf | 17837: PUSH1 0x00 | 17839: SWAP4 | 17840: PUSH2 0x31ac | 17843: DUP6 | 17844: SLOAD | 17845: PUSH2 0x0b8f | 17848: JUMP
17849: JUMPDEST | 17850: PUSH1 0x40 | 17852: MLOAD | 17853: SWAP1 | 17854: DUP2 | 17855: MSTORE | 17856: PUSH1 0x01 | 17858: PUSH1 0x01 | 17860: PUSH1 0xa0 | 17862: SHL | 17863: SUB | 17864: SWAP1 | 17865: SWAP5 | 17866: AND | 17867: SWAP4 | 17868: SWAP1 | 17869: DUP2 | 17870: SWAP1 | 17871: PUSH1 0x20 | 17873: DUP3 | 17874: ADD | 17875: SWAP1 | 17876: JUMP
17877: JUMPDEST | 17878: PUSH1 0x00 | 17880: DUP1 | 17881: MLOAD | 17882: PUSH1 0x20 | 17884: PUSH2 0x4832 | 17887: DUP4 | 17888: CODECOPY | 17889: DUP2 | 17890: MLOAD | 17891: SWAP2 | 17892: MSTORE | 17893: PUSH2 0x3b09 | 17896: PUSH2 0x3aed | 17899: PUSH1 0x00 | 17901: SWAP5 | 17902: PUSH2 0x31ac | 17905: DUP7 | 17906: SLOAD | 17907: PUSH2 0x0b8f | 17910: JUMP
17911: JUMPDEST | 17912: PUSH1 0x40 | 17914: MLOAD | 17915: SWAP1 | 17916: DUP2 | 17917: MSTORE | 17918: PUSH1 0x01 | 17920: PUSH1 0x01 | 17922: PUSH1 0xa0 | 17924: SHL | 17925: SUB | 17926: SWAP1 | 17927: SWAP4 | 17928: AND | 17929: SWAP3 | 17930: SWAP1 | 17931: DUP2 | 17932: SWAP1 | 17933: PUSH1 0x20 | 17935: DUP3 | 17936: ADD | 17937: SWAP1 | 17938: JUMP
17939: JUMPDEST | 17940: SUB | 17941: SWAP1 | 17942: LOG3 | 17943: CODESIZE | 17944: DUP1 | 17945: PUSH2 0x3a81 | 17948: JUMP
17949: JUMPDEST | 17950: PUSH2 0x3b1c | 17953: SWAP1 | 17954: PUSH2 0x29af | 17957: JUMP
17958: JUMPDEST | 17959: PUSH32 0x0000000000000000000000000000000000000000000000000000000000000000 | 17992: GT | 17993: PUSH2 0x3b6a | 17996: JUMPI
17997: PUSH2 0x3b4e | 18000: PUSH2 0x2f40 | 18003: DUP4 | 18004: PUSH2 0x27b4 | 18007: JUMP
18008: JUMPDEST | 18009: PUSH2 0x3b58 | 18012: JUMPI
18013: CODESIZE | 18014: PUSH2 0x3a6f | 18017: JUMP
18018: JUMPDEST | 18019: PUSH1 0x40 | 18021: MLOAD | 18022: PUSH4 0x0a62fbdb | 18027: PUSH1 0xe1 | 18029: SHL | 18030: DUP2 | 18031: MSTORE | 18032: PUSH1 0x04 | 18034: SWAP1 | 18035: REVERT
18036: JUMPDEST | 18037: PUSH1 0x40 | 18039: MLOAD | 18040: PUSH4 0x7139da23 | 18045: PUSH1 0xe1 | 18047: SHL | 18048: DUP2 | 18049: MSTORE | 18050: PUSH1 0x04 | 18052: SWAP1 | 18053: REVERT
18054: JUMPDEST | 18055: SWAP2 | 18056: SWAP1 | 18057: DUP3 | 18058: PUSH1 0x0c | 18060: SIGNEXTEND | 18061: DUP2 | 18062: PUSH1 0x0c | 18064: SIGNEXTEND | 18065: DUP2 | 18066: DUP2 | 18067: SGT | 18068: PUSH2 0x33cb | 18071: JUMPI
18072: PUSH1 0x00 | 18074: SGT | 18075: PUSH2 0x3b9f | 18078: JUMPI
18079: POP | 18080: PUSH2 0x3380 | 18083: SWAP2 | 18084: SWAP3 | 18085: PUSH2 0x331a | 18088: JUMP
18089: JUMPDEST | 18090: PUSH1 0x00 | 18092: SLT | 18093: PUSH2 0x3bb0 | 18096: JUMPI
18097: PUSH2 0x33a0 | 18100: SWAP2 | 18101: SWAP3 | 18102: PUSH2 0x331a | 18105: JUMP
18106: JUMPDEST | 18107: PUSH2 0x3bb9 | 18110: SWAP1 | 18111: PUSH2 0x2989 | 18114: JUMP
18115: JUMPDEST | 18116: PUSH1 0x01 | 18118: PUSH1 0x01 | 18120: PUSH1 0x68 | 18122: SHL | 18123: SUB | 18124: SWAP3 | 18125: DUP4 | 18126: AND | 18127: SWAP3 | 18128: AND | 18129: SWAP1 | 18130: JUMP
18131: JUMPDEST | 18132: PUSH1 0x01 | 18134: PUSH1 0x01 | 18136: PUSH1 0x80 | 18138: SHL | 18139: SUB | 18140: SWAP2 | 18141: DUP3 | 18142: AND | 18143: SWAP2 | 18144: AND | 18145: DUP2 | 18146: DUP2 | 18147: LT | 18148: PUSH2 0x1e5f | 18151: JUMPI
18152: SUB | 18153: SWAP1 | 18154: JUMP
18155: JUMPDEST | 18156: PUSH1 0x01 | 18158: PUSH1 0x01 | 18160: PUSH1 0xa0 | 18162: SHL | 18163: SUB | 18164: DUP1 | 18165: DUP3 | 18166: AND | 18167: PUSH1 0x00 | 18169: DUP2 | 18170: DUP2 | 18171: MSTORE | 18172: PUSH1 0x06 | 18174: PUSH1 0x20 | 18176: MSTORE | 18177: PUSH1 0x40 | 18179: SWAP1 | 18180: KECCAK256 | 18181: PUSH1 0x01 | 18183: PUSH1 0x01 | 18185: PUSH1 0x80 | 18187: SHL | 18188: SUB | 18189: SWAP6 | 18190: SWAP2 | 18191: SWAP5 | 18192: SWAP2 | 18193: SWAP4 | 18194: SWAP2 | 18195: SWAP1 | 18196: DUP7 | 18197: SWAP1 | 18198: PUSH2 0x3c16 | 18201: SWAP1 | 18202: DUP7 | 18203: SWAP1 | 18204: PUSH2 0x097c | 18207: JUMP
18208: JUMPDEST | 18209: SLOAD | 18210: AND | 18211: DUP4 | 18212: DUP3 | 18213: AND | 18214: SWAP7 | 18215: DUP8 | 18216: PUSH1 0x00 | 18218: MSTORE | 18219: PUSH1 0x06 | 18221: PUSH1 0x20 | 18223: MSTORE | 18224: DUP6 | 18225: PUSH1 0x40 | 18227: PUSH1 0x00 | 18229: KECCAK256 | 18230: SWAP1 | 18231: PUSH2 0x3c35 | 18234: SWAP2 | 18235: PUSH2 0x097c | 18238: JUMP
18239: JUMPDEST | 18240: SLOAD | 18241: AND | 18242: PUSH2 0x3c41 | 18245: DUP10 | 18246: DUP4 | 18247: PUSH2 0x3bc9 | 18250: JUMP
18251: JUMPDEST | 18252: PUSH2 0x3c4b | 18255: DUP11 | 18256: DUP4 | 18257: PUSH2 0x3579 | 18260: JUMP
18261: JUMPDEST | 18262: SWAP3 | 18263: DUP2 | 18264: DUP9 | 18265: PUSH2 0x3c59 | 18268: DUP9 | 18269: PUSH1 0x06 | 18271: PUSH2 0x097c | 18274: JUMP
18275: JUMPDEST | 18276: SWAP1 | 18277: PUSH2 0x3c63 | 18280: SWAP2 | 18281: PUSH2 0x097c | 18284: JUMP
18285: JUMPDEST | 18286: SWAP1 | 18287: PUSH2 0x3c6d | 18290: SWAP2 | 18291: PUSH2 0x3596 | 18294: JUMP
18295: JUMPDEST | 18296: DUP4 | 18297: DUP9 | 18298: PUSH2 0x3c7a | 18301: DUP8 | 18302: PUSH1 0x06 | 18304: PUSH2 0x097c | 18307: JUMP
18308: JUMPDEST | 18309: SWAP1 | 18310: PUSH2 0x3c84 | 18313: SWAP2 | 18314: PUSH2 0x097c | 18317: JUMP
18318: JUMPDEST | 18319: SWAP1 | 18320: PUSH2 0x3c8e | 18323: SWAP2 | 18324: PUSH2 0x3596 | 18327: JUMP
18328: JUMPDEST | 18329: PUSH2 0x3c97 | 18332: DUP9 | 18333: PUSH2 0x1d3a | 18336: JUMP
18337: JUMPDEST | 18338: SWAP2 | 18339: PUSH2 0x3ca3 | 18342: SWAP2 | 18343: DUP4 | 18344: DUP9 | 18345: PUSH2 0x3734 | 18348: JUMP
18349: JUMPDEST | 18350: PUSH2 0x3cac | 18353: SWAP4 | 18354: PUSH2 0x3734 | 18357: JUMP
18358: JUMPDEST | 18359: PUSH2 0x3cb5 | 18362: SWAP1 | 18363: PUSH2 0x27b4 | 18366: JUMP
18367: JUMPDEST | 18368: ISZERO | 18369: PUSH2 0x3b58 | 18372: JUMPI
18373: PUSH32 0x29db89d45e1a802b4d55e202984fce9faf1d30aedf86503ff1ea0ed9ebb64201 | 18406: SWAP2 | 18407: PUSH2 0x371d | 18410: PUSH1 0x40 | 18412: MLOAD | 18413: SWAP3 | 18414: DUP4 | 18415: SWAP3 | 18416: AND | 18417: SWAP7 | 18418: DUP3 | 18419: PUSH2 0x35e9 | 18422: JUMP
18423: JUMPDEST | 18424: SWAP4 | 18425: SWAP3 | 18426: SWAP1 | 18427: SWAP4 | 18428: PUSH1 0x04 | 18430: PUSH1 0x01 | 18432: SLOAD | 18433: PUSH1 0xf8 | 18435: SHR | 18436: AND | 18437: PUSH2 0x1a47 | 18440: JUMPI
18441: PUSH2 0x2f40 | 18444: PUSH2 0x3d0b | 18447: SWAP2 | 18448: DUP7 | 18449: PUSH2 0x1b09 | 18452: JUMP
18453: JUMPDEST | 18454: PUSH2 0x0e62 | 18457: JUMPI
18458: PUSH1 0x01 | 18460: PUSH1 0x01 | 18462: PUSH1 0xa0 | 18464: SHL | 18465: SUB | 18466: DUP2 | 18467: DUP2 | 18468: AND | 18469: PUSH32 0x0000000000000000000000000000000000000000000000000000000000000000 | 18502: SWAP1 | 18503: SWAP2 | 18504: AND | 18505: SUB | 18506: PUSH2 0x3d62 | 18509: JUMPI
18510: POP | 18511: PUSH2 0x0c31 | 18514: SWAP3 | 18515: PUSH1 0x00 | 18517: NOT | 18518: DUP4 | 18519: SUB | 18520: PUSH2 0x3d76 | 18523: JUMPI
18524: SWAP2 | 18525: POP | 18526: PUSH2 0x3d5c | 18529: DUP3 | 18530: PUSH2 0x474c | 18533: JUMP
18534: JUMPDEST | 18535: SWAP2 | 18536: PUSH2 0x3d76 | 18539: JUMP
18540: JUMPDEST | 18541: SWAP1 | 18542: PUSH2 0x3d70 | 18545: PUSH2 0x0c31 | 18548: SWAP5 | 18549: SWAP4 | 18550: PUSH2 0x2faf | 18553: JUMP
18554: JUMPDEST | 18555: SWAP3 | 18556: PUSH2 0x3f99 | 18559: JUMP
18560: JUMPDEST | 18561: SWAP1 | 18562: SWAP2 | 18563: PUSH2 0x312f | 18566: SWAP3 | 18567: PUSH2 0x3d84 | 18570: PUSH2 0x1ece | 18573: JUMP
18574: JUMPDEST | 18575: PUSH2 0x3d92 | 18578: PUSH2 0x30ca | 18581: DUP5 | 18582: PUSH1 0x05 | 18584: PUSH2 0x097c | 18587: JUMP
18588: JUMPDEST | 18589: PUSH2 0x3dec | 18592: PUSH2 0x3da0 | 18595: DUP3 | 18596: MLOAD | 18597: PUSH1 0x0c | 18599: SIGNEXTEND | 18600: SWAP1 | 18601: JUMP
18602: JUMPDEST | 18603: PUSH2 0x3db5 | 18606: PUSH2 0x3dac | 18609: DUP3 | 18610: PUSH2 0x29c0 | 18613: JUMP
18614: JUMPDEST | 18615: PUSH2 0x2740 | 18618: DUP8 | 18619: PUSH2 0x2791 | 18622: JUMP
18623: JUMPDEST | 18624: SWAP3 | 18625: PUSH2 0x3136 | 18628: PUSH2 0x3dcc | 18631: PUSH2 0x3dc5 | 18634: DUP7 | 18635: PUSH2 0x31c6 | 18638: JUMP
18639: JUMPDEST | 18640: DUP1 | 18641: SWAP5 | 18642: PUSH2 0x3b7c | 18645: JUMP
18646: JUMPDEST | 18647: PUSH2 0x3de1 | 18650: PUSH2 0x3118 | 18653: DUP4 | 18654: PUSH2 0x312a | 18657: PUSH1 0x01 | 18659: SWAP15 | 18660: SWAP6 | 18661: SWAP15 | 18662: SLOAD | 18663: PUSH2 0x1e6b | 18666: JUMP
18667: JUMPDEST | 18668: PUSH2 0x3113 | 18671: PUSH1 0x01 | 18673: SLOAD | 18674: PUSH2 0x1ebf | 18677: JUMP
18678: JUMPDEST | 18679: PUSH1 0x00 | 18681: DUP2 | 18682: SLT | 18683: PUSH2 0x3e91 | 18686: JUMPI
18687: JUMPDEST | 18688: POP | 18689: PUSH2 0x3e21 | 18692: DUP3 | 18693: DUP3 | 18694: PUSH32 0x0000000000000000000000000000000000000000000000000000000000000000 | 18727: PUSH2 0x3ef1 | 18730: JUMP
18731: JUMPDEST | 18732: PUSH1 0x40 | 18734: MLOAD | 18735: SWAP2 | 18736: DUP3 | 18737: MSTORE | 18738: PUSH1 0x01 | 18740: PUSH1 0x01 | 18742: PUSH1 0xa0 | 18744: SHL | 18745: SUB | 18746: SWAP3 | 18747: DUP4 | 18748: AND | 18749: SWAP3 | 18750: AND | 18751: SWAP1 | 18752: DUP3 | 18753: SWAP1 | 18754: PUSH32 0x9b1bfa7fa9ee420a16e124f794c35ac9f90472acc99140eb2f6447c714cad8eb | 18787: SWAP1 | 18788: PUSH1 0x20 | 18790: SWAP1 | 18791: LOG3 | 18792: PUSH1 0x01 | 18794: PUSH1 0x01 | 18796: PUSH1 0x68 | 18798: SHL | 18799: SUB | 18800: DUP3 | 18801: AND | 18802: PUSH2 0x3e6f | 18805: JUMPI
18806: POP | 18807: POP | 18808: JUMP
18809: JUMPDEST | 18810: PUSH1 0x00 | 18812: DUP1 | 18813: MLOAD | 18814: PUSH1 0x20 | 18816: PUSH2 0x4832 | 18819: DUP4 | 18820: CODECOPY | 18821: DUP2 | 18822: MLOAD | 18823: SWAP2 | 18824: MSTORE | 18825: PUSH2 0x31c1 | 18828: PUSH2 0x31b1 | 18831: PUSH1 0x00 | 18833: SWAP5 | 18834: PUSH2 0x31ac | 18837: DUP7 | 18838: SLOAD | 18839: PUSH2 0x0b8f | 18842: JUMP
18843: JUMPDEST | 18844: PUSH2 0x3e9a | 18847: SWAP1 | 18848: PUSH2 0x29af | 18851: JUMP
18852: JUMPDEST | 18853: PUSH32 0x0000000000000000000000000000000000000000000000000000000000000000 | 18886: GT | 18887: PUSH2 0x3b6a | 18890: JUMPI
18891: PUSH2 0x3ecc | 18894: PUSH2 0x2f40 | 18897: DUP5 | 18898: PUSH2 0x27b4 | 18901: JUMP
18902: JUMPDEST | 18903: PUSH2 0x3b58 | 18906: JUMPI
18907: CODESIZE | 18908: PUSH2 0x3df5 | 18911: JUMP
18912: JUMPDEST | 18913: PUSH1 0x01 | 18915: PUSH1 0x01 | 18917: PUSH1 0xa0 | 18919: SHL | 18920: SUB | 18921: SWAP1 | 18922: SWAP2 | 18923: AND | 18924: DUP2 | 18925: MSTORE | 18926: PUSH1 0x20 | 18928: DUP2 | 18929: ADD | 18930: SWAP2 | 18931: SWAP1 | 18932: SWAP2 | 18933: MSTORE | 18934: PUSH1 0x40 | 18936: ADD | 18937: SWAP1 | 18938: JUMP
18939: JUMPDEST | 18940: PUSH1 0x01 | 18942: PUSH1 0x01 | 18944: PUSH1 0xa0 | 18946: SHL | 18947: SUB | 18948: AND | 18949: SWAP3 | 18950: SWAP2 | 18951: DUP4 | 18952: EXTCODESIZE | 18953: ISZERO | 18954: PUSH2 0x0582 | 18957: JUMPI
18958: PUSH2 0x3f2b | 18961: SWAP1 | 18962: PUSH1 0x40 | 18964: MLOAD | 18965: DUP1 | 18966: SWAP6 | 18967: DUP2 | 18968: DUP1 | 18969: SWAP6 | 18970: PUSH4 0xa9059cbb | 18975: PUSH1 0xe0 | 18977: SHL | 18978: DUP3 | 18979: MSTORE | 18980: PUSH1 0x00 | 18982: SWAP9 | 18983: DUP10 | 18984: SWAP7 | 18985: DUP8 | 18986: SWAP7 | 18987: DUP8 | 18988: SWAP4 | 18989: PUSH1 0x04 | 18991: DUP5 | 18992: ADD | 18993: PUSH2 0x3ed6 | 18996: JUMP
18997: JUMPDEST | 18998: SUB | 18999: SWAP3 | 19000: GAS | 19001: CALL | 19002: DUP1 | 19003: ISZERO | 19004: PUSH2 0x3f8c | 19007: JUMPI
19008: JUMPDEST | 19009: PUSH2 0x3f7c | 19012: JUMPI
19013: JUMPDEST | 19014: POP | 19015: RETURNDATASIZE | 19016: SWAP1 | 19017: POP | 19018: DUP1 | 19019: ISZERO | 19020: PUSH2 0x3f71 | 19023: JUMPI
19024: PUSH1 0x20 | 19026: EQ | 19027: PUSH2 0x3f50 | 19030: JUMPI
19031: POP | 19032: DUP1 | 19033: REVERT
19034: JUMPDEST | 19035: SWAP1 | 19036: PUSH1 0x20 | 19038: DUP2 | 19039: DUP1 | 19040: RETURNDATACOPY | 19041: MLOAD
19042: JUMPDEST | 19043: ISZERO | 19044: PUSH2 0x3f5f | 19047: JUMPI
19048: JUMP
19049: JUMPDEST | 19050: PUSH1 0x40 | 19052: MLOAD | 19053: PUSH4 0xcefaffeb | 19058: PUSH1 0xe0 | 19060: SHL | 19061: DUP2 | 19062: MSTORE | 19063: PUSH1 0x04 | 19065: SWAP1 | 19066: REVERT
19067: JUMPDEST | 19068: POP | 19069: SWAP1 | 19070: POP | 19071: PUSH1 0x00 | 19073: NOT | 19074: PUSH2 0x3f58 | 19077: JUMP
19078: JUMPDEST | 19079: PUSH2 0x3f85 | 19082: SWAP2 | 19083: PUSH2 0x1b46 | 19086: JUMP
19087: JUMPDEST | 19088: CODESIZE | 19089: DUP3 | 19090: PUSH2 0x3f3b | 19093: JUMP
19094: JUMPDEST | 19095: PUSH2 0x3f94 | 19098: PUSH2 0x1bfe | 19101: JUMP
19102: JUMPDEST | 19103: PUSH2 0x3f36 | 19106: JUMP
19107: JUMPDEST | 19108: PUSH1 0x01 | 19110: PUSH1 0x01 | 19112: PUSH1 0xa0 | 19114: SHL | 19115: SUB | 19116: DUP1 | 19117: DUP3 | 19118: AND | 19119: PUSH1 0x00 | 19121: DUP2 | 19122: DUP2 | 19123: MSTORE | 19124: PUSH1 0x06 | 19126: PUSH1 0x20 | 19128: MSTORE | 19129: PUSH1 0x40 | 19131: DUP2 | 19132: KECCAK256 | 19133: SWAP1 | 19134: SWAP7 | 19135: SWAP6 | 19136: SWAP2 | 19137: SWAP5 | 19138: SWAP2 | 19139: SWAP4 | 19140: PUSH1 0x01 | 19142: PUSH1 0x01 | 19144: PUSH1 0x80 | 19146: SHL | 19147: SUB | 19148: SWAP2 | 19149: DUP3 | 19150: SWAP1 | 19151: PUSH2 0x3fcf | 19154: SWAP1 | 19155: DUP8 | 19156: SWAP1 | 19157: PUSH2 0x097c | 19160: JUMP
19161: JUMPDEST | 19162: SLOAD | 19163: AND | 19164: PUSH2 0x3fdb | 19167: DUP9 | 19168: DUP3 | 19169: PUSH2 0x3bc9 | 19172: JUMP
19173: JUMPDEST | 19174: DUP1 | 19175: DUP8 | 19176: DUP8 | 19177: DUP2 | 19178: AND | 19179: SWAP12 | 19180: DUP13 | 19181: DUP2 | 19182: MSTORE | 19183: PUSH1 0x02 | 19185: PUSH1 0x20 | 19187: MSTORE | 19188: PUSH1 0x40 | 19190: DUP2 | 19191: KECCAK256 | 19192: DUP13 | 19193: DUP9 | 19194: DUP3 | 19195: SLOAD | 19196: AND | 19197: SWAP1 | 19198: PUSH2 0x3ffc | 19201: SWAP2 | 19202: PUSH2 0x3bc9 | 19205: JUMP
19206: JUMPDEST | 19207: PUSH2 0x4005 | 19210: SWAP2 | 19211: PUSH2 0x3596 | 19214: JUMP
19215: JUMPDEST | 19216: DUP11 | 19217: DUP2 | 19218: MSTORE | 19219: PUSH1 0x06 | 19221: PUSH1 0x20 | 19223: MSTORE | 19224: PUSH1 0x40 | 19226: SWAP1 | 19227: KECCAK256 | 19228: SWAP1 | 19229: PUSH2 0x401b | 19232: SWAP2 | 19233: PUSH2 0x097c | 19236: JUMP
19237: JUMPDEST | 19238: SWAP1 | 19239: PUSH2 0x4025 | 19242: SWAP2 | 19243: PUSH2 0x3596 | 19246: JUMP
19247: JUMPDEST | 19248: PUSH2 0x402e | 19251: DUP8 | 19252: PUSH2 0x1d3a | 19255: JUMP
19256: JUMPDEST | 19257: SWAP2 | 19258: PUSH2 0x4039 | 19261: SWAP3 | 19262: DUP5 | 19263: PUSH2 0x3734 | 19266: JUMP
19267: JUMPDEST | 19268: PUSH2 0x4042 | 19271: SWAP1 | 19272: PUSH2 0x27b4 | 19275: JUMP
19276: JUMPDEST | 19277: ISZERO | 19278: PUSH2 0x3b58 | 19281: JUMPI
19282: PUSH32 0xd6d480d5b3068db003533b170d67561494d72e3bf9fa40a266471351ebba9e16 | 19315: SWAP4 | 19316: DUP3 | 19317: PUSH2 0x4076 | 19320: SWAP3 | 19321: DUP9 | 19322: AND | 19323: SWAP2 | 19324: PUSH2 0x3ef1 | 19327: JUMP
19328: JUMPDEST | 19329: PUSH2 0x371d | 19332: PUSH1 0x40 | 19334: MLOAD | 19335: SWAP3 | 19336: DUP4 | 19337: SWAP3 | 19338: AND | 19339: SWAP6 | 19340: DUP3 | 19341: PUSH2 0x35e9 | 19344: JUMP
19345: JUMPDEST | 19346: SWAP2 | 19347: SWAP1 | 19348: DUP2 | 19349: LT | 19350: ISZERO | 19351: PUSH2 0x4097 | 19354: JUMPI
19355: PUSH1 0x05 | 19357: SHL | 19358: ADD | 19359: SWAP1 | 19360: JUMP
19361: JUMPDEST | 19362: PUSH4 0x4e487b71 | 19367: PUSH1 0xe0 | 19369: SHL | 19370: PUSH1 0x00 | 19372: MSTORE | 19373: PUSH1 0x32 | 19375: PUSH1 0x04 | 19377: MSTORE | 19378: PUSH1 0x24 | 19380: PUSH1 0x00 | 19382: REVERT
19383: JUMPDEST | 19384: CALLDATALOAD | 19385: PUSH2 0x0979 | 19388: DUP2 | 19389: PUSH2 0x0571 | 19392: JUMP
19393: JUMPDEST | 19394: SWAP1 | 19395: PUSH1 0x40 | 19397: MLOAD | 19398: PUSH2 0x40c6 | 19401: PUSH1 0x80 | 19403: DUP3 | 19404: PUSH2 0x1b46 | 19407: JUMP
19408: JUMPDEST | 19409: SWAP2 | 19410: SLOAD | 19411: PUSH4 0xffffffff | 19416: DUP2 | 19417: AND | 19418: DUP4 | 19419: MSTORE | 19420: PUSH1 0x20 | 19422: DUP2 | 19423: DUP2 | 19424: SHR | 19425: PUSH1 0x01 | 19427: PUSH1 0x01 | 19429: PUSH1 0x40 | 19431: SHL | 19432: SUB | 19433: AND | 19434: SWAP1 | 19435: DUP5 | 19436: ADD | 19437: MSTORE | 19438: PUSH1 0x60 | 19440: DUP2 | 19441: DUP2 | 19442: SHR | 19443: PUSH1 0x01 | 19445: PUSH1 0x01 | 19447: PUSH1 0x80 | 19449: SHL | 19450: SUB | 19451: AND | 19452: PUSH1 0x40 | 19454: DUP6 | 19455: ADD | 19456: MSTORE | 19457: PUSH1 0xe0 | 19459: SWAP2 | 19460: SWAP1 | 19461: SWAP2 | 19462: SHR | 19463: SWAP1 | 19464: DUP4 | 19465: ADD | 19466: MSTORE | 19467: JUMP
19468: JUMPDEST | 19469: PUSH1 0x01 | 19471: SWAP1 | 19472: PUSH4 0xffffffff | 19477: DUP1 | 19478: SWAP2 | 19479: AND | 19480: SWAP1 | 19481: DUP2 | 19482: EQ | 19483: PUSH2 0x1eb3 | 19486: JUMPI
19487: ADD | 19488: SWAP1 | 19489: JUMP
19490: JUMPDEST | 19491: SWAP3 | 19492: SWAP2 | 19493: SWAP1 | 19494: SWAP3 | 19495: PUSH1 0x01 | 19497: PUSH1 0x08 | 19499: DUP2 | 19500: SLOAD | 19501: PUSH1 0xf8 | 19503: SHR | 19504: AND | 19505: PUSH2 0x1a47 | 19508: JUMPI
19509: GAS | 19510: SWAP5 | 19511: PUSH2 0x4134 | 19514: PUSH2 0x1ece | 19517: JUMP
19518: JUMPDEST | 19519: PUSH1 0x00
19521: JUMPDEST | 19522: DUP5 | 19523: DUP2 | 19524: LT | 19525: PUSH2 0x422e | 19528: JUMPI
19529: POP | 19530: POP | 19531: POP | 19532: PUSH2 0x41d9 | 19535: SWAP1 | 19536: PUSH2 0x41d2 | 19539: PUSH2 0x41b3 | 19542: PUSH2 0x3616 | 19545: PUSH2 0x415d | 19548: PUSH2 0x0c31 | 19551: SWAP8 | 19552: SWAP9 | 19553: GAS | 19554: SWAP1 | 19555: PUSH2 0x219b | 19558: JUMP
19559: JUMPDEST | 19560: PUSH2 0x41ac | 19563: PUSH2 0x419a | 19566: PUSH2 0x4176 | 19569: PUSH2 0x4171 | 19572: DUP9 | 19573: PUSH1 0x07 | 19575: PUSH2 0x097c | 19578: JUMP
19579: JUMPDEST | 19580: PUSH2 0x40b7 | 19583: JUMP
19584: JUMPDEST | 19585: SWAP9 | 19586: PUSH2 0x2025 | 19589: PUSH2 0x4190 | 19592: PUSH2 0x418b | 19595: DUP13 | 19596: MLOAD | 19597: PUSH4 0xffffffff | 19602: AND | 19603: SWAP1 | 19604: JUMP
19605: JUMPDEST | 19606: PUSH2 0x4102 | 19609: JUMP
19610: JUMPDEST | 19611: PUSH4 0xffffffff | 19616: AND | 19617: DUP12 | 19618: MSTORE | 19619: JUMP
19620: JUMPDEST | 19621: PUSH2 0x2e8e | 19624: PUSH1 0x20 | 19626: DUP11 | 19627: ADD | 19628: SWAP2 | 19629: PUSH2 0x2034 | 19632: DUP4 | 19633: MLOAD | 19634: PUSH2 0x0b8f | 19637: JUMP
19638: JUMPDEST | 19639: BASEFEE | 19640: SWAP1 | 19641: PUSH2 0x1e77 | 19644: JUMP
19645: JUMPDEST | 19646: PUSH2 0x41c5 | 19649: PUSH1 0x40 | 19651: DUP7 | 19652: ADD | 19653: SWAP2 | 19654: PUSH2 0x364b | 19657: DUP4 | 19658: MLOAD | 19659: PUSH2 0x0993 | 19662: JUMP
19663: JUMPDEST | 19664: PUSH1 0x01 | 19666: PUSH1 0x01 | 19668: PUSH1 0x80 | 19670: SHL | 19671: SUB | 19672: AND | 19673: SWAP1 | 19674: MSTORE | 19675: JUMP
19676: JUMPDEST | 19677: PUSH1 0x07 | 19679: PUSH2 0x097c | 19682: JUMP
19683: JUMPDEST | 19684: DUP2 | 19685: MLOAD | 19686: PUSH1 0x20 | 19688: DUP1 | 19689: DUP5 | 19690: ADD | 19691: MLOAD | 19692: PUSH1 0x40 | 19694: DUP6 | 19695: ADD | 19696: MLOAD | 19697: PUSH1 0x60 | 19699: SWAP6 | 19700: DUP7 | 19701: ADD | 19702: MLOAD | 19703: PUSH1 0x01 | 19705: PUSH1 0x01 | 19707: PUSH1 0xe0 | 19709: SHL | 19710: SUB | 19711: NOT | 19712: PUSH1 0xe0 | 19714: SWAP2 | 19715: SWAP1 | 19716: SWAP2 | 19717: SHL | 19718: AND | 19719: PUSH1 0x01 | 19721: PUSH1 0x60 | 19723: SHL | 19724: PUSH1 0x01 | 19726: PUSH1 0xe0 | 19728: SHL | 19729: SUB | 19730: SWAP2 | 19731: SWAP1 | 19732: SWAP7 | 19733: SHL | 19734: AND | 19735: PUSH4 0xffffffff | 19740: SWAP1 | 19741: SWAP4 | 19742: AND | 19743: PUSH1 0x01 | 19745: PUSH1 0x20 | 19747: SHL | 19748: PUSH1 0x01 | 19750: PUSH1 0x60 | 19752: SHL | 19753: SUB | 19754: SWAP2 | 19755: SWAP1 | 19756: SWAP3 | 19757: SHL | 19758: AND | 19759: OR | 19760: OR | 19761: SWAP2 | 19762: SWAP1 | 19763: SWAP2 | 19764: OR | 19765: SWAP1 | 19766: SSTORE | 19767: JUMP
19768: JUMPDEST | 19769: DUP1 | 19770: PUSH2 0x424c | 19773: PUSH2 0x4246 | 19776: PUSH2 0x4241 | 19779: DUP7 | 19780: SWAP5 | 19781: DUP10 | 19782: DUP8 | 19783: PUSH2 0x4087 | 19786: JUMP
19787: JUMPDEST | 19788: PUSH2 0x40ad | 19791: JUMP
19792: JUMPDEST | 19793: DUP7 | 19794: PUSH2 0x4252 | 19797: JUMP
19798: JUMPDEST | 19799: ADD | 19800: PUSH2 0x4137 | 19803: JUMP
19804: JUMPDEST | 19805: SWAP1 | 19806: PUSH2 0x425f | 19809: PUSH2 0x2f40 | 19812: DUP3 | 19813: PUSH2 0x2a35 | 19816: JUMP
19817: JUMPDEST | 19818: PUSH2 0x45e7 | 19821: JUMPI
19822: PUSH2 0x4271 | 19825: PUSH2 0x30ca | 19828: DUP3 | 19829: PUSH1 0x05 | 19831: PUSH2 0x097c | 19834: JUMP
19835: JUMPDEST | 19836: SWAP1 | 19837: PUSH2 0x427d | 19840: DUP3 | 19841: MLOAD | 19842: PUSH1 0x0c | 19844: SIGNEXTEND | 19845: SWAP1 | 19846: JUMP
19847: JUMPDEST | 19848: SWAP1 | 19849: PUSH2 0x4287 | 19852: DUP3 | 19853: PUSH2 0x29c0 | 19856: JUMP
19857: JUMPDEST | 19858: SWAP2 | 19859: PUSH2 0x4297 | 19862: PUSH1 0x60 | 19864: DUP6 | 19865: ADD | 19866: MLOAD | 19867: PUSH2 0xffff | 19870: AND | 19871: SWAP1 | 19872: JUMP
19873: JUMPDEST | 19874: SWAP1 | 19875: PUSH2 0x42a6 | 19878: PUSH1 0x80 | 19880: DUP7 | 19881: ADD | 19882: MLOAD | 19883: PUSH1 0xff | 19885: AND | 19886: SWAP1 | 19887: JUMP
19888: JUMPDEST | 19889: SWAP4 | 19890: PUSH2 0x42d0 | 19893: PUSH32 0x0000000000000000000000000000000000000000000000000000000000000000 | 19926: PUSH2 0x249f | 19929: JUMP
19930: JUMPDEST | 19931: SWAP3 | 19932: PUSH1 0x00 | 19934: SWAP6 | 19935: DUP7
19936: JUMPDEST | 19937: PUSH1 0xff | 19939: PUSH32 0x0000000000000000000000000000000000000000000000000000000000000000 | 19972: AND | 19973: PUSH1 0xff | 19975: DUP3 | 19976: AND | 19977: LT | 19978: PUSH2 0x448f | 19981: JUMPI
19982: POP | 19983: POP | 19984: POP | 19985: PUSH2 0x434e | 19988: PUSH2 0x4348 | 19991: PUSH2 0x2966 | 19994: DUP6 | 19995: PUSH2 0x4343 | 19998: PUSH1 0x01 | 20000: DUP1 | 20001: PUSH1 0x40 | 20003: SHL | 20004: SUB | 20005: PUSH32 0x0000000000000000000000000000000000000000000000000000000000000000 | 20038: AND | 20039: DUP1 | 20040: SWAP11 | 20041: PUSH2 0x1e77 | 20044: JUMP
20045: JUMPDEST | 20046: PUSH2 0x23d6 | 20049: JUMP
20050: JUMPDEST | 20051: DUP3 | 20052: PUSH2 0x2628 | 20055: JUMP
20056: JUMPDEST | 20057: SWAP2 | 20058: PUSH1 0x00 | 20060: DUP4 | 20061: SLT | 20062: PUSH2 0x4486 | 20065: JUMPI
20066: JUMPDEST | 20067: PUSH2 0x4361 | 20070: DUP4 | 20071: PUSH2 0x31c6 | 20074: JUMP
20075: JUMPDEST | 20076: SWAP7 | 20077: DUP8 | 20078: PUSH2 0x436d | 20081: SWAP2 | 20082: DUP8 | 20083: PUSH2 0x2db5 | 20086: JUMP
20087: JUMPDEST | 20088: PUSH2 0x4378 | 20091: DUP6 | 20092: PUSH1 0x05 | 20094: PUSH2 0x097c | 20097: JUMP
20098: JUMPDEST | 20099: PUSH1 0x00 | 20101: PUSH2 0x4383 | 20104: SWAP2 | 20105: PUSH2 0x2d1b | 20108: JUMP
20109: JUMPDEST | 20110: DUP7 | 20111: PUSH2 0x438f | 20114: DUP7 | 20115: PUSH1 0x05 | 20117: PUSH2 0x097c | 20120: JUMP
20121: JUMPDEST | 20122: PUSH1 0x00 | 20124: PUSH2 0x439a | 20127: SWAP2 | 20128: PUSH2 0x2b4b | 20131: JUMP
20132: JUMPDEST | 20133: PUSH2 0x43a3 | 20136: SWAP2 | 20137: PUSH2 0x335c | 20140: JUMP
20141: JUMPDEST | 20142: PUSH1 0x01 | 20144: SLOAD | 20145: PUSH2 0x43af | 20148: SWAP1 | 20149: PUSH2 0x1e6b | 20152: JUMP
20153: JUMPDEST | 20154: SWAP1 | 20155: PUSH2 0x43b9 | 20158: SWAP2 | 20159: PUSH2 0x3005 | 20162: JUMP
20163: JUMPDEST | 20164: PUSH2 0x43c4 | 20167: SWAP1 | 20168: PUSH1 0x01 | 20170: PUSH2 0x3022 | 20173: JUMP
20174: JUMPDEST | 20175: PUSH1 0x01 | 20177: SLOAD | 20178: PUSH2 0x43d0 | 20181: SWAP1 | 20182: PUSH2 0x1ebf | 20185: JUMP
20186: JUMPDEST | 20187: SWAP1 | 20188: PUSH2 0x43da | 20191: SWAP2 | 20192: PUSH2 0x3041 | 20195: JUMP
20196: JUMPDEST | 20197: PUSH2 0x43e5 | 20200: SWAP1 | 20201: PUSH1 0x01 | 20203: PUSH2 0x3059 | 20206: JUMP
20207: JUMPDEST | 20208: PUSH2 0x43ee | 20211: SWAP2 | 20212: PUSH2 0x25f1 | 20215: JUMP
20216: JUMPDEST | 20217: PUSH2 0x43f7 | 20220: SWAP1 | 20221: PUSH2 0x4622 | 20224: JUMP
20225: JUMPDEST | 20226: SWAP3 | 20227: PUSH2 0x4402 | 20230: SWAP2 | 20231: DUP5 | 20232: PUSH2 0x2bba | 20235: JUMP
20236: JUMPDEST | 20237: PUSH1 0x40 | 20239: DUP1 | 20240: MLOAD | 20241: SWAP4 | 20242: DUP5 | 20243: MSTORE | 20244: PUSH1 0x20 | 20246: DUP5 | 20247: ADD | 20248: SWAP2 | 20249: SWAP1 | 20250: SWAP2 | 20251: MSTORE | 20252: PUSH1 0x01 | 20254: PUSH1 0x01 | 20256: PUSH1 0xa0 | 20258: SHL | 20259: SUB | 20260: SWAP2 | 20261: DUP3 | 20262: AND | 20263: SWAP5 | 20264: DUP6 | 20265: SWAP4 | 20266: SWAP3 | 20267: AND | 20268: SWAP2 | 20269: PUSH32 0x1547a878dc89ad3c367b6338b4be6a65a5dd74fb77ae044da1e8747ef1f4f62f | 20302: SWAP2 | 20303: SWAP1 | 20304: LOG3 | 20305: DUP1 | 20306: PUSH1 0x0c | 20308: SIGNEXTEND | 20309: PUSH1 0x00 | 20311: SLT | 20312: PUSH2 0x4455 | 20315: JUMPI
20316: POP | 20317: POP | 20318: JUMP
20319: JUMPDEST | 20320: PUSH1 0x00 | 20322: DUP1 | 20323: MLOAD | 20324: PUSH1 0x20 | 20326: PUSH2 0x4832 | 20329: DUP4 | 20330: CODECOPY | 20331: DUP2 | 20332: MLOAD | 20333: SWAP2 | 20334: MSTORE | 20335: PUSH2 0x31c1 | 20338: PUSH2 0x31b1 | 20341: PUSH1 0x00 | 20343: SWAP4 | 20344: PUSH2 0x4480 | 20347: PUSH2 0x447a | 20350: DUP7 | 20351: SLOAD | 20352: PUSH2 0x0b8f | 20355: JUMP
20356: JUMPDEST | 20357: SWAP2 | 20358: PUSH2 0x45f9 | 20361: JUMP
20362: JUMPDEST | 20363: SWAP1 | 20364: PUSH2 0x2466 | 20367: JUMP
20368: JUMPDEST | 20369: PUSH1 0x00 | 20371: SWAP3 | 20372: POP | 20373: PUSH2 0x4358 | 20376: JUMP
20377: JUMPDEST | 20378: PUSH2 0x449a | 20381: DUP3 | 20382: DUP3 | 20383: DUP6 | 20384: PUSH2 0x2cc0 | 20387: JUMP
20388: JUMPDEST | 20389: PUSH2 0x44aa | 20392: JUMPI
20393: JUMPDEST | 20394: PUSH1 0x01 | 20396: ADD | 20397: PUSH1 0xff | 20399: AND | 20400: PUSH2 0x42d6 | 20403: JUMP
20404: JUMPDEST | 20405: DUP7 | 20406: DUP11 | 20407: PUSH2 0x44b5 | 20410: DUP4 | 20411: PUSH2 0x1c0b | 20414: JUMP
20415: JUMPDEST | 20416: PUSH1 0x20 | 20418: DUP2 | 20419: ADD | 20420: MLOAD | 20421: DUP4 | 20422: SWAP1 | 20423: PUSH1 0x01 | 20425: PUSH1 0x01 | 20427: PUSH1 0xa0 | 20429: SHL | 20430: SUB | 20431: AND | 20432: SWAP12 | 20433: DUP13 | 20434: PUSH1 0x06 | 20436: DUP2 | 20437: PUSH2 0x44d4 | 20440: DUP6 | 20441: DUP4 | 20442: PUSH2 0x097c | 20445: JUMP
20446: JUMPDEST | 20447: SWAP1 | 20448: PUSH2 0x44de | 20451: SWAP2 | 20452: PUSH2 0x097c | 20455: JUMP
20456: JUMPDEST | 20457: SLOAD | 20458: PUSH1 0x01 | 20460: PUSH1 0x01 | 20462: PUSH1 0x80 | 20464: SHL | 20465: SUB | 20466: AND | 20467: SWAP4 | 20468: PUSH2 0x44f2 | 20471: SWAP2 | 20472: PUSH2 0x097c | 20475: JUMP
20476: JUMPDEST | 20477: SWAP1 | 20478: PUSH2 0x44fc | 20481: SWAP2 | 20482: PUSH2 0x097c | 20485: JUMP
20486: JUMPDEST | 20487: PUSH1 0x00 | 20489: PUSH2 0x4507 | 20492: SWAP2 | 20493: PUSH2 0x3596 | 20496: JUMP
20497: JUMPDEST | 20498: PUSH2 0x4512 | 20501: DUP14 | 20502: PUSH1 0x02 | 20504: PUSH2 0x097c | 20507: JUMP
20508: JUMPDEST | 20509: DUP3 | 20510: DUP2 | 20511: SLOAD | 20512: PUSH2 0x451e | 20515: SWAP1 | 20516: PUSH2 0x0993 | 20519: JUMP
20520: JUMPDEST | 20521: SWAP1 | 20522: PUSH2 0x4528 | 20525: SWAP2 | 20526: PUSH2 0x3bc9 | 20529: JUMP
20530: JUMPDEST | 20531: PUSH2 0x4531 | 20534: SWAP2 | 20535: PUSH2 0x3596 | 20538: JUMP
20539: JUMPDEST | 20540: PUSH1 0x40 | 20542: DUP4 | 20543: ADD | 20544: MLOAD | 20545: PUSH1 0x01 | 20547: PUSH1 0x01 | 20549: PUSH1 0xa0 | 20551: SHL | 20552: SUB | 20553: AND | 20554: PUSH2 0x4548 | 20557: SWAP1 | 20558: PUSH2 0x249f | 20561: JUMP
20562: JUMPDEST | 20563: PUSH1 0x60 | 20565: DUP5 | 20566: ADD | 20567: MLOAD | 20568: PUSH2 0x4556 | 20571: SWAP1 | 20572: PUSH2 0x0b8f | 20575: JUMP
20576: JUMPDEST | 20577: PUSH2 0x4569 | 20580: SWAP2 | 20581: PUSH1 0x01 | 20583: PUSH1 0x01 | 20585: PUSH1 0x80 | 20587: SHL | 20588: SUB | 20589: DUP6 | 20590: AND | 20591: PUSH2 0x2bba | 20594: JUMP
20595: JUMPDEST | 20596: SWAP3 | 20597: PUSH1 0xc0 | 20599: ADD | 20600: MLOAD | 20601: PUSH2 0x4577 | 20604: SWAP1 | 20605: PUSH2 0x0b8f | 20608: JUMP
20609: JUMPDEST | 20610: PUSH2 0x4580 | 20613: SWAP1 | 20614: PUSH2 0x0b8f | 20617: JUMP
20618: JUMPDEST | 20619: PUSH2 0x458a | 20622: SWAP1 | 20623: DUP5 | 20624: PUSH2 0x2b7c | 20627: JUMP
20628: JUMPDEST | 20629: PUSH2 0x4593 | 20632: SWAP2 | 20633: PUSH2 0x218f | 20636: JUMP
20637: JUMPDEST | 20638: PUSH1 0x40 | 20640: DUP1 | 20641: MLOAD | 20642: PUSH1 0x01 | 20644: PUSH1 0x01 | 20646: PUSH1 0x80 | 20648: SHL | 20649: SUB | 20650: SWAP4 | 20651: SWAP1 | 20652: SWAP4 | 20653: AND | 20654: DUP4 | 20655: MSTORE | 20656: PUSH1 0x20 | 20658: DUP4 | 20659: ADD | 20660: SWAP4 | 20661: SWAP1 | 20662: SWAP4 | 20663: MSTORE | 20664: SWAP12 | 20665: PUSH1 0x01 | 20667: PUSH1 0x01 | 20669: PUSH1 0xa0 | 20671: SHL | 20672: SUB | 20673: SWAP1 | 20674: DUP2 | 20675: AND | 20676: SWAP5 | 20677: DUP2 | 20678: AND | 20679: SWAP4 | 20680: AND | 20681: SWAP2 | 20682: PUSH32 0x9850ab1af75177e4a9201c65a2cf7976d5d28e40ef63494b44366f86b2f9412e | 20715: SWAP2 | 20716: LOG4 | 20717: PUSH2 0x449f | 20720: JUMP
20721: JUMPDEST | 20722: PUSH1 0x40 | 20724: MLOAD | 20725: PUSH4 0x6ef5bcdd | 20730: PUSH1 0xe1 | 20732: SHL | 20733: DUP2 | 20734: MSTORE | 20735: PUSH1 0x04 | 20737: SWAP1 | 20738: REVERT
20739: JUMPDEST | 20740: PUSH1 0x00 | 20742: DUP2 | 20743: PUSH1 0x0c | 20745: SIGNEXTEND | 20746: SLT | 20747: PUSH2 0x4610 | 20750: JUMPI
20751: PUSH1 0x01 | 20753: PUSH1 0x01 | 20755: PUSH1 0x68 | 20757: SHL | 20758: SUB | 20759: AND | 20760: SWAP1 | 20761: JUMP
20762: JUMPDEST | 20763: PUSH1 0x40 | 20765: MLOAD | 20766: PUSH4 0x363b64b7 | 20771: PUSH1 0xe1 | 20773: SHL | 20774: DUP2 | 20775: MSTORE | 20776: PUSH1 0x04 | 20778: SWAP1 | 20779: REVERT
20780: JUMPDEST | 20781: PUSH1 0x00 | 20783: DUP2 | 20784: SLT | 20785: PUSH2 0x4610 | 20788: JUMPI
20789: SWAP1 | 20790: JUMP
20791: JUMPDEST | 20792: SWAP1 | 20793: PUSH2 0x46f5 | 20796: PUSH2 0x463d | 20799: PUSH2 0x0979 | 20802: SWAP4 | 20803: PUSH2 0x1d3a | 20806: JUMP
20807: JUMPDEST | 20808: PUSH2 0x46c0 | 20811: PUSH1 0x60 | 20813: PUSH2 0x46eb | 20816: PUSH2 0x465a | 20819: PUSH1 0x01 | 20821: DUP1 | 20822: PUSH1 0xa0 | 20824: SHL | 20825: SUB | 20826: PUSH1 0x40 | 20828: DUP7 | 20829: ADD | 20830: MLOAD | 20831: AND | 20832: PUSH2 0x249f | 20835: JUMP
20836: JUMPDEST | 20837: PUSH1 0xc0 | 20839: DUP6 | 20840: ADD | 20841: MLOAD | 20842: PUSH1 0x01 | 20844: PUSH1 0x01 | 20846: PUSH1 0x40 | 20848: SHL | 20849: SUB | 20850: SWAP5 | 20851: PUSH8 0x0de0b6b3a7640000 | 20860: SWAP3 | 20861: SWAP1 | 20862: SWAP2 | 20863: DUP4 | 20864: SWAP1 | 20865: PUSH2 0x46af | 20868: SWAP1 | 20869: DUP9 | 20870: SWAP1 | 20871: DUP2 | 20872: AND | 20873: DUP1 | 20874: DUP5 | 20875: LT | 20876: PUSH2 0x473f | 20879: JUMPI
20880: JUMPDEST | 20881: DUP4 | 20882: SUB | 20883: AND | 20884: PUSH32 0x0000000000000000000000000000000000000000000000000000000000000000 | 20917: PUSH2 0x1e77 | 20920: JUMP
20921: JUMPDEST | 20922: DIV | 20923: DUP1 | 20924: DUP5 | 20925: LT | 20926: PUSH2 0x4732 | 20929: JUMPI
20930: JUMPDEST | 20931: DUP4 | 20932: SUB | 20933: SWAP1 | 20934: PUSH2 0x1e77 | 20937: JUMP
20938: JUMPDEST | 20939: DIV | 20940: SWAP6 | 20941: PUSH2 0x2f19 | 20944: PUSH32 0x0000000000000000000000000000000000000000000000000000000000000000 | 20977: PUSH2 0x249f | 20980: JUMP
20981: JUMPDEST | 20982: SWAP3 | 20983: ADD | 20984: MLOAD | 20985: AND | 20986: SWAP1 | 20987: PUSH2 0x1e77 | 20990: JUMP
20991: JUMPDEST | 20992: SWAP1 | 20993: DUP1 | 20994: ISZERO | 20995: PUSH2 0x4725 | 20998: JUMPI
20999: JUMPDEST | 21000: PUSH32 0x0000000000000000000000000000000000000000000000000000000000000000 | 21033: SWAP2 | 21034: DIV | 21035: PUSH2 0x23d6 | 21038: JUMP
21039: JUMPDEST | 21040: PUSH2 0x472d | 21043: PUSH2 0x23bf | 21046: JUMP
21047: JUMPDEST | 21048: PUSH2 0x46fd | 21051: JUMP
21052: JUMPDEST | 21053: PUSH2 0x473a | 21056: PUSH2 0x1e32 | 21059: JUMP
21060: JUMPDEST | 21061: PUSH2 0x46b8 | 21064: JUMP
21065: JUMPDEST | 21066: PUSH2 0x4747 | 21069: PUSH2 0x1e32 | 21072: JUMP
21073: JUMPDEST | 21074: PUSH2 0x4686 | 21077: JUMP
21078: JUMPDEST | 21079: PUSH2 0x476f | 21082: PUSH2 0x4757 | 21085: PUSH2 0x1dbe | 21088: JUMP
21089: JUMPDEST | 21090: PUSH2 0x06ab | 21093: PUSH5 0xffffffffff | 21099: SWAP2 | 21100: DUP3 | 21101: PUSH1 0x01 | 21103: SLOAD | 21104: PUSH1 0xd0 | 21106: SHR | 21107: AND | 21108: SWAP1 | 21109: PUSH2 0x1e49 | 21112: JUMP
21113: JUMPDEST | 21114: POP | 21115: PUSH1 0x01 | 21117: PUSH1 0x01 | 21119: PUSH1 0xa0 | 21121: SHL | 21122: SUB | 21123: SWAP1 | 21124: SWAP2 | 21125: AND | 21126: PUSH1 0x00 | 21128: SWAP1 | 21129: DUP2 | 21130: MSTORE | 21131: PUSH1 0x05 | 21133: PUSH1 0x20 | 21135: MSTORE | 21136: PUSH1 0x40 | 21138: DUP2 | 21139: KECCAK256 | 21140: SLOAD | 21141: PUSH1 0x0c | 21143: SIGNEXTEND | 21144: SWAP2 | 21145: SWAP1 | 21146: DUP1 | 21147: DUP4 | 21148: SGT | 21149: ISZERO | 21150: PUSH2 0x47a4 | 21153: JUMPI
21154: POP | 21155: PUSH2 0x4480 | 21158: PUSH2 0x0979 | 21161: SWAP3 | 21162: PUSH2 0x45f9 | 21165: JUMP
21166: JUMPDEST | 21167: SWAP2 | 21168: POP | 21169: POP | 21170: SWAP1 | 21171: JUMP
21172: JUMPDEST | 21173: PUSH2 0x47b5 | 21176: PUSH2 0x4757 | 21179: PUSH2 0x1dbe | 21182: JUMP
21183: JUMPDEST | 21184: PUSH1 0x01 | 21186: PUSH1 0x01 | 21188: PUSH1 0xa0 | 21190: SHL | 21191: SUB | 21192: SWAP1 | 21193: SWAP3 | 21194: AND | 21195: PUSH1 0x00 | 21197: SWAP1 | 21198: DUP2 | 21199: MSTORE | 21200: PUSH1 0x05 | 21202: PUSH1 0x20 | 21204: MSTORE | 21205: PUSH1 0x40 | 21207: DUP2 | 21208: KECCAK256 | 21209: SLOAD | 21210: PUSH1 0x0c | 21212: SIGNEXTEND | 21213: SWAP3 | 21214: SWAP2 | 21215: POP | 21216: DUP1 | 21217: DUP4 | 21218: SLT | 21219: ISZERO | 21220: PUSH2 0x47a4 | 21223: JUMPI
21224: POP | 21225: PUSH2 0x4480 | 21228: PUSH2 0x47ed | 21231: PUSH2 0x0979 | 21234: SWAP4 | 21235: PUSH2 0x2989 | 21238: JUMP
21239: JUMPDEST | 21240: PUSH2 0x45f9 | 21243: JUMP
21244: JUMPDEST | 21245: POP | 21246: PUSH1 0x00 | 21248: CALLDATASIZE | 21249: DUP2 | 21250: DUP1 | 21251: CALLDATACOPY | 21252: DUP1 | 21253: DUP1 | 21254: CALLDATASIZE | 21255: DUP2 | 21256: PUSH32 0x0000000000000000000000000000000000000000000000000000000000000000 | 21289: GAS | 21290: UNSUPPORTED_F4 | 21291: RETURNDATASIZE | 21292: DUP3 | 21293: DUP1 | 21294: RETURNDATACOPY | 21295: ISZERO | 21296: PUSH2 0x482d | 21299: JUMPI
21300: RETURNDATASIZE | 21301: SWAP1 | 21302: RETURN
21303: JUMPDEST | 21304: RETURNDATASIZE | 21305: SWAP1 | 21306: REVERT
21307: INVALID
21308: UNSUPPORTED_DD | 21309: UNSUPPORTED_F2 | 21310: MSTORE | 21311: UNSUPPORTED_AD | 21312: SHL | 21313: UNSUPPORTED_E2 | 21314: UNSUPPORTED_C8 | 21315: SWAP12 | 21316: PUSH10 0xc2b068fc378daa952ba7 | 21327: CALL | 21328: PUSH4 0xc4a11628 | 21333: UNSUPPORTED_F5 | 21334: GAS | 21335: UNSUPPORTED_4D | 21336: UNSUPPORTED_F5 | 21337: UNSUPPORTED_23 | 21338: UNSUPPORTED_B3 | 21339: UNSUPPORTED_EF | 21340: UNSUPPORTED_C9 | 21341: DUP13 | 21342: PUSH24 0x30ba19013824f711a9ab74801459b27e6ff7685cb924587c | 21367: DUP10 | 21368: UNSUPPORTED_AE | 21369: UNSUPPORTED_DA | 21370: MSTORE8 | 21371: UNSUPPORTED_AC
```

