import Ethereum.Semantics
import Reasoning.JumpDest

/-!
# ModExp replacement bytecode

This is the runtime of `evmification/src/modexp/ModexpDeployed.sol` at commit
`c0aabf32aa4682925836044948a204da8cd62e9f`.

It was reproduced with the repository's CI settings:

```text
solc 0.8.30+commit.73712a01
--via-ir --optimize --optimize-runs 10000 --evm-version osaka
```

The upstream CI artifact is `ModexpDeployed`, artifact id `8772013577`, from workflow run
`30574140694`. Its recorded artifact digest is
`sha256:6b7f10af7b2743271faf17fa8534e175018d38d410962ad2a77de4c5c5d0aa6e`.
-/

open Ethereum Ethereum.EVM

namespace Modexp

set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def runtimeHex : Blob :=
  "6080604052346101b4575f35602035906040359161040083116104008211176104008311176101b4576020821115806101a9575b8061019e575b6101" ++
  "2e5781606001906060818401018461005382856102b6565b1561010c57505f846100ff575b600281106100b5575b506100ad946100a8916100a26100" ++
  "7e87610245565b9461008881610245565b9661009c61009586610245565b9988610344565b8761039c565b8561039c565b61049f565b602081519101" ++
  "f35b5f600186116100ed575b6100695785925060016100d98460405194813687376102fa565b9114166100e257f35b60015f198383010153f35b5061" ++
  "00fa605f8601610271565b6100bf565b50605f8401355f1a610060565b61011b818381366080376102fa565b610123576080f35b6001607f82015360" ++
  "80f35b6060358260200360031b1c6060838101358360200360031b1c9285602003940101358360031b1c915f9260018111610168575b5050505f52f3" ++
  "5b600193509091819006825b156101615760018316610190575b808291099160011c9182610173565b928184819209939050610181565b5060208311" ++
  "15610039565b506020811115610033565b5f80fd5b7f4e487b71000000000000000000000000000000000000000000000000000000005f5260416004" ++
  "5260245ffd5b90601f19601f604051930116820182811067ffffffffffffffff82111761020b57604052565b6101b8565b67ffffffffffffffff8111" ++
  "61020b57601f01601f191660200190565b61023660206101e5565b5f815290815f90369060200137565b9061025761025283610210565b6101e5565b" ++
  "828152601f196102678294610210565b0190602036910137565b905f9160605b818110610282575050565b8035818303602081106102a9575b506102" ++
  "9e575b602001610277565b506001925080610296565b60200360031b1c5f610290565b905f92915b8181106102c6575050565b803581830360208110" ++
  "6102ed575b506102e2575b6020016102bb565b5060019250806102da565b60200360031b1c5f6102d4565b905f92916001821161032d575b81151584" ++
  "1516610315575050565b600191015f1901355f1a11610327575b565b60019150565b925061033e5f1982850101846102b6565b92610307565b5f9160" ++
  "603611610372575b80831161036a575b5081610361575050565b60206060910137565b91505f610357565b367fffffffffffffffffffffffffffffff" ++
  "ffffffffffffffffffffffffffffffffa001925061034f565b5f928236116103c7575b8084116103bf575b50826103b957505050565b60200137565b" ++
  "92505f6103ae565b9250813603926103a6565b7f4e487b71000000000000000000000000000000000000000000000000000000005f52601160045260" ++
  "245ffd5b905f19820191821161040d57565b6103d2565b6101000390610100821161040d57565b907fffffffffffffffffffffffffffffffffffffff" ++
  "fffffffffffffffffffffffffe820191821161040d57565b9190820391821161040d57565b7f4e487b71000000000000000000000000000000000000" ++
  "000000000000000000005f52603260045260245ffd5b90815181101561049a570160200190565b61045c565b91908151156105035781515f19810190" ++
  "811161040d5760017fff000000000000000000000000000000000000000000000000000000000000006104e3829386610489565b511660f81c160361" ++
  "04fa576104f792610785565b90565b6104f79261060d565b50505061051060206101e5565b5f80825236602083013790565b90601f82018092116104" ++
  "0d57565b906001820180921161040d57565b906002820180921161040d57565b906040820180921161040d57565b906020820180921161040d57565b" ++
  "906010820180921161040d57565b906008820180921161040d57565b906004820180921161040d57565b9190820180921161040d57565b67ffffffff" ++
  "ffffffff811161020b5760051b60200190565b6040906105be826101e5565b6001815291601f1901366020840137565b906105dc6102528361059a56" ++
  "5b828152601f19610267829461059a565b80511561049a5760200190565b805182101561049a5760209160051b010190565b92919091815180156107" ++
  "325761062281610245565b9261062c8161093b565b8015610723575b61071a57818101601f0194602082015b80515f1a158782101615610659576001" ++
  "01610643565b82939495965091909103601f198101806106e557505061068161067b8461051d565b60051c90565b91600183146106d657916106d191" ++
  "86976106ab836106a4816103259a9b98610b14565b8093610b8d565b916106b68483610bdb565b926106c0856105cf565b60016106cb826105ec565b" ++
  "52610c52565b610de7565b91508492506104f79395610a0e565b6106f8906107109493929598969861044f565b94858561070482610245565b940160" ++
  "2085015e61060d565b6020019083015e90565b50509250905090565b5061072d81610991565b610633565b50925050506104f761022c565b90816001" ++
  "1b917f7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff81160361040d57565b908160051b9180830460201490151715" ++
  "61040d57565b929190815191821561092e5761079a83610245565b946107a48261093b565b801561091f575b610919576107bb61067b8561051d565b" ++
  "916001831461090857916103259493916107d6828995610b14565b908282816107e761067b855161051d565b116108f957506107f691610b14565b82" ++
  "82610803828285610e6c565b156108e7575050925b61081581610ec9565b90600182036108275750505050610de7565b600382036108685750506108" ++
  "4b82848161085a818661084b8286816108619d611398565b6108548361073f565b90611442565b9050611398565b9050610de7565b91909361087d61" ++
  "0877836105ec565b51610f60565b926108888386610f89565b620100016108ae8787878561089c846105cf565b9860016108a88b6105ec565b52610f" ++
  "d4565b97036108ca5750506108c58484846106d19861132f565b610fd4565b84846108c5936106d1996108e28a858582988b610fd4565b6111d6565b" ++
  "816108f193611442565b90509261080c565b61090292610b8d565b9261080c565b91506104f793509185949592610a0e565b50505050565b50610929" ++
  "82610991565b6107ab565b50505090506104f761022c565b908151602083019201602081016001935b81811061095857505050565b80518184036020" ++
  "80820110610980575b50610976575b60200161094c565b505f93508061096e565b602003601f190160031b1c5f610968565b9081518015610a085760" ++
  "208301920191601f83019060019384915b8381106109c65750506109bc5750565b515f1a6001149150565b80919250515f1982840301602080820110" ++
  "6109f7575b506109ed575b6020019084916109ac565b505f9350816109e2565b602003601f190160031b1c5f6109dc565b505f9150565b9290926020" ++
  "83015192519384602003938460031b1c905f9280516020820191601f821680610af6575b50016020018360015f19829006085b818310610adf575050" ++
  "5060019281846020808295019280510101935b610abc575b505b828110610a7e5750505050906020915f52015e565b80515f1a846008805b610a9657" ++
  "505050600101610a69565b5f190196800995600182821c16610ab0575b808691610a87565b85848298099650610aa8565b929080515f1a1582821016" ++
  "15610ad85783019280939193610a62565b9092610a67565b909194846020918184895192090895019190610a46565b95509190602085819351888303" ++
  "60031b1c0696840101929091610a37565b9190610b1f906105cf565b918051908160051c5f5b818110610b5a575050601f82169081610b4157505050" ++
  "565b60209182601f1992015190830360031b1c921684010152565b806020610b79610b73610b6e60019561052b565b61076f565b8761044f565b8501" ++
  "015160208260051b8901015201610b29565b91908251928315610bcf57601f840180941161040d57610bc29360051c90838210610bc7575b81610bbd" ++
  "91610b14565b611442565b905090565b839150610bb3565b50506104f791506105cf565b908060011b917f7fffffffffffffffffffffffffffffffff" ++
  "ffffffffffffffffffffffffffffff8216820361040d576001830180841161040d57610c34936001610c2e610c27846105cf565b92836105f9565b52" ++
  "611442565b5090565b5f19811461040d5760010190565b801561040d575f190190565b9394908251925f5b84811080610db1575b15610c7657610c71" ++
  "90610c38565b610c5a565b96848814610da65760405191610cbe610cb8610c928b84610489565b517fff000000000000000000000000000000000000" ++
  "000000000000000000000000001690565b60f81c90565b9860075b80151580610d96575b15610cde57610cd990610c46565b610cc2565b9293949596" ++
  "979899505b878110610cfb5750505050505050505090565b899284868b8a610d1a610d14610cb8610c92898b610489565b9561052b565b9760079880" ++
  "5b610d335750505050505050600101610ce8565b8282610d4e825f19610d539501998a99604052888480611935565b611c19565b8b8b8b600160ff8a" ++
  "16881c811614610d78575b5050505050508b8a8e89948b94610d20565b610d8b95610d4e93869360405285611935565b8b8a8e8b8b8b610d66565b50" ++
  "60ff8b16811c60011615610ccb565b505050505050905090565b507fff00000000000000000000000000000000000000000000000000000000000000" ++
  "610de0610c928385610489565b1615610c63565b9190918160051c5f5b818110610e3c575050601f82169182610e095750505050565b602091601f19" ++
  "83921601015191810360031b9201918251915f196001831b018093169219911b161790525f808080610919565b80610e54610e4e610b6e6001946105" ++
  "2b565b8661044f565b6020610e6083876105f9565b51918801015201610df0565b9091805b610e7b575050505f90565b5f1901610e8881836105f956" ++
  "5b51610e9382856105f9565b5111610ec157610ea381836105f9565b51610eae82856105f9565b5110610eba5780610e70565b5050505f90565b5050" ++
  "50600190565b8051908115610f5a575f5b82811080610f24575b15610ef057610eeb90610c38565b610ed4565b9182610efb9161044f565b91821580" ++
  "15610f1a575b610eba576020910101519060200360031b1c90565b5060208311610f05565b507fff0000000000000000000000000000000000000000" ++
  "000000000000000000000080610f518385610489565b51161615610edd565b50505f90565b6001905f905b60088210610f755750505f0390565b9091" ++
  "80600191830260020302920190610f66565b8060011b917f7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff82168203" ++
  "61040d576001830180841161040d57610bc2936001610c2e610c27846105cf565b90949391926020610fe4846105cf565b9601602085019260208801" ++
  "9460051b95869260405192848401956040870180604052855b8181106111c857505060208087840101920160208801916020870194601f198a01925b" ++
  "8581106110d857505050505050508351159384159461108a575b5050845e61105257505050565b91840160200191905f905b83811061106a57505050" ++
  "50565b60208181925185518082039580870396109110179381520192019161105d565b60019450908301602001905b8281111561104557601f199192" ++
  "9350810191019080518251908181116110d0575b106110c6575b90869291611096565b505f9250816110bd565b8492506110b7565b80919293949596" ++
  "97989950515f90838b915b8d8310611193575050508a51908101808c5210855101855288515f19848202918d51808402928391850991810110918082" ++
  "10910303019060408a019089915b8d831061115857505050906020918b51908101808752108651018b525f865201908c989796959493929161102b56" ++
  "5b909192602080918351905f198287029287099082885181018092810180601f198c015210911001918082109103030194019101919091611129565b" ++
  "909192602080918451905f1982860292860990828851810180928101808b5210911001918082109103030194019201906110ea565b5f81528b975060" ++
  "2001611008565b9394908251925f5b848110806112f9575b156111fa576111f590610c38565b6111de565b96848814610da657604051916007986112" ++
  "2261121c610cb8610c928486610489565b60ff1690565b995b801515806112ec575b156112405761123b90610c46565b611224565b92939495969798" ++
  "99505b87811061125d5750505050505050505090565b899284868b8a611279610d1461121c610cb8610c928a8c610489565b97886007995b61129257" ++
  "5050505050505060010161124a565b8282610d4e825f196112ac9501998a996040528884611c28565b8b8b8b6001808a891c16146112ce575b505050" ++
  "5050508b8a8e89948b9461127f565b6112e195610d4e93869360405285610fd4565b8b8a8e8b8b8b6112bc565b5060018b821c161561122d565b507f" ++
  "ff00000000000000000000000000000000000000000000000000000000000000611328610c928385610489565b16156111e7565b939290919361133d" ++
  "826105cf565b948161134b84888095611c19565b6040515f5b6010811061136d575091610325958592610d4e9460405285610fd4565b816001929394" ++
  "9697955060405261138b878a610d4e828a8a84611c28565b0190879395949291611350565b93926113ac6113a7828461058d565b6105cf565b945f5b" ++
  "8381106113bd575050505050565b60208160051b83010151806113d6575b506001016113af565b5f905f905b8582106113fd57505083820160051b88" ++
  "016020018051909101905260016113cd565b90915f19600191602085870160051b8d010160208660051b8c0101518086029384918709928251820192" ++
  "839182018091521091100191808210910303019201906113db565b9093919361144f846105cf565b905b8015158061191b575b1561146d5761146890" ++
  "610c46565b611451565b938415611909575b60018111806118ef575b156114925761148d90610c46565b611475565b93909192936001811461188957" ++
  "80821061184d576114b86114b3828461044f565b61052b565b946114c2866105cf565b936114cf6113a78561052b565b9560208560051b9101602088" ++
  "015e6114f86114f26114ec856103ff565b8a6105f9565b51611f71565b91611502846105cf565b94831515998a5f14611839575f90815b8783106117" ++
  "ff575050505f905f5b8181106117c5575061153290896105f9565b525b611546611540856103ff565b866105f9565b5197925b83801561170d575f19" ++
  "8991019461156a611564888861058d565b836105f9565b51908b8761158361154061157e8c8461058d565b6103ff565b51938281106116f45750905f" ++
  "19938a8c61159d848461058d565b928310155b806116e9575b6116a7575b50505050509091505f5f8b5f5b8b8b821061165a5750505060205f198a85" ++
  "010160051b8d0101918251918183038181038552109110176115fa575b50506115f485896105f9565b5261154a565b909161160590610c46565b915f" ++
  "905f905b8c8a83106116225750505081510190525f806115e8565b92602083945f198495600195010160051b01019060208d8660051b010151908251" ++
  "91820192839182018091521091101792019061160b565b9260208060019496958460051b0101515f19818a02918a0995810195818710918082109103" ++
  "0301955f198489010160051b0101938451908082039280840393109110179352018c906115ba565b966116c46116d1836116ca6116dd9a999b6116c4" ++
  "6116d697610422565b906105f9565b519761058d565b610422565b5193612122565b8991868c5f8a8c6115ad565b5060028210156115a8565b918094" ++
  "6117019293611ee1565b9390938a8c60016115a2565b50939598925095935095505f14611797575f5b83811061172d5750505050565b8061173a6001" ++
  "92856105f9565b51831c61174782896105f9565b52846117528261052b565b1061175e575b01611720565b61177061176a8261052b565b856105f956" ++
  "5b5161177a84610412565b1b61178582896105f9565b511761179182896105f9565b52611758565b505f5b8281106117a657505050565b806117b360" ++
  "0192846105f9565b516117be82886105f9565b520161179a565b916001906117d3848c6105f9565b51871b17926117e2818c6105f9565b516117ec88" ++
  "610412565b1c936117f8828d6105f9565b5201611520565b60019061180c84846105f9565b51881b179261181b81846105f9565b5161182589610412" ++
  "565b1c93611831828c6105f9565b520191611512565b905060208560051b9101602087015e611534565b509093506118596105b2565b915f5b828110" ++
  "61186a575050509190565b80611877600192846105f9565b5161188282896105f9565b520161185c565b50919093611896906105ec565b51916118a1" ++
  "816105cf565b925f9192835b6118bd57505090506118b8846105ec565b529190565b916118da5f198395019485926118d384876105f9565b5190611e" ++
  "e1565b94906118e682886105f9565b529392906118a7565b506119026118fc826103ff565b876105f9565b511561147f565b50935050905061191761" ++
  "05b2565b9190565b5061192e611928826103ff565b846105f9565b511561145a565b61194b8580949361198996989761198f94611398565b95611955" ++
  "84610539565b948591611961836105cf565b9061196b8761052b565b60051b60205f19890160051b8c0101602084015e8051938492611398565b9461" ++
  "058d565b926119998361052b565b841115611c11576119b26119ac8461052b565b8561044f565b905b6119bd826105cf565b946119c78561052b565b" ++
  "811115611c0a576119e1906119db8661052b565b9061044f565b828111611c03575b60209060051b916001860160051b0101602086015e611a078361" ++
  "052b565b90611a11826105cf565b94828211611bfb575b5f5b828110611b4e57505050611a2f836105cf565b955f5f5b838110611b23575050505f5b" ++
  "60028110611a595750505060209060051b9101602084015e565b60208460051b8601015115801590611ad9575b8015611ad0575b611a80575b600101" ++
  "611a3f565b5f5f5b838110611a91575050611a78565b8060019160051b926020848a0101938451905f908a8510611ac2575b50808203928084039310" ++
  "911017935201611a83565b60209150890101515f611aad565b60029150611a73565b50600184805b611ae95750611a6c565b5f19018060051b602080" ++
  "828a010151918701015190818111611b1b575b10611b12575b80611adf565b50505f5f611b0c565b5f9250611b06565b8060019160051b9260208085" ++
  "87010151948a0101938451808203928084039310911017935201611a33565b60208160051b8301015180611b67575b50600101611a1c565b5f908286" ++
  "0390888211611bf3575b5f905b828210611bae57505090829160019301868110611b98575b505090611b5e565b60209060051b8a0101908151019052" ++
  "5f80611b90565b90925f1960019160208d87890160051b010160208760051b8d01015180860293849187099282518201928391820180915210911001" ++
  "9180821091030301930190611b78565b889150611b75565b829150611a1a565b50816119e9565b505f6119e1565b6001906119b4565b916020809160" ++
  "051b930191015e565b93929091602092611c38836105cf565b958481019285830194868901948160051b9788809501019060206040519360061b8401" ++
  "0180604052835b818110611ed3575081602085015b848210611e675750505f84905b828210611e4a57505050825b828210611ddb5750505060208385" ++
  "01019383820191925b828410611d45575050508181019283511593841594611cfe575b5050835e611cc757505050565b918401602001915f905b8381" ++
  "10611cde5750505050565b602081819251855180820395808703961091101793815201920191611cd1565b600194505b82811115611cba57601f1991" ++
  "92935081019101908051825190818111611d3d575b10611d33575b90869291611d03565b505f925081611d2a565b849250611d24565b919350918051" ++
  "5f1983820291895180840292839185099181011091808210910303016020830191604086015b888110611da4575050805b611d8e5750506020019187" ++
  "9391611ca0565b6020825191820191821092839281520191611d7c565b91602080918495939551905f19828802928809908286518101809281018089" ++
  "52109110019180821091030301930191019290611d71565b9091929450604082969496515f1981800291800990835191818301908186526020860190" ++
  "81519380821091030383019384921082018091521091100191018181925b611e34575050602090910188949291959395611c89565b60208251918201" ++
  "91821092839281520191611e1d565b8151600181901b90911782528b975060209091019060ff1c611c7d565b9080929394959750979597515f908290" ++
  "60208501905b888210611e9e5750505294968a969095909493929160200190604001611c70565b909192602080918451905f19828602928609908288" ++
  "51810180928101808b521091100191808210910303019401920190611e7d565b5f81528a9650602001611c62565b9290915f935f93811580611f6257" ++
  "5b15611efa57505050565b82808096508093959750600183955f1906088509089283815f038216809204600281600302188082026002030280820260" ++
  "0203028082026002030280820260020302808202600203028091026002030293600183805f03040190828510900302920304170291565b8382049650" ++
  "8382069550611ef0565b905f917001000000000000000000000000000000008110612117575b80780100000000000000000000000000000000000000" ++
  "00000000007f80000000000000000000000000000000000000000000000000000000000000009210612104575b7c0100000000000000000000000000" ++
  "00000000000000000000000000000081106120f1575b7e0100000000000000000000000000000000000000000000000000000000000081106120de57" ++
  "5b7f010000000000000000000000000000000000000000000000000000000000000081106120cb575b7f100000000000000000000000000000000000" ++
  "000000000000000000000000000081106120b8575b7f400000000000000000000000000000000000000000000000000000000000000081106120a557" ++
  "5b1061209b57565b906104f79061052b565b6120b29060021b93610539565b92612094565b6120c59060041b9361057f565b9261206c565b6120d890" ++
  "60081b93610571565b92612044565b6120eb9060101b93610563565b9261201c565b6120fe9060201b93610555565b92611ff5565b6121119060401b" ++
  "93610547565b92611fd0565b60809250821b611f8d565b939192909281850284845f1985890983808210910303925b118183141691111761214e575b" ++
  "5050505090565b5f1981929394950194019281841061217e5783838602915f1985880983808210910303929080959493929161213a565b61214756fe" ++
  "a2646970667358221220cd5419ea3b9d7cd676f3a77ed655fbe370aaa764520b31ad258e1af5e342558c64736f6c634300081e0033"

/-- Exact deployed runtime produced from the pinned source and compiler settings above. -/
def runtimeBytecode : ByteArray :=
  match ByteArray.ofBlob runtimeHex with
  | .ok code => code
  | .error _ => ByteArray.empty

@[simp] theorem runtimeBytecode_size : runtimeBytecode.size = 8633 := by
  native_decide

/-! Decode caches: each list is checked in one native evaluation, rather than recompiling the
large hex parser once per opcode in downstream symbolic traces. -/

theorem entryDecodes :
    [Ethereum.EVM.decode runtimeBytecode ⟨0x00⟩,
      Ethereum.EVM.decode runtimeBytecode ⟨0x02⟩,
      Ethereum.EVM.decode runtimeBytecode ⟨0x04⟩,
      Ethereum.EVM.decode runtimeBytecode ⟨0x05⟩,
      Ethereum.EVM.decode runtimeBytecode ⟨0x06⟩,
      Ethereum.EVM.decode runtimeBytecode ⟨0x09⟩] =
    [some (.Push .PUSH1, some (⟨128⟩, 1)), some (.Push .PUSH1, some (⟨64⟩, 1)),
      some (.MSTORE, .none), some (.CALLVALUE, .none),
      some (.Push .PUSH2, some (⟨0x1b4⟩, 2)), some (.JUMPI, .none)] := by native_decide

theorem lengthDecodes :
    [Ethereum.EVM.decode runtimeBytecode ⟨0x0a⟩,
      Ethereum.EVM.decode runtimeBytecode ⟨0x0b⟩,
      Ethereum.EVM.decode runtimeBytecode ⟨0x0c⟩,
      Ethereum.EVM.decode runtimeBytecode ⟨0x0e⟩,
      Ethereum.EVM.decode runtimeBytecode ⟨0x0f⟩,
      Ethereum.EVM.decode runtimeBytecode ⟨0x10⟩,
      Ethereum.EVM.decode runtimeBytecode ⟨0x12⟩,
      Ethereum.EVM.decode runtimeBytecode ⟨0x13⟩] =
    [some (.PUSH0, .none), some (.CALLDATALOAD, .none),
      some (.Push .PUSH1, some (⟨32⟩, 1)), some (.CALLDATALOAD, .none),
      some (.SWAP1, .none), some (.Push .PUSH1, some (⟨64⟩, 1)),
      some (.CALLDATALOAD, .none), some (.SWAP2, .none)] := by native_decide

theorem boundDecodes :
    [Ethereum.EVM.decode runtimeBytecode ⟨0x14⟩,
      Ethereum.EVM.decode runtimeBytecode ⟨0x17⟩,
      Ethereum.EVM.decode runtimeBytecode ⟨0x18⟩,
      Ethereum.EVM.decode runtimeBytecode ⟨0x19⟩,
      Ethereum.EVM.decode runtimeBytecode ⟨0x1c⟩,
      Ethereum.EVM.decode runtimeBytecode ⟨0x1d⟩,
      Ethereum.EVM.decode runtimeBytecode ⟨0x1e⟩,
      Ethereum.EVM.decode runtimeBytecode ⟨0x1f⟩,
      Ethereum.EVM.decode runtimeBytecode ⟨0x22⟩,
      Ethereum.EVM.decode runtimeBytecode ⟨0x23⟩,
      Ethereum.EVM.decode runtimeBytecode ⟨0x24⟩,
      Ethereum.EVM.decode runtimeBytecode ⟨0x25⟩,
      Ethereum.EVM.decode runtimeBytecode ⟨0x28⟩] =
    [some (.Push .PUSH2, some (⟨1024⟩, 2)), some (.DUP4, .none), some (.GT, .none),
      some (.Push .PUSH2, some (⟨1024⟩, 2)), some (.DUP3, .none), some (.GT, .none),
      some (.OR, .none), some (.Push .PUSH2, some (⟨1024⟩, 2)), some (.DUP4, .none),
      some (.GT, .none), some (.OR, .none),
      some (.Push .PUSH2, some (⟨0x1b4⟩, 2)), some (.JUMPI, .none)] := by native_decide

theorem wordDispatchDecodes :
    [decode runtimeBytecode ⟨0x29⟩, decode runtimeBytecode ⟨0x2b⟩,
      decode runtimeBytecode ⟨0x2c⟩, decode runtimeBytecode ⟨0x2d⟩,
      decode runtimeBytecode ⟨0x2e⟩, decode runtimeBytecode ⟨0x2f⟩,
      decode runtimeBytecode ⟨0x32⟩, decode runtimeBytecode ⟨0x1a9⟩,
      decode runtimeBytecode ⟨0x1aa⟩, decode runtimeBytecode ⟨0x1ab⟩,
      decode runtimeBytecode ⟨0x1ad⟩, decode runtimeBytecode ⟨0x1ae⟩,
      decode runtimeBytecode ⟨0x1af⟩, decode runtimeBytecode ⟨0x1b0⟩,
      decode runtimeBytecode ⟨0x1b3⟩, decode runtimeBytecode ⟨0x33⟩,
      decode runtimeBytecode ⟨0x34⟩, decode runtimeBytecode ⟨0x35⟩,
      decode runtimeBytecode ⟨0x38⟩, decode runtimeBytecode ⟨0x19e⟩,
      decode runtimeBytecode ⟨0x19f⟩, decode runtimeBytecode ⟨0x1a0⟩,
      decode runtimeBytecode ⟨0x1a2⟩, decode runtimeBytecode ⟨0x1a3⟩,
      decode runtimeBytecode ⟨0x1a4⟩, decode runtimeBytecode ⟨0x1a5⟩,
      decode runtimeBytecode ⟨0x1a8⟩, decode runtimeBytecode ⟨0x39⟩,
      decode runtimeBytecode ⟨0x3a⟩, decode runtimeBytecode ⟨0x3d⟩] =
    [some (.Push .PUSH1, some (⟨32⟩, 1)), some (.DUP3, .none), some (.GT, .none),
      some (.ISZERO, .none), some (.DUP1, .none),
      some (.Push .PUSH2, some (⟨0x1a9⟩, 2)), some (.JUMPI, .none),
      some (.JUMPDEST, .none), some (.POP, .none),
      some (.Push .PUSH1, some (⟨32⟩, 1)), some (.DUP2, .none), some (.GT, .none),
      some (.ISZERO, .none), some (.Push .PUSH2, some (⟨0x33⟩, 2)),
      some (.JUMP, .none), some (.JUMPDEST, .none), some (.DUP1, .none),
      some (.Push .PUSH2, some (⟨0x19e⟩, 2)), some (.JUMPI, .none),
      some (.JUMPDEST, .none), some (.POP, .none),
      some (.Push .PUSH1, some (⟨32⟩, 1)), some (.DUP4, .none), some (.GT, .none),
      some (.ISZERO, .none), some (.Push .PUSH2, some (⟨0x39⟩, 2)),
      some (.JUMP, .none), some (.JUMPDEST, .none),
      some (.Push .PUSH2, some (⟨0x12e⟩, 2)), some (.JUMPI, .none)] := by native_decide

theorem wordDispatchFacts :
    decode runtimeBytecode ⟨0x29⟩ = some (.Push .PUSH1, some (⟨32⟩, 1)) ∧
    decode runtimeBytecode ⟨0x2b⟩ = some (.DUP3, .none) ∧
    decode runtimeBytecode ⟨0x2c⟩ = some (.GT, .none) ∧
    decode runtimeBytecode ⟨0x2d⟩ = some (.ISZERO, .none) ∧
    decode runtimeBytecode ⟨0x2e⟩ = some (.DUP1, .none) ∧
    decode runtimeBytecode ⟨0x2f⟩ = some (.Push .PUSH2, some (⟨0x1a9⟩, 2)) ∧
    decode runtimeBytecode ⟨0x32⟩ = some (.JUMPI, .none) ∧
    decode runtimeBytecode ⟨0x1a9⟩ = some (.JUMPDEST, .none) ∧
    decode runtimeBytecode ⟨0x1aa⟩ = some (.POP, .none) ∧
    decode runtimeBytecode ⟨0x1ab⟩ = some (.Push .PUSH1, some (⟨32⟩, 1)) ∧
    decode runtimeBytecode ⟨0x1ad⟩ = some (.DUP2, .none) ∧
    decode runtimeBytecode ⟨0x1ae⟩ = some (.GT, .none) ∧
    decode runtimeBytecode ⟨0x1af⟩ = some (.ISZERO, .none) ∧
    decode runtimeBytecode ⟨0x1b0⟩ = some (.Push .PUSH2, some (⟨0x33⟩, 2)) ∧
    decode runtimeBytecode ⟨0x1b3⟩ = some (.JUMP, .none) ∧
    decode runtimeBytecode ⟨0x33⟩ = some (.JUMPDEST, .none) ∧
    decode runtimeBytecode ⟨0x34⟩ = some (.DUP1, .none) ∧
    decode runtimeBytecode ⟨0x35⟩ = some (.Push .PUSH2, some (⟨0x19e⟩, 2)) ∧
    decode runtimeBytecode ⟨0x38⟩ = some (.JUMPI, .none) ∧
    decode runtimeBytecode ⟨0x19e⟩ = some (.JUMPDEST, .none) ∧
    decode runtimeBytecode ⟨0x19f⟩ = some (.POP, .none) ∧
    decode runtimeBytecode ⟨0x1a0⟩ = some (.Push .PUSH1, some (⟨32⟩, 1)) ∧
    decode runtimeBytecode ⟨0x1a2⟩ = some (.DUP4, .none) ∧
    decode runtimeBytecode ⟨0x1a3⟩ = some (.GT, .none) ∧
    decode runtimeBytecode ⟨0x1a4⟩ = some (.ISZERO, .none) ∧
    decode runtimeBytecode ⟨0x1a5⟩ = some (.Push .PUSH2, some (⟨0x39⟩, 2)) ∧
    decode runtimeBytecode ⟨0x1a8⟩ = some (.JUMP, .none) ∧
    decode runtimeBytecode ⟨0x39⟩ = some (.JUMPDEST, .none) ∧
    decode runtimeBytecode ⟨0x3a⟩ = some (.Push .PUSH2, some (⟨0x12e⟩, 2)) ∧
    decode runtimeBytecode ⟨0x3d⟩ = some (.JUMPI, .none) := by
  simpa only [List.cons.injEq, and_true] using wordDispatchDecodes

theorem wordOperandDecodes :
    [decode runtimeBytecode ⟨0x12e⟩, decode runtimeBytecode ⟨0x12f⟩,
      decode runtimeBytecode ⟨0x131⟩, decode runtimeBytecode ⟨0x132⟩,
      decode runtimeBytecode ⟨0x133⟩, decode runtimeBytecode ⟨0x135⟩,
      decode runtimeBytecode ⟨0x136⟩, decode runtimeBytecode ⟨0x138⟩,
      decode runtimeBytecode ⟨0x139⟩, decode runtimeBytecode ⟨0x13a⟩,
      decode runtimeBytecode ⟨0x13c⟩, decode runtimeBytecode ⟨0x13d⟩,
      decode runtimeBytecode ⟨0x13e⟩, decode runtimeBytecode ⟨0x13f⟩,
      decode runtimeBytecode ⟨0x140⟩, decode runtimeBytecode ⟨0x141⟩,
      decode runtimeBytecode ⟨0x143⟩, decode runtimeBytecode ⟨0x144⟩,
      decode runtimeBytecode ⟨0x146⟩, decode runtimeBytecode ⟨0x147⟩,
      decode runtimeBytecode ⟨0x148⟩, decode runtimeBytecode ⟨0x149⟩,
      decode runtimeBytecode ⟨0x14a⟩, decode runtimeBytecode ⟨0x14c⟩,
      decode runtimeBytecode ⟨0x14d⟩, decode runtimeBytecode ⟨0x14e⟩,
      decode runtimeBytecode ⟨0x14f⟩, decode runtimeBytecode ⟨0x150⟩,
      decode runtimeBytecode ⟨0x151⟩, decode runtimeBytecode ⟨0x152⟩,
      decode runtimeBytecode ⟨0x154⟩, decode runtimeBytecode ⟨0x155⟩,
      decode runtimeBytecode ⟨0x156⟩, decode runtimeBytecode ⟨0x157⟩,
      decode runtimeBytecode ⟨0x158⟩, decode runtimeBytecode ⟨0x159⟩,
      decode runtimeBytecode ⟨0x15b⟩, decode runtimeBytecode ⟨0x15c⟩,
      decode runtimeBytecode ⟨0x15d⟩, decode runtimeBytecode ⟨0x160⟩] =
    [some (.JUMPDEST, .none), some (.Push .PUSH1, some (⟨96⟩, 1)),
      some (.CALLDATALOAD, .none), some (.DUP3, .none),
      some (.Push .PUSH1, some (⟨32⟩, 1)), some (.SUB, .none),
      some (.Push .PUSH1, some (⟨3⟩, 1)), some (.SHL, .none), some (.SHR, .none),
      some (.Push .PUSH1, some (⟨96⟩, 1)), some (.DUP4, .none), some (.DUP2, .none),
      some (.ADD, .none), some (.CALLDATALOAD, .none), some (.DUP4, .none),
      some (.Push .PUSH1, some (⟨32⟩, 1)), some (.SUB, .none),
      some (.Push .PUSH1, some (⟨3⟩, 1)), some (.SHL, .none), some (.SHR, .none),
      some (.SWAP3, .none), some (.DUP6, .none),
      some (.Push .PUSH1, some (⟨32⟩, 1)), some (.SUB, .none), some (.SWAP5, .none),
      some (.ADD, .none), some (.ADD, .none), some (.CALLDATALOAD, .none),
      some (.DUP4, .none), some (.Push .PUSH1, some (⟨3⟩, 1)),
      some (.SHL, .none), some (.SHR, .none), some (.SWAP2, .none), some (.PUSH0, .none),
      some (.SWAP3, .none), some (.Push .PUSH1, some (⟨1⟩, 1)), some (.DUP2, .none),
      some (.GT, .none), some (.Push .PUSH2, some (⟨0x168⟩, 2)),
      some (.JUMPI, .none)] := by native_decide

theorem baseOperandDecodes :
    [decode runtimeBytecode ⟨0x12e⟩, decode runtimeBytecode ⟨0x12f⟩,
      decode runtimeBytecode ⟨0x131⟩, decode runtimeBytecode ⟨0x132⟩,
      decode runtimeBytecode ⟨0x133⟩, decode runtimeBytecode ⟨0x135⟩,
      decode runtimeBytecode ⟨0x136⟩, decode runtimeBytecode ⟨0x138⟩,
      decode runtimeBytecode ⟨0x139⟩] =
    [some (.JUMPDEST, .none), some (.Push .PUSH1, some (⟨96⟩, 1)),
      some (.CALLDATALOAD, .none), some (.DUP3, .none),
      some (.Push .PUSH1, some (⟨32⟩, 1)), some (.SUB, .none),
      some (.Push .PUSH1, some (⟨3⟩, 1)), some (.SHL, .none), some (.SHR, .none)] := by
  native_decide

theorem exponentOperandDecodes :
    [decode runtimeBytecode ⟨0x13a⟩, decode runtimeBytecode ⟨0x13c⟩,
      decode runtimeBytecode ⟨0x13d⟩, decode runtimeBytecode ⟨0x13e⟩,
      decode runtimeBytecode ⟨0x13f⟩, decode runtimeBytecode ⟨0x140⟩,
      decode runtimeBytecode ⟨0x141⟩, decode runtimeBytecode ⟨0x143⟩,
      decode runtimeBytecode ⟨0x144⟩, decode runtimeBytecode ⟨0x146⟩,
      decode runtimeBytecode ⟨0x147⟩] =
    [some (.Push .PUSH1, some (⟨96⟩, 1)), some (.DUP4, .none), some (.DUP2, .none),
      some (.ADD, .none), some (.CALLDATALOAD, .none), some (.DUP4, .none),
      some (.Push .PUSH1, some (⟨32⟩, 1)), some (.SUB, .none),
      some (.Push .PUSH1, some (⟨3⟩, 1)), some (.SHL, .none), some (.SHR, .none)] := by
  native_decide

theorem modulusOperandDecodes :
    [decode runtimeBytecode ⟨0x148⟩, decode runtimeBytecode ⟨0x149⟩,
      decode runtimeBytecode ⟨0x14a⟩, decode runtimeBytecode ⟨0x14c⟩,
      decode runtimeBytecode ⟨0x14d⟩, decode runtimeBytecode ⟨0x14e⟩,
      decode runtimeBytecode ⟨0x14f⟩, decode runtimeBytecode ⟨0x150⟩,
      decode runtimeBytecode ⟨0x151⟩, decode runtimeBytecode ⟨0x152⟩,
      decode runtimeBytecode ⟨0x154⟩, decode runtimeBytecode ⟨0x155⟩,
      decode runtimeBytecode ⟨0x156⟩] =
    [some (.SWAP3, .none), some (.DUP6, .none),
      some (.Push .PUSH1, some (⟨32⟩, 1)), some (.SUB, .none), some (.SWAP5, .none),
      some (.ADD, .none), some (.ADD, .none), some (.CALLDATALOAD, .none),
      some (.DUP4, .none), some (.Push .PUSH1, some (⟨3⟩, 1)),
      some (.SHL, .none), some (.SHR, .none), some (.SWAP2, .none)] := by
  native_decide

/-- Tail of `modulusOperandDecodes`, kept separately so downstream proofs do not have to
normalize the already-consumed prefix again. -/
theorem modulusOperandTailDecodes :
    [decode runtimeBytecode ⟨0x150⟩, decode runtimeBytecode ⟨0x151⟩,
      decode runtimeBytecode ⟨0x152⟩, decode runtimeBytecode ⟨0x154⟩,
      decode runtimeBytecode ⟨0x155⟩, decode runtimeBytecode ⟨0x156⟩] =
    [some (.CALLDATALOAD, .none), some (.DUP4, .none),
      some (.Push .PUSH1, some (⟨3⟩, 1)), some (.SHL, .none),
      some (.SHR, .none), some (.SWAP2, .none)] := by
  native_decide

theorem edgeBranchDecodes :
    [decode runtimeBytecode ⟨0x157⟩, decode runtimeBytecode ⟨0x158⟩,
      decode runtimeBytecode ⟨0x159⟩, decode runtimeBytecode ⟨0x15b⟩,
      decode runtimeBytecode ⟨0x15c⟩, decode runtimeBytecode ⟨0x15d⟩,
      decode runtimeBytecode ⟨0x160⟩] =
    [some (.PUSH0, .none), some (.SWAP3, .none),
      some (.Push .PUSH1, some (⟨1⟩, 1)), some (.DUP2, .none), some (.GT, .none),
      some (.Push .PUSH2, some (⟨0x168⟩, 2)), some (.JUMPI, .none)] := by
  native_decide

theorem smallModulusReturnDecodes :
    [decode runtimeBytecode ⟨0x161⟩, decode runtimeBytecode ⟨0x162⟩,
      decode runtimeBytecode ⟨0x163⟩, decode runtimeBytecode ⟨0x164⟩,
      decode runtimeBytecode ⟨0x165⟩, decode runtimeBytecode ⟨0x166⟩,
      decode runtimeBytecode ⟨0x167⟩] =
    [some (.JUMPDEST, .none), some (.POP, .none), some (.POP, .none),
      some (.POP, .none), some (.PUSH0, .none), some (.MSTORE, .none),
      some (.RETURN, .none)] := by
  native_decide

theorem wordLoopSetupDecodes :
    [decode runtimeBytecode ⟨0x168⟩, decode runtimeBytecode ⟨0x169⟩,
      decode runtimeBytecode ⟨0x16b⟩, decode runtimeBytecode ⟨0x16c⟩,
      decode runtimeBytecode ⟨0x16d⟩, decode runtimeBytecode ⟨0x16e⟩,
      decode runtimeBytecode ⟨0x16f⟩, decode runtimeBytecode ⟨0x170⟩,
      decode runtimeBytecode ⟨0x171⟩, decode runtimeBytecode ⟨0x172⟩] =
    [some (.JUMPDEST, .none), some (.Push .PUSH1, some (⟨1⟩, 1)),
      some (.SWAP4, .none), some (.POP, .none), some (.SWAP1, .none),
      some (.SWAP2, .none), some (.DUP2, .none), some (.SWAP1, .none),
      some (.MOD, .none), some (.DUP3, .none)] := by native_decide

theorem wordLoopHeaderDecodes :
    [decode runtimeBytecode ⟨0x173⟩, decode runtimeBytecode ⟨0x174⟩,
      decode runtimeBytecode ⟨0x175⟩, decode runtimeBytecode ⟨0x178⟩,
      decode runtimeBytecode ⟨0x179⟩, decode runtimeBytecode ⟨0x17b⟩,
      decode runtimeBytecode ⟨0x17c⟩, decode runtimeBytecode ⟨0x17d⟩,
      decode runtimeBytecode ⟨0x180⟩] =
    [some (.JUMPDEST, .none), some (.ISZERO, .none),
      some (.Push .PUSH2, some (⟨0x161⟩, 2)), some (.JUMPI, .none),
      some (.Push .PUSH1, some (⟨1⟩, 1)), some (.DUP4, .none),
      some (.AND, .none), some (.Push .PUSH2, some (⟨0x190⟩, 2)),
      some (.JUMPI, .none)] := by native_decide

theorem wordLoopEvenDecodes :
    [decode runtimeBytecode ⟨0x181⟩, decode runtimeBytecode ⟨0x182⟩,
      decode runtimeBytecode ⟨0x183⟩, decode runtimeBytecode ⟨0x184⟩,
      decode runtimeBytecode ⟨0x185⟩, decode runtimeBytecode ⟨0x186⟩,
      decode runtimeBytecode ⟨0x187⟩, decode runtimeBytecode ⟨0x189⟩,
      decode runtimeBytecode ⟨0x18a⟩, decode runtimeBytecode ⟨0x18b⟩,
      decode runtimeBytecode ⟨0x18c⟩, decode runtimeBytecode ⟨0x18f⟩] =
    [some (.JUMPDEST, .none), some (.DUP1, .none), some (.DUP3, .none),
      some (.SWAP2, .none), some (.MULMOD, .none), some (.SWAP2, .none),
      some (.Push .PUSH1, some (⟨1⟩, 1)), some (.SHR, .none),
      some (.SWAP2, .none), some (.DUP3, .none),
      some (.Push .PUSH2, some (⟨0x173⟩, 2)), some (.JUMP, .none)] := by native_decide

theorem wordLoopOddDecodes :
    [decode runtimeBytecode ⟨0x190⟩, decode runtimeBytecode ⟨0x191⟩,
      decode runtimeBytecode ⟨0x192⟩, decode runtimeBytecode ⟨0x193⟩,
      decode runtimeBytecode ⟨0x194⟩, decode runtimeBytecode ⟨0x195⟩,
      decode runtimeBytecode ⟨0x196⟩, decode runtimeBytecode ⟨0x197⟩,
      decode runtimeBytecode ⟨0x198⟩, decode runtimeBytecode ⟨0x199⟩,
      decode runtimeBytecode ⟨0x19a⟩, decode runtimeBytecode ⟨0x19d⟩] =
    [some (.JUMPDEST, .none), some (.SWAP3, .none), some (.DUP2, .none),
      some (.DUP5, .none), some (.DUP2, .none), some (.SWAP3, .none),
      some (.MULMOD, .none), some (.SWAP4, .none), some (.SWAP1, .none),
      some (.POP, .none), some (.Push .PUSH2, some (⟨0x181⟩, 2)),
      some (.JUMP, .none)] := by native_decide

/-! Decode cache for the `cdRangeNonZero` helper used by the wide-input fast paths. -/

theorem cdRangeNonZeroDecodes :
    [decode runtimeBytecode ⟨694⟩, decode runtimeBytecode ⟨695⟩,
      decode runtimeBytecode ⟨696⟩, decode runtimeBytecode ⟨697⟩,
      decode runtimeBytecode ⟨698⟩,
      decode runtimeBytecode ⟨699⟩, decode runtimeBytecode ⟨700⟩,
      decode runtimeBytecode ⟨701⟩, decode runtimeBytecode ⟨702⟩,
      decode runtimeBytecode ⟨703⟩, decode runtimeBytecode ⟨706⟩,
      decode runtimeBytecode ⟨707⟩, decode runtimeBytecode ⟨708⟩,
      decode runtimeBytecode ⟨709⟩,
      decode runtimeBytecode ⟨710⟩, decode runtimeBytecode ⟨711⟩,
      decode runtimeBytecode ⟨712⟩, decode runtimeBytecode ⟨713⟩,
      decode runtimeBytecode ⟨714⟩, decode runtimeBytecode ⟨715⟩,
      decode runtimeBytecode ⟨716⟩, decode runtimeBytecode ⟨718⟩,
      decode runtimeBytecode ⟨719⟩, decode runtimeBytecode ⟨720⟩,
      decode runtimeBytecode ⟨723⟩,
      decode runtimeBytecode ⟨724⟩, decode runtimeBytecode ⟨725⟩,
      decode runtimeBytecode ⟨726⟩, decode runtimeBytecode ⟨729⟩,
      decode runtimeBytecode ⟨730⟩, decode runtimeBytecode ⟨731⟩,
      decode runtimeBytecode ⟨733⟩, decode runtimeBytecode ⟨734⟩,
      decode runtimeBytecode ⟨737⟩,
      decode runtimeBytecode ⟨738⟩, decode runtimeBytecode ⟨739⟩,
      decode runtimeBytecode ⟨740⟩, decode runtimeBytecode ⟨742⟩,
      decode runtimeBytecode ⟨743⟩, decode runtimeBytecode ⟨744⟩,
      decode runtimeBytecode ⟨745⟩, decode runtimeBytecode ⟨748⟩,
      decode runtimeBytecode ⟨749⟩, decode runtimeBytecode ⟨750⟩,
      decode runtimeBytecode ⟨752⟩, decode runtimeBytecode ⟨753⟩,
      decode runtimeBytecode ⟨755⟩, decode runtimeBytecode ⟨756⟩,
      decode runtimeBytecode ⟨757⟩, decode runtimeBytecode ⟨758⟩,
      decode runtimeBytecode ⟨761⟩] =
    [some (.JUMPDEST, .none), some (.SWAP1, .none), some (.PUSH0, .none),
      some (.SWAP3, .none), some (.SWAP2, .none),
      some (.JUMPDEST, .none), some (.DUP2, .none), some (.DUP2, .none),
      some (.LT, .none), some (.Push .PUSH2, some (⟨710⟩, 2)), some (.JUMPI, .none),
      some (.POP, .none), some (.POP, .none), some (.JUMP, .none),
      some (.JUMPDEST, .none), some (.DUP1, .none), some (.CALLDATALOAD, .none),
      some (.DUP2, .none), some (.DUP4, .none), some (.SUB, .none),
      some (.Push .PUSH1, some (⟨32⟩, 1)), some (.DUP2, .none), some (.LT, .none),
      some (.Push .PUSH2, some (⟨749⟩, 2)), some (.JUMPI, .none),
      some (.JUMPDEST, .none), some (.POP, .none),
      some (.Push .PUSH2, some (⟨738⟩, 2)), some (.JUMPI, .none),
      some (.JUMPDEST, .none), some (.Push .PUSH1, some (⟨32⟩, 1)),
      some (.ADD, .none), some (.Push .PUSH2, some (⟨699⟩, 2)), some (.JUMP, .none),
      some (.JUMPDEST, .none), some (.POP, .none),
      some (.Push .PUSH1, some (⟨1⟩, 1)), some (.SWAP3, .none), some (.POP, .none),
      some (.DUP1, .none), some (.Push .PUSH2, some (⟨730⟩, 2)), some (.JUMP, .none),
      some (.JUMPDEST, .none), some (.Push .PUSH1, some (⟨32⟩, 1)),
      some (.SUB, .none), some (.Push .PUSH1, some (⟨3⟩, 1)), some (.SHL, .none),
      some (.SHR, .none), some (.PUSH0, .none),
      some (.Push .PUSH2, some (⟨724⟩, 2)), some (.JUMP, .none)] := by
  native_decide

/-! Decode cache for the wide-input `isGt1` helper. -/

theorem isGt1Decodes :
    [decode runtimeBytecode ⟨762⟩, decode runtimeBytecode ⟨763⟩,
      decode runtimeBytecode ⟨764⟩, decode runtimeBytecode ⟨765⟩,
      decode runtimeBytecode ⟨766⟩, decode runtimeBytecode ⟨767⟩,
      decode runtimeBytecode ⟨769⟩, decode runtimeBytecode ⟨770⟩,
      decode runtimeBytecode ⟨771⟩, decode runtimeBytecode ⟨774⟩,
      decode runtimeBytecode ⟨775⟩, decode runtimeBytecode ⟨776⟩,
      decode runtimeBytecode ⟨777⟩, decode runtimeBytecode ⟨778⟩,
      decode runtimeBytecode ⟨779⟩, decode runtimeBytecode ⟨780⟩,
      decode runtimeBytecode ⟨781⟩, decode runtimeBytecode ⟨782⟩,
      decode runtimeBytecode ⟨785⟩, decode runtimeBytecode ⟨786⟩,
      decode runtimeBytecode ⟨787⟩, decode runtimeBytecode ⟨788⟩,
      decode runtimeBytecode ⟨789⟩, decode runtimeBytecode ⟨790⟩,
      decode runtimeBytecode ⟨792⟩, decode runtimeBytecode ⟨793⟩,
      decode runtimeBytecode ⟨794⟩, decode runtimeBytecode ⟨795⟩,
      decode runtimeBytecode ⟨796⟩, decode runtimeBytecode ⟨797⟩,
      decode runtimeBytecode ⟨798⟩, decode runtimeBytecode ⟨799⟩,
      decode runtimeBytecode ⟨800⟩, decode runtimeBytecode ⟨801⟩,
      decode runtimeBytecode ⟨804⟩, decode runtimeBytecode ⟨805⟩,
      decode runtimeBytecode ⟨806⟩, decode runtimeBytecode ⟨807⟩,
      decode runtimeBytecode ⟨808⟩, decode runtimeBytecode ⟨810⟩,
      decode runtimeBytecode ⟨811⟩, decode runtimeBytecode ⟨812⟩,
      decode runtimeBytecode ⟨813⟩, decode runtimeBytecode ⟨814⟩,
      decode runtimeBytecode ⟨815⟩, decode runtimeBytecode ⟨816⟩,
      decode runtimeBytecode ⟨819⟩, decode runtimeBytecode ⟨820⟩,
      decode runtimeBytecode ⟨821⟩, decode runtimeBytecode ⟨822⟩,
      decode runtimeBytecode ⟨823⟩, decode runtimeBytecode ⟨824⟩,
      decode runtimeBytecode ⟨825⟩, decode runtimeBytecode ⟨826⟩,
      decode runtimeBytecode ⟨829⟩, decode runtimeBytecode ⟨830⟩,
      decode runtimeBytecode ⟨831⟩, decode runtimeBytecode ⟨832⟩,
      decode runtimeBytecode ⟨835⟩] =
    [some (.JUMPDEST, .none), some (.SWAP1, .none), some (.PUSH0, .none),
      some (.SWAP3, .none), some (.SWAP2, .none),
      some (.Push .PUSH1, some (⟨1⟩, 1)), some (.DUP3, .none), some (.GT, .none),
      some (.Push .PUSH2, some (⟨813⟩, 2)), some (.JUMPI, .none),
      some (.JUMPDEST, .none), some (.DUP2, .none), some (.ISZERO, .none),
      some (.ISZERO, .none), some (.DUP5, .none), some (.ISZERO, .none),
      some (.AND, .none), some (.Push .PUSH2, some (⟨789⟩, 2)), some (.JUMPI, .none),
      some (.POP, .none), some (.POP, .none), some (.JUMP, .none),
      some (.JUMPDEST, .none), some (.Push .PUSH1, some (⟨1⟩, 1)),
      some (.SWAP2, .none), some (.ADD, .none), some (.PUSH0, .none), some (.NOT, .none),
      some (.ADD, .none), some (.CALLDATALOAD, .none), some (.PUSH0, .none),
      some (.BYTE, .none), some (.GT, .none),
      some (.Push .PUSH2, some (⟨807⟩, 2)), some (.JUMPI, .none),
      some (.JUMPDEST, .none), some (.JUMP, .none),
      some (.JUMPDEST, .none), some (.Push .PUSH1, some (⟨1⟩, 1)),
      some (.SWAP2, .none), some (.POP, .none), some (.JUMP, .none),
      some (.JUMPDEST, .none), some (.SWAP3, .none), some (.POP, .none),
      some (.Push .PUSH2, some (⟨830⟩, 2)), some (.PUSH0, .none), some (.NOT, .none),
      some (.DUP3, .none), some (.DUP6, .none), some (.ADD, .none), some (.ADD, .none),
      some (.DUP5, .none), some (.Push .PUSH2, some (⟨694⟩, 2)), some (.JUMP, .none),
      some (.JUMPDEST, .none), some (.SWAP3, .none),
      some (.Push .PUSH2, some (⟨775⟩, 2)), some (.JUMP, .none)] := by
  native_decide

/-- Jump destinations used by the single-word implementation. They are checked together so the
8.6KB runtime's jump-destination analysis is evaluated only once. -/
private theorem wordPathJumpDests :
    (Ethereum.EVM.D_J runtimeBytecode 0).contains ⟨0x1a9⟩ = true ∧
    (Ethereum.EVM.D_J runtimeBytecode 0).contains ⟨0x33⟩ = true ∧
    (Ethereum.EVM.D_J runtimeBytecode 0).contains ⟨0x19e⟩ = true ∧
    (Ethereum.EVM.D_J runtimeBytecode 0).contains ⟨0x39⟩ = true ∧
    (Ethereum.EVM.D_J runtimeBytecode 0).contains ⟨0x12e⟩ = true := by
  have hbool :
      let jumps := Ethereum.EVM.D_J runtimeBytecode 0
      decide (jumps.contains ⟨0x1a9⟩ = true) &&
      decide (jumps.contains ⟨0x33⟩ = true) &&
      decide (jumps.contains ⟨0x19e⟩ = true) &&
      decide (jumps.contains ⟨0x39⟩ = true) &&
      decide (jumps.contains ⟨0x12e⟩ = true) = true := by native_decide
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hbool
  rcases hbool with ⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩
  exact ⟨h0, h1, h2, h3, h4⟩

@[valid_jumps] theorem jumpDest_1a9 :
    (Ethereum.EVM.D_J runtimeBytecode 0).contains ⟨0x1a9⟩ = true :=
  wordPathJumpDests.1

@[valid_jumps] theorem jumpDest_33 :
    (Ethereum.EVM.D_J runtimeBytecode 0).contains ⟨0x33⟩ = true :=
  wordPathJumpDests.2.1

@[valid_jumps] theorem jumpDest_19e :
    (Ethereum.EVM.D_J runtimeBytecode 0).contains ⟨0x19e⟩ = true :=
  wordPathJumpDests.2.2.1

@[valid_jumps] theorem jumpDest_39 :
    (Ethereum.EVM.D_J runtimeBytecode 0).contains ⟨0x39⟩ = true :=
  wordPathJumpDests.2.2.2.1

@[valid_jumps] theorem jumpDest_12e :
    (Ethereum.EVM.D_J runtimeBytecode 0).contains ⟨0x12e⟩ = true :=
  wordPathJumpDests.2.2.2.2

private theorem wordLoopJumpDests :
    (Ethereum.EVM.D_J runtimeBytecode 0).contains ⟨0x161⟩ = true ∧
    (Ethereum.EVM.D_J runtimeBytecode 0).contains ⟨0x168⟩ = true ∧
    (Ethereum.EVM.D_J runtimeBytecode 0).contains ⟨0x173⟩ = true ∧
    (Ethereum.EVM.D_J runtimeBytecode 0).contains ⟨0x181⟩ = true ∧
    (Ethereum.EVM.D_J runtimeBytecode 0).contains ⟨0x190⟩ = true := by
  have hbool :
      let jumps := Ethereum.EVM.D_J runtimeBytecode 0
      decide (jumps.contains ⟨0x161⟩ = true) &&
      decide (jumps.contains ⟨0x168⟩ = true) &&
      decide (jumps.contains ⟨0x173⟩ = true) &&
      decide (jumps.contains ⟨0x181⟩ = true) &&
      decide (jumps.contains ⟨0x190⟩ = true) = true := by native_decide
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hbool
  rcases hbool with ⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩
  exact ⟨h0, h1, h2, h3, h4⟩

@[valid_jumps] theorem jumpDest_161 :
    (Ethereum.EVM.D_J runtimeBytecode 0).contains ⟨0x161⟩ = true :=
  wordLoopJumpDests.1

@[valid_jumps] theorem jumpDest_168 :
    (Ethereum.EVM.D_J runtimeBytecode 0).contains ⟨0x168⟩ = true :=
  wordLoopJumpDests.2.1

@[valid_jumps] theorem jumpDest_173 :
    (Ethereum.EVM.D_J runtimeBytecode 0).contains ⟨0x173⟩ = true :=
  wordLoopJumpDests.2.2.1

@[valid_jumps] theorem jumpDest_181 :
    (Ethereum.EVM.D_J runtimeBytecode 0).contains ⟨0x181⟩ = true :=
  wordLoopJumpDests.2.2.2.1

@[valid_jumps] theorem jumpDest_190 :
    (Ethereum.EVM.D_J runtimeBytecode 0).contains ⟨0x190⟩ = true :=
  wordLoopJumpDests.2.2.2.2

private theorem cdRangeJumpDests :
    (Ethereum.EVM.D_J runtimeBytecode 0).contains ⟨694⟩ = true ∧
    (Ethereum.EVM.D_J runtimeBytecode 0).contains ⟨699⟩ = true ∧
    (Ethereum.EVM.D_J runtimeBytecode 0).contains ⟨710⟩ = true ∧
    (Ethereum.EVM.D_J runtimeBytecode 0).contains ⟨724⟩ = true ∧
    (Ethereum.EVM.D_J runtimeBytecode 0).contains ⟨730⟩ = true ∧
    (Ethereum.EVM.D_J runtimeBytecode 0).contains ⟨738⟩ = true ∧
    (Ethereum.EVM.D_J runtimeBytecode 0).contains ⟨749⟩ = true := by
  have hbool :
      let jumps := Ethereum.EVM.D_J runtimeBytecode 0
      decide (jumps.contains ⟨694⟩ = true) &&
      decide (jumps.contains ⟨699⟩ = true) &&
      decide (jumps.contains ⟨710⟩ = true) &&
      decide (jumps.contains ⟨724⟩ = true) &&
      decide (jumps.contains ⟨730⟩ = true) &&
      decide (jumps.contains ⟨738⟩ = true) &&
      decide (jumps.contains ⟨749⟩ = true) = true := by native_decide
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hbool
  rcases hbool with ⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩
  exact ⟨h0, h1, h2, h3, h4, h5, h6⟩

@[valid_jumps] theorem jumpDest_694 :
    (Ethereum.EVM.D_J runtimeBytecode 0).contains ⟨694⟩ = true := cdRangeJumpDests.1

@[valid_jumps] theorem jumpDest_699 :
    (Ethereum.EVM.D_J runtimeBytecode 0).contains ⟨699⟩ = true := cdRangeJumpDests.2.1

@[valid_jumps] theorem jumpDest_710 :
    (Ethereum.EVM.D_J runtimeBytecode 0).contains ⟨710⟩ = true := cdRangeJumpDests.2.2.1

@[valid_jumps] theorem jumpDest_724 :
    (Ethereum.EVM.D_J runtimeBytecode 0).contains ⟨724⟩ = true := cdRangeJumpDests.2.2.2.1

@[valid_jumps] theorem jumpDest_730 :
    (Ethereum.EVM.D_J runtimeBytecode 0).contains ⟨730⟩ = true := cdRangeJumpDests.2.2.2.2.1

@[valid_jumps] theorem jumpDest_738 :
    (Ethereum.EVM.D_J runtimeBytecode 0).contains ⟨738⟩ = true := cdRangeJumpDests.2.2.2.2.2.1

@[valid_jumps] theorem jumpDest_749 :
    (Ethereum.EVM.D_J runtimeBytecode 0).contains ⟨749⟩ = true := cdRangeJumpDests.2.2.2.2.2.2

private theorem isGt1JumpDests :
    (Ethereum.EVM.D_J runtimeBytecode 0).contains ⟨762⟩ = true ∧
    (Ethereum.EVM.D_J runtimeBytecode 0).contains ⟨775⟩ = true ∧
    (Ethereum.EVM.D_J runtimeBytecode 0).contains ⟨789⟩ = true ∧
    (Ethereum.EVM.D_J runtimeBytecode 0).contains ⟨807⟩ = true ∧
    (Ethereum.EVM.D_J runtimeBytecode 0).contains ⟨813⟩ = true ∧
    (Ethereum.EVM.D_J runtimeBytecode 0).contains ⟨830⟩ = true := by
  have hbool :
      let jumps := Ethereum.EVM.D_J runtimeBytecode 0
      decide (jumps.contains ⟨762⟩ = true) &&
      decide (jumps.contains ⟨775⟩ = true) &&
      decide (jumps.contains ⟨789⟩ = true) &&
      decide (jumps.contains ⟨807⟩ = true) &&
      decide (jumps.contains ⟨813⟩ = true) &&
      decide (jumps.contains ⟨830⟩ = true) = true := by native_decide
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hbool
  rcases hbool with ⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩
  exact ⟨h0, h1, h2, h3, h4, h5⟩

@[valid_jumps] theorem jumpDest_762 :
    (Ethereum.EVM.D_J runtimeBytecode 0).contains ⟨762⟩ = true := isGt1JumpDests.1

@[valid_jumps] theorem jumpDest_775 :
    (Ethereum.EVM.D_J runtimeBytecode 0).contains ⟨775⟩ = true := isGt1JumpDests.2.1

@[valid_jumps] theorem jumpDest_789 :
    (Ethereum.EVM.D_J runtimeBytecode 0).contains ⟨789⟩ = true := isGt1JumpDests.2.2.1

@[valid_jumps] theorem jumpDest_807 :
    (Ethereum.EVM.D_J runtimeBytecode 0).contains ⟨807⟩ = true := isGt1JumpDests.2.2.2.1

@[valid_jumps] theorem jumpDest_813 :
    (Ethereum.EVM.D_J runtimeBytecode 0).contains ⟨813⟩ = true := isGt1JumpDests.2.2.2.2.1

@[valid_jumps] theorem jumpDest_830 :
    (Ethereum.EVM.D_J runtimeBytecode 0).contains ⟨830⟩ = true := isGt1JumpDests.2.2.2.2.2

private theorem trivialJumpDests :
    (Ethereum.EVM.D_J runtimeBytecode 0).contains ⟨83⟩ = true ∧
    (Ethereum.EVM.D_J runtimeBytecode 0).contains ⟨268⟩ = true ∧
    (Ethereum.EVM.D_J runtimeBytecode 0).contains ⟨283⟩ = true ∧
    (Ethereum.EVM.D_J runtimeBytecode 0).contains ⟨291⟩ = true := by
  let jumps := Ethereum.EVM.D_J runtimeBytecode 0
  have h :
      decide (jumps.contains ⟨83⟩ = true) &&
      decide (jumps.contains ⟨268⟩ = true) &&
      decide (jumps.contains ⟨283⟩ = true) &&
      decide (jumps.contains ⟨291⟩ = true) = true := by native_decide
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩
  exact ⟨h0, h1, h2, h3⟩

@[valid_jumps] theorem jumpDest_83 :
    (Ethereum.EVM.D_J runtimeBytecode 0).contains ⟨83⟩ = true := trivialJumpDests.1

@[valid_jumps] theorem jumpDest_268 :
    (Ethereum.EVM.D_J runtimeBytecode 0).contains ⟨268⟩ = true := trivialJumpDests.2.1

@[valid_jumps] theorem jumpDest_283 :
    (Ethereum.EVM.D_J runtimeBytecode 0).contains ⟨283⟩ = true := trivialJumpDests.2.2.1

@[valid_jumps] theorem jumpDest_291 :
    (Ethereum.EVM.D_J runtimeBytecode 0).contains ⟨291⟩ = true := trivialJumpDests.2.2.2

private theorem baseRangeJumpDests :
    (Ethereum.EVM.D_J runtimeBytecode 0).contains ⟨625⟩ = true ∧
    (Ethereum.EVM.D_J runtimeBytecode 0).contains ⟨631⟩ = true ∧
    (Ethereum.EVM.D_J runtimeBytecode 0).contains ⟨642⟩ = true ∧
    (Ethereum.EVM.D_J runtimeBytecode 0).contains ⟨656⟩ = true ∧
    (Ethereum.EVM.D_J runtimeBytecode 0).contains ⟨662⟩ = true ∧
    (Ethereum.EVM.D_J runtimeBytecode 0).contains ⟨670⟩ = true ∧
    (Ethereum.EVM.D_J runtimeBytecode 0).contains ⟨681⟩ = true := by
  let jumps := Ethereum.EVM.D_J runtimeBytecode 0
  have h :
      decide (jumps.contains ⟨625⟩ = true) &&
      decide (jumps.contains ⟨631⟩ = true) &&
      decide (jumps.contains ⟨642⟩ = true) &&
      decide (jumps.contains ⟨656⟩ = true) &&
      decide (jumps.contains ⟨662⟩ = true) &&
      decide (jumps.contains ⟨670⟩ = true) &&
      decide (jumps.contains ⟨681⟩ = true) = true := by native_decide
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with ⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩
  exact ⟨h0, h1, h2, h3, h4, h5, h6⟩

@[valid_jumps] theorem jumpDest_625 :
    (Ethereum.EVM.D_J runtimeBytecode 0).contains ⟨625⟩ = true := baseRangeJumpDests.1
@[valid_jumps] theorem jumpDest_631 :
    (Ethereum.EVM.D_J runtimeBytecode 0).contains ⟨631⟩ = true := baseRangeJumpDests.2.1
@[valid_jumps] theorem jumpDest_642 :
    (Ethereum.EVM.D_J runtimeBytecode 0).contains ⟨642⟩ = true := baseRangeJumpDests.2.2.1
@[valid_jumps] theorem jumpDest_656 :
    (Ethereum.EVM.D_J runtimeBytecode 0).contains ⟨656⟩ = true := baseRangeJumpDests.2.2.2.1
@[valid_jumps] theorem jumpDest_662 :
    (Ethereum.EVM.D_J runtimeBytecode 0).contains ⟨662⟩ = true := baseRangeJumpDests.2.2.2.2.1
@[valid_jumps] theorem jumpDest_670 :
    (Ethereum.EVM.D_J runtimeBytecode 0).contains ⟨670⟩ = true := baseRangeJumpDests.2.2.2.2.2.1
@[valid_jumps] theorem jumpDest_681 :
    (Ethereum.EVM.D_J runtimeBytecode 0).contains ⟨681⟩ = true := baseRangeJumpDests.2.2.2.2.2.2

private theorem baseTrivialJumpDests :
    (Ethereum.EVM.D_J runtimeBytecode 0).contains ⟨96⟩ = true ∧
    (Ethereum.EVM.D_J runtimeBytecode 0).contains ⟨181⟩ = true ∧
    (Ethereum.EVM.D_J runtimeBytecode 0).contains ⟨191⟩ = true ∧
    (Ethereum.EVM.D_J runtimeBytecode 0).contains ⟨217⟩ = true ∧
    (Ethereum.EVM.D_J runtimeBytecode 0).contains ⟨226⟩ = true ∧
    (Ethereum.EVM.D_J runtimeBytecode 0).contains ⟨237⟩ = true ∧
    (Ethereum.EVM.D_J runtimeBytecode 0).contains ⟨250⟩ = true ∧
    (Ethereum.EVM.D_J runtimeBytecode 0).contains ⟨255⟩ = true := by
  let jumps := Ethereum.EVM.D_J runtimeBytecode 0
  have h :
      decide (jumps.contains ⟨96⟩ = true) &&
      decide (jumps.contains ⟨181⟩ = true) &&
      decide (jumps.contains ⟨191⟩ = true) &&
      decide (jumps.contains ⟨217⟩ = true) &&
      decide (jumps.contains ⟨226⟩ = true) &&
      decide (jumps.contains ⟨237⟩ = true) &&
      decide (jumps.contains ⟨250⟩ = true) &&
      decide (jumps.contains ⟨255⟩ = true) = true := by native_decide
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with ⟨⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩

@[valid_jumps] theorem jumpDest_wide96 :
    (Ethereum.EVM.D_J runtimeBytecode 0).contains ⟨96⟩ = true := baseTrivialJumpDests.1
@[valid_jumps] theorem jumpDest_wide181 :
    (Ethereum.EVM.D_J runtimeBytecode 0).contains ⟨181⟩ = true := baseTrivialJumpDests.2.1
@[valid_jumps] theorem jumpDest_wide191 :
    (Ethereum.EVM.D_J runtimeBytecode 0).contains ⟨191⟩ = true := baseTrivialJumpDests.2.2.1
@[valid_jumps] theorem jumpDest_wide217 :
    (Ethereum.EVM.D_J runtimeBytecode 0).contains ⟨217⟩ = true := baseTrivialJumpDests.2.2.2.1
@[valid_jumps] theorem jumpDest_wide226 :
    (Ethereum.EVM.D_J runtimeBytecode 0).contains ⟨226⟩ = true := baseTrivialJumpDests.2.2.2.2.1
@[valid_jumps] theorem jumpDest_wide237 :
    (Ethereum.EVM.D_J runtimeBytecode 0).contains ⟨237⟩ = true := baseTrivialJumpDests.2.2.2.2.2.1
@[valid_jumps] theorem jumpDest_wide250 :
    (Ethereum.EVM.D_J runtimeBytecode 0).contains ⟨250⟩ = true := baseTrivialJumpDests.2.2.2.2.2.2.1
@[valid_jumps] theorem jumpDest_wide255 :
    (Ethereum.EVM.D_J runtimeBytecode 0).contains ⟨255⟩ = true := baseTrivialJumpDests.2.2.2.2.2.2.2

private theorem allocationJumpDests :
    (Ethereum.EVM.D_J runtimeBytecode 0).contains ⟨523⟩ = true ∧
    (Ethereum.EVM.D_J runtimeBytecode 0).contains ⟨528⟩ = true ∧
    (Ethereum.EVM.D_J runtimeBytecode 0).contains ⟨556⟩ = true ∧
    (Ethereum.EVM.D_J runtimeBytecode 0).contains ⟨566⟩ = true ∧
    (Ethereum.EVM.D_J runtimeBytecode 0).contains ⟨581⟩ = true ∧
    (Ethereum.EVM.D_J runtimeBytecode 0).contains ⟨594⟩ = true ∧
    (Ethereum.EVM.D_J runtimeBytecode 0).contains ⟨599⟩ = true ∧
    (Ethereum.EVM.D_J runtimeBytecode 0).contains ⟨615⟩ = true := by
  let jumps := Ethereum.EVM.D_J runtimeBytecode 0
  have h :
      decide (jumps.contains ⟨523⟩ = true) &&
      decide (jumps.contains ⟨528⟩ = true) &&
      decide (jumps.contains ⟨556⟩ = true) &&
      decide (jumps.contains ⟨566⟩ = true) &&
      decide (jumps.contains ⟨581⟩ = true) &&
      decide (jumps.contains ⟨594⟩ = true) &&
      decide (jumps.contains ⟨599⟩ = true) &&
      decide (jumps.contains ⟨615⟩ = true) = true := by native_decide
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with ⟨⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩

@[valid_jumps] theorem jumpDest_523 :
    (Ethereum.EVM.D_J runtimeBytecode 0).contains ⟨523⟩ = true := allocationJumpDests.1
@[valid_jumps] theorem jumpDest_528 :
    (Ethereum.EVM.D_J runtimeBytecode 0).contains ⟨528⟩ = true := allocationJumpDests.2.1
@[valid_jumps] theorem jumpDest_556 :
    (Ethereum.EVM.D_J runtimeBytecode 0).contains ⟨556⟩ = true := allocationJumpDests.2.2.1
@[valid_jumps] theorem jumpDest_566 :
    (Ethereum.EVM.D_J runtimeBytecode 0).contains ⟨566⟩ = true := allocationJumpDests.2.2.2.1
@[valid_jumps] theorem jumpDest_581 :
    (Ethereum.EVM.D_J runtimeBytecode 0).contains ⟨581⟩ = true := allocationJumpDests.2.2.2.2.1
@[valid_jumps] theorem jumpDest_594 :
    (Ethereum.EVM.D_J runtimeBytecode 0).contains ⟨594⟩ = true := allocationJumpDests.2.2.2.2.2.1
@[valid_jumps] theorem jumpDest_599 :
    (Ethereum.EVM.D_J runtimeBytecode 0).contains ⟨599⟩ = true := allocationJumpDests.2.2.2.2.2.2.1
@[valid_jumps] theorem jumpDest_615 :
    (Ethereum.EVM.D_J runtimeBytecode 0).contains ⟨615⟩ = true := allocationJumpDests.2.2.2.2.2.2.2

private theorem operandSetupJumpDests :
    (Ethereum.EVM.D_J runtimeBytecode 0).contains ⟨126⟩ = true ∧
    (Ethereum.EVM.D_J runtimeBytecode 0).contains ⟨136⟩ = true ∧
    (Ethereum.EVM.D_J runtimeBytecode 0).contains ⟨149⟩ = true ∧
    (Ethereum.EVM.D_J runtimeBytecode 0).contains ⟨156⟩ = true ∧
    (Ethereum.EVM.D_J runtimeBytecode 0).contains ⟨162⟩ = true ∧
    (Ethereum.EVM.D_J runtimeBytecode 0).contains ⟨836⟩ = true ∧
    (Ethereum.EVM.D_J runtimeBytecode 0).contains ⟨847⟩ = true ∧
    (Ethereum.EVM.D_J runtimeBytecode 0).contains ⟨855⟩ = true ∧
    (Ethereum.EVM.D_J runtimeBytecode 0).contains ⟨865⟩ = true ∧
    (Ethereum.EVM.D_J runtimeBytecode 0).contains ⟨874⟩ = true ∧
    (Ethereum.EVM.D_J runtimeBytecode 0).contains ⟨882⟩ = true ∧
    (Ethereum.EVM.D_J runtimeBytecode 0).contains ⟨924⟩ = true ∧
    (Ethereum.EVM.D_J runtimeBytecode 0).contains ⟨934⟩ = true ∧
    (Ethereum.EVM.D_J runtimeBytecode 0).contains ⟨942⟩ = true ∧
    (Ethereum.EVM.D_J runtimeBytecode 0).contains ⟨953⟩ = true ∧
    (Ethereum.EVM.D_J runtimeBytecode 0).contains ⟨959⟩ = true ∧
    (Ethereum.EVM.D_J runtimeBytecode 0).contains ⟨967⟩ = true ∧
    (Ethereum.EVM.D_J runtimeBytecode 0).contains ⟨1183⟩ = true := by
  let jumps := Ethereum.EVM.D_J runtimeBytecode 0
  have h : decide (
      jumps.contains ⟨126⟩ = true ∧ jumps.contains ⟨136⟩ = true ∧
      jumps.contains ⟨149⟩ = true ∧ jumps.contains ⟨156⟩ = true ∧
      jumps.contains ⟨162⟩ = true ∧ jumps.contains ⟨836⟩ = true ∧
      jumps.contains ⟨847⟩ = true ∧ jumps.contains ⟨855⟩ = true ∧
      jumps.contains ⟨865⟩ = true ∧ jumps.contains ⟨874⟩ = true ∧
      jumps.contains ⟨882⟩ = true ∧ jumps.contains ⟨924⟩ = true ∧
      jumps.contains ⟨934⟩ = true ∧ jumps.contains ⟨942⟩ = true ∧
      jumps.contains ⟨953⟩ = true ∧ jumps.contains ⟨959⟩ = true ∧
      jumps.contains ⟨967⟩ = true ∧ jumps.contains ⟨1183⟩ = true) = true := by
    native_decide
  simpa only [decide_eq_true_eq] using h

@[valid_jumps] theorem jumpDest_126 :
    (Ethereum.EVM.D_J runtimeBytecode 0).contains ⟨126⟩ = true := operandSetupJumpDests.1
@[valid_jumps] theorem jumpDest_136 :
    (Ethereum.EVM.D_J runtimeBytecode 0).contains ⟨136⟩ = true := operandSetupJumpDests.2.1
@[valid_jumps] theorem jumpDest_149 :
    (Ethereum.EVM.D_J runtimeBytecode 0).contains ⟨149⟩ = true := operandSetupJumpDests.2.2.1
@[valid_jumps] theorem jumpDest_156 :
    (Ethereum.EVM.D_J runtimeBytecode 0).contains ⟨156⟩ = true := operandSetupJumpDests.2.2.2.1
@[valid_jumps] theorem jumpDest_162 :
    (Ethereum.EVM.D_J runtimeBytecode 0).contains ⟨162⟩ = true := operandSetupJumpDests.2.2.2.2.1
@[valid_jumps] theorem jumpDest_operand168 :
    (Ethereum.EVM.D_J runtimeBytecode 0).contains ⟨168⟩ = true := by native_decide
@[valid_jumps] theorem jumpDest_836 :
    (Ethereum.EVM.D_J runtimeBytecode 0).contains ⟨836⟩ = true := operandSetupJumpDests.2.2.2.2.2.1
@[valid_jumps] theorem jumpDest_847 :
    (Ethereum.EVM.D_J runtimeBytecode 0).contains ⟨847⟩ = true := operandSetupJumpDests.2.2.2.2.2.2.1
@[valid_jumps] theorem jumpDest_855 :
    (Ethereum.EVM.D_J runtimeBytecode 0).contains ⟨855⟩ = true := operandSetupJumpDests.2.2.2.2.2.2.2.1
@[valid_jumps] theorem jumpDest_865 :
    (Ethereum.EVM.D_J runtimeBytecode 0).contains ⟨865⟩ = true := operandSetupJumpDests.2.2.2.2.2.2.2.2.1
@[valid_jumps] theorem jumpDest_874 :
    (Ethereum.EVM.D_J runtimeBytecode 0).contains ⟨874⟩ = true := operandSetupJumpDests.2.2.2.2.2.2.2.2.2.1
@[valid_jumps] theorem jumpDest_882 :
    (Ethereum.EVM.D_J runtimeBytecode 0).contains ⟨882⟩ = true := operandSetupJumpDests.2.2.2.2.2.2.2.2.2.2.1
@[valid_jumps] theorem jumpDest_924 :
    (Ethereum.EVM.D_J runtimeBytecode 0).contains ⟨924⟩ = true := operandSetupJumpDests.2.2.2.2.2.2.2.2.2.2.2.1
@[valid_jumps] theorem jumpDest_934 :
    (Ethereum.EVM.D_J runtimeBytecode 0).contains ⟨934⟩ = true := operandSetupJumpDests.2.2.2.2.2.2.2.2.2.2.2.2.1
@[valid_jumps] theorem jumpDest_942 :
    (Ethereum.EVM.D_J runtimeBytecode 0).contains ⟨942⟩ = true := operandSetupJumpDests.2.2.2.2.2.2.2.2.2.2.2.2.2.1
@[valid_jumps] theorem jumpDest_953 :
    (Ethereum.EVM.D_J runtimeBytecode 0).contains ⟨953⟩ = true := operandSetupJumpDests.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
@[valid_jumps] theorem jumpDest_959 :
    (Ethereum.EVM.D_J runtimeBytecode 0).contains ⟨959⟩ = true := operandSetupJumpDests.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
@[valid_jumps] theorem jumpDest_967 :
    (Ethereum.EVM.D_J runtimeBytecode 0).contains ⟨967⟩ = true := operandSetupJumpDests.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
@[valid_jumps] theorem jumpDest_1183 :
    (Ethereum.EVM.D_J runtimeBytecode 0).contains ⟨1183⟩ = true := operandSetupJumpDests.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

/-! Jump destinations used by the arbitrary-length/single-word-modulus helper.  They are cached
as one native computation because recomputing `D_J` separately for every loop edge is expensive. -/
private theorem wordHelperJumpDests :
    (Ethereum.EVM.D_J runtimeBytecode 0).contains ⟨1271⟩ = true ∧
    (Ethereum.EVM.D_J runtimeBytecode 0).contains ⟨2574⟩ = true ∧
    (Ethereum.EVM.D_J runtimeBytecode 0).contains ⟨2615⟩ = true ∧
    (Ethereum.EVM.D_J runtimeBytecode 0).contains ⟨2630⟩ = true ∧
    (Ethereum.EVM.D_J runtimeBytecode 0).contains ⟨2663⟩ = true ∧
    (Ethereum.EVM.D_J runtimeBytecode 0).contains ⟨2665⟩ = true ∧
    (Ethereum.EVM.D_J runtimeBytecode 0).contains ⟨2686⟩ = true ∧
    (Ethereum.EVM.D_J runtimeBytecode 0).contains ⟨2695⟩ = true ∧
    (Ethereum.EVM.D_J runtimeBytecode 0).contains ⟨2710⟩ = true ∧
    (Ethereum.EVM.D_J runtimeBytecode 0).contains ⟨2728⟩ = true ∧
    (Ethereum.EVM.D_J runtimeBytecode 0).contains ⟨2736⟩ = true ∧
    (Ethereum.EVM.D_J runtimeBytecode 0).contains ⟨2748⟩ = true ∧
    (Ethereum.EVM.D_J runtimeBytecode 0).contains ⟨2776⟩ = true ∧
    (Ethereum.EVM.D_J runtimeBytecode 0).contains ⟨2783⟩ = true ∧
    (Ethereum.EVM.D_J runtimeBytecode 0).contains ⟨2806⟩ = true := by
  let jumps := Ethereum.EVM.D_J runtimeBytecode 0
  have h : decide (
      jumps.contains ⟨1271⟩ = true ∧ jumps.contains ⟨2574⟩ = true ∧
      jumps.contains ⟨2615⟩ = true ∧ jumps.contains ⟨2630⟩ = true ∧
      jumps.contains ⟨2663⟩ = true ∧ jumps.contains ⟨2665⟩ = true ∧
      jumps.contains ⟨2686⟩ = true ∧ jumps.contains ⟨2695⟩ = true ∧
      jumps.contains ⟨2710⟩ = true ∧ jumps.contains ⟨2728⟩ = true ∧
      jumps.contains ⟨2736⟩ = true ∧ jumps.contains ⟨2748⟩ = true ∧
      jumps.contains ⟨2776⟩ = true ∧ jumps.contains ⟨2783⟩ = true ∧
      jumps.contains ⟨2806⟩ = true) = true := by
    native_decide
  simpa only [decide_eq_true_eq] using h

@[valid_jumps] theorem jumpDest_1271 :
    (Ethereum.EVM.D_J runtimeBytecode 0).contains ⟨1271⟩ = true := wordHelperJumpDests.1
@[valid_jumps] theorem jumpDest_2574 :
    (Ethereum.EVM.D_J runtimeBytecode 0).contains ⟨2574⟩ = true := wordHelperJumpDests.2.1
@[valid_jumps] theorem jumpDest_2658 :
    (Ethereum.EVM.D_J runtimeBytecode 0).contains ⟨2658⟩ = true := by native_decide
@[valid_jumps] theorem jumpDest_2615 :
    (Ethereum.EVM.D_J runtimeBytecode 0).contains ⟨2615⟩ = true := wordHelperJumpDests.2.2.1
@[valid_jumps] theorem jumpDest_2630 :
    (Ethereum.EVM.D_J runtimeBytecode 0).contains ⟨2630⟩ = true := wordHelperJumpDests.2.2.2.1
@[valid_jumps] theorem jumpDest_2663 :
    (Ethereum.EVM.D_J runtimeBytecode 0).contains ⟨2663⟩ = true := wordHelperJumpDests.2.2.2.2.1
@[valid_jumps] theorem jumpDest_2665 :
    (Ethereum.EVM.D_J runtimeBytecode 0).contains ⟨2665⟩ = true := wordHelperJumpDests.2.2.2.2.2.1
@[valid_jumps] theorem jumpDest_2686 :
    (Ethereum.EVM.D_J runtimeBytecode 0).contains ⟨2686⟩ = true := wordHelperJumpDests.2.2.2.2.2.2.1
@[valid_jumps] theorem jumpDest_2695 :
    (Ethereum.EVM.D_J runtimeBytecode 0).contains ⟨2695⟩ = true := wordHelperJumpDests.2.2.2.2.2.2.2.1
@[valid_jumps] theorem jumpDest_2710 :
    (Ethereum.EVM.D_J runtimeBytecode 0).contains ⟨2710⟩ = true := wordHelperJumpDests.2.2.2.2.2.2.2.2.1
@[valid_jumps] theorem jumpDest_2728 :
    (Ethereum.EVM.D_J runtimeBytecode 0).contains ⟨2728⟩ = true := wordHelperJumpDests.2.2.2.2.2.2.2.2.2.1
@[valid_jumps] theorem jumpDest_2736 :
    (Ethereum.EVM.D_J runtimeBytecode 0).contains ⟨2736⟩ = true := wordHelperJumpDests.2.2.2.2.2.2.2.2.2.2.1
@[valid_jumps] theorem jumpDest_2748 :
    (Ethereum.EVM.D_J runtimeBytecode 0).contains ⟨2748⟩ = true := wordHelperJumpDests.2.2.2.2.2.2.2.2.2.2.2.1
@[valid_jumps] theorem jumpDest_2776 :
    (Ethereum.EVM.D_J runtimeBytecode 0).contains ⟨2776⟩ = true := wordHelperJumpDests.2.2.2.2.2.2.2.2.2.2.2.2.1
@[valid_jumps] theorem jumpDest_2783 :
    (Ethereum.EVM.D_J runtimeBytecode 0).contains ⟨2783⟩ = true := wordHelperJumpDests.2.2.2.2.2.2.2.2.2.2.2.2.2.1
@[valid_jumps] theorem jumpDest_2806 :
    (Ethereum.EVM.D_J runtimeBytecode 0).contains ⟨2806⟩ = true := wordHelperJumpDests.2.2.2.2.2.2.2.2.2.2.2.2.2.2

end Modexp
