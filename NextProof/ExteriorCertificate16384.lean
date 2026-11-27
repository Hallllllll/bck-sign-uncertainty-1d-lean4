import NextProof.ExteriorOrigin
import NextProof.ExteriorData16384

/-! Kernel checks for the exact projected-16384 data. -/
namespace NextProof.Exterior

open Data16384 Polynomial
open scoped FourierTransform

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

private def originScale : ℕ := 2^40

private theorem chunk00_len : chunk00.length = 128 := by decide +kernel
private theorem chunk00_mass : negativeMass chunk00 = 30156563134771699448476073984 := by decide +kernel
private theorem chunk00_origin :
    originRun 0 chunk00 ⟨1099511627776, 1099511627776, 0⟩ = ⟨38751886493, 38751886576, -1522832844956883897370838567192274927616⟩ := by decide +kernel

private theorem chunk01_len : chunk01.length = 128 := by decide +kernel
private theorem chunk01_mass : negativeMass chunk01 = 691857711540102176968802304 := by decide +kernel
private theorem chunk01_origin :
    originRun 128 chunk01 ⟨38751886493, 38751886576, -1522832844956883897370838567192274927616⟩ = ⟨27408412350, 27408412519, -1023845156440401722521082214311513817088⟩ := by decide +kernel

private theorem chunk02_len : chunk02.length = 128 := by decide +kernel
private theorem chunk02_mass : negativeMass chunk02 = 250203092175214467148152832 := by decide +kernel
private theorem chunk02_origin :
    originRun 256 chunk02 ⟨27408412350, 27408412519, -1023845156440401722521082214311513817088⟩ = ⟨22380696185, 22380696436, -754562462784918637850341729533525229568⟩ := by decide +kernel

private theorem chunk03_len : chunk03.length = 128 := by decide +kernel
private theorem chunk03_mass : negativeMass chunk03 = 188290525845873092217274368 := by decide +kernel
private theorem chunk03_origin :
    originRun 384 chunk03 ⟨22380696185, 22380696436, -754562462784918637850341729533525229568⟩ = ⟨19383040072, 19383040408, -618245385863274935692640350685400924160⟩ := by decide +kernel

private theorem chunk04_len : chunk04.length = 128 := by decide +kernel
private theorem chunk04_mass : negativeMass chunk04 = 261491610316067221264138240 := by decide +kernel
private theorem chunk04_origin :
    originRun 512 chunk04 ⟨19383040072, 19383040408, -618245385863274935692640350685400924160⟩ = ⟨17337141291, 17337141715, -550702473441157970282684974855862878208⟩ := by decide +kernel

private theorem chunk05_len : chunk05.length = 128 := by decide +kernel
private theorem chunk05_mass : negativeMass chunk05 = 212826939402744524255002624 := by decide +kernel
private theorem chunk05_origin :
    originRun 640 chunk05 ⟨17337141291, 17337141715, -550702473441157970282684974855862878208⟩ = ⟨15826829814, 15826830326, -446134799853168515953570275504996483072⟩ := by decide +kernel

private theorem chunk06_len : chunk06.length = 128 := by decide +kernel
private theorem chunk06_mass : negativeMass chunk06 = 104339551650268544673775616 := by decide +kernel
private theorem chunk06_origin :
    originRun 768 chunk06 ⟨15826829814, 15826830326, -446134799853168515953570275504996483072⟩ = ⟨14652967451, 14652968049, -402247143766221859265840603067319320576⟩ := by decide +kernel

private theorem chunk07_len : chunk07.length = 128 := by decide +kernel
private theorem chunk07_mass : negativeMass chunk07 = 100619610531834987064328192 := by decide +kernel
private theorem chunk07_origin :
    originRun 896 chunk07 ⟨14652967451, 14652968049, -402247143766221859265840603067319320576⟩ = ⟨13706715421, 13706716113, -362001854531907898676108267820938166272⟩ := by decide +kernel

private theorem chunk08_len : chunk08.length = 128 := by decide +kernel
private theorem chunk08_mass : negativeMass chunk08 = 101280238443979819344461824 := by decide +kernel
private theorem chunk08_origin :
    originRun 1024 chunk08 ⟨13706715421, 13706716113, -362001854531907898676108267820938166272⟩ = ⟨12922902804, 12922903584, -295761077759284713970480477056703397888⟩ := by decide +kernel

private theorem chunk09_len : chunk09.length = 128 := by decide +kernel
private theorem chunk09_mass : negativeMass chunk09 = 166569017504827171621830656 := by decide +kernel
private theorem chunk09_origin :
    originRun 1152 chunk09 ⟨12922902804, 12922903584, -295761077759284713970480477056703397888⟩ = ⟨12259808505, 12259809367, -266639893408720062104383970500670390272⟩ := by decide +kernel

private theorem chunk10_len : chunk10.length = 128 := by decide +kernel
private theorem chunk10_mass : negativeMass chunk10 = 86817420212813309669277696 := by decide +kernel
private theorem chunk10_origin :
    originRun 1280 chunk10 ⟨12259808505, 12259809367, -266639893408720062104383970500670390272⟩ = ⟨11689320581, 11689321536, -239575287041228337802146431537410736128⟩ := by decide +kernel

private theorem chunk11_len : chunk11.length = 128 := by decide +kernel
private theorem chunk11_mass : negativeMass chunk11 = 72933765664784792105779200 := by decide +kernel
private theorem chunk11_origin :
    originRun 1408 chunk11 ⟨11689320581, 11689321536, -239575287041228337802146431537410736128⟩ = ⟨11191713729, 11191714772, -214440938503212063792134343553474101248⟩ := by decide +kernel

private theorem chunk12_len : chunk12.length = 128 := by decide +kernel
private theorem chunk12_mass : negativeMass chunk12 = 61809361923742701438631936 := by decide +kernel
private theorem chunk12_origin :
    originRun 1536 chunk12 ⟨11191713729, 11191714772, -214440938503212063792134343553474101248⟩ = ⟨10752684333, 10752685462, -191316378602941486794396371494785515520⟩ := by decide +kernel

private theorem chunk13_len : chunk13.length = 128 := by decide +kernel
private theorem chunk13_mass : negativeMass chunk13 = 50161131122116934974832640 := by decide +kernel
private theorem chunk13_origin :
    originRun 1664 chunk13 ⟨10752684333, 10752685462, -191316378602941486794396371494785515520⟩ = ⟨10361573623, 10361574836, -170317213639681051738253641755590656000⟩ := by decide +kernel

private theorem chunk14_len : chunk14.length = 128 := by decide +kernel
private theorem chunk14_mass : negativeMass chunk14 = 45255859508911952095608832 := by decide +kernel
private theorem chunk14_origin :
    originRun 1792 chunk14 ⟨10361573623, 10361574836, -170317213639681051738253641755590656000⟩ = ⟨10010254354, 10010255645, -151215657502499776424585081412707680256⟩ := by decide +kernel

private theorem chunk15_len : chunk15.length = 128 := by decide +kernel
private theorem chunk15_mass : negativeMass chunk15 = 4637139972397181534470144 := by decide +kernel
private theorem chunk15_origin :
    originRun 1920 chunk15 ⟨10010254354, 10010255645, -151215657502499776424585081412707680256⟩ = ⟨9692406761, 9692408136, -133522314288403332890487744047779676160⟩ := by decide +kernel

private theorem chunk16_len : chunk16.length = 128 := by decide +kernel
private theorem chunk16_mass : negativeMass chunk16 = 42114108563653314002026496 := by decide +kernel
private theorem chunk16_origin :
    originRun 2048 chunk16 ⟨9692406761, 9692408136, -133522314288403332890487744047779676160⟩ = ⟨9403032543, 9403034003, -126453890572255892108446386967193698304⟩ := by decide +kernel

private theorem chunk17_len : chunk17.length = 128 := by decide +kernel
private theorem chunk17_mass : negativeMass chunk17 = 38928249336945909106212864 := by decide +kernel
private theorem chunk17_origin :
    originRun 2176 chunk17 ⟨9403032543, 9403034003, -126453890572255892108446386967193698304⟩ = ⟨9138119590, 9138121128, -117508937415689039738767811213716996096⟩ := by decide +kernel

private theorem chunk18_len : chunk18.length = 128 := by decide +kernel
private theorem chunk18_mass : negativeMass chunk18 = 33271338033334290047041536 := by decide +kernel
private theorem chunk18_origin :
    originRun 2304 chunk18 ⟨9138119590, 9138121128, -117508937415689039738767811213716996096⟩ = ⟨8894405113, 8894406734, -102568940465929120224818037272937086976⟩ := by decide +kernel

private theorem chunk19_len : chunk19.length = 128 := by decide +kernel
private theorem chunk19_mass : negativeMass chunk19 = 30563093711803173941805056 := by decide +kernel
private theorem chunk19_origin :
    originRun 2432 chunk19 ⟨8894405113, 8894406734, -102568940465929120224818037272937086976⟩ = ⟨8669204821, 8669206529, -88577810326826097405960713815779819520⟩ := by decide +kernel

private theorem chunk20_len : chunk20.length = 128 := by decide +kernel
private theorem chunk20_mass : negativeMass chunk20 = 29953110564759840768393216 := by decide +kernel
private theorem chunk20_origin :
    originRun 2560 chunk20 ⟨8669204821, 8669206529, -88577810326826097405960713815779819520⟩ = ⟨8460287389, 8460289181, -75534768579969100145710749118675140608⟩ := by decide +kernel

private theorem chunk21_len : chunk21.length = 128 := by decide +kernel
private theorem chunk21_mass : negativeMass chunk21 = 1984175168860558532280320 := by decide +kernel
private theorem chunk21_origin :
    originRun 2688 chunk21 ⟨8460287389, 8460289181, -75534768579969100145710749118675140608⟩ = ⟨8265780695, 8265782570, -71019793742724170770215469314044182528⟩ := by decide +kernel

private theorem chunk22_len : chunk22.length = 128 := by decide +kernel
private theorem chunk22_mass : negativeMass chunk22 = 25589213602197273399263232 := by decide +kernel
private theorem chunk22_origin :
    originRun 2816 chunk22 ⟨8265780695, 8265782570, -71019793742724170770215469314044182528⟩ = ⟨8084100734, 8084102701, -63398501711861126481841667095065640960⟩ := by decide +kernel

private theorem chunk23_len : chunk23.length = 128 := by decide +kernel
private theorem chunk23_mass : negativeMass chunk23 = 19528713222499363372138496 := by decide +kernel
private theorem chunk23_origin :
    originRun 2944 chunk23 ⟨8084100734, 8084102701, -63398501711861126481841667095065640960⟩ = ⟨7913897008, 7913899066, -52420261592301686129559542355458637824⟩ := by decide +kernel

private theorem chunk24_len : chunk24.length = 128 := by decide +kernel
private theorem chunk24_mass : negativeMass chunk24 = 5456947959215170537914368 := by decide +kernel
private theorem chunk24_origin :
    originRun 3072 chunk24 ⟨7913897008, 7913899066, -52420261592301686129559542355458637824⟩ = ⟨7754010065, 7754012206, -42625013042541676496062859682150727680⟩ := by decide +kernel

private theorem chunk25_len : chunk25.length = 128 := by decide +kernel
private theorem chunk25_mass : negativeMass chunk25 = 8305154429523763436453888 := by decide +kernel
private theorem chunk25_origin :
    originRun 3200 chunk25 ⟨7754010065, 7754012206, -42625013042541676496062859682150727680⟩ = ⟨7603438079, 7603440303, -42554863789342144465777500172390612992⟩ := by decide +kernel

private theorem chunk26_len : chunk26.length = 128 := by decide +kernel
private theorem chunk26_mass : negativeMass chunk26 = 7947544496481613624901632 := by decide +kernel
private theorem chunk26_origin :
    originRun 3328 chunk26 ⟨7603438079, 7603440303, -42554863789342144465777500172390612992⟩ = ⟨7461310335, 7461312637, -34084849313527035053143089528266407936⟩ := by decide +kernel

private theorem chunk27_len : chunk27.length = 128 := by decide +kernel
private theorem chunk27_mass : negativeMass chunk27 = 8018179787725186469986304 := by decide +kernel
private theorem chunk27_origin :
    originRun 3456 chunk27 ⟨7461310335, 7461312637, -34084849313527035053143089528266407936⟩ = ⟨7326865967, 7326868355, -26756991260035491936885362506441277440⟩ := by decide +kernel

private theorem chunk28_len : chunk28.length = 128 := by decide +kernel
private theorem chunk28_mass : negativeMass chunk28 = 0 := by decide +kernel
private theorem chunk28_origin :
    originRun 3584 chunk28 ⟨7326865967, 7326868355, -26756991260035491936885362506441277440⟩ = ⟨7199436755, 7199439228, -26627385802835324800817238302588518400⟩ := by decide +kernel

private theorem chunk29_len : chunk29.length = 128 := by decide +kernel
private theorem chunk29_mass : negativeMass chunk29 = 6608840491993687495016448 := by decide +kernel
private theorem chunk29_origin :
    originRun 3712 chunk29 ⟨7199436755, 7199439228, -26627385802835324800817238302588518400⟩ = ⟨7078433108, 7078435669, -20388282867767768688168486531804282880⟩ := by decide +kernel

private theorem chunk30_len : chunk30.length = 128 := by decide +kernel
private theorem chunk30_mass : negativeMass chunk30 = 569273293236987865595904 := by decide +kernel
private theorem chunk30_origin :
    originRun 3840 chunk30 ⟨7078433108, 7078435669, -20388282867767768688168486531804282880⟩ = ⟨6963332562, 6963335200, -15015001648036224622283685566160683008⟩ := by decide +kernel

private theorem chunk31_len : chunk31.length = 128 := by decide +kernel
private theorem chunk31_mass : negativeMass chunk31 = 4424945705978503393968128 := by decide +kernel
private theorem chunk31_origin :
    originRun 3968 chunk31 ⟨6963332562, 6963335200, -15015001648036224622283685566160683008⟩ = ⟨6853670237, 6853672957, -14983426728335755929652337566017503232⟩ := by decide +kernel

private theorem chunk32_len : chunk32.length = 128 := by decide +kernel
private theorem chunk32_mass : negativeMass chunk32 = 3514432758241787386003456 := by decide +kernel
private theorem chunk32_origin :
    originRun 4096 chunk32 ⟨6853670237, 6853672957, -14983426728335755929652337566017503232⟩ = ⟨6749030959, 6749033769, -10481337171887300544392153119416500224⟩ := by decide +kernel

private theorem chunk33_len : chunk33.length = 128 := by decide +kernel
private theorem chunk33_mass : negativeMass chunk33 = 0 := by decide +kernel
private theorem chunk33_origin :
    originRun 4224 chunk33 ⟨6749030959, 6749033769, -10481337171887300544392153119416500224⟩ = ⟨6649042616, 6649045512, -8714072446316186042967567265588953088⟩ := by decide +kernel

private theorem chunk34_len : chunk34.length = 128 := by decide +kernel
private theorem chunk34_mass : negativeMass chunk34 = 1655719444580259892035584 := by decide +kernel
private theorem chunk34_origin :
    originRun 4352 chunk34 ⟨6649042616, 6649045512, -8714072446316186042967567265588953088⟩ = ⟨6553370572, 6553373559, -6753639047635845301496093827353657344⟩ := by decide +kernel

private theorem chunk35_len : chunk35.length = 128 := by decide +kernel
private theorem chunk35_mass : negativeMass chunk35 = 1326789827476084823687168 := by decide +kernel
private theorem chunk35_origin :
    originRun 4480 chunk35 ⟨6553370572, 6553373559, -6753639047635845301496093827353657344⟩ = ⟨6461712967, 6461716039, -3940928796698225793215252446161518592⟩ := by decide +kernel

private theorem chunk36_len : chunk36.length = 3 := by decide +kernel
private theorem chunk36_mass : negativeMass chunk36 = 232247769140506243629056 := by decide +kernel
private theorem chunk36_origin :
    originRun 4608 chunk36 ⟨6461712967, 6461716039, -3940928796698225793215252446161518592⟩ = ⟨6459610627, 6459613702, -3942429407055818633183229900472041472⟩ := by decide +kernel

private theorem chunk37_len : chunk37.length = 128 := by decide +kernel
private theorem chunk37_sign : chunk37.all (fun w => decide (0 ≤ w)) = true := by decide +kernel
private theorem chunk37_origin :
    originRun 4611 chunk37 ⟨6459610627, 6459613702, -3942429407055818633183229900472041472⟩ = ⟨6371778960, 6371782125, -3883116156683402879355094912817938432⟩ := by decide +kernel

private theorem chunk38_len : chunk38.length = 128 := by decide +kernel
private theorem chunk38_sign : chunk38.all (fun w => decide (0 ≤ w)) = true := by decide +kernel
private theorem chunk38_origin :
    originRun 4739 chunk38 ⟨6371778960, 6371782125, -3883116156683402879355094912817938432⟩ = ⟨6287435294, 6287438547, -1949734500549875417148820749080576000⟩ := by decide +kernel

private theorem chunk39_len : chunk39.length = 128 := by decide +kernel
private theorem chunk39_sign : chunk39.all (fun w => decide (0 ≤ w)) = true := by decide +kernel
private theorem chunk39_origin :
    originRun 4867 chunk39 ⟨6287435294, 6287438547, -1949734500549875417148820749080576000⟩ = ⟨6206354720, 6206358060, -1810521711609500137095863242310008832⟩ := by decide +kernel

private theorem chunk40_len : chunk40.length = 128 := by decide +kernel
private theorem chunk40_sign : chunk40.all (fun w => decide (0 ≤ w)) = true := by decide +kernel
private theorem chunk40_origin :
    originRun 4995 chunk40 ⟨6206354720, 6206358060, -1810521711609500137095863242310008832⟩ = ⟨6128332118, 6128335544, -900854706613574363681841624818368512⟩ := by decide +kernel

private theorem chunk41_len : chunk41.length = 128 := by decide +kernel
private theorem chunk41_sign : chunk41.all (fun w => decide (0 ≤ w)) = true := by decide +kernel
private theorem chunk41_origin :
    originRun 5123 chunk41 ⟨6128332118, 6128335544, -900854706613574363681841624818368512⟩ = ⟨6053179976, 6053183488, -847669286167504538386455290272530432⟩ := by decide +kernel

private theorem chunk42_len : chunk42.length = 128 := by decide +kernel
private theorem chunk42_sign : chunk42.all (fun w => decide (0 ≤ w)) = true := by decide +kernel
private theorem chunk42_origin :
    originRun 5251 chunk42 ⟨6053179976, 6053183488, -847669286167504538386455290272530432⟩ = ⟨5980726493, 5980730092, -796019543310466765367377432377278464⟩ := by decide +kernel

private theorem chunk43_len : chunk43.length = 128 := by decide +kernel
private theorem chunk43_sign : chunk43.all (fun w => decide (0 ≤ w)) = true := by decide +kernel
private theorem chunk43_origin :
    originRun 5379 chunk43 ⟨5980726493, 5980730092, -796019543310466765367377432377278464⟩ = ⟨5910813935, 5910817621, -745412266430491613021692377648840704⟩ := by decide +kernel

private theorem chunk44_len : chunk44.length = 128 := by decide +kernel
private theorem chunk44_sign : chunk44.all (fun w => decide (0 ≤ w)) = true := by decide +kernel
private theorem chunk44_origin :
    originRun 5507 chunk44 ⟨5910813935, 5910817621, -745412266430491613021692377648840704⟩ = ⟨5843297174, 5843300942, -695943642217768295901767142111690752⟩ := by decide +kernel

private theorem chunk45_len : chunk45.length = 128 := by decide +kernel
private theorem chunk45_sign : chunk45.all (fun w => decide (0 ≤ w)) = true := by decide +kernel
private theorem chunk45_origin :
    originRun 5635 chunk45 ⟨5843297174, 5843300942, -695943642217768295901767142111690752⟩ = ⟨5778042431, 5778046274, -647707080991224795560266532486103040⟩ := by decide +kernel

private theorem chunk46_len : chunk46.length = 128 := by decide +kernel
private theorem chunk46_sign : chunk46.all (fun w => decide (0 ≤ w)) = true := by decide +kernel
private theorem chunk46_origin :
    originRun 5763 chunk46 ⟨5778042431, 5778046274, -647707080991224795560266532486103040⟩ = ⟨5714926153, 5714930077, -600783937656606183645479942472056832⟩ := by decide +kernel

private theorem chunk47_len : chunk47.length = 128 := by decide +kernel
private theorem chunk47_sign : chunk47.all (fun w => decide (0 ≤ w)) = true := by decide +kernel
private theorem chunk47_origin :
    originRun 5891 chunk47 ⟨5714926153, 5714930077, -600783937656606183645479942472056832⟩ = ⟨5653834036, 5653838043, -555243743705888047582681908053262336⟩ := by decide +kernel

private theorem chunk48_len : chunk48.length = 128 := by decide +kernel
private theorem chunk48_sign : chunk48.all (fun w => decide (0 ≤ w)) = true := by decide +kernel
private theorem chunk48_origin :
    originRun 6019 chunk48 ⟨5653834036, 5653838043, -555243743705888047582681908053262336⟩ = ⟨5594660144, 5594664242, -511144540424833253640990661850939392⟩ := by decide +kernel

private theorem chunk49_len : chunk49.length = 128 := by decide +kernel
private theorem chunk49_sign : chunk49.all (fun w => decide (0 ≤ w)) = true := by decide +kernel
private theorem chunk49_origin :
    originRun 6147 chunk49 ⟨5594660144, 5594664242, -511144540424833253640990661850939392⟩ = ⟨5537306156, 5537310345, -468533299052352385305011935337234432⟩ := by decide +kernel

private theorem chunk50_len : chunk50.length = 128 := by decide +kernel
private theorem chunk50_sign : chunk50.all (fun w => decide (0 ≤ w)) = true := by decide +kernel
private theorem chunk50_origin :
    originRun 6275 chunk50 ⟨5537306156, 5537310345, -468533299052352385305011935337234432⟩ = ⟨5481680656, 5481684936, -427446413422427743748611362570092544⟩ := by decide +kernel

private theorem chunk51_len : chunk51.length = 128 := by decide +kernel
private theorem chunk51_sign : chunk51.all (fun w => decide (0 ≤ w)) = true := by decide +kernel
private theorem chunk51_origin :
    originRun 6403 chunk51 ⟨5481680656, 5481684936, -427446413422427743748611362570092544⟩ = ⟨5427698542, 5427702906, -387910251941374826997285233407803392⟩ := by decide +kernel

private theorem chunk52_len : chunk52.length = 128 := by decide +kernel
private theorem chunk52_sign : chunk52.all (fun w => decide (0 ≤ w)) = true := by decide +kernel
private theorem chunk52_origin :
    originRun 6531 chunk52 ⟨5427698542, 5427702906, -387910251941374826997285233407803392⟩ = ⟨5375280441, 5375284897, -349941755935697691505149780219904000⟩ := by decide +kernel

private theorem chunk53_len : chunk53.length = 128 := by decide +kernel
private theorem chunk53_sign : chunk53.all (fun w => decide (0 ≤ w)) = true := by decide +kernel
private theorem chunk53_origin :
    originRun 6659 chunk53 ⟨5375280441, 5375284897, -349941755935697691505149780219904000⟩ = ⟨5324352273, 5324356822, -313549072463041137933474810343178240⟩ := by decide +kernel

private theorem chunk54_len : chunk54.length = 128 := by decide +kernel
private theorem chunk54_sign : chunk54.all (fun w => decide (0 ≤ w)) = true := by decide +kernel
private theorem chunk54_origin :
    originRun 6787 chunk54 ⟨5324352273, 5324356822, -313549072463041137933474810343178240⟩ = ⟨5274844763, 5274849394, -278732210718972715574348560831594496⟩ := by decide +kernel

private theorem chunk55_len : chunk55.length = 128 := by decide +kernel
private theorem chunk55_sign : chunk55.all (fun w => decide (0 ≤ w)) = true := by decide +kernel
private theorem chunk55_origin :
    originRun 6915 chunk55 ⟨5274844763, 5274849394, -278732210718972715574348560831594496⟩ = ⟨5226693061, 5226697785, -245483711803899867120083155404177408⟩ := by decide +kernel

private theorem chunk56_len : chunk56.length = 128 := by decide +kernel
private theorem chunk56_sign : chunk56.all (fun w => decide (0 ≤ w)) = true := by decide +kernel
private theorem chunk56_origin :
    originRun 7043 chunk56 ⟨5226693061, 5226697785, -245483711803899867120083155404177408⟩ = ⟨5179836401, 5179841208, -213789323097205965933621326232928256⟩ := by decide +kernel

private theorem chunk57_len : chunk57.length = 128 := by decide +kernel
private theorem chunk57_sign : chunk57.all (fun w => decide (0 ≤ w)) = true := by decide +kernel
private theorem chunk57_origin :
    originRun 7171 chunk57 ⟨5179836401, 5179841208, -213789323097205965933621326232928256⟩ = ⟨5134217746, 5134222639, -183628668989147866779134421390573568⟩ := by decide +kernel

private theorem chunk58_len : chunk58.length = 128 := by decide +kernel
private theorem chunk58_sign : chunk58.all (fun w => decide (0 ≤ w)) = true := by decide +kernel
private theorem chunk58_origin :
    originRun 7299 chunk58 ⟨5134217746, 5134222639, -183628668989147866779134421390573568⟩ = ⟨5089783531, 5089788508, -154975911170219234928583132333195264⟩ := by decide +kernel

private theorem chunk59_len : chunk59.length = 128 := by decide +kernel
private theorem chunk59_sign : chunk59.all (fun w => decide (0 ≤ w)) = true := by decide +kernel
private theorem chunk59_origin :
    originRun 7427 chunk59 ⟨5089783531, 5089788508, -154975911170219234928583132333195264⟩ = ⟨5046483361, 5046488430, -127800392347991244733108404980793344⟩ := by decide +kernel

private theorem chunk60_len : chunk60.length = 128 := by decide +kernel
private theorem chunk60_sign : chunk60.all (fun w => decide (0 ≤ w)) = true := by decide +kernel
private theorem chunk60_origin :
    originRun 7555 chunk60 ⟨5046483361, 5046488430, -127800392347991244733108404980793344⟩ = ⟨5004269816, 5004274971, -102067258306610616507720334725332992⟩ := by decide +kernel

private theorem chunk61_len : chunk61.length = 128 := by decide +kernel
private theorem chunk61_sign : chunk61.all (fun w => decide (0 ≤ w)) = true := by decide +kernel
private theorem chunk61_origin :
    originRun 7683 chunk61 ⟨5004269816, 5004274971, -102067258306610616507720334725332992⟩ = ⟨4963098194, 4963103433, -77738054211467046511826888379056128⟩ := by decide +kernel

private theorem chunk62_len : chunk62.length = 128 := by decide +kernel
private theorem chunk62_sign : chunk62.all (fun w => decide (0 ≤ w)) = true := by decide +kernel
private theorem chunk62_origin :
    originRun 7811 chunk62 ⟨4963098194, 4963103433, -77738054211467046511826888379056128⟩ = ⟨4922926324, 4922931643, -54771291633284180933220377618530304⟩ := by decide +kernel

private theorem chunk63_len : chunk63.length = 128 := by decide +kernel
private theorem chunk63_sign : chunk63.all (fun w => decide (0 ≤ w)) = true := by decide +kernel
private theorem chunk63_origin :
    originRun 7939 chunk63 ⟨4922926324, 4922931643, -54771291633284180933220377618530304⟩ = ⟨4883714381, 4883719791, -33122983773976059107658078909874176⟩ := by decide +kernel

private theorem chunk64_len : chunk64.length = 125 := by decide +kernel
private theorem chunk64_sign : chunk64.all (fun w => decide (0 ≤ w)) = true := by decide +kernel
private theorem chunk64_origin :
    originRun 8067 chunk64 ⟨4883714381, 4883719791, -33122983773976059107658078909874176⟩ = ⟨4846311873, 4846317374, -13210499194714300723991473799544832⟩ := by decide +kernel

private theorem lead_origin :
    originRun 8192 [lead] ⟨4846311873, 4846317374, -13210499194714300723991473799544832⟩ = ⟨4846016109, 4846021610, -13055973648815480223170437445304320⟩ := by decide +kernel

private theorem low_length : lowWeights.length = 4611 := by
  norm_num [lowWeights, List.length_append,
    chunk00_len, chunk01_len, chunk02_len, chunk03_len, chunk04_len, chunk05_len, chunk06_len, chunk07_len, chunk08_len, chunk09_len,
    chunk10_len, chunk11_len, chunk12_len, chunk13_len, chunk14_len, chunk15_len, chunk16_len, chunk17_len, chunk18_len, chunk19_len,
    chunk20_len, chunk21_len, chunk22_len, chunk23_len, chunk24_len, chunk25_len, chunk26_len, chunk27_len, chunk28_len, chunk29_len,
    chunk30_len, chunk31_len, chunk32_len, chunk33_len, chunk34_len, chunk35_len, chunk36_len]

private theorem high_length : highWeights.length = 3581 := by
  norm_num [highWeights, List.length_append,
    chunk37_len, chunk38_len, chunk39_len, chunk40_len, chunk41_len, chunk42_len, chunk43_len, chunk44_len, chunk45_len, chunk46_len,
    chunk47_len, chunk48_len, chunk49_len, chunk50_len, chunk51_len, chunk52_len, chunk53_len, chunk54_len, chunk55_len, chunk56_len,
    chunk57_len, chunk58_len, chunk59_len, chunk60_len, chunk61_len, chunk62_len, chunk63_len, chunk64_len]

private theorem low_mass : negativeMass lowWeights ≤ 2^96 := by
  norm_num [lowWeights, negativeMass_append,
    chunk00_mass, chunk01_mass, chunk02_mass, chunk03_mass, chunk04_mass, chunk05_mass, chunk06_mass, chunk07_mass, chunk08_mass, chunk09_mass,
    chunk10_mass, chunk11_mass, chunk12_mass, chunk13_mass, chunk14_mass, chunk15_mass, chunk16_mass, chunk17_mass, chunk18_mass, chunk19_mass,
    chunk20_mass, chunk21_mass, chunk22_mass, chunk23_mass, chunk24_mass, chunk25_mass, chunk26_mass, chunk27_mass, chunk28_mass, chunk29_mass,
    chunk30_mass, chunk31_mass, chunk32_mass, chunk33_mass, chunk34_mass, chunk35_mass, chunk36_mass]

private theorem high_sign : highWeights.all (fun w => decide (0 ≤ w)) = true := by
  simp only [highWeights, List.all_append, Bool.and_self,
    chunk37_sign, chunk38_sign, chunk39_sign, chunk40_sign, chunk41_sign, chunk42_sign, chunk43_sign, chunk44_sign, chunk45_sign, chunk46_sign,
    chunk47_sign, chunk48_sign, chunk49_sign, chunk50_sign, chunk51_sign, chunk52_sign, chunk53_sign, chunk54_sign, chunk55_sign, chunk56_sign,
    chunk57_sign, chunk58_sign, chunk59_sign, chunk60_sign, chunk61_sign, chunk62_sign, chunk63_sign, chunk64_sign]

private theorem origin_result :
    originRun 0 weights ⟨originScale,originScale,0⟩ = ⟨4846016109, 4846021610, -13055973648815480223170437445304320⟩ := by
  change originRun 0 weights ⟨1099511627776, 1099511627776, 0⟩ = ⟨4846016109, 4846021610, -13055973648815480223170437445304320⟩
  simp only [weights, lowWeights, highWeights, originRun_append, List.length_append,
    Nat.reduceAdd, lead_origin,
    chunk00_len, chunk01_len, chunk02_len, chunk03_len, chunk04_len, chunk05_len, chunk06_len, chunk07_len, chunk08_len, chunk09_len,
    chunk10_len, chunk11_len, chunk12_len, chunk13_len, chunk14_len, chunk15_len, chunk16_len, chunk17_len, chunk18_len, chunk19_len,
    chunk20_len, chunk21_len, chunk22_len, chunk23_len, chunk24_len, chunk25_len, chunk26_len, chunk27_len, chunk28_len, chunk29_len,
    chunk30_len, chunk31_len, chunk32_len, chunk33_len, chunk34_len, chunk35_len, chunk36_len, chunk37_len, chunk38_len, chunk39_len,
    chunk40_len, chunk41_len, chunk42_len, chunk43_len, chunk44_len, chunk45_len, chunk46_len, chunk47_len, chunk48_len, chunk49_len,
    chunk50_len, chunk51_len, chunk52_len, chunk53_len, chunk54_len, chunk55_len, chunk56_len, chunk57_len, chunk58_len, chunk59_len,
    chunk60_len, chunk61_len, chunk62_len, chunk63_len, chunk64_len, chunk00_origin, chunk01_origin, chunk02_origin, chunk03_origin, chunk04_origin,
    chunk05_origin, chunk06_origin, chunk07_origin, chunk08_origin, chunk09_origin, chunk10_origin, chunk11_origin, chunk12_origin, chunk13_origin, chunk14_origin,
    chunk15_origin, chunk16_origin, chunk17_origin, chunk18_origin, chunk19_origin, chunk20_origin, chunk21_origin, chunk22_origin, chunk23_origin, chunk24_origin,
    chunk25_origin, chunk26_origin, chunk27_origin, chunk28_origin, chunk29_origin, chunk30_origin, chunk31_origin, chunk32_origin, chunk33_origin, chunk34_origin,
    chunk35_origin, chunk36_origin, chunk37_origin, chunk38_origin, chunk39_origin, chunk40_origin, chunk41_origin, chunk42_origin, chunk43_origin, chunk44_origin,
    chunk45_origin, chunk46_origin, chunk47_origin, chunk48_origin, chunk49_origin, chunk50_origin, chunk51_origin, chunk52_origin, chunk53_origin, chunk54_origin,
    chunk55_origin, chunk56_origin, chunk57_origin, chunk58_origin, chunk59_origin, chunk60_origin, chunk61_origin, chunk62_origin, chunk63_origin, chunk64_origin]

/-- The exact rational polynomial whose coefficients are the dyadic source payload. -/
noncomputable def projected16384 : ℚ[X] := witness denominator weights

theorem projected16384_far (t : ℝ) (ht : 65536 ≤ t) :
    0 < projected16384.eval₂ (algebraMap ℚ ℝ) t :=
  far_positive denominator lowWeights highWeights lead (by decide +kernel)
    low_length high_length high_sign low_mass (by decide +kernel) t ht

theorem projected16384_origin_bound :
    projected16384.eval₂ (algebraMap ℚ ℝ) 0 ≤
      (-13055973648815480223170437445304320 : ℝ) / ((2 : ℝ)^90 * (2 : ℝ)^40) := by
  have h := origin_le denominator originScale weights (by decide +kernel) (by decide +kernel)
  rw [origin_result] at h
  norm_num [projected16384, denominator, originScale] at h ⊢
  exact h

theorem projected16384_origin : projected16384.eval₂ (algebraMap ℚ ℝ) 0 < 0 := by
  apply origin_negative denominator originScale weights (by decide +kernel) (by decide +kernel)
  rw [origin_result]
  decide +kernel

theorem projected16384_self_fourier :
    𝓕 (radialGaussian projected16384) = radialGaussian projected16384 :=
  witness_fourier denominator weights

theorem projected16384_gaussian_origin : (radialGaussian projected16384 0).re < 0 := by
  simpa [radialGaussian_apply] using projected16384_origin

theorem projected16384_gaussian_far (x : ℝ) (hx : 65536 ≤ 2 * Real.pi * x^2) :
    0 < (radialGaussian projected16384 x).re := by
  rw [radialGaussian_apply, Complex.ofReal_re]
  exact mul_pos (projected16384_far _ hx) (Real.exp_pos _)

end NextProof.Exterior

#print axioms NextProof.Exterior.projected16384_far
#print axioms NextProof.Exterior.projected16384_origin
#print axioms NextProof.Exterior.projected16384_self_fourier
