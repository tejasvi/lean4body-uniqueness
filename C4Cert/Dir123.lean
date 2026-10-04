module

public import C4Check

public section

/-! Cells `3763 ≤ n < 3813` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir123

theorem k3763_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3763) 3).1
      26241503046244526779949999272576792882583914895727194526761350916181719763067858191273702698098162276802265546188019627104640501998990218133976147246140).isSome = true := by
  decide +kernel

theorem k3763_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 3763) 3).2
      22219949323858948470010557982700333473634652776691889318650982480774028671288897632889651950345121503540534243740230340576547748924).isSome = true := by
  decide +kernel

theorem k3764_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3764) 3).1
      22213113457707188325299748872935205181617843625887618301641391557841374831059682149108993549462173733355815100882567963620155374652).isSome = true := by
  decide +kernel

theorem k3764_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 3764) 3).2
      75243270254682088307610447981395019365184347198769424079077102332459945759232978446341091422338922763428545340).isSome = true := by
  decide +kernel

theorem k3765_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3765) 1).1
      3982016083705553783828847635100978184327430092523092843569305168770129664635035440692284).isSome = true := by
  decide +kernel

theorem k3765_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 3765) 1).2
      3983138331370892358055785647711817464675970836095341059541768359179369257382372282514492).isSome = true := by
  decide +kernel

theorem k3766_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3766) 3).1
      293753636972531675764650338107368162450478315283835227368112078756585959612049108861597037802395926298084156).isSome = true := by
  decide +kernel

theorem k3766_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 3766) 3).2
      3372441273603315324320509629930254570419758682480923490850871952188).isSome = true := by
  decide +kernel

theorem k3767_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3767) 1).1
      842757008983415807430430166762379592794056045261227426323073724988).isSome = true := by
  decide +kernel

theorem k3767_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 3767) 1).2
      210701713469756256568727838901845613383230471210994578979098033212).isSome = true := by
  decide +kernel

theorem c5 : allCells dirCell 3768 3769 [
    18351064514282646356126638649124819490288818611479225950467727893717789658076361061472168789454161186282929] = true := by
  decide +kernel

theorem c6 : allCells dirCell 3769 3784 [
    51424473036826913059784750096324690392464482850139755209758353, 147558357906936522228, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0] = true := by
  decide +kernel

theorem c7 : allCells dirCell 3784 3785 [
    1377109179971359253057531522983141376857118043990841802599567142985387036642413070577363278707723810175562750129851847622719819] = true := by
  decide +kernel

theorem k3785_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3785) 3).1
      3944976339894998393923513504644752641267645959162133627583888108326872640874536097586).isSome = true := by
  decide +kernel

theorem k3785_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 3785) 3).2
      74276909306533685996534581723034872656048659973934368325777326785052834083083255627596260402493400618061618).isSome = true := by
  decide +kernel

theorem k3786_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3786) 2).1 3).1
      3326161269782265414073953238955716678933195847020537351027151820).isSome = true := by
  decide +kernel

theorem k3786_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3786) 2).1 3).2
      980559442874312124238946397870620289521071598189851039304766872584486527746629425868).isSome = true := by
  decide +kernel

theorem k3786_2 : (checkBoxH dirMode depth (splitBox (dirCellBox 3786) 2).2
      5466740258584134423187295063794713041408088618950006120711960583262067171691131319816879351553300572096566606610026092422355763).isSome = true := by
  decide +kernel

theorem k3787_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3787) 2).1 3).1
      212322320883938275481389059894295545471172005880366454928320219852).isSome = true := by
  decide +kernel

theorem k3787_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3787) 2).1 3).2
      848284021777847864164328924082448838514925619558863467880707466188).isSome = true := by
  decide +kernel

theorem k3787_2 : (checkBoxH dirMode depth (splitBox (dirCellBox 3787) 2).2
      5583604425780927694255967160351758513658665315782434158106651471114504221833338105405144623381414822517007017197978814033446816563).isSome = true := by
  decide +kernel

theorem k3788_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3788) 2).1 3).1
      211857494242507699889265348330517245145890216295069399069014606796).isSome = true := by
  decide +kernel

theorem k3788_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3788) 2).1 3).2
      211675670536649370039235232763404908200074487361885857066008429516).isSome = true := by
  decide +kernel

theorem k3788_2 : (checkBoxH dirMode depth (splitBox (dirCellBox 3788) 2).2
      309492613159965718208716059646138670616153866331004125807666270732223965291869293494104128687142982623956140232497).isSome = true := by
  decide +kernel

theorem k3789_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3789) 2).1 1).1
      13538940807035674573713677961831733302119033190998316045385411476540).isSome = true := by
  decide +kernel

theorem k3789_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3789) 2).1 1).2
      845762923514707328890862038590475386632111237016927942290527994828).isSome = true := by
  decide +kernel

theorem k3789_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3789) 2).2 1).1
      845813985383467011751227284519319880577122563219040715111399367628).isSome = true := by
  decide +kernel

theorem k3789_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3789) 2).2 1).2
      211455546506140302422654624543048558066850284860119453924790354892).isSome = true := by
  decide +kernel

theorem k3790_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3790) 2).1
      356063358391087978611002422563947829571639575626837524651134712773842878294025328059245723120307341566418354525806835242486659759164).isSome = true := by
  decide +kernel

theorem k3790_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 3790) 2).2
      5561062259727055140417246463163110141100199834014194175861060241027320849271673717879514300532949603680738233833346602638981151804).isSome = true := by
  decide +kernel

theorem k3791_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3791) 2).1
      1204815948332096366396823715423797053420307252210152839657468838779798750937047045490575666194292347709634165820).isSome = true := by
  decide +kernel

theorem k3791_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 3791) 2).2
      63786198929018973243124787311699113423598853077017381405154999433941271004401348526259260).isSome = true := by
  decide +kernel

theorem k3792_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3792) 1).1
      15936475990934162145998773885784135893452281227397932449616909369517882098898577911431996).isSome = true := by
  decide +kernel

theorem k3792_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 3792) 1).2
      3984178372211625191436980134611005811732646563410432373131053453638774682418603861261372).isSome = true := by
  decide +kernel

theorem k3793_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3793) 3).1
      3983727186946567551866270439649345368982230907928873166118881869214163115015318357656380).isSome = true := by
  decide +kernel

theorem k3793_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 3793) 3).2
      995491326871417761020990943277808922511884975839763674125543491261866497279916777390908).isSome = true := by
  decide +kernel

theorem k3794_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3794) 1).1
      52686769668128173097010960005748345539819299364161783438483255868).isSome = true := by
  decide +kernel

theorem k3794_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 3794) 1).2
      843027049507909338735588931334797380610061317888915999558224036668).isSome = true := by
  decide +kernel

theorem c18 : allCells dirCell 3795 3796 [
    5547430567784594815836019844481709020773327055976996849457708003776944366942190737328452281011822606037337782555783257207399237873] = true := by
  decide +kernel

theorem c19 : allCells dirCell 3796 3797 [
    21158016497049509262339922157871494065487589381069851652566048531756374643415166917141829949167093994535352870312088893611441] = true := by
  decide +kernel

theorem c20 : allCells dirCell 3797 3813 [
    51424384822561097813866475983103667384384233300522464894240401, 147557636283735752292, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2836659762559348349041050731321480997351715] = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 3763 3813 :=
  (Cover.one (box := dirCellBox) (n := 3763)
      (.split 3 (.leaf _ k3763_0) (.leaf _ k3763_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 3764)
      (.split 3 (.leaf _ k3764_0) (.leaf _ k3764_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 3765)
      (.split 1 (.leaf _ k3765_0) (.leaf _ k3765_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 3766)
      (.split 3 (.leaf _ k3766_0) (.leaf _ k3766_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 3767)
      (.split 1 (.leaf _ k3767_0) (.leaf _ k3767_1))).trans <|
  (Cover.dir c5).trans <|
  (Cover.dir c6).trans <|
  (Cover.dir c7).trans <|
  (Cover.one (box := dirCellBox) (n := 3785)
      (.split 3 (.leaf _ k3785_0) (.leaf _ k3785_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 3786)
      (.split 2 (.split 3 (.leaf _ k3786_0) (.leaf _ k3786_1)) (.leaf _ k3786_2))).trans <|
  (Cover.one (box := dirCellBox) (n := 3787)
      (.split 2 (.split 3 (.leaf _ k3787_0) (.leaf _ k3787_1)) (.leaf _ k3787_2))).trans <|
  (Cover.one (box := dirCellBox) (n := 3788)
      (.split 2 (.split 3 (.leaf _ k3788_0) (.leaf _ k3788_1)) (.leaf _ k3788_2))).trans <|
  (Cover.one (box := dirCellBox) (n := 3789)
      (.split 2 (.split 1 (.leaf _ k3789_0) (.leaf _ k3789_1)) (.split 1 (.leaf _ k3789_2) (.leaf _ k3789_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 3790)
      (.split 2 (.leaf _ k3790_0) (.leaf _ k3790_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 3791)
      (.split 2 (.leaf _ k3791_0) (.leaf _ k3791_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 3792)
      (.split 1 (.leaf _ k3792_0) (.leaf _ k3792_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 3793)
      (.split 3 (.leaf _ k3793_0) (.leaf _ k3793_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 3794)
      (.split 1 (.leaf _ k3794_0) (.leaf _ k3794_1))).trans <|
  (Cover.dir c18).trans <|
  (Cover.dir c19).trans <|
  (Cover.dir c20)

end C4.Cert.Dir123
