module

public import C4Check

public section

/-! Cells `2051 ≤ n < 2077` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir026

theorem k2051_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2051) 3).1 2).1 1).1
      5573733457984375868471545510594828167368853821052647227359603120893492754786993344441777315879777515027996533672680955039539211059).isSome = true := by
  decide +kernel

theorem k2051_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2051) 3).1 2).1 1).2 3).1
      52955439552797984386432197871104086458439992259566389170582975180).isSome = true := by
  decide +kernel

theorem k2051_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2051) 3).1 2).1 1).2 3).2
      52926565620408124806983403216279963601416053964157077982680576716).isSome = true := by
  decide +kernel

theorem k2051_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2051) 3).1 2).2 1).1
      1181735493637468614991514197014186689061023476529280399248541188442825684867493365562165123191962063986875187).isSome = true := by
  decide +kernel

theorem k2051_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2051) 3).1 2).2 1).2 3).1
      244371749823112773278657271387832995254780087641867691245812952816612114398753191628).isSome = true := by
  decide +kernel

theorem k2051_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2051) 3).1 2).2 1).2 3).2
      52945690576323477880430797138479575452327176203348490172105214668).isSome = true := by
  decide +kernel

theorem k2051_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2051) 3).2 2).1 1).1
      1179014781755561623365342746374659013650978662946538261649234159932291372465934545166434485073899837919195955).isSome = true := by
  decide +kernel

theorem k2051_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2051) 3).2 2).1 1).2
      1179021499896239723304744554221771143930068261569424777018841104621940400958386269672142851573477832306062131).isSome = true := by
  decide +kernel

theorem k2051_8 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2051) 3).2 2).2 1).1
      3999859542749357869579206844090039442930342326336216838687926212835455912398618043468595).isSome = true := by
  decide +kernel

theorem k2051_9 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2051) 3).2 2).2 1).2
      5446594299015451259319738576639957605401727842590275933917436846782413686521324705489797899194429840830339270013028099319384780).isSome = true := by
  decide +kernel

theorem k2052_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2052) 3).1 2).1 1).1
      3995609589567944371897074176544647215527806554190215912186749863032366260300262299513651).isSome = true := by
  decide +kernel

theorem k2052_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2052) 3).1 2).1 1).2
      997872042328446032820312513706095502748011523378036098420882979072440237176417901441843).isSome = true := by
  decide +kernel

theorem k2052_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2052) 3).1 2).2 1).1
      15969837933533705071266821142934876999243234454947311587719186275878228721449154079208243).isSome = true := by
  decide +kernel

theorem k2052_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2052) 3).1 2).2 1).2
      3996696458584763820175667105140835883212993850395618817223793218360784281855414647501619).isSome = true := by
  decide +kernel

theorem k2052_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2052) 3).2 2).1 1).1
      3900090001463644775866984947908526657048686926723952857676236596404800014418454115020).isSome = true := by
  decide +kernel

theorem k2052_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2052) 3).2 2).1 1).2
      15584515689402544468839015880586803002356486843827860573977839848380573477799477103308).isSome = true := by
  decide +kernel

theorem k2052_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2052) 3).2 2).2 1).1
      845782628903754561125019502465490294953147987048664203390631460044).isSome = true := by
  decide +kernel

theorem k2052_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2052) 3).2 2).2 1).2
      3897291858490844491719940297593698151452976448449441763432413041596178572394620121804).isSome = true := by
  decide +kernel

theorem k2053_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2053) 3).1 2).1 1).1
      3893968710561170906481672839376133500546648919008472031618331898800351871778445193932).isSome = true := by
  decide +kernel

theorem k2053_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2053) 3).1 2).1 1).2
      824688467813084983263116532333527950886585818748273968025007820).isSome = true := by
  decide +kernel

theorem k2053_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2053) 3).1 2).2 1).1
      973742424699951835776468171234486673061115262194489836866913357337751014807055465676).isSome = true := by
  decide +kernel

theorem k2053_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2053) 3).1 2).2 1).2
      52785240769688155420111321676454860801387970930728847881311482572).isSome = true := by
  decide +kernel

theorem k2053_4 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2053) 3).2 2).1
      4080371412248354731135199571462909293469801203079153378969901905845004685880667871000251185).isSome = true := by
  decide +kernel

theorem k2053_5 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2053) 3).2 2).2
      347574894580793991196177326465203848589863469361879109746582746340756501338437864975663793116063260084341129326987732547192353585).isSome = true := by
  decide +kernel

theorem k2054_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2054) 3).1 2).1
      4079016026960010052207368675189430569820585601180295453295426030928574243778844484346170161).isSome = true := by
  decide +kernel

theorem k2054_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2054) 3).1 2).2
      3984474761042375412850038067115452567711726801636512041478214045431301676213135059284785).isSome = true := by
  decide +kernel

theorem k2054_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2054) 3).2 2).1
      995782118783644673461748736190958814904773349454768834438462332162955357456982350351153).isSome = true := by
  decide +kernel

theorem k2054_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2054) 3).2 2).2
      3983153765982258885936195535965885184282567179001306877238014721578329832692519361934129).isSome = true := by
  decide +kernel

theorem k2055_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2055) 2).1
      22205813974339860111673358989467841753414777862949590400845772843523187268934493887579232710925056344475023407059012801900295564487).isSome = true := by
  decide +kernel

theorem k2055_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2055) 2).2 3).1
      3982056764697633384639383405364644957545561721366404840290035223461530176220229103350577).isSome = true := by
  decide +kernel

theorem k2055_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2055) 2).2 3).2
      13487922513932717774907737233790288825004824399538198317418462147377).isSome = true := by
  decide +kernel

theorem k2056_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2056) 2).1
      4698314983339043931382821677414553852437772659848451782924742607450535016490858003277277831531031679974461235).isSome = true := by
  decide +kernel

theorem k2056_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 2056) 2).2
      5417028750863198220572527977684322294795315839298005517831056754406791232669412914455453840247684283615944324319139447340129075).isSome = true := by
  decide +kernel

theorem k2057_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2057) 2).1
      1146778129130755008261747727837438936784811393237282984784988614503191931517384668607498030930379136823687).isSome = true := by
  decide +kernel

theorem k2057_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 2057) 2).2
      971341185797563324336200583613446427964183477466891317294668398565924969499669800519).isSome = true := by
  decide +kernel

theorem c7 : allCells dirCell 2058 2075 [
    174179080973818102532733159367707372664786, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3] = true := by
  decide +kernel

theorem k2075_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2075) 3).1
      11866099350792628909095973993950038436892545102).isSome = true := by
  decide +kernel

theorem k2075_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 2075) 3).2
      421533691532784018376664551478768239620252347986685332906687436262206570313346646782390011668397916682240408630719991818867385295875574396804529806366).isSome = true := by
  decide +kernel

theorem k2076_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2076) 3).1 2).1 3).1
      62302541056170679732819511311514821237100836005566670435192954647478076992550298193).isSome = true := by
  decide +kernel

theorem k2076_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2076) 3).1 2).1 3).2
      1353038215470849264694112889021932298916880678039635320652417212570726077676941647937584749432920640357422857532655930538353).isSome = true := by
  decide +kernel

theorem k2076_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2076) 3).1 2).2
      6391900968591027983137728011975920383404588292541422766573826582002260957506509034966940298525204747110091205446420595572103768954351206371949645).isSome = true := by
  decide +kernel

theorem k2076_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2076) 3).2 2).1 3).1
      292597753380345806722190670597129132465839816960276876020041003891411935996346984938016801611010636930417).isSome = true := by
  decide +kernel

theorem k2076_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2076) 3).2 2).1 3).2
      25432430374023221194600531336381098614306542216987839042986123639266772312318245921733379520680917838960917713702582681133713618338112209631147505).isSome = true := by
  decide +kernel

theorem k2076_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2076) 3).2 2).2 1).1
      15463098215937955914339276537751455540745916855638592947774460327419246146646468979).isSome = true := by
  decide +kernel

theorem k2076_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2076) 3).2 2).2 1).2
      1380957683611166025237086415080539488461646112880176648624927224933993525424004609468454827785374064981580880613468693450028274).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 2051 2077 :=
  (Cover.one (box := dirCellBox) (n := 2051)
      (.split 3 (.split 2 (.split 1 (.leaf _ k2051_0) (.split 3 (.leaf _ k2051_1) (.leaf _ k2051_2))) (.split 1 (.leaf _ k2051_3) (.split 3 (.leaf _ k2051_4) (.leaf _ k2051_5)))) (.split 2 (.split 1 (.leaf _ k2051_6) (.leaf _ k2051_7)) (.split 1 (.leaf _ k2051_8) (.leaf _ k2051_9))))).trans <|
  (Cover.one (box := dirCellBox) (n := 2052)
      (.split 3 (.split 2 (.split 1 (.leaf _ k2052_0) (.leaf _ k2052_1)) (.split 1 (.leaf _ k2052_2) (.leaf _ k2052_3))) (.split 2 (.split 1 (.leaf _ k2052_4) (.leaf _ k2052_5)) (.split 1 (.leaf _ k2052_6) (.leaf _ k2052_7))))).trans <|
  (Cover.one (box := dirCellBox) (n := 2053)
      (.split 3 (.split 2 (.split 1 (.leaf _ k2053_0) (.leaf _ k2053_1)) (.split 1 (.leaf _ k2053_2) (.leaf _ k2053_3))) (.split 2 (.leaf _ k2053_4) (.leaf _ k2053_5)))).trans <|
  (Cover.one (box := dirCellBox) (n := 2054)
      (.split 3 (.split 2 (.leaf _ k2054_0) (.leaf _ k2054_1)) (.split 2 (.leaf _ k2054_2) (.leaf _ k2054_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 2055)
      (.split 2 (.leaf _ k2055_0) (.split 3 (.leaf _ k2055_1) (.leaf _ k2055_2)))).trans <|
  (Cover.one (box := dirCellBox) (n := 2056)
      (.split 2 (.leaf _ k2056_0) (.leaf _ k2056_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 2057)
      (.split 2 (.leaf _ k2057_0) (.leaf _ k2057_1))).trans <|
  (Cover.dir c7).trans <|
  (Cover.one (box := dirCellBox) (n := 2075)
      (.split 3 (.leaf _ k2075_0) (.leaf _ k2075_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 2076)
      (.split 3 (.split 2 (.split 3 (.leaf _ k2076_0) (.leaf _ k2076_1)) (.leaf _ k2076_2)) (.split 2 (.split 3 (.leaf _ k2076_3) (.leaf _ k2076_4)) (.split 1 (.leaf _ k2076_5) (.leaf _ k2076_6)))))

end C4.Cert.Dir026
