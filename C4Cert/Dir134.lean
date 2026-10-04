module

public import C4Check

public section

/-! Cells `4098 ≤ n < 4125` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir134

theorem k4098_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4098) 2).1 3).1
      997014795514934884240000516442781284273105446099962770678058964009793060866892624544572).isSome = true := by
  decide +kernel

theorem k4098_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4098) 2).1 3).2
      3376746871070111033197158599607351888902786622118500376124795372348).isSome = true := by
  decide +kernel

theorem k4098_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4098) 2).2 3).1
      3988531224723173864054027172899183226797878260343525229074548235865740963470503030078524).isSome = true := by
  decide +kernel

theorem k4098_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4098) 2).2 3).2
      54032572495284065782577019098837840868549580553158598100919692475452).isSome = true := by
  decide +kernel

theorem k4099_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4099) 3).1 2).1
      52744556495024866628356820070317478202936904317653290243341021756).isSome = true := by
  decide +kernel

theorem k4099_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4099) 3).1 2).2
      3375999974427927319366687389217021494356506484276211919011322774332).isSome = true := by
  decide +kernel

theorem k4099_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4099) 3).2 2).1
      210919723490003880663609547787340864768758477456936259462524029500).isSome = true := by
  decide +kernel

theorem k4099_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4099) 3).2 2).2
      210942573023073375387324609400224131849228798079348418566392628028).isSome = true := by
  decide +kernel

theorem k4100_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4100) 3).1 2).1
      972520459024277411001909144422758738122802195194073843224205380991330866392360941116).isSome = true := by
  decide +kernel

theorem k4100_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4100) 3).1 2).2
      210889822712081456344946229729671679889519067848411749874660787004).isSome = true := by
  decide +kernel

theorem k4100_2 : (checkBoxH dirMode depth (splitBox (dirCellBox 4100) 3).2
      102401278693474404376379514661880924843979545864167583440678624194053943210494655472161653982504791476141315852377824358749049025417958313424007930684).isSome = true := by
  decide +kernel

theorem k4101_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4101) 2).1
      346853224815739820137591708242266420045700955328526630080184549821891321731097577008282768095607322876494412209432187332663227196).isSome = true := by
  decide +kernel

theorem k4101_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4101) 2).2
      1599665366020035682865903022475659307502408902094203933831591890828386992832671765030471356209321414884586800215281510712032810031974409593430172476).isSome = true := by
  decide +kernel

theorem k4102_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4102) 3).1
      18359162639202401194707657012021487135754491020523517908305728852307791400769703866481141934934103085228860).isSome = true := by
  decide +kernel

theorem k4102_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4102) 3).2
      62211258290864855524431991225010317409447386418665549546234743263156025566912894149436).isSome = true := by
  decide +kernel

theorem k4103_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4103) 3).1
      3886890003637929254294461526259443002167687920299110472281280345082140262125633139260).isSome = true := by
  decide +kernel

theorem k4103_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4103) 3).2
      3886569737192710183514589854231005220878713403468106543129455820089838667436884619836).isSome = true := by
  decide +kernel

theorem c6 : allCells dirCell 4104 4105 [
    399673531690754029321102282431634687812816466332460845851242812176702729115812283524650150893168363565238947081013745790647781805204429506461922546] = true := by
  decide +kernel

theorem c7 : allCells dirCell 4105 4106 [
    18350294405509778362877585838894280418821729223330574839656623949952855903051815484538492683117739992533233] = true := by
  decide +kernel

theorem c8 : allCells dirCell 4106 4119 [
    4479631313681610071122655499224016848939342005935477105783396539491781604944881110271942020924970894705,
    147562890987157458580, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] = true := by
  decide +kernel

theorem c9 : allCells dirCell 4119 4120 [
    6556935156990566352834609639259528831073658513312962789278039105766830412565026340717462038972531318376189860191732569247293393812786165665456030779] = true := by
  decide +kernel

theorem k4120_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4120) 3).1
      5663479673886258860817049826972787395752113771789317033526092994102007286571880617461132096298575443375125855328835884561277869254).isSome = true := by
  decide +kernel

theorem k4120_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4120) 3).2 2).1
      1377812839280491374221491621310208454575922043318611900103102380867909222534316595562619058501251785348188665692392500334228428).isSome = true := by
  decide +kernel

theorem k4120_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4120) 3).2 2).2
      3953314718212433758458709106357101396749059663217604284270124870215373899764700223281).isSome = true := by
  decide +kernel

theorem k4121_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4121) 2).1 3).1
      4132617010666041549969166006328225370770216078811275394934131636020695330056843586194918601).isSome = true := by
  decide +kernel

theorem k4121_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4121) 2).1 3).2
      1189262035548237743472061052179758154434002975307578469882194556738741039523496700122657793228397257775500081).isSome = true := by
  decide +kernel

theorem k4121_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4121) 2).2 3).1
      4653591473311865701600752082106172446687529788513939395850301835565652693556218211121680457254052028036044).isSome = true := by
  decide +kernel

theorem k4121_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4121) 2).2 3).2
      4029680772669724964196205395720507579403125886165946405399028008528320374979186505665329).isSome = true := by
  decide +kernel

theorem k4122_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4122) 2).1 3).1
      5604373851469588131934802114935002014621833643071191176773980969426801934912818876822843323387355487867266013021947072352213257009).isSome = true := by
  decide +kernel

theorem k4122_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4122) 2).1 3).2
      303272704636684906409943554170975894300831781810236982769935926580885501459634447938548324945306094658758626097).isSome = true := by
  decide +kernel

theorem k4122_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4122) 2).2 3).1
      16085442680485083539966302351599686071349413881980241299139674363843124483268314687458097).isSome = true := by
  decide +kernel

theorem k4122_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4122) 2).2 3).2
      1366202467612854093502067327235181816941013751951257103672632256756923620591542870162727571948371420166093744334638493229118156).isSome = true := by
  decide +kernel

theorem k4123_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4123) 2).1 3).1 1).1
      53053634192492784372141706457250670468054019599747201739618906828).isSome = true := by
  decide +kernel

theorem k4123_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4123) 2).1 3).1 1).2
      53046827877138027736525249640527815324552440580682523873653420748).isSome = true := by
  decide +kernel

theorem k4123_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4123) 2).1 3).2
      348755300231342781295740600619355101568698917153057181255704594491995663727191780925021455717442571999622771789707595287260603340).isSome = true := by
  decide +kernel

theorem k4123_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4123) 2).2 3).1
      295816278793234607162137868487567228440188662751311434299051213411547305228989245663822185756965117556147148).isSome = true := by
  decide +kernel

theorem k4123_4 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4123) 2).2 3).2
      73864631136490049680768510482482905318278814046041178520099752280235322936356805239190072654198095918908364).isSome = true := by
  decide +kernel

theorem k4124_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4124) 2).1 3).1
      295106833084358926133079127716562690470756199401249166442216291863019127236451470365228182859733632143893452).isSome = true := by
  decide +kernel

theorem k4124_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4124) 2).1 3).2
      221806856741889182683077367652504353191815103654007439831327401081449265).isSome = true := by
  decide +kernel

theorem k4124_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4124) 2).2 3).1
      16000468301930168963714149816087587359520273196791989610310758705033714337963464576672716).isSome = true := by
  decide +kernel

theorem k4124_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4124) 2).2 3).2
      999192601550691438875683348691062318670796397180240105346174847514411539810907244504012).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 4098 4125 :=
  (Cover.one (box := dirCellBox) (n := 4098)
      (.split 2 (.split 3 (.leaf _ k4098_0) (.leaf _ k4098_1)) (.split 3 (.leaf _ k4098_2) (.leaf _ k4098_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 4099)
      (.split 3 (.split 2 (.leaf _ k4099_0) (.leaf _ k4099_1)) (.split 2 (.leaf _ k4099_2) (.leaf _ k4099_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 4100)
      (.split 3 (.split 2 (.leaf _ k4100_0) (.leaf _ k4100_1)) (.leaf _ k4100_2))).trans <|
  (Cover.one (box := dirCellBox) (n := 4101)
      (.split 2 (.leaf _ k4101_0) (.leaf _ k4101_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 4102)
      (.split 3 (.leaf _ k4102_0) (.leaf _ k4102_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 4103)
      (.split 3 (.leaf _ k4103_0) (.leaf _ k4103_1))).trans <|
  (Cover.dir c6).trans <|
  (Cover.dir c7).trans <|
  (Cover.dir c8).trans <|
  (Cover.dir c9).trans <|
  (Cover.one (box := dirCellBox) (n := 4120)
      (.split 3 (.leaf _ k4120_0) (.split 2 (.leaf _ k4120_1) (.leaf _ k4120_2)))).trans <|
  (Cover.one (box := dirCellBox) (n := 4121)
      (.split 2 (.split 3 (.leaf _ k4121_0) (.leaf _ k4121_1)) (.split 3 (.leaf _ k4121_2) (.leaf _ k4121_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 4122)
      (.split 2 (.split 3 (.leaf _ k4122_0) (.leaf _ k4122_1)) (.split 3 (.leaf _ k4122_2) (.leaf _ k4122_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 4123)
      (.split 2 (.split 3 (.split 1 (.leaf _ k4123_0) (.leaf _ k4123_1)) (.leaf _ k4123_2)) (.split 3 (.leaf _ k4123_3) (.leaf _ k4123_4)))).trans <|
  (Cover.one (box := dirCellBox) (n := 4124)
      (.split 2 (.split 3 (.leaf _ k4124_0) (.leaf _ k4124_1)) (.split 3 (.leaf _ k4124_2) (.leaf _ k4124_3))))

end C4.Cert.Dir134
