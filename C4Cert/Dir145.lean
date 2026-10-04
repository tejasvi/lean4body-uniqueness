module

public import C4Check

public section

/-! Cells `4543 ≤ n < 4573` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir145

theorem k4543_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4543) 2).1 3).1
      18486486553739176758552958486641758665464329621601443920796648211041330346312856065985735317413213423221964).isSome = true := by
  decide +kernel

theorem k4543_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4543) 2).1 3).2
      16014642921063819819673109644166694394471261797634788184875049971534246278293511253373745).isSome = true := by
  decide +kernel

theorem k4543_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4543) 2).2 3).1
      62640751037191324026660695763742912627755390865349345025792259409413950035563409370316).isSome = true := by
  decide +kernel

theorem k4543_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4543) 2).2 3).2
      250273865049153521414763254759605281344093637348522399568828474957272662971846646492364).isSome = true := by
  decide +kernel

theorem k4544_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4544) 2).1 3).1
      3999822989514270562791627022646069668197455656482470371898005673445541372551219132085041).isSome = true := by
  decide +kernel

theorem k4544_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4544) 2).1 3).2
      3385371684182287996608362807458671783915645843000903952879762993868).isSome = true := by
  decide +kernel

theorem k4544_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4544) 2).2 3).1
      847130487030572292642494914825259572503816079799853963418340093132).isSome = true := by
  decide +kernel

theorem k4544_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4544) 2).2 3).2
      734161204599594800146787254758479834800177529804).isSome = true := by
  decide +kernel

theorem k4545_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4545) 2).1 3).1
      211439735859947120302521207933350250097932399766834214620561394380).isSome = true := by
  decide +kernel

theorem k4545_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4545) 2).1 3).2
      211314586046012670395052652707596215726401188263023507574093236940).isSome = true := by
  decide +kernel

theorem k4545_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4545) 2).2 3).1
      211467186018169006423144288257227458698273646123688653318117639116).isSome = true := by
  decide +kernel

theorem k4545_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4545) 2).2 3).2
      211340233302921496982573680556820610630077038383184660106803921868).isSome = true := by
  decide +kernel

theorem k4546_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4546) 2).1 3).1
      844835347952433134302954636510085744789102131794440670214533098188).isSome = true := by
  decide +kernel

theorem k4546_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4546) 2).1 3).2
      15578289888959010947755884849935512087248180536416426186078552939460911391048761977916).isSome = true := by
  decide +kernel

theorem k4546_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4546) 2).2 1).1
      844745816081161283380676016420679653258609125167255701041159545804).isSome = true := by
  decide +kernel

theorem k4546_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4546) 2).2 1).2
      211180873382611140286518594824169510830762574381456548405842528972).isSome = true := by
  decide +kernel

theorem k4547_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4547) 2).1
      5554896433187435549285469053505266148100325830054668114424059892012769944886390302553292388316884233949653883961821490628938608883).isSome = true := by
  decide +kernel

theorem k4547_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4547) 2).2
      77091593903363552480442987383479983538509821139525073203950558106359043585338521689903050449406154677965098356531).isSome = true := by
  decide +kernel

theorem k4548_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4548) 3).1
      4704094898382924576629728850641637521298298269342031711757770343350599128244473614960084960193708585483189308).isSome = true := by
  decide +kernel

theorem k4548_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4548) 3).2
      18373736068648054036647404641212352914721614148038150372482161921731723560892492291152646524954276657577020).isSome = true := by
  decide +kernel

theorem k4549_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4549) 1).1
      3982486305190418415926844537389152090429607527897518923135908027688098058461279707511868).isSome = true := by
  decide +kernel

theorem k4549_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4549) 1).2
      3982531180646248082027225806012544939892053614060001430860957457104217825044286848941116).isSome = true := by
  decide +kernel

theorem k4550_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4550) 3).1
      15926432907655968103271368136177595312208393567523139175239873228182358535098855031225404).isSome = true := by
  decide +kernel

theorem k4550_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4550) 3).2
      53953904617373838829396485499143185124492233549960502361039029058620).isSome = true := by
  decide +kernel

theorem k4551_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4551) 2).1
      842895910259888049254167229938797945539188211747101748932453581628).isSome = true := by
  decide +kernel

theorem k4551_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4551) 2).2
      13486628489448179136653505839275541929610959352767536526323951059772).isSome = true := by
  decide +kernel

theorem c9 : allCells dirCell 4552 4553 [
    1386777714211039887401582588586192665093175025448325806872648642376297897486037705764830926277487071961228279791670354696580612924] = true := by
  decide +kernel

theorem c10 : allCells dirCell 4553 4554 [
    5546421744730562505205756764885536123003041822335210482474457524807577069469340786542503850506765707356920340609955965918095208689] = true := by
  decide +kernel

theorem c11 : allCells dirCell 4554 4555 [
    18349666843983564028932829887336472246321577655413045233214819943262762934708850701688948021917330261192956] = true := by
  decide +kernel

theorem c12 : allCells dirCell 4555 4568 [
    51423313392665068543042622043087791053119309831222816856589329, 147564495655729112500, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 38681140043410908972051] = true := by
  decide +kernel

theorem k4568_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4568) 3).1
      15490344503044384151619443625101155257936040993583961751485637374122371383442067826).isSome = true := by
  decide +kernel

theorem k4568_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4568) 3).2
      3952862725601392108249255541153922520614304531397801711312407994948234896641977718578).isSome = true := by
  decide +kernel

theorem k4569_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4569) 3).1
      64594328052915857341504232221742817839968692329882579175283958262301211704937889573391558).isSome = true := by
  decide +kernel

theorem k4569_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4569) 3).2
      1007083987594238345340343754637114308756782136659207424869604322051658960084026969649970).isSome = true := by
  decide +kernel

theorem k4570_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4570) 2).1 3).1
      981717726521645103435772556923743032613883321608445414478523230984735709263623453900).isSome = true := by
  decide +kernel

theorem k4570_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4570) 2).1 3).2
      53133933305385398373721562077133717714178423092410507030152690892).isSome = true := by
  decide +kernel

theorem k4570_2 : (checkBoxH dirMode depth (splitBox (dirCellBox 4570) 2).2
      1184378532420548488767087853452691691376514447051429311385707577456111112768213194202605791148057882148303667).isSome = true := by
  decide +kernel

theorem k4571_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4571) 2).1
      22327295506773379451133767533677342401945475397484388301322092033115421983431090011652625905127718013589147799622493044689031459635).isSome = true := by
  decide +kernel

theorem k4571_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4571) 2).2
      1395550929475963503849238727896998233799029941988746530483478704916621361606971899677240864232511505007887888116370102408649225011).isSome = true := by
  decide +kernel

theorem k4572_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4572) 2).1
      22287375896495306049998314534732452319577750395793024760028519539756823198458117412413961447884335324981336029398818251343459169075).isSome = true := by
  decide +kernel

theorem k4572_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4572) 2).2
      1393080443245879473878850612935841677752283975873954209128849937502386349050179679615706267365391559131367309333593747235966661427).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 4543 4573 :=
  (Cover.one (box := dirCellBox) (n := 4543)
      (.split 2 (.split 3 (.leaf _ k4543_0) (.leaf _ k4543_1)) (.split 3 (.leaf _ k4543_2) (.leaf _ k4543_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 4544)
      (.split 2 (.split 3 (.leaf _ k4544_0) (.leaf _ k4544_1)) (.split 3 (.leaf _ k4544_2) (.leaf _ k4544_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 4545)
      (.split 2 (.split 3 (.leaf _ k4545_0) (.leaf _ k4545_1)) (.split 3 (.leaf _ k4545_2) (.leaf _ k4545_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 4546)
      (.split 2 (.split 3 (.leaf _ k4546_0) (.leaf _ k4546_1)) (.split 1 (.leaf _ k4546_2) (.leaf _ k4546_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 4547)
      (.split 2 (.leaf _ k4547_0) (.leaf _ k4547_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 4548)
      (.split 3 (.leaf _ k4548_0) (.leaf _ k4548_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 4549)
      (.split 1 (.leaf _ k4549_0) (.leaf _ k4549_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 4550)
      (.split 3 (.leaf _ k4550_0) (.leaf _ k4550_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 4551)
      (.split 2 (.leaf _ k4551_0) (.leaf _ k4551_1))).trans <|
  (Cover.dir c9).trans <|
  (Cover.dir c10).trans <|
  (Cover.dir c11).trans <|
  (Cover.dir c12).trans <|
  (Cover.one (box := dirCellBox) (n := 4568)
      (.split 3 (.leaf _ k4568_0) (.leaf _ k4568_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 4569)
      (.split 3 (.leaf _ k4569_0) (.leaf _ k4569_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 4570)
      (.split 2 (.split 3 (.leaf _ k4570_0) (.leaf _ k4570_1)) (.leaf _ k4570_2))).trans <|
  (Cover.one (box := dirCellBox) (n := 4571)
      (.split 2 (.leaf _ k4571_0) (.leaf _ k4571_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 4572)
      (.split 2 (.leaf _ k4572_0) (.leaf _ k4572_1)))

end C4.Cert.Dir145
