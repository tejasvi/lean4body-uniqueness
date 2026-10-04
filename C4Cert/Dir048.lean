module

public import C4Check

public section

/-! Cells `2473 ≤ n < 2498` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir048

theorem k2473_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2473) 3).1 2).1 1).1
      52796295260797343585594242029645416503856168101628180851006501580).isSome = true := by
  decide +kernel

theorem k2473_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2473) 3).1 2).1 1).2
      243747060887230842041970544066634575588490496773156105384644458299630677922994845388).isSome = true := by
  decide +kernel

theorem k2473_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2473) 3).1 2).2 1).1
      52808910003997442870127641053021909784469456306830930065978946252).isSome = true := by
  decide +kernel

theorem k2473_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2473) 3).1 2).2 1).2
      211225273284404516457629310607919396825206851914547320720752888524).isSome = true := by
  decide +kernel

theorem k2473_4 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2473) 3).2 2).1
      294229121219714891398669400682765973664692675628110181941166213546699536656746469525726628264443029646330673).isSome = true := by
  decide +kernel

theorem k2473_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2473) 3).2 2).2 1).1
      52779065572833945787119168603857716646702544171293410121333732044).isSome = true := by
  decide +kernel

theorem k2473_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2473) 3).2 2).2 1).2
      52777760377034239686732432607352721404062911886136796647133792972).isSome = true := by
  decide +kernel

theorem k2474_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2474) 3).1 2).1
      294101004102131558530516178790261454697854442523303079939851714742804982623332795615904279082639604093143857).isSome = true := by
  decide +kernel

theorem k2474_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2474) 3).1 2).2
      63772665608969351301678443907241017327462189167768453244647784732475046529475569929014065).isSome = true := by
  decide +kernel

theorem k2474_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2474) 3).2 2).1
      1149514287941283536577448570279899759708612477005139754115924240726892307398014725709339242727551155523276).isSome = true := by
  decide +kernel

theorem k2474_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2474) 3).2 2).2
      287419345975476133586407391445989936656873484460917547718396806764300010415952308001038619847338770291404).isSome = true := by
  decide +kernel

theorem k2475_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2475) 3).1 2).1
      1148046638432860820044639411534380535511159116911023991045060198308256092691013216582878704796026500239052).isSome = true := by
  decide +kernel

theorem k2475_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2475) 3).1 2).2
      3983174506665691520924862627478621284457296002461404564315357170886138019779552222737201).isSome = true := by
  decide +kernel

theorem k2475_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2475) 3).2 2).1
      3293957160214773514317583010583700052470634554029057604484192972).isSome = true := by
  decide +kernel

theorem k2475_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2475) 3).2 2).2
      3982181053151541870437298713671569750015783357773492430386073106960833488514353705349937).isSome = true := by
  decide +kernel

theorem k2476_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2476) 2).1
      5418095850496977387421133906424759751513153089618154658915995127162097632956941951277331444982094806251197849985787370017250099).isSome = true := by
  decide +kernel

theorem k2476_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 2476) 2).2
      1599243126168025803588557552960647331641329769625448248682830333185978224325431790752918710455667604082299993965633334243199036479940490317440473907).isSome = true := by
  decide +kernel

theorem k2477_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2477) 2).1
      18351986218283017178957342987514580210896226457187055699044890654093480700909578783470379046430420265982771).isSome = true := by
  decide +kernel

theorem k2477_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 2477) 2).2
      18352147382783944321387122865482477251529969127785708209037970157603765145330402577676802858785005384358707).isSome = true := by
  decide +kernel

theorem k2478_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2478) 2).1
      971354643462185611190788992947761145596007034791272601163030380979952704396501064049).isSome = true := by
  decide +kernel

theorem k2478_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 2478) 2).2
      971354376597957743346021815207698124360986903161487210679288407239836452431137882481).isSome = true := by
  decide +kernel

theorem c6 : allCells dirCell 2479 2495 [
    2360843342253636035649, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] = true := by
  decide +kernel

theorem k2495_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2495) 3).1
      13981091372941751279429416678247003123190741785480203446688405651739).isSome = true := by
  decide +kernel

theorem k2495_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2495) 3).2 3).1
      21863558237122644080197489666750502428008655473940876255805009696003857380380121588381870539743651922476805504843727089395142).isSome = true := by
  decide +kernel

theorem k2495_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2495) 3).2 3).2
      6429487005582624458790893628410567458560191807599109719984696896743907783661398901011097679927917060547717820362392029356275842931178222034466246).isSome = true := by
  decide +kernel

theorem k2496_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2496) 3).1 2).1 1).1
      21659598953086105719523324713253086294066380006118911389245749643968896265032617585809104745018683034889998534286127852709363).isSome = true := by
  decide +kernel

theorem k2496_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2496) 3).1 2).1 1).2
      4695584613185643316693163221248773412667524248798676083453282188360906293877959331502438319275215559943667).isSome = true := by
  decide +kernel

theorem k2496_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2496) 3).1 2).2 1).1
      15533460624606576840629832157294703152021192574257857146958416342789823594735879539).isSome = true := by
  decide +kernel

theorem k2496_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2496) 3).1 2).2 1).2
      73406292822083178766040035302135263954021233550725420448514532195725365539313718712775660031912133620978).isSome = true := by
  decide +kernel

theorem k2496_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2496) 3).2 2).1 1).1
      1168621397924271091196433694116591545085197256389034387955996780361486450737669401916589835738357796070899).isSome = true := by
  decide +kernel

theorem k2496_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2496) 3).2 2).1 1).2
      18697986889300357937369244086382921092114411231714764791026908923416127843689920339547760983879437438641395).isSome = true := by
  decide +kernel

theorem k2496_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2496) 3).2 2).2 1).1
      1170216833924928954798070869943813073636260145604522564687968373996776775530837875188765829958684689396988).isSome = true := by
  decide +kernel

theorem k2496_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2496) 3).2 2).2 1).2
      3962403374988349774417895609428717941412201698441934477023024148121769105481872693052).isSome = true := by
  decide +kernel

theorem k2497_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2497) 3).1 2).1 1).1
      258791517937285820619692719289892913744124291652247808903999883828972325674778803904682226).isSome = true := by
  decide +kernel

theorem k2497_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2497) 3).1 2).1 1).2
      298336222929885812732556987065174185973941492132467415389035760899984163729089363097683200914039154385734460).isSome = true := by
  decide +kernel

theorem k2497_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2497) 3).1 2).2 1).1
      3949754021004117963253662875768186877122115417583955694278774476524012584454634560316).isSome = true := by
  decide +kernel

theorem k2497_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2497) 3).1 2).2 1).2
      252762005115308629242438688344950958977420984722560104339913410861601766915748769680188).isSome = true := by
  decide +kernel

theorem k2497_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2497) 3).2 2).1 1).1
      74362888184442530204927429976433733169180176410152586863993076883651836652029636923069540415986357602605628).isSome = true := by
  decide +kernel

theorem k2497_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2497) 3).2 2).1 1).2
      18598758799856532332667247517372318566623573301631975184896710952587994557618707336087098048194237438089788).isSome = true := by
  decide +kernel

theorem k2497_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2497) 3).2 2).2 1).1
      252009905505493311443462703015150158906464333384276283877622325686591986929569089146428).isSome = true := by
  decide +kernel

theorem k2497_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2497) 3).2 2).2 1).2
      1008010154324766328958306279546296281070936879283705148171818913919506573721732682567228).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 2473 2498 :=
  (Cover.one (box := dirCellBox) (n := 2473)
      (.split 3 (.split 2 (.split 1 (.leaf _ k2473_0) (.leaf _ k2473_1)) (.split 1 (.leaf _ k2473_2) (.leaf _ k2473_3))) (.split 2 (.leaf _ k2473_4) (.split 1 (.leaf _ k2473_5) (.leaf _ k2473_6))))).trans <|
  (Cover.one (box := dirCellBox) (n := 2474)
      (.split 3 (.split 2 (.leaf _ k2474_0) (.leaf _ k2474_1)) (.split 2 (.leaf _ k2474_2) (.leaf _ k2474_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 2475)
      (.split 3 (.split 2 (.leaf _ k2475_0) (.leaf _ k2475_1)) (.split 2 (.leaf _ k2475_2) (.leaf _ k2475_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 2476)
      (.split 2 (.leaf _ k2476_0) (.leaf _ k2476_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 2477)
      (.split 2 (.leaf _ k2477_0) (.leaf _ k2477_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 2478)
      (.split 2 (.leaf _ k2478_0) (.leaf _ k2478_1))).trans <|
  (Cover.dir c6).trans <|
  (Cover.one (box := dirCellBox) (n := 2495)
      (.split 3 (.leaf _ k2495_0) (.split 3 (.leaf _ k2495_1) (.leaf _ k2495_2)))).trans <|
  (Cover.one (box := dirCellBox) (n := 2496)
      (.split 3 (.split 2 (.split 1 (.leaf _ k2496_0) (.leaf _ k2496_1)) (.split 1 (.leaf _ k2496_2) (.leaf _ k2496_3))) (.split 2 (.split 1 (.leaf _ k2496_4) (.leaf _ k2496_5)) (.split 1 (.leaf _ k2496_6) (.leaf _ k2496_7))))).trans <|
  (Cover.one (box := dirCellBox) (n := 2497)
      (.split 3 (.split 2 (.split 1 (.leaf _ k2497_0) (.leaf _ k2497_1)) (.split 1 (.leaf _ k2497_2) (.leaf _ k2497_3))) (.split 2 (.split 1 (.leaf _ k2497_4) (.leaf _ k2497_5)) (.split 1 (.leaf _ k2497_6) (.leaf _ k2497_7)))))

end C4.Cert.Dir048
