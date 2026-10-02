module

public import C4Check

public section

/-! Cells `4400 ≤ n < 4428` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir146

theorem k4400_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4400) 2).1
      87834020161882476165945843239362114648492057747328166794139655713334160843476167675426611886186657294381300703450112394427249947).isSome = true := by
  decide +kernel

theorem k4400_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4400) 2).2 3).1
      15850410359398698303547340060350251949173441875897487493699116268843667564703682540742).isSome = true := by
  decide +kernel

theorem k4400_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4400) 2).2 3).2
      15773513990848101426358740675250209169820247550163037260474262963428908095186004690121).isSome = true := by
  decide +kernel

theorem k4401_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4401) 2).1
      6295030729351169646408734155855752772474534091620165584715349589670548345345157129938421755265228112595611659502943540923185207535521813631346123).isSome = true := by
  decide +kernel

theorem k4401_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4401) 2).2 3).1
      62887906298893155660515436684745978387118660084293722321984703265276709322852068266697).isSome = true := by
  decide +kernel

theorem k4401_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4401) 2).2 3).2
      15322593173182787808846209390386842957468430173659629357956318011351579869340864882).isSome = true := by
  decide +kernel

theorem k4402_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4402) 2).1
      21265200296882517593243740123315677913005746827488084457273997572230485874549725407024591656872353209584942127389406031164871).isSome = true := by
  decide +kernel

theorem k4402_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4402) 2).2
      21276538667450542466070498738887950207300283573761831488863802519899440380877251876287466291993260442518332395206043972904391).isSome = true := by
  decide +kernel

theorem k4403_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4403) 2).1
      15232842854835000134123623702642195978919930331425574660341743609375655003451970931).isSome = true := by
  decide +kernel

theorem k4403_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4403) 2).2
      21235720681202500417462180703208470283580370426977358249657825362206828822270588598926159998068595263093188559612138675893703).isSome = true := by
  decide +kernel

theorem c4 : allCells dirCell 4404 4405 [
    1847907328973250143948359477828418467717270265728113872428160492716631303731755194951189808844306233757745696034745307361055557814131864681887122323330736914154755534] = true := by
  decide +kernel

theorem c5 : allCells dirCell 4405 4406 [
    6255951631885077966195579342446928319050924455578769245186338675179045375276704776069632791600173474023670600010953018125700721986625456378742214] = true := by
  decide +kernel

theorem c6 : allCells dirCell 4406 4407 [
    21186098986503769584035582752115801310351451764978989354574126609799844085020367290802696426924581172908696230698553279350214] = true := by
  decide +kernel

theorem c7 : allCells dirCell 4407 4426 [
    71753587971604185749754298928002394768285429515558278954458315909986297021364976298218634836760572445510,
    2790036840070760308336630385637194789345026, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] = true := by
  decide +kernel

theorem k4426_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4426) 3).1
      1428651338299655706780269433423781146489915271083281666921950202040709805878368704782069419415283636332615531148551377380781339).isSome = true := by
  decide +kernel

theorem k4426_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4426) 3).2 2).1
      1223403257533392534348551801056302029927965205816027166776284664453512799501780080286326202742866087632704203).isSome = true := by
  decide +kernel

theorem k4426_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4426) 3).2 2).2
      64780751447442142546789687236982040848742731325615664120177704594601515616361511684167).isSome = true := by
  decide +kernel

theorem k4427_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4427) 3).1 2).1
      4114808152402987347378315352950207426598083086351656498122724805350031795152267479257990).isSome = true := by
  decide +kernel

theorem k4427_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4427) 3).1 2).2
      256692138111865856887622285697961282605045269451751258644509810770485573495241828947763).isSome = true := by
  decide +kernel

theorem k4427_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4427) 3).2 2).1
      1020754919935153121066332518312600325246159602569372536516495833126637086858946858259657).isSome = true := by
  decide +kernel

theorem k4427_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4427) 3).2 2).2
      16342385830439222582850545773055607539859312151292743948712379181267565940557463680799625).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 4400 4428 :=
  (Cover.one (box := dirCellBox) (n := 4400)
      (.split 2 (.leaf _ k4400_0) (.split 3 (.leaf _ k4400_1) (.leaf _ k4400_2)))).trans <|
  (Cover.one (box := dirCellBox) (n := 4401)
      (.split 2 (.leaf _ k4401_0) (.split 3 (.leaf _ k4401_1) (.leaf _ k4401_2)))).trans <|
  (Cover.one (box := dirCellBox) (n := 4402)
      (.split 2 (.leaf _ k4402_0) (.leaf _ k4402_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 4403)
      (.split 2 (.leaf _ k4403_0) (.leaf _ k4403_1))).trans <|
  (Cover.dir c4).trans <|
  (Cover.dir c5).trans <|
  (Cover.dir c6).trans <|
  (Cover.dir c7).trans <|
  (Cover.one (box := dirCellBox) (n := 4426)
      (.split 3 (.leaf _ k4426_0) (.split 2 (.leaf _ k4426_1) (.leaf _ k4426_2)))).trans <|
  (Cover.one (box := dirCellBox) (n := 4427)
      (.split 3 (.split 2 (.leaf _ k4427_0) (.leaf _ k4427_1)) (.split 2 (.leaf _ k4427_2) (.leaf _ k4427_3))))

end C4.Cert.Dir146
