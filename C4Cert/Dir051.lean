module

public import C4Check

public section

/-! Cells `2501 ≤ n < 2527` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir051

theorem k2501_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2501) 3).1 1).1
      845220954626547231464774055771417991472419900573829671661065937868).isSome = true := by
  decide +kernel

theorem k2501_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2501) 3).1 1).2
      845217401394672728947921575988756048166587404370488832456969364428).isSome = true := by
  decide +kernel

theorem k2501_2 : (checkBoxH dirMode depth (splitBox (dirCellBox 2501) 3).2
      301394061060453868420513617041235614136666107699106610819592174926449555380326276151378827402636002453433569074).isSome = true := by
  decide +kernel

theorem k2502_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2502) 3).1
      15948286013304631173410078580567695222488325911048729833841137498687299122145849797459004).isSome = true := by
  decide +kernel

theorem k2502_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 2502) 3).2
      15941616907712724070432345391954500687541611926584436451892258027502009262034224458972220).isSome = true := by
  decide +kernel

theorem k2503_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2503) 3).1
      996002888446428868352758771877202455861510575314509029106613486934552290488131416898620).isSome = true := by
  decide +kernel

theorem k2503_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 2503) 3).2
      3982741633226607943879487042573175578174624814717706479026987160301541142146919443348540).isSome = true := by
  decide +kernel

theorem c3 : allCells dirCell 2504 2505 [
    22195157473283045497901726197635105702165539258561642503318490005382505692908718650653123136894585734136352060397385837665848717555] = true := by
  decide +kernel

theorem c4 : allCells dirCell 2505 2506 [
    4698822569875637149620390189130128067693452648778020581258474646251515516572739747683820484032899108934349041] = true := by
  decide +kernel

theorem c5 : allCells dirCell 2506 2523 [
    971353989870906972758815489199566561363130991688158166724124704433021033718326249841,
    147542018476787528260, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] = true := by
  decide +kernel

theorem c6 : allCells dirCell 2523 2524 [
    1001667664083668875552888845832714616054559430603999430942151812629531578202855683171] = true := by
  decide +kernel

theorem k2524_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2524) 3).1
      1599827856660571291090505262297950060383416526929372057618417378505688605349575685903554226910965652961838950819876478705512102226499223020991986).isSome = true := by
  decide +kernel

theorem k2524_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2524) 3).2 2).1
      86348520690221955365339162779579349922000587618008091538367845865324522586477552477849056171018209168911312036099686800389372).isSome = true := by
  decide +kernel

theorem k2524_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2524) 3).2 2).2
      3871798968890850565719538274015730275112990099981619861755255385978175577789980028).isSome = true := by
  decide +kernel

theorem k2525_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2525) 3).1 2).1
      252823333237479322272612591277363829013575891426963150095410655727239235086917950075132).isSome = true := by
  decide +kernel

theorem k2525_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2525) 3).1 2).2
      3346022664854680723828752002167574342915345324981596407115141372).isSome = true := by
  decide +kernel

theorem k2525_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2525) 3).2 2).1
      15756683588976195180509765363944203263526132667795575821658564787601325523741984675644).isSome = true := by
  decide +kernel

theorem k2525_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2525) 3).2 2).2
      15757608731586576493081219999683844512579864300581746605390377866959020888529701427004).isSome = true := by
  decide +kernel

theorem k2526_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2526) 2).1 3).1
      852040759670793450021802889321773531278454058817287914733740479292).isSome = true := by
  decide +kernel

theorem k2526_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2526) 2).1 3).2
      3401047837154972604912615971833688307025699999098722341597906674492).isSome = true := by
  decide +kernel

theorem k2526_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2526) 2).2 3).1
      852140983800433399082494416786786203297231714718161539071244489532).isSome = true := by
  decide +kernel

theorem k2526_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2526) 2).2 3).2
      850571729551640313660618498006214619666619932328692204404345393980).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 2501 2527 :=
  (Cover.one (box := dirCellBox) (n := 2501)
      (.split 3 (.split 1 (.leaf _ k2501_0) (.leaf _ k2501_1)) (.leaf _ k2501_2))).trans <|
  (Cover.one (box := dirCellBox) (n := 2502)
      (.split 3 (.leaf _ k2502_0) (.leaf _ k2502_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 2503)
      (.split 3 (.leaf _ k2503_0) (.leaf _ k2503_1))).trans <|
  (Cover.dir c3).trans <|
  (Cover.dir c4).trans <|
  (Cover.dir c5).trans <|
  (Cover.dir c6).trans <|
  (Cover.one (box := dirCellBox) (n := 2524)
      (.split 3 (.leaf _ k2524_0) (.split 2 (.leaf _ k2524_1) (.leaf _ k2524_2)))).trans <|
  (Cover.one (box := dirCellBox) (n := 2525)
      (.split 3 (.split 2 (.leaf _ k2525_0) (.leaf _ k2525_1)) (.split 2 (.leaf _ k2525_2) (.leaf _ k2525_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 2526)
      (.split 2 (.split 3 (.leaf _ k2526_0) (.leaf _ k2526_1)) (.split 3 (.leaf _ k2526_2) (.leaf _ k2526_3))))

end C4.Cert.Dir051
