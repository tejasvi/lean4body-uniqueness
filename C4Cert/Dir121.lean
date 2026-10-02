module

public import C4Check

public section

/-! Cells `3619 ≤ n < 3643` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir121

theorem k3619_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3619) 2).1 3).1
      288139790639529637261254651820860223674677065068173666743055920872887139777447247670868037189438061139772).isSome = true := by
  decide +kernel

theorem k3619_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3619) 2).1 3).2
      287865836818730076996304767505623140746995465988944656274369589421441363320715800553018957312484156364604).isSome = true := by
  decide +kernel

theorem k3619_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3619) 2).2 3).1
      15626077732849486479937018044818757978614638695123159546926798103566523709146762040124).isSome = true := by
  decide +kernel

theorem k3619_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3619) 2).2 3).2
      62439704300981468469282198389722909838635745921864657240512439556103640364519836830524).isSome = true := by
  decide +kernel

theorem k3620_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3620) 2).1 3).1
      287656491933302152661952785621711079859937105654679609581650120774642490302435323606307539153884605306684).isSome = true := by
  decide +kernel

theorem k3620_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3620) 2).1 3).2
      287492083409145937205117793641555307479828959322543471260844599583150378454660591077905382486148086486844).isSome = true := by
  decide +kernel

theorem k3620_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3620) 2).2 3).1
      287759044943046905065114976533500229056073094561373090666243317578202119093900454879021706863587158906684).isSome = true := by
  decide +kernel

theorem k3620_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3620) 2).2 3).2
      287572125919013177723079432458456559280892597329438652439259355068439437969797201018483935162403298727740).isSome = true := by
  decide +kernel

theorem k3621_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3621) 2).1
      5425904919600752960599567854500849809416359365851091825681599373951234600550844560186189369066869956252118708002254129629352691).isSome = true := by
  decide +kernel

theorem k3621_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 3621) 2).2
      5426777904148936762762344326871484101172658401731924620425894111607697008219990164832795853652989315115880587675077617933317363).isSome = true := by
  decide +kernel

theorem k3622_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3622) 2).1
      287093231617925052082589217706423062347717827274441940855348211186501800301050019741903321553063073141491).isSome = true := by
  decide +kernel

theorem k3622_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 3622) 2).2
      338963258948196308910231266246519378846528275197911298577186272229904719729246222950755957929603884870189372029158102184850675).isSome = true := by
  decide +kernel

theorem k3623_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3623) 2).1
      15193574325444822661715541058426592394141678324490801350589979717189939273142897009).isSome = true := by
  decide +kernel

theorem k3623_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 3623) 2).2
      71748628543437514786176218703508936804985416624357890456696893442840876802402487839952147311147646022899).isSome = true := by
  decide +kernel

theorem c5 : allCells dirCell 3624 3625 [
    5292827392882495272806123167549053514701296949641322060153571981941250412154771358249255460098690839852364137281150885259590] = true := by
  decide +kernel

theorem c6 : allCells dirCell 3625 3642 [
    51450558385617979147919816360922358258280789202529620725753746, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0] = true := by
  decide +kernel

theorem k3642_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3642) 3).1
      3487207511413570863359610580835551865777860165663797717363020899).isSome = true := by
  decide +kernel

theorem k3642_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3642) 3).2 2).1
      22105097558863179609386065243672921262615600465712017485821795168618399338018122962443562652914918978643093354014800508431943).isSome = true := by
  decide +kernel

theorem k3642_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3642) 3).2 2).2
      63429442587911329945331910252936274010631999780486352935849760405005797202613539187).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 3619 3643 :=
  (Cover.one (box := dirCellBox) (n := 3619)
      (.split 2 (.split 3 (.leaf _ k3619_0) (.leaf _ k3619_1)) (.split 3 (.leaf _ k3619_2) (.leaf _ k3619_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 3620)
      (.split 2 (.split 3 (.leaf _ k3620_0) (.leaf _ k3620_1)) (.split 3 (.leaf _ k3620_2) (.leaf _ k3620_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 3621)
      (.split 2 (.leaf _ k3621_0) (.leaf _ k3621_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 3622)
      (.split 2 (.leaf _ k3622_0) (.leaf _ k3622_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 3623)
      (.split 2 (.leaf _ k3623_0) (.leaf _ k3623_1))).trans <|
  (Cover.dir c5).trans <|
  (Cover.dir c6).trans <|
  (Cover.one (box := dirCellBox) (n := 3642)
      (.split 3 (.leaf _ k3642_0) (.split 2 (.leaf _ k3642_1) (.leaf _ k3642_2))))

end C4.Cert.Dir121
