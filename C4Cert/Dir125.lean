module

public import C4Check

public section

/-! Cells `3677 ≤ n < 3702` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir125

theorem k3677_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3677) 2).1
      1390347620438673866545697100590896857516645881486924184550431242892804971625022090882104253040535598758077792515492872593176605500).isSome = true := by
  decide +kernel

theorem k3677_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 3677) 2).2
      1390593157542094765390035959384920202862749536107199633255225264871043356836413529590057998598264634647674029435527941963105710908).isSome = true := by
  decide +kernel

theorem k3678_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3678) 3).1
      1389465604575777852595516915338289051875948019635903706020425093864383648163630095981921414113882185963034764370015673369809953596).isSome = true := by
  decide +kernel

theorem k3678_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 3678) 3).2
      15944424634295549177390209843624787818797973433887910517955865262442338150288976026313532).isSome = true := by
  decide +kernel

theorem k3679_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3679) 2).1
      249012338605595683858528119341213775058269798731281667788126174748544654365451464725308).isSome = true := by
  decide +kernel

theorem k3679_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 3679) 2).2
      62260617505779710033151276617160005556625923891871044578267850026253797623739708855100).isSome = true := by
  decide +kernel

theorem k3680_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3680) 3).1
      62232919198535057281441394116016831355568389617243853307301725025575423765147872600892).isSome = true := by
  decide +kernel

theorem k3680_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 3680) 3).2
      62221435633877351776970572205966787652381059937082085440849233608467997900749498426172).isSome = true := by
  decide +kernel

theorem k3681_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3681) 2).1
      205826580299341935300269123873097500478834267249171707724717372).isSome = true := by
  decide +kernel

theorem k3681_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 3681) 2).2
      286892960272513958009849483611246720327838633251308075255684857241616617578146721301062577470135258829628).isSome = true := by
  decide +kernel

theorem c5 : allCells dirCell 3682 3683 [
    15920304049030935554052626291455940930271931401764508675844492058141103440962971095124211] = true := by
  decide +kernel

theorem c6 : allCells dirCell 3683 3684 [
    1147068986488135741337364596793035588689173883990525869936019418371117885144682454465040455598544496104690] = true := by
  decide +kernel

theorem c7 : allCells dirCell 3684 3699 [
    242864753210961644751019107347791592592382097927978150370559565794541640608726697330,
    51422898493400170604641240752417960068998774613397586086111762, 147560478864743407908, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0] = true := by
  decide +kernel

theorem k3699_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3699) 3).1
      62879836934599633166867511442305544486419412510015974186859831024274279816012400710).isSome = true := by
  decide +kernel

theorem k3699_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 3699) 3).2
      6413956380895856932294204684569931717242508792457603044465721568645830936841255803323354404189847453019589685246951219976329199696533907256407494).isSome = true := by
  decide +kernel

theorem k3700_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3700) 3).1
      22698025713216827863815842074107135362882473602175013054052499362910762472971000963086634093811521093018782103881530781538906475762).isSome = true := by
  decide +kernel

theorem k3700_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3700) 3).2 2).1
      990020155466223910175798587963264815157993828102278122766401686603649527392956677180).isSome = true := by
  decide +kernel

theorem k3700_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3700) 3).2 2).2
      990040178903811330623107736390859573622065744098167314096659717773767333761431469116).isSome = true := by
  decide +kernel

theorem k3701_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3701) 2).1
      22468298920505797281298262884576099217437159268239914917556660521154884732433950682156941692824234422435348115987462905843546386675).isSome = true := by
  decide +kernel

theorem k3701_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 3701) 2).2
      22472550749868014341394090902555480701935072067389127933063450931045916777412534836080601912539461468876231453359373751749516259571).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 3677 3702 :=
  (Cover.one (box := dirCellBox) (n := 3677)
      (.split 2 (.leaf _ k3677_0) (.leaf _ k3677_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 3678)
      (.split 3 (.leaf _ k3678_0) (.leaf _ k3678_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 3679)
      (.split 2 (.leaf _ k3679_0) (.leaf _ k3679_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 3680)
      (.split 3 (.leaf _ k3680_0) (.leaf _ k3680_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 3681)
      (.split 2 (.leaf _ k3681_0) (.leaf _ k3681_1))).trans <|
  (Cover.dir c5).trans <|
  (Cover.dir c6).trans <|
  (Cover.dir c7).trans <|
  (Cover.one (box := dirCellBox) (n := 3699)
      (.split 3 (.leaf _ k3699_0) (.leaf _ k3699_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 3700)
      (.split 3 (.leaf _ k3700_0) (.split 2 (.leaf _ k3700_1) (.leaf _ k3700_2)))).trans <|
  (Cover.one (box := dirCellBox) (n := 3701)
      (.split 2 (.leaf _ k3701_0) (.leaf _ k3701_1)))

end C4.Cert.Dir125
