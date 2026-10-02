module

public import C4Check

public section

/-! Cells `3169 ≤ n < 3193` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir091

theorem k3169_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3169) 2).1 3).1 2).1
      340979105615506507539623923805824860366294044329689594576434300605818853719632787298552857428979977797490453558805612288111859).isSome = true := by
  decide +kernel

theorem k3169_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3169) 2).1 3).1 2).2
      73984712567795659758543215396273697669037431877412196267587193753949857929240359894406087396862522129478897).isSome = true := by
  decide +kernel

theorem k3169_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3169) 2).1 3).2 2).1
      21284581779122006138105528588406964043655266033468717612328507770598460515463919167543411973784450087008614250973636168873201).isSome = true := by
  decide +kernel

theorem k3169_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3169) 2).1 3).2 2).2
      340593033884200170607665374721106136121641396125664895774587513767540694409459106489288126830793225039054656581994875889480947).isSome = true := by
  decide +kernel

theorem k3169_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3169) 2).2 3).1 1).1
      6453798104566743079534796031956665498624698803020054484287414351632827971589729871066518021881299722005780513649485637885157038437304808265530307388).isSome = true := by
  decide +kernel

theorem k3169_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3169) 2).2 3).1 1).2
      296303172696239918991719479957645363361808392646253782057036887665638162757186350438670469149618065651299570).isSome = true := by
  decide +kernel

theorem k3169_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3169) 2).2 3).2 1).1
      250479902017397289500235962621646659724962126126499089965749898730908764256534253226812).isSome = true := by
  decide +kernel

theorem k3169_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3169) 2).2 3).2 1).2
      288746936943639426672355249811878500104467875551246833846616443875453142998896817773179005951138575406908).isSome = true := by
  decide +kernel

theorem k3170_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3170) 2).1 3).1 3).1
      18016472408611295688982197865334619083932028102640768976757578138716541291413837246732860019620049090121).isSome = true := by
  decide +kernel

theorem k3170_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3170) 2).1 3).1 3).2
      15252776359725674472742179568884207693206144037083432977225289984812715952476500337).isSome = true := by
  decide +kernel

theorem k3170_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3170) 2).1 3).2
      1359748207792482055742895925012615228565219634632538372620335862410581746979063691571187469728018760389924100242468336259515377).isSome = true := by
  decide +kernel

theorem k3170_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3170) 2).2 3).1 1).1
      250109230581323409263669936818800282781137317042905683362320098957954915184103993068348).isSome = true := by
  decide +kernel

theorem k3170_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3170) 2).2 3).1 1).2
      288331017414442521861810833785927184301779694473895001213757528239935341670154575868640528701485078796092).isSome = true := by
  decide +kernel

theorem k3170_5 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3170) 2).2 3).2
      340022591812776722772182058636006900805147828900900871683802187580008154040186138740129072939809640696598650778832283943400689).isSome = true := by
  decide +kernel

theorem k3171_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3171) 2).1
      29577775902264079920885688884666713317584063168318251377233521788402245286349357964203093153829613542838475465034415118117531563647808211917769408891920012754658424094).isSome = true := by
  decide +kernel

theorem k3171_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3171) 2).2 3).1
      339733217332511373370489070076859057295604862012204838276852230420931025471389243746405102361912776200884803994878747634136307).isSome = true := by
  decide +kernel

theorem k3171_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3171) 2).2 3).2
      4494015630242375486560484648210040110651877725228517465932180999334504827711417868717317867617740347249).isSome = true := by
  decide +kernel

theorem c3 : allCells dirCell 3172 3173 [
    30261589103292589817025620328405266054506680179777112017848545053849870444533418601160974073534042550398379063909537082574308804866882157248556303120172366151382853558558] = true := by
  decide +kernel

theorem c4 : allCells dirCell 3173 3193 [
    3892075432094770187501457325963247683785888300461790489853809316751304077377117065666, 1, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 3169 3193 :=
  (Cover.one (box := dirCellBox) (n := 3169)
      (.split 2 (.split 3 (.split 2 (.leaf _ k3169_0) (.leaf _ k3169_1)) (.split 2 (.leaf _ k3169_2) (.leaf _ k3169_3))) (.split 3 (.split 1 (.leaf _ k3169_4) (.leaf _ k3169_5)) (.split 1 (.leaf _ k3169_6) (.leaf _ k3169_7))))).trans <|
  (Cover.one (box := dirCellBox) (n := 3170)
      (.split 2 (.split 3 (.split 3 (.leaf _ k3170_0) (.leaf _ k3170_1)) (.leaf _ k3170_2)) (.split 3 (.split 1 (.leaf _ k3170_3) (.leaf _ k3170_4)) (.leaf _ k3170_5)))).trans <|
  (Cover.one (box := dirCellBox) (n := 3171)
      (.split 2 (.leaf _ k3171_0) (.split 3 (.leaf _ k3171_1) (.leaf _ k3171_2)))).trans <|
  (Cover.dir c3).trans <|
  (Cover.dir c4)

end C4.Cert.Dir091
