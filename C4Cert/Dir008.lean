module

public import C4Check

public section

/-! Cells `1269 ≤ n < 1324` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir008

theorem k1269_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 1269) 3).1
      1204843141629154736319966341702337081682154564508915741589458832582872596608661738706421327163243494038473428166).isSome = true := by
  decide +kernel

theorem k1269_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 1269) 3).2
      4704306191162981595268777964915216503973527321321710980004773735958152841908152509397015624693059683871945522).isSome = true := by
  decide +kernel

theorem k1270_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 1270) 3).1
      3982389167657737660293198610532947431916934344755663914028239148600753252439645255988018).isSome = true := by
  decide +kernel

theorem k1270_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 1270) 3).2
      3981946739979762184448400054408162944007627533283580571756761205577875055796531605017798).isSome = true := by
  decide +kernel

theorem k1271_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 1271) 2).1
      242904794318248447860107876887433070960562396017248944516547083050164823020082579825).isSome = true := by
  decide +kernel

theorem k1271_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 1271) 2).2
      242902291671435385315622082309595594200327998211976973384566602601147373605043292529).isSome = true := by
  decide +kernel

theorem c3 : allCells dirCell 1272 1294 [
    2360262043645955594817, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 51] = true := by
  decide +kernel

theorem k1294_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 1294) 3).1
      830710012509906223402239727545197381734862423081774426409735430).isSome = true := by
  decide +kernel

theorem k1294_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 1294) 3).2
      21327530005437613695402187491858912540015405813135399052297359963197499644106097620799635797369915610599466758347021206346566).isSome = true := by
  decide +kernel

theorem k1295_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 1295) 3).1
      402205536371264129859835753185523093843888229370896817971740907876792305498631673097204325284975644137606211703629647865005725534873120337337066950).isSome = true := by
  decide +kernel

theorem k1295_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 1295) 3).2
      102818867198298137909597329215708844941646904375825082881756567644879344343812474456057735726873383081138220333423993499517024044417453243674379284722).isSome = true := by
  decide +kernel

theorem k1296_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 1296) 3).1
      86984277217404453880404171565511497570656753538123722927111538281474199477682332951885364518144105200327226089601099585000263474).isSome = true := by
  decide +kernel

theorem k1296_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 1296) 3).2
      75399797930506119357026391821223426421260382313534178790838134214628785736958998831324864792712229809324182726).isSome = true := by
  decide +kernel

theorem k1297_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 1297) 3).1
      15948990147768974010248617078242527985020818951207349873049397337121560160847988952255282).isSome = true := by
  decide +kernel

theorem k1297_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 1297) 3).2
      15939558706095755867520876731708915264270994206940233251867639872294976391680824321624882).isSome = true := by
  decide +kernel

theorem k1298_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 1298) 3).1
      3983259033036605211867831204907285363887526640892274495135970767819848906910491438598961).isSome = true := by
  decide +kernel

theorem k1298_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 1298) 3).2
      3889239238768882123304863602963958527735444549997652127623000234287955733591941240625).isSome = true := by
  decide +kernel

theorem c9 : allCells dirCell 1299 1316 [
    99917458569730753111876721344700637018580294609410889710124305029800053677145061539437128613704451408372593582785401127455173436142976295417939399,
    2360164212402562583361, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] = true := by
  decide +kernel

theorem c10 : allCells dirCell 1316 1323 [
    0, 0, 0, 0, 0, 51,
    475758499071906418887130201698398159560722992726340460323284846293591976305824154600461690333093358041190768777004249882383672611916349405127562895710934393650644808839] = true := by
  decide +kernel

theorem k1323_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 1323) 3).1
      340758411671743140993456198498263069951020867929304364810478796159170412624718406677106201190818147420926907482750723274142962).isSome = true := by
  decide +kernel

theorem k1323_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 1323) 3).2
      73810487897821369191403691740492692542960075955038063274152476050924269421072602012944598147830421053098226).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 1269 1324 :=
  (Cover.one (box := dirCellBox) (n := 1269)
      (.split 3 (.leaf _ k1269_0) (.leaf _ k1269_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 1270)
      (.split 3 (.leaf _ k1270_0) (.leaf _ k1270_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 1271)
      (.split 2 (.leaf _ k1271_0) (.leaf _ k1271_1))).trans <|
  (Cover.dir c3).trans <|
  (Cover.one (box := dirCellBox) (n := 1294)
      (.split 3 (.leaf _ k1294_0) (.leaf _ k1294_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 1295)
      (.split 3 (.leaf _ k1295_0) (.leaf _ k1295_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 1296)
      (.split 3 (.leaf _ k1296_0) (.leaf _ k1296_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 1297)
      (.split 3 (.leaf _ k1297_0) (.leaf _ k1297_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 1298)
      (.split 3 (.leaf _ k1298_0) (.leaf _ k1298_1))).trans <|
  (Cover.dir c9).trans <|
  (Cover.dir c10).trans <|
  (Cover.one (box := dirCellBox) (n := 1323)
      (.split 3 (.leaf _ k1323_0) (.leaf _ k1323_1)))

end C4.Cert.Dir008
