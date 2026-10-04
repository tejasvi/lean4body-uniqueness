module

public import C4Check

public section

/-! Cells `3283 ≤ n < 3308` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir097

theorem k3283_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3283) 2).1 3).1 1).1
      1001479319308372502817272810093244300755358694314265416982055618597504541564769750694972).isSome = true := by
  decide +kernel

theorem k3283_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3283) 2).1 3).1 1).2
      16021988786010258370612247208907284527905583184509182466124017821138856868701032064695356).isSome = true := by
  decide +kernel

theorem k3283_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3283) 2).1 3).2 1).1
      1000255112076455425313112475493696511232126184942903243856972803020511470001536406174780).isSome = true := by
  decide +kernel

theorem k3283_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3283) 2).1 3).2 1).2
      3388597384757792365832882046242694214332457204042010010198461955132).isSome = true := by
  decide +kernel

theorem k3283_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3283) 2).2 3).1 1).1
      11786725346226164257489556291482619522790919453756).isSome = true := by
  decide +kernel

theorem k3283_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3283) 2).2 3).1 1).2
      15652483771448199426401430226857191311200408680097295862695153584580658568924036981708).isSome = true := by
  decide +kernel

theorem k3283_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3283) 2).2 3).2 1).1
      183756024687487213032686893589960672164776197180).isSome = true := by
  decide +kernel

theorem k3283_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3283) 2).2 3).2 1).2
      13572937508419518140628085973157097148711565519683078223902415469628).isSome = true := by
  decide +kernel

theorem k3284_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3284) 2).1 3).1 1).1
      3385487830961083146264286032268041549278623903922948577890127363132).isSome = true := by
  decide +kernel

theorem k3284_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3284) 2).1 3).1 1).2
      15612670492518435730364843175190980362152587644672001649161467997776477600401149770812).isSome = true := by
  decide +kernel

theorem k3284_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3284) 2).1 3).2 1).1
      845687279337540348075594989395795651998033413280765661236298562620).isSome = true := by
  decide +kernel

theorem k3284_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3284) 2).1 3).2 1).2
      3382689557070446616783723800581180056806669754037447583154587941948).isSome = true := by
  decide +kernel

theorem k3284_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3284) 2).2 3).1 1).1
      846629379328769489142006291622429159699055893605986870899236092988).isSome = true := by
  decide +kernel

theorem k3284_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3284) 2).2 3).1 1).2
      3386315036844495314571612823848202406929269194333362353572752964668).isSome = true := by
  decide +kernel

theorem k3284_6 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3284) 2).2 3).2
      356338206457211999215888605468669285474751591447936933178135818052226785220746324060172708551365165147424142503878744233550314912828).isSome = true := by
  decide +kernel

theorem k3285_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3285) 2).1 3).1
      89049612244728126520666753789459267661224327451146204700606592343121959457988958922113734474102010598148197229774702644703659803452).isSome = true := by
  decide +kernel

theorem k3285_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3285) 2).1 3).2
      301404275136322488966001187170574140890222993635849509570866720282505311862513424014082503685708199379959214321).isSome = true := by
  decide +kernel

theorem k3285_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3285) 2).2 3).1
      301617445641941469492012587408882976946494641460439342697193128113067515656276313769399326941286151829222243388).isSome = true := by
  decide +kernel

theorem k3285_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3285) 2).2 3).2
      4710095056431352837432410941514743060082278572876914486586963933882414433149953622231755157011224400502111292).isSome = true := by
  decide +kernel

theorem k3286_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3286) 2).1 3).1
      73551961902332959840177297522547263244486203119082002672024256082384064957238498835616488815973703727561788).isSome = true := by
  decide +kernel

theorem k3286_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3286) 2).1 3).2
      294097133078732953943438850101993309173325210526204459535169082394273085388804062341527666349011254193798204).isSome = true := by
  decide +kernel

theorem k3286_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3286) 2).2 3).1
      15950550298897555144610956150686968945822546578856024210716238115164000465319406238612540).isSome = true := by
  decide +kernel

theorem k3286_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3286) 2).2 3).2
      3986084167340623402677369708035003145827461392456236475151658132267860215729952841841724).isSome = true := by
  decide +kernel

theorem k3287_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3287) 2).1 3).1
      1148455761652827819229210344272735239484801680836209354871518365771644991731630696582876230293617840602172).isSome = true := by
  decide +kernel

theorem k3287_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3287) 2).1 3).2
      3890092270047518423098236837385852454000476031999667586967075009381049710891662425148).isSome = true := by
  decide +kernel

theorem k3287_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3287) 2).2 3).1
      18376573607793131371976460150357166866184805179935780001484382453267233867089568353249213053103429010635836).isSome = true := by
  decide +kernel

theorem k3287_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3287) 2).2 3).2
      62245165398844825174772341888339716121177485531647828446373000577668761368799945210940).isSome = true := by
  decide +kernel

theorem k3288_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3288) 3).1 1).1
      52708327393174331140111591780122767537586147223070127387943218236).isSome = true := by
  decide +kernel

theorem k3288_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3288) 3).1 1).2
      210940567096627941891969322463634289828699567979678365648499817532).isSome = true := by
  decide +kernel

theorem k3288_2 : (checkBoxH dirMode depth (splitBox (dirCellBox 3288) 3).2
      346870281060202472208854354577051477353980390104892222885103403395047614728223889413870463848402961694067762291052737007959006001).isSome = true := by
  decide +kernel

theorem k3289_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3289) 3).1
      5419030425742621029996958761123385082808744771945860708770950639759082082007420539232921675863381352012905325116154217575602993).isSome = true := by
  decide +kernel

theorem k3289_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 3289) 3).2
      1174890651618553479219978737821215899465393254284554917799623802874615341504734435539987432225633310435274994).isSome = true := by
  decide +kernel

theorem k3290_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3290) 2).1
      15546661229106394010012565572899557663199057861132301411959477396471671770401698748209).isSome = true := by
  decide +kernel

theorem k3290_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 3290) 2).2
      4588717238738385125767286082125016757600477991566423223236248058302382464309006130530607098426125786143537).isSome = true := by
  decide +kernel

theorem c8 : allCells dirCell 3291 3292 [
    102312699792837351816551751155752543235109670532805535301672688718341690281033339021036311712466420314789726035024502142429601822423539781516006022349] = true := by
  decide +kernel

theorem c9 : allCells dirCell 3292 3307 [
    15541461759032592780484004140246800411618343330097848443509711693445299261713029857609,
    2360980517325658898753, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] = true := by
  decide +kernel

theorem k3307_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3307) 3).1
      135383345723447209679427172980555626835702279).isSome = true := by
  decide +kernel

theorem k3307_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 3307) 3).2
      30282774970489891344643291695967296699568219887357502730339869144103616536405939956278520604545469663200448861889412439205201498589782819839713085981152910931977672142).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 3283 3308 :=
  (Cover.one (box := dirCellBox) (n := 3283)
      (.split 2 (.split 3 (.split 1 (.leaf _ k3283_0) (.leaf _ k3283_1)) (.split 1 (.leaf _ k3283_2) (.leaf _ k3283_3))) (.split 3 (.split 1 (.leaf _ k3283_4) (.leaf _ k3283_5)) (.split 1 (.leaf _ k3283_6) (.leaf _ k3283_7))))).trans <|
  (Cover.one (box := dirCellBox) (n := 3284)
      (.split 2 (.split 3 (.split 1 (.leaf _ k3284_0) (.leaf _ k3284_1)) (.split 1 (.leaf _ k3284_2) (.leaf _ k3284_3))) (.split 3 (.split 1 (.leaf _ k3284_4) (.leaf _ k3284_5)) (.leaf _ k3284_6)))).trans <|
  (Cover.one (box := dirCellBox) (n := 3285)
      (.split 2 (.split 3 (.leaf _ k3285_0) (.leaf _ k3285_1)) (.split 3 (.leaf _ k3285_2) (.leaf _ k3285_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 3286)
      (.split 2 (.split 3 (.leaf _ k3286_0) (.leaf _ k3286_1)) (.split 3 (.leaf _ k3286_2) (.leaf _ k3286_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 3287)
      (.split 2 (.split 3 (.leaf _ k3287_0) (.leaf _ k3287_1)) (.split 3 (.leaf _ k3287_2) (.leaf _ k3287_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 3288)
      (.split 3 (.split 1 (.leaf _ k3288_0) (.leaf _ k3288_1)) (.leaf _ k3288_2))).trans <|
  (Cover.one (box := dirCellBox) (n := 3289)
      (.split 3 (.leaf _ k3289_0) (.leaf _ k3289_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 3290)
      (.split 2 (.leaf _ k3290_0) (.leaf _ k3290_1))).trans <|
  (Cover.dir c8).trans <|
  (Cover.dir c9).trans <|
  (Cover.one (box := dirCellBox) (n := 3307)
      (.split 3 (.leaf _ k3307_0) (.leaf _ k3307_1)))

end C4.Cert.Dir097
