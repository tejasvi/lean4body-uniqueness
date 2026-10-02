module

public import C4Check

public section

/-! Cells `3562 ≤ n < 3587` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir116

theorem k3562_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3562) 2).1 2).1
      21239681873096146181718030370976980778723494524462737746445358755907306259191619491920048902498644633869986160445507397109191).isSome = true := by
  decide +kernel

theorem k3562_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3562) 2).1 2).2
      6269033842145599604061794014042748594786373075644726182904543348143540756847817752582436918780590898562468642416840412764552529215780942096446919).isSome = true := by
  decide +kernel

theorem k3562_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3562) 2).2 3).1 1).1
      15627457040925898034773595135192391541229496794154672787844479111272976602528162505074).isSome = true := by
  decide +kernel

theorem k3562_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3562) 2).2 3).1 1).2
      3814986001498006513813365139432865059074216968971056289115741066649079364030193020).isSome = true := by
  decide +kernel

theorem k3562_4 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3562) 2).2 3).2
      115685597600150092658255866242441055501233966906890044167400342645317619659512443956036017680109810787805722453065012942496214035614283069799147332486146119668168177).isSome = true := by
  decide +kernel

theorem k3563_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3563) 2).1
      25051537866915780714026224348614835988839592140666504610302943053539706239937883102556685599834871819529964163011227876704843165652872505861084622).isSome = true := by
  decide +kernel

theorem k3563_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3563) 2).2 3).1
      5307874790005017236267109413907342454262332676507620909939285263589021387109625205958789950490964568343644759646039470406985).isSome = true := by
  decide +kernel

theorem k3563_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3563) 2).2 3).2
      15224407241356652368060256780580901256668797896767611059470098199510954799540269425).isSome = true := by
  decide +kernel

theorem c2 : allCells dirCell 3564 3585 [
    73561646638082102484324728269138580718684321773491822130038049313421698046724253526440443046130177323506694,
    1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] = true := by
  decide +kernel

theorem k3585_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3585) 3).1
      1).isSome = true := by
  decide +kernel

theorem k3585_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3585) 3).2 3).1
      888951536269606958937760347133374436316025469143047717786578241362683522112303142577332831710876273534238).isSome = true := by
  decide +kernel

theorem k3585_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3585) 3).2 3).2 2).1
      22969043904254281168331469268497176747905452644414854508345401773807735120977438593843332584714372999252899084656112632534470).isSome = true := by
  decide +kernel

theorem k3585_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3585) 3).2 3).2 2).2
      263614646980161728205317326672025948850687783523515948939801985247116786998310276422).isSome = true := by
  decide +kernel

theorem k3586_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3586) 3).1 2).1 3).1
      106979630386634475907225635670903751298087725936022282554141864544430875461989438795668809348318859732212156745255030349780200272279737331491894726).isSome = true := by
  decide +kernel

theorem k3586_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3586) 3).1 2).1 3).2
      23498276085137428076973629945842287437026473196004790358132014911588262038434540996646126152871538882258202455608290701663423263430).isSome = true := by
  decide +kernel

theorem k3586_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3586) 3).1 2).2 3).1
      22667026118114791191209309896768921059794470620602795564105691228489599557417418974231881094725194161251886882692463148500422).isSome = true := by
  decide +kernel

theorem k3586_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3586) 3).1 2).2 3).2
      1436261444928904287751888658892112425214945806616784160796706883060939917992474847357522868508355800411967317465272026009216454).isSome = true := by
  decide +kernel

theorem k3586_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3586) 3).2 2).1 2).1 1).1
      4047297030920459878972449319884474577662299199516523388513175746443589349218695878451).isSome = true := by
  decide +kernel

theorem k3586_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3586) 3).2 2).1 2).1 1).2
      4059366413089260437674778120278959864041416777517416551912994021780865041398991558450).isSome = true := by
  decide +kernel

theorem k3586_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3586) 3).2 2).1 2).2 3).1
      1020221617191801420572951904119821049979885062120307104725419399198082993528126667836).isSome = true := by
  decide +kernel

theorem k3586_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3586) 3).2 2).1 2).2 3).2
      1012586085095087962047613813783148921720394490681948844502787777243170041007324363836).isSome = true := by
  decide +kernel

theorem k3586_8 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3586) 3).2 2).2 3).1
      66920910808313729171772168588338800798743336985374641195629598516014808453420703687812294).isSome = true := by
  decide +kernel

theorem k3586_9 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3586) 3).2 2).2 3).2
      1446864699265428716997914907085608500197514240779819489095136292484287774211035074271736779520758345296082289288263037653625887945).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 3562 3587 :=
  (Cover.one (box := dirCellBox) (n := 3562)
      (.split 2 (.split 2 (.leaf _ k3562_0) (.leaf _ k3562_1)) (.split 3 (.split 1 (.leaf _ k3562_2) (.leaf _ k3562_3)) (.leaf _ k3562_4)))).trans <|
  (Cover.one (box := dirCellBox) (n := 3563)
      (.split 2 (.leaf _ k3563_0) (.split 3 (.leaf _ k3563_1) (.leaf _ k3563_2)))).trans <|
  (Cover.dir c2).trans <|
  (Cover.one (box := dirCellBox) (n := 3585)
      (.split 3 (.leaf _ k3585_0) (.split 3 (.leaf _ k3585_1) (.split 2 (.leaf _ k3585_2) (.leaf _ k3585_3))))).trans <|
  (Cover.one (box := dirCellBox) (n := 3586)
      (.split 3 (.split 2 (.split 3 (.leaf _ k3586_0) (.leaf _ k3586_1)) (.split 3 (.leaf _ k3586_2) (.leaf _ k3586_3))) (.split 2 (.split 2 (.split 1 (.leaf _ k3586_4) (.leaf _ k3586_5)) (.split 3 (.leaf _ k3586_6) (.leaf _ k3586_7))) (.split 3 (.leaf _ k3586_8) (.leaf _ k3586_9)))))

end C4.Cert.Dir116
