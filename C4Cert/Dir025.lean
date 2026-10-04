module

public import C4Check

public section

/-! Cells `2047 ≤ n < 2051` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir025

theorem k2047_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2047) 3).1
      189710603453189160785471887490068778874070697038).isSome = true := by
  decide +kernel

theorem k2047_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2047) 3).2 2).1
      5570167362601629515312839256506695476468908239765482563678324303273190761388522316154640037797512276407760635125711066359137415).isSome = true := by
  decide +kernel

theorem k2047_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2047) 3).2 2).2
      15997211656992108111642724503434193569416665057384260492202530559909723577896684705543).isSome = true := by
  decide +kernel

theorem k2048_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2048) 3).1 2).1 3).1
      293870910055026362145359846882716777584408474244415537088970424093434382103558722036150005944137098422533).isSome = true := by
  decide +kernel

theorem k2048_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2048) 3).1 2).1 3).2
      102087588322069333157542467398835572799974583015952099787656243208034481635453815374542015817389913390237900219010877559018627239589797692937064009).isSome = true := by
  decide +kernel

theorem k2048_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2048) 3).1 2).2 3).1
      18381483890878519406087898205369307841348462788681012588751655594966725653876627856013329145392636623185).isSome = true := by
  decide +kernel

theorem k2048_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2048) 3).1 2).2 3).2
      5409392682394201414966356846223105177765625680720933269960724540492993721962860253405478392639790651852952215653525951455601).isSome = true := by
  decide +kernel

theorem k2048_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2048) 3).2 2).1 3).1 1).1
      15472080216201658725647961321218150462055024277388430740329259284334290137581285746).isSome = true := by
  decide +kernel

theorem k2048_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2048) 3).2 2).1 3).1 1).2
      21563003279972578241152851808094713968512141927898974642498627998164086628717078413284366837432099979875410540310810022796722).isSome = true := by
  decide +kernel

theorem k2048_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2048) 3).2 2).1 3).2 1).1
      61757070588172964687090588210104057033914699826960026938632090430580230285435729330).isSome = true := by
  decide +kernel

theorem k2048_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2048) 3).2 2).1 3).2 1).2
      4665549826627299600105883233250065071240864881359907291295534990013757850812793564275111785384035905794738).isSome = true := by
  decide +kernel

theorem k2048_8 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2048) 3).2 2).2 3).1
      407637101633656179871722659624327075375328837226153108966912126105618171866302167100057039073596751087461262028044541406247553968028488763260567621).isSome = true := by
  decide +kernel

theorem k2048_9 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2048) 3).2 2).2 3).2 1).1
      15450326003597655233250904262104863605386260036775199445311388195755883540870051186).isSome = true := by
  decide +kernel

theorem k2048_10 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2048) 3).2 2).2 3).2 1).2
      989471321768074413708336954893626886992192002879210442621330554206346989443970626796).isSome = true := by
  decide +kernel

theorem k2049_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2049) 3).1 2).1 3).1 1).1
      1163924619816076360613048248193794372286575114843395814301081934081628490306228703014024456979710596413833).isSome = true := by
  decide +kernel

theorem k2049_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2049) 3).1 2).1 3).1 1).2
      63087126733124012359615360927067921515053810585189453668732541490992529912009938984114).isSome = true := by
  decide +kernel

theorem k2049_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2049) 3).1 2).1 3).2 1).1
      62985771398917749261855701288274653213155211022550542565022011586121953281650936470706).isSome = true := by
  decide +kernel

theorem k2049_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2049) 3).1 2).1 3).2 1).2
      251934916695365313303411866175345924815601033796409237671040443164848656064881102253234).isSome = true := by
  decide +kernel

theorem k2049_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2049) 3).1 2).2 3).1 1).1
      61745727571388892384092917946561463364064652066742665205818876888308042476320593330).isSome = true := by
  decide +kernel

theorem k2049_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2049) 3).1 2).2 3).1 1).2
      246653605612292356540191857281936568833944331529753044547756806303287012911098723756).isSome = true := by
  decide +kernel

theorem k2049_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2049) 3).1 2).2 3).2 1).1
      246235810679450732130964905831847877418825622529591880056055947560516595696937827756).isSome = true := by
  decide +kernel

theorem k2049_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2049) 3).1 2).2 3).2 1).2
      3939411283425086867946855283305573441270213099534175030422280451997541606660804836524).isSome = true := by
  decide +kernel

theorem k2049_8 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2049) 3).2 2).1 3).1 1).1
      62942506697911879274203202820471098053964458958418598410879765389744999903505762309937).isSome = true := by
  decide +kernel

theorem k2049_9 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2049) 3).2 2).1 3).1 1).2
      62889723453023446416769168594832626644196262891108314454322485133034581472185929063218).isSome = true := by
  decide +kernel

theorem k2049_10 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2049) 3).2 2).1 3).2 1).1
      3926103595322272398978474406373611961253941411782260854672505725453424175815185372978).isSome = true := by
  decide +kernel

theorem k2049_11 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2049) 3).2 2).1 3).2 1).2
      15700366094447252629721303514500264398338693451529508613282089322728453217486943669196).isSome = true := by
  decide +kernel

theorem k2049_12 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2049) 3).2 2).2 3).1 1).1
      13326867754033436784355950711399977837596544079093980925401857196).isSome = true := by
  decide +kernel

theorem k2049_13 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2049) 3).2 2).2 3).1 1).2
      3933315815967920038849159241426061999103420523029563853358004155628038451077664173868).isSome = true := by
  decide +kernel

theorem k2049_14 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2049) 3).2 2).2 3).2 1).1
      13322888604835843827874852415290188741470002788893307544612265772).isSome = true := by
  decide +kernel

theorem k2049_15 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2049) 3).2 2).2 3).2 1).2
      15729135608792362430529608513907484269334242537914369524907099220957596653137843018546).isSome = true := by
  decide +kernel

theorem k2050_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2050) 3).1 2).1 3).1 1).1
      15702715675151894604924573045735910451191779100453643761326032534126363620447244802866).isSome = true := by
  decide +kernel

theorem k2050_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2050) 3).1 2).1 3).1 1).2
      3920959602317209915001681395225717608284952332179104097860827933869893616801569928140).isSome = true := by
  decide +kernel

theorem k2050_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2050) 3).1 2).1 3).2 1).1
      62679048691557412481562897306310983044071177344102745326066786449467217195471158139698).isSome = true := by
  decide +kernel

theorem k2050_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2050) 3).1 2).1 3).2 1).2
      62665517604321917457577503193560053743201351089164931970879373505100588585430422205388).isSome = true := by
  decide +kernel

theorem k2050_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2050) 3).1 2).2 3).1 1).1
      3924032912531509640030856146458609583566691630319192123136285262678732762315676751666).isSome = true := by
  decide +kernel

theorem k2050_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2050) 3).1 2).2 3).1 1).2
      212911582043427566131315300289946560223606793656618626144803351340).isSome = true := by
  decide +kernel

theorem k2050_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2050) 3).1 2).2 3).2 1).1
      2882071580641189577090943347826971982854310860).isSome = true := by
  decide +kernel

theorem k2050_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2050) 3).1 2).2 3).2 1).2
      979911674785925439086797115655793549866640586786531386200694419548697826386755083980).isSome = true := by
  decide +kernel

theorem k2050_8 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2050) 3).2 2).1 3).1 1).1
      978387453307598550858095738003820877747353862106077965817309041246485103009766824652).isSome = true := by
  decide +kernel

theorem k2050_9 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2050) 3).2 2).1 3).1 1).2
      3913398273952294475163175340251497104817048516518166238788643157161465713863024958156).isSome = true := by
  decide +kernel

theorem k2050_10 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2050) 3).2 2).1 3).2 1).1
      244664029636395851031475124871350773121629543960799700586968023563641248312389400268).isSome = true := by
  decide +kernel

theorem k2050_11 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2050) 3).2 2).1 3).2 1).2
      978654994548200199106367404034705866689227517220431928451234449486366265421800535756).isSome = true := by
  decide +kernel

theorem k2050_12 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2050) 3).2 2).2 3).1
      349276208783402090897024601514875749281160681174474857691208977629806105895730283591511909659770710023722241795795848362756369201).isSome = true := by
  decide +kernel

theorem k2050_13 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2050) 3).2 2).2 3).2
      21834839540389929880987044623240927274420091146836155979477077810310514114086925275080863061330172183385486740004838571798551345).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 2047 2051 :=
  (Cover.one (box := dirCellBox) (n := 2047)
      (.split 3 (.leaf _ k2047_0) (.split 2 (.leaf _ k2047_1) (.leaf _ k2047_2)))).trans <|
  (Cover.one (box := dirCellBox) (n := 2048)
      (.split 3 (.split 2 (.split 3 (.leaf _ k2048_0) (.leaf _ k2048_1)) (.split 3 (.leaf _ k2048_2) (.leaf _ k2048_3))) (.split 2 (.split 3 (.split 1 (.leaf _ k2048_4) (.leaf _ k2048_5)) (.split 1 (.leaf _ k2048_6) (.leaf _ k2048_7))) (.split 3 (.leaf _ k2048_8) (.split 1 (.leaf _ k2048_9) (.leaf _ k2048_10)))))).trans <|
  (Cover.one (box := dirCellBox) (n := 2049)
      (.split 3 (.split 2 (.split 3 (.split 1 (.leaf _ k2049_0) (.leaf _ k2049_1)) (.split 1 (.leaf _ k2049_2) (.leaf _ k2049_3))) (.split 3 (.split 1 (.leaf _ k2049_4) (.leaf _ k2049_5)) (.split 1 (.leaf _ k2049_6) (.leaf _ k2049_7)))) (.split 2 (.split 3 (.split 1 (.leaf _ k2049_8) (.leaf _ k2049_9)) (.split 1 (.leaf _ k2049_10) (.leaf _ k2049_11))) (.split 3 (.split 1 (.leaf _ k2049_12) (.leaf _ k2049_13)) (.split 1 (.leaf _ k2049_14) (.leaf _ k2049_15)))))).trans <|
  (Cover.one (box := dirCellBox) (n := 2050)
      (.split 3 (.split 2 (.split 3 (.split 1 (.leaf _ k2050_0) (.leaf _ k2050_1)) (.split 1 (.leaf _ k2050_2) (.leaf _ k2050_3))) (.split 3 (.split 1 (.leaf _ k2050_4) (.leaf _ k2050_5)) (.split 1 (.leaf _ k2050_6) (.leaf _ k2050_7)))) (.split 2 (.split 3 (.split 1 (.leaf _ k2050_8) (.leaf _ k2050_9)) (.split 1 (.leaf _ k2050_10) (.leaf _ k2050_11))) (.split 3 (.leaf _ k2050_12) (.leaf _ k2050_13)))))

end C4.Cert.Dir025
