module

public import C4Check

public section

/-! Cells `3531 ≤ n < 3557` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir105

theorem k3531_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3531) 2).1 3).1 2).1 3).1
      74734223446419440547885359274550482885087409135127984059226502425024623228119483907342136517916718702302998).isSome = true := by
  decide +kernel

theorem k3531_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3531) 2).1 3).1 2).1 3).2
      855397568885105727999658168565061753392482508547046413626854143254).isSome = true := by
  decide +kernel

theorem k3531_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3531) 2).1 3).1 2).2 3).1
      6521471778885158197153713871535923951440593491324300390329930631852479416800257447198754016832559855081233056158056799825821695760451914995101538070).isSome = true := by
  decide +kernel

theorem k3531_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3531) 2).1 3).1 2).2 3).2
      22027401474304627303167465479529587836974088373467290201938546328507484607557251369732544867502643890695788488237311621630056214).isSome = true := by
  decide +kernel

theorem k3531_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3531) 2).1 3).2 2).1
      65228549733428125908251852117847331095365662091621980483779906648401674091869140163539225657957186629996889619715412575007840023).isSome = true := by
  decide +kernel

theorem k3531_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3531) 2).1 3).2 2).2 3).1
      3160369014027563677733060666307001407632621475332045383425927826513148166919732516297).isSome = true := by
  decide +kernel

theorem k3531_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3531) 2).1 3).2 2).2 3).2
      789942013384109839987601790517059857275822545079876983065000736794822079398288664005).isSome = true := by
  decide +kernel

theorem k3531_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3531) 2).2 3).1 2).1 3).1 2).1
      1219316631497307353420668780670621809447248924927069102089358726607119675513216046797).isSome = true := by
  decide +kernel

theorem k3531_8 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3531) 2).2 3).1 2).1 3).1 2).2
      1172503139972009676090190359732315653816519063746451061441919064326653681721505911823561648159911858824901).isSome = true := by
  decide +kernel

theorem k3531_9 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3531) 2).2 3).1 2).1 3).2
      416724831091058936120516154734693961516139803812593644832010666747665505110670850250679049662561970152707266665372648303925103331006657099195111536326).isSome = true := by
  decide +kernel

theorem k3531_10 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3531) 2).2 3).1 2).2 3).1 2).1
      752113822703686304466092309825297613194414336446272882793126657065913985011506260462257).isSome = true := by
  decide +kernel

theorem k3531_11 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3531) 2).2 3).1 2).2 3).1 2).2
      254833159340055178360510942473533324462503450745533666547396408699680529707490831889073).isSome = true := by
  decide +kernel

theorem k3531_12 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3531) 2).2 3).1 2).2 3).2 2).1
      216407955860497153131100833339111963204457639199341998002294187678864249592272553476727936159372265487793).isSome = true := by
  decide +kernel

theorem k3531_13 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3531) 2).2 3).1 2).2 3).2 2).2
      1170110823279030845197565604912496068254789406276264492095479126254203145626024957218745995698276241341873).isSome = true := by
  decide +kernel

theorem k3531_14 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3531) 2).2 3).2 2).1 3).1
      119723488168128018188911844220267644398769578277037734468369033680295216062936930730856210585422543578926597106601664716794467625569988541190547961331858221678300877765).isSome = true := by
  decide +kernel

theorem k3531_15 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3531) 2).2 3).2 2).1 3).2
      342791846132756253146098794985515449820782129505033934966177976398038900658282550753285041608226746939713902029871523373110213).isSome = true := by
  decide +kernel

theorem k3531_16 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3531) 2).2 3).2 2).2 3).1 1).1
      21526724394866841321561047725494614523192103900201888195719244581934105561001969211036762990268281728527137368774851841514930).isSome = true := by
  decide +kernel

theorem k3531_17 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3531) 2).2 3).2 2).2 3).1 1).2
      2268007477452109570432765399764259205438833).isSome = true := by
  decide +kernel

theorem k3531_18 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3531) 2).2 3).2 2).2 3).2 1).1
      5376315922074509265954561690534965367406724473092402250246495562793707010243567831033394754920735351748219747274679022769980).isSome = true := by
  decide +kernel

theorem k3531_19 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3531) 2).2 3).2 2).2 3).2 1).2
      2267380239878566450145624619332458515775857).isSome = true := by
  decide +kernel

theorem k3532_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3532) 2).1 2).1
      31158136789651272247348192864085119012470935840408171469907636613228038959441064237818664932980601738401077770074595150637206440710481031165985413833396859741756715955860699).isSome = true := by
  decide +kernel

theorem k3532_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3532) 2).1 2).2 3).1
      18035166931962157507447675372938363610071432569093036506905916794779085201631530802861029724664314260209515143667293893986958907159).isSome = true := by
  decide +kernel

theorem k3532_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3532) 2).1 2).2 3).2
      12938023601214151161489089203821966282563079201489685760162428308837495471600588369020359).isSome = true := by
  decide +kernel

theorem k3532_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3532) 2).2 3).1 2).1 3).1
      982049981055600771000698071553783209265949327717089636031239063864751575776808760561).isSome = true := by
  decide +kernel

theorem k3532_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3532) 2).2 3).1 2).1 3).2
      3922790466997211221694001496456917311069897153855588046140149900984248317188468232945).isSome = true := by
  decide +kernel

theorem k3532_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3532) 2).2 3).1 2).2 3).1
      342907663444817506179908596320524680068176033967787147426611728689491852927209820815458685276834860823990949971435603317216177).isSome = true := by
  decide +kernel

theorem k3532_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3532) 2).2 3).1 2).2 3).2
      72420513778189436307738400744517335337052094571126814005505086596067294111644879336006443147816985785585).isSome = true := by
  decide +kernel

theorem k3532_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3532) 2).2 3).2 2).1
      25164607015326411133002005390091163521593923870094672124931750404036119633898748261604581801321384840314007965642106165644079674092356066028640023).isSome = true := by
  decide +kernel

theorem k3532_8 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3532) 2).2 3).2 2).2 3).1
      72326870270897517159358592777822764805630751620238698875533304074611356115118618134868853901945303037169).isSome = true := by
  decide +kernel

theorem k3532_9 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3532) 2).2 3).2 2).2 3).2
      289003500224485026537931497074093691557741097686708106548782913213735610466279697173563869800202484699889).isSome = true := by
  decide +kernel

theorem k3533_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3533) 2).1
      99995942334411923437219536747107232397569279831073624158).isSome = true := by
  decide +kernel

theorem k3533_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3533) 2).2 2).1
      1897416380107125422670314277519567436832246232727013422092237266842766043878412081819435928727839465774140021152598572114843199319415229767235848050296183699463971247895).isSome = true := by
  decide +kernel

theorem k3533_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3533) 2).2 2).2 3).1
      6283600969402472809749189879456297892738040598935731332179695256616667055965784451961164808067550149620485644675260598129631973992176094008203213).isSome = true := by
  decide +kernel

theorem k3533_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3533) 2).2 2).2 3).2
      18036123956567010829456795998728173517296555138945955710485602249013885092186034689138486104382169007565).isSome = true := by
  decide +kernel

theorem c3 : allCells dirCell 3534 3557 [
    34355201909506125018442523163786614986106449808488409681151215672521478463745257010764032927424006,
    1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1] = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 3531 3557 :=
  (Cover.one (box := dirCellBox) (n := 3531)
      (.split 2 (.split 3 (.split 2 (.split 3 (.leaf _ k3531_0) (.leaf _ k3531_1)) (.split 3 (.leaf _ k3531_2) (.leaf _ k3531_3))) (.split 2 (.leaf _ k3531_4) (.split 3 (.leaf _ k3531_5) (.leaf _ k3531_6)))) (.split 3 (.split 2 (.split 3 (.split 2 (.leaf _ k3531_7) (.leaf _ k3531_8)) (.leaf _ k3531_9)) (.split 3 (.split 2 (.leaf _ k3531_10) (.leaf _ k3531_11)) (.split 2 (.leaf _ k3531_12) (.leaf _ k3531_13)))) (.split 2 (.split 3 (.leaf _ k3531_14) (.leaf _ k3531_15)) (.split 3 (.split 1 (.leaf _ k3531_16) (.leaf _ k3531_17)) (.split 1 (.leaf _ k3531_18) (.leaf _ k3531_19))))))).trans <|
  (Cover.one (box := dirCellBox) (n := 3532)
      (.split 2 (.split 2 (.leaf _ k3532_0) (.split 3 (.leaf _ k3532_1) (.leaf _ k3532_2))) (.split 3 (.split 2 (.split 3 (.leaf _ k3532_3) (.leaf _ k3532_4)) (.split 3 (.leaf _ k3532_5) (.leaf _ k3532_6))) (.split 2 (.leaf _ k3532_7) (.split 3 (.leaf _ k3532_8) (.leaf _ k3532_9)))))).trans <|
  (Cover.one (box := dirCellBox) (n := 3533)
      (.split 2 (.leaf _ k3533_0) (.split 2 (.leaf _ k3533_1) (.split 3 (.leaf _ k3533_2) (.leaf _ k3533_3))))).trans <|
  (Cover.dir c3)

end C4.Cert.Dir105
