module

public import C4Check

public section

/-! Cells `3003 ≤ n < 3058` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir077

theorem k3003_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3003) 2).1 3).1
      46032446306214367092781680497038416656083500092).isSome = true := by
  decide +kernel

theorem k3003_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3003) 2).1 3).2
      1001543451916007943374818104501014111544501279924708936975073928982381208564286040259644).isSome = true := by
  decide +kernel

theorem k3003_2 : (checkBoxH dirMode depth (splitBox (dirCellBox 3003) 2).2
      4200659415493903303978760771039330657379022817790473316859740892909644926763606560226856464627).isSome = true := by
  decide +kernel

theorem k3004_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3004) 2).1 1).1
      54207454432798985278819388283479730262853048607936711854120173255740).isSome = true := by
  decide +kernel

theorem k3004_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3004) 2).1 1).2
      54211367753779047848363452910221911534851850152846247329342470634556).isSome = true := by
  decide +kernel

theorem k3004_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3004) 2).2 1).1
      13552239022824008613880464439805092566244784179685296892848001924156).isSome = true := by
  decide +kernel

theorem k3004_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3004) 2).2 1).2
      54209787505976694930798589476810197001904300149581390470990078295100).isSome = true := by
  decide +kernel

theorem k3005_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3005) 2).1 1).1
      13537206111141059771463578477611833824079065035465456897097047882812).isSome = true := by
  decide +kernel

theorem k3005_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3005) 2).1 1).2
      13531654089981282277428529668060082764754256352573238880811332549692).isSome = true := by
  decide +kernel

theorem k3005_2 : (checkBoxH dirMode depth (splitBox (dirCellBox 3005) 2).2
      22271882531501778996759062350561178206240444056650708253175577621160895009188074414137814462037416698208251672061333413590280649788).isSome = true := by
  decide +kernel

theorem k3006_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3006) 2).1
      5696087251095934412153064501154438711586731275567737751980042676795170799926616819815797967510113173787340181813450114124158218257212).isSome = true := by
  decide +kernel

theorem k3006_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 3006) 2).2
      77161595781444242647542303416269619483359551816351695852389020967248224177221504095409256991011374327749049905393).isSome = true := by
  decide +kernel

theorem k3007_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3007) 2).1
      19273627826318979957613853403587531299939611734914053808877173316220852113073763090961694526510269446016264761585).isSome = true := by
  decide +kernel

theorem k3007_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 3007) 2).2
      255087411572533112897965396707087710226704649127168626424116395361551313012491734288941884).isSome = true := by
  decide +kernel

theorem k3008_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3008) 1).1
      996216958377914195840155394530413794749224390165491422060520323242038930611136762725180).isSome = true := by
  decide +kernel

theorem k3008_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 3008) 1).2
      15933295306371878412318647550550658248611192197822176291392787390230623947208646515737404).isSome = true := by
  decide +kernel

theorem k3009_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3009) 1).1
      210749113924669896096614919223425659513479783744236618062329530940).isSome = true := by
  decide +kernel

theorem k3009_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 3009) 1).2
      52693197199625584649191312193382343548350787266393032751942332988).isSome = true := by
  decide +kernel

theorem c7 : allCells dirCell 3010 3011 [
    18362785333035587270054897822567907419468480120648439358913258342376278660105921889319414263061562213424561] = true := by
  decide +kernel

theorem c8 : allCells dirCell 3011 3029 [
    51426516571747517216787758609757879220608444079553689291025297, 147544748564344758644, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] = true := by
  decide +kernel

theorem c9 : allCells dirCell 3029 3030 [
    29838427670252267906639038417720354463608561319343802407163951108187500967913708410515028472101938822993711274494345808488478201842140745980376434454825968498062178887] = true := by
  decide +kernel

theorem k3030_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3030) 3).1
      62851590107609888869461096124498902501155257800303395019745307464903902596533756648626).isSome = true := by
  decide +kernel

theorem k3030_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 3030) 3).2
      1184179315984415313646932492921233131851025708950711566858827931391540707248079940258875804155997235516207346).isSome = true := by
  decide +kernel

theorem k3031_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3031) 2).1
      1396707461741366659363646324698268140222027195344572237954702623684868926885499056331701757704788225775303573463975344883264450801).isSome = true := by
  decide +kernel

theorem k3031_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 3031) 2).2
      5455717539155067578840582395990784062763856411639643091402911032386551224656848820782697552237121391148978810242497783109376817).isSome = true := by
  decide +kernel

theorem k3032_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3032) 2).1
      5575313495389439501753313913558861014125810980092447728661813504300965401896692547106539400512528523124966210272796558674388794428).isSome = true := by
  decide +kernel

theorem k3032_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 3032) 2).2
      5572981553321128559141426624970336025969421102919261803776753804028283977130072161380507368275998128933808612481708748014540927219).isSome = true := by
  decide +kernel

theorem k3033_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3033) 2).1
      301769658554991549351126462569959973364500119068452270401822158084507054421932147568740747363914006415318662204).isSome = true := by
  decide +kernel

theorem k3033_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 3033) 2).2
      3464107776126997356150146813270303480881815377380164278983126252469308).isSome = true := by
  decide +kernel

theorem k3034_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3034) 2).1
      255436637252993440774551619948553624787478286566459164995488682876831248265771421079946044).isSome = true := by
  decide +kernel

theorem k3034_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 3034) 2).2
      255314551824815570145661591699741933199841722965033158810561127218118616487536838853772092).isSome = true := by
  decide +kernel

theorem k3035_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3035) 1).1
      15942460066824849355136527807304935507939558341004474961927488653964748031994608418276156).isSome = true := by
  decide +kernel

theorem k3035_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 3035) 1).2
      3986046539548324064380723374846148530842927860727510090601364658911364888210212194861884).isSome = true := by
  decide +kernel

theorem k3036_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3036) 1).1
      52740047133067886161517732752939136166100875227068036920446939708).isSome = true := by
  decide +kernel

theorem k3036_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 3036) 1).2
      13496566346702082212819494171636721865125926533187779238744651973436).isSome = true := by
  decide +kernel

theorem k3037_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3037) 1).1
      210750349827186652633761051116719582666024250970233709341695265340).isSome = true := by
  decide +kernel

theorem k3037_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 3037) 1).2
      210774808848337429429584285049103555849472684676791535774834608700).isSome = true := by
  decide +kernel

theorem c18 : allCells dirCell 3038 3039 [
    21161612698456797729452604737504905867486355047809356498717218382281586875231363628897762261326541766951796165553253130395057] = true := by
  decide +kernel

theorem c19 : allCells dirCell 3039 3058 [
    51426178393090767240021744790777009726995833969576123958115793, 147543603010689176148, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    13330990160937223608077831095254673489240346847266704014472761607] = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 3003 3058 :=
  (Cover.one (box := dirCellBox) (n := 3003)
      (.split 2 (.split 3 (.leaf _ k3003_0) (.leaf _ k3003_1)) (.leaf _ k3003_2))).trans <|
  (Cover.one (box := dirCellBox) (n := 3004)
      (.split 2 (.split 1 (.leaf _ k3004_0) (.leaf _ k3004_1)) (.split 1 (.leaf _ k3004_2) (.leaf _ k3004_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 3005)
      (.split 2 (.split 1 (.leaf _ k3005_0) (.leaf _ k3005_1)) (.leaf _ k3005_2))).trans <|
  (Cover.one (box := dirCellBox) (n := 3006)
      (.split 2 (.leaf _ k3006_0) (.leaf _ k3006_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 3007)
      (.split 2 (.leaf _ k3007_0) (.leaf _ k3007_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 3008)
      (.split 1 (.leaf _ k3008_0) (.leaf _ k3008_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 3009)
      (.split 1 (.leaf _ k3009_0) (.leaf _ k3009_1))).trans <|
  (Cover.dir c7).trans <|
  (Cover.dir c8).trans <|
  (Cover.dir c9).trans <|
  (Cover.one (box := dirCellBox) (n := 3030)
      (.split 3 (.leaf _ k3030_0) (.leaf _ k3030_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 3031)
      (.split 2 (.leaf _ k3031_0) (.leaf _ k3031_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 3032)
      (.split 2 (.leaf _ k3032_0) (.leaf _ k3032_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 3033)
      (.split 2 (.leaf _ k3033_0) (.leaf _ k3033_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 3034)
      (.split 2 (.leaf _ k3034_0) (.leaf _ k3034_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 3035)
      (.split 1 (.leaf _ k3035_0) (.leaf _ k3035_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 3036)
      (.split 1 (.leaf _ k3036_0) (.leaf _ k3036_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 3037)
      (.split 1 (.leaf _ k3037_0) (.leaf _ k3037_1))).trans <|
  (Cover.dir c18).trans <|
  (Cover.dir c19)

end C4.Cert.Dir077
