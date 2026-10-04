module

public import C4Check

public section

/-! Cells `2832 ≤ n < 2834` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir068

theorem k2832_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2832) 3).1 2).1 3).1 2).1
      65125714513255316441988691791411055564853526162840829530617603310553215197065817360541361).isSome = true := by
  decide +kernel

theorem k2832_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2832) 3).1 2).1 3).1 2).2
      4072913103488158351741659470941226514091399010872163477453329953176227801924603833591473).isSome = true := by
  decide +kernel

theorem k2832_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2832) 3).1 2).1 3).2 2).1
      16624398178018417381022233722143045625285721597399317413786154826823313313443891565685516529).isSome = true := by
  decide +kernel

theorem k2832_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2832) 3).1 2).1 3).2 2).2
      64979201422877944468631392153697397956360310127132701549984340703419509872143775912335601).isSome = true := by
  decide +kernel

theorem k2832_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2832) 3).1 2).2 3).1 1).1
      15932727722764123310734274892450881220450853942236500421316565950351746924768784115378).isSome = true := by
  decide +kernel

theorem k2832_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2832) 3).1 2).2 3).1 1).2
      18804905147220412145463228716147045540378207249457982611616453304535815118681172024295700244858868318435762).isSome = true := by
  decide +kernel

theorem k2832_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2832) 3).1 2).2 3).2 1).1
      4068061085172225821206261907923085261961906756677666828979960398681253843093378139802428).isSome = true := by
  decide +kernel

theorem k2832_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2832) 3).1 2).2 3).2 1).2
      65043542221783270622388400749622221137386563543050014066964202955287967893643524916611314).isSome = true := by
  decide +kernel

theorem k2832_8 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2832) 3).2 2).1 3).1 2).1
      265330063276906007726261589084756766874739147300116437156764086145281115757040629810715937009).isSome = true := by
  decide +kernel

theorem k2832_9 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2832) 3).2 2).1 3).1 2).2
      4148379404886881275022997715278246444966778992713827452883100357554548787129653634558036209).isSome = true := by
  decide +kernel

theorem k2832_10 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2832) 3).2 2).1 3).2 1).1
      16562207700891609505924434988248380145564914103406116960111691356339179284396221748830662898).isSome = true := by
  decide +kernel

theorem k2832_11 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2832) 3).2 2).1 3).2 1).2
      66232611612742277061490640055799705586939372424481613138433094553592885402592059996455235826).isSome = true := by
  decide +kernel

theorem k2832_12 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2832) 3).2 2).2 3).1 2).1
      64851134942360233351786870901082963166780775045696590149125543009954004375191033503717617).isSome = true := by
  decide +kernel

theorem k2832_13 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2832) 3).2 2).2 3).1 2).2
      4056268978134322926582488067092577874334239810795698383336237892583868489585001748050748).isSome = true := by
  decide +kernel

theorem k2832_14 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2832) 3).2 2).2 3).2 1).1
      74653786071575662816592092426600489120735686557147132701528560415659234129601218974744925030736491913927228).isSome = true := by
  decide +kernel

theorem k2832_15 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2832) 3).2 2).2 3).2 1).2
      66296159195912310417558096305228348117395618316184801748428284649910540427400948909591742706).isSome = true := by
  decide +kernel

theorem k2833_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2833) 3).1 2).1 3).1 1).1
      4133078555775877459609941841791370004709787308724221509143153946385224017695561826376741106).isSome = true := by
  decide +kernel

theorem k2833_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2833) 3).1 2).1 3).1 1).2
      66105051389792677472097422791182854562602600162053441090772237565428337223857831067570860274).isSome = true := by
  decide +kernel

theorem k2833_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2833) 3).1 2).1 3).2 1).1
      66026610062405990499601344726023659597303017302550727030630373575192943622050093022993117426).isSome = true := by
  decide +kernel

theorem k2833_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2833) 3).1 2).1 3).2 1).2
      4754839349224729139231496487854238440767865818566738319094848536827296439447130909398796905856452196975230012).isSome = true := by
  decide +kernel

theorem k2833_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2833) 3).1 2).2 3).1 1).1
      1009728787292215143132274502122930709424840191841385308339444346526275441907139073536572).isSome = true := by
  decide +kernel

theorem k2833_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2833) 3).1 2).2 3).1 1).2
      4135720606340664776394306878312989384526917755064035543622953041492190210662583216311234802).isSome = true := by
  decide +kernel

theorem k2833_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2833) 3).1 2).2 3).2 1).1
      1008089395018451914121198575532748011109802539982050663511479091005007587372699081437756).isSome = true := by
  decide +kernel

theorem k2833_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2833) 3).1 2).2 3).2 1).2
      4128941706874448511262590474192009367834658788115886770767378769853581491444278283848773874).isSome = true := by
  decide +kernel

theorem k2833_8 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2833) 3).2 2).1 3).1 1).1
      257459932950813306352224036554052153092215699677500595075819563731217332512076642836650802).isSome = true := by
  decide +kernel

theorem k2833_9 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2833) 3).2 2).1 3).1 1).2
      296758533828133734033124544134445892585586132032427718831428246145726952036494678991953595691436762130594876).isSome = true := by
  decide +kernel

theorem k2833_10 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2833) 3).2 2).1 3).2 1).1
      218006773803798067804926867845468794559784083000110971103345982499900).isSome = true := by
  decide +kernel

theorem k2833_11 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2833) 3).2 2).1 3).2 1).2
      296407213242159392599547966452089584090007346770439841958783977603719801680215869214474134942340231647247420).isSome = true := by
  decide +kernel

theorem k2833_12 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2833) 3).2 2).2 3).1 1).1
      3410305705385235626172282802884278266548978563500102908491482381372).isSome = true := by
  decide +kernel

theorem k2833_13 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2833) 3).2 2).2 3).1 1).2
      4025287448497782078624663274882274241574883123346000393674995096035963773988745856334908).isSome = true := by
  decide +kernel

theorem k2833_14 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2833) 3).2 2).2 3).2 1).1
      13622045340452160219119939370750222449424367118574618021437847551036).isSome = true := by
  decide +kernel

theorem k2833_15 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2833) 3).2 2).2 3).2 1).2
      2956116873858916424976889459827420936800312671292).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 2832 2834 :=
  (Cover.one (box := dirCellBox) (n := 2832)
      (.split 3 (.split 2 (.split 3 (.split 2 (.leaf _ k2832_0) (.leaf _ k2832_1)) (.split 2 (.leaf _ k2832_2) (.leaf _ k2832_3))) (.split 3 (.split 1 (.leaf _ k2832_4) (.leaf _ k2832_5)) (.split 1 (.leaf _ k2832_6) (.leaf _ k2832_7)))) (.split 2 (.split 3 (.split 2 (.leaf _ k2832_8) (.leaf _ k2832_9)) (.split 1 (.leaf _ k2832_10) (.leaf _ k2832_11))) (.split 3 (.split 2 (.leaf _ k2832_12) (.leaf _ k2832_13)) (.split 1 (.leaf _ k2832_14) (.leaf _ k2832_15)))))).trans <|
  (Cover.one (box := dirCellBox) (n := 2833)
      (.split 3 (.split 2 (.split 3 (.split 1 (.leaf _ k2833_0) (.leaf _ k2833_1)) (.split 1 (.leaf _ k2833_2) (.leaf _ k2833_3))) (.split 3 (.split 1 (.leaf _ k2833_4) (.leaf _ k2833_5)) (.split 1 (.leaf _ k2833_6) (.leaf _ k2833_7)))) (.split 2 (.split 3 (.split 1 (.leaf _ k2833_8) (.leaf _ k2833_9)) (.split 1 (.leaf _ k2833_10) (.leaf _ k2833_11))) (.split 3 (.split 1 (.leaf _ k2833_12) (.leaf _ k2833_13)) (.split 1 (.leaf _ k2833_14) (.leaf _ k2833_15))))))

end C4.Cert.Dir068
