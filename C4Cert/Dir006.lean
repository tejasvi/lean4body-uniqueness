module

public import C4Check

public section

/-! Cells `1184 ≤ n < 1239` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir006

theorem k1184_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 1184) 2).1
      52739792051381699762566879070931240662297827056561202581861713670).isSome = true := by
  decide +kernel

theorem k1184_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 1184) 2).2
      1890191345104522001237007236529362049006331559472554685039584062317188469465789842037526586714615449565722569871215604517448661077637377831718159416970552597788625164574).isSome = true := by
  decide +kernel

theorem c1 : allCells dirCell 1185 1210 [
    62217313521674689846898055718257166285867311887149609670288195781021177324198722949506,
    151154362247905194971426, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    209102] = true := by
  decide +kernel

theorem k1210_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 1210) 2).1
      1392659288605671424932860801289134957728877586591921083746716951142995577383837083998307258567070885322245272247027422962463265991).isSome = true := by
  decide +kernel

theorem k1210_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 1210) 2).2
      25691930293880498614977358973670055384719248777658511042323813807685207771333701966898213577065336064669085023662725251035627987623817253174929196231).isSome = true := by
  decide +kernel

theorem k1211_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1211) 2).1 3).1
      294588017482765585704798168828981456866263547637665478291383938142618350385621617382150634378622529817060553).isSome = true := by
  decide +kernel

theorem k1211_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1211) 2).1 3).2
      1021452345646447897271438502942648653165192875613952012585118705821371809361253018097349833).isSome = true := by
  decide +kernel

theorem k1211_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1211) 2).2 3).1
      249601117987670506672326318887792938134195728499482300498114086350762698874023425968461).isSome = true := by
  decide +kernel

theorem k1211_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1211) 2).2 3).2
      63849835177892993514137259629497501492303905594150322362994235259792311954645743533971249).isSome = true := by
  decide +kernel

theorem k1212_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1212) 2).1 3).1
      249271477362111503874877872661723999595884361777404682349414321657872562824204208489673).isSome = true := by
  decide +kernel

theorem k1212_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1212) 2).1 3).2
      3892535881131297609106260006060521735872696155000984964875042096760251158960859207473).isSome = true := by
  decide +kernel

theorem k1212_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1212) 2).2 3).1
      997088969604077208978359462346368585669145637650992761237822337724450712117801957815089).isSome = true := by
  decide +kernel

theorem k1212_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1212) 2).2 3).2
      211089617856680935330998370668865937521473591675499620688061879089).isSome = true := by
  decide +kernel

theorem k1213_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 1213) 2).1
      86743276965317652565129412612112857000856228798831562482008579847486665338428869772478951700650068753491771297464454537000672455).isSome = true := by
  decide +kernel

theorem k1213_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 1213) 2).2
      5551256031493604167854114642401920405255835879424200521634501177789412365754437436232874046810869982116281039998833394849834749127).isSome = true := by
  decide +kernel

theorem k1214_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 1214) 2).1
      71699979068586758079530467763900638278183949902155111290910837168513560223586422846757126975319724185031).isSome = true := by
  decide +kernel

theorem k1214_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 1214) 2).2
      15921090442103332920399030602214347796584147649903633045081749564733891161090785692890311).isSome = true := by
  decide +kernel

theorem k1215_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 1215) 2).1
      60701994470635906843643788268087064705661243445753366091072536983111264235096607303).isSome = true := by
  decide +kernel

theorem k1215_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 1215) 2).2
      248669990839493141634994292724709431175358315140877555653784911347669012063702130242767).isSome = true := by
  decide +kernel

theorem c8 : allCells dirCell 1216 1238 [
    604277933596109177045254, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 51] = true := by
  decide +kernel

theorem k1238_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 1238) 3).1
      288997804883553164801012368566079889582075398063441927598285211705118519968681822060230572911270941450830).isSome = true := by
  decide +kernel

theorem k1238_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1238) 3).2 2).1
      976292498499656022492131566085897926868964310277210374812614206821651708799271226737).isSome = true := by
  decide +kernel

theorem k1238_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1238) 3).2 2).2
      976766301185462875983520729151640695106211261718673864366230370030662434965572591985).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 1184 1239 :=
  (Cover.one (box := dirCellBox) (n := 1184)
      (.split 2 (.leaf _ k1184_0) (.leaf _ k1184_1))).trans <|
  (Cover.dir c1).trans <|
  (Cover.one (box := dirCellBox) (n := 1210)
      (.split 2 (.leaf _ k1210_0) (.leaf _ k1210_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 1211)
      (.split 2 (.split 3 (.leaf _ k1211_0) (.leaf _ k1211_1)) (.split 3 (.leaf _ k1211_2) (.leaf _ k1211_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 1212)
      (.split 2 (.split 3 (.leaf _ k1212_0) (.leaf _ k1212_1)) (.split 3 (.leaf _ k1212_2) (.leaf _ k1212_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 1213)
      (.split 2 (.leaf _ k1213_0) (.leaf _ k1213_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 1214)
      (.split 2 (.leaf _ k1214_0) (.leaf _ k1214_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 1215)
      (.split 2 (.leaf _ k1215_0) (.leaf _ k1215_1))).trans <|
  (Cover.dir c8).trans <|
  (Cover.one (box := dirCellBox) (n := 1238)
      (.split 3 (.leaf _ k1238_0) (.split 2 (.leaf _ k1238_1) (.leaf _ k1238_2))))

end C4.Cert.Dir006
