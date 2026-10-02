module

public import C4Check

public section

/-! Cells `4096 ≤ n < 4122` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir140

theorem k4096_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4096) 2).1
      348143286674849511643609717752071908224016335194002978894558494606660176499398145537247087723065115513228868930637962097799971644).isSome = true := by
  decide +kernel

theorem k4096_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4096) 2).2
      1179776189983646140325757792888289744853046902309220649562937237916729394969853701954136765386542501332827196).isSome = true := by
  decide +kernel

theorem k4097_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4097) 3).1
      347812874730312265236686959546105506758308187291008040121933510762916079960069595828508328461951607285207949449063936488459191100).isSome = true := by
  decide +kernel

theorem k4097_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4097) 3).2
      86902766361676458280554203757795177732324968094412325106229342115459567777862512278470849761739068782857491285903207436701909820).isSome = true := by
  decide +kernel

theorem k4098_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4098) 2).1
      62307500796393659758864939000626708989124935243296461204205338277948551837389893915452).isSome = true := by
  decide +kernel

theorem k4098_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4098) 2).2
      15577970708057983414014470494122213385887214389142419478162823956077312309660806005564).isSome = true := by
  decide +kernel

theorem k4099_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4099) 3).1
      13503630640923698448045219277421079194633037544226951032825406497596).isSome = true := by
  decide +kernel

theorem k4099_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4099) 3).2
      3374935605518194299686132064166438708074075636706093441929468388156).isSome = true := by
  decide +kernel

theorem k4100_0 : (checkBoxH dirMode depth (dirCellBox 4100)
      1638602922859478112864481582530133774707577035186709958143938006642903153056298036649133011172768360482929926646723822323045429425230264276596475097916).isSome = true := by
  decide +kernel

theorem k4101_0 : (checkBoxH dirMode depth (dirCellBox 4101)
      1888529390134465750386500356458975679785687030703288031544663499320112128412698788364530574788755360282406778083852149446992547912925196397294023770017760517205981475644).isSome = true := by
  decide +kernel

theorem c6 : allCells dirCell 4102 4103 [
    286850941536145391706416385487322117342039201651276067145418456825701057889002087436614624103130631492412] = true := by
  decide +kernel

theorem c7 : allCells dirCell 4103 4104 [
    286794347091144160237309184805768349481475407884805157882923928070095478024164052967477067371107692565308] = true := by
  decide +kernel

theorem c8 : allCells dirCell 4104 4105 [
    286750841574202752878149202943594481821560861483565424697739224550697484618878935776032692384217116955452] = true := by
  decide +kernel

theorem c9 : allCells dirCell 4105 4119 [
    52662666749868968873197508770432108931041810737058925856538052849,
    51423493173523052838052388975916641324337589391317330750476241, 147562890987157458580, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0] = true := by
  decide +kernel

theorem c10 : allCells dirCell 4119 4120 [
    347671932440263274823617943450365652360940067118212743667393378682684196264462365139601479382873908096934794348726664250971467] = true := by
  decide +kernel

theorem k4120_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4120) 3).1
      15889766672091822708077807245467760808343533231252613395524854053704232302666886289202).isSome = true := by
  decide +kernel

theorem k4120_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4120) 3).2
      1168074840493871684500793729710768413430812132183274176311786518197849014937310202065696497003902821562162).isSome = true := by
  decide +kernel

theorem k4121_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4121) 2).1
      5485409983201849012366720416760467436060245427364153059169985852970255758197867950306113981963090308154038775448515592413633331).isSome = true := by
  decide +kernel

theorem k4121_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4121) 2).2
      4646591183774244352458995915515745954393223574076911936513582113579761058521525759204796113379699304814387).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 4096 4122 :=
  (Cover.one (box := dirCellBox) (n := 4096)
      (.split 2 (.leaf _ k4096_0) (.leaf _ k4096_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 4097)
      (.split 3 (.leaf _ k4097_0) (.leaf _ k4097_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 4098)
      (.split 2 (.leaf _ k4098_0) (.leaf _ k4098_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 4099)
      (.split 3 (.leaf _ k4099_0) (.leaf _ k4099_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 4100)
      (.leaf _ k4100_0)).trans <|
  (Cover.one (box := dirCellBox) (n := 4101)
      (.leaf _ k4101_0)).trans <|
  (Cover.dir c6).trans <|
  (Cover.dir c7).trans <|
  (Cover.dir c8).trans <|
  (Cover.dir c9).trans <|
  (Cover.dir c10).trans <|
  (Cover.one (box := dirCellBox) (n := 4120)
      (.split 3 (.leaf _ k4120_0) (.leaf _ k4120_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 4121)
      (.split 2 (.leaf _ k4121_0) (.leaf _ k4121_1)))

end C4.Cert.Dir140
