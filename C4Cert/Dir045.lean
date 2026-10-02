module

public import C4Check

public section

/-! Cells `2417 ≤ n < 2440` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir045

theorem k2417_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2417) 2).1
      1356195830090453722541158052419029916405549190012763884453977021789751643723033415371501123828971538539890494357387299990725831).isSome = true := by
  decide +kernel

theorem k2417_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 2417) 2).2
      102464450277865846263108137401911936736141851015940600157845691921711025904854669975855229609139144862204956182088212854839321830490122327886556164339).isSome = true := by
  decide +kernel

theorem k2418_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2418) 2).1
      71750295046995801535316293873211312215997195536545568462715674538485208223131855220171418018319687214535).isSome = true := by
  decide +kernel

theorem k2418_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 2418) 2).2
      254910336424472685729747377147227535570601193661038889538851395800402471162023743474115783).isSome = true := by
  decide +kernel

theorem c2 : allCells dirCell 2419 2420 [
    118027659519044353374659033627376868901434779761268341078621633545112413755364547699647144477822996403981505568676305292003833469695901047801249546966286351346035750342] = true := by
  decide +kernel

theorem c3 : allCells dirCell 2420 2438 [
    286827784765737642719539419853120569015803440243225243938171592532873553641374106359493483199027501000006,
    2788184925612818898851493736871161591565586, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] = true := by
  decide +kernel

theorem k2438_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2438) 3).1
      161578032346579167571141813946386359925245019806601808540284044807).isSome = true := by
  decide +kernel

theorem k2438_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2438) 3).2 3).1
      75861172877133383775900831822343430091582219080197217303913504988776861267873803178278457828187155979078).isSome = true := by
  decide +kernel

theorem k2438_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2438) 3).2 3).2
      7740244455639682889436549436070509508414100517728889723031135469783783217284565900780722537183019121167766075764461746994286719117055064582942278579935544208198346182).isSome = true := by
  decide +kernel

theorem k2439_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2439) 3).1 3).1 2).1
      298896057453174588846275017162122968826668150878211255500820547850691875321681502327163058154037083007345).isSome = true := by
  decide +kernel

theorem k2439_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2439) 3).1 3).1 2).2
      15833798087600747397800667293345303197297417843335360119396173336312863752803860849).isSome = true := by
  decide +kernel

theorem k2439_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2439) 3).1 3).2 2).1
      74313995464917658268612724190921048745158004178876723269306391850257805743305527507937261521529957606769).isSome = true := by
  decide +kernel

theorem k2439_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2439) 3).1 3).2 2).2
      74366906834190908714825243136396969482200986100429784255371896195038780764340221689422567573237650558321).isSome = true := by
  decide +kernel

theorem k2439_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2439) 3).2 2).1 2).1
      5575135233106882534157649808675308565497531593344404690152632614967417905257613401464492302344101219073590886229145534223447537).isSome = true := by
  decide +kernel

theorem k2439_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2439) 3).2 2).1 2).2
      75596366836693060880884617428673127563229799023305224346083751292246507655990443051483694243799383438092109).isSome = true := by
  decide +kernel

theorem k2439_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2439) 3).2 2).2 1).1
      15618091263271877054259321253121948011929242953451129991874807653928703292566666611).isSome = true := by
  decide +kernel

theorem k2439_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2439) 3).2 2).2 1).2
      1182115620445269845511907026088318952419802801886745464574054794536204061907895288523126540533290162287868).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 2417 2440 :=
  (Cover.one (box := dirCellBox) (n := 2417)
      (.split 2 (.leaf _ k2417_0) (.leaf _ k2417_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 2418)
      (.split 2 (.leaf _ k2418_0) (.leaf _ k2418_1))).trans <|
  (Cover.dir c2).trans <|
  (Cover.dir c3).trans <|
  (Cover.one (box := dirCellBox) (n := 2438)
      (.split 3 (.leaf _ k2438_0) (.split 3 (.leaf _ k2438_1) (.leaf _ k2438_2)))).trans <|
  (Cover.one (box := dirCellBox) (n := 2439)
      (.split 3 (.split 3 (.split 2 (.leaf _ k2439_0) (.leaf _ k2439_1)) (.split 2 (.leaf _ k2439_2) (.leaf _ k2439_3))) (.split 2 (.split 2 (.leaf _ k2439_4) (.leaf _ k2439_5)) (.split 1 (.leaf _ k2439_6) (.leaf _ k2439_7)))))

end C4.Cert.Dir045
