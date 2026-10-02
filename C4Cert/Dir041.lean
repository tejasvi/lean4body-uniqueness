module

public import C4Check

public section

/-! Cells `2384 ≤ n < 2386` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir041

theorem k2384_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2384) 3).1 2).1 3).1 2).1
      15788242657640910566115940615421916361982982600438072713278824688188202933531165351089).isSome = true := by
  decide +kernel

theorem k2384_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2384) 3).1 2).1 3).1 2).2
      63223801983259401062715296406798141266059373293406038799461031215336966751449252453553).isSome = true := by
  decide +kernel

theorem k2384_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2384) 3).1 2).1 3).2 1).1
      246405298069253490253836175706150242991680450560034747759093543862613648416194387756).isSome = true := by
  decide +kernel

theorem k2384_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2384) 3).1 2).1 3).2 1).2
      246358000393182021260804647735165735478192941727141567171421883015397057351550359500).isSome = true := by
  decide +kernel

theorem k2384_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2384) 3).1 2).2 3).1 1).1
      4571816809533494801660330150945865092893705082743780513123314469004383616855051039951819837196548560754).isSome = true := by
  decide +kernel

theorem k2384_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2384) 3).1 2).2 3).1 1).2
      214612191412852877510219205901492147572719185057091113937449382460).isSome = true := by
  decide +kernel

theorem k2384_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2384) 3).1 2).2 3).2 1).1
      987523047945063810671441575027614619208746608480504352153798176786741887303816150188).isSome = true := by
  decide +kernel

theorem k2384_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2384) 3).1 2).2 3).2 1).2
      214082168438796579963256754307675517709235958947542666001984093244).isSome = true := by
  decide +kernel

theorem k2384_8 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2384) 3).2 2).1 3).1
      1617910762028733391510299455891655118510715952119266015538350250315773142611322424602618367516104018682529198913135722409428617059037099862506561329).isSome = true := by
  decide +kernel

theorem k2384_9 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2384) 3).2 2).1 3).2
      87573732197870388504552519740568774640232723170990522334087031347561359199578503037093101930656163632544911004858711124808781617).isSome = true := by
  decide +kernel

theorem k2384_10 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2384) 3).2 2).2 3).1 1).1
      246366470743334390532177641587207496877852787737957560710446879818227009298112143148).isSome = true := by
  decide +kernel

theorem k2384_11 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2384) 3).2 2).2 3).1 1).2
      213646348284414867593066358123275368032355091783833684827401190460).isSome = true := by
  decide +kernel

theorem k2384_12 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2384) 3).2 2).2 3).2
      6470984682311293510840626684396058427972750902842805806403983459230510468951668027074407433532497191426608559539537019510315693967809467469998284593).isSome = true := by
  decide +kernel

theorem k2385_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2385) 2).1 3).1 3).1
      21864227551167860965599348097651743830399641117931408102108217835805501937981878998605064614363262069031321153935601568653368113).isSome = true := by
  decide +kernel

theorem k2385_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2385) 2).1 3).1 3).2
      5460651330973818143558316408463753824147410864683053506979885958473208698577279054915068426454265133112713550113663236105952049).isSome = true := by
  decide +kernel

theorem k2385_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2385) 2).1 3).2 2).1
      250202846052966712265946652625252685057824387140132984717614938849134358239308707747633).isSome = true := by
  decide +kernel

theorem k2385_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2385) 2).1 3).2 2).2
      15651869718640749202323248231711180536222008038873689739169206239094241162412367025969).isSome = true := by
  decide +kernel

theorem k2385_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2385) 2).2 3).1 3).1
      5473831459669428119641488652032045176907571827315931662715828236983309274529421950217906222558597804791359960734554894630247217).isSome = true := by
  decide +kernel

theorem k2385_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2385) 2).2 3).1 3).2
      5467649765284703118397340247095615832901213634934796454052405965559947440452991556719933473002428313303260086976824576233487420).isSome = true := by
  decide +kernel

theorem k2385_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2385) 2).2 3).2 1).1
      85309149786283874476876046625135406786194786706435724098404061764215858113663133729009479243106591106033387980080792978944972).isSome = true := by
  decide +kernel

theorem k2385_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2385) 2).2 3).2 1).2
      4621395727870210900659756312977654848409423894259462772903594569862151023133957662220448537192311816575795).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 2384 2386 :=
  (Cover.one (box := dirCellBox) (n := 2384)
      (.split 3 (.split 2 (.split 3 (.split 2 (.leaf _ k2384_0) (.leaf _ k2384_1)) (.split 1 (.leaf _ k2384_2) (.leaf _ k2384_3))) (.split 3 (.split 1 (.leaf _ k2384_4) (.leaf _ k2384_5)) (.split 1 (.leaf _ k2384_6) (.leaf _ k2384_7)))) (.split 2 (.split 3 (.leaf _ k2384_8) (.leaf _ k2384_9)) (.split 3 (.split 1 (.leaf _ k2384_10) (.leaf _ k2384_11)) (.leaf _ k2384_12))))).trans <|
  (Cover.one (box := dirCellBox) (n := 2385)
      (.split 2 (.split 3 (.split 3 (.leaf _ k2385_0) (.leaf _ k2385_1)) (.split 2 (.leaf _ k2385_2) (.leaf _ k2385_3))) (.split 3 (.split 3 (.leaf _ k2385_4) (.leaf _ k2385_5)) (.split 1 (.leaf _ k2385_6) (.leaf _ k2385_7)))))

end C4.Cert.Dir041
