module

public import C4Check

public section

/-! Cells `3643 ≤ n < 3647` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir122

theorem k3643_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3643) 3).1 2).1
      26457184025758873980470359314997036236298775499679212270639240761124844045269643814602622747234616474574724377552182942844681329485247702463405579465).isSome = true := by
  decide +kernel

theorem k3643_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3643) 3).1 2).2
      350311514601581089884487789116533595794310115120328895495175487669855553729575373098983360054348443763309267724844543670842611).isSome = true := by
  decide +kernel

theorem k3643_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3643) 3).2 2).1
      6575741017351652739623566676053806623925990659762475314736220305404832667085142868302993350171012916148895512356017249180719128861005085941979511985).isSome = true := by
  decide +kernel

theorem k3643_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3643) 3).2 2).2
      22785911131425638016269263556443535576205568957913910918761200867104621260869676775482583630810561104040302965350224113544534069965).isSome = true := by
  decide +kernel

theorem k3644_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3644) 2).1 3).1
      5668813987556142302186108039282069219644502103742931653741020490050909700227758903014813191043250035379127524246146700475813261553).isSome = true := by
  decide +kernel

theorem k3644_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3644) 2).1 3).2
      19117118816569599508471982160343903040810635501096062818705086029593802569712471041163260071499846687404805937).isSome = true := by
  decide +kernel

theorem k3644_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3644) 2).2 3).1
      22694563081385072661127012813259790904128964334343643645954935082340218485529400176517097556908446162891026503570116702992067784946).isSome = true := by
  decide +kernel

theorem k3644_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3644) 2).2 3).2
      4783211724771809181011230014491164655067427967564961861264292480440931195629953035335050390530842760890350652).isSome = true := by
  decide +kernel

theorem k3645_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3645) 2).1 3).1
      4130162991097381431018341337822710568493555048625295686505577975670903957446253703049203505).isSome = true := by
  decide +kernel

theorem k3645_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3645) 2).1 3).2
      5476116687795792755867529750274813512296435624841481773216688669114148923135582041290980111247867056781717242301687166051613756).isSome = true := by
  decide +kernel

theorem k3645_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3645) 2).2 3).1
      18617605015043982625645435294999737827896663309680350979767099146675705901592051693401876812842927637609532).isSome = true := by
  decide +kernel

theorem k3645_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3645) 2).2 3).2
      74258063099810469745771465293406444073156609955688014068798294570416796931136202268496719974396757809085500).isSome = true := by
  decide +kernel

theorem k3646_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3646) 2).1 3).1
      75824756844101140128864295970432299829063172276853284469751185230018325631522782606029602655764448020431618876).isSome = true := by
  decide +kernel

theorem k3646_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3646) 2).1 3).2
      349100772179472235930283822274656700301649590015033969573791857357255950841938370635713871673287600183999032388918957201495630652).isSome = true := by
  decide +kernel

theorem k3646_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3646) 2).2 3).1
      4111916302784118786805812632642536839266036448496641228329434386018211946463843457001910513).isSome = true := by
  decide +kernel

theorem k3646_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3646) 2).2 3).2
      4733596164321580930932366060684563082934160550978154901236910405512457737791822590065300782602362667895866172).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 3643 3647 :=
  (Cover.one (box := dirCellBox) (n := 3643)
      (.split 3 (.split 2 (.leaf _ k3643_0) (.leaf _ k3643_1)) (.split 2 (.leaf _ k3643_2) (.leaf _ k3643_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 3644)
      (.split 2 (.split 3 (.leaf _ k3644_0) (.leaf _ k3644_1)) (.split 3 (.leaf _ k3644_2) (.leaf _ k3644_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 3645)
      (.split 2 (.split 3 (.leaf _ k3645_0) (.leaf _ k3645_1)) (.split 3 (.leaf _ k3645_2) (.leaf _ k3645_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 3646)
      (.split 2 (.split 3 (.leaf _ k3646_0) (.leaf _ k3646_1)) (.split 3 (.leaf _ k3646_2) (.leaf _ k3646_3))))

end C4.Cert.Dir122
