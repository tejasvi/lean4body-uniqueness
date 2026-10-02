module

public import C4Check

public section

/-! Cells `3168 ≤ n < 3169` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir090

theorem k3168_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3168) 2).1 3).1 2).1 3).1
      63057240418216034365996222512430907025401322141269540246116616937469459702533398154044).isSome = true := by
  decide +kernel

theorem k3168_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3168) 2).1 3).1 2).1 3).2
      290330893615518068229192594069703991691375000861986660131463814883192978232765495717622844271468261922620).isSome = true := by
  decide +kernel

theorem k3168_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3168) 2).1 3).1 2).2 3).1
      15785043691334685974865339136899774208767608247931014401615442888491974618992780759868).isSome = true := by
  decide +kernel

theorem k3168_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3168) 2).1 3).1 2).2 3).2
      13660194162548094727785948971743581112851453083984827770401351224124).isSome = true := by
  decide +kernel

theorem k3168_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3168) 2).1 3).2 3).1 1).1
      3929476758174487558978062431102157602902607106215254414323470677056288564462340264764).isSome = true := by
  decide +kernel

theorem k3168_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3168) 2).1 3).2 3).1 1).2
      3928388184079575752862921623365240272229832156478199912276411754791219626333915567932).isSome = true := by
  decide +kernel

theorem k3168_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3168) 2).1 3).2 3).2 1).1
      981022606700250330075553574418436986928785901849791765237688587292142649562504754748).isSome = true := by
  decide +kernel

theorem k3168_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3168) 2).1 3).2 3).2 1).2
      245216735808565315585490766997858549425815792464990442439996519060667555927762299250).isSome = true := by
  decide +kernel

theorem k3168_8 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3168) 2).2 3).1 2).1 3).1
      15805987216406085842793271753185162843625510029613988497350093426109061000535893070652).isSome = true := by
  decide +kernel

theorem k3168_9 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3168) 2).2 3).1 2).1 3).2
      15767172296871066319347836482601887088494174215066272240042078655797286150808924574524).isSome = true := by
  decide +kernel

theorem k3168_10 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3168) 2).2 3).1 2).2 3).1
      3430147176720921827001058495128687540075955928813415726802855207740).isSome = true := by
  decide +kernel

theorem k3168_11 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3168) 2).2 3).1 2).2 3).2
      15785198461962100147399500682454697376993797630161802776191611263745371040268049437500).isSome = true := by
  decide +kernel

theorem k3168_12 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3168) 2).2 3).2 3).1 1).1
      213410183414704162100719437415928080340063781880162811771537978940).isSome = true := by
  decide +kernel

theorem k3168_13 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3168) 2).2 3).2 3).1 1).2
      853183974466397938995777303265938302597167075914455025541816243004).isSome = true := by
  decide +kernel

theorem k3168_14 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3168) 2).2 3).2 3).2 1).1
      982482261877703904845997976673801270099015874313077868935319663042012384717204485692).isSome = true := by
  decide +kernel

theorem k3168_15 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3168) 2).2 3).2 3).2 1).2
      851731153785283197185932887509772489695617051434955770219160619836).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 3168 3169 :=
  (Cover.one (box := dirCellBox) (n := 3168)
      (.split 2 (.split 3 (.split 2 (.split 3 (.leaf _ k3168_0) (.leaf _ k3168_1)) (.split 3 (.leaf _ k3168_2) (.leaf _ k3168_3))) (.split 3 (.split 1 (.leaf _ k3168_4) (.leaf _ k3168_5)) (.split 1 (.leaf _ k3168_6) (.leaf _ k3168_7)))) (.split 3 (.split 2 (.split 3 (.leaf _ k3168_8) (.leaf _ k3168_9)) (.split 3 (.leaf _ k3168_10) (.leaf _ k3168_11))) (.split 3 (.split 1 (.leaf _ k3168_12) (.leaf _ k3168_13)) (.split 1 (.leaf _ k3168_14) (.leaf _ k3168_15))))))

end C4.Cert.Dir090
