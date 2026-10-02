module

public import C4Check

public section

/-! Cells `3136 ≤ n < 3137` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir082

theorem k3136_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3136) 1).1 2).1 3).1
      0).isSome = true := by
  decide +kernel

theorem k3136_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3136) 1).1 2).1 3).2 3).1
      1).isSome = true := by
  decide +kernel

theorem k3136_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3136) 1).1 2).1 3).2 3).2 3).1
      675166976510641508400986842776356224240865652842056497387394506).isSome = true := by
  decide +kernel

theorem k3136_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3136) 1).1 2).1 3).2 3).2 3).2
      26096292422749979484731114103741368047300535065537468208597142425155852728785086630772131505894878311233607417480202172294602).isSome = true := by
  decide +kernel

theorem k3136_4 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3136) 1).1 2).2
      1).isSome = true := by
  decide +kernel

theorem k3136_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3136) 1).2 2).1 3).1
      0).isSome = true := by
  decide +kernel

theorem k3136_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3136) 1).2 2).1 3).2 3).1
      1).isSome = true := by
  decide +kernel

theorem k3136_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3136) 1).2 2).1 3).2 3).2 3).1
      673506805605109875821719119455584609222154161366830823673931210).isSome = true := by
  decide +kernel

theorem k3136_8 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3136) 1).2 2).1 3).2 3).2 3).2
      25960448027102443251728677551956727471313683718293356515131781537140427081164864194879996670868280552172527924384299072792010).isSome = true := by
  decide +kernel

theorem k3136_9 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3136) 1).2 2).2
      1).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 3136 3137 :=
  (Cover.one (box := dirCellBox) (n := 3136)
      (.split 1 (.split 2 (.split 3 (.leaf _ k3136_0) (.split 3 (.leaf _ k3136_1) (.split 3 (.leaf _ k3136_2) (.leaf _ k3136_3)))) (.leaf _ k3136_4)) (.split 2 (.split 3 (.leaf _ k3136_5) (.split 3 (.leaf _ k3136_6) (.split 3 (.leaf _ k3136_7) (.leaf _ k3136_8)))) (.leaf _ k3136_9))))

end C4.Cert.Dir082
