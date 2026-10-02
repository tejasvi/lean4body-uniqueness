module

public import C4Check

public section

/-! Cells `3195 ≤ n < 3196` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir093

theorem k3195_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3195) 3).1 2).1 3).1 2).1
      4027241244007968658971711960413351258193520340787938354208262767242684539739334759228).isSome = true := by
  decide +kernel

theorem k3195_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3195) 3).1 2).1 3).1 2).2
      4031737942951666378204535819647646824571282429644719177210039973060046331948515709756).isSome = true := by
  decide +kernel

theorem k3195_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3195) 3).1 2).1 3).2 2).1
      868357317470835281898860372322401396929345997235417133023192097596).isSome = true := by
  decide +kernel

theorem k3195_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3195) 3).1 2).1 3).2 2).2
      869374648918882546201698169457788236545618489323470272975456903996).isSome = true := by
  decide +kernel

theorem k3195_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3195) 3).1 2).2 2).1 1).1
      1006417790746485369387884635199474552550076975635850563180898914642263356483920328252).isSome = true := by
  decide +kernel

theorem k3195_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3195) 3).1 2).2 2).1 1).2
      218061156829998513913166135880272794706989638107022561606853557308).isSome = true := by
  decide +kernel

theorem k3195_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3195) 3).1 2).2 2).2 1).1
      1007179040055720238390311529697175230889446589706481663663782992887200446905068156476).isSome = true := by
  decide +kernel

theorem k3195_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3195) 3).1 2).2 2).2 1).2
      3409914593889983788115808042692049501271868072390651560368430892).isSome = true := by
  decide +kernel

theorem k3195_8 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3195) 3).2 2).1 2).1 3).1
      216125170268033526408729792153422019046635032823481588389500142396).isSome = true := by
  decide +kernel

theorem k3195_9 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3195) 3).2 2).1 2).1 3).2
      861324018780734303821221352436809889414320908736026104217493553980).isSome = true := by
  decide +kernel

theorem k3195_10 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3195) 3).2 2).1 2).2
      5684379485106378304504182964027074152691215766301829092952733389276614465517919872074685256856226878951737057377561150952425638129).isSome = true := by
  decide +kernel

theorem k3195_11 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3195) 3).2 2).2 2).1
      5690039133861780437942239580778139231527634386004263244878517620969882712228393666946420642719509789333811005024619570641705093361).isSome = true := by
  decide +kernel

theorem k3195_12 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3195) 3).2 2).2 2).2
      5694688784639769151992669461891420329646386780988903634685977753034603243399682708431528194503940056662740908138891447429481613553).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 3195 3196 :=
  (Cover.one (box := dirCellBox) (n := 3195)
      (.split 3 (.split 2 (.split 3 (.split 2 (.leaf _ k3195_0) (.leaf _ k3195_1)) (.split 2 (.leaf _ k3195_2) (.leaf _ k3195_3))) (.split 2 (.split 1 (.leaf _ k3195_4) (.leaf _ k3195_5)) (.split 1 (.leaf _ k3195_6) (.leaf _ k3195_7)))) (.split 2 (.split 2 (.split 3 (.leaf _ k3195_8) (.leaf _ k3195_9)) (.leaf _ k3195_10)) (.split 2 (.leaf _ k3195_11) (.leaf _ k3195_12)))))

end C4.Cert.Dir093
