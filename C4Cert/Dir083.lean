module

public import C4Check

public section

/-! Cells `3165 ≤ n < 3166` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir083

theorem k3165_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3165) 3).1 3).1
      17044510).isSome = true := by
  decide +kernel

theorem k3165_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3165) 3).1 3).2 2).1 3).1
      48865477174907203949707671185685975925205786840121760536344690063333207904420417099209).isSome = true := by
  decide +kernel

theorem k3165_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3165) 3).1 3).2 2).1 3).2
      95061382378636886280067029504895777205161051638579982586758234396944988112739822543998755062125340082602778986124525221893577).isSome = true := by
  decide +kernel

theorem k3165_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3165) 3).1 3).2 2).2
      1115399).isSome = true := by
  decide +kernel

theorem k3165_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3165) 3).2 2).1 3).1 1).1 2).1
      6875556844660260065611613613141781730534067039553557010480208007814966479189123487860749747939767948951745494417431700730476188718812556592485835).isSome = true := by
  decide +kernel

theorem k3165_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3165) 3).2 2).1 3).1 1).1 2).2
      66805179826847578361741978171833400054359227686812594642017622227600887346317670771).isSome = true := by
  decide +kernel

theorem k3165_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3165) 3).2 2).1 3).1 1).2 2).1
      109923734156977819888436577672943306624532333549329728041935031129356754718901926345557484453146440208119256171379910272458493686047833971207284174).isSome = true := by
  decide +kernel

theorem k3165_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3165) 3).2 2).1 3).1 1).2 2).2
      19739710020789253796554975847991108871764913988896766972907648322308249885555479625515172181449946574195).isSome = true := by
  decide +kernel

theorem k3165_8 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3165) 3).2 2).1 3).2 1).1 2).1 2).1
      77429823833980636167079753540751771978799362719531717226130145763035028133361368287904303182570134373811).isSome = true := by
  decide +kernel

theorem k3165_9 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3165) 3).2 2).1 3).2 1).1 2).1 2).2
      262679239584008400638484601091373042241530162512419192374489783514165379947019054451).isSome = true := by
  decide +kernel

theorem k3165_10 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3165) 3).2 2).1 3).2 1).1 2).2
      1468582440312153134928075964755345518971630316594617106373959397276296771121779596886384865519290305456733705355438218834990002).isSome = true := by
  decide +kernel

theorem k3165_11 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3165) 3).2 2).1 3).2 1).2 2).1 2).1
      16782507158069006947880808532522920153421780458896560842320046943843001603533372546225).isSome = true := by
  decide +kernel

theorem k3165_12 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3165) 3).2 2).1 3).2 1).2 2).1 2).2
      16849252294686324450767306238659799823930779686914383948175936832872156362908959595697).isSome = true := by
  decide +kernel

theorem k3165_13 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3165) 3).2 2).1 3).2 1).2 2).2
      364739944703000917633676171892414957303826051456077929384181122139399874170768734395880983342997048680446484247314587446244595).isSome = true := by
  decide +kernel

theorem k3165_14 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3165) 3).2 2).2 3).1 1).1
      79703389094363448047584130723243088594201492193607868923034837278234545654105175626419775096158470799950).isSome = true := by
  decide +kernel

theorem k3165_15 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3165) 3).2 2).2 3).1 1).2
      79442435624892873001628583433506775525094053187562386124803467923770581473857427971997314732950404575310).isSome = true := by
  decide +kernel

theorem k3165_16 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3165) 3).2 2).2 3).2 1).1
      128107456655394482453878033660619009575299843764974867103625251455638002230657347437128207822573377112655308947996255052997829439755349120641429677056539160516656576826).isSome = true := by
  decide +kernel

theorem k3165_17 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3165) 3).2 2).2 3).2 1).2 2).1
      77637636983154981934011239464710069464978989941443275029260382498635839270601756767661966003519254491507).isSome = true := by
  decide +kernel

theorem k3165_18 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3165) 3).2 2).2 3).2 1).2 2).2
      16456811784008941077155018732649094425387681523854975370813834140143499218725733745).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 3165 3166 :=
  (Cover.one (box := dirCellBox) (n := 3165)
      (.split 3 (.split 3 (.leaf _ k3165_0) (.split 2 (.split 3 (.leaf _ k3165_1) (.leaf _ k3165_2)) (.leaf _ k3165_3))) (.split 2 (.split 3 (.split 1 (.split 2 (.leaf _ k3165_4) (.leaf _ k3165_5)) (.split 2 (.leaf _ k3165_6) (.leaf _ k3165_7))) (.split 1 (.split 2 (.split 2 (.leaf _ k3165_8) (.leaf _ k3165_9)) (.leaf _ k3165_10)) (.split 2 (.split 2 (.leaf _ k3165_11) (.leaf _ k3165_12)) (.leaf _ k3165_13)))) (.split 3 (.split 1 (.leaf _ k3165_14) (.leaf _ k3165_15)) (.split 1 (.leaf _ k3165_16) (.split 2 (.leaf _ k3165_17) (.leaf _ k3165_18)))))))

end C4.Cert.Dir083
