module

public import C4Check

public section

/-! Cells `3165 ≤ n < 3166` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir087

theorem k3165_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3165) 3).1 3).1
      17044510).isSome = true := by
  decide +kernel

theorem k3165_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3165) 3).1 3).2 2).1 3).1
      278756209142350405401137701630977266012422699115008273206029142549570155888679226185).isSome = true := by
  decide +kernel

theorem k3165_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3165) 3).1 3).2 2).1 3).2
      23909951587841708081456707269675235670455816556282018227393611136269132237599771084893959586972865975830946873362253649728969).isSome = true := by
  decide +kernel

theorem k3165_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3165) 3).1 3).2 2).2
      17592978016031197024560254297054335885334872101540593914782951097368256902668458542599).isSome = true := by
  decide +kernel

theorem k3165_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3165) 3).2 2).1 3).1 1).1
      6897256943310021575565745982154904591136818761896855025952975364778975934882930566312488127639950683712223976842072748086387816308197984334255566).isSome = true := by
  decide +kernel

theorem k3165_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3165) 3).2 2).1 3).1 1).2
      6881768800892163248543405491376703636875638673077233322944223514713940015034941515157553359771443469898367493974248445565319729585503654450898382).isSome = true := by
  decide +kernel

theorem k3165_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3165) 3).2 2).1 3).2 1).1 2).1
      1245275636775958044688610539933151101689074464147485574946908645101156439706289932550482101599536724563772).isSome = true := by
  decide +kernel

theorem k3165_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3165) 3).2 2).1 3).2 1).1 2).2
      3581317901670375647685583314946156051724885153365690289662316796).isSome = true := by
  decide +kernel

theorem k3165_8 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3165) 3).2 2).1 3).2 1).2 2).1
      310757753626770633317044942990484582135756257535604260226863931187204480519114070234567264467738689000252).isSome = true := by
  decide +kernel

theorem k3165_9 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3165) 3).2 2).1 3).2 1).2 2).2
      16490903818984660421192135264466473036017091320106340690243236486322605602767187314).isSome = true := by
  decide +kernel

theorem k3165_10 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3165) 3).2 2).2 3).1
      32722802481545662046786820527781398904322000060572473307037466108386984891716877420624094617237614898149452553694983901374504263184000535371858598264840398899023700249).isSome = true := by
  decide +kernel

theorem k3165_11 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3165) 3).2 2).2 3).2 1).1
      19543898682482561049182745221873210307544906641853621592558441916061368701985099456792117737223550852942).isSome = true := by
  decide +kernel

theorem k3165_12 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3165) 3).2 2).2 3).2 1).2
      78028141303719088012520646265180904450667574541453444107975244274452574923641490070698679481271278728434).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 3165 3166 :=
  (Cover.one (box := dirCellBox) (n := 3165)
      (.split 3 (.split 3 (.leaf _ k3165_0) (.split 2 (.split 3 (.leaf _ k3165_1) (.leaf _ k3165_2)) (.leaf _ k3165_3))) (.split 2 (.split 3 (.split 1 (.leaf _ k3165_4) (.leaf _ k3165_5)) (.split 1 (.split 2 (.leaf _ k3165_6) (.leaf _ k3165_7)) (.split 2 (.leaf _ k3165_8) (.leaf _ k3165_9)))) (.split 3 (.leaf _ k3165_10) (.split 1 (.leaf _ k3165_11) (.leaf _ k3165_12))))))

end C4.Cert.Dir087
