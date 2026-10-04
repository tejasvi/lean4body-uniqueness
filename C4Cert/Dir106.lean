module

public import C4Check

public section

/-! Cells `3557 ≤ n < 3558` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir106

theorem k3557_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3557) 3).1 3).1
      1497502219946351337586382873214688466948976354334).isSome = true := by
  decide +kernel

theorem k3557_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3557) 3).1 3).2 2).1 3).1
      24132228411416770826810751447169481367355635013298965503101906815018467226941377982187298993971373160497156003059980691629513).isSome = true := by
  decide +kernel

theorem k3557_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3557) 3).1 3).2 2).1 3).2 1).1
      68413280856311725307223203095848753839402282922735007434153048003927523044172748870).isSome = true := by
  decide +kernel

theorem k3557_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3557) 3).1 3).2 2).1 3).2 1).2
      20137989275739449952835393371405332067260929748898941813231546106866835240571598910619157920066496738886).isSome = true := by
  decide +kernel

theorem k3557_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3557) 3).1 3).2 2).2
      2283256458297072412850655030880525757308907638855).isSome = true := by
  decide +kernel

theorem k3557_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3557) 3).2 2).1 3).1 2).1 1).1
      322478772582103281927287097082897805527848526511519628297557008388536639099636233781475916186964359123961294).isSome = true := by
  decide +kernel

theorem k3557_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3557) 3).2 2).1 3).1 2).1 1).2
      17018166610206019742721729654218465526784252494916202956648720171378257387227483174086).isSome = true := by
  decide +kernel

theorem k3557_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3557) 3).2 2).1 3).1 2).2 1).1
      78833798734555524508865294797905649270327726682361139385071774940358109736776029750292214603562659210611).isSome = true := by
  decide +kernel

theorem k3557_8 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3557) 3).2 2).1 3).1 2).2 1).2
      4243631457752323176669204087527127834949880719271111619636588883827085853044202327411).isSome = true := by
  decide +kernel

theorem k3557_9 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3557) 3).2 2).1 3).2 2).1 1).1
      110271319491502998011375416256749078065715654368154955254465747113684292840379861387858894149611832061725716221416679854096538233313070398819061357766).isSome = true := by
  decide +kernel

theorem k3557_10 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3557) 3).2 2).1 3).2 2).1 1).2
      66786897099861446411917695781166760503741795088348098595802995381571665464501550453958).isSome = true := by
  decide +kernel

theorem k3557_11 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3557) 3).2 2).1 3).2 2).2 1).1
      1072168830305123521039480258737611621586080797681623895230189134970932356279315641607374).isSome = true := by
  decide +kernel

theorem k3557_12 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3557) 3).2 2).1 3).2 2).2 1).2
      16721863605993998717909865531723830581484502287832121912745032503618696111489214340322).isSome = true := by
  decide +kernel

theorem k3557_13 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3557) 3).2 2).2 3).1 1).1
      78980718998430492505308709318784713422397382861652933449348262072451612627044305126039724222308991549262).isSome = true := by
  decide +kernel

theorem k3557_14 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3557) 3).2 2).2 3).1 1).2
      23218376982236251629755798032880673559861047225926802184172263530607024365130882329502064446420433313446447874905060520728014).isSome = true := by
  decide +kernel

theorem k3557_15 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3557) 3).2 2).2 3).2 2).1 1).1
      67256696059338924254045172202846459319095067916692651248649645998354685686786427458931).isSome = true := by
  decide +kernel

theorem k3557_16 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3557) 3).2 2).2 3).2 2).1 1).2
      226959058390021989014031387370314898228469044743244068441827333938).isSome = true := by
  decide +kernel

theorem k3557_17 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3557) 3).2 2).2 3).2 2).2
      5856104650128975399631831517895179310755890762341689670549699940688840376551313014293829759565430764764113702166161238764606917).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 3557 3558 :=
  (Cover.one (box := dirCellBox) (n := 3557)
      (.split 3 (.split 3 (.leaf _ k3557_0) (.split 2 (.split 3 (.leaf _ k3557_1) (.split 1 (.leaf _ k3557_2) (.leaf _ k3557_3))) (.leaf _ k3557_4))) (.split 2 (.split 3 (.split 2 (.split 1 (.leaf _ k3557_5) (.leaf _ k3557_6)) (.split 1 (.leaf _ k3557_7) (.leaf _ k3557_8))) (.split 2 (.split 1 (.leaf _ k3557_9) (.leaf _ k3557_10)) (.split 1 (.leaf _ k3557_11) (.leaf _ k3557_12)))) (.split 3 (.split 1 (.leaf _ k3557_13) (.leaf _ k3557_14)) (.split 2 (.split 1 (.leaf _ k3557_15) (.leaf _ k3557_16)) (.leaf _ k3557_17))))))

end C4.Cert.Dir106
