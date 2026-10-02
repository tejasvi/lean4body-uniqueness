module

public import C4Check

public section

/-! Cells `2888 ≤ n < 2893` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir075

theorem k2888_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2888) 3).1 2).1
      346791326916747475641023663309085568630288336372354161440911054199174785426310940327864432225533643812322329664865585272812785).isSome = true := by
  decide +kernel

theorem k2888_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2888) 3).1 2).2
      86715773590327661459609885979421098824260154274819150517946558496426236726248601374701951051870802144315130927433408959049980).isSome = true := by
  decide +kernel

theorem k2888_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2888) 3).2 2).1
      74849936700281928382629696355779392994539813232336401629638410905508157124581533780472058698427420524049649).isSome = true := by
  decide +kernel

theorem k2888_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2888) 3).2 2).2
      292471108573121396619935478744310539473373852623906520630376900041367608310104763241020683670668552165180).isSome = true := by
  decide +kernel

theorem k2889_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2889) 3).1 2).1
      22010176334637440214233077257869646247900792670794657356846857378489550579447805760592737654308276855069274229910941536215708476).isSome = true := by
  decide +kernel

theorem k2889_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2889) 3).1 2).2
      3949052096595897538439640095758526367526646199095595532567496836383731223263970841404).isSome = true := by
  decide +kernel

theorem k2889_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2889) 3).2 2).1
      21946491980314510013303761793401381412876045430472208792351809860816328586078276194977242651995329702638116043101372488678716220).isSome = true := by
  decide +kernel

theorem k2889_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2889) 3).2 2).2
      3937815216127282874019659136250828249330824108295559697410060521962230066590680339260).isSome = true := by
  decide +kernel

theorem k2890_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2890) 3).1 2).1
      1186789774569841950490097570439397309996883274345518537134612426637233840316004486758969792038620456227382076).isSome = true := by
  decide +kernel

theorem k2890_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2890) 3).1 2).2
      3406777774916872557658186730729689839468211931524071442420298883900).isSome = true := by
  decide +kernel

theorem k2890_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2890) 3).2 2).1
      64206161192653340790492066450429839827844243505428119950725726870688767700606422099149628).isSome = true := by
  decide +kernel

theorem k2890_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2890) 3).2 2).2
      64226789184687459610319742066323267643840865244108412239037785786071624758426652342469436).isSome = true := by
  decide +kernel

theorem k2891_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2891) 2).1 3).1
      64115666217811603706504178692632864640209323173743023437861715653123671020256379532540988).isSome = true := by
  decide +kernel

theorem k2891_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2891) 2).1 3).2
      4001875055062296013751710895130619865695832088021451802805090634321096902007994374208572).isSome = true := by
  decide +kernel

theorem k2891_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2891) 2).2 1).1
      13895802725655418259050481575181402644530473894947982222103882511219772).isSome = true := by
  decide +kernel

theorem k2891_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2891) 2).2 1).2
      868466240629448245809012865880579973183923034040000180914812478078012).isSome = true := by
  decide +kernel

theorem k2892_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2892) 3).1 1).1
      866910933906002414977943899589413840268651449138222613021510471466044).isSome = true := by
  decide +kernel

theorem k2892_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2892) 3).1 1).2
      999589710519783783231423641255858741721733380753659611887674087663007452408718722284604).isSome = true := by
  decide +kernel

theorem k2892_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2892) 3).2 2).1
      45849785411307450034748772172185333514972773436).isSome = true := by
  decide +kernel

theorem k2892_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2892) 3).2 2).2
      866231716949135914034099635284229098450988379239503887214127669263420).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 2888 2893 :=
  (Cover.one (box := dirCellBox) (n := 2888)
      (.split 3 (.split 2 (.leaf _ k2888_0) (.leaf _ k2888_1)) (.split 2 (.leaf _ k2888_2) (.leaf _ k2888_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 2889)
      (.split 3 (.split 2 (.leaf _ k2889_0) (.leaf _ k2889_1)) (.split 2 (.leaf _ k2889_2) (.leaf _ k2889_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 2890)
      (.split 3 (.split 2 (.leaf _ k2890_0) (.leaf _ k2890_1)) (.split 2 (.leaf _ k2890_2) (.leaf _ k2890_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 2891)
      (.split 2 (.split 3 (.leaf _ k2891_0) (.leaf _ k2891_1)) (.split 1 (.leaf _ k2891_2) (.leaf _ k2891_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 2892)
      (.split 3 (.split 1 (.leaf _ k2892_0) (.leaf _ k2892_1)) (.split 2 (.leaf _ k2892_2) (.leaf _ k2892_3))))

end C4.Cert.Dir075
