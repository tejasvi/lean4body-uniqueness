module

public import C4Check

public section

/-! Cells `3616 ≤ n < 3619` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir120

theorem k3616_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3616) 2).1 3).1 1).1
      1015573565758818344221096189293872167038179013972130222343229999315200532169481329417010).isSome = true := by
  decide +kernel

theorem k3616_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3616) 2).1 3).1 1).2
      3965381455249193834390215745967231659135587802832857278606316233727351873646828951346).isSome = true := by
  decide +kernel

theorem k3616_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3616) 2).1 3).2 1).1
      298248417799763907911064501190986351413554237859097860535940816896186091059255999405203602135035943000013884).isSome = true := by
  decide +kernel

theorem k3616_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3616) 2).1 3).2 1).2
      15786203986039483219986584375693409327606710629663385278576305393243920638987315338418).isSome = true := by
  decide +kernel

theorem k3616_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3616) 2).2 3).1 2).1
      63484759170332141903476095655298505629255543618717879248053305118433765555923861740337).isSome = true := by
  decide +kernel

theorem k3616_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3616) 2).2 3).1 2).2
      13452161886153394066354693301514668747740669993342920339914085324).isSome = true := by
  decide +kernel

theorem k3616_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3616) 2).2 3).2 2).1
      856601345173192392155917156668750573306333760818465927916955728956).isSome = true := by
  decide +kernel

theorem k3616_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3616) 2).2 3).2 2).2
      214210944260708967911706149931283852138965774019032204873557687356).isSome = true := by
  decide +kernel

theorem k3617_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3617) 2).1 3).1 2).1
      15726098317153245320991502492473532403791668127544334945985949604590088359978835888700).isSome = true := by
  decide +kernel

theorem k3617_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3617) 2).1 3).1 2).2
      853005567075976417812964206176492490128178671453737734904466502204).isSome = true := by
  decide +kernel

theorem k3617_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3617) 2).1 3).2 1).1
      212640368191431350536373017230761869837392544926624402757303913020).isSome = true := by
  decide +kernel

theorem k3617_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3617) 2).1 3).2 1).2
      980542481140064774977825925743965191148965246058663765798228379806249976172995016252).isSome = true := by
  decide +kernel

theorem k3617_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3617) 2).2 3).1 1).1
      213454664527692546222128920729508112955571728711319630567645740092).isSome = true := by
  decide +kernel

theorem k3617_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3617) 2).2 3).1 1).2
      213374676597247215532942834506899767814146065885192362600372730940).isSome = true := by
  decide +kernel

theorem k3617_6 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3617) 2).2 3).2
      1400537686514962510984358656437274631953077264486709296403019423156726608986997853467397111968698290699312203630793072819267039473).isSome = true := by
  decide +kernel

theorem k3618_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3618) 2).1 3).1
      412290366128085050245329831098422274217054065242767765285597062826097451397186676430121871289939033373901803449779270648445849603472136420829791826748).isSome = true := by
  decide +kernel

theorem k3618_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3618) 2).1 3).2
      348670354377086774759480039295461315548074249821674552321845050598141144649143153503576400783486830243691210320191427945361299697).isSome = true := by
  decide +kernel

theorem k3618_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3618) 2).2 3).1
      5591422569448323319786914650562479499500615676717731151073072342064970990972234109180631197829418854435194925836027015214122443580).isSome = true := by
  decide +kernel

theorem k3618_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3618) 2).2 3).2
      1395617698707871282655957412206354590999415992753769987945802743543309375658232478036525400471973677482485961407345128400383584497).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 3616 3619 :=
  (Cover.one (box := dirCellBox) (n := 3616)
      (.split 2 (.split 3 (.split 1 (.leaf _ k3616_0) (.leaf _ k3616_1)) (.split 1 (.leaf _ k3616_2) (.leaf _ k3616_3))) (.split 3 (.split 2 (.leaf _ k3616_4) (.leaf _ k3616_5)) (.split 2 (.leaf _ k3616_6) (.leaf _ k3616_7))))).trans <|
  (Cover.one (box := dirCellBox) (n := 3617)
      (.split 2 (.split 3 (.split 2 (.leaf _ k3617_0) (.leaf _ k3617_1)) (.split 1 (.leaf _ k3617_2) (.leaf _ k3617_3))) (.split 3 (.split 1 (.leaf _ k3617_4) (.leaf _ k3617_5)) (.leaf _ k3617_6)))).trans <|
  (Cover.one (box := dirCellBox) (n := 3618)
      (.split 2 (.split 3 (.leaf _ k3618_0) (.leaf _ k3618_1)) (.split 3 (.leaf _ k3618_2) (.leaf _ k3618_3))))

end C4.Cert.Dir120
