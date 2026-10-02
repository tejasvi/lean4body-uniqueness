module

public import C4Check

public section

/-! Cells `3702 ≤ n < 3714` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir126

theorem k3702_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3702) 2).1 3).1
      3326203821052509025160137313681606347624119872789336843377562572).isSome = true := by
  decide +kernel

theorem k3702_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3702) 2).1 3).2
      62713819261335216356592182972127699005840228385618715259797860982725404481011175994316).isSome = true := by
  decide +kernel

theorem k3702_2 : (checkBoxH dirMode depth (splitBox (dirCellBox 3702) 2).2
      87435153176630443357197872100470340058035599235547914385507877810661606942884066522288580889801706129840472082965445076158205747).isSome = true := by
  decide +kernel

theorem k3703_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3703) 2).1 3).1
      62622390840844558767094170543331124992598031414671288510812016175931845431783099022396).isSome = true := by
  decide +kernel

theorem k3703_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3703) 2).1 3).2
      52975621048025189854799142318282663958128126727306669723081325628).isSome = true := by
  decide +kernel

theorem k3703_2 : (checkBoxH dirMode depth (splitBox (dirCellBox 3703) 2).2
      5580614077128680120228445600982982863089558126198411488209634834610306588249069968406089474171465166664673123562462392232012369715).isSome = true := by
  decide +kernel

theorem k3704_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3704) 2).1
      4189111834143756680616178051695190884812478505848134426827624787028623803886916041069974319347).isSome = true := by
  decide +kernel

theorem k3704_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 3704) 2).2
      4830929956244258649763896972147240911371495425633435936222660350569082342924104571185212066713884564645681098995).isSome = true := by
  decide +kernel

theorem k3705_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3705) 3).1
      1178600904161967940096434622758214409571307200927227405751952031728199026414561766033779955062454843503606844).isSome = true := by
  decide +kernel

theorem k3705_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 3705) 3).2
      18845887338101035592690798107669554794722184524104802262358445285384980119171915674412456863439704970627105596).isSome = true := by
  decide +kernel

theorem k3706_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3706) 1).1
      1020868479271749910734516876020896376062925809972970428965487571678441241857653047731143484).isSome = true := by
  decide +kernel

theorem k3706_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 3706) 1).2
      4083396056663288693513365687673515435920822163702993785481558020255548774605034292331397948).isSome = true := by
  decide +kernel

theorem k3707_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3707) 3).1
      4705383937096679965262817515363422320207158365600654490334080399981096565715985066061455968530928561843847996).isSome = true := by
  decide +kernel

theorem k3707_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 3707) 3).2
      3375066106463009967079423697555598858730169844616329941091450602300).isSome = true := by
  decide +kernel

theorem c6 : allCells dirCell 3708 3709 [
    6400750853608718880042862077616116494510648728533863050881689291141154869147285432739925613038783530969110706280233731836649952337003416951707386684] = true := by
  decide +kernel

theorem k3709_0 : (checkBoxH dirMode depth (dirCellBox 3709)
      102371209570912624262498084906082587861660468823110251455156435008443518677340490614224692094887693089694660297243266314365371140581076433578171024188).isSome = true := by
  decide +kernel

theorem c8 : allCells dirCell 3710 3711 [
    1387047363071587523324732824783050969629493579539090277380518824056114985574611413774539893451786022403197495728688479121488415986] = true := by
  decide +kernel

theorem c9 : allCells dirCell 3711 3712 [
    15546057105601032187151125183114546515250423136494041785256158742524440385420671828796] = true := by
  decide +kernel

theorem c10 : allCells dirCell 3712 3714 [
    62174122552025923237276294551958555716613132772582226935971680467387164130241631167292,
    51424467577286049177691442508367332382113337793899262823903633] = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 3702 3714 :=
  (Cover.one (box := dirCellBox) (n := 3702)
      (.split 2 (.split 3 (.leaf _ k3702_0) (.leaf _ k3702_1)) (.leaf _ k3702_2))).trans <|
  (Cover.one (box := dirCellBox) (n := 3703)
      (.split 2 (.split 3 (.leaf _ k3703_0) (.leaf _ k3703_1)) (.leaf _ k3703_2))).trans <|
  (Cover.one (box := dirCellBox) (n := 3704)
      (.split 2 (.leaf _ k3704_0) (.leaf _ k3704_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 3705)
      (.split 3 (.leaf _ k3705_0) (.leaf _ k3705_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 3706)
      (.split 1 (.leaf _ k3706_0) (.leaf _ k3706_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 3707)
      (.split 3 (.leaf _ k3707_0) (.leaf _ k3707_1))).trans <|
  (Cover.dir c6).trans <|
  (Cover.one (box := dirCellBox) (n := 3709)
      (.leaf _ k3709_0)).trans <|
  (Cover.dir c8).trans <|
  (Cover.dir c9).trans <|
  (Cover.dir c10)

end C4.Cert.Dir126
