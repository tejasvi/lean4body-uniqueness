module

public import C4Check

public section

/-! Cells `3738 ≤ n < 3767` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir128

theorem c0 : allCells dirCell 3738 3739 [
    346770221459955168767344091529977742311847014114064674177460830344652082953411783136803444106581775048940717017235805974320628540] = true := by
  decide +kernel

theorem c1 : allCells dirCell 3739 3740 [
    15546474941359697495363730592425940146952044943582689446968081831378140189495924343612] = true := by
  decide +kernel

theorem c2 : allCells dirCell 3740 3756 [
    3291539821676687231810308324164890135792165625554979850396488508,
    43557098115218963323828788807943956005212, 147559084203055130404, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 38806227839729809994771] = true := by
  decide +kernel

theorem c3 : allCells dirCell 3756 3757 [
    6512817734272276665089645608691104856579386458980430351403435539550954611263019926305907157829754110142818719389935766861941944662750894125578401227] = true := by
  decide +kernel

theorem k3757_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3757) 2).1
      3937051885729296172222948462583476142903222745659697838862995799229996725282950108979).isSome = true := by
  decide +kernel

theorem k3757_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 3757) 2).2
      3936825946415335976408209599670056521420659810505907219440913717171846297721858856755).isSome = true := by
  decide +kernel

theorem k3758_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3758) 2).1
      16078282534916734744790066469967340556541171370460399952180371766051150848626685688101948).isSome = true := by
  decide +kernel

theorem k3758_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 3758) 2).2
      4630648347416790086139758184364493384701793062962623141634910037020500026296138285858224460173256929023795).isSome = true := by
  decide +kernel

theorem k3759_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3759) 2).1
      16032051211213412531489777935939325327293876795180849867481893055945444148005490444680252).isSome = true := by
  decide +kernel

theorem k3759_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 3759) 2).2
      13905664973671657659215804256944364568598716650938453740545130573806652).isSome = true := by
  decide +kernel

theorem k3760_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3760) 2).1
      867244389620452372147951607676774368281545585036870074504954893253692).isSome = true := by
  decide +kernel

theorem k3760_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 3760) 2).2
      867329781906462972741757586767269898975309109418961187292518514113596).isSome = true := by
  decide +kernel

theorem k3761_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3761) 1).1
      865976710746481011224341049421646892040854500259197514221298605308988).isSome = true := by
  decide +kernel

theorem k3761_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 3761) 1).2
      865962419442992345117985163100972649944488654745138080475574071147580).isSome = true := by
  decide +kernel

theorem k3762_0 : (checkBoxH dirMode depth (dirCellBox 3762)
      420138013587800824470249807259449787178004202297967877250541202587177586333826342892001652145721733770908952119336648390773349251646312838708602103348284).isSome = true := by
  decide +kernel

theorem k3763_0 : (checkBoxH dirMode depth (dirCellBox 3763)
      484008266753443433406887511050821568469538202670712101054354571496427514851010150550437872843739985911707130200403094905631728336746455366039363064015665500208936019542844).isSome = true := by
  decide +kernel

theorem c11 : allCells dirCell 3764 3765 [
    75255471754107845272626001200522955597219189723215714988707410065355170250970024172290042155902196589815382844] = true := by
  decide +kernel

theorem c12 : allCells dirCell 3765 3766 [
    75221913798620010121866176225780509366068052376142405591667695336325278346587215875160440669577815665973117756] = true := by
  decide +kernel

theorem c13 : allCells dirCell 3766 3767 [
    15550618307981288059270827901058856684810278253656789973398002662928340118294941385532] = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 3738 3767 :=
  (Cover.dir c0).trans <|
  (Cover.dir c1).trans <|
  (Cover.dir c2).trans <|
  (Cover.dir c3).trans <|
  (Cover.one (box := dirCellBox) (n := 3757)
      (.split 2 (.leaf _ k3757_0) (.leaf _ k3757_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 3758)
      (.split 2 (.leaf _ k3758_0) (.leaf _ k3758_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 3759)
      (.split 2 (.leaf _ k3759_0) (.leaf _ k3759_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 3760)
      (.split 2 (.leaf _ k3760_0) (.leaf _ k3760_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 3761)
      (.split 1 (.leaf _ k3761_0) (.leaf _ k3761_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 3762)
      (.leaf _ k3762_0)).trans <|
  (Cover.one (box := dirCellBox) (n := 3763)
      (.leaf _ k3763_0)).trans <|
  (Cover.dir c11).trans <|
  (Cover.dir c12).trans <|
  (Cover.dir c13)

end C4.Cert.Dir128
