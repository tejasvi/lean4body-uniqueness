module

public import C4Check

public section

/-! Cells `0 ≤ n < 512` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir000

theorem c0 : allCells dirCell 0 93 [
    0, 0, 0, 0, 0, 0, 0, 0, 0,
    3447173556042530888885443824731053832049915722423315408416013064388858, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 61502, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 11132179478990890675978854984313808660696142, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] = true := by
  decide +kernel

theorem c1 : allCells dirCell 93 205 [
    44534080603326564434068039260907663156489478, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 44533688605738791191523182760692827372977414, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 589320013441896257555, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2357728254290666657345, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] = true := by
  decide +kernel

theorem c2 : allCells dirCell 205 345 [
    2357844560631483055937, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 2357968169928256206401, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 2358091271250484567105, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 2358209998715345699137, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2358322616194016610881, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] = true := by
  decide +kernel

theorem c3 : allCells dirCell 345 400 [
    2358428524452683668545, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 2358527703700152811073, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0] = true := by
  decide +kernel

theorem k400_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 400) 2).1
      86714495288149870978589364152244671996197050835408686534405170276650722549862896839694359890927166073177799197631663405615232030).isSome = true := by
  decide +kernel

theorem k400_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 400) 2).2
      73448682314441408366534101236957438759417605537755340097331094407448414732708577449334322477308312834658375).isSome = true := by
  decide +kernel

theorem k401_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 401) 2).1
      1353632194964845569164649173713307483223428953471062303968469622466708068576997869530431367609868864887944660101315174829620510).isSome = true := by
  decide +kernel

theorem k401_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 401) 2).2 2).1
      971343096354975855875370994975720990886127491559953503230946312083065452495109708167).isSome = true := by
  decide +kernel

theorem k401_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 401) 2).2 2).2
      3886097361506986724077428777441792063937567716082758682005305581779668692221223885191).isSome = true := by
  decide +kernel

theorem c6 : allCells dirCell 402 428 [
    11410820711147340245776542721537716903426983430, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0] = true := by
  decide +kernel

theorem k428_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 428) 2).1
      1148077832378164320996148571822051452792457763503830989951282725243417152107926451185894773555514848433927).isSome = true := by
  decide +kernel

theorem k428_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 428) 2).2
      972908854179654641986770069890134162555501554666050761008076219749968884863878696199).isSome = true := by
  decide +kernel

theorem k429_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 429) 2).1
      346589739135883461785230658694007749983250897081490514665890033073606876056282887891201087839633270754722719337057635695309841703).isSome = true := by
  decide +kernel

theorem k429_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 429) 2).2
      293599466962328201136060816496772329554791115262997463860742536818288549077573165936018020664035770117661895).isSome = true := by
  decide +kernel

theorem c9 : allCells dirCell 430 456 [
    44567690402966580448667688449681581589995598, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0] = true := by
  decide +kernel

theorem c10 : allCells dirCell 456 457 [
    7561723329266466676500147471947590888261974185883930234457678533909893564814188145091169817500052220010827976514179101390316159360267057746073053304428547647314798093339] = true := by
  decide +kernel

theorem k457_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 457) 3).1
      1387768482811826890569435143847058143459955580600838381185247046098234786196893703845427750187640360838992041726909814306997957830).isSome = true := by
  decide +kernel

theorem k457_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 457) 3).2
      62168103823687706985139359566432552967878859530057092659763485646197967816558544259398).isSome = true := by
  decide +kernel

theorem c12 : allCells dirCell 458 484 [
    44562160731565427271402016658746334121318662, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0] = true := by
  decide +kernel

theorem k484_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 484) 3).1
      15200344494691587901423996939455848001567283063202641287582743675139904714521921906).isSome = true := by
  decide +kernel

theorem k484_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 484) 3).2
      21194505897032401770202695691836447249317725521413466817198925774695009159934456508696739979115076114781622194345025597670726).isSome = true := by
  decide +kernel

theorem k485_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 485) 3).1
      399894046138987367781062704273441813352140259286497273775757202429897764976385865150878787370549989271187543612360390472496839777992968253098909490).isSome = true := by
  decide +kernel

theorem k485_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 485) 3).2
      3291657895850106545493519859237411443675601010399991436153851921).isSome = true := by
  decide +kernel

theorem c15 : allCells dirCell 486 512 [
    44558431561741002351390958078409514354874630, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0] = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 0 512 :=
  (Cover.dir c0).trans <|
  (Cover.dir c1).trans <|
  (Cover.dir c2).trans <|
  (Cover.dir c3).trans <|
  (Cover.one (box := dirCellBox) (n := 400)
      (.split 2 (.leaf _ k400_0) (.leaf _ k400_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 401)
      (.split 2 (.leaf _ k401_0) (.split 2 (.leaf _ k401_1) (.leaf _ k401_2)))).trans <|
  (Cover.dir c6).trans <|
  (Cover.one (box := dirCellBox) (n := 428)
      (.split 2 (.leaf _ k428_0) (.leaf _ k428_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 429)
      (.split 2 (.leaf _ k429_0) (.leaf _ k429_1))).trans <|
  (Cover.dir c9).trans <|
  (Cover.dir c10).trans <|
  (Cover.one (box := dirCellBox) (n := 457)
      (.split 3 (.leaf _ k457_0) (.leaf _ k457_1))).trans <|
  (Cover.dir c12).trans <|
  (Cover.one (box := dirCellBox) (n := 484)
      (.split 3 (.leaf _ k484_0) (.leaf _ k484_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 485)
      (.split 3 (.leaf _ k485_0) (.leaf _ k485_1))).trans <|
  (Cover.dir c15)

end C4.Cert.Dir000
