module

public import C4Check

public section

/-! Cells `2194 ≤ n < 2249` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir034

theorem k2194_0 : (checkBoxH dirMode depth (dirCellBox 2194)
      1640256615804699734936840657552829658306618793431154655559509779511833774003976965763716092446092261321184228089763756868203800625574271371655982859068).isSome = true := by
  decide +kernel

theorem c1 : allCells dirCell 2195 2196 [
    1388213055868997381216852423317502191438149909881567777112078661942708358227244850457388685831411921992188863431687387612341192945] = true := by
  decide +kernel

theorem c2 : allCells dirCell 2196 2197 [
    84672383894009154735151039613006979756346241120328110055949395335117980294090556818776313574445995187671999397838534483996924] = true := by
  decide +kernel

theorem c3 : allCells dirCell 2197 2217 [
    51431557620037514655698944510537745255974174087391315945079249, 147520610779390519076, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] = true := by
  decide +kernel

theorem c4 : allCells dirCell 2217 2218 [
    5359065637616204743788428544396620706996172937155851776814022698393049498844696585127948859300665088652369051230515848487751] = true := by
  decide +kernel

theorem k2218_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2218) 2).1
      5343104860104272791649476847358405721982517966407253531130709209114177278452286858607502835114794084676657791471271634523964).isSome = true := by
  decide +kernel

theorem k2218_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 2218) 2).2
      72339785650691934497498161217042800080796257801881926354615132166050507348879735779682461913120341942643).isSome = true := by
  decide +kernel

theorem k2219_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2219) 3).1
      250610601876557706378584495948932037709794437253048758619265799280053371381525235175228).isSome = true := by
  decide +kernel

theorem k2219_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 2219) 3).2
      15644226796791212345003664426186617852294912501236702917244403006695565662740238816060).isSome = true := by
  decide +kernel

theorem k2220_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2220) 3).1
      54213540785968792880771457273881383406703086222688458016064131576636).isSome = true := by
  decide +kernel

theorem k2220_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 2220) 3).2
      3385492954649566153552093526809787662999722603530574735805121020732).isSome = true := by
  decide +kernel

theorem k2221_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2221) 2).1
      13524362200593916175338547459178192820421230559828218844916021445436).isSome = true := by
  decide +kernel

theorem k2221_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 2221) 2).2
      3381614824670452138409766562573000608506476635841717899241589293884).isSome = true := by
  decide +kernel

theorem k2222_0 : (checkBoxH dirMode depth (dirCellBox 2222)
      410086872941236901264121194289398416737835901191168492060754476688070422839202062716620307950284055729782528545821949306668052341825439657182965281596).isSome = true := by
  decide +kernel

theorem c10 : allCells dirCell 2223 2224 [
    287068868684167206918542208740892544707484092817254946481241276442094630100609134463341429368050706535228] = true := by
  decide +kernel

theorem c11 : allCells dirCell 2224 2245 [
    971951004385685487388693955337369627948463851710488161280004425619733332960034517244,
    43558898321064228243663259722630712172636, 147518965222831191172, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0] = true := by
  decide +kernel

theorem c12 : allCells dirCell 2245 2246 [
    705976358278384626127187242918748472178115] = true := by
  decide +kernel

theorem c13 : allCells dirCell 2246 2247 [
    100811732653625308280533522808386417790195296750099138023529992822413669449558396606787019918163293386136064813004366427305903095198012427509003763] = true := by
  decide +kernel

theorem k2247_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2247) 1).1
      62601603034484462573101659238346712446176496983533802411569324405349679596773574169404).isSome = true := by
  decide +kernel

theorem k2247_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 2247) 1).2
      54304508243025768741651746316401066079274179719910081884589565686588).isSome = true := by
  decide +kernel

theorem c15 : allCells dirCell 2248 2249 [
    348302887954746445855818572104097886159767840162336836221115502902105933283806998925677312652253464097002293607301454481572479804] = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 2194 2249 :=
  (Cover.one (box := dirCellBox) (n := 2194)
      (.leaf _ k2194_0)).trans <|
  (Cover.dir c1).trans <|
  (Cover.dir c2).trans <|
  (Cover.dir c3).trans <|
  (Cover.dir c4).trans <|
  (Cover.one (box := dirCellBox) (n := 2218)
      (.split 2 (.leaf _ k2218_0) (.leaf _ k2218_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 2219)
      (.split 3 (.leaf _ k2219_0) (.leaf _ k2219_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 2220)
      (.split 3 (.leaf _ k2220_0) (.leaf _ k2220_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 2221)
      (.split 2 (.leaf _ k2221_0) (.leaf _ k2221_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 2222)
      (.leaf _ k2222_0)).trans <|
  (Cover.dir c10).trans <|
  (Cover.dir c11).trans <|
  (Cover.dir c12).trans <|
  (Cover.dir c13).trans <|
  (Cover.one (box := dirCellBox) (n := 2247)
      (.split 1 (.leaf _ k2247_0) (.leaf _ k2247_1))).trans <|
  (Cover.dir c15)

end C4.Cert.Dir034
