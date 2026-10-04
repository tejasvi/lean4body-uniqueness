module

public import C4Check

public section

/-! Cells `4515 ≤ n < 4543` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir144

theorem k4515_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4515) 2).1 3).1
      5584920593377847156410140321069209165501254955897405862908716758868436032287915739482185848803561628422096143961275969172030343985).isSome = true := by
  decide +kernel

theorem k4515_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4515) 2).1 3).2
      4725023333537032258534575808265880860213775726241535956877642377988877741364734754263617297953035397488954161).isSome = true := by
  decide +kernel

theorem k4515_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4515) 2).2 3).1
      64122948321237900830694755870363545299863934335375453972477252129138798839927882747851569).isSome = true := by
  decide +kernel

theorem k4515_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4515) 2).2 3).2
      4003058059303977340195431143567372490641586640799699630277148752591950804086335424803633).isSome = true := by
  decide +kernel

theorem k4516_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4516) 2).1 3).1
      4610289750882619102205402227014548497850717169626453343766004611131265685617635364829204848600164237011660).isSome = true := by
  decide +kernel

theorem k4516_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4516) 2).1 3).2
      3901943358800949666151844179528609293384849995370659635789858177607520623736988883660).isSome = true := by
  decide +kernel

theorem k4516_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4516) 2).2 3).1
      15996652128152783363149831225155098132561479706181242021637738768048684951000359938411313).isSome = true := by
  decide +kernel

theorem k4516_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4516) 2).2 3).2
      846218129124349309635402833371847362476091055233197496508692245196).isSome = true := by
  decide +kernel

theorem k4517_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4517) 2).1 3).1
      62389140674740655416335394810317476659879750305346941165824706788664260500572231019580).isSome = true := by
  decide +kernel

theorem k4517_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4517) 2).1 3).2
      62354121441606280192882643481396162147307034794981178861427495235803134077787822242876).isSome = true := by
  decide +kernel

theorem k4517_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4517) 2).2 3).1
      845633738406908468002588419994381998476994123776161031469049785036).isSome = true := by
  decide +kernel

theorem k4517_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4517) 2).2 3).2
      3897668092328986935724114902736320506791392501221124586984174067089149696597699320524).isSome = true := by
  decide +kernel

theorem k4518_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4518) 2).1 3).1
      844657088070916158011287488363765224874803671043365951242119605308).isSome = true := by
  decide +kernel

theorem k4518_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4518) 2).1 3).2
      211081043337336398467411210449347307367774111668733060423458536508).isSome = true := by
  decide +kernel

theorem k4518_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4518) 2).2 3).1
      15583063258622474532440245297398922763565666217731688060166919513181823228199061793852).isSome = true := by
  decide +kernel

theorem k4518_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4518) 2).2 3).2
      52775869571860677368318532057547511550436823257068472509700877372).isSome = true := by
  decide +kernel

theorem k4519_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4519) 3).1
      88897109524941255866679867426981640296285257204480348515328426987477999725730547450439193574804482264328696960120467598156485554418).isSome = true := by
  decide +kernel

theorem k4519_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4519) 3).2
      77082792530724973395417563253945832092892001650121333380874563609225519680996105955294407308839298376727193121009).isSome = true := by
  decide +kernel

theorem k4520_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4520) 3).1
      347063161892350762955158953914414518558975170034129607570528602521512627028596756048134239732093716113380737207380237280273744700).isSome = true := by
  decide +kernel

theorem k4520_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4520) 3).2
      75241251404752207778279413846044790243454443088597007305955578937452525447088608542948720112618986703577662268).isSome = true := by
  decide +kernel

theorem k4521_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4521) 1).1
      293835197091346515156942761117087887086350437058055590809804273002940739485439734470809430142626701120619324).isSome = true := by
  decide +kernel

theorem k4521_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4521) 1).2
      346902078885507127413127750800495781612706602717135533449396408674817059677870555034946878868918151341304264935719054840973697852).isSome = true := by
  decide +kernel

theorem k4522_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4522) 3).1
      995349174944292798358752006388448964020457509822367034214366850366828898427241922241340).isSome = true := by
  decide +kernel

theorem k4522_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4522) 3).2
      13489505963097429693809383425823525665210701692706602934270634697532).isSome = true := by
  decide +kernel

theorem k4523_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4523) 1).1
      842861012320328044842792074148772117390657317637559897628100391484).isSome = true := by
  decide +kernel

theorem k4523_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4523) 1).2
      15548570778175994582801683111214769554762737437499186769499076249066326279916568957756).isSome = true := by
  decide +kernel

theorem k4524_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4524) 2).1
      971615572342981634913125871279628868852781495794037494652663318991516550071903048508).isSome = true := by
  decide +kernel

theorem k4524_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4524) 2).2
      62183697718338311442204424578625744165061292785989163983554322786408940555479627539260).isSome = true := by
  decide +kernel

theorem c10 : allCells dirCell 4525 4526 [
    18351579569106690818026906426774793880279247579382789300865467068091957183180560192431943261503212905132273] = true := by
  decide +kernel

theorem c11 : allCells dirCell 4526 4527 [
    73399272663378431584193952799271934699818006619966262826413925158688678733222187121934337535749164784535793] = true := by
  decide +kernel

theorem c12 : allCells dirCell 4527 4540 [
    51423279103073440014027275908852791485742721393519035525927057, 147564823035289068500, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0,
    995300781326318639781499112962830364579537405076534801029412209047068542572019278947] = true := by
  decide +kernel

theorem k4540_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4540) 3).1
      253711944194076182014427057704762719807323798975563792956681235330457439849378713703622).isSome = true := by
  decide +kernel

theorem k4540_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4540) 3).2
      66338180156184427191818612876119247448383822033198416575065813660035577653856721871160888522).isSome = true := by
  decide +kernel

theorem k4541_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4541) 2).1 3).1
      3939938226092030044562798212944674667776568008347981900404703765021482630421228679884).isSome = true := by
  decide +kernel

theorem k4541_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4541) 2).1 3).2
      15737448554495012427713139442973163311335898154817203792163794518450635284268147080396).isSome = true := by
  decide +kernel

theorem k4541_2 : (checkBoxH dirMode depth (splitBox (dirCellBox 4541) 2).2
      1403835004639654719599536763063416926909771792502354915671172065115811937733766601314891111712781541528577176481954392905272994611).isSome = true := by
  decide +kernel

theorem k4542_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4542) 2).1 3).1
      4020451880077579339432968047416868024855791862767500873453476592308002270436313624048433).isSome = true := by
  decide +kernel

theorem k4542_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4542) 2).1 3).2
      18512138843839433207865265882797733022677463904933240842309238867999948461036235874025628048363481768344780).isSome = true := by
  decide +kernel

theorem k4542_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4542) 2).2 3).1
      981235038603458816584650002216216509409313184301784944468047416694335966974230494412).isSome = true := by
  decide +kernel

theorem k4542_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4542) 2).2 3).2
      850098416465266378654524185167763868357432924622741216189272485068).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 4515 4543 :=
  (Cover.one (box := dirCellBox) (n := 4515)
      (.split 2 (.split 3 (.leaf _ k4515_0) (.leaf _ k4515_1)) (.split 3 (.leaf _ k4515_2) (.leaf _ k4515_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 4516)
      (.split 2 (.split 3 (.leaf _ k4516_0) (.leaf _ k4516_1)) (.split 3 (.leaf _ k4516_2) (.leaf _ k4516_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 4517)
      (.split 2 (.split 3 (.leaf _ k4517_0) (.leaf _ k4517_1)) (.split 3 (.leaf _ k4517_2) (.leaf _ k4517_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 4518)
      (.split 2 (.split 3 (.leaf _ k4518_0) (.leaf _ k4518_1)) (.split 3 (.leaf _ k4518_2) (.leaf _ k4518_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 4519)
      (.split 3 (.leaf _ k4519_0) (.leaf _ k4519_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 4520)
      (.split 3 (.leaf _ k4520_0) (.leaf _ k4520_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 4521)
      (.split 1 (.leaf _ k4521_0) (.leaf _ k4521_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 4522)
      (.split 3 (.leaf _ k4522_0) (.leaf _ k4522_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 4523)
      (.split 1 (.leaf _ k4523_0) (.leaf _ k4523_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 4524)
      (.split 2 (.leaf _ k4524_0) (.leaf _ k4524_1))).trans <|
  (Cover.dir c10).trans <|
  (Cover.dir c11).trans <|
  (Cover.dir c12).trans <|
  (Cover.one (box := dirCellBox) (n := 4540)
      (.split 3 (.leaf _ k4540_0) (.leaf _ k4540_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 4541)
      (.split 2 (.split 3 (.leaf _ k4541_0) (.leaf _ k4541_1)) (.leaf _ k4541_2))).trans <|
  (Cover.one (box := dirCellBox) (n := 4542)
      (.split 2 (.split 3 (.leaf _ k4542_0) (.leaf _ k4542_1)) (.split 3 (.leaf _ k4542_2) (.leaf _ k4542_3))))

end C4.Cert.Dir144
