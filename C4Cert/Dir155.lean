module

public import C4Check

public section

/-! Cells `5270 ≤ n < 5303` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir155

theorem k5270_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 5270) 2).1
      266824909972479091563895875715089321106237142620966445807145023598723929949077456672202988706920742052438566718761350186006012282407).isSome = true := by
  decide +kernel

theorem k5270_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 5270) 2).2 3).1
      250955921097781993971854874950366485040634595651836146003668574866996753480738431416713).isSome = true := by
  decide +kernel

theorem k5270_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 5270) 2).2 3).2
      62636490901475017697446989847026852598299330272725214884871479576763340153625836979593).isSome = true := by
  decide +kernel

theorem k5271_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 5271) 2).1
      1393259340870916692255744374793868253983162046173040014647058824315629464767710903464999846469875690228287496521419850882107006151).isSome = true := by
  decide +kernel

theorem k5271_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 5271) 2).2 3).1
      15639134875848425805719465161807217172984226375330607733904108361079300521150246182113).isSome = true := by
  decide +kernel

theorem k5271_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 5271) 2).2 3).2
      976457219989110176770550244260185923430316678753296552297474471392475769026386712369).isSome = true := by
  decide +kernel

theorem k5272_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 5272) 2).1
      18412373211901865748933947452426910442253782612260986820565414886113470571720897876459483910402401385335495).isSome = true := by
  decide +kernel

theorem k5272_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 5272) 2).2 3).1
      243910772357083808741064883028859473642878266833087518547605068912574071695215548209).isSome = true := by
  decide +kernel

theorem k5272_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 5272) 2).2 3).2
      243741202644781409239299218882557715786419365386928856955390257903338404604215580465).isSome = true := by
  decide +kernel

theorem k5273_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 5273) 2).1
      21207010557175809131979162524633827708942705956122412491676907208754737148181647573306556240430769431647246004209622952166855).isSome = true := by
  decide +kernel

theorem k5273_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 5273) 2).2
      73587487638783571292901463702894382864475755778395289270865068536918081972930787722042865065185456190487731).isSome = true := by
  decide +kernel

theorem k5274_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 5274) 2).1
      60822909031666564720650975887130675636536427738459923080820851705356087980319065523).isSome = true := by
  decide +kernel

theorem k5274_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 5274) 2).2
      996581031864637617457356095687410960748788395115223007810467460237260622987968281334471).isSome = true := by
  decide +kernel

theorem c5 : allCells dirCell 5275 5276 [
    7382528131923019192377079006446837279064785134126361404455806901083595930058356980831005254435715588729403877599041421765044055389727440632352223471004321231226340806] = true := by
  decide +kernel

theorem c6 : allCells dirCell 5276 5277 [
    6250349664888783115836668826687200495239218861440774612813446045033282477182400503381433335644070546608992567563904335599048625019720746621003206] = true := by
  decide +kernel

theorem c7 : allCells dirCell 5277 5278 [
    5292984567495611692216416837304691083755168868417049543626554928376411557918543621554609936796252074128023342184668219512306] = true := by
  decide +kernel

theorem c8 : allCells dirCell 5278 5279 [
    17929434024207168916361063794748802336290747298080853660805488959718010496931142843510056197770602941810] = true := by
  decide +kernel

theorem c9 : allCells dirCell 5279 5280 [
    4481667109576167565436194552001004648881277910734876887610483583263027412283364045811767010377508433266] = true := by
  decide +kernel

theorem c10 : allCells dirCell 5280 5295 [
    15182400092040626593004213542311914452386843433804139930582843197819517153625020785,
    174268180139254132774918240856236556224017, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1] = true := by
  decide +kernel

theorem k5295_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 5295) 3).1
      63936123218627877823881660588303011375664948672284343973724432679470902480934135575754).isSome = true := by
  decide +kernel

theorem k5295_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 5295) 3).2
      260443365241374442594985606136679486156671419295442827576427768933171374334062163411866502).isSome = true := by
  decide +kernel

theorem k5296_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 5296) 3).1
      4903013199991257999062115351515787299655083191837208291896473134084943549402456832409389186815187685483934199430).isSome = true := by
  decide +kernel

theorem k5296_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 5296) 3).2 2).1
      252584227899713059570438654651275265621703906995367897870369115968647077751038003999537).isSome = true := by
  decide +kernel

theorem k5296_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 5296) 3).2 2).2
      742416770943822446641216934393946842385871490274).isSome = true := by
  decide +kernel

theorem k5297_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 5297) 2).1 3).1
      251846484540531275555046138124601088326674177577417381285816364651143965345264010359601).isSome = true := by
  decide +kernel

theorem k5297_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 5297) 2).1 3).2
      251491274937895980473697546077612700092304272776756833684452391250894044405021983208241).isSome = true := by
  decide +kernel

theorem k5297_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 5297) 2).2 3).1
      62985420896400096560866988737530409516895577537521996074670640599621682537580892877617).isSome = true := by
  decide +kernel

theorem k5297_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 5297) 2).2 3).2
      251536601172335787702292955513128147376342974305021488244093788736339933217660911842097).isSome = true := by
  decide +kernel

theorem k5298_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 5298) 2).1 3).1
      4016081215961540410074012218164932398156835933763948707942529037725205062034207003847473).isSome = true := by
  decide +kernel

theorem k5298_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 5298) 2).1 3).2
      1002489463095352474774333799578863641480051342627090580076880008280311875219175191414409).isSome = true := by
  decide +kernel

theorem k5298_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 5298) 2).2 3).1
      251057122573257434115208143604043591709637294652544195408176103556560352830674940293937).isSome = true := by
  decide +kernel

theorem k5298_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 5298) 2).2 3).2
      250663351773338279815537233555863023100267102049614055737564738303928366892236569670449).isSome = true := by
  decide +kernel

theorem k5299_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 5299) 2).1 3).1
      250289975665629988439304163614090824736207698336932059844292079110122908805324515686961).isSome = true := by
  decide +kernel

theorem k5299_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 5299) 2).1 3).2
      15626574567789948820183953187243647739604379742557555971014374848766325997701505375025).isSome = true := by
  decide +kernel

theorem k5299_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 5299) 2).2 3).1
      250339416687737947842984347243355723710399761918827474742140650347079152362607372497713).isSome = true := by
  decide +kernel

theorem k5299_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 5299) 2).2 3).2
      250072461499748607295062011831607249233374814616554169240216638121321570444284044343857).isSome = true := by
  decide +kernel

theorem k5300_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 5300) 2).1 3).1
      3903247472634711276152682140391715986074613532285751265573690398652336537758285420337).isSome = true := by
  decide +kernel

theorem k5300_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 5300) 2).1 3).2
      13215831341336805904676180815624251332510507458526892617658485708).isSome = true := by
  decide +kernel

theorem k5300_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 5300) 2).2 3).1
      15615982971306742798439770261290425354613232264743446671578633137536924900173352492593).isSome = true := by
  decide +kernel

theorem k5300_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 5300) 2).2 3).2
      3304501417633230909551672104520492044020604562978166304051419852).isSome = true := by
  decide +kernel

theorem k5301_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 5301) 2).1
      294400462649996694535588592735974102492510240697134681643846836229581165014425357100758993960156146743729351).isSome = true := by
  decide +kernel

theorem k5301_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 5301) 2).2
      5431421054224085750660138189998277920902651786505675077399545497045554129311994162775979488628193667258594093556072844652567347).isSome = true := by
  decide +kernel

theorem k5302_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 5302) 2).1
      62293907702538557194239927935721061741458341808880746779803442057978741054313092111539).isSome = true := by
  decide +kernel

theorem k5302_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 5302) 2).2
      18387701963564774664006616034534053886886925526976131915266108545582344043974132412030319483646695651531571).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 5270 5303 :=
  (Cover.one (box := dirCellBox) (n := 5270)
      (.split 2 (.leaf _ k5270_0) (.split 3 (.leaf _ k5270_1) (.leaf _ k5270_2)))).trans <|
  (Cover.one (box := dirCellBox) (n := 5271)
      (.split 2 (.leaf _ k5271_0) (.split 3 (.leaf _ k5271_1) (.leaf _ k5271_2)))).trans <|
  (Cover.one (box := dirCellBox) (n := 5272)
      (.split 2 (.leaf _ k5272_0) (.split 3 (.leaf _ k5272_1) (.leaf _ k5272_2)))).trans <|
  (Cover.one (box := dirCellBox) (n := 5273)
      (.split 2 (.leaf _ k5273_0) (.leaf _ k5273_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 5274)
      (.split 2 (.leaf _ k5274_0) (.leaf _ k5274_1))).trans <|
  (Cover.dir c5).trans <|
  (Cover.dir c6).trans <|
  (Cover.dir c7).trans <|
  (Cover.dir c8).trans <|
  (Cover.dir c9).trans <|
  (Cover.dir c10).trans <|
  (Cover.one (box := dirCellBox) (n := 5295)
      (.split 3 (.leaf _ k5295_0) (.leaf _ k5295_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 5296)
      (.split 3 (.leaf _ k5296_0) (.split 2 (.leaf _ k5296_1) (.leaf _ k5296_2)))).trans <|
  (Cover.one (box := dirCellBox) (n := 5297)
      (.split 2 (.split 3 (.leaf _ k5297_0) (.leaf _ k5297_1)) (.split 3 (.leaf _ k5297_2) (.leaf _ k5297_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 5298)
      (.split 2 (.split 3 (.leaf _ k5298_0) (.leaf _ k5298_1)) (.split 3 (.leaf _ k5298_2) (.leaf _ k5298_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 5299)
      (.split 2 (.split 3 (.leaf _ k5299_0) (.leaf _ k5299_1)) (.split 3 (.leaf _ k5299_2) (.leaf _ k5299_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 5300)
      (.split 2 (.split 3 (.leaf _ k5300_0) (.leaf _ k5300_1)) (.split 3 (.leaf _ k5300_2) (.leaf _ k5300_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 5301)
      (.split 2 (.leaf _ k5301_0) (.leaf _ k5301_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 5302)
      (.split 2 (.leaf _ k5302_0) (.leaf _ k5302_1)))

end C4.Cert.Dir155
