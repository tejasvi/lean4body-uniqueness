module

public import C4Check

public section

/-! Cells `2613 ≤ n < 2673` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir053

theorem k2613_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2613) 2).1 3).1
      216526125824511303439677554449731950532423684630052099663839883902012).isSome = true := by
  decide +kernel

theorem k2613_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2613) 2).1 3).2
      13524515368153009604675383315683741041658869515615176728550139444284).isSome = true := by
  decide +kernel

theorem k2613_2 : (checkBoxH dirMode depth (splitBox (dirCellBox 2613) 2).2
      1425482167380141594123144902916305261289344892129183633473897915058260437814078299031025213293926458753274953770949080196854487696188).isSome = true := by
  decide +kernel

theorem k2614_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2614) 2).1 3).1
      54065102294529094772996161659114953349883283788691295981718663380028).isSome = true := by
  decide +kernel

theorem k2614_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2614) 2).1 3).2
      45791618670751279938210556686407410738047269948).isSome = true := by
  decide +kernel

theorem k2614_2 : (checkBoxH dirMode depth (splitBox (dirCellBox 2614) 2).2
      1205427411525341484888632143049010592220114814200462449064660336312416230756870997058051702010524134639970272060).isSome = true := by
  decide +kernel

theorem k2615_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2615) 1).1
      4704098516096265569804450466462219056395153752682313447700379796543973375243884336169808681460487590585025340).isSome = true := by
  decide +kernel

theorem k2615_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 2615) 1).2
      1020685320123743717104756085825506598255000533606438813824332943932149605019216331968332604).isSome = true := by
  decide +kernel

theorem k2616_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2616) 1).1
      3372742342234448764941456971654454171796586566271506513525732788796).isSome = true := by
  decide +kernel

theorem k2616_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 2616) 1).2
      13492833059274330246066031651030938375436752150912492046712698565180).isSome = true := by
  decide +kernel

theorem c4 : allCells dirCell 2617 2618 [
    399781051536303027478200434130764735516124871194721258721888184528383303155302195618729949467595691139955266231965694277513930529113936568143672561] = true := by
  decide +kernel

theorem c5 : allCells dirCell 2618 2637 [
    205712099626152725420734130964069962519754529899960767997198417, 147534033823531077444, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] = true := by
  decide +kernel

theorem c6 : allCells dirCell 2637 2638 [
    290417022088677792201722409170319024771763930104263378644961037541268672835929290825004426124811244805707] = true := by
  decide +kernel

theorem k2638_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2638) 3).1
      1159369865093332613452912839210294430661786675131952536570343614180435449297890623173757154462542737274098).isSome = true := by
  decide +kernel

theorem k2638_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 2638) 3).2
      16062417121556930521785065561956407465874725512832765201055560854145553746920982513567986).isSome = true := by
  decide +kernel

theorem k2639_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2639) 2).1
      19380945751103826940509291773573034803849810320444517881367830299734248263602568785437857997022022550524479598833).isSome = true := by
  decide +kernel

theorem k2639_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 2639) 2).2
      302620417196311663471713467618063731114821621070705606010186617231202086433851473117888227625208793815573721331).isSome = true := by
  decide +kernel

theorem k2640_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2640) 2).1
      4191765956954600120489330847918043958080915607871941435216230517229805418788812016265825939699).isSome = true := by
  decide +kernel

theorem k2640_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 2640) 2).2
      1047945563986685398635798360757186683237643444701085865567447115788319308217322844322480320755).isSome = true := by
  decide +kernel

theorem k2641_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2641) 2).1
      75427478271006253572265079046461947157485540836598427583566623493008265823517528093291696758915957036072877116).isSome = true := by
  decide +kernel

theorem k2641_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 2641) 2).2
      3993096886424984127931401657692302967531932105447035716297416268307895663253143842241596).isSome = true := by
  decide +kernel

theorem k2642_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2642) 2).1
      63846641554783213605349123126266346036715084455686040766342348794883312725884956862038844).isSome = true := by
  decide +kernel

theorem k2642_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 2642) 2).2
      63815086050256460979062587872701935885549219103421681337880991412092545065745195876729660).isSome = true := by
  decide +kernel

theorem k2643_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2643) 1).1
      15564988171394244364579667062529917544617186305017620346508402237170239662694067597884).isSome = true := by
  decide +kernel

theorem k2643_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 2643) 1).2
      18378732099611827979092751506440830466936739927223647101186277748665223464936398479567248728125000034272060).isSome = true := by
  decide +kernel

theorem k2644_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2644) 1).1
      972165373537291728452611397627878336580028084403314305011448361027341728045775320636).isSome = true := by
  decide +kernel

theorem k2644_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 2644) 1).2
      210829264667487940700203024002703953965248555146702064482447247932).isSome = true := by
  decide +kernel

theorem c14 : allCells dirCell 2645 2646 [
    1354502728413561350770263879618798421073464024420542109520467616542979385013500142000634568757300830871165940800578188155385073] = true := by
  decide +kernel

theorem c15 : allCells dirCell 2646 2666 [
    51427674683424539715245549109535969700798612601547122357551569, 147532774539142367188, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2823080892478077474124066409278695417424147] = true := by
  decide +kernel

theorem c16 : allCells dirCell 2666 2667 [
    25792864575878547702475992501033560069299561745484645973209794425506769925824488284518017275677076987177840923804561541349981030833287060392488981959] = true := by
  decide +kernel

theorem k2667_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2667) 2).1
      295542085042495646372452784216661317198528123590178847559543774544078829972125042352719066357014001389878332).isSome = true := by
  decide +kernel

theorem k2667_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 2667) 2).2
      15643280999772451483895246513327523690559394553469620979062815158091279180187969115955).isSome = true := by
  decide +kernel

theorem k2668_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2668) 2).1
      999776270566837536400144056309901412854800178164087347760116564147244348055213495761980).isSome = true := by
  decide +kernel

theorem k2668_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 2668) 2).2
      999725082589566267212331631054138909519213793827782142210442945589065442647036849765436).isSome = true := by
  decide +kernel

theorem k2669_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2669) 2).1
      3993005949803098940929493626070140269877828677378857977036217960341496003789488744348732).isSome = true := by
  decide +kernel

theorem k2669_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 2669) 2).2
      54113779285156629971943560688264625350248812762757799595560683093052).isSome = true := by
  decide +kernel

theorem k2670_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2670) 1).1
      13512051071613876254483061323441538313126236386964294352579425452860).isSome = true := by
  decide +kernel

theorem k2670_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 2670) 1).2
      844639716192276517840203670854342747981315570059138984551124812604).isSome = true := by
  decide +kernel

theorem k2671_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2671) 1).1
      45739904045374458957212819687227435288951769660).isSome = true := by
  decide +kernel

theorem k2671_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 2671) 1).2
      45747263161982491759438951439499100550096996924).isSome = true := by
  decide +kernel

theorem k2672_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2672) 1).1
      243037134274060570315501837205683205338742090138098575584005211827681877479252162108).isSome = true := by
  decide +kernel

theorem k2672_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 2672) 1).2
      210835859057122464936486740395885214927492530885540755189837198908).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 2613 2673 :=
  (Cover.one (box := dirCellBox) (n := 2613)
      (.split 2 (.split 3 (.leaf _ k2613_0) (.leaf _ k2613_1)) (.leaf _ k2613_2))).trans <|
  (Cover.one (box := dirCellBox) (n := 2614)
      (.split 2 (.split 3 (.leaf _ k2614_0) (.leaf _ k2614_1)) (.leaf _ k2614_2))).trans <|
  (Cover.one (box := dirCellBox) (n := 2615)
      (.split 1 (.leaf _ k2615_0) (.leaf _ k2615_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 2616)
      (.split 1 (.leaf _ k2616_0) (.leaf _ k2616_1))).trans <|
  (Cover.dir c4).trans <|
  (Cover.dir c5).trans <|
  (Cover.dir c6).trans <|
  (Cover.one (box := dirCellBox) (n := 2638)
      (.split 3 (.leaf _ k2638_0) (.leaf _ k2638_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 2639)
      (.split 2 (.leaf _ k2639_0) (.leaf _ k2639_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 2640)
      (.split 2 (.leaf _ k2640_0) (.leaf _ k2640_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 2641)
      (.split 2 (.leaf _ k2641_0) (.leaf _ k2641_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 2642)
      (.split 2 (.leaf _ k2642_0) (.leaf _ k2642_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 2643)
      (.split 1 (.leaf _ k2643_0) (.leaf _ k2643_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 2644)
      (.split 1 (.leaf _ k2644_0) (.leaf _ k2644_1))).trans <|
  (Cover.dir c14).trans <|
  (Cover.dir c15).trans <|
  (Cover.dir c16).trans <|
  (Cover.one (box := dirCellBox) (n := 2667)
      (.split 2 (.leaf _ k2667_0) (.leaf _ k2667_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 2668)
      (.split 2 (.leaf _ k2668_0) (.leaf _ k2668_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 2669)
      (.split 2 (.leaf _ k2669_0) (.leaf _ k2669_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 2670)
      (.split 1 (.leaf _ k2670_0) (.leaf _ k2670_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 2671)
      (.split 1 (.leaf _ k2671_0) (.leaf _ k2671_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 2672)
      (.split 1 (.leaf _ k2672_0) (.leaf _ k2672_1)))

end C4.Cert.Dir053
