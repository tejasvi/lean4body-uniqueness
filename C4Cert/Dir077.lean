module

public import C4Check

public section

/-! Cells `2918 ≤ n < 2944` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir077

theorem k2918_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2918) 2).1 3).1
      212976733652015552455800285424216057843589745308568467851932320572).isSome = true := by
  decide +kernel

theorem k2918_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2918) 2).1 3).2
      850318481058970513655460325883370961155252524107693243454755160892).isSome = true := by
  decide +kernel

theorem k2918_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2918) 2).2 3).1
      213013426548322658400720033493919530551036194732438421637523030844).isSome = true := by
  decide +kernel

theorem k2918_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2918) 2).2 3).2
      212619316263835244969998772999432033886711469241290362513920607036).isSome = true := by
  decide +kernel

theorem k2919_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2919) 2).1
      498143762208753822603933596371431133372317600500524626802647634829605432985596393531623916783872113515457620349835395668831389684110651872182297273598669474823878059161011004).isSome = true := by
  decide +kernel

theorem k2919_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 2919) 2).2
      22329764137642108973204689899491477036485761093646422006359848732496034567406858037150234650188371015335351441426031317930581815539).isSome = true := by
  decide +kernel

theorem k2920_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2920) 2).1
      1684062996755380483667790426665120136613082264652365106353078917024940815564580585241628310841934182028363983595841742117374338940833696310676827808005180).isSome = true := by
  decide +kernel

theorem k2920_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 2920) 2).2
      105276356573441795690287072411450420126589095191896960033082828733233499321405928367411539969705751435364280357853609401367874423717536944543151853993020).isSome = true := by
  decide +kernel

theorem k2921_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2921) 3).1
      1642794114937031185521693335607472295945115497793198374739436250100456831673269779302707193454798198342390073529532795875226005601909589925952542686268).isSome = true := by
  decide +kernel

theorem k2921_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 2921) 3).2
      301522685121625321500940744901426683908258381163109922885689388871187716125144719545933685914085586432630668348).isSome = true := by
  decide +kernel

theorem k2922_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2922) 3).1
      15954661870344143910851220115149744373072536089585540853642779466114252368712052004568124).isSome = true := by
  decide +kernel

theorem k2922_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 2922) 3).2
      15947548345450328963288536729890706462079441471030776975135622434031097711542683886107708).isSome = true := by
  decide +kernel

theorem k2923_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2923) 1).1
      15938269586300017393323947716492753273777980254480432857306231722364251410944585133931580).isSome = true := by
  decide +kernel

theorem k2923_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 2923) 1).2
      996158813611187723534536311274004357564316736055700432539255587507719214895675938651196).isSome = true := by
  decide +kernel

theorem c6 : allCells dirCell 2924 2925 [
    22200336764178379516930836897569516751141185480101234407384566547709724923387591060074594090751276085299602233615421380731673571571] = true := by
  decide +kernel

theorem c7 : allCells dirCell 2925 2926 [
    5548448854779111699487072009997281456052754491646913317917477929346291324677231108619252471998039175519430071604146606231467836220] = true := by
  decide +kernel

theorem c8 : allCells dirCell 2926 2927 [
    286777319536448910102827559784461474786017844795434134996546995459781155454366454164520437694801009693500] = true := by
  decide +kernel

theorem c9 : allCells dirCell 2927 2944 [
    51427325849079747945326444646334381016054570707354885668380369, 147549062704264859140, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9728625528836723558691] = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 2918 2944 :=
  (Cover.one (box := dirCellBox) (n := 2918)
      (.split 2 (.split 3 (.leaf _ k2918_0) (.leaf _ k2918_1)) (.split 3 (.leaf _ k2918_2) (.leaf _ k2918_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 2919)
      (.split 2 (.leaf _ k2919_0) (.leaf _ k2919_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 2920)
      (.split 2 (.leaf _ k2920_0) (.leaf _ k2920_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 2921)
      (.split 3 (.leaf _ k2921_0) (.leaf _ k2921_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 2922)
      (.split 3 (.leaf _ k2922_0) (.leaf _ k2922_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 2923)
      (.split 1 (.leaf _ k2923_0) (.leaf _ k2923_1))).trans <|
  (Cover.dir c6).trans <|
  (Cover.dir c7).trans <|
  (Cover.dir c8).trans <|
  (Cover.dir c9)

end C4.Cert.Dir077
