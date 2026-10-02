module

public import C4Check

public section

/-! Cells `2864 ≤ n < 2888` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir074

theorem k2864_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2864) 3).1 2).1
      3902328922930876647032613281410981654664822525821336003748155695656337232298015292476).isSome = true := by
  decide +kernel

theorem k2864_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2864) 3).1 2).2
      15985962810125735199921747278806103615321603285729443025573153803815517551391370318232636).isSome = true := by
  decide +kernel

theorem k2864_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2864) 3).2 2).1
      974804523568489124971543881460913122406717116051684088118014467274670054385878137916).isSome = true := by
  decide +kernel

theorem k2864_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2864) 3).2 2).2
      211384255107434806231730488958283294186704180416745406909576952892).isSome = true := by
  decide +kernel

theorem k2865_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2865) 3).1 2).1
      974173024723333809830487719496739261739602964959733894627342056473365073667691478076).isSome = true := by
  decide +kernel

theorem k2865_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2865) 3).1 2).2
      211246292257655032161238089141821728179767157714098167134448565308).isSome = true := by
  decide +kernel

theorem k2865_2 : (checkBoxH dirMode depth (splitBox (dirCellBox 2865) 3).2
      88932051414606894660541712626302877135295732933980483529807531534845481606375265686342208090544487304656539324232360556105557143793).isSome = true := by
  decide +kernel

theorem k2866_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2866) 3).1
      21704194360153494199209364326200674220371924875316725821853423461461329614550028577212888209428756240531181275488928557845101628).isSome = true := by
  decide +kernel

theorem k2866_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 2866) 3).2
      5424087532646550408870390679221700959932658454198142698348609493776778019279604084453282928932190174029717236878572961442610236).isSome = true := by
  decide +kernel

theorem k2867_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2867) 3).1
      293969638097152755106535866033979016813729026253754460132653094136958770999978094465426747319246025414766834).isSome = true := by
  decide +kernel

theorem k2867_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 2867) 3).2
      995743053776747923687179802399303563083011992929511537461724345516332639721792764735730).isSome = true := by
  decide +kernel

theorem k2868_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2868) 3).1
      210797106290206419305422771611361070247032632329860593217998994492).isSome = true := by
  decide +kernel

theorem k2868_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 2868) 3).2
      210759488796467873079576796055611864939145998307221505325994916924).isSome = true := by
  decide +kernel

theorem c5 : allCells dirCell 2869 2870 [
    25585290673344720982715194562079239622849958573593482994933507768075009818003164617553619202356299711294242883668946837584629059537998198529781615858] = true := by
  decide +kernel

theorem c6 : allCells dirCell 2870 2871 [
    18351688025958188932989891900525271843331483883789433449743907796819745362989952243486994278932994161734898] = true := by
  decide +kernel

theorem c7 : allCells dirCell 2871 2887 [
    3885385650902445524716629090574110562903859045517461810856601808340394968022292924785,
    147552224212368631700, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1] = true := by
  decide +kernel

theorem k2887_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2887) 3).1
      21936082515379053476843178347424719678635247239858905511754693999282443957370802563163179811257568487491328625419437074183627).isSome = true := by
  decide +kernel

theorem k2887_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2887) 3).2 2).1
      87226563940619923363342074272953227031865648274732179000100181046814661578836615558897813986479726235161412728448374198878797).isSome = true := by
  decide +kernel

theorem k2887_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2887) 3).2 2).2
      15643693796013025459146764322087624548427378722977253099651784734499063163961354609).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 2864 2888 :=
  (Cover.one (box := dirCellBox) (n := 2864)
      (.split 3 (.split 2 (.leaf _ k2864_0) (.leaf _ k2864_1)) (.split 2 (.leaf _ k2864_2) (.leaf _ k2864_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 2865)
      (.split 3 (.split 2 (.leaf _ k2865_0) (.leaf _ k2865_1)) (.leaf _ k2865_2))).trans <|
  (Cover.one (box := dirCellBox) (n := 2866)
      (.split 3 (.leaf _ k2866_0) (.leaf _ k2866_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 2867)
      (.split 3 (.leaf _ k2867_0) (.leaf _ k2867_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 2868)
      (.split 3 (.leaf _ k2868_0) (.leaf _ k2868_1))).trans <|
  (Cover.dir c5).trans <|
  (Cover.dir c6).trans <|
  (Cover.dir c7).trans <|
  (Cover.one (box := dirCellBox) (n := 2887)
      (.split 3 (.leaf _ k2887_0) (.split 2 (.leaf _ k2887_1) (.leaf _ k2887_2))))

end C4.Cert.Dir074
