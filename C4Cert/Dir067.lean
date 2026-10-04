module

public import C4Check

public section

/-! Cells `2808 ≤ n < 2832` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir067

theorem k2808_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2808) 2).1 3).1 1).1
      3896124712215856615708243055744612204451666616256702638528004711185997536605930034995).isSome = true := by
  decide +kernel

theorem k2808_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2808) 2).1 3).1 1).2
      17972178453850290753232536339208797185711826759273687076561964865376283578582239394836993043136113133938).isSome = true := by
  decide +kernel

theorem k2808_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2808) 2).1 3).2
      21227164289230607823589046003644471188644038380195316129530374999794058603534108460917817633940745217455230250011011101842865).isSome = true := by
  decide +kernel

theorem k2808_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2808) 2).2 3).1 1).1
      243860761820660444351995832033879631164413328037057500098099063603806087363727679276).isSome = true := by
  decide +kernel

theorem k2808_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2808) 2).2 3).1 1).2
      974404843650492293419366567645737387492406517405402595377471169573045752191178865836).isSome = true := by
  decide +kernel

theorem k2808_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2808) 2).2 3).2 1).1
      243478649961519927379347952080190316217540848647505318327892327704831440409345875756).isSome = true := by
  decide +kernel

theorem k2808_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2808) 2).2 3).2 1).2
      973861257687328194581555849484154313637927284215413548052875454597376966048452803756).isSome = true := by
  decide +kernel

theorem k2809_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2809) 2).1 3).1
      21198548966399692030477845994507844531300906904552363691933315400725072069189033946823258466558737194969922822016815116541361).isSome = true := by
  decide +kernel

theorem k2809_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2809) 2).1 3).2
      15203547774254528075869383592098216161855166976015985738181567880970820004093820273).isSome = true := by
  decide +kernel

theorem k2809_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2809) 2).2 3).1
      1149316061400144229275925511266770226267451891525588170071133890076303756802108194107782187587573692783793).isSome = true := by
  decide +kernel

theorem k2809_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2809) 2).2 3).2
      1148868941641909359821725957285149980803502706343041229212318654460018346071948357963519969367169291476145).isSome = true := by
  decide +kernel

theorem k2810_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2810) 2).1
      71757077940594245775984971628226251909414641154008303624568387298730312484903792909787142052750755493319).isSome = true := by
  decide +kernel

theorem k2810_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2810) 2).2 3).1
      62260426998655365450327602800912569953096714706951275703081817708892868743411503641805).isSome = true := by
  decide +kernel

theorem k2810_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2810) 2).2 3).2
      15196548402553143656184872499031881803866626447406074702049202875129023035873028465).isSome = true := by
  decide +kernel

theorem c3 : allCells dirCell 2811 2812 [
    346872150123995115272093578622845667121516939506153079977691295768676435796087451826762938735444623034339627584705870244018664486] = true := by
  decide +kernel

theorem c4 : allCells dirCell 2812 2830 [
    13171881992812612947461364745685419683099527291728971998230835462, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0] = true := by
  decide +kernel

theorem k2830_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2830) 3).1
      1310849659471869756963309118980378426675116088192754843363971911161517529493138080181943866186311467613363997249627).isSome = true := by
  decide +kernel

theorem k2830_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2830) 3).2 2).1 3).1
      6592868427752221583725110681412331044016831042875022614649044894638989450945754962741126824424344049469500796029906546174741697015152272652690886).isSome = true := by
  decide +kernel

theorem k2830_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2830) 3).2 2).1 3).2 2).1
      22163345987900488633996492122736886060185502236744094782065084317318519006857792567444317372315922747316129374775340082861553).isSome = true := by
  decide +kernel

theorem k2830_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2830) 3).2 2).1 3).2 2).2
      15891513277754139289479865129615166602689477010228191870916261688395786155724170609).isSome = true := by
  decide +kernel

theorem k2830_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2830) 3).2 2).2 3).1
      63984246474944490845503031883451171511183423327445707218457151179840098766131733873).isSome = true := by
  decide +kernel

theorem k2830_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2830) 3).2 2).2 3).2
      22116899287177112840321296473905936419635991055995878621416858470771422999364730333624213876920608609523916367654376072283593).isSome = true := by
  decide +kernel

theorem k2831_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2831) 3).1 2).1 3).1 2).1
      19101101051220491891970247004550336738066452299091422369610691697534958754877981057216534107590504985093617).isSome = true := by
  decide +kernel

theorem k2831_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2831) 3).1 2).1 3).1 2).2
      298585406574092118232403094419702241524243464326935517113479967736943935310074638004756520062806026380785).isSome = true := by
  decide +kernel

theorem k2831_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2831) 3).1 2).1 3).2 2).1
      257238614476754026848681513958602144882987220401390577273755764216861110080057447965937).isSome = true := by
  decide +kernel

theorem k2831_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2831) 3).1 2).1 3).2 2).2
      16100635240532224394234103043686889009258834187851521174026728839545635368642070668529).isSome = true := by
  decide +kernel

theorem k2831_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2831) 3).1 2).2 3).1
      1920178508030654679853931995180777718242983100790244436567031012440890880959568161606751773197728255614762337608331882831057303522859163998361330739678023769090921926).isSome = true := by
  decide +kernel

theorem k2831_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2831) 3).1 2).2 3).2 1).1
      4026169313222728513825444252113579896578449758441698637977917200333914127468726424306).isSome = true := by
  decide +kernel

theorem k2831_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2831) 3).1 2).2 3).2 1).2
      1006959296976115427410747209013032845652610974710588096497771637585946732462270142898).isSome = true := by
  decide +kernel

theorem k2831_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2831) 3).2 2).1 3).1 2).1
      75644579789245341146396960934501105293478937423519763109510728286216222187799221083806450443010459462898609).isSome = true := by
  decide +kernel

theorem k2831_8 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2831) 3).2 2).1 3).1 2).2
      256452239019074788073199399479047468525056922479577243700650119478925618832589725263089).isSome = true := by
  decide +kernel

theorem k2831_9 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2831) 3).2 2).1 3).2 2).1
      301400242950330796898845696623912970701152406706303094439626233928254690035121874609356613965728865422054321).isSome = true := by
  decide +kernel

theorem k2831_10 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2831) 3).2 2).1 3).2 2).2
      18848579135874554900098504716728557600250942369642968710251871460369869036772178915045327294142878696826545).isSome = true := by
  decide +kernel

theorem k2831_11 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2831) 3).2 2).2 3).1 1).1
      16047653325336493323263041117972958013399671074516069002174845145126107402872506115314).isSome = true := by
  decide +kernel

theorem k2831_12 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2831) 3).2 2).2 3).1 1).2
      4010160391079874218911675684454264762453358882330940825990147209700633545262221875634).isSome = true := by
  decide +kernel

theorem k2831_13 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2831) 3).2 2).2 3).2 1).1
      3996416541318357184295124423131339129640574071352311097580206837597506878723058391474).isSome = true := by
  decide +kernel

theorem k2831_14 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2831) 3).2 2).2 3).2 1).2
      63920910019685899783403706133125604689738895858397834651334500456136236525458814967218).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 2808 2832 :=
  (Cover.one (box := dirCellBox) (n := 2808)
      (.split 2 (.split 3 (.split 1 (.leaf _ k2808_0) (.leaf _ k2808_1)) (.leaf _ k2808_2)) (.split 3 (.split 1 (.leaf _ k2808_3) (.leaf _ k2808_4)) (.split 1 (.leaf _ k2808_5) (.leaf _ k2808_6))))).trans <|
  (Cover.one (box := dirCellBox) (n := 2809)
      (.split 2 (.split 3 (.leaf _ k2809_0) (.leaf _ k2809_1)) (.split 3 (.leaf _ k2809_2) (.leaf _ k2809_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 2810)
      (.split 2 (.leaf _ k2810_0) (.split 3 (.leaf _ k2810_1) (.leaf _ k2810_2)))).trans <|
  (Cover.dir c3).trans <|
  (Cover.dir c4).trans <|
  (Cover.one (box := dirCellBox) (n := 2830)
      (.split 3 (.leaf _ k2830_0) (.split 2 (.split 3 (.leaf _ k2830_1) (.split 2 (.leaf _ k2830_2) (.leaf _ k2830_3))) (.split 3 (.leaf _ k2830_4) (.leaf _ k2830_5))))).trans <|
  (Cover.one (box := dirCellBox) (n := 2831)
      (.split 3 (.split 2 (.split 3 (.split 2 (.leaf _ k2831_0) (.leaf _ k2831_1)) (.split 2 (.leaf _ k2831_2) (.leaf _ k2831_3))) (.split 3 (.leaf _ k2831_4) (.split 1 (.leaf _ k2831_5) (.leaf _ k2831_6)))) (.split 2 (.split 3 (.split 2 (.leaf _ k2831_7) (.leaf _ k2831_8)) (.split 2 (.leaf _ k2831_9) (.leaf _ k2831_10))) (.split 3 (.split 1 (.leaf _ k2831_11) (.leaf _ k2831_12)) (.split 1 (.leaf _ k2831_13) (.leaf _ k2831_14))))))

end C4.Cert.Dir067
