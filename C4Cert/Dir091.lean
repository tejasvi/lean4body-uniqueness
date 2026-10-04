module

public import C4Check

public section

/-! Cells `3200 ≤ n < 3224` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir091

theorem k3200_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3200) 2).1 3).1
      1357731528641557104619229971818243829438735903017056637950403373875396823973280050688805156880761896353169112618298383462159281).isSome = true := by
  decide +kernel

theorem k3200_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3200) 2).1 3).2
      84823652529634760742115153596978990758884377283622375386972895933822301974590789717350714190213709942912518758250824451585265).isSome = true := by
  decide +kernel

theorem k3200_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3200) 2).2 3).1 1).1
      243604520711863704039077569938237377636150839116552642837447386216640784767213206956).isSome = true := by
  decide +kernel

theorem k3200_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3200) 2).2 3).1 1).2
      3897370437893344537963211467748247416989588300277425915661962927094033472624340226988).isSome = true := by
  decide +kernel

theorem k3200_4 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3200) 2).2 3).2
      339340969731319640813306136923010611335708100664238275703823338676851130066254767142950531146007311057855553731359183356655281).isSome = true := by
  decide +kernel

theorem k3201_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3201) 2).1
      6257338727984005639049618312717266031881305161361366561547987819435784003871952514566729231629061008581375192819502525132841606612353467049457095).isSome = true := by
  decide +kernel

theorem k3201_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3201) 2).2 3).1
      84799064968595547966450766455899148973433955620293170387458188811796193970773330119874787007983856802328261138538194791914929).isSome = true := by
  decide +kernel

theorem k3201_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3201) 2).2 3).2
      17959932756758869785422522140138274276362133918846305891414410553017809355188822152135080737721078144433).isSome = true := by
  decide +kernel

theorem k3202_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3202) 2).1
      2469269818786449009695480711855282233496781012947820466921692487).isSome = true := by
  decide +kernel

theorem k3202_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 3202) 2).2
      6251521558573294854247271528898752366865040641418293251089601421023369095632756772765539253845359459069817522224801791635091163990920205342406087).isSome = true := by
  decide +kernel

theorem c3 : allCells dirCell 3203 3222 [
    15556951020710837531491826197059235154880983964755755115314977034179162577183082498310, 82, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1] = true := by
  decide +kernel

theorem k3222_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3222) 3).1 3).1
      647280314461916948324696416145982328419063188134635812889683443798).isSome = true := by
  decide +kernel

theorem k3222_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3222) 3).1 3).2 2).1
      76122403657727480367829191481817352601545782343727363936173411989645063142406573717598050900761866500934).isSome = true := by
  decide +kernel

theorem k3222_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3222) 3).1 3).2 2).2
      16100917765666329288614475686674188895398144114784820607785609338958340883601589617).isSome = true := by
  decide +kernel

theorem k3222_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3222) 3).2 2).1 3).1
      1941956881245837494098766487885748925801036018805435443348519691178481937758203159507938807637178459687416718600761055024887308352460907455892725649764813823535171014).isSome = true := by
  decide +kernel

theorem k3222_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3222) 3).2 2).1 3).2 2).1
      76684211637302529817610274292973668573845359486419552403224848178154867432943305889272963356035470349524401).isSome = true := by
  decide +kernel

theorem k3222_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3222) 3).2 2).1 3).2 2).2
      63522842251095086559965117225023839843579447371357912701713754474896452532846974321).isSome = true := by
  decide +kernel

theorem k3222_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3222) 3).2 2).2 3).1
      75540345888772649931231858942277729034851662570168445297297145102513551947476892015229681096702393115721).isSome = true := by
  decide +kernel

theorem k3222_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3222) 3).2 2).2 3).2
      417231109319329954424729465031080951113901092012935038069758925928748758646192195197701564521497393710237836979287844128627636022981041343016125894).isSome = true := by
  decide +kernel

theorem k3223_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3223) 3).1 2).1 3).1 2).1
      1191009279329288048680968027223684830485988220261576378773580364653344251165748721630510762614567667457457).isSome = true := by
  decide +kernel

theorem k3223_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3223) 3).1 2).1 3).1 2).2
      1192696723505822595812541452835887400147141792060004271361722805677303989830605942475394596573382511320497).isSome = true := by
  decide +kernel

theorem k3223_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3223) 3).1 2).1 3).2 2).1
      5600469318491885419476559934519283722000294279565918607675819144964796689425627206106025845523601791469682045134576615531051441).isSome = true := by
  decide +kernel

theorem k3223_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3223) 3).1 2).1 3).2 2).2
      1185432744232899714614785629112480833169463134065679186762859351186475537611526164911732540054376752438705).isSome = true := by
  decide +kernel

theorem k3223_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3223) 3).1 2).2 3).1 1).1
      63217017477045842292549625862673702823004267432243258112952935983144974023927907762).isSome = true := by
  decide +kernel

theorem k3223_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3223) 3).1 2).2 3).1 1).2
      4035575652834845623622267517192277302529268218145485426475466084103751274085115327154).isSome = true := by
  decide +kernel

theorem k3223_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3223) 3).1 2).2 3).2 2).1
      1187062391270211058688091550210528543610378889836644145062535241119811704416646456824684885038064912391601).isSome = true := by
  decide +kernel

theorem k3223_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3223) 3).1 2).2 3).2 2).2
      64270077880544245927179035364331994444490733912083036493355966875532289137125405217596).isSome = true := by
  decide +kernel

theorem k3223_8 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3223) 3).2 2).1 2).1 3).1
      1209047785305623243781444309562827790409584771637985898987969258056799751215087290182519896412430585645595825).isSome = true := by
  decide +kernel

theorem k3223_9 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3223) 3).2 2).1 2).1 3).2
      261134060747843641509184443666961264870078099403674355392189910089003090990626075564407985).isSome = true := by
  decide +kernel

theorem k3223_10 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3223) 3).2 2).1 2).2 3).1
      302437890278527829242968803342047758549521407007948960905553236336275703399635071708182153631195440742785713).isSome = true := by
  decide +kernel

theorem k3223_11 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3223) 3).2 2).1 2).2 3).2
      261302083821435284748412971512169615669219131454091666476857262757599021677693348113644721).isSome = true := by
  decide +kernel

theorem k3223_12 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3223) 3).2 2).2 3).1 2).1
      64010834156202203710187737837648752884267056249060735758670643114803939900052643082929).isSome = true := by
  decide +kernel

theorem k3223_13 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3223) 3).2 2).2 3).1 2).2
      16014110904506770062235311169115544541579107617867976597268957027725454728293448109628).isSome = true := by
  decide +kernel

theorem k3223_14 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3223) 3).2 2).2 3).2 2).1
      1021297014958816327029615239348968767157614517631509787837410130470011356136660545140913).isSome = true := by
  decide +kernel

theorem k3223_15 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3223) 3).2 2).2 3).2 2).2
      15949783021836207550089549369166771616203856723518491996295777879430121750285319560369).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 3200 3224 :=
  (Cover.one (box := dirCellBox) (n := 3200)
      (.split 2 (.split 3 (.leaf _ k3200_0) (.leaf _ k3200_1)) (.split 3 (.split 1 (.leaf _ k3200_2) (.leaf _ k3200_3)) (.leaf _ k3200_4)))).trans <|
  (Cover.one (box := dirCellBox) (n := 3201)
      (.split 2 (.leaf _ k3201_0) (.split 3 (.leaf _ k3201_1) (.leaf _ k3201_2)))).trans <|
  (Cover.one (box := dirCellBox) (n := 3202)
      (.split 2 (.leaf _ k3202_0) (.leaf _ k3202_1))).trans <|
  (Cover.dir c3).trans <|
  (Cover.one (box := dirCellBox) (n := 3222)
      (.split 3 (.split 3 (.leaf _ k3222_0) (.split 2 (.leaf _ k3222_1) (.leaf _ k3222_2))) (.split 2 (.split 3 (.leaf _ k3222_3) (.split 2 (.leaf _ k3222_4) (.leaf _ k3222_5))) (.split 3 (.leaf _ k3222_6) (.leaf _ k3222_7))))).trans <|
  (Cover.one (box := dirCellBox) (n := 3223)
      (.split 3 (.split 2 (.split 3 (.split 2 (.leaf _ k3223_0) (.leaf _ k3223_1)) (.split 2 (.leaf _ k3223_2) (.leaf _ k3223_3))) (.split 3 (.split 1 (.leaf _ k3223_4) (.leaf _ k3223_5)) (.split 2 (.leaf _ k3223_6) (.leaf _ k3223_7)))) (.split 2 (.split 2 (.split 3 (.leaf _ k3223_8) (.leaf _ k3223_9)) (.split 3 (.leaf _ k3223_10) (.leaf _ k3223_11))) (.split 3 (.split 2 (.leaf _ k3223_12) (.leaf _ k3223_13)) (.split 2 (.leaf _ k3223_14) (.leaf _ k3223_15))))))

end C4.Cert.Dir091
