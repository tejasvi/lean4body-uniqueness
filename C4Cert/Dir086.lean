module

public import C4Check

public section

/-! Cells `3168 ≤ n < 3170` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir086

theorem k3168_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3168) 2).1 3).1 2).1 3).1 1).1
      18613194962096929136256697939093685117854319345917439820781116353267946147976258820817988443653008661666364).isSome = true := by
  decide +kernel

theorem k3168_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3168) 2).1 3).1 2).1 3).1 1).2
      3940182171045869107814019571215802924497141401260590566071683843600251212582354409388).isSome = true := by
  decide +kernel

theorem k3168_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3168) 2).1 3).1 2).1 3).2 1).1
      13327957082431945468898649438120677838296794872539663827204668844).isSome = true := by
  decide +kernel

theorem k3168_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3168) 2).1 3).1 2).1 3).2 1).2
      983164096808320176245589010300486445594146575259416527327850794585462648394034435900).isSome = true := by
  decide +kernel

theorem k3168_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3168) 2).1 3).1 2).2 3).1 1).1
      252560377969884110929177350508836672055365989460147822597558227568363175598157979441724).isSome = true := by
  decide +kernel

theorem k3168_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3168) 2).1 3).1 2).2 3).1 1).2
      3421053793652379368680407084427410516936628822961962163273992218284).isSome = true := by
  decide +kernel

theorem k3168_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3168) 2).1 3).1 2).2 3).2 1).1
      63005467951448702574755688984860134515484039517780047816590611589599577728657611290172).isSome = true := by
  decide +kernel

theorem k3168_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3168) 2).1 3).1 2).2 3).2 1).2
      3336981045351195849433394610301909972612266355682241686281485740).isSome = true := by
  decide +kernel

theorem k3168_8 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3168) 2).1 3).2 2).1 3).1 1).1
      53224451245191456606817656307492962834601936549547574815330237868).isSome = true := by
  decide +kernel

theorem k3168_9 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3168) 2).1 3).2 2).1 3).1 1).2
      13302732463286665681383003775468427121121215364372707537486059324).isSome = true := by
  decide +kernel

theorem k3168_10 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3168) 2).1 3).2 2).1 3).2
      18515395010676174568280803133714292469647109910523420334784357657637306238382504543639939966911487133375921).isSome = true := by
  decide +kernel

theorem k3168_11 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3168) 2).1 3).2 2).2 1).1 3).1
      13317301567390554857044062891403783568954690726379407407651061164).isSome = true := by
  decide +kernel

theorem k3168_12 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3168) 2).1 3).2 2).2 1).1 3).2
      13297430960484347095962322722484006114847432986220294473591127468).isSome = true := by
  decide +kernel

theorem k3168_13 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3168) 2).1 3).2 2).2 1).2
      303599260117969023864047791881188887868312609037827626485022936385456571682129418733940403100392712206169295795).isSome = true := by
  decide +kernel

theorem k3168_14 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3168) 2).2 3).1 2).1 3).1 1).1
      13719329338222719187116332258457250101302729412334986617119873944124).isSome = true := by
  decide +kernel

theorem k3168_15 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3168) 2).2 3).1 2).1 3).1 1).2
      1010854358650416013519979530765779793448406893483212292722070426153486338111236864985660).isSome = true := by
  decide +kernel

theorem k3168_16 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3168) 2).2 3).1 2).1 3).2 1).1
      13673522125534333769708329970853490613290291047226715563002421037628).isSome = true := by
  decide +kernel

theorem k3168_17 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3168) 2).2 3).1 2).1 3).2 1).2
      53397478206098217045102383053414522631361200434268474262801479228).isSome = true := by
  decide +kernel

theorem k3168_18 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3168) 2).2 3).1 2).2 3).1 1).1
      1012638052878616975615946445833537148552001608830786115095740930289372719225361160663612).isSome = true := by
  decide +kernel

theorem k3168_19 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3168) 2).2 3).1 2).2 3).1 1).2
      1012135624982541463199484550121229701593443291806872502181367850351924946027723678544444).isSome = true := by
  decide +kernel

theorem k3168_20 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3168) 2).2 3).1 2).2 3).2 1).1
      3422050834374007751900615325841438134867018009223653075497162109500).isSome = true := by
  decide +kernel

theorem k3168_21 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3168) 2).2 3).1 2).2 3).2 1).2
      252393056780317955476739186339639580583194835675733635998739291210121466629273844970044).isSome = true := by
  decide +kernel

theorem k3168_22 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3168) 2).2 3).2 2).1 3).1
      1403095481835670263297804883070212699207255221943542820659523231695372463687794020508087620388306013217145737965227063599892519153).isSome = true := by
  decide +kernel

theorem k3168_23 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3168) 2).2 3).2 2).1 3).2
      350218873463962787581386568123662547123536925763633191546047197805253083088490519352939117084046682123987835217224203529176471793).isSome = true := by
  decide +kernel

theorem k3168_24 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3168) 2).2 3).2 2).2 3).1 1).1
      3414863670581298853696083094909175893303616830488593028950099751484).isSome = true := by
  decide +kernel

theorem k3168_25 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3168) 2).2 3).2 2).2 3).1 1).2
      53343514967827824116865096493415257595499938536973213221840614972).isSome = true := by
  decide +kernel

theorem k3168_26 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3168) 2).2 3).2 2).2 3).2
      304008357474864948674913845798675795833955248078708344159439569602461123468441233076761983459183524369181649137).isSome = true := by
  decide +kernel

theorem k3169_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3169) 2).1 3).1 2).1 3).1
      18495861597191195308486040488302815085020173119209738921468896864413706006466216756130806517830802126953905).isSome = true := by
  decide +kernel

theorem k3169_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3169) 2).1 3).1 2).1 3).2
      21306455674809065497972075935761283892188925381535220604652264237773037567915051064118678880790367497949943812465668051721649).isSome = true := by
  decide +kernel

theorem k3169_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3169) 2).1 3).1 2).2 3).1
      1156628841564836337382593088619168476025386306404236026947225895994015852635139924866755506507163415764401).isSome = true := by
  decide +kernel

theorem k3169_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3169) 2).1 3).1 2).2 3).2
      4621949612801644933996490434134794772022002890030758159628507310809659187930956712174359760187825355316657).isSome = true := by
  decide +kernel

theorem k3169_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3169) 2).1 3).2 2).1 1).1
      18027166669912150609141852083309543777445032639688561158856054399942794318062076232470885959952540392883).isSome = true := by
  decide +kernel

theorem k3169_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3169) 2).1 3).2 2).1 1).2
      15266367873167423081831516682885474223926222061885582401159509439495207385377638771).isSome = true := by
  decide +kernel

theorem k3169_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3169) 2).1 3).2 2).2 1).1
      288613489284073568531895935886876973781622729118823546433674644957906491360221513351964005319112640125756).isSome = true := by
  decide +kernel

theorem k3169_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3169) 2).1 3).2 2).2 1).2
      72107973785568332923815282128646699274118532765438793583673109219903245809313721998140673126989474520499).isSome = true := by
  decide +kernel

theorem k3169_8 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3169) 2).2 3).1 2).1 3).1
      296262042129630179469386703228908051073888609439030978262528286092106095545339757638744925026906552060706225).isSome = true := by
  decide +kernel

theorem k3169_9 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3169) 2).2 3).1 2).1 3).2
      250684058060509441239219614512192810014602867248224373535111313495186608769060892089777).isSome = true := by
  decide +kernel

theorem k3169_10 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3169) 2).2 3).1 2).2 3).1
      75890688314781723483882693373596712406320928497661552359197733019232042316274489610862837623482341442805770481).isSome = true := by
  decide +kernel

theorem k3169_11 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3169) 2).2 3).1 2).2 3).2
      18525585044464292407789250991548202908228385495298296844236844381828672328097064591987093138869680028903857).isSome = true := by
  decide +kernel

theorem k3169_12 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3169) 2).2 3).2 2).1 1).1
      21294859674277412690142216725788531217098055927555957144636194126192809144374783202983694718194096420639251824448920374369715).isSome = true := by
  decide +kernel

theorem k3169_13 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3169) 2).2 3).2 2).1 1).2
      62590322337145061355834235043594409054539709963693126147985539172348286070312662814524).isSome = true := by
  decide +kernel

theorem k3169_14 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3169) 2).2 3).2 2).2 1).1
      4619564544052744010223949239756193432798257574398309029927619897972316018661548308691189712330589265501619).isSome = true := by
  decide +kernel

theorem k3169_15 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3169) 2).2 3).2 2).2 1).2
      3911841993887472216095908016688054855808963175997873249118752543119967324099149093299).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 3168 3170 :=
  (Cover.one (box := dirCellBox) (n := 3168)
      (.split 2 (.split 3 (.split 2 (.split 3 (.split 1 (.leaf _ k3168_0) (.leaf _ k3168_1)) (.split 1 (.leaf _ k3168_2) (.leaf _ k3168_3))) (.split 3 (.split 1 (.leaf _ k3168_4) (.leaf _ k3168_5)) (.split 1 (.leaf _ k3168_6) (.leaf _ k3168_7)))) (.split 2 (.split 3 (.split 1 (.leaf _ k3168_8) (.leaf _ k3168_9)) (.leaf _ k3168_10)) (.split 1 (.split 3 (.leaf _ k3168_11) (.leaf _ k3168_12)) (.leaf _ k3168_13)))) (.split 3 (.split 2 (.split 3 (.split 1 (.leaf _ k3168_14) (.leaf _ k3168_15)) (.split 1 (.leaf _ k3168_16) (.leaf _ k3168_17))) (.split 3 (.split 1 (.leaf _ k3168_18) (.leaf _ k3168_19)) (.split 1 (.leaf _ k3168_20) (.leaf _ k3168_21)))) (.split 2 (.split 3 (.leaf _ k3168_22) (.leaf _ k3168_23)) (.split 3 (.split 1 (.leaf _ k3168_24) (.leaf _ k3168_25)) (.leaf _ k3168_26)))))).trans <|
  (Cover.one (box := dirCellBox) (n := 3169)
      (.split 2 (.split 3 (.split 2 (.split 3 (.leaf _ k3169_0) (.leaf _ k3169_1)) (.split 3 (.leaf _ k3169_2) (.leaf _ k3169_3))) (.split 2 (.split 1 (.leaf _ k3169_4) (.leaf _ k3169_5)) (.split 1 (.leaf _ k3169_6) (.leaf _ k3169_7)))) (.split 3 (.split 2 (.split 3 (.leaf _ k3169_8) (.leaf _ k3169_9)) (.split 3 (.leaf _ k3169_10) (.leaf _ k3169_11))) (.split 2 (.split 1 (.leaf _ k3169_12) (.leaf _ k3169_13)) (.split 1 (.leaf _ k3169_14) (.leaf _ k3169_15))))))

end C4.Cert.Dir086
