module

public import C4Check

public section

/-! Cells `4488 ≤ n < 4515` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir143

theorem k4488_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4488) 2).1 3).1
      15987208125347794256543590585952455826807213039083913929110767851824986965638844909214513).isSome = true := by
  decide +kernel

theorem k4488_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4488) 2).1 3).2
      998452062970140689615514204126436493162178699203788057905565739959058136147667615062833).isSome = true := by
  decide +kernel

theorem k4488_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4488) 2).2 3).1
      294995442283117012978604536135562710310131731232593134898918491146428888274817529685308674972065368250699468).isSome = true := by
  decide +kernel

theorem k4488_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4488) 2).2 3).2
      998659962571675023038276975019260476959084131728736609158158431831746681582891959950129).isSome = true := by
  decide +kernel

theorem k4489_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4489) 2).1 3).1
      3991355382663546115144907664696951137785006935086495960790677690719578469819887585439985).isSome = true := by
  decide +kernel

theorem k4489_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4489) 2).1 3).2
      15584175702165213615577613351494195977638576207425714449675158160723230906380136673852).isSome = true := by
  decide +kernel

theorem k4489_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4489) 2).2 3).1
      998015873706932119185334792587653782774843804071422949832224371013599562848705723341617).isSome = true := by
  decide +kernel

theorem k4489_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4489) 2).2 3).2
      62345537310860525043913898815335867316270248526437916145366631780706877124412905929788).isSome = true := by
  decide +kernel

theorem k4490_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4490) 2).1 3).1
      3894400287591718032793933957352293738089551781942446759536084880190190715795087422012).isSome = true := by
  decide +kernel

theorem k4490_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4490) 2).1 3).2
      3892976866294162175033928959294468125842337459564174738894651223486562631458196156988).isSome = true := by
  decide +kernel

theorem k4490_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4490) 2).2 3).1
      844540514837515681020692837872809219093159883240932113736312994876).isSome = true := by
  decide +kernel

theorem k4490_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4490) 2).2 3).2
      973372271768882956833229299874629343890081720959858063411466370987965134456036883516).isSome = true := by
  decide +kernel

theorem k4491_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4491) 3).1 2).1
      3375585401674156991988048388038193013530036329479140576538853362236).isSome = true := by
  decide +kernel

theorem k4491_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4491) 3).1 2).2
      843991317867785807541738396085947078691838023750766968276270838332).isSome = true := by
  decide +kernel

theorem k4491_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4491) 3).2 2).1
      972729015051074961209074421102279604698510524773804420971863865704652036655032956476).isSome = true := by
  decide +kernel

theorem k4491_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4491) 3).2 2).2
      52734981315777453587358938227388647064289528943377092696345014844).isSome = true := by
  decide +kernel

theorem k4492_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4492) 2).1
      1599979848598313660804163674467475213170733116988803337076324939920440174051025906799578264672528483713419378856424155692364373936984021134722193651).isSome = true := by
  decide +kernel

theorem k4492_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4492) 2).2
      25603786042746515577436968527925972581365415564849070445587476776187296934836052113019707887807622279532290915349457747289090111054325115475254391612).isSome = true := by
  decide +kernel

theorem k4493_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4493) 3).1
      1355094552219557536043128616588659925510539790313328106223290975774534328600782695122641214881486284899026184304993770569037042).isSome = true := by
  decide +kernel

theorem k4493_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4493) 3).2
      293794689891358007434115744664573268846126359792068197722034729105815114637708229118917940536339794761206588).isSome = true := by
  decide +kernel

theorem k4494_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4494) 2).1
      1147415518345225985545204042825741400367235617249171359690884420070362682939912804347513426741882565647548).isSome = true := by
  decide +kernel

theorem k4494_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4494) 2).2
      286935070990078522342188404667568675340802090174347133584466714720644217857316856956970765457325538400060).isSome = true := by
  decide +kernel

theorem k4495_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4495) 2).1
      60733350550517067921579674981352296605655589459491237368041913414446426889757512956).isSome = true := by
  decide +kernel

theorem k4495_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4495) 2).2
      17925623798799554448556177127505962662254517411749008707616300460762538493222979048785618177256731432764).isSome = true := by
  decide +kernel

theorem c8 : allCells dirCell 4496 4497 [
    338555370011123322770850894447007793884842896657134424846802903582810197207224150311388687131667774261571825426096573891048689] = true := by
  decide +kernel

theorem c9 : allCells dirCell 4497 4498 [
    1322338834955397793366749747404310955800548567209192107534497050728834407356626487256082818504357155843740110044653938999666] = true := by
  decide +kernel

theorem c10 : allCells dirCell 4498 4511 [
    51425830564461112451318032100813709724038327745872914993562706,
    174226686953590817871044827383139399292497, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] = true := by
  decide +kernel

theorem k4511_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4511) 3).1
      211980488262598164588533380451674951065766367498377496168936262).isSome = true := by
  decide +kernel

theorem k4511_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4511) 3).2
      261103410948967051534728869052324492548666961574289707944125594236245891266756967116653766).isSome = true := by
  decide +kernel

theorem k4512_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4512) 3).1
      22640055484242286936281900332474694992616307607184410075004143655207690976902903829841337861798541615756249149671966019875385597126).isSome = true := by
  decide +kernel

theorem k4512_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4512) 3).2 2).1
      1012662814326712728948795348659295755707939719139578152782639294443284432633510835876658).isSome = true := by
  decide +kernel

theorem k4512_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4512) 3).2 2).2
      3426709030786359700633801573627049044852273122270771422794342560562).isSome = true := by
  decide +kernel

theorem k4513_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4513) 2).1 3).1
      4033846084610120014467316777596286018260412242204886194146050094992025543627519194133297).isSome = true := by
  decide +kernel

theorem k4513_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4513) 2).1 3).2
      19020010422519675781344910079134667709361266005171439369764825800963648828589760697928244265299874732182188849).isSome = true := by
  decide +kernel

theorem k4513_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4513) 2).2 3).1
      1009491738191902207821575619795183641472905581347748959118413604917588744141115240313649).isSome = true := by
  decide +kernel

theorem k4513_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4513) 2).2 3).2
      4028130587085057161011972943884617313009764409177352905421287413623225352906915134665521).isSome = true := by
  decide +kernel

theorem k4514_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4514) 2).1 3).1
      257238580391590568280080860949864762053080332681112320360747488373044722979492361326408497).isSome = true := by
  decide +kernel

theorem k4514_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4514) 2).1 3).2
      1027456368285072666172387579265752698347713249976000732159728476254112720804287299921031985).isSome = true := by
  decide +kernel

theorem k4514_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4514) 2).2 3).1
      257281253537476947998644128676634348445396312765128011083450869919623715649562329480803121).isSome = true := by
  decide +kernel

theorem k4514_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4514) 2).2 3).2
      256849978553387853146881057808509538233501913954647949560164789126184170515252809834279729).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 4488 4515 :=
  (Cover.one (box := dirCellBox) (n := 4488)
      (.split 2 (.split 3 (.leaf _ k4488_0) (.leaf _ k4488_1)) (.split 3 (.leaf _ k4488_2) (.leaf _ k4488_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 4489)
      (.split 2 (.split 3 (.leaf _ k4489_0) (.leaf _ k4489_1)) (.split 3 (.leaf _ k4489_2) (.leaf _ k4489_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 4490)
      (.split 2 (.split 3 (.leaf _ k4490_0) (.leaf _ k4490_1)) (.split 3 (.leaf _ k4490_2) (.leaf _ k4490_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 4491)
      (.split 3 (.split 2 (.leaf _ k4491_0) (.leaf _ k4491_1)) (.split 2 (.leaf _ k4491_2) (.leaf _ k4491_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 4492)
      (.split 2 (.leaf _ k4492_0) (.leaf _ k4492_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 4493)
      (.split 3 (.leaf _ k4493_0) (.leaf _ k4493_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 4494)
      (.split 2 (.leaf _ k4494_0) (.leaf _ k4494_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 4495)
      (.split 2 (.leaf _ k4495_0) (.leaf _ k4495_1))).trans <|
  (Cover.dir c8).trans <|
  (Cover.dir c9).trans <|
  (Cover.dir c10).trans <|
  (Cover.one (box := dirCellBox) (n := 4511)
      (.split 3 (.leaf _ k4511_0) (.leaf _ k4511_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 4512)
      (.split 3 (.leaf _ k4512_0) (.split 2 (.leaf _ k4512_1) (.leaf _ k4512_2)))).trans <|
  (Cover.one (box := dirCellBox) (n := 4513)
      (.split 2 (.split 3 (.leaf _ k4513_0) (.leaf _ k4513_1)) (.split 3 (.leaf _ k4513_2) (.leaf _ k4513_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 4514)
      (.split 2 (.split 3 (.leaf _ k4514_0) (.leaf _ k4514_1)) (.split 3 (.leaf _ k4514_2) (.leaf _ k4514_3))))

end C4.Cert.Dir143
