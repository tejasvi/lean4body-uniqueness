module

public import C4Check

public section

/-! Cells `1773 ≤ n < 1829` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir018

theorem k1773_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1773) 3).1 2).1
      15963847039849206076579594952660537461148027802081909137877659225194457220626153453505329).isSome = true := by
  decide +kernel

theorem k1773_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1773) 3).1 2).2
      3991427342353248004960432499998401664044583570009271724199913801202580993663763542850620).isSome = true := by
  decide +kernel

theorem k1773_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1773) 3).2 1).1
      15593389264235574267517284680885710969195307249382741368169723363035001111035227134668).isSome = true := by
  decide +kernel

theorem k1773_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1773) 3).2 1).2
      249556742524073731109695386654880741635761926108281871369710230516182809704579135323196).isSome = true := by
  decide +kernel

theorem k1774_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1774) 3).1 2).1
      15585528161006428240333952399801100455641102196461677547497851917007382548140695333948).isSome = true := by
  decide +kernel

theorem k1774_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1774) 3).1 2).2
      211226919650799567189714994222531117053044320866549982588248144956).isSome = true := by
  decide +kernel

theorem k1774_2 : (checkBoxH dirMode depth (splitBox (dirCellBox 1774) 3).2
      22213866679332550605856405559655414069062331622290705724900956434957782556242424116182918095913474530202138463127303057835132514545).isSome = true := by
  decide +kernel

theorem k1775_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 1775) 3).1
      346933124146019096187069023401181389157973382074811377690523410171275578945763799228351219546566287954369187881734268755115343025).isSome = true := by
  decide +kernel

theorem k1775_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 1775) 3).2
      1148615614651562166244523602666889260420254583590384676908585141556746022882832244890854729212931380960689).isSome = true := by
  decide +kernel

theorem c3 : allCells dirCell 1776 1777 [
    7371560076513350042098110403462956463988687424328836832512840788926194103087797136596666251181373514444822437538880159451738331087099640133910629224889217748065281479] = true := by
  decide +kernel

theorem c4 : allCells dirCell 1777 1797 [
    2360351174463424352321, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1] = true := by
  decide +kernel

theorem k1797_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 1797) 3).1
      61692034219993526649820088128221393913496982280162846749936399340305773655551862598).isSome = true := by
  decide +kernel

theorem k1797_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 1797) 3).2
      21435740060162930153389089764096616203117924463889416098537877492468607332202013768854058551626015903740760150992034808897350).isSome = true := by
  decide +kernel

theorem k1798_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1798) 3).1 2).1
      18115603133230696504437737809980496565138299613493090370804037993079094551588320058194218695268740461820).isSome = true := by
  decide +kernel

theorem k1798_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1798) 3).1 2).2
      61373153379016199892135072484391907086550416384690137324810511453581438785184716028).isSome = true := by
  decide +kernel

theorem k1798_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1798) 3).2 2).1
      250942610102381378148726577314330220490662838526474739153996090491897959930811493979377).isSome = true := by
  decide +kernel

theorem k1798_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1798) 3).2 2).2
      250929725685049232380558971917072693183198944038012610037321960366271857059427937162481).isSome = true := by
  decide +kernel

theorem k1799_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1799) 3).1 2).1
      250526765856481252599674486879596535365123604867308272988193222771199009902236192951100).isSome = true := by
  decide +kernel

theorem k1799_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1799) 3).1 2).2
      15657267540702480921300572880180124248439893078837880972991944773382177927042397326140).isSome = true := by
  decide +kernel

theorem k1799_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1799) 3).2 2).1
      3392250634432135646372987276475033859349827824480040207790405831228).isSome = true := by
  decide +kernel

theorem k1799_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1799) 3).2 2).2
      3390531295465983114327474397858343931321964450485860445378936556092).isSome = true := by
  decide +kernel

theorem k1800_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1800) 3).1 2).1
      1152527405774099115375946080705102416141939369789830176422992930049278330451625081646265670537067148196924).isSome = true := by
  decide +kernel

theorem k1800_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1800) 3).1 2).2
      13547689178617102927158777546150754399964384671854021429405832430396).isSome = true := by
  decide +kernel

theorem k1800_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1800) 3).2 2).1
      4605736023033116292821195352824634218519164898176173138776521960120093492969006338592766502986804327038012).isSome = true := by
  decide +kernel

theorem k1800_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1800) 3).2 2).2
      62418483519149971214606682589450568930363324027982109585751099801991061735908996594748).isSome = true := by
  decide +kernel

theorem k1801_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1801) 2).1 3).1
      249462564765236933107922015412062055872900203196669227231052445896576646798851217701948).isSome = true := by
  decide +kernel

theorem k1801_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1801) 2).1 3).2
      211153575934484180248086175689073265176034658254886474900506557500).isSome = true := by
  decide +kernel

theorem k1801_2 : (checkBoxH dirMode depth (splitBox (dirCellBox 1801) 2).2
      88948342436755641024322651123643584933725851125831761586944121853385516813088390081222786517017148839400692146423949065817429700851).isSome = true := by
  decide +kernel

theorem k1802_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 1802) 3).1
      22247948876199244527169257684573036353440037920101325969838494947579031804239337187030210972349523985180838552381931045051602104561).isSome = true := by
  decide +kernel

theorem k1802_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1802) 3).2 1).1
      243149628437137845488566721659150368284975151395863963467370824559487892792668544812).isSome = true := by
  decide +kernel

theorem k1802_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1802) 3).2 1).2
      210935961665764586941892165849667214228049101661388742910245387324).isSome = true := by
  decide +kernel

theorem k1803_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 1803) 3).1
      249165745407906954043227927186655859428042816682737119301432459646048181405889337973937).isSome = true := by
  decide +kernel

theorem k1803_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 1803) 3).2
      3887847291216899245213820148138364762313684477127806579990869087174762284508184303025).isSome = true := by
  decide +kernel

theorem c12 : allCells dirCell 1804 1825 [
    71673067267957506842791076299826479928444841602626540456081098909871743962564933619736295563120882682185,
    147499284995457047220, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] = true := by
  decide +kernel

theorem c13 : allCells dirCell 1825 1826 [
    213267424271967538037310188517324925529884640794818098244653359175] = true := by
  decide +kernel

theorem k1826_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 1826) 3).1
      394423111576839177929070444697937991335982869774614745664219881878168026863170664594302264108472022173486605799975912585468678922701108942304754).isSome = true := by
  decide +kernel

theorem k1826_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1826) 3).2 2).1
      980135388723309163416251955809972926489327056260651324800149611222220011348392861041).isSome = true := by
  decide +kernel

theorem k1826_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1826) 3).2 2).2
      3826865639819365402982662394352826562059798765579491482294424465017186168406433148).isSome = true := by
  decide +kernel

theorem k1827_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1827) 3).1 2).1
      72209565701659055040737503548981028430383770945502583391255755798651371794414810101256642345684480546620).isSome = true := by
  decide +kernel

theorem k1827_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1827) 3).1 2).2
      61158965294038404341278241767863428134862331640852075141365049497477260495549749052).isSome = true := by
  decide +kernel

theorem k1827_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1827) 3).2 1).1
      3908638182396536321978589206167502462463831251855715315618163900856852664898335265596).isSome = true := by
  decide +kernel

theorem k1827_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1827) 3).2 1).2
      847783737554160891502468797281310502714090290423584334268652311356).isSome = true := by
  decide +kernel

theorem k1828_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1828) 2).1 3).1
      3386956376178397345586853131714366836119994205016455733103516173116).isSome = true := by
  decide +kernel

theorem k1828_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1828) 2).1 3).2
      45854882819960748944758959782512990482853051452).isSome = true := by
  decide +kernel

theorem k1828_2 : (checkBoxH dirMode depth (splitBox (dirCellBox 1828) 2).2
      77263710689602175588798778564362700975503935900980816187660198554505045186124182073064677565550454998965661142259).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 1773 1829 :=
  (Cover.one (box := dirCellBox) (n := 1773)
      (.split 3 (.split 2 (.leaf _ k1773_0) (.leaf _ k1773_1)) (.split 1 (.leaf _ k1773_2) (.leaf _ k1773_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 1774)
      (.split 3 (.split 2 (.leaf _ k1774_0) (.leaf _ k1774_1)) (.leaf _ k1774_2))).trans <|
  (Cover.one (box := dirCellBox) (n := 1775)
      (.split 3 (.leaf _ k1775_0) (.leaf _ k1775_1))).trans <|
  (Cover.dir c3).trans <|
  (Cover.dir c4).trans <|
  (Cover.one (box := dirCellBox) (n := 1797)
      (.split 3 (.leaf _ k1797_0) (.leaf _ k1797_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 1798)
      (.split 3 (.split 2 (.leaf _ k1798_0) (.leaf _ k1798_1)) (.split 2 (.leaf _ k1798_2) (.leaf _ k1798_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 1799)
      (.split 3 (.split 2 (.leaf _ k1799_0) (.leaf _ k1799_1)) (.split 2 (.leaf _ k1799_2) (.leaf _ k1799_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 1800)
      (.split 3 (.split 2 (.leaf _ k1800_0) (.leaf _ k1800_1)) (.split 2 (.leaf _ k1800_2) (.leaf _ k1800_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 1801)
      (.split 2 (.split 3 (.leaf _ k1801_0) (.leaf _ k1801_1)) (.leaf _ k1801_2))).trans <|
  (Cover.one (box := dirCellBox) (n := 1802)
      (.split 3 (.leaf _ k1802_0) (.split 1 (.leaf _ k1802_1) (.leaf _ k1802_2)))).trans <|
  (Cover.one (box := dirCellBox) (n := 1803)
      (.split 3 (.leaf _ k1803_0) (.leaf _ k1803_1))).trans <|
  (Cover.dir c12).trans <|
  (Cover.dir c13).trans <|
  (Cover.one (box := dirCellBox) (n := 1826)
      (.split 3 (.leaf _ k1826_0) (.split 2 (.leaf _ k1826_1) (.leaf _ k1826_2)))).trans <|
  (Cover.one (box := dirCellBox) (n := 1827)
      (.split 3 (.split 2 (.leaf _ k1827_0) (.leaf _ k1827_1)) (.split 1 (.leaf _ k1827_2) (.leaf _ k1827_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 1828)
      (.split 2 (.split 3 (.leaf _ k1828_0) (.leaf _ k1828_1)) (.leaf _ k1828_2)))

end C4.Cert.Dir018
