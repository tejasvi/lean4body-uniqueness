module

public import C4Check

public section

/-! Cells `3813 ≤ n < 3872` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir124

theorem k3813_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3813) 3).1
      246222088751962486024355120146059393127078019107347957144104603014581003824457193266).isSome = true := by
  decide +kernel

theorem k3813_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 3813) 3).2
      3934810415032795956861331675931039701148415672158897729881992817655813767780040906546).isSome = true := by
  decide +kernel

theorem k3814_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3814) 2).1
      1185307450695136658731599716712466871927274087787293831271238101305684130258597639480966241799309947722652467).isSome = true := by
  decide +kernel

theorem k3814_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 3814) 2).2
      250982470139651541673598507765831486879785844977968974867710623660508565042082327598899).isSome = true := by
  decide +kernel

theorem k3815_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3815) 2).1
      4729538840480683847002230430181725255095563669894950369972998170980964699862185036907564164515505959290129203).isSome = true := by
  decide +kernel

theorem k3815_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 3815) 2).2
      4005972725900604842241875776216415432926943726091879843829771221620332045311384017554227).isSome = true := by
  decide +kernel

theorem k3816_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3816) 2).1
      262159624002717107746881278610594554518196723342203533482441614096032256739067980213602160433).isSome = true := by
  decide +kernel

theorem k3816_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 3816) 2).2
      15994840776756196141187737523134680864729830917035556116200439359182279628584884302623539).isSome = true := by
  decide +kernel

theorem k3817_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3817) 2).1
      5567447799578883241523683800901028048822640532566321174163613409866788033226402224159699845744531039745445582441610058856590359612).isSome = true := by
  decide +kernel

theorem k3817_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 3817) 2).2
      15977950390345547648552343529783419465342674515550296708181304463420958314579362710932273).isSome = true := by
  decide +kernel

theorem k3818_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3818) 2).1
      301487729145734078428477415273422388223324663137729498631343138643184050043283068906034064782740187645935988977).isSome = true := by
  decide +kernel

theorem k3818_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 3818) 2).2
      3990166938979528255313618885257464889591188776127640342017404670641219225367791700491324).isSome = true := by
  decide +kernel

theorem k3819_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3819) 1).1
      3986763370393017873363962487804298287364682572317292186882290588014519583268751049276476).isSome = true := by
  decide +kernel

theorem k3819_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 3819) 1).2
      3986924960568927232151526674497617664423376859362225869172521745024604848270282525031484).isSome = true := by
  decide +kernel

theorem k3820_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3820) 1).1
      249018163990182877834268273302412467726852763982700673973741359220341518371352057987900).isSome = true := by
  decide +kernel

theorem k3820_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 3820) 1).2
      13499688106322889143463562730764450035799682215236910589946595818556).isSome = true := by
  decide +kernel

theorem k3821_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3821) 1).1
      52706542563116481684900571266998771886626164169617068189978849852).isSome = true := by
  decide +kernel

theorem k3821_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 3821) 1).2
      52722382780305821473579595429082045086367556388720236875282248252).isSome = true := by
  decide +kernel

theorem c9 : allCells dirCell 3822 3823 [
    1043643590746810886372524557868259830224557312378106662159416515288066350716438290519817701617] = true := by
  decide +kernel

theorem c10 : allCells dirCell 3823 3824 [
    16302612127512698782001166189596455498910563719041248600673481292401155889266886305818028273] = true := by
  decide +kernel

theorem c11 : allCells dirCell 3824 3825 [
    21157533556512973336116245497459544953595756550501809775174574099616740389662281051994408659065253605355465855641335168457916] = true := by
  decide +kernel

theorem c12 : allCells dirCell 3825 3841 [
    51424271417898002161485173496709025234112898023661500179854929, 147556936719481978772, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] = true := by
  decide +kernel

theorem c13 : allCells dirCell 3841 3842 [
    18575061031899237134929200512164197525381487907086202791323645623840551143081416048883957314726119128469831] = true := by
  decide +kernel

theorem c14 : allCells dirCell 3842 3843 [
    1432593009598333141542862448111620809359723040342538694024649102927135494633644599823112520214129524232607830180153875697097796705486] = true := by
  decide +kernel

theorem k3843_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3843) 2).1
      1001465729950047758104860133213353777748816246055399591860425529884810558303133664637747).isSome = true := by
  decide +kernel

theorem k3843_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 3843) 2).2
      53019587070099264402199494501267864709209253977249371087213247692).isSome = true := by
  decide +kernel

theorem k3844_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3844) 2).1
      62498054134956911813482767405464235674138083108671069717577774768692602341760551285452).isSome = true := by
  decide +kernel

theorem k3844_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 3844) 2).2
      3906515834621244370036482105690865844283675316184709782684956409194325088715335398092).isSome = true := by
  decide +kernel

theorem k3845_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3845) 2).1
      249665497001879084081580822870319326393361955290729654020713085956753835222434659580988).isSome = true := by
  decide +kernel

theorem k3845_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 3845) 2).2
      15604074702981500328312165158863817775319611151195070660365267789067490854535488711740).isSome = true := by
  decide +kernel

theorem k3846_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3846) 2).1
      3990245992554894849613505953742215575582980085981589380227111151108182522319571990035516).isSome = true := by
  decide +kernel

theorem k3846_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 3846) 2).2
      52811444114210968999949934149014336613577775874660674322143460412).isSome = true := by
  decide +kernel

theorem c19 : allCells dirCell 3847 3848 [
    77121724383096286848851422267477172133661352153771173985844214792490522094150151646849632992844963891277812920562] = true := by
  decide +kernel

theorem k3848_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3848) 1).1
      52733567521253422824271023171956938510724496572037403847172682300).isSome = true := by
  decide +kernel

theorem k3848_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 3848) 1).2
      52736326699784870739789094691785734424587328078934870001556255292).isSome = true := by
  decide +kernel

theorem c21 : allCells dirCell 3849 3850 [
    5551034585536045059824607423577536494918101607583240573773060240104954001666302028078928534628494806199650557022860950328160629564] = true := by
  decide +kernel

theorem c22 : allCells dirCell 3850 3851 [
    4700166036146799030914561234621713402767991776638074817538051433942328289612308519193014710202261877948599100] = true := by
  decide +kernel

theorem c23 : allCells dirCell 3851 3852 [
    995022894143150390461146742210238020735157656939794371407445059004126618891351031098556] = true := by
  decide +kernel

theorem c24 : allCells dirCell 3852 3854 [
    15544499195425563914316355425969680763229195727994300293933755842438617743639436981681,
    51424148099902946558926513708109493113391812565682986756231889] = true := by
  decide +kernel

theorem c25 : allCells dirCell 3854 3870 [
    147556274950936467812, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    3330475422500323795131762518351353673364259614772630897750156243] = true := by
  decide +kernel

theorem c26 : allCells dirCell 3870 3871 [
    64221835313851433755880737033509443574763292597125107814404284130269251559410664143611086] = true := by
  decide +kernel

theorem c27 : allCells dirCell 3871 3872 [
    1025334688336099951599872858424543915158629386039913224948458460849942572054989024378965198] = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 3813 3872 :=
  (Cover.one (box := dirCellBox) (n := 3813)
      (.split 3 (.leaf _ k3813_0) (.leaf _ k3813_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 3814)
      (.split 2 (.leaf _ k3814_0) (.leaf _ k3814_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 3815)
      (.split 2 (.leaf _ k3815_0) (.leaf _ k3815_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 3816)
      (.split 2 (.leaf _ k3816_0) (.leaf _ k3816_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 3817)
      (.split 2 (.leaf _ k3817_0) (.leaf _ k3817_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 3818)
      (.split 2 (.leaf _ k3818_0) (.leaf _ k3818_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 3819)
      (.split 1 (.leaf _ k3819_0) (.leaf _ k3819_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 3820)
      (.split 1 (.leaf _ k3820_0) (.leaf _ k3820_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 3821)
      (.split 1 (.leaf _ k3821_0) (.leaf _ k3821_1))).trans <|
  (Cover.dir c9).trans <|
  (Cover.dir c10).trans <|
  (Cover.dir c11).trans <|
  (Cover.dir c12).trans <|
  (Cover.dir c13).trans <|
  (Cover.dir c14).trans <|
  (Cover.one (box := dirCellBox) (n := 3843)
      (.split 2 (.leaf _ k3843_0) (.leaf _ k3843_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 3844)
      (.split 2 (.leaf _ k3844_0) (.leaf _ k3844_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 3845)
      (.split 2 (.leaf _ k3845_0) (.leaf _ k3845_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 3846)
      (.split 2 (.leaf _ k3846_0) (.leaf _ k3846_1))).trans <|
  (Cover.dir c19).trans <|
  (Cover.one (box := dirCellBox) (n := 3848)
      (.split 1 (.leaf _ k3848_0) (.leaf _ k3848_1))).trans <|
  (Cover.dir c21).trans <|
  (Cover.dir c22).trans <|
  (Cover.dir c23).trans <|
  (Cover.dir c24).trans <|
  (Cover.dir c25).trans <|
  (Cover.dir c26).trans <|
  (Cover.dir c27)

end C4.Cert.Dir124
