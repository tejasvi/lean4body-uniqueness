module

public import C4Check

public section

/-! Cells `2834 ≤ n < 2841` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir069

theorem k2834_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2834) 3).1 2).1 3).1 1).1
      3402357072655772671950539746289923532608569565352710015518780863436).isSome = true := by
  decide +kernel

theorem k2834_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2834) 3).1 2).1 3).1 1).2
      3402045598159997266029140638579624159174259596255783129701622266940).isSome = true := by
  decide +kernel

theorem k2834_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2834) 3).1 2).1 3).2 1).1
      212245396276558322136661940073686393454506749828636794642648084172).isSome = true := by
  decide +kernel

theorem k2834_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2834) 3).1 2).1 3).2 1).2
      3395580930347941234407721657022461220887085457711535931847381662780).isSome = true := by
  decide +kernel

theorem k2834_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2834) 3).1 2).2 3).1 1).1
      3401898458190627396460871425692955669245445164146790295032632753212).isSome = true := by
  decide +kernel

theorem k2834_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2834) 3).1 2).2 3).1 1).2
      3404627977415875333517185146876332008089438527941402730617536035900).isSome = true := by
  decide +kernel

theorem k2834_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2834) 3).1 2).2 3).2 1).1
      2878288743980747751342136813096898763755695820).isSome = true := by
  decide +kernel

theorem k2834_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2834) 3).1 2).2 3).2 1).2
      3398072478372407208500740551712464180573373585535717978686409718844).isSome = true := by
  decide +kernel

theorem k2834_8 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2834) 3).2 2).1 1).1 3).1
      212068049713520270713472204550947747908865805608208695414337646284).isSome = true := by
  decide +kernel

theorem k2834_9 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2834) 3).2 2).1 1).1 3).2
      13258179011259778973671987774992987401204556793792012980602772172).isSome = true := by
  decide +kernel

theorem k2834_10 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2834) 3).2 2).1 1).2 3).1
      848202706237779570296229223419561669957801237562874855024842554428).isSome = true := by
  decide +kernel

theorem k2834_11 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2834) 3).2 2).1 1).2 3).2
      45943972741798840373211314759379611665614695484).isSome = true := by
  decide +kernel

theorem k2834_12 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2834) 3).2 2).2 1).1 3).1
      212203013089617210238487172847302586302873595029081037704670032844).isSome = true := by
  decide +kernel

theorem k2834_13 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2834) 3).2 2).2 1).1 3).2
      13252691261208138315410568744950492840936292605398650524855147212).isSome = true := by
  decide +kernel

theorem k2834_14 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2834) 3).2 2).2 1).2 3).1
      3395084326861881630450083359427348442650260465145758227673839877180).isSome = true := by
  decide +kernel

theorem k2834_15 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2834) 3).2 2).2 1).2 3).2
      11503726394882442680342351400273815018132401212).isSome = true := by
  decide +kernel

theorem k2835_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2835) 2).1 3).1 1).1
      255895738857516152889576793358627538944822378124868191906598006877317182635946902574033715).isSome = true := by
  decide +kernel

theorem k2835_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2835) 2).1 3).1 1).2
      65498192771170207436399519927039082798715257908422710782621052557182134562710258748824416499).isSome = true := by
  decide +kernel

theorem k2835_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2835) 2).1 3).2 1).1
      3999491644416714999455040617742138477212293181922272779848996927982133322448302478507068).isSome = true := by
  decide +kernel

theorem k2835_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2835) 2).1 3).2 1).2
      18425827520782387857530862435542899194024550343031473300646857707691239964642749549801460531502295526210620).isSome = true := by
  decide +kernel

theorem k2835_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2835) 2).2 3).1 1).1
      18909355684746866072501827644121803368657103225854555232064732113005259193621064587671648220831929786936748851).isSome = true := by
  decide +kernel

theorem k2835_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2835) 2).2 3).1 1).2
      18894979996858118746319254551804126218735245866225387125100263462313664642987450123637685298708093066026335292).isSome = true := by
  decide +kernel

theorem k2835_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2835) 2).2 3).2 1).1
      3997274570507573583850522853787740126043899501966723212999841073136214184811366249610300).isSome = true := by
  decide +kernel

theorem k2835_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2835) 2).2 3).2 1).2
      4608438343524660397417832650834089840124538992594765804706437118562725054779725125619934904258694884473916).isSome = true := by
  decide +kernel

theorem k2836_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2836) 2).1 3).1 1).1
      249523782189331569620241831865406276336558661369146999456247004407575727899049006513212).isSome = true := by
  decide +kernel

theorem k2836_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2836) 2).1 3).1 1).2
      845420815582479381358134147074757239673045234266776932532285193276).isSome = true := by
  decide +kernel

theorem k2836_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2836) 2).1 3).2 1).1
      975145486491307405996618503034015443045314422947110164908215240376321822711179213884).isSome = true := by
  decide +kernel

theorem k2836_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2836) 2).1 3).2 1).2
      211227233505247909265920876372505869950988158015842619581951474748).isSome = true := by
  decide +kernel

theorem k2836_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2836) 2).2 3).1 1).1
      998456782653525594924348838010840886790482845214587942280959624181262872234488373918780).isSome = true := by
  decide +kernel

theorem k2836_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2836) 2).2 3).1 1).2
      4604433931732453476062260744047116969775956141836425432969009863714948196156866776146089254059914263641148).isSome = true := by
  decide +kernel

theorem k2836_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2836) 2).2 3).2 1).1
      11452616004632402368179561577361877434718039756).isSome = true := by
  decide +kernel

theorem k2836_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2836) 2).2 3).2 1).2
      211278568526101980705832547018386935638784554518221078881632631868).isSome = true := by
  decide +kernel

theorem k2837_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2837) 2).1 3).1 1).1
      243416988525720961261988541250466703989969301717323310017199824792005846146257215276).isSome = true := by
  decide +kernel

theorem k2837_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2837) 2).1 3).1 1).2
      3298742449564213722745752225841482133899510737716000687484460844).isSome = true := by
  decide +kernel

theorem k2837_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2837) 2).1 3).2
      4595685734097967122466657252399365710863041067326555144634786201500252735614837338532806309053896800165681).isSome = true := by
  decide +kernel

theorem k2837_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2837) 2).2 3).1
      347481246383949234694267035180621131289974726726763317123750670577768193814146499809887780860923398878660302349197230638137560881).isSome = true := by
  decide +kernel

theorem k2837_4 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2837) 2).2 3).2
      86829990611440396329988344934556320659770561195643839309155011456991583637504232786081077053030304801458093619153006249150634801).isSome = true := by
  decide +kernel

theorem k2838_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2838) 2).1 3).1
      15565640370282058478331915085957181074339452878250754224418219688864941614696530040625).isSome = true := by
  decide +kernel

theorem k2838_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2838) 2).1 3).2
      62241653019366538893694869518881958498905925078553123287941519363892972714535153523891).isSome = true := by
  decide +kernel

theorem k2838_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2838) 2).2 3).1
      62270948591685267423271438068312506914788271581433321820705953437863467665325573757745).isSome = true := by
  decide +kernel

theorem k2838_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2838) 2).2 3).2
      15562983839232726018744727692756987567748632909869283326401346271177041849758462547761).isSome = true := by
  decide +kernel

theorem k2839_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2839) 2).1
      21680921641448598795453397640826752258072654633935193283310894285665007498321898479654058010927886804657070373183663458531545799).isSome = true := by
  decide +kernel

theorem k2839_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2839) 2).2 3).1
      3889864108968384609652099756761948689204642106251801593295312941455984308035417141820).isSome = true := by
  decide +kernel

theorem k2839_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2839) 2).2 3).2
      972243250951531929930763100568074730298158626569616595035069858071567271702193601708).isSome = true := by
  decide +kernel

theorem k2840_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2840) 2).1
      71711671829190977419698918315509441833638657337213242202969838243145875655348148565425969686404907009479).isSome = true := by
  decide +kernel

theorem k2840_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 2840) 2).2
      73437239405573148668132336728878153719699715688814778852239758650954263102340290491006643159301342244222151).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 2834 2841 :=
  (Cover.one (box := dirCellBox) (n := 2834)
      (.split 3 (.split 2 (.split 3 (.split 1 (.leaf _ k2834_0) (.leaf _ k2834_1)) (.split 1 (.leaf _ k2834_2) (.leaf _ k2834_3))) (.split 3 (.split 1 (.leaf _ k2834_4) (.leaf _ k2834_5)) (.split 1 (.leaf _ k2834_6) (.leaf _ k2834_7)))) (.split 2 (.split 1 (.split 3 (.leaf _ k2834_8) (.leaf _ k2834_9)) (.split 3 (.leaf _ k2834_10) (.leaf _ k2834_11))) (.split 1 (.split 3 (.leaf _ k2834_12) (.leaf _ k2834_13)) (.split 3 (.leaf _ k2834_14) (.leaf _ k2834_15)))))).trans <|
  (Cover.one (box := dirCellBox) (n := 2835)
      (.split 2 (.split 3 (.split 1 (.leaf _ k2835_0) (.leaf _ k2835_1)) (.split 1 (.leaf _ k2835_2) (.leaf _ k2835_3))) (.split 3 (.split 1 (.leaf _ k2835_4) (.leaf _ k2835_5)) (.split 1 (.leaf _ k2835_6) (.leaf _ k2835_7))))).trans <|
  (Cover.one (box := dirCellBox) (n := 2836)
      (.split 2 (.split 3 (.split 1 (.leaf _ k2836_0) (.leaf _ k2836_1)) (.split 1 (.leaf _ k2836_2) (.leaf _ k2836_3))) (.split 3 (.split 1 (.leaf _ k2836_4) (.leaf _ k2836_5)) (.split 1 (.leaf _ k2836_6) (.leaf _ k2836_7))))).trans <|
  (Cover.one (box := dirCellBox) (n := 2837)
      (.split 2 (.split 3 (.split 1 (.leaf _ k2837_0) (.leaf _ k2837_1)) (.leaf _ k2837_2)) (.split 3 (.leaf _ k2837_3) (.leaf _ k2837_4)))).trans <|
  (Cover.one (box := dirCellBox) (n := 2838)
      (.split 2 (.split 3 (.leaf _ k2838_0) (.leaf _ k2838_1)) (.split 3 (.leaf _ k2838_2) (.leaf _ k2838_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 2839)
      (.split 2 (.leaf _ k2839_0) (.split 3 (.leaf _ k2839_1) (.leaf _ k2839_2)))).trans <|
  (Cover.one (box := dirCellBox) (n := 2840)
      (.split 2 (.leaf _ k2840_0) (.leaf _ k2840_1)))

end C4.Cert.Dir069
