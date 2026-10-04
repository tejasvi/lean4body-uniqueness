module

public import C4Check

public section

/-! Cells `4065 ≤ n < 4073` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir132

theorem k4065_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4065) 2).1 3).1 1).1
      258381420225862317350722953189112280906114890288866517559349983262043163522856749087820594).isSome = true := by
  decide +kernel

theorem k4065_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4065) 2).1 3).1 1).2
      16144194756563201991716277761689658257677422778472140714185146226011741088007301858970418).isSome = true := by
  decide +kernel

theorem k4065_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4065) 2).1 3).2 1).1
      64413957281499427936308545161619338121705883343174358350063808243197662714331276727933746).isSome = true := by
  decide +kernel

theorem k4065_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4065) 2).1 3).2 1).2
      1187941140071078635498557361116359183096474260293534264224177748905648707074424422953459966460101807455984434).isSome = true := by
  decide +kernel

theorem k4065_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4065) 2).2 3).1 1).1
      1009681801642771752702291439663856168145005552668256522163045716248142205750000804262706).isSome = true := by
  decide +kernel

theorem k4065_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4065) 2).2 3).1 1).2
      1009421211545914187534455697634785387538542085365577826432770404630987449885813068886834).isSome = true := by
  decide +kernel

theorem k4065_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4065) 2).2 3).2 1).1
      4027604450062234394755514307132792000227961491214395525823526818619765585841688290904882).isSome = true := by
  decide +kernel

theorem k4065_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4065) 2).2 3).2 1).2
      4026655323612528090515487024091268083195995518054509389426272660238593959173838571162418).isSome = true := by
  decide +kernel

theorem k4066_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4066) 2).1 3).1 1).1
      16069065121478960164780860677534282445176331022293524049291477892981596655224971022932786).isSome = true := by
  decide +kernel

theorem k4066_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4066) 2).1 3).1 1).2
      1004095129764172784813511892664254723163296216747560600011362892904622573573150738062130).isSome = true := by
  decide +kernel

theorem k4066_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4066) 2).1 3).2 1).1
      250607690284243839377925423567785109425110230411609424641882229536524122780800537441228).isSome = true := by
  decide +kernel

theorem k4066_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4066) 2).1 3).2 1).2
      62702347391640866558468480851625061295399876185990303286579574837218050747246873244620).isSome = true := by
  decide +kernel

theorem k4066_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4066) 2).2 3).1 1).1
      13942155129943828354880920017469337519613098852776618956015389479742258).isSome = true := by
  decide +kernel

theorem k4066_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4066) 2).2 3).1 1).2
      1158015063517302696200397722382073659147999743184284349147795916061503075192132285212019623374988031023820).isSome = true := by
  decide +kernel

theorem k4066_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4066) 2).2 3).2 1).1
      212353544659021641225259637226114330860217573596830740790507985612).isSome = true := by
  decide +kernel

theorem k4066_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4066) 2).2 3).2 1).2
      3916558075436376206054141934730265561834237153944106806529971507588645445591748827852).isSome = true := by
  decide +kernel

theorem k4067_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4067) 2).1 3).1 1).1
      250251932174533546848792478514208303916657967933231361452797116150477786979587044719676).isSome = true := by
  decide +kernel

theorem k4067_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4067) 2).1 3).1 1).2
      62586393280313606609832951690197335825221873904147166763389501310162179116094052609084).isSome = true := by
  decide +kernel

theorem k4067_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4067) 2).1 3).2 1).1
      3387612447863398419548661620361804529809649404189431857646801173564).isSome = true := by
  decide +kernel

theorem k4067_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4067) 2).1 3).2 1).2
      52927838253879410275347548468689522080872816449538138144634158140).isSome = true := by
  decide +kernel

theorem k4067_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4067) 2).2 3).1 1).1
      13259143545593798984974544138341062784449135925988829318637656780).isSome = true := by
  decide +kernel

theorem k4067_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4067) 2).2 3).1 1).2
      13250894949645227242855746436217492474515802700823904910321359564).isSome = true := by
  decide +kernel

theorem k4067_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4067) 2).2 3).2 1).1
      976785424524144948680917387310560570436892828195711780878843799821269066395777130188).isSome = true := by
  decide +kernel

theorem k4067_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4067) 2).2 3).2 1).2
      52944865971226700911304488057290115448705920098322201798974594764).isSome = true := by
  decide +kernel

theorem k4068_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4068) 2).1 3).1
      5569066622349879052886078052670692323378125484070579875244671480551551936414785220848497067572129733803517635868429704280986284273).isSome = true := by
  decide +kernel

theorem k4068_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4068) 2).1 3).2 1).1
      52846258268963769585499432987749020983210232454557031429684195900).isSome = true := by
  decide +kernel

theorem k4068_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4068) 2).1 3).2 1).2
      52842466286519768936562925724740923307916602235623170262541136444).isSome = true := by
  decide +kernel

theorem k4068_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4068) 2).2 3).1
      1207853950978098663870843021538466908385789492107096065179599275101543933669335183013190483685743485120331362545).isSome = true := by
  decide +kernel

theorem k4068_4 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4068) 2).2 3).2
      1391615471560211825743759197761804380869679021724182474055146131862576024968300199695590123979435352568850813199885518231849791729).isSome = true := by
  decide +kernel

theorem k4069_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4069) 2).1 3).1
      86906158267889925102149096705932371126960665976664036216628835020402935275360972216418804197787264474376350522814009501265414716).isSome = true := by
  decide +kernel

theorem k4069_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4069) 2).1 3).2
      4598611363510315303663904680983029835762199704136186343186132850238668878750478448175911163616408987753020).isSome = true := by
  decide +kernel

theorem k4069_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4069) 2).2 3).1
      18848271091427582255484775784640398324497980949123858319380943202854118164769746860404289667348968927294112572).isSome = true := by
  decide +kernel

theorem k4069_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4069) 2).2 3).2
      294360527962793891608920119035493514464177668605237795621962030742881962166390690776314969700457761193062972).isSome = true := by
  decide +kernel

theorem k4070_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4070) 2).1 3).1
      15574307031870757055447387654092229552249079883666467004116992419892836808893895531068).isSome = true := by
  decide +kernel

theorem k4070_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4070) 2).1 3).2
      15569107540080377230333212007541793801963884135512370552212413909900383136346793300796).isSome = true := by
  decide +kernel

theorem k4070_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4070) 2).2 3).1
      249221710619273937869906673408694978163099814035976933643844757826146109411867911768636).isSome = true := by
  decide +kernel

theorem k4070_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4070) 2).2 3).2
      973207846097093378696676085832312709553700946060183776168929681430075164094588384828).isSome = true := by
  decide +kernel

theorem k4071_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4071) 2).1 1).1
      3374592346915701046444266971869225465341416641565395289018109741884).isSome = true := by
  decide +kernel

theorem k4071_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4071) 2).1 1).2
      3890748695402131447855097221929643945436171423230660759393551988135357402961776465724).isSome = true := by
  decide +kernel

theorem k4071_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4071) 2).2 3).1
      972902831189208439789825877718767444275234778641586792123536144504368800743236695612).isSome = true := by
  decide +kernel

theorem k4071_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4071) 2).2 3).2
      972649274557171303606064945750040557469705934225763031033754981793238049962397660732).isSome = true := by
  decide +kernel

theorem k4072_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4072) 2).1
      21681257767714495509577647836549912213073612748630041260639661733944514661154598387291812331751287980432480644123581843974728947).isSome = true := by
  decide +kernel

theorem k4072_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4072) 2).2 3).1
      972442800526482472235908906581284446344830351563919981407800178192339726847051167292).isSome = true := by
  decide +kernel

theorem k4072_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4072) 2).2 3).2
      243066746065168735248953103260484311543693037288973273692944708430237074655005767228).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 4065 4073 :=
  (Cover.one (box := dirCellBox) (n := 4065)
      (.split 2 (.split 3 (.split 1 (.leaf _ k4065_0) (.leaf _ k4065_1)) (.split 1 (.leaf _ k4065_2) (.leaf _ k4065_3))) (.split 3 (.split 1 (.leaf _ k4065_4) (.leaf _ k4065_5)) (.split 1 (.leaf _ k4065_6) (.leaf _ k4065_7))))).trans <|
  (Cover.one (box := dirCellBox) (n := 4066)
      (.split 2 (.split 3 (.split 1 (.leaf _ k4066_0) (.leaf _ k4066_1)) (.split 1 (.leaf _ k4066_2) (.leaf _ k4066_3))) (.split 3 (.split 1 (.leaf _ k4066_4) (.leaf _ k4066_5)) (.split 1 (.leaf _ k4066_6) (.leaf _ k4066_7))))).trans <|
  (Cover.one (box := dirCellBox) (n := 4067)
      (.split 2 (.split 3 (.split 1 (.leaf _ k4067_0) (.leaf _ k4067_1)) (.split 1 (.leaf _ k4067_2) (.leaf _ k4067_3))) (.split 3 (.split 1 (.leaf _ k4067_4) (.leaf _ k4067_5)) (.split 1 (.leaf _ k4067_6) (.leaf _ k4067_7))))).trans <|
  (Cover.one (box := dirCellBox) (n := 4068)
      (.split 2 (.split 3 (.leaf _ k4068_0) (.split 1 (.leaf _ k4068_1) (.leaf _ k4068_2))) (.split 3 (.leaf _ k4068_3) (.leaf _ k4068_4)))).trans <|
  (Cover.one (box := dirCellBox) (n := 4069)
      (.split 2 (.split 3 (.leaf _ k4069_0) (.leaf _ k4069_1)) (.split 3 (.leaf _ k4069_2) (.leaf _ k4069_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 4070)
      (.split 2 (.split 3 (.leaf _ k4070_0) (.leaf _ k4070_1)) (.split 3 (.leaf _ k4070_2) (.leaf _ k4070_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 4071)
      (.split 2 (.split 1 (.leaf _ k4071_0) (.leaf _ k4071_1)) (.split 3 (.leaf _ k4071_2) (.leaf _ k4071_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 4072)
      (.split 2 (.leaf _ k4072_0) (.split 3 (.leaf _ k4072_1) (.leaf _ k4072_2))))

end C4.Cert.Dir132
