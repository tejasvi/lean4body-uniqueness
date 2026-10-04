module

public import C4Check

public section

/-! Cells `2774 ≤ n < 2775` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir060

theorem k2774_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2774) 3).1 3).1 2).1 1).1 3).1 2).1
      19262768512585400199602987794212923801277699297282745234963890814842804788208396193727707197644813315441).isSome = true := by
  decide +kernel

theorem k2774_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2774) 3).1 3).1 2).1 1).1 3).1 2).2
      221329544452642070978419813012858391297400230644034553105030524).isSome = true := by
  decide +kernel

theorem k2774_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2774) 3).1 3).1 2).1 1).1 3).2 2).1
      305729780851646099874347743034003876219988569737066423343320637361412721354128487386300052052955264546044).isSome = true := by
  decide +kernel

theorem k2774_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2774) 3).1 3).1 2).1 1).1 3).2 2).2
      1039328171763690598619943489882073752838048079588911107941758678202765877247846741244).isSome = true := by
  decide +kernel

theorem k2774_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2774) 3).1 3).1 2).1 1).2 2).1 2).1
      16577424134096618686712620663056666387519478065236651907402220458344806284073931203825).isSome = true := by
  decide +kernel

theorem k2774_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2774) 3).1 3).1 2).1 1).2 2).1 2).2
      16630724781507819613791629815878939194838413337650153709225652488166360711285390140657).isSome = true := by
  decide +kernel

theorem k2774_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2774) 3).1 3).1 2).1 1).2 2).2 2).1
      1040119085106089530873991968141393575849541038199964635789201271332932462087539416252).isSome = true := by
  decide +kernel

theorem k2774_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2774) 3).1 3).1 2).1 1).2 2).2 2).2
      260538065529541261545248147743725035078587788665563891118168989852298150492157467836).isSome = true := by
  decide +kernel

theorem k2774_8 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2774) 3).1 3).1 2).2 1).1 2).1
      1453345949296011299878929076343475046912459088888384133476258551049645609193726369496159672025516545015655476260569070052734449).isSome = true := by
  decide +kernel

theorem k2774_9 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2774) 3).1 3).1 2).2 1).1 2).2
      16293240051041154166627335538562974756430216577764545228863445649647981478216649073).isSome = true := by
  decide +kernel

theorem k2774_10 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2774) 3).1 3).1 2).2 1).2 2).1
      1448661869690369697994968038597345426920147427955454438230095136959883665088895915302077984951206243952344155275085001003267569).isSome = true := by
  decide +kernel

theorem k2774_11 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2774) 3).1 3).1 2).2 1).2 2).2
      19208523119337442691944226526508063036907702449080680139148159168280353823592740315295287799848867401075).isSome = true := by
  decide +kernel

theorem k2774_12 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2774) 3).1 3).2 2).1 1).1 2).1 3).1
      263537703204964532241828523483095412685225866556914606321743640226381255062363818714801).isSome = true := by
  decide +kernel

theorem k2774_13 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2774) 3).1 3).2 2).1 1).1 2).1 3).2
      16375245769162621708139919923331170480701730736461525057927699500702928017456492485041).isSome = true := by
  decide +kernel

theorem k2774_14 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2774) 3).1 3).2 2).1 1).1 2).2 3).1
      257898664688120445580350795323737637102983112331500808529098563108908063155426057660).isSome = true := by
  decide +kernel

theorem k2774_15 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2774) 3).1 3).2 2).1 1).1 2).2 3).2
      256633019497605695072372839013325538073251229474843133132435205408670748133035761084).isSome = true := by
  decide +kernel

theorem k2774_16 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2774) 3).1 3).2 2).1 1).2 2).1 3).1
      16454212000926928780235020099203504092491328977428565115454823883794391354511120950962).isSome = true := by
  decide +kernel

theorem k2774_17 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2774) 3).1 3).2 2).1 1).2 2).1 3).2
      16374267861556987904826242255685976481015227598144420391444545004352434615718419064498).isSome = true := by
  decide +kernel

theorem k2774_18 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2774) 3).1 3).2 2).1 1).2 2).2 3).1
      1031258078740509996222673988746359091489287537075624144481736112808687679021109894332).isSome = true := by
  decide +kernel

theorem k2774_19 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2774) 3).1 3).2 2).1 1).2 2).2 3).2
      55533696050056955001182132151550721534204594920353235683743602492).isSome = true := by
  decide +kernel

theorem k2774_20 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2774) 3).1 3).2 2).2 1).1 2).1
      89600566493194046407596518030465218455635499869980180245960954196422655948794339508009124370546042298642603065688331593213427).isSome = true := by
  decide +kernel

theorem k2774_21 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2774) 3).1 3).2 2).2 1).1 2).2
      89990881466397585803655219643950093211635440147014662741510305157781599276855252141560605017733463237483705119988931660045564).isSome = true := by
  decide +kernel

theorem k2774_22 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2774) 3).1 3).2 2).2 1).2 2).1
      91697988327135173215262581507047559504568498416993520004391298371914430498934041747627069055645689119202707815832519386083515634).isSome = true := by
  decide +kernel

theorem k2774_23 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2774) 3).1 3).2 2).2 1).2 2).2
      4221345780307630733680770042651551829343658543986495355185188512521128954264198851957489).isSome = true := by
  decide +kernel

theorem k2774_24 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2774) 3).2 2).1 3).1 1).1 2).1 2).1
      4052619218891671938420265430967678712141066862158103905980220988108929032271145048499).isSome = true := by
  decide +kernel

theorem k2774_25 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2774) 3).2 2).1 3).1 1).1 2).1 2).2
      4057893485235669124977206095461303269259056025906555070235306401468486092632810035635).isSome = true := by
  decide +kernel

theorem k2774_26 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2774) 3).2 2).1 3).1 1).1 2).2 3).1
      13838251959399953529738666946138851856147116365659945965406805180).isSome = true := by
  decide +kernel

theorem k2774_27 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2774) 3).2 2).1 3).1 1).1 2).2 3).2
      55098831241180490791648697495102594323819722236149933325555308348).isSome = true := by
  decide +kernel

theorem k2774_28 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2774) 3).2 2).1 3).1 1).2 2).1 2).1
      259082758079556340020041716401262625716855116350546966069800509217278727821061131429555).isSome = true := by
  decide +kernel

theorem k2774_29 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2774) 3).2 2).1 3).1 1).2 2).1 2).2
      4160821657277531096137151688641675404746063847270094150380642726049111721018511241081660).isSome = true := by
  decide +kernel

theorem k2774_30 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2774) 3).2 2).1 3).1 1).2 2).2 2).1
      220316208178265209207597918242367627406899225030375017315552611244).isSome = true := by
  decide +kernel

theorem k2774_31 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2774) 3).2 2).1 3).1 1).2 2).2 2).2
      55143557430062119157111052680168366066927916134974020313019206460).isSome = true := by
  decide +kernel

theorem k2774_32 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2774) 3).2 2).1 3).2 2).1 1).1 3).1
      4041391122339853465736703865121333754674853212835320334208116155424537519008665377202).isSome = true := by
  decide +kernel

theorem k2774_33 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2774) 3).2 2).1 3).2 2).1 1).1 3).2
      4026823562029865980103707601511286829123533009159721977174333825865564781324254960050).isSome = true := by
  decide +kernel

theorem k2774_34 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2774) 3).2 2).1 3).2 2).1 1).2 3).1
      64562482287856991494630385050053225064815516910773093019635124036032538432007428791980).isSome = true := by
  decide +kernel

theorem k2774_35 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2774) 3).2 2).1 3).2 2).1 1).2 3).2
      4020447586426921167063097793992833293575425964156163267407497411227461200760370882220).isSome = true := by
  decide +kernel

theorem k2774_36 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2774) 3).2 2).1 3).2 2).2 1).1
      1248164374022902094221439693065912738139007283850758519616367059841487516154334985919557779698733772258758929651).isSome = true := by
  decide +kernel

theorem k2774_37 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2774) 3).2 2).1 3).2 2).2 1).2 2).1
      874898249322170619826869185237789243289520418913613032061736056492).isSome = true := by
  decide +kernel

theorem k2774_38 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2774) 3).2 2).1 3).2 2).2 1).2 2).2
      13685387349783711243421391538043872322705867328243647052814722732).isSome = true := by
  decide +kernel

theorem k2774_39 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2774) 3).2 2).2 3).1 1).1 2).1
      364373167755507738516148247193537907830512046261979881459407302304493445601932606270791814166141620468109867851130002866979828466).isSome = true := by
  decide +kernel

theorem k2774_40 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2774) 3).2 2).2 3).1 1).1 2).2
      22218959860849515849770273072985748511858623704700816894536380802274424654330832361449294366343823984748906483963031567558131).isSome = true := by
  decide +kernel

theorem k2774_41 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2774) 3).2 2).2 3).1 1).2 2).1
      90855024756853824934566308404982319367290516270830414499378679335741604390489979294384355488192023702508241702065169660475235569).isSome = true := by
  decide +kernel

theorem k2774_42 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2774) 3).2 2).2 3).1 1).2 2).2
      261105458296298923123559520979670333608131369711635618424778968053405293650507845105330).isSome = true := by
  decide +kernel

theorem k2774_43 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2774) 3).2 2).2 3).2 2).1 1).1
      4885224050878139357962124236190391238469717318124885099838469499151596264718415879667212835208025087145565427).isSome = true := by
  decide +kernel

theorem k2774_44 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2774) 3).2 2).2 3).2 2).1 1).2
      4233972512211374554912106875057917389829711244642497122056715144019948581136079656317431027).isSome = true := by
  decide +kernel

theorem k2774_45 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2774) 3).2 2).2 3).2 2).2 1).1
      353328108396663334475263252569667597717257148389856628662844904838172338239829375756879923215429449988536592568450091763727548).isSome = true := by
  decide +kernel

theorem k2774_46 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2774) 3).2 2).2 3).2 2).2 1).2
      4141922287387405112127189858309751745667394411812365849455085757453235261492311069465267).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 2774 2775 :=
  (Cover.one (box := dirCellBox) (n := 2774)
      (.split 3 (.split 3 (.split 2 (.split 1 (.split 3 (.split 2 (.leaf _ k2774_0) (.leaf _ k2774_1)) (.split 2 (.leaf _ k2774_2) (.leaf _ k2774_3))) (.split 2 (.split 2 (.leaf _ k2774_4) (.leaf _ k2774_5)) (.split 2 (.leaf _ k2774_6) (.leaf _ k2774_7)))) (.split 1 (.split 2 (.leaf _ k2774_8) (.leaf _ k2774_9)) (.split 2 (.leaf _ k2774_10) (.leaf _ k2774_11)))) (.split 2 (.split 1 (.split 2 (.split 3 (.leaf _ k2774_12) (.leaf _ k2774_13)) (.split 3 (.leaf _ k2774_14) (.leaf _ k2774_15))) (.split 2 (.split 3 (.leaf _ k2774_16) (.leaf _ k2774_17)) (.split 3 (.leaf _ k2774_18) (.leaf _ k2774_19)))) (.split 1 (.split 2 (.leaf _ k2774_20) (.leaf _ k2774_21)) (.split 2 (.leaf _ k2774_22) (.leaf _ k2774_23))))) (.split 2 (.split 3 (.split 1 (.split 2 (.split 2 (.leaf _ k2774_24) (.leaf _ k2774_25)) (.split 3 (.leaf _ k2774_26) (.leaf _ k2774_27))) (.split 2 (.split 2 (.leaf _ k2774_28) (.leaf _ k2774_29)) (.split 2 (.leaf _ k2774_30) (.leaf _ k2774_31)))) (.split 2 (.split 1 (.split 3 (.leaf _ k2774_32) (.leaf _ k2774_33)) (.split 3 (.leaf _ k2774_34) (.leaf _ k2774_35))) (.split 1 (.leaf _ k2774_36) (.split 2 (.leaf _ k2774_37) (.leaf _ k2774_38))))) (.split 3 (.split 1 (.split 2 (.leaf _ k2774_39) (.leaf _ k2774_40)) (.split 2 (.leaf _ k2774_41) (.leaf _ k2774_42))) (.split 2 (.split 1 (.leaf _ k2774_43) (.leaf _ k2774_44)) (.split 1 (.leaf _ k2774_45) (.leaf _ k2774_46)))))))

end C4.Cert.Dir060
