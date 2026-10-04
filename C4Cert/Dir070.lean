module

public import C4Check

public section

/-! Cells `2841 ≤ n < 2862` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir070

theorem c0 : allCells dirCell 2841 2842 [
    29494056770553504553083019700149768150136370562262014191871431612828987728977233699542072796915657914737035385147060943167867229709884237337795013276532657094329882054] = true := by
  decide +kernel

theorem c1 : allCells dirCell 2842 2858 [
    971509545686384850631218412841497660041101795865992127692963647992651767619251143750,
    28333765858934549981458, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] = true := by
  decide +kernel

theorem c2 : allCells dirCell 2858 2859 [
    439188526651219815577037860490602999303208783790741255830983435499211541536710591865527609809731492404021781613902532407341306179811004508549343462054663] = true := by
  decide +kernel

theorem k2859_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2859) 3).1 2).1 3).1
      22026525486386143247813780481575369028394358783529657225475756361825005067731202093573379737870278044351034125423348073502153).isSome = true := by
  decide +kernel

theorem k2859_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2859) 3).1 2).1 3).2
      119313883003208780209384230305636660120961969668840115417544221759313427023846639206806006636923608687674737878827801950264808016364705653208087502794493434751972849).isSome = true := by
  decide +kernel

theorem k2859_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2859) 3).1 2).2
      6465565465666005375172200664538724118516154033253893602466157581417546756483962032733888791921099266153727420222363321485231839944936810868513095).isSome = true := by
  decide +kernel

theorem k2859_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2859) 3).2 2).1 3).1 1).1
      62713252430544591295060183032610032948917330649114232854407144631726926325109413298).isSome = true := by
  decide +kernel

theorem k2859_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2859) 3).2 2).1 3).1 1).2
      250511457095379010120506071716614143757800368839371403879895670784958085278813870514).isSome = true := by
  decide +kernel

theorem k2859_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2859) 3).2 2).1 3).2 1).1
      999548295239298751246248852291864006184433343948450019188987362495958682575025626300).isSome = true := by
  decide +kernel

theorem k2859_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2859) 3).2 2).1 3).2 1).2
      866628992050181440891457066270990871650481128039202022854536153916).isSome = true := by
  decide +kernel

theorem k2859_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2859) 3).2 2).2 1).1
      349031849657229278152802422369287523881158624659699070908095702236112494627915936365486462521947964701291081357443572916385010).isSome = true := by
  decide +kernel

theorem k2859_8 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2859) 3).2 2).2 1).2
      347947874461345328574918158053236318176485292162921145797694742296486454610722324017451048861058091608173142436568046680241395).isSome = true := by
  decide +kernel

theorem k2860_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2860) 3).1 2).1 3).1 1).1
      54010297010416531901271142369811068950439871343952080595658970940).isSome = true := by
  decide +kernel

theorem k2860_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2860) 3).1 2).1 3).1 1).2
      215961620284661780669444352879748019197480819360467393183653286716).isSome = true := by
  decide +kernel

theorem k2860_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2860) 3).1 2).1 3).2 1).1
      11676994757369181840526539135467716102647073596).isSome = true := by
  decide +kernel

theorem k2860_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2860) 3).1 2).1 3).2 1).2
      2988560960026461314796586770227163238221916304050).isSome = true := by
  decide +kernel

theorem k2860_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2860) 3).1 2).2 1).1
      88702103939683788566645436408542541844162433852167183539989137848474894945437201170277250846057146407065281306097596604062618546).isSome = true := by
  decide +kernel

theorem k2860_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2860) 3).1 2).2 1).2
      354543191905340948689782108508750382025283404795340420356894113322033625652315866715442270259708275648663412537563739342662767539).isSome = true := by
  decide +kernel

theorem k2860_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2860) 3).2 2).1 3).1 1).1
      859455780685944420264776606544335249923460391151155481250470899260).isSome = true := by
  decide +kernel

theorem k2860_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2860) 3).2 2).1 3).1 1).2
      54993397811978477025490606312406960249830620107145096078541248362674).isSome = true := by
  decide +kernel

theorem k2860_8 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2860) 3).2 2).1 3).2 1).1
      54884829989362108889120499787152364317228494407729799092044233133628).isSome = true := by
  decide +kernel

theorem k2860_9 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2860) 3).2 2).1 3).2 1).2
      13718072323553563031660767482416304621703681390543115269476102163004).isSome = true := by
  decide +kernel

theorem k2860_10 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2860) 3).2 2).2 1).1
      352996611279938810745975536705483523863946234987429840941433896195785729704220558736126243910465148455473488227321322327628467443).isSome = true := by
  decide +kernel

theorem k2860_11 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2860) 3).2 2).2 1).2
      265804619527058259487758967509888196528633604533220648847892945472601906461737793032673544434).isSome = true := by
  decide +kernel

theorem k2861_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2861) 3).1 2).1 3).1 2).1
      219053723166257302460952736302223172151725583143278653320294100355644).isSome = true := by
  decide +kernel

theorem k2861_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2861) 3).1 2).1 3).1 2).2
      13695462039896437829243164452829947935208702602923182470433026853436).isSome = true := by
  decide +kernel

theorem k2861_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2861) 3).1 2).1 3).2 1).1
      3417829257492661255676222292096886714444363638248955428645025346108).isSome = true := by
  decide +kernel

theorem k2861_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2861) 3).1 2).1 3).2 1).2
      252162016246508642722274282092643588793765624452272841115395848401844531825470162334268).isSome = true := by
  decide +kernel

theorem k2861_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2861) 3).1 2).2 1).1 2).1
      3422155497211839823772217818377258932261986487552268712446852581948).isSome = true := by
  decide +kernel

theorem k2861_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2861) 3).1 2).2 1).1 2).2
      11596939550224809250295640138151840042194553404).isSome = true := by
  decide +kernel

theorem k2861_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2861) 3).1 2).2 1).2 2).1
      855387022580967872851425635251616020592336850394174231234937207868).isSome = true := by
  decide +kernel

theorem k2861_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2861) 3).1 2).2 1).2 2).2
      11595613996214834343025952266331855541280029756).isSome = true := by
  decide +kernel

theorem k2861_8 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2861) 3).2 2).1 1).1 2).1
      3409798967518302200647329442875745780049879703100021923423650167868).isSome = true := by
  decide +kernel

theorem k2861_9 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2861) 3).2 2).1 1).1 2).2
      3414099400502427422451943465758052271019297133515527526206181667388).isSome = true := by
  decide +kernel

theorem k2861_10 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2861) 3).2 2).1 1).2 2).1
      3409274810692153435523825000726164027911418219673734357573718359100).isSome = true := by
  decide +kernel

theorem k2861_11 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2861) 3).2 2).1 1).2 2).2
      3410370179069282125347498947400705447405658253634761587335913913404).isSome = true := by
  decide +kernel

theorem k2861_12 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2861) 3).2 2).2 1).1 2).1
      3412097254564232418749515957788781057443319858895090458102989320764).isSome = true := by
  decide +kernel

theorem k2861_13 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2861) 3).2 2).2 1).1 2).2
      853213779718411173002545734684750265554928604658327075985894666812).isSome = true := by
  decide +kernel

theorem k2861_14 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2861) 3).2 2).2 1).2 3).1
      3414036234029044258704409855702432263069002889525697079770382529084).isSome = true := by
  decide +kernel

theorem k2861_15 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2861) 3).2 2).2 1).2 3).2
      852370755931915048714340167745896651039456103589093298459471887420).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 2841 2862 :=
  (Cover.dir c0).trans <|
  (Cover.dir c1).trans <|
  (Cover.dir c2).trans <|
  (Cover.one (box := dirCellBox) (n := 2859)
      (.split 3 (.split 2 (.split 3 (.leaf _ k2859_0) (.leaf _ k2859_1)) (.leaf _ k2859_2)) (.split 2 (.split 3 (.split 1 (.leaf _ k2859_3) (.leaf _ k2859_4)) (.split 1 (.leaf _ k2859_5) (.leaf _ k2859_6))) (.split 1 (.leaf _ k2859_7) (.leaf _ k2859_8))))).trans <|
  (Cover.one (box := dirCellBox) (n := 2860)
      (.split 3 (.split 2 (.split 3 (.split 1 (.leaf _ k2860_0) (.leaf _ k2860_1)) (.split 1 (.leaf _ k2860_2) (.leaf _ k2860_3))) (.split 1 (.leaf _ k2860_4) (.leaf _ k2860_5))) (.split 2 (.split 3 (.split 1 (.leaf _ k2860_6) (.leaf _ k2860_7)) (.split 1 (.leaf _ k2860_8) (.leaf _ k2860_9))) (.split 1 (.leaf _ k2860_10) (.leaf _ k2860_11))))).trans <|
  (Cover.one (box := dirCellBox) (n := 2861)
      (.split 3 (.split 2 (.split 3 (.split 2 (.leaf _ k2861_0) (.leaf _ k2861_1)) (.split 1 (.leaf _ k2861_2) (.leaf _ k2861_3))) (.split 1 (.split 2 (.leaf _ k2861_4) (.leaf _ k2861_5)) (.split 2 (.leaf _ k2861_6) (.leaf _ k2861_7)))) (.split 2 (.split 1 (.split 2 (.leaf _ k2861_8) (.leaf _ k2861_9)) (.split 2 (.leaf _ k2861_10) (.leaf _ k2861_11))) (.split 1 (.split 2 (.leaf _ k2861_12) (.leaf _ k2861_13)) (.split 3 (.leaf _ k2861_14) (.leaf _ k2861_15))))))

end C4.Cert.Dir070
