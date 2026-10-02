module

public import C4Check

public section

/-! Cells `3979 ≤ n < 3984` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir133

theorem k3979_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3979) 2).1 3).1 2).1
      255385608493707995831270972738483728918341471714967057175356293362933040609313540699335).isSome = true := by
  decide +kernel

theorem k3979_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3979) 2).1 3).1 2).2
      16021766910979761800959660424781612592396716994900097357086935496231863257832795088073).isSome = true := by
  decide +kernel

theorem k3979_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3979) 2).1 3).2 2).1
      61982640899803406222959485903870376670917607809184803138886764987371602357479824817).isSome = true := by
  decide +kernel

theorem k3979_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3979) 2).1 3).2 2).2
      3971883396358037977262794108996241292680522264618144654503935442333841543132439999153).isSome = true := by
  decide +kernel

theorem k3979_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3979) 2).2 3).1 2).1
      4001678027104721141587116972088451350913328187589568634234282120378830374211842938675).isSome = true := by
  decide +kernel

theorem k3979_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3979) 2).2 3).1 2).2
      4013311611272298015772962747065680664340374858599152652555571809229441707894715078449).isSome = true := by
  decide +kernel

theorem k3979_6 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3979) 2).2 3).2
      104764253381617959847812696961089077437400392618822949739942714782729136019959293669557520696584869897749320656297510370085456724882060918780878740678).isSome = true := by
  decide +kernel

theorem k3980_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3980) 2).1 3).1 2).1
      61634937355422439955365397000453200989561612512739816316259505485175064318046377413).isSome = true := by
  decide +kernel

theorem k3980_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3980) 2).1 3).1 2).2
      18210565687543547046587787764351937589735287233259435955141450793503059287340613941207928275125775850929).isSome = true := by
  decide +kernel

theorem k3980_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3980) 2).1 3).2
      21410405190689562716236427743675911753176451654103156856257113277455973805115737134224625225662690198831692310153954452706758).isSome = true := by
  decide +kernel

theorem k3980_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3980) 2).2 3).1 2).1
      3952519809129528305176065448405275692369495027096970094358534752775263757951544423089).isSome = true := by
  decide +kernel

theorem k3980_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3980) 2).2 3).1 2).2
      988996216422600479273953963145103373831874708181676092375731831728011672799142960305).isSome = true := by
  decide +kernel

theorem k3980_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3980) 2).2 3).2 2).1
      18150718284464405770233558388775821470543576855564702414597348793381611976880105749399500847968693607857).isSome = true := by
  decide +kernel

theorem k3980_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3980) 2).2 3).2 2).2
      984684038959492431386832263303841855807454136559202924740420821502088517010469641393).isSome = true := by
  decide +kernel

theorem k3981_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3981) 2).1 3).1
      21349410500917758485352296705291351776203317205542195772391582214031861094647933912311631070299602859573031361423059661051334).isSome = true := by
  decide +kernel

theorem k3981_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3981) 2).1 3).2
      72179440307582494836874316474377340627138845019698668625386129143438289394106997857295719999344234820849).isSome = true := by
  decide +kernel

theorem k3981_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3981) 2).2 3).1
      25243377551753696912413451880114154347340703167792209706977177474383581752467699448490255762951493740939451317989650187279762899221111610867439046).isSome = true := by
  decide +kernel

theorem k3981_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3981) 2).2 3).2
      85309689988148281230261790526647294046828272869302939542134729935994117111198779986561396760327061830441934821418222660187377).isSome = true := by
  decide +kernel

theorem k3982_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3982) 2).1
      7404392618846195827800993609843491334212702254325017069338586359885513385427548151815257986929116600063385847173967556297705929561195539533884047208208091126137382347).isSome = true := by
  decide +kernel

theorem k3982_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3982) 2).2 3).1
      72126805882472483074561064749822955159856256096604831413898020913214501717338900026727969308153231537393).isSome = true := by
  decide +kernel

theorem k3982_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3982) 2).2 3).2
      72037510610674577873782595185441506592884117904895978091334848784810872693406506032984596226005887710449).isSome = true := by
  decide +kernel

theorem k3983_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3983) 2).1
      21220093983396764496716873667584388220455611316148016288172990120302337545175974758101293414123785963571387275055707103880647).isSome = true := by
  decide +kernel

theorem k3983_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 3983) 2).2
      462348853647954106539356700124546182646784094410359163854414179823823968013573817756783557069891484100110694321993863874414066735275682201812928711108238491136447947).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 3979 3984 :=
  (Cover.one (box := dirCellBox) (n := 3979)
      (.split 2 (.split 3 (.split 2 (.leaf _ k3979_0) (.leaf _ k3979_1)) (.split 2 (.leaf _ k3979_2) (.leaf _ k3979_3))) (.split 3 (.split 2 (.leaf _ k3979_4) (.leaf _ k3979_5)) (.leaf _ k3979_6)))).trans <|
  (Cover.one (box := dirCellBox) (n := 3980)
      (.split 2 (.split 3 (.split 2 (.leaf _ k3980_0) (.leaf _ k3980_1)) (.leaf _ k3980_2)) (.split 3 (.split 2 (.leaf _ k3980_3) (.leaf _ k3980_4)) (.split 2 (.leaf _ k3980_5) (.leaf _ k3980_6))))).trans <|
  (Cover.one (box := dirCellBox) (n := 3981)
      (.split 2 (.split 3 (.leaf _ k3981_0) (.leaf _ k3981_1)) (.split 3 (.leaf _ k3981_2) (.leaf _ k3981_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 3982)
      (.split 2 (.leaf _ k3982_0) (.split 3 (.leaf _ k3982_1) (.leaf _ k3982_2)))).trans <|
  (Cover.one (box := dirCellBox) (n := 3983)
      (.split 2 (.leaf _ k3983_0) (.leaf _ k3983_1)))

end C4.Cert.Dir133
