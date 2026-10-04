module

public import C4Check

public section

/-! Cells `4009 ≤ n < 4034` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir129

theorem k4009_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 4009) 2).1 3).1 2).1 1).1
      62821011008833226341940650353591906437394108986009793028151554702190469793407975316659).isSome = true := by
  decide +kernel

theorem k4009_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 4009) 2).1 3).1 2).1 1).2
      53192222766213025304153806958485307173849164471190273184418715555).isSome = true := by
  decide +kernel

theorem k4009_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 4009) 2).1 3).1 2).2 1).1
      3928395650882314467748760013826782200592483234733141604227650629207201462377307658035).isSome = true := by
  decide +kernel

theorem k4009_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 4009) 2).1 3).1 2).2 1).2
      3930396087681624781197185664415320006371414806696349590065083335048203267389212186418).isSome = true := by
  decide +kernel

theorem k4009_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4009) 2).1 3).2 2).1
      75749850750885754783680425964065531661176786003024425573780665487687690789615426750115993528225388769099248305).isSome = true := by
  decide +kernel

theorem k4009_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4009) 2).1 3).2 2).2
      75780976378606818618456216737083009685507776397044930575588615884492967818406425343339629815788652560589094065).isSome = true := by
  decide +kernel

theorem k4009_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 4009) 2).2 3).1 2).1 1).1
      15721510164179830300495533596592674135471513892757777344426278466733424768632810986291).isSome = true := by
  decide +kernel

theorem k4009_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 4009) 2).2 3).1 2).1 1).2
      245984981833200773034177092276571010502693507228756879613658442913227629399568244428).isSome = true := by
  decide +kernel

theorem k4009_8 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 4009) 2).2 3).1 2).2 1).1
      983778584173733039325513842587285075349162572063947551579176287144440548930954878668).isSome = true := by
  decide +kernel

theorem k4009_9 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 4009) 2).2 3).1 2).2 1).2
      245860905973438304764081943769885815493866442473795176811696008921817903060957486796).isSome = true := by
  decide +kernel

theorem k4009_10 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4009) 2).2 3).2 2).1
      349849317840562072403272247114057370841119638414082412418635501015799325657763718115347418994842283437311739054902614194869628081).isSome = true := by
  decide +kernel

theorem k4009_11 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4009) 2).2 3).2 2).2
      4743331144850813696376412764618747156539173142243006866145173941626201517957052248094732194204591200200342705).isSome = true := by
  decide +kernel

theorem k4010_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4010) 2).1 3).1 2).1
      6285977409360854692269541481854633671772925286319512124569818853688134891659842181711304180127736089016963870712892295173361698672846712551603633).isSome = true := by
  decide +kernel

theorem k4010_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4010) 2).1 3).1 2).2
      5454196717528554121233777341408442591429918954082433515664176712043171523366636427311404435561276632793233789320134729557996209).isSome = true := by
  decide +kernel

theorem k4010_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4010) 2).1 3).2 1).1
      21279150045247007229123198066548089760640208313933357164433342278234890719068674049645607845707429132978794848327328395386290).isSome = true := by
  decide +kernel

theorem k4010_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4010) 2).1 3).2 1).2
      21275247463694719421390300764605090364028054202862859940428025743580877199315383144713704769447156057403382588474233881451954).isSome = true := by
  decide +kernel

theorem k4010_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4010) 2).2 3).1 1).1
      87342488857200594624968635480477451904688364157228221143382741220573403571652650902635963736403603585627064104587262200469093554).isSome = true := by
  decide +kernel

theorem k4010_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4010) 2).2 3).1 1).2
      73965197233739408180588496910010118275046544305666554614571079969273523973869328985844086854748243335934642).isSome = true := by
  decide +kernel

theorem k4010_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4010) 2).2 3).2 1).1
      87202336074968973489256010786761835610307176477843123049702697844252286646497882727036354592599314352319062152328117679413392050).isSome = true := by
  decide +kernel

theorem k4010_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4010) 2).2 3).2 1).2
      4615503479495843435785358243517894487476524016751639308406686403371779695497040039953932698366084553137586).isSome = true := by
  decide +kernel

theorem k4011_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4011) 2).1 3).1 1).1
      1152162611759137844202178632015158303634311733685767419018275579919698539123625035333584216395387754208060).isSome = true := by
  decide +kernel

theorem k4011_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4011) 2).1 3).1 1).2
      60990759644056283189773108518354519522035154713646591864280887425605580308088501618).isSome = true := by
  decide +kernel

theorem k4011_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4011) 2).1 3).2 1).1
      71949412292658003353522035457099155058150816213229239356631610133502295814092339037139988062392991340348).isSome = true := by
  decide +kernel

theorem k4011_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4011) 2).1 3).2 1).2
      206457246273368736439960312532499854171965617634522255275941180).isSome = true := by
  decide +kernel

theorem k4011_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4011) 2).2 3).1 1).1
      1152649530830591166231946200679287372040962163104741295800877831934782431929390460798305131948479755573820).isSome = true := by
  decide +kernel

theorem k4011_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4011) 2).2 3).1 1).2
      72031302931818147434966149074297968413477964769553597849702658601262146197365802410453273828683331007724).isSome = true := by
  decide +kernel

theorem k4011_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4011) 2).2 3).2 1).1
      975415037811338059966253675072830401982526687832802864010161667449221533917715494124).isSome = true := by
  decide +kernel

theorem k4011_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4011) 2).2 3).2 1).2
      243830280684430085045475567548117384485133754622502906577388124986021345841623987436).isSome = true := by
  decide +kernel

theorem k4012_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4012) 2).1 3).1
      400820377043470635203385129016804437952498755996565395592576033278089152205498054617847229538213492405945813576222873556128785790778352983483047153).isSome = true := by
  decide +kernel

theorem k4012_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4012) 2).1 3).2
      25040949245613764420037879087492540567650554433817082550132480588957026269497335437580861775432570629167128585065096375121293226972258259893581298).isSome = true := by
  decide +kernel

theorem k4012_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4012) 2).2 3).1 1).1
      15594860033613259525164603003188806403271567894200375537403251789711413750434759658300).isSome = true := by
  decide +kernel

theorem k4012_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4012) 2).2 3).1 1).2
      206386758374826981739039095413336056154294475435713054976073020).isSome = true := by
  decide +kernel

theorem k4012_4 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4012) 2).2 3).2
      100177490903174729676822720657202614021642551008406843659139883029826806814447397934734657575595687292272895615774170372925925784010943061080628465).isSome = true := by
  decide +kernel

theorem k4013_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4013) 2).1 3).1
      391090091756398239948798558847998943226276077585497527841442303212196549091066965791690624547413599434764886157896811006251189720732008888759793).isSome = true := by
  decide +kernel

theorem k4013_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4013) 2).1 3).2
      4487868257482998360866383637444543095903659222153771099232235581919354233564683566217195480696818587121).isSome = true := by
  decide +kernel

theorem k4013_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4013) 2).2 3).1
      294259061674682030853572965018341217196993482651280405074111983583492257815178054986369030774022627340219633).isSome = true := by
  decide +kernel

theorem k4013_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4013) 2).2 3).2
      339167370008819880838804012320869235686591813348496248832819422447219244732186123486905787442966173005800422691616368134938044).isSome = true := by
  decide +kernel

theorem k4014_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4014) 2).1
      6252021353236538086683111955592137117862570098073985274125458826897493674486618085530236464164127568807661792499172667283550778349430878729377223).isSome = true := by
  decide +kernel

theorem k4014_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4014) 2).2 3).1
      84761630659328968111713180417215691825787993393972748297458993208417288301711340764014579993988558896193023115673273246274289).isSome = true := by
  decide +kernel

theorem k4014_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4014) 2).2 3).2
      15199152911838139521733184862070662743487003252062492199288604839077840795171605873).isSome = true := by
  decide +kernel

theorem k4015_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4015) 2).1
      15193947879320473062844715686126625430771657928143088911696787538898167652202107249).isSome = true := by
  decide +kernel

theorem k4015_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4015) 2).2
      21176021637752030008854612103748316209161590022439856608427245741442728444229483421331029958891156255425018558021861784970701).isSome = true := by
  decide +kernel

theorem c7 : allCells dirCell 4016 4034 [
    210852647753686503623496063853570957228723473160499018930354327574, 82, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0] = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 4009 4034 :=
  (Cover.one (box := dirCellBox) (n := 4009)
      (.split 2 (.split 3 (.split 2 (.split 1 (.leaf _ k4009_0) (.leaf _ k4009_1)) (.split 1 (.leaf _ k4009_2) (.leaf _ k4009_3))) (.split 2 (.leaf _ k4009_4) (.leaf _ k4009_5))) (.split 3 (.split 2 (.split 1 (.leaf _ k4009_6) (.leaf _ k4009_7)) (.split 1 (.leaf _ k4009_8) (.leaf _ k4009_9))) (.split 2 (.leaf _ k4009_10) (.leaf _ k4009_11))))).trans <|
  (Cover.one (box := dirCellBox) (n := 4010)
      (.split 2 (.split 3 (.split 2 (.leaf _ k4010_0) (.leaf _ k4010_1)) (.split 1 (.leaf _ k4010_2) (.leaf _ k4010_3))) (.split 3 (.split 1 (.leaf _ k4010_4) (.leaf _ k4010_5)) (.split 1 (.leaf _ k4010_6) (.leaf _ k4010_7))))).trans <|
  (Cover.one (box := dirCellBox) (n := 4011)
      (.split 2 (.split 3 (.split 1 (.leaf _ k4011_0) (.leaf _ k4011_1)) (.split 1 (.leaf _ k4011_2) (.leaf _ k4011_3))) (.split 3 (.split 1 (.leaf _ k4011_4) (.leaf _ k4011_5)) (.split 1 (.leaf _ k4011_6) (.leaf _ k4011_7))))).trans <|
  (Cover.one (box := dirCellBox) (n := 4012)
      (.split 2 (.split 3 (.leaf _ k4012_0) (.leaf _ k4012_1)) (.split 3 (.split 1 (.leaf _ k4012_2) (.leaf _ k4012_3)) (.leaf _ k4012_4)))).trans <|
  (Cover.one (box := dirCellBox) (n := 4013)
      (.split 2 (.split 3 (.leaf _ k4013_0) (.leaf _ k4013_1)) (.split 3 (.leaf _ k4013_2) (.leaf _ k4013_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 4014)
      (.split 2 (.leaf _ k4014_0) (.split 3 (.leaf _ k4014_1) (.leaf _ k4014_2)))).trans <|
  (Cover.one (box := dirCellBox) (n := 4015)
      (.split 2 (.leaf _ k4015_0) (.leaf _ k4015_1))).trans <|
  (Cover.dir c7)

end C4.Cert.Dir129
