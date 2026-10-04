module

public import C4Check

public section

/-! Cells `4073 ≤ n < 4098` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir133

theorem k4073_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4073) 2).1
      338676943640166936096693718871119226055419355772952099131465462406789891772107661434523977787361951945201054688026007360074995).isSome = true := by
  decide +kernel

theorem k4073_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4073) 2).2
      1354846880664541334598968656582180272042224514176950815655922511297428901564310369397069485472521882660466724860430165696960753).isSome = true := by
  decide +kernel

theorem k4074_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4074) 2).1
      242952509027461077112299686723805469762813072009949410200916043483448042118249010417).isSome = true := by
  decide +kernel

theorem k4074_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4074) 2).2
      5291191544724052659212789167972542086795761130306506545825089975267790090778018466324802408810254022581039605063746800047932).isSome = true := by
  decide +kernel

theorem c2 : allCells dirCell 4075 4076 [
    1354620118021228880917787558065234454579160294507084156350554712518062607714009716785949681980624827236282195328998051667436998] = true := by
  decide +kernel

theorem c3 : allCells dirCell 4076 4091 [
    17921525932696138428599833187416581840878570649591627196218731984438323487588469651736214858262707146098,
    44605752930033081747738409094145334051803161, 590281876934226030417, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 1] = true := by
  decide +kernel

theorem k4091_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4091) 3).1
      25793326652235160974428033732860811603873150234769075325113982304104665182857230228255483962775663301416865358480893002419246228779007000449844683).isSome = true := by
  decide +kernel

theorem k4091_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4091) 3).2 2).1
      254778649289210008044616247616524882562507304745091401778821972932401273779507247175473).isSome = true := by
  decide +kernel

theorem k4091_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4091) 3).2 2).2
      3989893187718594127672489959803926862488635261996891169426374386140432388231060412210).isSome = true := by
  decide +kernel

theorem k4092_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4092) 3).1 2).1
      4796649895760909267725364910944131914471316688340571526718722759885383012152219920894448353391395450922684209).isSome = true := by
  decide +kernel

theorem k4092_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4092) 3).1 2).2
      18745667400112435638983532410776718941709590243016035228022027996015905596699690215209769881734835142022963).isSome = true := by
  decide +kernel

theorem k4092_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4092) 3).2 2).1 1).1
      3429911896839083711300397445440436265205752319598888154238378466866).isSome = true := by
  decide +kernel

theorem k4092_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4092) 3).2 2).1 1).2
      214303145077470029578572289738621012320555050709489808282851199692).isSome = true := by
  decide +kernel

theorem k4092_4 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4092) 3).2 2).2
      76546526101105046262234815805144766729487004570521066760764178725912391367678771750952494294128894087188044593).isSome = true := by
  decide +kernel

theorem k4093_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4093) 2).1 3).1 1).1
      855408286656013783168955273193357771501378234632610411447771409100).isSome = true := by
  decide +kernel

theorem k4093_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4093) 2).1 3).1 1).2
      53424348394704354622402157305916034167505152481452809704616358604).isSome = true := by
  decide +kernel

theorem k4093_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4093) 2).1 3).2 1).1
      53318418673960730318825982981338911397309544880131356216451789516).isSome = true := by
  decide +kernel

theorem k4093_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4093) 2).1 3).2 1).2
      213227561929584039899455287500488206267585065851973992307131609804).isSome = true := by
  decide +kernel

theorem k4093_4 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4093) 2).2 3).1
      351872564525166918418784779601126960588444451781253681706883541579506722210579163151633641229638878367608383584879836522368850737).isSome = true := by
  decide +kernel

theorem k4093_5 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4093) 2).2 3).2
      5615265895074645346660868517138079652626658025206275152020640531664700019186047949001410909789983299834080898001916241867504601905).isSome = true := by
  decide +kernel

theorem k4094_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4094) 2).1 3).1 1).1
      212803153938538480954559067755438940264637473552847464778318672588).isSome = true := by
  decide +kernel

theorem k4094_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4094) 2).1 3).1 1).2
      53190558696828911736636069681571140746679657995300455132273439436).isSome = true := by
  decide +kernel

theorem k4094_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4094) 2).1 3).2 1).1
      212416644243466218618166128543351597883423945506744776726605712076).isSome = true := by
  decide +kernel

theorem k4094_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4094) 2).1 3).2 1).2
      849528795767742586308785844348174982504720709193235915550136150732).isSome = true := by
  decide +kernel

theorem k4094_4 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4094) 2).2 3).1
      5603267039779524898842357609511569052856372866061997218571496104785008739141421882711795091261151492430372793490071222569357790001).isSome = true := by
  decide +kernel

theorem k4094_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4094) 2).2 3).2 1).1
      53120089721445136950859767536256962283528917479664275870099829452).isSome = true := by
  decide +kernel

theorem k4094_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4094) 2).2 3).2 1).2
      53111597219636714939745393385270980110942770282391955703117247180).isSome = true := by
  decide +kernel

theorem k4095_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4095) 2).1 3).1 1).1
      212112491888592471845117301225768750765233979328816047539665492684).isSome = true := by
  decide +kernel

theorem k4095_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4095) 2).1 3).1 1).2
      11772796755944096907184653699723090480845343304498).isSome = true := by
  decide +kernel

theorem k4095_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4095) 2).1 3).2 1).1
      13240903342312056259394955017044779613057777237789251526813260492).isSome = true := by
  decide +kernel

theorem k4095_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4095) 2).1 3).2 1).2
      13239442291713606275063681720951770547892737409402065229677304524).isSome = true := by
  decide +kernel

theorem k4095_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4095) 2).2 3).1 1).1
      53040689288473348431195724616171013074537103204236712946004521676).isSome = true := by
  decide +kernel

theorem k4095_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4095) 2).2 3).1 1).2
      53033794922054830589949784905966356739557212553703173732128125644).isSome = true := by
  decide +kernel

theorem k4095_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4095) 2).2 3).2 1).1
      45948619318911173482982130872091342898648828620).isSome = true := by
  decide +kernel

theorem k4095_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4095) 2).2 3).2 1).2
      244297190121390573108936238805287943698745896977287689008115880914295613632766408396).isSome = true := by
  decide +kernel

theorem k4096_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4096) 2).1 3).1
      1023378595297358634281529403510890825328582960878534404849136934854408912680980996562578225).isSome = true := by
  decide +kernel

theorem k4096_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4096) 2).1 3).2
      255640208653345992557616453063296387729181330547071383582025499050549922895826954879611121).isSome = true := by
  decide +kernel

theorem k4096_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4096) 2).2 3).1
      4720678716492764297719923985100036881504495304517733826378740763470916626996225254919865933878694773958089521).isSome = true := by
  decide +kernel

theorem k4096_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4096) 2).2 3).2
      255697098474014539468295338168973848329280954356873871950740740379386216694287253264522033).isSome = true := by
  decide +kernel

theorem k4097_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4097) 2).1 3).1
      15967870735281612508913282784512850004893333496911683743855817287049917025688481265007676).isSome = true := by
  decide +kernel

theorem k4097_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4097) 2).1 3).2
      73600875937154252316175852825598828448611958695317392240149870392377711464078290418160216892122787366157372).isSome = true := by
  decide +kernel

theorem k4097_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4097) 2).2 3).1
      998132460129851190534231889655922807846389733274516436132651103842314788107334397565745).isSome = true := by
  decide +kernel

theorem k4097_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4097) 2).2 3).2
      3990480731833119110295295164378704444224445949956043991664053979719652261511767095295036).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 4073 4098 :=
  (Cover.one (box := dirCellBox) (n := 4073)
      (.split 2 (.leaf _ k4073_0) (.leaf _ k4073_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 4074)
      (.split 2 (.leaf _ k4074_0) (.leaf _ k4074_1))).trans <|
  (Cover.dir c2).trans <|
  (Cover.dir c3).trans <|
  (Cover.one (box := dirCellBox) (n := 4091)
      (.split 3 (.leaf _ k4091_0) (.split 2 (.leaf _ k4091_1) (.leaf _ k4091_2)))).trans <|
  (Cover.one (box := dirCellBox) (n := 4092)
      (.split 3 (.split 2 (.leaf _ k4092_0) (.leaf _ k4092_1)) (.split 2 (.split 1 (.leaf _ k4092_2) (.leaf _ k4092_3)) (.leaf _ k4092_4)))).trans <|
  (Cover.one (box := dirCellBox) (n := 4093)
      (.split 2 (.split 3 (.split 1 (.leaf _ k4093_0) (.leaf _ k4093_1)) (.split 1 (.leaf _ k4093_2) (.leaf _ k4093_3))) (.split 3 (.leaf _ k4093_4) (.leaf _ k4093_5)))).trans <|
  (Cover.one (box := dirCellBox) (n := 4094)
      (.split 2 (.split 3 (.split 1 (.leaf _ k4094_0) (.leaf _ k4094_1)) (.split 1 (.leaf _ k4094_2) (.leaf _ k4094_3))) (.split 3 (.leaf _ k4094_4) (.split 1 (.leaf _ k4094_5) (.leaf _ k4094_6))))).trans <|
  (Cover.one (box := dirCellBox) (n := 4095)
      (.split 2 (.split 3 (.split 1 (.leaf _ k4095_0) (.leaf _ k4095_1)) (.split 1 (.leaf _ k4095_2) (.leaf _ k4095_3))) (.split 3 (.split 1 (.leaf _ k4095_4) (.leaf _ k4095_5)) (.split 1 (.leaf _ k4095_6) (.leaf _ k4095_7))))).trans <|
  (Cover.one (box := dirCellBox) (n := 4096)
      (.split 2 (.split 3 (.leaf _ k4096_0) (.leaf _ k4096_1)) (.split 3 (.leaf _ k4096_2) (.leaf _ k4096_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 4097)
      (.split 2 (.split 3 (.leaf _ k4097_0) (.leaf _ k4097_1)) (.split 3 (.leaf _ k4097_2) (.leaf _ k4097_3))))

end C4.Cert.Dir133
