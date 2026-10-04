module

public import C4Check

public section

/-! Cells `3316 ≤ n < 3343` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir099

theorem k3316_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3316) 3).1 2).1
      210959927051555836633562456347037526259257887271909538167260593212).isSome = true := by
  decide +kernel

theorem k3316_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3316) 3).1 2).2
      62237392391713430747242864113376325803621250463090655915005383202800382511272034712636).isSome = true := by
  decide +kernel

theorem k3316_2 : (checkBoxH dirMode depth (splitBox (dirCellBox 3316) 3).2
      88808813725210069175184940081264505950410585513598178030205441270603298833801148518876844356040275170916330454334409951208120054002).isSome = true := by
  decide +kernel

theorem k3317_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3317) 3).1
      300845157577645353708683019004895465810612050852057963502861802071307202857749306605488464348439662276291768561).isSome = true := by
  decide +kernel

theorem k3317_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 3317) 3).2
      73434884522721331784597769200230406662668510382370648160526332957958646508541355382096508809303801359645756).isSome = true := by
  decide +kernel

theorem k3318_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3318) 3).1
      73424394810003967522033877997763386989592710736257233855860316516712961245182567335005843126673949754342460).isSome = true := by
  decide +kernel

theorem k3318_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 3318) 3).2
      4588541395742487298170808252163918474450529315409159455773026545953721412029194732954103840345630094867516).isSome = true := by
  decide +kernel

theorem c3 : allCells dirCell 3319 3320 [
    88743055637197348114307815843794225217616819499125921050244304083039773757441738472341079693890632160390838785825933255309321723085] = true := by
  decide +kernel

theorem c4 : allCells dirCell 3320 3335 [
    3885363487576962554942602189161528089580429856223325249979404810434065141604539185521,
    147555414445509167204, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] = true := by
  decide +kernel

theorem c5 : allCells dirCell 3335 3336 [
    54163494606823631769045910546749790933457442144934862952755770467] = true := by
  decide +kernel

theorem k3336_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3336) 3).1
      25534643587303931849592187695013447388546281073118909743424750815937240204507697551436236378131098988864167569814936391747031107207490180030113222).isSome = true := by
  decide +kernel

theorem k3336_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3336) 3).2 2).1
      1169137001699367386536425940923655197522955207897447297010785347324293934838904635255654994831647169797553).isSome = true := by
  decide +kernel

theorem k3336_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3336) 3).2 2).2
      291995793786077775747767028114799235880418353103976914029446992335415408727760125414197160782638974751548).isSome = true := by
  decide +kernel

theorem k3337_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3337) 3).1 2).1
      5503121171118962424143794564898663600965788024623722739848338397085400140120704105584649656649440251512637815155659781138906289).isSome = true := by
  decide +kernel

theorem k3337_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3337) 3).1 2).2
      15776993246431202035786925294146086683730646589656560218941530252227414849467509988529).isSome = true := by
  decide +kernel

theorem k3337_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3337) 3).2 2).1
      4760209130693594525964131027417445701072989167806345852179682430954042087633420960993716148554082728142041329).isSome = true := by
  decide +kernel

theorem k3337_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3337) 3).2 2).2
      258074978318163712156705176784060846728065229997461926924929884547470771075654846102434034).isSome = true := by
  decide +kernel

theorem k3338_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3338) 2).1 3).1
      257485007774563512530095307360801161824436629469236428899768453421045985272334994892976369).isSome = true := by
  decide +kernel

theorem k3338_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3338) 2).1 3).2
      1028038078573098042783584327626782085519304531819665740182765292831034573710159619917713201).isSome = true := by
  decide +kernel

theorem k3338_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3338) 2).2 3).1
      4023767213237991932700495827125666411244608836994794747788130291822327601723234104163388).isSome = true := by
  decide +kernel

theorem k3338_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3338) 2).2 3).2
      4016568356059595241100004086251095186787767569746739901766973701339390960694704547249212).isSome = true := by
  decide +kernel

theorem k3339_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3339) 2).1 3).1
      4733798397528531244070170841667341165721130521846216965354809465234973496400521914823995081113906499433163569).isSome = true := by
  decide +kernel

theorem k3339_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3339) 2).1 3).2
      5581945211448344095015371670287479010268620131647456826175817984435579299751116123654185307489470019474824686647032596254044142652).isSome = true := by
  decide +kernel

theorem k3339_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3339) 2).2 3).1
      16041545362175794862488239671809922390490074895610369369554158051932175371168567076952881).isSome = true := by
  decide +kernel

theorem k3339_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3339) 2).2 3).2
      4728756622751340482786633649129508630172198162340097175519142162294491039274013424746848225372016863419251772).isSome = true := by
  decide +kernel

theorem k3340_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3340) 2).1 3).1
      302263182109281047543322409382738055309850192008581636688032473653840792335649905083172278570569004035609934908).isSome = true := by
  decide +kernel

theorem k3340_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3340) 2).1 3).2
      75499404313746540845902392855991156114761266955130762265991957223360967007359372765323909659879453307663760444).isSome = true := by
  decide +kernel

theorem k3340_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3340) 2).2 3).1
      75577704635079776898934849464123343356925109243489406308955060476863042414408692905985488917811918972195322940).isSome = true := by
  decide +kernel

theorem k3340_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3340) 2).2 3).2
      4093184928071208881180150639713196411260653337252065708097076266131752388194992745253321788).isSome = true := by
  decide +kernel

theorem k3341_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3341) 2).1 3).1
      18860292728862565498226325684661946793322074757719347319130965944873310743895298836198147564776934901662563388).isSome = true := by
  decide +kernel

theorem k3341_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3341) 2).1 3).2
      18848839111700129713548354364626781512400424734687039071426637794461450923692895102624739724184071330153053244).isSome = true := by
  decide +kernel

theorem k3341_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3341) 2).2 3).1
      1022532295498679094824222889457483646713444158833736616150386959160201535434758487762680892).isSome = true := by
  decide +kernel

theorem k3341_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3341) 2).2 3).2
      13848725309503183991034508764974285782387564571446120954055057837014076).isSome = true := by
  decide +kernel

theorem k3342_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3342) 3).1 2).1
      63826214600032644080045994070511790223204956332917111286211360673218977922106505944579132).isSome = true := by
  decide +kernel

theorem k3342_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3342) 3).1 2).2
      54068458309292761236945668098390491701786143016666336026613499182140).isSome = true := by
  decide +kernel

theorem k3342_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3342) 3).2 2).1
      216151009137260689332237004154683837583286408721143947203370115873852).isSome = true := by
  decide +kernel

theorem k3342_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3342) 3).2 2).2
      216172784654271810287639852381868272654010016067549107376005646597180).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 3316 3343 :=
  (Cover.one (box := dirCellBox) (n := 3316)
      (.split 3 (.split 2 (.leaf _ k3316_0) (.leaf _ k3316_1)) (.leaf _ k3316_2))).trans <|
  (Cover.one (box := dirCellBox) (n := 3317)
      (.split 3 (.leaf _ k3317_0) (.leaf _ k3317_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 3318)
      (.split 3 (.leaf _ k3318_0) (.leaf _ k3318_1))).trans <|
  (Cover.dir c3).trans <|
  (Cover.dir c4).trans <|
  (Cover.dir c5).trans <|
  (Cover.one (box := dirCellBox) (n := 3336)
      (.split 3 (.leaf _ k3336_0) (.split 2 (.leaf _ k3336_1) (.leaf _ k3336_2)))).trans <|
  (Cover.one (box := dirCellBox) (n := 3337)
      (.split 3 (.split 2 (.leaf _ k3337_0) (.leaf _ k3337_1)) (.split 2 (.leaf _ k3337_2) (.leaf _ k3337_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 3338)
      (.split 2 (.split 3 (.leaf _ k3338_0) (.leaf _ k3338_1)) (.split 3 (.leaf _ k3338_2) (.leaf _ k3338_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 3339)
      (.split 2 (.split 3 (.leaf _ k3339_0) (.leaf _ k3339_1)) (.split 3 (.leaf _ k3339_2) (.leaf _ k3339_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 3340)
      (.split 2 (.split 3 (.leaf _ k3340_0) (.leaf _ k3340_1)) (.split 3 (.leaf _ k3340_2) (.leaf _ k3340_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 3341)
      (.split 2 (.split 3 (.leaf _ k3341_0) (.leaf _ k3341_1)) (.split 3 (.leaf _ k3341_2) (.leaf _ k3341_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 3342)
      (.split 3 (.split 2 (.leaf _ k3342_0) (.leaf _ k3342_1)) (.split 2 (.leaf _ k3342_2) (.leaf _ k3342_3))))

end C4.Cert.Dir099
