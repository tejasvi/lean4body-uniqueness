module

public import C4Check

public section

/-! Cells `3343 ≤ n < 3373` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir100

theorem k3343_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3343) 3).1 1).1
      13505233919420930260358670159930440059290479195520136418678621486140).isSome = true := by
  decide +kernel

theorem k3343_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3343) 3).1 1).2
      54021078996465744859342069077120703465237710230339218025117163666492).isSome = true := by
  decide +kernel

theorem k3343_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3343) 3).2 1).1
      13500533192521315589506082941331852123638682707196972023543632378940).isSome = true := by
  decide +kernel

theorem k3343_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3343) 3).2 1).2
      13500959363789657476078605433496840610866924480677677702823642807356).isSome = true := by
  decide +kernel

theorem k3344_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3344) 3).1
      409895855616577720204625150294251231931273555719728642829167526973767956829982857381582161317654614302360325741950668774458132206961330142126755494972).isSome = true := by
  decide +kernel

theorem k3344_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 3344) 3).2
      1387754519302166499346216423050788462040595134837412531304927654285362282822363318219269521835406414177954361330754895775770819644).isSome = true := by
  decide +kernel

theorem k3345_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3345) 3).1
      3982732536603796049213806341257731801318715711471555560354103122419896146758571054021692).isSome = true := by
  decide +kernel

theorem k3345_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 3345) 3).2
      73439758298348818249736010976571503787989517137737779844834653579742724394894189002347183989811028726430780).isSome = true := by
  decide +kernel

theorem k3346_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3346) 1).1
      843013202221123444805632518345706042119985268267303754715026865212).isSome = true := by
  decide +kernel

theorem k3346_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 3346) 1).2
      18356260054967832486048234835256686601042340712187263790193458335969619022504160932772623131474895388326972).isSome = true := by
  decide +kernel

theorem c4 : allCells dirCell 3347 3348 [
    1386655938534194488709283129300445706814302022582936026515375740151165946181852616821875698289923205817695844334897762612037405361] = true := by
  decide +kernel

theorem c5 : allCells dirCell 3348 3364 [
    17918056397231604996826291064488429663969954728723190298697884360094222431459080066515468759383333730673,
    147554350805491154836, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] = true := by
  decide +kernel

theorem k3364_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3364) 3).1
      210152674126270930027992436070476288644797062871302623737786438).isSome = true := by
  decide +kernel

theorem k3364_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 3364) 3).2
      1378520324051735325260028551711502193940599954132689468815976751179043947975273324881396743557204198829141372999460993214401778).isSome = true := by
  decide +kernel

theorem k3365_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3365) 3).1
      22513654342376156638306934173533054664624740782381718422748735589801557233472489070559107890843088294750015264414791229115781859570).isSome = true := by
  decide +kernel

theorem k3365_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3365) 3).2 2).1
      3935805302471649004375396868631907731300014008343743793708588402785339222515693164337).isSome = true := by
  decide +kernel

theorem k3365_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3365) 3).2 2).2
      984418357179137373078932644720860030710708397036854288807651017218764893523808189500).isSome = true := by
  decide +kernel

theorem k3366_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3366) 2).1 3).1
      4023867433608235581728802710115844174222992854810318560241811613882811652253500441410620).isSome = true := by
  decide +kernel

theorem k3366_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3366) 2).1 3).2
      1004210765766265051844621706775895044855828047821349124626786707932659103631675672181820).isSome = true := by
  decide +kernel

theorem k3366_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3366) 2).2 3).1
      53228094539233160045025318987603335228221463655272559365622414396).isSome = true := by
  decide +kernel

theorem k3366_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3366) 2).2 3).2
      4631193325285217495975974090380187398289296423975089992495025202695318808917415704939037038903433553722428).isSome = true := by
  decide +kernel

theorem k3367_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3367) 2).1 3).1
      217421047096824343868210029252019054042710079143035809656725379431484).isSome = true := by
  decide +kernel

theorem k3367_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3367) 2).1 3).2
      868600780312687339001397274494263453361796364924013523209492000619580).isSome = true := by
  decide +kernel

theorem k3367_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3367) 2).2 3).1
      217433258419904402833325791642648447485981669522802541900646082362428).isSome = true := by
  decide +kernel

theorem k3367_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3367) 2).2 3).2
      54292016685019937994492489466542063005846289556194163620118875487292).isSome = true := by
  decide +kernel

theorem k3368_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3368) 2).1 3).1
      216919757551336336256044394379033606737088392870940948508793265339452).isSome = true := by
  decide +kernel

theorem k3368_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3368) 2).1 3).2
      3467485990554410084275604197136060437138220608557568165246952631057468).isSome = true := by
  decide +kernel

theorem k3368_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3368) 2).2 3).1
      250117458884586536196740184220893769875828807277536340472955329057556345156490734484540).isSome = true := by
  decide +kernel

theorem k3368_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3368) 2).2 3).2
      54183508771070695656526678860514820519541673030871873398576352214076).isSome = true := by
  decide +kernel

theorem k3369_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3369) 2).1 3).1
      3464880030376407936148636285414267515583003799316128438729813688728636).isSome = true := by
  decide +kernel

theorem k3369_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3369) 2).1 3).2
      3462556812554319653475934105761105419891797320944182250106361624542268).isSome = true := by
  decide +kernel

theorem k3369_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3369) 2).2 3).1
      13535640112352191449110271556471096022641155641067888160828080405564).isSome = true := by
  decide +kernel

theorem k3369_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3369) 2).2 3).2
      11732237417173884103703991658836336253550751005756).isSome = true := by
  decide +kernel

theorem k3370_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3370) 3).1 2).1
      13518592696687210653519974598283703065228705591099861740877669350460).isSome = true := by
  decide +kernel

theorem k3370_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3370) 3).1 2).2
      13519449590123719973652891390597744529201080941468941068025493601340).isSome = true := by
  decide +kernel

theorem k3370_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3370) 3).2 1).1
      46878268916750682208211297390707403601260137102396).isSome = true := by
  decide +kernel

theorem k3370_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3370) 3).2 1).2
      54050219462053306905142421013670331051684929142231249417981549296700).isSome = true := by
  decide +kernel

theorem k3371_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3371) 3).1 2).1
      46858095910910836103073660215006578096944766991420).isSome = true := by
  decide +kernel

theorem k3371_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3371) 3).1 2).2
      11715212012341386533627523437961228581616250207292).isSome = true := by
  decide +kernel

theorem k3371_2 : (checkBoxH dirMode depth (splitBox (dirCellBox 3371) 3).2
      1421955959325719485829954637168362245340600160728561312855585852262447853770339944046885561998194660906636160319193459986265153454908).isSome = true := by
  decide +kernel

theorem k3372_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3372) 3).1
      301022723841029520530307531486507654090776802013031109013973711627069101220045332391133761833784491028106691388).isSome = true := by
  decide +kernel

theorem k3372_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 3372) 3).2
      4079596657316344308612850601446423600500512932358449000238351192248261533475553243826548977).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 3343 3373 :=
  (Cover.one (box := dirCellBox) (n := 3343)
      (.split 3 (.split 1 (.leaf _ k3343_0) (.leaf _ k3343_1)) (.split 1 (.leaf _ k3343_2) (.leaf _ k3343_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 3344)
      (.split 3 (.leaf _ k3344_0) (.leaf _ k3344_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 3345)
      (.split 3 (.leaf _ k3345_0) (.leaf _ k3345_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 3346)
      (.split 1 (.leaf _ k3346_0) (.leaf _ k3346_1))).trans <|
  (Cover.dir c4).trans <|
  (Cover.dir c5).trans <|
  (Cover.one (box := dirCellBox) (n := 3364)
      (.split 3 (.leaf _ k3364_0) (.leaf _ k3364_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 3365)
      (.split 3 (.leaf _ k3365_0) (.split 2 (.leaf _ k3365_1) (.leaf _ k3365_2)))).trans <|
  (Cover.one (box := dirCellBox) (n := 3366)
      (.split 2 (.split 3 (.leaf _ k3366_0) (.leaf _ k3366_1)) (.split 3 (.leaf _ k3366_2) (.leaf _ k3366_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 3367)
      (.split 2 (.split 3 (.leaf _ k3367_0) (.leaf _ k3367_1)) (.split 3 (.leaf _ k3367_2) (.leaf _ k3367_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 3368)
      (.split 2 (.split 3 (.leaf _ k3368_0) (.leaf _ k3368_1)) (.split 3 (.leaf _ k3368_2) (.leaf _ k3368_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 3369)
      (.split 2 (.split 3 (.leaf _ k3369_0) (.leaf _ k3369_1)) (.split 3 (.leaf _ k3369_2) (.leaf _ k3369_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 3370)
      (.split 3 (.split 2 (.leaf _ k3370_0) (.leaf _ k3370_1)) (.split 1 (.leaf _ k3370_2) (.leaf _ k3370_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 3371)
      (.split 3 (.split 2 (.leaf _ k3371_0) (.leaf _ k3371_1)) (.leaf _ k3371_2))).trans <|
  (Cover.one (box := dirCellBox) (n := 3372)
      (.split 3 (.leaf _ k3372_0) (.leaf _ k3372_1)))

end C4.Cert.Dir100
