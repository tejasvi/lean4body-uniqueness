module

public import C4Check

public section

/-! Cells `4186 ≤ n < 4241` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir137

theorem k4186_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4186) 1).1
      843063019262452401819738918799159074742003160234909910411081663292).isSome = true := by
  decide +kernel

theorem k4186_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4186) 1).2
      248837942750825922474443128138061678974059382999216490573820866058276231713148393734972).isSome = true := by
  decide +kernel

theorem k4187_0 : (checkBoxH dirMode depth (dirCellBox 4187)
      5547850671435032555505477455712991846558161647033897500459863699305577334755803391570115064945999041440094496579594692031269511996).isSome = true := by
  decide +kernel

theorem c2 : allCells dirCell 4188 4189 [
    18793635073167623620408563783458078215069474678497205609045065575536378663541208489271245105345858525341272305] = true := by
  decide +kernel

theorem c3 : allCells dirCell 4189 4190 [
    4587559854167472474712793967817723546101088758921487958151729107927093823391017114913110319815568295537852] = true := by
  decide +kernel

theorem c4 : allCells dirCell 4190 4205 [
    51423755014785232668885472146586809184556743553370760001085201, 147561424651052004964, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0,
    987135428956478247712630368849303355358706514129244277866205236280464212394228141319] = true := by
  decide +kernel

theorem c5 : allCells dirCell 4205 4206 [
    414302335165868655341602927614480947042077509938939276565272313910778621811344369008756732459290332346132866352297631390850574320425965625642292960459] = true := by
  decide +kernel

theorem k4206_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4206) 3).1
      4021277416536150332308051100328286406610745853197906871803491676129079259553396692470578).isSome = true := by
  decide +kernel

theorem k4206_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4206) 3).2
      1003812763344676732245857987509058737947117054064311528156304621303264448302834583171890).isSome = true := by
  decide +kernel

theorem k4207_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4207) 2).1
      64091014278481219661684407277448769488261488154106921251762641641892240447081146108719923).isSome = true := by
  decide +kernel

theorem k4207_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4207) 2).2
      4005689444723706700179572269100213260202941837635146342749146462800595363325026191373107).isSome = true := by
  decide +kernel

theorem k4208_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4208) 2).1
      18882327171416649027246066457387783966818525250858658388776060685991101292504514794863100740579889121276572467).isSome = true := by
  decide +kernel

theorem k4208_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4208) 2).2
      63977512834669101084172901507001353462448742286027136402235921384593333290934590169002803).isSome = true := by
  decide +kernel

theorem k4209_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4209) 2).1
      4827464856115800594552812007884158034715950934087721048536495792595326728758568617519027532510731099683555053363).isSome = true := by
  decide +kernel

theorem k4209_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4209) 2).2
      15973123420177087137647910927634792346220086617997914692520149499498518784971676290763571).isSome = true := by
  decide +kernel

theorem k4210_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4210) 2).1
      65357445408456426470119890776745922481267940126324598492888705415620813911182488712137322739).isSome = true := by
  decide +kernel

theorem k4210_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4210) 2).2
      249485068378887161374342820627761306690010049777173622752146360736144374289857674361916).isSome = true := by
  decide +kernel

theorem k4211_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4211) 1).1
      3988980531379832785692874486424862979574903267790002701675074027058517328046206085446716).isSome = true := by
  decide +kernel

theorem k4211_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4211) 1).2
      3987019648855216269509843714528327551428688344832418599433636282842370482258995097320508).isSome = true := by
  decide +kernel

theorem k4212_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4212) 2).1
      18375585961586398388922813310091449171857258522348437891502942237874306464186977874513903474260198337330236).isSome = true := by
  decide +kernel

theorem k4212_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4212) 2).2
      13500607946534483417618727642095688309191547352115774693999309012028).isSome = true := by
  decide +kernel

theorem k4213_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4213) 1).1
      210845929980275545741006083617023518732891571163152874743526781500).isSome = true := by
  decide +kernel

theorem k4213_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4213) 1).2
      45720655101310891936251712295929538017500511292).isSome = true := by
  decide +kernel

theorem c14 : allCells dirCell 4214 4215 [
    75208444498702235858880947854648043723455984551325578352193663582317419632668214243502227805129360335444058940] = true := by
  decide +kernel

theorem c15 : allCells dirCell 4215 4216 [
    86687332562921689607232013700669997689570021386493190842046281627714212477009008770464672437740791242732715594341953668600783676] = true := by
  decide +kernel

theorem c16 : allCells dirCell 4216 4217 [
    73412434683878474037960572487815868597105821620881687658155906643707201180759665596053539396351662523114300] = true := by
  decide +kernel

theorem c17 : allCells dirCell 4217 4218 [
    71682649305826137518140742303755924411283750429942272768797168815530174935067151665749633390470933943729] = true := by
  decide +kernel

theorem c18 : allCells dirCell 4218 4233 [
    51423693427627218824714711083460802483773958564249420504097297, 147560918669563090820, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 38389322866802185192499] = true := by
  decide +kernel

theorem c19 : allCells dirCell 4233 4234 [
    4749786959731698385739935382628286194906260045437836329911919400398174573624377686889331657298413536172573899] = true := by
  decide +kernel

theorem c20 : allCells dirCell 4234 4235 [
    310426756149726503162526445992432050410876567090010909744367803235103795379664051470794896456697273188808035159246] = true := by
  decide +kernel

theorem k4235_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4235) 2).1
      1001416452542084760293066042911843357901475751260913108868189189571401645786432355005235).isSome = true := by
  decide +kernel

theorem k4235_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4235) 2).2
      62587209701467190315244555776514649674792234606810469888091337682742214031884443512012).isSome = true := by
  decide +kernel

theorem k4236_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4236) 2).1
      999665377872490070705791668003488443192485188605670442285921385302393353150802076463923).isSome = true := by
  decide +kernel

theorem k4236_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4236) 2).2
      3905989244765669967867091040612817737762619556957564376973482827306077949344326480588).isSome = true := by
  decide +kernel

theorem k4237_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4237) 2).1
      54137099948408072087338938827013442066373162196399495838279910861884).isSome = true := by
  decide +kernel

theorem k4237_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4237) 2).2
      845900931873677989029320992666978173541771956112562036467063270092).isSome = true := by
  decide +kernel

theorem k4238_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4238) 2).1
      249400418456291993906256428080495992868265339464955507596623767727973912014233460423740).isSome = true := by
  decide +kernel

theorem k4238_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4238) 2).2
      52813674103648239760679879127135230535544902470379533078139612220).isSome = true := by
  decide +kernel

theorem k4239_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4239) 2).1
      15575093687162617403740370052605448759984966392138789398410812683759857706172063104060).isSome = true := by
  decide +kernel

theorem k4239_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4239) 2).2
      211084835295400025777067404633819859964859347184684752683712953404).isSome = true := by
  decide +kernel

theorem c26 : allCells dirCell 4240 4241 [
    22216722637384153362459001339128571261091871261494006230706271315319884507757379753007627589907766562134555190341732412018206830833] = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 4186 4241 :=
  (Cover.one (box := dirCellBox) (n := 4186)
      (.split 1 (.leaf _ k4186_0) (.leaf _ k4186_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 4187)
      (.leaf _ k4187_0)).trans <|
  (Cover.dir c2).trans <|
  (Cover.dir c3).trans <|
  (Cover.dir c4).trans <|
  (Cover.dir c5).trans <|
  (Cover.one (box := dirCellBox) (n := 4206)
      (.split 3 (.leaf _ k4206_0) (.leaf _ k4206_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 4207)
      (.split 2 (.leaf _ k4207_0) (.leaf _ k4207_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 4208)
      (.split 2 (.leaf _ k4208_0) (.leaf _ k4208_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 4209)
      (.split 2 (.leaf _ k4209_0) (.leaf _ k4209_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 4210)
      (.split 2 (.leaf _ k4210_0) (.leaf _ k4210_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 4211)
      (.split 1 (.leaf _ k4211_0) (.leaf _ k4211_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 4212)
      (.split 2 (.leaf _ k4212_0) (.leaf _ k4212_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 4213)
      (.split 1 (.leaf _ k4213_0) (.leaf _ k4213_1))).trans <|
  (Cover.dir c14).trans <|
  (Cover.dir c15).trans <|
  (Cover.dir c16).trans <|
  (Cover.dir c17).trans <|
  (Cover.dir c18).trans <|
  (Cover.dir c19).trans <|
  (Cover.dir c20).trans <|
  (Cover.one (box := dirCellBox) (n := 4235)
      (.split 2 (.leaf _ k4235_0) (.leaf _ k4235_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 4236)
      (.split 2 (.leaf _ k4236_0) (.leaf _ k4236_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 4237)
      (.split 2 (.leaf _ k4237_0) (.leaf _ k4237_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 4238)
      (.split 2 (.leaf _ k4238_0) (.leaf _ k4238_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 4239)
      (.split 2 (.leaf _ k4239_0) (.leaf _ k4239_1))).trans <|
  (Cover.dir c26)

end C4.Cert.Dir137
