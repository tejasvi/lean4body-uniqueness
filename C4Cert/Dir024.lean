module

public import C4Check

public section

/-! Cells `2022 ≤ n < 2047` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir024

theorem k2022_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2022) 3).1 2).1 3).1 1).1
      73955002457822633949821554518386606110432583148323373541718840793103594657742049062009408485858089037820833).isSome = true := by
  decide +kernel

theorem k2022_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2022) 3).1 2).1 3).1 1).2
      16046232803723689028152920452339502736648708106004005701298197075593686361516792336468785).isSome = true := by
  decide +kernel

theorem k2022_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2022) 3).1 2).1 3).2 1).1
      1154565896743688418190720360444179896595226940753958723559441723251499192903550028741457417390061101469388).isSome = true := by
  decide +kernel

theorem k2022_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2022) 3).1 2).1 3).2 1).2
      1001151277999449651875441481409580243247773264040571698309781349812734900826343939076913).isSome = true := by
  decide +kernel

theorem k2022_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2022) 3).1 2).2 3).1 1).1
      250795241393653383049821160476354199905682919946173648780967009637528544352254525283122).isSome = true := by
  decide +kernel

theorem k2022_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2022) 3).1 2).2 3).1 1).2
      62753636628933015420680874125075795231305110835520819825501324810993689399685933773772).isSome = true := by
  decide +kernel

theorem k2022_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2022) 3).1 2).2 3).2 1).1
      15657212206490751534588073239094502798038337352873890031201096540846644484183022325452).isSome = true := by
  decide +kernel

theorem k2022_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2022) 3).1 2).2 3).2 1).2
      3914242747464706137082545133802389178100227493073069608448401350318848939998725003980).isSome = true := by
  decide +kernel

theorem k2022_8 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2022) 3).2 2).1 1).1 3).1
      1000520943381825136046414677423153423431655226196817036938232678012087113069179271476017).isSome = true := by
  decide +kernel

theorem k2022_9 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2022) 3).2 2).1 1).1 3).2
      3906183319520613451053599739246809393245953556252259980031551509423634748966404747980).isSome = true := by
  decide +kernel

theorem k2022_10 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2022) 3).2 2).1 1).2 3).1
      3908445924084768935775199811339637757099868476039230240291836184572133925708056883916).isSome = true := by
  decide +kernel

theorem k2022_11 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2022) 3).2 2).1 1).2 3).2
      52935734308172084846332365406700731501717021718376849048332530380).isSome = true := by
  decide +kernel

theorem k2022_12 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2022) 3).2 2).2 1).1 3).1
      3911320080952247627352223959204233019229439968883481088263655366543472032224783096524).isSome = true := by
  decide +kernel

theorem k2022_13 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2022) 3).2 2).2 1).1 3).2
      211854962607958007553426586076176792477028197579303496187343522508).isSome = true := by
  decide +kernel

theorem k2022_14 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2022) 3).2 2).2 1).2 3).1
      3911169372120624473510089633240720105471651168189112271398265328916332966610447358668).isSome = true := by
  decide +kernel

theorem k2022_15 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2022) 3).2 2).2 1).2 3).2
      52963347744656721698431946355771561098303839972576367304507781836).isSome = true := by
  decide +kernel

theorem k2023_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2023) 3).1 2).1 1).1
      25684062986001342692277322731048239900433397164121850677670074234017501513162693546863998966815871610092844344220069275886902975284909585916491068211).isSome = true := by
  decide +kernel

theorem k2023_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2023) 3).1 2).1 1).2
      5446302171897849239744847531644463776780065323325025537140401019457330224979873406185823520757414750241636710975893938796616498).isSome = true := by
  decide +kernel

theorem k2023_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2023) 3).1 2).2 1).1
      5571677158173277075882495294018593994405669860712823045041701651735716343795662487357333906755344717821328131049149706129936730931).isSome = true := by
  decide +kernel

theorem k2023_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2023) 3).1 2).2 1).2
      5571458684340573499175904660863526309707436368618009778094462215162994926149148065965345363235565250466380835960783489038928038707).isSome = true := by
  decide +kernel

theorem k2023_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2023) 3).2 2).1 1).1
      997987499544646059621324951633296793289758994882095080783096835858283195580767911899955).isSome = true := by
  decide +kernel

theorem k2023_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2023) 3).2 2).1 1).2
      75430142446943584536094758621794002234882307739676034327812974743214336233459912428968795987479375287040036045).isSome = true := by
  decide +kernel

theorem k2023_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2023) 3).2 2).2 1).1
      3997868474610259450047791053550196084479500697047941925704708863675616697912911224746803).isSome = true := by
  decide +kernel

theorem k2023_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2023) 3).2 2).2 1).2
      15972720945324525207386874251825373873757679084033337683652023297119007135453671327124275).isSome = true := by
  decide +kernel

theorem k2024_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2024) 2).1 3).1 1).1
      997530848430088656911814220523903227504907378295278117473434476565177317323451575683891).isSome = true := by
  decide +kernel

theorem k2024_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2024) 2).1 3).1 1).2
      15588379548362916976909397877603400090586533391966900464835486027265140677950994749234).isSome = true := by
  decide +kernel

theorem k2024_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2024) 2).1 3).2
      86852506821437571652497616846187376950140262061935775357556106361922920248696295278850063558295899533322077142498671564594572081).isSome = true := by
  decide +kernel

theorem k2024_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2024) 2).2 3).1 1).1
      997597106053858091428814083772082668709823903032432284676771222928702455431565055718195).isSome = true := by
  decide +kernel

theorem k2024_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2024) 2).2 3).1 1).2
      1150489221307591966210421020168089673534988744369690580805823614803763376066151861829702624646117401251532).isSome = true := by
  decide +kernel

theorem k2024_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2024) 2).2 3).2 1).1
      997103669181621061588453238916356358929510510054446421793006069256189091769193364288305).isSome = true := by
  decide +kernel

theorem k2024_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2024) 2).2 3).2 1).2
      973886832812524213184854943642136735292041365542831727908383703522394311123816405708).isSome = true := by
  decide +kernel

theorem k2025_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2025) 2).1 3).1
      86817880545185644896201531214962532464850024404385280683646389228181557696412666185539682310552822680239328375739038302023834417).isSome = true := by
  decide +kernel

theorem k2025_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2025) 2).1 3).2
      3891401277889508848651429752732291308146243041513455282607395794506510627437365024561).isSome = true := by
  decide +kernel

theorem k2025_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2025) 2).2 3).1
      5426851800867422753740722181939374865028880178635677109224401576702891139075398739321465776979106947330292431902062735335480113).isSome = true := by
  decide +kernel

theorem k2025_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2025) 2).2 3).2
      75280345274006637473084159173895141168159351647229432006902406417348657683141147010583597515769077112192584909).isSome = true := by
  decide +kernel

theorem k2026_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2026) 2).1 3).1
      3890116419918768509467664393527408840161212288289447767071144501636858909528192587569).isSome = true := by
  decide +kernel

theorem k2026_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2026) 2).1 3).2
      243090690036313497552022133133832943715024918246247676433612107770948298436346238769).isSome = true := by
  decide +kernel

theorem k2026_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2026) 2).2 3).1
      15936171885639878307847110163755179957650149191493515983253417849398378549027282943036613).isSome = true := by
  decide +kernel

theorem k2026_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2026) 2).2 3).2
      3889461139825372646595411447531147209571048183570662732857869874910939391759910426417).isSome = true := by
  decide +kernel

theorem k2027_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2027) 2).1
      6246855928459527913501200175400315878359397424397431393794333240023056503278776446503305069949949202021189080341985787201337681788900100090197447).isSome = true := by
  decide +kernel

theorem k2027_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 2027) 2).2
      5548378387742711477112361871400606473670225643439231131241741128076975090869277987297688890007678318228734330075039712260446837959).isSome = true := by
  decide +kernel

theorem k2028_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2028) 2).1
      3291909864165177899821645259991153620224230332539676473186971977).isSome = true := by
  decide +kernel

theorem k2028_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 2028) 2).2
      18352709634340334432707482185783785402470090947833118215854599589950725257378078355519925110382421035709639).isSome = true := by
  decide +kernel

theorem c7 : allCells dirCell 2029 2047 [
    248676846079386129945544362958610583415289659720010126120385633109893296280007495405590, 274, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3] = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 2022 2047 :=
  (Cover.one (box := dirCellBox) (n := 2022)
      (.split 3 (.split 2 (.split 3 (.split 1 (.leaf _ k2022_0) (.leaf _ k2022_1)) (.split 1 (.leaf _ k2022_2) (.leaf _ k2022_3))) (.split 3 (.split 1 (.leaf _ k2022_4) (.leaf _ k2022_5)) (.split 1 (.leaf _ k2022_6) (.leaf _ k2022_7)))) (.split 2 (.split 1 (.split 3 (.leaf _ k2022_8) (.leaf _ k2022_9)) (.split 3 (.leaf _ k2022_10) (.leaf _ k2022_11))) (.split 1 (.split 3 (.leaf _ k2022_12) (.leaf _ k2022_13)) (.split 3 (.leaf _ k2022_14) (.leaf _ k2022_15)))))).trans <|
  (Cover.one (box := dirCellBox) (n := 2023)
      (.split 3 (.split 2 (.split 1 (.leaf _ k2023_0) (.leaf _ k2023_1)) (.split 1 (.leaf _ k2023_2) (.leaf _ k2023_3))) (.split 2 (.split 1 (.leaf _ k2023_4) (.leaf _ k2023_5)) (.split 1 (.leaf _ k2023_6) (.leaf _ k2023_7))))).trans <|
  (Cover.one (box := dirCellBox) (n := 2024)
      (.split 2 (.split 3 (.split 1 (.leaf _ k2024_0) (.leaf _ k2024_1)) (.leaf _ k2024_2)) (.split 3 (.split 1 (.leaf _ k2024_3) (.leaf _ k2024_4)) (.split 1 (.leaf _ k2024_5) (.leaf _ k2024_6))))).trans <|
  (Cover.one (box := dirCellBox) (n := 2025)
      (.split 2 (.split 3 (.leaf _ k2025_0) (.leaf _ k2025_1)) (.split 3 (.leaf _ k2025_2) (.leaf _ k2025_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 2026)
      (.split 2 (.split 3 (.leaf _ k2026_0) (.leaf _ k2026_1)) (.split 3 (.leaf _ k2026_2) (.leaf _ k2026_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 2027)
      (.split 2 (.leaf _ k2027_0) (.leaf _ k2027_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 2028)
      (.split 2 (.leaf _ k2028_0) (.leaf _ k2028_1))).trans <|
  (Cover.dir c7)

end C4.Cert.Dir024
