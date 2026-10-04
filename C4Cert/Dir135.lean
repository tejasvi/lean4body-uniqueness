module

public import C4Check

public section

/-! Cells `4125 ≤ n < 4154` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir135

theorem k4125_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4125) 2).1 3).1
      998328540138059226965178394246140610661933936296970842161094157270382468554585974389820).isSome = true := by
  decide +kernel

theorem k4125_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4125) 2).1 3).2
      865400980197624933410396676524305512615689069525241820191795576519740).isSome = true := by
  decide +kernel

theorem k4125_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4125) 2).2 3).1
      3382883776878794132764988716801112016307279082344012669952412394444).isSome = true := by
  decide +kernel

theorem k4125_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4125) 2).2 3).2
      249473354503676008650556988948540990012903708567095159210810475999204482228405138766908).isSome = true := by
  decide +kernel

theorem k4126_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4126) 2).1 3).1
      216241301981654826426101785989710803857659998632053715628799455607868).isSome = true := by
  decide +kernel

theorem k4126_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4126) 2).1 3).2
      3987446551127922056932359869201820005103665872304344952967753639492233512414355188923452).isSome = true := by
  decide +kernel

theorem k4126_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4126) 2).2 1).1
      54055731711495861534362643163091523434257917408192579420908739050556).isSome = true := by
  decide +kernel

theorem k4126_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4126) 2).2 1).2
      216218960621617766813817875057392065550514096775959662741524224621628).isSome = true := by
  decide +kernel

theorem k4127_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4127) 3).1 2).1
      13505117485461057871803648515338235377026238069360371610673347345468).isSome = true := by
  decide +kernel

theorem k4127_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4127) 3).1 2).2
      13506224264040892414175349087129086157493256245850919029861837585468).isSome = true := by
  decide +kernel

theorem k4127_2 : (checkBoxH dirMode depth (splitBox (dirCellBox 4127) 3).2
      308339207832169642888243509469882599449481084318050187654945301373243397385132625519240787327413979716960786772210).isSome = true := by
  decide +kernel

theorem k4128_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4128) 3).1
      19265606458246666266928208708012397157859741241972320296156248859944602477354373877176783771231097392523690504434).isSome = true := by
  decide +kernel

theorem k4128_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4128) 3).2
      19261174648449393988367868407852557044977493703831359706157785329374629726416112591994312902254782069130099887346).isSome = true := by
  decide +kernel

theorem k4129_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4129) 1).1
      293823167895865781138861073457986568017661983523704843535374933381392011713103798637418481186406218880957500).isSome = true := by
  decide +kernel

theorem k4129_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4129) 1).2
      1175321307616783914169408827941181722218463817018643087121506706357670722060939835212588836970978506280256316).isSome = true := by
  decide +kernel

theorem k4130_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4130) 1).1
      15923479205227318139724839885007767453520334798083010401487276026382241437065151243271228).isSome = true := by
  decide +kernel

theorem k4130_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4130) 1).2
      4699943984262978352984548945498195532312023196818818605922701252590393921904894760971198417161960657244898108).isSome = true := by
  decide +kernel

theorem c6 : allCells dirCell 4131 4132 [
    88755412260651823160025022935012831850120477380894505243813991099984448889253985262142964297248651900422040860117649228894919913715] = true := by
  decide +kernel

theorem c7 : allCells dirCell 4132 4133 [
    88746515976005580040719918011783857973130065921395537172857650260805640135347041468875409347998727776287217997943205133933169930481] = true := by
  decide +kernel

theorem c8 : allCells dirCell 4133 4134 [
    994769034345207765421023447336400484802645290858795319147534174503711262337198502539953] = true := by
  decide +kernel

theorem c9 : allCells dirCell 4134 4148 [
    51436336659488597552262341967625610181843592867958296381477073, 147562421495729619268, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 844458891654403352865996516873184719396701288850921727759030051] = true := by
  decide +kernel

theorem k4148_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4148) 3).1
      253815853699070176368547068777517240951005065236794489746040383181043629692027031401674).isSome = true := by
  decide +kernel

theorem k4148_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4148) 3).2
      18659456066937277390117721637042197993842100637228472912374149610338095326281008498982131879778461238644530).isSome = true := by
  decide +kernel

theorem k4149_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4149) 3).1
      351565846659993108073814718834530943424670469993345397509430395656476874255239579498160795232743675081578262176583281228398803762).isSome = true := by
  decide +kernel

theorem k4149_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4149) 3).2 2).1
      15728024048186049433956739340266243473643418012728734040518112307412584549874239753932).isSome = true := by
  decide +kernel

theorem k4149_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4149) 3).2 2).2
      3333661977258214804087752961548687792395013412599167836218579660).isSome = true := by
  decide +kernel

theorem k4150_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4150) 2).1 3).1
      3405154929129358815203475723756360509044043362491718130456931584716).isSome = true := by
  decide +kernel

theorem k4150_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4150) 2).1 3).2
      4014912631081069570090534366147966618263713468134671969422299512022701927382613258761009).isSome = true := by
  decide +kernel

theorem k4150_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4150) 2).2 3).1
      53232758818152276235951227067519903841693886295802753193223779020).isSome = true := by
  decide +kernel

theorem k4150_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4150) 2).2 3).2
      53145043456682554969476550501529109940829595406009195691325649612).isSome = true := by
  decide +kernel

theorem k4151_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4151) 2).1 3).1
      64147701965017929530554408990516250717840183785439468857683421235042792177917356015989553).isSome = true := by
  decide +kernel

theorem k4151_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4151) 2).1 3).2
      16018717683589743023240209405027727115852084906916443514439647566793862414958382488994764).isSome = true := by
  decide +kernel

theorem k4151_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4151) 2).2 3).1
      3396524380318004543861454886349096291092478550663039136068353323724).isSome = true := by
  decide +kernel

theorem k4151_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4151) 2).2 3).2
      868468197479033781842601255685803846236832171511795269385082249135052).isSome = true := by
  decide +kernel

theorem k4152_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4152) 2).1 3).1
      16002457072751547584259812826875020602318060438704129342368747834952234358753349262361548).isSome = true := by
  decide +kernel

theorem k4152_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4152) 2).1 3).2
      249829596276958382127325721123045008590176697278629295673634529342112140293836476498892).isSome = true := by
  decide +kernel

theorem k4152_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4152) 2).2 3).1
      216900826917297469371282262567379366138938741846819817470937956860876).isSome = true := by
  decide +kernel

theorem k4152_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4152) 2).2 3).2
      216714992165426004048768786873778200731173619808950106462046449812428).isSome = true := by
  decide +kernel

theorem k4153_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4153) 2).1 3).1
      3383355317469311151333993087822566307034311814973290574288427885516).isSome = true := by
  decide +kernel

theorem k4153_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4153) 2).1 3).2
      845323183898722036888143566542900459444816994750534922923512112076).isSome = true := by
  decide +kernel

theorem k4153_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4153) 2).2 3).1
      183427169513054129259422978975104305121010107340).isSome = true := by
  decide +kernel

theorem k4153_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4153) 2).2 3).2
      211356953442265227134064033622116338014065921358834497253839193036).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 4125 4154 :=
  (Cover.one (box := dirCellBox) (n := 4125)
      (.split 2 (.split 3 (.leaf _ k4125_0) (.leaf _ k4125_1)) (.split 3 (.leaf _ k4125_2) (.leaf _ k4125_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 4126)
      (.split 2 (.split 3 (.leaf _ k4126_0) (.leaf _ k4126_1)) (.split 1 (.leaf _ k4126_2) (.leaf _ k4126_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 4127)
      (.split 3 (.split 2 (.leaf _ k4127_0) (.leaf _ k4127_1)) (.leaf _ k4127_2))).trans <|
  (Cover.one (box := dirCellBox) (n := 4128)
      (.split 3 (.leaf _ k4128_0) (.leaf _ k4128_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 4129)
      (.split 1 (.leaf _ k4129_0) (.leaf _ k4129_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 4130)
      (.split 1 (.leaf _ k4130_0) (.leaf _ k4130_1))).trans <|
  (Cover.dir c6).trans <|
  (Cover.dir c7).trans <|
  (Cover.dir c8).trans <|
  (Cover.dir c9).trans <|
  (Cover.one (box := dirCellBox) (n := 4148)
      (.split 3 (.leaf _ k4148_0) (.leaf _ k4148_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 4149)
      (.split 3 (.leaf _ k4149_0) (.split 2 (.leaf _ k4149_1) (.leaf _ k4149_2)))).trans <|
  (Cover.one (box := dirCellBox) (n := 4150)
      (.split 2 (.split 3 (.leaf _ k4150_0) (.leaf _ k4150_1)) (.split 3 (.leaf _ k4150_2) (.leaf _ k4150_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 4151)
      (.split 2 (.split 3 (.leaf _ k4151_0) (.leaf _ k4151_1)) (.split 3 (.leaf _ k4151_2) (.leaf _ k4151_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 4152)
      (.split 2 (.split 3 (.leaf _ k4152_0) (.leaf _ k4152_1)) (.split 3 (.leaf _ k4152_2) (.leaf _ k4152_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 4153)
      (.split 2 (.split 3 (.leaf _ k4153_0) (.leaf _ k4153_1)) (.split 3 (.leaf _ k4153_2) (.leaf _ k4153_3))))

end C4.Cert.Dir135
