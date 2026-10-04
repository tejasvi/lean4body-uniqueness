module

public import C4Check

public section

/-! Cells `1685 ≤ n < 1693` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir015

theorem k1685_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1685) 3).1 2).1
      1163411894285258851372616000032119442275954992111283335259752181483487780122198050821040335676125724350215).isSome = true := by
  decide +kernel

theorem k1685_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1685) 3).1 2).2
      290981778529176227191503890120566095314943378855918126748697661946693002595964151908520212202335765278981).isSome = true := by
  decide +kernel

theorem k1685_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1685) 3).2 2).1 3).1
      61497504753814167743265385527094833233420187279007555712076372934467958899395958801).isSome = true := by
  decide +kernel

theorem k1685_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1685) 3).2 2).1 3).2
      18127327916477442071325213828271134080941055880557215749295140266547414459866707938741205975146354039153).isSome = true := by
  decide +kernel

theorem k1685_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1685) 3).2 2).2 1).1
      52031103111591011527007045292525520461584821814123578268179475).isSome = true := by
  decide +kernel

theorem k1685_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1685) 3).2 2).2 1).2
      72536089367295475374162020733501918382348939945245095257746848482969649602131902713432311674710164723123).isSome = true := by
  decide +kernel

theorem k1686_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1686) 3).1 2).1 3).1
      4640563093000143402316028036057109710485561946418406810093179210128341055256482422864396827713654639910321).isSome = true := by
  decide +kernel

theorem k1686_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1686) 3).1 2).1 3).2
      1366435559162000723989323891958650958996545333138657356602897554220365222388928801704075873615397052311326959730351181015899569).isSome = true := by
  decide +kernel

theorem k1686_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1686) 3).1 2).2 1).1
      15685293937569399976639367342480208423413111881923711912368711271394804931593852256627).isSome = true := by
  decide +kernel

theorem k1686_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1686) 3).1 2).2 1).2
      251033235475458783264229083044114282732612738708620477777720054448143350423980894679731).isSome = true := by
  decide +kernel

theorem k1686_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1686) 3).2 2).1 1).1
      62615297533162046450110111041697329641854159309866115534705197665160408429225760087219).isSome = true := by
  decide +kernel

theorem k1686_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1686) 3).2 2).1 1).2
      73931702530509296073225373240599811248695042521958236255442457414777021305620145725556445470171899119901491).isSome = true := by
  decide +kernel

theorem k1686_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1686) 3).2 2).2 1).1
      15659134731540055272442100488230603325944548969340794921695739963365995737313280941235).isSome = true := by
  decide +kernel

theorem k1686_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1686) 3).2 2).2 1).2
      1002297185234866172701751130556202802330816842096005972117176841062767446496851068284083).isSome = true := by
  decide +kernel

theorem k1687_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1687) 3).1 2).1 1).1
      5449293814312240986558798144382747028652345535368197275461056923567152973254413482633135900074943880765978612899183084946447154).isSome = true := by
  decide +kernel

theorem k1687_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1687) 3).1 2).1 1).2
      5449920852165041280746223306625510195526060294109254619209071392013305769352690779512415098315061080368046721423553875176446770).isSome = true := by
  decide +kernel

theorem k1687_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1687) 3).1 2).2 1).1
      62542380649267650320460579799758001180015386156334939228209130851644367396004579072819).isSome = true := by
  decide +kernel

theorem k1687_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1687) 3).1 2).2 1).2
      1155519614425677769382619024309681101266756713591607344606154340319078200543429407491262777902771772158924).isSome = true := by
  decide +kernel

theorem k1687_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1687) 3).2 2).1 1).1
      294868436014977134086703298259539549610962955412505776948294488110322020172590334363120917599102167682505523).isSome = true := by
  decide +kernel

theorem k1687_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1687) 3).2 2).1 1).2
      63947786911684004939640794737496372265967929007946788281320642657153801030730298686909235).isSome = true := by
  decide +kernel

theorem k1687_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1687) 3).2 2).2 1).1
      15621643243216710656869734993405407719894657201674622759860984233534389927777402834636).isSome = true := by
  decide +kernel

theorem k1687_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1687) 3).2 2).2 1).2
      15624078083084310640562918779673980177485199307306781369017869012510600449636895248076).isSome = true := by
  decide +kernel

theorem k1688_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1688) 3).1 2).1 1).1
      3992769526431285350488191224951880511308772817264111585306076721517842116554656646023987).isSome = true := by
  decide +kernel

theorem k1688_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1688) 3).1 2).1 1).2
      998327979239189192355159928469106085657379895304986570318957510013950336906285785903923).isSome = true := by
  decide +kernel

theorem k1688_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1688) 3).1 2).2 1).1
      62416373381902747102641107104617628039284114881814402369370483851039031369340381244108).isSome = true := by
  decide +kernel

theorem k1688_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1688) 3).1 2).2 1).2
      211507490111082568762276376767680059955301798048216365685857045196).isSome = true := by
  decide +kernel

theorem k1688_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1688) 3).2 2).1 1).1
      3897327319820258534516216068645232898055729855003994617195792218021133104700479356108).isSome = true := by
  decide +kernel

theorem k1688_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1688) 3).2 2).1 1).2
      3897818663649250294668670668739304211171314268579685165586841425142489626352129785036).isSome = true := by
  decide +kernel

theorem k1688_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1688) 3).2 2).2 1).1
      974517528352510936571552592228375828068090244761265714254694007588346450535375535308).isSome = true := by
  decide +kernel

theorem k1688_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1688) 3).2 2).2 1).2
      3898669156546747890328452200385244373025241609415036548387509347082902044975155245772).isSome = true := by
  decide +kernel

theorem k1689_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1689) 3).1 2).1
      22236031865263851281614399440623766128356347824804532694303854345172374217212994115690616138960332994014173872868022781916837376817).isSome = true := by
  decide +kernel

theorem k1689_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1689) 3).1 2).2
      22238847612516622356175190420640470313374065988943912000584679118041691635159111176676733467298171531729405084098933068677269222193).isSome = true := by
  decide +kernel

theorem k1689_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1689) 3).2 2).1
      1389025407791667814263296743873738029573416437203776124950061004429627556275589046031783691998690161147558734752705327656616178481).isSome = true := by
  decide +kernel

theorem k1689_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1689) 3).2 2).2
      1389207641685216746134531960836687809718000259109310466600651431655707787951534259629670227512061475575490748279162335903323370289).isSome = true := by
  decide +kernel

theorem k1690_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1690) 3).1 2).1
      1388376323133280853795184269346804445752995948246005326448492054593988700207915003738870390174448385925449175427770383028960736049).isSome = true := by
  decide +kernel

theorem k1690_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1690) 3).1 2).2
      4704359518528557390132502103951619172598182300579835056383453648538422293812722576789561607201034483980940081).isSome = true := by
  decide +kernel

theorem k1690_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1690) 3).2 2).1
      996748515393168951184486930302873692324802468631045994580038692569436470301189325026097).isSome = true := by
  decide +kernel

theorem k1690_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1690) 3).2 2).2
      995807110423496343558943163628483899702576769068446375797047344093716336897967808672561).isSome = true := by
  decide +kernel

theorem k1691_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1691) 3).1 2).1
      995399384707894653579093690714854529626345675263935214777339577929925099835371558892337).isSome = true := by
  decide +kernel

theorem k1691_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1691) 3).1 2).2
      53961780798120627110257435237101831820159973494318855315540701948721).isSome = true := by
  decide +kernel

theorem k1691_2 : (checkBoxH dirMode depth (splitBox (dirCellBox 1691) 3).2
      19251716349713814397857302920812774866165776018543989860081957376786938051663279696459601297886279689799512968838).isSome = true := by
  decide +kernel

theorem k1692_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 1692) 3).1
      63670426996737147210969701896349515168480517572028389120138137926475165310578273288803021).isSome = true := by
  decide +kernel

theorem k1692_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 1692) 3).2
      13164672992820921845661919795098078367744352039387664843455700625).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 1685 1693 :=
  (Cover.one (box := dirCellBox) (n := 1685)
      (.split 3 (.split 2 (.leaf _ k1685_0) (.leaf _ k1685_1)) (.split 2 (.split 3 (.leaf _ k1685_2) (.leaf _ k1685_3)) (.split 1 (.leaf _ k1685_4) (.leaf _ k1685_5))))).trans <|
  (Cover.one (box := dirCellBox) (n := 1686)
      (.split 3 (.split 2 (.split 3 (.leaf _ k1686_0) (.leaf _ k1686_1)) (.split 1 (.leaf _ k1686_2) (.leaf _ k1686_3))) (.split 2 (.split 1 (.leaf _ k1686_4) (.leaf _ k1686_5)) (.split 1 (.leaf _ k1686_6) (.leaf _ k1686_7))))).trans <|
  (Cover.one (box := dirCellBox) (n := 1687)
      (.split 3 (.split 2 (.split 1 (.leaf _ k1687_0) (.leaf _ k1687_1)) (.split 1 (.leaf _ k1687_2) (.leaf _ k1687_3))) (.split 2 (.split 1 (.leaf _ k1687_4) (.leaf _ k1687_5)) (.split 1 (.leaf _ k1687_6) (.leaf _ k1687_7))))).trans <|
  (Cover.one (box := dirCellBox) (n := 1688)
      (.split 3 (.split 2 (.split 1 (.leaf _ k1688_0) (.leaf _ k1688_1)) (.split 1 (.leaf _ k1688_2) (.leaf _ k1688_3))) (.split 2 (.split 1 (.leaf _ k1688_4) (.leaf _ k1688_5)) (.split 1 (.leaf _ k1688_6) (.leaf _ k1688_7))))).trans <|
  (Cover.one (box := dirCellBox) (n := 1689)
      (.split 3 (.split 2 (.leaf _ k1689_0) (.leaf _ k1689_1)) (.split 2 (.leaf _ k1689_2) (.leaf _ k1689_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 1690)
      (.split 3 (.split 2 (.leaf _ k1690_0) (.leaf _ k1690_1)) (.split 2 (.leaf _ k1690_2) (.leaf _ k1690_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 1691)
      (.split 3 (.split 2 (.leaf _ k1691_0) (.leaf _ k1691_1)) (.leaf _ k1691_2))).trans <|
  (Cover.one (box := dirCellBox) (n := 1692)
      (.split 3 (.leaf _ k1692_0) (.leaf _ k1692_1)))

end C4.Cert.Dir015
