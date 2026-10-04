module

public import C4Check

public section

/-! Cells `3166 ≤ n < 3167` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir084

theorem k3166_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3166) 3).1 2).1 3).1 2).1 1).1 2).1
      1059318968086790696397083300273374303346647317219392774176843254440674139504810015890865).isSome = true := by
  decide +kernel

theorem k3166_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3166) 3).1 2).1 3).1 2).1 1).1 2).2
      4138049017541550940261235379007840296418739421959552090719577674886501717027589708012).isSome = true := by
  decide +kernel

theorem k3166_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3166) 3).1 2).1 3).1 2).1 1).2 2).1
      4115242016015124669599447819739216290726495877364678253761026144337553310586750080819).isSome = true := by
  decide +kernel

theorem k3166_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3166) 3).1 2).1 3).1 2).1 1).2 2).2
      4133946409736435027023078204736303000865170621695980770515629295823735416616029886257).isSome = true := by
  decide +kernel

theorem k3166_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3166) 3).1 2).1 3).1 2).2 1).1 2).1
      1037659273046069800070729415995260570936482041113849389550992241243977013565692703980).isSome = true := by
  decide +kernel

theorem k3166_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3166) 3).1 2).1 3).1 2).2 1).1 2).2
      259266116341716949377076642537291855655980006859529293284388175735406770684098891123).isSome = true := by
  decide +kernel

theorem k3166_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3166) 3).1 2).1 3).1 2).2 1).2
      1483057311497182351232734295036709976899435866220925929347563811660250766105936475502336313531592074684173010607346486455226432690).isSome = true := by
  decide +kernel

theorem k3166_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3166) 3).1 2).1 3).2 1).1 2).1 2).1
      16721196089514845135155069841797742500247407858528672551256941536696812876307065491284659).isSome = true := by
  decide +kernel

theorem k3166_8 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3166) 3).1 2).1 3).2 1).1 2).1 2).2
      1049599118425144934734999568146426994751801050859206584205059280860571995563418789081772).isSome = true := by
  decide +kernel

theorem k3166_9 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3166) 3).1 2).1 3).2 1).1 2).2 2).1
      256599330218924880613235383335620185865190298854727093982158973519430015726900575660).isSome = true := by
  decide +kernel

theorem k3166_10 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3166) 3).1 2).1 3).2 1).1 2).2 2).2
      256887502353378154494183541554243386693973271188556938677461441112886136398044298668).isSome = true := by
  decide +kernel

theorem k3166_11 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3166) 3).1 2).1 3).2 1).2 2).1 2).1
      1046328819122231057078966297844472418829414910230949045119108053702797136224994302729009).isSome = true := by
  decide +kernel

theorem k3166_12 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3166) 3).1 2).1 3).2 1).2 2).1 2).2
      65334405098173599093323377997743130012502114229145411509006533644231401591811468842803).isSome = true := by
  decide +kernel

theorem k3166_13 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3166) 3).1 2).1 3).2 1).2 2).2
      26969348100358714710375746457993683142864212682761939599896223099869281580137317663752967138310888946595310977167400414851798374073576344993278876878).isSome = true := by
  decide +kernel

theorem k3166_14 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3166) 3).1 2).2 3).1 1).1 2).1
      90389558687947655932518807750235648748720911764163633308420678369318088077274025737589927487467215284862319485259515419522290).isSome = true := by
  decide +kernel

theorem k3166_15 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3166) 3).1 2).2 3).1 1).1 2).2
      76731656079316211671352669564278366112933080970239846573564503682005616739861623481407737819483873436019).isSome = true := by
  decide +kernel

theorem k3166_16 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3166) 3).1 2).2 3).1 1).2 2).1
      16986096872077067412372500483185279748839061477895869722471514004708118188799104929067698).isSome = true := by
  decide +kernel

theorem k3166_17 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3166) 3).1 2).2 3).1 1).2 2).2
      306089785580790218373729461899716683117285861856031928781246993223068589415499688972510593379986449093436).isSome = true := by
  decide +kernel

theorem k3166_18 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3166) 3).1 2).2 3).2 1).1 2).1
      105585654424030991876062574155043679084469668242860707390229838291789485676801009904015937300252627321199164784173697951378146938527127270184056498).isSome = true := by
  decide +kernel

theorem k3166_19 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3166) 3).1 2).2 3).2 1).1 2).2
      22417815521247541474878517329266858535314122203725491444160366475363264253919823762919013486681217848280376622402696962334129).isSome = true := by
  decide +kernel

theorem k3166_20 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3166) 3).1 2).2 3).2 1).2 2).1
      22870382172283730897273237600644476779627777477859453976382968478293395611048800823456603601470131858821353716785610400741293233).isSome = true := by
  decide +kernel

theorem k3166_21 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3166) 3).1 2).2 3).2 1).2 2).2
      65840977425187389200165570982276721672553127410804697460403884359165012200262057155762).isSome = true := by
  decide +kernel

theorem k3166_22 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3166) 3).2 2).1 2).1 3).1 1).1 2).1
      1035225032598698049865704192204052661186633974767113886422724525428377110262180216928435).isSome = true := by
  decide +kernel

theorem k3166_23 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3166) 3).2 2).1 2).1 3).1 1).1 2).2
      16235535043576362466538196851694209752526597953403455324200273835524842266785784626988).isSome = true := by
  decide +kernel

theorem k3166_24 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3166) 3).2 2).1 2).1 3).1 1).2 2).1
      1034088535095542869851865846663124942980355374772322256614674935372477376443528022170419).isSome = true := by
  decide +kernel

theorem k3166_25 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3166) 3).2 2).1 2).1 3).1 1).2 2).2
      16216128962462365020997772451284804802982184174160368429849889580276317426782055025612).isSome = true := by
  decide +kernel

theorem k3166_26 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3166) 3).2 2).1 2).1 3).2 2).1 1).1
      65868541107880399318094608838883183126725029953764252186701539925309536134122101816261809).isSome = true := by
  decide +kernel

theorem k3166_27 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3166) 3).2 2).1 2).1 3).2 2).1 1).2
      4020930714445421112790469198603904000832071750959648646635575551688264102870150246188).isSome = true := by
  decide +kernel

theorem k3166_28 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3166) 3).2 2).1 2).1 3).2 2).2 1).1
      257691234752508792930615855583140599739483984129197762582286340881920447636102763232316).isSome = true := by
  decide +kernel

theorem k3166_29 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3166) 3).2 2).1 2).1 3).2 2).2 1).2
      4022428747463927821194941961933594927553908789497318220141543376426430322236460592940).isSome = true := by
  decide +kernel

theorem k3166_30 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3166) 3).2 2).1 2).2 3).1 1).1 2).1
      65023009948442556147726126827287849994429216832008059252130461862302549680456367209644).isSome = true := by
  decide +kernel

theorem k3166_31 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3166) 3).2 2).1 2).2 3).1 1).1 2).2
      220557847465543755533405110899872016580630839333327081217321204908).isSome = true := by
  decide +kernel

theorem k3166_32 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3166) 3).2 2).1 2).2 3).1 1).2 2).1
      16237166764000148987674423956251743044363751729317838988149445353930050835160118971340).isSome = true := by
  decide +kernel

theorem k3166_33 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3166) 3).2 2).1 2).2 3).1 1).2 2).2
      3439429092548814926317984057679868681902521198321642285063102156).isSome = true := by
  decide +kernel

theorem k3166_34 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3166) 3).2 2).1 2).2 3).2 1).1 2).1
      13984578528874463835423322379075354511193634696106843440588881329212).isSome = true := by
  decide +kernel

theorem k3166_35 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3166) 3).2 2).1 2).2 3).2 1).1 2).2
      16143678119996633481247838035736431465629477438466793654588232333486522656207377628972).isSome = true := by
  decide +kernel

theorem k3166_36 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3166) 3).2 2).1 2).2 3).2 1).2 2).1
      218299416682010899600594238743704571589770261686698266544047598540).isSome = true := by
  decide +kernel

theorem k3166_37 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3166) 3).2 2).1 2).2 3).2 1).2 2).2
      3416833546126997052051625777885676654813980747487889622980517580).isSome = true := by
  decide +kernel

theorem k3166_38 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3166) 3).2 2).2 3).1 1).1 2).1
      68391999790058957779736726519137192162885044225463803118137376070466658207959513202654835378).isSome = true := by
  decide +kernel

theorem k3166_39 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3166) 3).2 2).2 3).1 1).1 2).2
      76935054094274539316203262383324535544211400152677324237596962432373622375470157279394710791282858999193011).isSome = true := by
  decide +kernel

theorem k3166_40 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3166) 3).2 2).2 3).1 1).2 2).1
      22705392523947600440573842042845998503097022180079461157323169689244772537303421092945658246815332535629148777200917459456588594).isSome = true := by
  decide +kernel

theorem k3166_41 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3166) 3).2 2).2 3).1 1).2 2).2
      5685350655975245468854616501166827396865276097508687922845114790137119803234622972671165195745907536977752676106017240065138482).isSome = true := by
  decide +kernel

theorem k3166_42 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3166) 3).2 2).2 3).2 2).1 1).1
      1059971597257405142649329291967192169613714033987339203485729983260439177186064027953249458).isSome = true := by
  decide +kernel

theorem k3166_43 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3166) 3).2 2).2 3).2 2).1 1).2
      4878845697491870575171243932841015592479712023468786886132501307840694943212861137635720591854666913278425906).isSome = true := by
  decide +kernel

theorem k3166_44 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3166) 3).2 2).2 3).2 2).2 1).1
      1061715069074887128210366147691884384442899851899374255834252615789005618231849716575468722).isSome = true := by
  decide +kernel

theorem k3166_45 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3166) 3).2 2).2 3).2 2).2 1).2
      305542887894241113089475391492668905413638352848482557394902305784807006142533811203574862404280352960306993).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 3166 3167 :=
  (Cover.one (box := dirCellBox) (n := 3166)
      (.split 3 (.split 2 (.split 3 (.split 2 (.split 1 (.split 2 (.leaf _ k3166_0) (.leaf _ k3166_1)) (.split 2 (.leaf _ k3166_2) (.leaf _ k3166_3))) (.split 1 (.split 2 (.leaf _ k3166_4) (.leaf _ k3166_5)) (.leaf _ k3166_6))) (.split 1 (.split 2 (.split 2 (.leaf _ k3166_7) (.leaf _ k3166_8)) (.split 2 (.leaf _ k3166_9) (.leaf _ k3166_10))) (.split 2 (.split 2 (.leaf _ k3166_11) (.leaf _ k3166_12)) (.leaf _ k3166_13)))) (.split 3 (.split 1 (.split 2 (.leaf _ k3166_14) (.leaf _ k3166_15)) (.split 2 (.leaf _ k3166_16) (.leaf _ k3166_17))) (.split 1 (.split 2 (.leaf _ k3166_18) (.leaf _ k3166_19)) (.split 2 (.leaf _ k3166_20) (.leaf _ k3166_21))))) (.split 2 (.split 2 (.split 3 (.split 1 (.split 2 (.leaf _ k3166_22) (.leaf _ k3166_23)) (.split 2 (.leaf _ k3166_24) (.leaf _ k3166_25))) (.split 2 (.split 1 (.leaf _ k3166_26) (.leaf _ k3166_27)) (.split 1 (.leaf _ k3166_28) (.leaf _ k3166_29)))) (.split 3 (.split 1 (.split 2 (.leaf _ k3166_30) (.leaf _ k3166_31)) (.split 2 (.leaf _ k3166_32) (.leaf _ k3166_33))) (.split 1 (.split 2 (.leaf _ k3166_34) (.leaf _ k3166_35)) (.split 2 (.leaf _ k3166_36) (.leaf _ k3166_37))))) (.split 3 (.split 1 (.split 2 (.leaf _ k3166_38) (.leaf _ k3166_39)) (.split 2 (.leaf _ k3166_40) (.leaf _ k3166_41))) (.split 2 (.split 1 (.leaf _ k3166_42) (.leaf _ k3166_43)) (.split 1 (.leaf _ k3166_44) (.leaf _ k3166_45)))))))

end C4.Cert.Dir084
