module

public import C4Check

public section

/-! Cells `2414 ≤ n < 2439` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir043

theorem k2414_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2414) 3).1 2).1 1).1 3).1
      1155335739579633700622524915967534274024433569215771751346990405459554949984736700697142085971312967146188).isSome = true := by
  decide +kernel

theorem k2414_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2414) 3).1 2).1 1).1 3).2
      3911215985669052881577258857830352030495839566635094336782012726480129613054644574924).isSome = true := by
  decide +kernel

theorem k2414_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2414) 3).1 2).1 1).2 3).1
      15654015881647852762515799576911572619142998204563280952039046295195072626850963345100).isSome = true := by
  decide +kernel

theorem k2414_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2414) 3).1 2).1 1).2 3).2
      62565412274545855555354521410604290580505476204662267745092049837995514554024325885644).isSome = true := by
  decide +kernel

theorem k2414_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2414) 3).1 2).2 1).1 3).1
      15684134764631727079389636435219533608415170179115181044202724315080755273804413882060).isSome = true := by
  decide +kernel

theorem k2414_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2414) 3).1 2).2 1).1 3).2
      3913890880635324141448758801097834074378614364554451753619731961813842194859621341900).isSome = true := by
  decide +kernel

theorem k2414_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2414) 3).1 2).2 1).2 3).1
      3397254807401680236726672273921204434128140808458756038551664545484).isSome = true := by
  decide +kernel

theorem k2414_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2414) 3).1 2).2 1).2 3).2
      3913345467328823834272742519857945422978135122709452524218020604467795760265989446348).isSome = true := by
  decide +kernel

theorem k2414_8 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2414) 3).2 2).1 1).1 3).1
      3908350723085216619443459454150062626444732802659093612894412857973802349541467871948).isSome = true := by
  decide +kernel

theorem k2414_9 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2414) 3).2 2).1 1).1 3).2
      827147974502795269255642916583149759339631830196073167404234444).isSome = true := by
  decide +kernel

theorem k2414_10 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2414) 3).2 2).1 1).2
      21773833654966119557279539717827181305675812987416782818226936063916640430917560097307150147434831140222278607388093338214689587).isSome = true := by
  decide +kernel

theorem k2414_11 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2414) 3).2 2).2 1).1 3).1
      211978459092195231324286072906005863534631446613443864309385382604).isSome = true := by
  decide +kernel

theorem k2414_12 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2414) 3).2 2).2 1).1 3).2
      211833916270511430874442465981603513104535617597371770273176996556).isSome = true := by
  decide +kernel

theorem k2414_13 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2414) 3).2 2).2 1).2 3).1
      3910269881079589020412579271939353708233714035655800361319029545935037911345604844236).isSome = true := by
  decide +kernel

theorem k2414_14 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2414) 3).2 2).2 1).2 3).2
      13239409067161185161371934868945149559278263070325340354635078348).isSome = true := by
  decide +kernel

theorem k2415_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2415) 2).1 3).1 1).1
      87044126345305128694316307339820047507605150094415451281333540992266475204021217025303375761184742458281420738802457806024167218).isSome = true := by
  decide +kernel

theorem k2415_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2415) 2).1 3).1 1).2
      5438012110835226531322113314882626487207425417292827810604975984391034169436193205159214350422528443679372005455983427333774131).isSome = true := by
  decide +kernel

theorem k2415_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2415) 2).1 3).2 1).1
      4604071095874020372710725927672457617459529174550344861003078421707094276112500636064251503129443519387442).isSome = true := by
  decide +kernel

theorem k2415_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2415) 2).1 3).2 1).2
      15595106279920240401995022885926401106198046989870487630539998388829302144965158394675).isSome = true := by
  decide +kernel

theorem k2415_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2415) 2).2 3).1 1).1
      348232144635483467886760906212346050737506508152713099074564930776416528465732328336136909520823603278696387750973422328363297587).isSome = true := by
  decide +kernel

theorem k2415_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2415) 2).2 3).1 1).2
      87161293754873219181818167666983375113848277804247890068557211202283168516653382571206121697935289921963672711539617875415748402).isSome = true := by
  decide +kernel

theorem k2415_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2415) 2).2 3).2 1).1
      5437593566971823385987052673180077868913095654228920063057042425948872255026134674427531339241244906143017862262252867463535410).isSome = true := by
  decide +kernel

theorem k2415_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2415) 2).2 3).2 1).2
      4609734122964715185511944748528674221668059119956583520809187429500984312426428753582564954745239122594764).isSome = true := by
  decide +kernel

theorem k2416_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2416) 2).1 3).1 1).1
      243571097958147349432265684859525123729854174037692767674251356356445292848016219084).isSome = true := by
  decide +kernel

theorem k2416_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2416) 2).1 3).1 1).2
      243801108879545575551690645130014758234550976172192880437948985118668980315449941804).isSome = true := by
  decide +kernel

theorem k2416_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2416) 2).1 3).2
      400564375186643958640393132640701311019332048709182669831505794464412429549609052113141888627288869121691584251430398223536815269921560961475895089).isSome = true := by
  decide +kernel

theorem k2416_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2416) 2).2 3).1 1).1
      62364787919145212785030543760254297958300656559794309892077413193829419249479586754252).isSome = true := by
  decide +kernel

theorem k2416_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2416) 2).2 3).1 1).2
      211522186865410753410387595233290104701922159306404406839221726924).isSome = true := by
  decide +kernel

theorem k2416_5 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2416) 2).2 3).2
      1602681148781884660857360605166753239038826483224602288539072788218901617339055438915214566268952195569647037678957221711258213842135889131603447601).isSome = true := by
  decide +kernel

theorem k2417_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2417) 2).1 3).1
      249119277809614228307453083769166644133033560200215116662144680780152458854186560247601).isSome = true := by
  decide +kernel

theorem k2417_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2417) 2).1 3).2
      1148770447540594666191714766098512274600717401762100616229685156493995781762162434328235057639027723885745).isSome = true := by
  decide +kernel

theorem k2417_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2417) 2).2 3).1
      400465428735960889823168723358336170961588050907820468561977893492370139163735117728056164846682998909209918956203100270244688201400036775228201777).isSome = true := by
  decide +kernel

theorem k2417_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2417) 2).2 3).2
      3892137985160613134868969831619610841727838740509724325224772808947955769032123553585).isSome = true := by
  decide +kernel

theorem k2418_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2418) 2).1
      7379327258655538464787139336891331617666900042692387356463150038102824909001915767247730187617801583062578839368739057080471732194158438579829135086605691491267352263).isSome = true := by
  decide +kernel

theorem k2418_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2418) 2).2 3).1
      15563402094707821896333488378491438900901049168734001803996063349778307694438052599601).isSome = true := by
  decide +kernel

theorem k2418_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2418) 2).2 3).2
      52765644074851679963413055432442148592067208074123427221950912305).isSome = true := by
  decide +kernel

theorem k2419_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2419) 2).1
      243001152446425068794764219551805081274468991449162726567499815051199247409974365255).isSome = true := by
  decide +kernel

theorem k2419_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 2419) 2).2
      99972658539976480640600667563935591729095475886619840160079039103988552125064908237542852512074060548901766546076888849263269030668979277133063367).isSome = true := by
  decide +kernel

theorem c6 : allCells dirCell 2420 2438 [
    15920797393687135638195104595333035793986024844333079927170775243435307683588035060367446,
    2788184925612818898851502960243200593825042, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] = true := by
  decide +kernel

theorem k2438_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2438) 3).1
      140135423915486843428612602934053085793063548423).isSome = true := by
  decide +kernel

theorem k2438_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2438) 3).2 3).1
      422903915634046280459936971076917350127398007127329572143453947599900310398842643155511402177725939143953455570494507635771582973364722696912610326).isSome = true := by
  decide +kernel

theorem k2438_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2438) 3).2 3).2 2).1
      22205848518276270262040514698994604229449119688371393399714984402843095659608542357689296437863582881461190073382346414536009).isSome = true := by
  decide +kernel

theorem k2438_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2438) 3).2 3).2 2).2
      63757772216054472236691906520924271148041344118872332098881524342535885124911716721).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 2414 2439 :=
  (Cover.one (box := dirCellBox) (n := 2414)
      (.split 3 (.split 2 (.split 1 (.split 3 (.leaf _ k2414_0) (.leaf _ k2414_1)) (.split 3 (.leaf _ k2414_2) (.leaf _ k2414_3))) (.split 1 (.split 3 (.leaf _ k2414_4) (.leaf _ k2414_5)) (.split 3 (.leaf _ k2414_6) (.leaf _ k2414_7)))) (.split 2 (.split 1 (.split 3 (.leaf _ k2414_8) (.leaf _ k2414_9)) (.leaf _ k2414_10)) (.split 1 (.split 3 (.leaf _ k2414_11) (.leaf _ k2414_12)) (.split 3 (.leaf _ k2414_13) (.leaf _ k2414_14)))))).trans <|
  (Cover.one (box := dirCellBox) (n := 2415)
      (.split 2 (.split 3 (.split 1 (.leaf _ k2415_0) (.leaf _ k2415_1)) (.split 1 (.leaf _ k2415_2) (.leaf _ k2415_3))) (.split 3 (.split 1 (.leaf _ k2415_4) (.leaf _ k2415_5)) (.split 1 (.leaf _ k2415_6) (.leaf _ k2415_7))))).trans <|
  (Cover.one (box := dirCellBox) (n := 2416)
      (.split 2 (.split 3 (.split 1 (.leaf _ k2416_0) (.leaf _ k2416_1)) (.leaf _ k2416_2)) (.split 3 (.split 1 (.leaf _ k2416_3) (.leaf _ k2416_4)) (.leaf _ k2416_5)))).trans <|
  (Cover.one (box := dirCellBox) (n := 2417)
      (.split 2 (.split 3 (.leaf _ k2417_0) (.leaf _ k2417_1)) (.split 3 (.leaf _ k2417_2) (.leaf _ k2417_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 2418)
      (.split 2 (.leaf _ k2418_0) (.split 3 (.leaf _ k2418_1) (.leaf _ k2418_2)))).trans <|
  (Cover.one (box := dirCellBox) (n := 2419)
      (.split 2 (.leaf _ k2419_0) (.leaf _ k2419_1))).trans <|
  (Cover.dir c6).trans <|
  (Cover.one (box := dirCellBox) (n := 2438)
      (.split 3 (.leaf _ k2438_0) (.split 3 (.leaf _ k2438_1) (.split 2 (.leaf _ k2438_2) (.leaf _ k2438_3)))))

end C4.Cert.Dir043
