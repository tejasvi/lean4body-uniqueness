module

public import C4Check

public section

/-! Cells `1829 ≤ n < 1940` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir019

theorem k1829_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 1829) 3).1
      19300800938113993739690048625118416109367089132284561715342424760734928669876414533477221300499795036099344396530).isSome = true := by
  decide +kernel

theorem k1829_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 1829) 3).2
      19289884834352487592693780699221521618430754307187325875618800824078778011110383241369305249257479873260407681265).isSome = true := by
  decide +kernel

theorem k1830_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 1830) 3).1
      1389720287364002702060473874193921996507858350453365524021474590777301930278086169693197984591111397746847676904367416350606345020).isSome = true := by
  decide +kernel

theorem k1830_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 1830) 3).2
      73506635266436767888089225949482004927508466384434629210725566976194365960882796040429144484513282866830513).isSome = true := by
  decide +kernel

theorem k1831_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 1831) 1).1
      3887073639038236399388998266990492563153310747127285689483209245766734100216809353907).isSome = true := by
  decide +kernel

theorem k1831_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 1831) 1).2
      287094974450695036003565223143021071177492422189684687731585301177037628722837139233750539501143198257980).isSome = true := by
  decide +kernel

theorem c3 : allCells dirCell 1832 1854 [
    17918146133725620104527084963608863317360960750306117641408352678512978669877965370560294700182674930033,
    147498093056164151940, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    38266404151851667371027] = true := by
  decide +kernel

theorem k1854_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 1854) 3).1
      51913367633185954680513127297626855416525319721102530476250482).isSome = true := by
  decide +kernel

theorem k1854_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 1854) 3).2
      393639952481994857308142332657466439623785527010619145792374933553691211329028348803318488090184396304502754648438271501330252335373710669477362).isSome = true := by
  decide +kernel

theorem k1855_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 1855) 3).1
      340917079295671432250766453142071002851560857427986647576492284556865775156883604356973959714969994530204580707839143323464946).isSome = true := by
  decide +kernel

theorem k1855_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 1855) 3).2
      5578714997611058052244110541349863967769909261225483616304323766828132524295884897068636018677097165339671487732414863288259529970).isSome = true := by
  decide +kernel

theorem k1856_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1856) 3).1 2).1
      211665445726456207621622245845430525919690139597266815758041072444).isSome = true := by
  decide +kernel

theorem k1856_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1856) 3).1 2).2
      211657779227492613605820456969050917410181829864286161296376185660).isSome = true := by
  decide +kernel

theorem k1856_2 : (checkBoxH dirMode depth (splitBox (dirCellBox 1856) 3).2
      5568524117479724241553968446828377308035270992445791457163176916603319272364157181752347241950240651694644368389232211886587900145).isSome = true := by
  decide +kernel

theorem k1857_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 1857) 1).1
      18839490863357293165365859073207821241177610586270901959320521653575815850607064593821969317927118208188269372).isSome = true := by
  decide +kernel

theorem k1857_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 1857) 1).2
      1206051818203517042263590847949375320097654573864969754851935829389677361961365030626648921652774886002282971964).isSome = true := by
  decide +kernel

theorem k1858_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 1858) 1).1
      62258004628417748262106722170675273531006477015975585438227017895872806855066372745788).isSome = true := by
  decide +kernel

theorem k1858_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 1858) 1).2
      996441524629745383480163407636698730784581686925483119467999062731720812499682495285820).isSome = true := by
  decide +kernel

theorem k1859_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 1859) 1).1
      205912488264210181443391396643088132974630791766523886505516348).isSome = true := by
  decide +kernel

theorem k1859_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 1859) 1).2
      15555350882651263335372218145176548713750063525695415209197528234555918333871541057084).isSome = true := by
  decide +kernel

theorem c10 : allCells dirCell 1860 1882 [
    15180431343838310715370710003077079835533360417960592860317861496809058512224111761,
    147497679777253828884, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] = true := by
  decide +kernel

theorem c11 : allCells dirCell 1882 1883 [
    979138054723159790241639341141402821238712470059930235560693551926915781833116244231] = true := by
  decide +kernel

theorem k1883_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 1883) 3).1
      1154875707785942470352854915125604806870045373225183973476773839566655883728287311844700890763845821625586).isSome = true := by
  decide +kernel

theorem k1883_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 1883) 3).2
      340508258579305874617725893009201356717946837653980247600946976787673098105916715552790077954191826566765134599031514266957041).isSome = true := by
  decide +kernel

theorem k1884_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 1884) 1).1
      1391911238589269096665777170604524698232925086759035312770932918983425126579734604851255909319362819884977030092888797413656768764).isSome = true := by
  decide +kernel

theorem k1884_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 1884) 1).2
      4717177004638711506243829105261832099048737582839947448097149083494752020444565247644626088398924636146877244).isSome = true := by
  decide +kernel

theorem k1885_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 1885) 3).1
      1178009532810132292820577171170587007573597976491266492925678123301502880203066316648214755128049019643740988).isSome = true := by
  decide +kernel

theorem k1885_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 1885) 3).2
      3988480785692381153238653959973522079298580608864715122471904189337400964240636282610492).isSome = true := by
  decide +kernel

theorem k1886_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 1886) 1).1
      3891130380509894206082186785540541994971521433837982715014775923182091460152126853948).isSome = true := by
  decide +kernel

theorem k1886_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 1886) 1).2
      973074778372032146214338498047701692543043981594751909767612696537630799418590885436).isSome = true := by
  decide +kernel

theorem c16 : allCells dirCell 1887 1888 [
    1355233773062777508645049693550281428753838750333145673395213331486937645237199452731417747499172845358671058452434671246889713] = true := by
  decide +kernel

theorem c17 : allCells dirCell 1888 1911 [
    51431087886234327109705717431986316758889243542975728699657105, 147497887241370770244, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 38080040730847010780211] = true := by
  decide +kernel

theorem k1911_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 1911) 3).1
      15284102812743528109610434665541661991169424747918565590086090269053079932885752177).isSome = true := by
  decide +kernel

theorem k1911_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 1911) 3).2
      54226621537856481493745561207842734583346010725206152646710823078130).isSome = true := by
  decide +kernel

theorem k1912_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 1912) 3).1
      249837705312859163531806586285584611098921639354388745710537307696382953893996122616060).isSome = true := by
  decide +kernel

theorem k1912_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 1912) 3).2
      3382972188289216687211351543661362497253714632355021748698579714876).isSome = true := by
  decide +kernel

theorem k1913_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 1913) 1).1
      844677353302136711718364855775327021912841440510819319253947065148).isSome = true := by
  decide +kernel

theorem k1913_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 1913) 1).2
      211228695972659412822397307688919764352303204225402397873766124092).isSome = true := by
  decide +kernel

theorem k1914_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 1914) 2).1
      972889248687971853748011959959446179913072399056396866832148553195446745568419116604).isSome = true := by
  decide +kernel

theorem k1914_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 1914) 2).2
      3296169892222016109047733204638398282686648082554513428929960124).isSome = true := by
  decide +kernel

theorem c22 : allCells dirCell 1915 1916 [
    1354976098442405044419002771942149108383044620623976527758287962926644196201591217044047127708598524197584647771664865135284977] = true := by
  decide +kernel

theorem c23 : allCells dirCell 1916 1939 [
    51430166042280191708587885091381581199588165512018546846465489, 147498568663714306196, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] = true := by
  decide +kernel

theorem c24 : allCells dirCell 1939 1940 [
    4612353157081682029481680284518781463127814738117135867259737724934552000870000288893405528814120553808243] = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 1829 1940 :=
  (Cover.one (box := dirCellBox) (n := 1829)
      (.split 3 (.leaf _ k1829_0) (.leaf _ k1829_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 1830)
      (.split 3 (.leaf _ k1830_0) (.leaf _ k1830_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 1831)
      (.split 1 (.leaf _ k1831_0) (.leaf _ k1831_1))).trans <|
  (Cover.dir c3).trans <|
  (Cover.one (box := dirCellBox) (n := 1854)
      (.split 3 (.leaf _ k1854_0) (.leaf _ k1854_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 1855)
      (.split 3 (.leaf _ k1855_0) (.leaf _ k1855_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 1856)
      (.split 3 (.split 2 (.leaf _ k1856_0) (.leaf _ k1856_1)) (.leaf _ k1856_2))).trans <|
  (Cover.one (box := dirCellBox) (n := 1857)
      (.split 1 (.leaf _ k1857_0) (.leaf _ k1857_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 1858)
      (.split 1 (.leaf _ k1858_0) (.leaf _ k1858_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 1859)
      (.split 1 (.leaf _ k1859_0) (.leaf _ k1859_1))).trans <|
  (Cover.dir c10).trans <|
  (Cover.dir c11).trans <|
  (Cover.one (box := dirCellBox) (n := 1883)
      (.split 3 (.leaf _ k1883_0) (.leaf _ k1883_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 1884)
      (.split 1 (.leaf _ k1884_0) (.leaf _ k1884_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 1885)
      (.split 3 (.leaf _ k1885_0) (.leaf _ k1885_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 1886)
      (.split 1 (.leaf _ k1886_0) (.leaf _ k1886_1))).trans <|
  (Cover.dir c16).trans <|
  (Cover.dir c17).trans <|
  (Cover.one (box := dirCellBox) (n := 1911)
      (.split 3 (.leaf _ k1911_0) (.leaf _ k1911_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 1912)
      (.split 3 (.leaf _ k1912_0) (.leaf _ k1912_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 1913)
      (.split 1 (.leaf _ k1913_0) (.leaf _ k1913_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 1914)
      (.split 2 (.leaf _ k1914_0) (.leaf _ k1914_1))).trans <|
  (Cover.dir c22).trans <|
  (Cover.dir c23).trans <|
  (Cover.dir c24)

end C4.Cert.Dir019
