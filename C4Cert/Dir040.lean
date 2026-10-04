module

public import C4Check

public section

/-! Cells `2385 ≤ n < 2410` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir040

theorem k2385_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2385) 2).1 3).1 3).1 2).1
      5464322485867193035615927576729231213436280980351213293052166027714964969012842647202361767277057861525007305616249193409927985).isSome = true := by
  decide +kernel

theorem k2385_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2385) 2).1 3).1 3).1 2).2
      5467540614784645714651360216412848709421580787022611958840574874210914247405224061131118512057307794228060089375158621533756209).isSome = true := by
  decide +kernel

theorem k2385_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2385) 2).1 3).1 3).2 2).1
      4623909109629443140137139347348580403183483975670489806356154623605341518363457266553359273374179665500977).isSome = true := by
  decide +kernel

theorem k2385_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2385) 2).1 3).1 3).2 2).2
      74014306719375422397950364203633536111531685420270828867878318855151561446018607186153729968681576232770353).isSome = true := by
  decide +kernel

theorem k2385_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2385) 2).1 3).2 2).1 1).1
      3910943999079215321850556891935510192485139626230559427616185491207501364765677262643).isSome = true := by
  decide +kernel

theorem k2385_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2385) 2).1 3).2 2).1 1).2
      3910090231439664933237421408173019394251405998486303579886735081757067716358977083187).isSome = true := by
  decide +kernel

theorem k2385_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2385) 2).1 3).2 2).2 1).1
      4619186700750820581806223040968879982459116926429554928881345869047448395412902348405719864422069017369395).isSome = true := by
  decide +kernel

theorem k2385_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2385) 2).1 3).2 2).2 1).2
      3911541459127267082298933434474003320025452027504187829894400189950889432577910888243).isSome = true := by
  decide +kernel

theorem k2385_8 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2385) 2).2 3).1 1).1 3).1
      5476051596917235171359433991252699446657890177970338939396030832999178335548771875928834188779703944635058839307386142305147698).isSome = true := by
  decide +kernel

theorem k2385_9 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2385) 2).2 3).1 1).1 3).2
      5468894535814916061111276017407260739542975882275832810509422538621736680588891029897603791152841121382768736843542945840094002).isSome = true := by
  decide +kernel

theorem k2385_10 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2385) 2).2 3).1 1).2 3).1
      1187166837450517954586761500428834710059302645826746260268134289792335595047213106382512115193849189588392754).isSome = true := by
  decide +kernel

theorem k2385_11 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2385) 2).2 3).1 1).2 3).2
      5467620783063497531880056871418115035782038977274737959215085580151165880463125363933856850710357376493635493845944164113832754).isSome = true := by
  decide +kernel

theorem k2385_12 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2385) 2).2 3).2 1).1 3).1
      5462839366631303973306020097771671121651403231899641267324698641283574925770954567413102754371922432410752086679293219814366002).isSome = true := by
  decide +kernel

theorem k2385_13 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2385) 2).2 3).2 1).1 3).2
      5457397708749543452973829605951019775314950719208973054899632579414594798227159524927016246480738568372851178181774288614710066).isSome = true := by
  decide +kernel

theorem k2385_14 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2385) 2).2 3).2 1).2 3).1
      74014399780213663748376332583754921856135641216240999270686415523609724512765853832923237210577493200575282).isSome = true := by
  decide +kernel

theorem k2385_15 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2385) 2).2 3).2 1).2 3).2
      250523997960803735163947015358878001634674578449438070028219518894081739620569292561202).isSome = true := by
  decide +kernel

theorem k2386_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2386) 2).1 3).1 2).1
      5573303590811097318994173337159902853107547350803861940786040567772476134061242600497452757109721126563180843260727719779703020749).isSome = true := by
  decide +kernel

theorem k2386_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2386) 2).1 3).1 2).2 1).1
      244751631778433175520320099112243672796014152892908246984384695239642902819000245196).isSome = true := by
  decide +kernel

theorem k2386_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2386) 2).1 3).1 2).2 1).2
      3906278708670835558119717351409350585988258975753232240095449730649846750892276619059).isSome = true := by
  decide +kernel

theorem k2386_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2386) 2).1 3).2 2).1
      18450547888167354610484327217047912053160312645659243972324626299778053301892781924856018555222130184176845).isSome = true := by
  decide +kernel

theorem k2386_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2386) 2).1 3).2 2).2
      4717179907078548342362832428123061708177292030210868981697702647788706497150182036320223858614051188059036877).isSome = true := by
  decide +kernel

theorem k2386_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2386) 2).2 3).1 1).1 3).1
      250319802085111879107847340418711739482464201469866107248792180672177398129359694286540).isSome = true := by
  decide +kernel

theorem k2386_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2386) 2).2 3).1 1).1 3).2
      15636141889060364339217661668276561889685668130161232034157574942813973751515100976946).isSome = true := by
  decide +kernel

theorem k2386_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2386) 2).2 3).1 1).2 3).1
      15644596216875967127097827290210100059214242513121413642693571655881206519992158770994).isSome = true := by
  decide +kernel

theorem k2386_8 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2386) 2).2 3).1 1).2 3).2
      244275838126410836167363519023855934597224277407464401536619406923439634352663125708).isSome = true := by
  decide +kernel

theorem k2386_9 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2386) 2).2 3).2 1).1
      5441329764792257646423610897484023947269858660330044294611728072729403072192614325969250424138328945421771371854349546393295667).isSome = true := by
  decide +kernel

theorem k2386_10 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2386) 2).2 3).2 1).2
      1392790178337035459330291275380427348929854469223153264533211007285979702098101948431589815979404566909022815652948866996715204403).isSome = true := by
  decide +kernel

theorem k2387_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2387) 2).1 3).1 1).1
      3899422398532575634184238944037402732934375686197446792740318532158722729771281979187).isSome = true := by
  decide +kernel

theorem k2387_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2387) 2).1 3).1 1).2
      17988201185068695771536572089721837905201307066446665969787475053347505452777643723784165464037049735538).isSome = true := by
  decide +kernel

theorem k2387_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2387) 2).1 3).2
      6263878552416653412863893395701556138900854152404667810340285224424497978467174215104312930237297801538995639119514009965472181797191548521821641).isSome = true := by
  decide +kernel

theorem k2387_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2387) 2).2 3).1 1).1
      18419297423861288379002961298012999566815439601031141510350063050022986987258127999034256547998594843925299).isSome = true := by
  decide +kernel

theorem k2387_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2387) 2).2 3).1 1).2
      15601246929787551172039526194312825258789510874990054234294522207103760790800913554227).isSome = true := by
  decide +kernel

theorem k2387_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2387) 2).2 3).2 1).1
      3897788747658370885712620482647087245645245587238905574723930924268975851169218664243).isSome = true := by
  decide +kernel

theorem k2387_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2387) 2).2 3).2 1).2
      3897616769267756198456318047881209932759765169353785926807130264088410506980441380659).isSome = true := by
  decide +kernel

theorem k2388_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2388) 2).1
      104979994837315851463331535068018216326460999512322178652170010010251832042284894856986296593582784013879215483581193634400864558836694183043236744508702).isSome = true := by
  decide +kernel

theorem k2388_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2388) 2).2 3).1
      88952057777277841416779203437746665700022456830352033398058626668522999583403869677841454317778794336403838868389956975906024479949).isSome = true := by
  decide +kernel

theorem k2388_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2388) 2).2 3).2
      18392041263830125954884966152614054020539066671553430167967965972501222968289528148084434463135867424412877).isSome = true := by
  decide +kernel

theorem k2389_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2389) 2).1
      79185605806112720552936710).isSome = true := by
  decide +kernel

theorem k2389_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2389) 2).2 3).1
      17952951650206915197809164141615361543558340072962300794302959214127621463032938130098121568679308126537).isSome = true := by
  decide +kernel

theorem k2389_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2389) 2).2 3).2
      15201398079672836990951510103504051693327209985380915655034211579064728206289895793).isSome = true := by
  decide +kernel

theorem c5 : allCells dirCell 2390 2410 [
    632082626896231894077448774996201903515067511905035447122906924806, 1, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 338001239705958107937813216274866291] = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 2385 2410 :=
  (Cover.one (box := dirCellBox) (n := 2385)
      (.split 2 (.split 3 (.split 3 (.split 2 (.leaf _ k2385_0) (.leaf _ k2385_1)) (.split 2 (.leaf _ k2385_2) (.leaf _ k2385_3))) (.split 2 (.split 1 (.leaf _ k2385_4) (.leaf _ k2385_5)) (.split 1 (.leaf _ k2385_6) (.leaf _ k2385_7)))) (.split 3 (.split 1 (.split 3 (.leaf _ k2385_8) (.leaf _ k2385_9)) (.split 3 (.leaf _ k2385_10) (.leaf _ k2385_11))) (.split 1 (.split 3 (.leaf _ k2385_12) (.leaf _ k2385_13)) (.split 3 (.leaf _ k2385_14) (.leaf _ k2385_15)))))).trans <|
  (Cover.one (box := dirCellBox) (n := 2386)
      (.split 2 (.split 3 (.split 2 (.leaf _ k2386_0) (.split 1 (.leaf _ k2386_1) (.leaf _ k2386_2))) (.split 2 (.leaf _ k2386_3) (.leaf _ k2386_4))) (.split 3 (.split 1 (.split 3 (.leaf _ k2386_5) (.leaf _ k2386_6)) (.split 3 (.leaf _ k2386_7) (.leaf _ k2386_8))) (.split 1 (.leaf _ k2386_9) (.leaf _ k2386_10))))).trans <|
  (Cover.one (box := dirCellBox) (n := 2387)
      (.split 2 (.split 3 (.split 1 (.leaf _ k2387_0) (.leaf _ k2387_1)) (.leaf _ k2387_2)) (.split 3 (.split 1 (.leaf _ k2387_3) (.leaf _ k2387_4)) (.split 1 (.leaf _ k2387_5) (.leaf _ k2387_6))))).trans <|
  (Cover.one (box := dirCellBox) (n := 2388)
      (.split 2 (.leaf _ k2388_0) (.split 3 (.leaf _ k2388_1) (.leaf _ k2388_2)))).trans <|
  (Cover.one (box := dirCellBox) (n := 2389)
      (.split 2 (.leaf _ k2389_0) (.split 3 (.leaf _ k2389_1) (.leaf _ k2389_2)))).trans <|
  (Cover.dir c5)

end C4.Cert.Dir040
