module

public import C4Check

public section

/-! Cells `4881 ≤ n < 4910` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir150

theorem k4881_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4881) 2).1 3).1
      243600004142777326432863119473887293686366131334151945012459486955245876178207596332).isSome = true := by
  decide +kernel

theorem k4881_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4881) 2).1 3).2
      211169752712118924884336343792551664535465200071378035230236957873).isSome = true := by
  decide +kernel

theorem k4881_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4881) 2).2 3).1
      211319840568558813411004595171392386360035321891071050320100768828).isSome = true := by
  decide +kernel

theorem k4881_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4881) 2).2 3).2
      974079941002424670015235775554357482148822125950173032777747236207659240765079256124).isSome = true := by
  decide +kernel

theorem k4882_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4882) 2).1
      1356486451099114611673604362696380277282560849396921960745029225959206185750982238263643796472949541420020103116227307938116275).isSome = true := by
  decide +kernel

theorem k4882_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4882) 2).2 3).1
      973661173483921377933865611941503200432766394426182569676043393246591551673338788924).isSome = true := by
  decide +kernel

theorem k4882_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4882) 2).2 3).2
      13190822951181541803877769469723684511894778884664634280420700732).isSome = true := by
  decide +kernel

theorem k4883_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4883) 2).1
      338942298184772314264901280535167684418646688466283487353618702975305711044411058669753831677380837939396618378142504043508979).isSome = true := by
  decide +kernel

theorem k4883_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4883) 2).2
      15937627938801684673427126962055720809678340530106961221931126102674887079764862771251443).isSome = true := by
  decide +kernel

theorem k4884_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4884) 2).1
      338836153120286209672770473100781004906386280405331209083382957522233566312634767868880650901872337620104470551516104728868081).isSome = true := by
  decide +kernel

theorem k4884_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4884) 2).2
      338834772316423408878551129805436576703872238521662070236585051418924905766140351657738092088574679772317266987715233252209907).isSome = true := by
  decide +kernel

theorem k4885_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4885) 2).1
      71730893977203554684645852879285000819720413970429705144515255699475650713000884815094236987755867501809).isSome = true := by
  decide +kernel

theorem k4885_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4885) 2).2
      5293101803239338975758208138633612665127245588323134451899193944455845902070696206495044226990241553156069557567869460928316).isSome = true := by
  decide +kernel

theorem k4886_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4886) 2).1
      60745520932336336225019460297522772014710013518992986092156913911844602835671307516).isSome = true := by
  decide +kernel

theorem k4886_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4886) 2).2
      71717483015734504294927972515234820433808699510616657336458445045393456001257490983852458406886999284924).isSome = true := by
  decide +kernel

theorem c6 : allCells dirCell 4887 4888 [
    1843608409048135502995803054198334938053420803541768458529152913003790461608947953184528103196117104848605123482997340900413636488605865520269023374676992724355347954] = true := by
  decide +kernel

theorem c7 : allCells dirCell 4888 4889 [
    1322541432067753600356089683680487109076639250634938686630763569833039352608754360422609992469085737159795823370256287588722] = true := by
  decide +kernel

theorem c8 : allCells dirCell 4889 4903 [
    51432812877543582160161803689178630281664201201146189768892306,
    174247476423435482941398358137871781169937, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] = true := by
  decide +kernel

theorem k4903_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4903) 3).1
      18448495594734859387049257990974463220339110717861700619799275263652327157661830915158826991082548136006).isSome = true := by
  decide +kernel

theorem k4903_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4903) 3).2
      260636735733159987813219837081663008914957100149898216874255806144246707026715262297150342).isSome = true := by
  decide +kernel

theorem k4904_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4904) 3).1
      4255435280572915851369989565700857991371854899124136393603342364090633940985994217009127405770).isSome = true := by
  decide +kernel

theorem k4904_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4904) 3).2 2).1
      1010960817438993540587890542798477178055010500946105839527625126105231428782155296764721).isSome = true := by
  decide +kernel

theorem k4904_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4904) 3).2 2).2
      15798488998433079709564157914979004183065524656045443924733639500874539491898124729548).isSome = true := by
  decide +kernel

theorem k4905_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4905) 2).1 3).1
      16126996092710935823693992230103571056735780798607728104819487615896020084860550999559729).isSome = true := by
  decide +kernel

theorem k4905_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4905) 2).1 3).2
      64381594663506574615203025748426422091186056774214163533842255597914009334810952666297137).isSome = true := by
  decide +kernel

theorem k4905_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4905) 2).2 3).1
      1008038413152880167893153272145031993004027058407555571109070176864997252700300303758129).isSome = true := by
  decide +kernel

theorem k4905_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4905) 2).2 3).2
      4024493281512763858100482260026766703914250128974726837076125801554424181210100330253873).isSome = true := by
  decide +kernel

theorem k4906_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4906) 2).1 3).1
      16070998853081116655636204199355031851847372076317111139119937799080458006627845605536561).isSome = true := by
  decide +kernel

theorem k4906_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4906) 2).1 3).2
      1183884013076480508114871688235991625317537194813445618029158435794295981745054507768384495581222081584821041).isSome = true := by
  decide +kernel

theorem k4906_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4906) 2).2 3).1
      4017553485511713697699486914545603614702967280424564403843157212360490807369939122762545).isSome = true := by
  decide +kernel

theorem k4906_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4906) 2).2 3).2
      4011990116560731062127264610604224321987518877095343550897175673463996828160024820167473).isSome = true := by
  decide +kernel

theorem k4907_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4907) 2).1 3).1
      64091887613896856167560073465146426353659010989113321366018336358787775977614628159343409).isSome = true := by
  decide +kernel

theorem k4907_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4907) 2).1 3).2
      64028330006778637943950719130984849418479170086945712676272253429479889969809524526623538).isSome = true := by
  decide +kernel

theorem k4907_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4907) 2).2 3).1
      1001645746352930451717052601373987822537393498307094333924663766339194397918370211656497).isSome = true := by
  decide +kernel

theorem k4907_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4907) 2).2 3).2
      1000525572292084486389658254097258103783859795906807784426356167767549143650776602735409).isSome = true := by
  decide +kernel

theorem k4908_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4908) 2).1 3).1
      1152337716775303287729472547609688427249973256756118772469215261229828484842961504357301923960157554830028).isSome = true := by
  decide +kernel

theorem k4908_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4908) 2).1 3).2
      3901293435897176828354869663863142361419342617859571299942051408104733337036864871116).isSome = true := by
  decide +kernel

theorem k4908_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4908) 2).2 3).1
      62478926671295618628840349851834446365363710657593653085209848384257616184207495604940).isSome = true := by
  decide +kernel

theorem k4908_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4908) 2).2 3).2
      846083375835286346289887826115575339588100979796173476550234024652).isSome = true := by
  decide +kernel

theorem k4909_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4909) 2).1
      86900590170623241418256024697722378363827011612383018269661691914795757050812984606640199467694856490156046384408652352125889331).isSome = true := by
  decide +kernel

theorem k4909_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4909) 2).2 3).1
      974850188623389998910664727889635316462396429466874801271266303783715888439431256780).isSome = true := by
  decide +kernel

theorem k4909_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4909) 2).2 3).2
      825287398106340562212678107795060027675871376112431855782688460).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 4881 4910 :=
  (Cover.one (box := dirCellBox) (n := 4881)
      (.split 2 (.split 3 (.leaf _ k4881_0) (.leaf _ k4881_1)) (.split 3 (.leaf _ k4881_2) (.leaf _ k4881_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 4882)
      (.split 2 (.leaf _ k4882_0) (.split 3 (.leaf _ k4882_1) (.leaf _ k4882_2)))).trans <|
  (Cover.one (box := dirCellBox) (n := 4883)
      (.split 2 (.leaf _ k4883_0) (.leaf _ k4883_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 4884)
      (.split 2 (.leaf _ k4884_0) (.leaf _ k4884_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 4885)
      (.split 2 (.leaf _ k4885_0) (.leaf _ k4885_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 4886)
      (.split 2 (.leaf _ k4886_0) (.leaf _ k4886_1))).trans <|
  (Cover.dir c6).trans <|
  (Cover.dir c7).trans <|
  (Cover.dir c8).trans <|
  (Cover.one (box := dirCellBox) (n := 4903)
      (.split 3 (.leaf _ k4903_0) (.leaf _ k4903_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 4904)
      (.split 3 (.leaf _ k4904_0) (.split 2 (.leaf _ k4904_1) (.leaf _ k4904_2)))).trans <|
  (Cover.one (box := dirCellBox) (n := 4905)
      (.split 2 (.split 3 (.leaf _ k4905_0) (.leaf _ k4905_1)) (.split 3 (.leaf _ k4905_2) (.leaf _ k4905_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 4906)
      (.split 2 (.split 3 (.leaf _ k4906_0) (.leaf _ k4906_1)) (.split 3 (.leaf _ k4906_2) (.leaf _ k4906_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 4907)
      (.split 2 (.split 3 (.leaf _ k4907_0) (.leaf _ k4907_1)) (.split 3 (.leaf _ k4907_2) (.leaf _ k4907_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 4908)
      (.split 2 (.split 3 (.leaf _ k4908_0) (.leaf _ k4908_1)) (.split 3 (.leaf _ k4908_2) (.leaf _ k4908_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 4909)
      (.split 2 (.leaf _ k4909_0) (.split 3 (.leaf _ k4909_1) (.leaf _ k4909_2))))

end C4.Cert.Dir150
