module

public import C4Check

public section

/-! Cells `2953 ≤ n < 3003` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir076

theorem k2953_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2953) 3).1
      1175071138080969756649261007055442764667710418409443385790728440340880656493454296529287563419290049999322172).isSome = true := by
  decide +kernel

theorem k2953_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 2953) 3).2
      995127971294919670720411893209430373709226125645379094420121761899038900438173741675068).isSome = true := by
  decide +kernel

theorem k2954_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2954) 3).1
      3886692628785155779522708958110250408665562076748024618253501689469602170746405515836).isSome = true := by
  decide +kernel

theorem k2954_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 2954) 3).2
      971558582280941785075553599530106771693022156857566966959468644313373050437066411377).isSome = true := by
  decide +kernel

theorem c2 : allCells dirCell 2955 2972 [
    17918108445227482021687063861328664349991130322698084420605348974219884399192236327777699463012569429361,
    147547515966328869204, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] = true := by
  decide +kernel

theorem c3 : allCells dirCell 2972 2973 [
    26042574593331176482822327760177425410525889932637749923995497970552109493854528928309255667589297565718979462353009794617692452234627699487666808267] = true := by
  decide +kernel

theorem k2973_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2973) 3).1 2).1
      72841025246252960201353052168822329048420567356794399521866027713528967618170964564889440263333397005745).isSome = true := by
  decide +kernel

theorem k2973_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2973) 3).1 2).2
      208819281938529845338996211413711082661075264898899109018557756).isSome = true := by
  decide +kernel

theorem k2973_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2973) 3).2 2).1
      62988275576669640269496554040897400664923162152220682626938372001022374327288497427260).isSome = true := by
  decide +kernel

theorem k2973_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2973) 3).2 2).2
      63007996648474798123418961761920840793354157033521920308834124127580139038273953422514).isSome = true := by
  decide +kernel

theorem k2974_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2974) 3).1 2).1
      251526235232903883915668790892305588507317500470726227143813363974516201570923730956860).isSome = true := by
  decide +kernel

theorem k2974_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2974) 3).1 2).2
      852154146490758222974895993504083991451634294850806426660737774140).isSome = true := by
  decide +kernel

theorem k2974_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2974) 3).2 2).1
      1004285330313484399881030053689119158798879786085218857720834595660047507446004811938876).isSome = true := by
  decide +kernel

theorem k2974_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2974) 3).2 2).2
      850656694047198585319016025066714226486866394382685096969084714044).isSome = true := by
  decide +kernel

theorem k2975_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2975) 2).1 3).1
      217429359385591012939565449268103987064372008413075202436841566551100).isSome = true := by
  decide +kernel

theorem k2975_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2975) 2).1 3).2
      4005839524238876909452489327219071529517156776542398862949113414134438839438264468552764).isSome = true := by
  decide +kernel

theorem k2975_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2975) 2).2 1).1
      1002105566465743673980514393672133674213881724895713829848172533388425893157949215816764).isSome = true := by
  decide +kernel

theorem k2975_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2975) 2).2 1).2
      217293374764421408354354664703785735461861883687759056391644109290556).isSome = true := by
  decide +kernel

theorem k2976_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2976) 2).1 3).1
      867624658653162952983507601467343904947856380027794544223657004842044).isSome = true := by
  decide +kernel

theorem k2976_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2976) 2).1 3).2
      216816039844339817240895406927898994013330072217169116690677561506876).isSome = true := by
  decide +kernel

theorem k2976_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2976) 2).2 3).1
      216923810851707152353185304047688336977148076739723162274785672248380).isSome = true := by
  decide +kernel

theorem k2976_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2976) 2).2 3).2
      54182327621389973693063133122968845074353150525057506414843745483836).isSome = true := by
  decide +kernel

theorem k2977_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2977) 2).1 3).1
      216543140988384631079496088246619978237561338179420739157140814642236).isSome = true := by
  decide +kernel

theorem k2977_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2977) 2).1 3).2
      216396921577950554881109775625684895704463500091446195796368760716348).isSome = true := by
  decide +kernel

theorem k2977_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2977) 2).2 3).1
      54167403611143963739856878805137511584605994044704781040810338761788).isSome = true := by
  decide +kernel

theorem k2977_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2977) 2).2 3).2
      54103197121055589216687447334211777598679496064843772760230869548092).isSome = true := by
  decide +kernel

theorem k2978_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2978) 2).1 3).1
      216273425677534107415113661828915463625484335508985111333888760429628).isSome = true := by
  decide +kernel

theorem k2978_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2978) 2).1 3).2
      216165274127203719153794772708354253212866375885681443150124888570940).isSome = true := by
  decide +kernel

theorem k2978_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2978) 2).2 3).1
      46898220352491388295258708442573704185167286582332).isSome = true := by
  decide +kernel

theorem k2978_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2978) 2).2 3).2
      46874754044906014707762704014493018152786767592508).isSome = true := by
  decide +kernel

theorem k2979_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2979) 3).1
      5691999844202923249269752274348746436318398553183447084924366076873437790686196262812501174487130868447842190320359270370265627607868).isSome = true := by
  decide +kernel

theorem k2979_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2979) 3).2 1).1
      45738606931505864534318630039535925982259461180).isSome = true := by
  decide +kernel

theorem k2979_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2979) 3).2 1).2
      182970012658408478158271955766702319806326389820).isSome = true := by
  decide +kernel

theorem k2980_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2980) 1).1
      73506037053345063030262701019717209415659752465164976644031167561711267469489925954566785366042132726266940).isSome = true := by
  decide +kernel

theorem k2980_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 2980) 1).2
      4078015922436600489258672771777575436283248968448087728272383070361839537863694162782908659).isSome = true := by
  decide +kernel

theorem k2981_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2981) 1).1
      3371937361999353454889120421994100719496117660221501703624200745532).isSome = true := by
  decide +kernel

theorem k2981_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 2981) 1).2
      995319099570349739533408378514449048969279874970242053350093736461868319891975266824764).isSome = true := by
  decide +kernel

theorem k2982_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2982) 1).1
      205738440542591355787476061758553029622599683799666721844190636).isSome = true := by
  decide +kernel

theorem k2982_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 2982) 1).2
      3886606121240024388153167592661359081294290044468782945362027169054080604527144596028).isSome = true := by
  decide +kernel

theorem c14 : allCells dirCell 2983 3000 [
    17918068261975788826676519655070486934197757050530768442641345026052528106940820779440614775916583328113,
    147546063511504337460, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] = true := by
  decide +kernel

theorem c15 : allCells dirCell 3000 3001 [
    837516498357129344728206256958180501432837870325029048750951699] = true := by
  decide +kernel

theorem k3001_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3001) 3).1
      72734166720945217317928003915280858426757920195629027414728756050163456767660393130516028661544744744178).isSome = true := by
  decide +kernel

theorem k3001_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 3001) 3).2
      1371912280418084079164967552724607339038998860541207759324981235529357366958512094544092941272117784877144744488369570178259186).isSome = true := by
  decide +kernel

theorem k3002_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3002) 3).1
      87580986626186149310597831363278225392879014248798748501873803612571338988224027743852212211094196851444349958437843779448074482).isSome = true := by
  decide +kernel

theorem k3002_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3002) 3).2 2).1
      212661624518102724789899954606337202342665895647514488029851778108).isSome = true := by
  decide +kernel

theorem k3002_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3002) 3).2 2).2
      980669426361966508161609042353538556301073288340946548168417015103900996010044652604).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 2953 3003 :=
  (Cover.one (box := dirCellBox) (n := 2953)
      (.split 3 (.leaf _ k2953_0) (.leaf _ k2953_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 2954)
      (.split 3 (.leaf _ k2954_0) (.leaf _ k2954_1))).trans <|
  (Cover.dir c2).trans <|
  (Cover.dir c3).trans <|
  (Cover.one (box := dirCellBox) (n := 2973)
      (.split 3 (.split 2 (.leaf _ k2973_0) (.leaf _ k2973_1)) (.split 2 (.leaf _ k2973_2) (.leaf _ k2973_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 2974)
      (.split 3 (.split 2 (.leaf _ k2974_0) (.leaf _ k2974_1)) (.split 2 (.leaf _ k2974_2) (.leaf _ k2974_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 2975)
      (.split 2 (.split 3 (.leaf _ k2975_0) (.leaf _ k2975_1)) (.split 1 (.leaf _ k2975_2) (.leaf _ k2975_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 2976)
      (.split 2 (.split 3 (.leaf _ k2976_0) (.leaf _ k2976_1)) (.split 3 (.leaf _ k2976_2) (.leaf _ k2976_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 2977)
      (.split 2 (.split 3 (.leaf _ k2977_0) (.leaf _ k2977_1)) (.split 3 (.leaf _ k2977_2) (.leaf _ k2977_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 2978)
      (.split 2 (.split 3 (.leaf _ k2978_0) (.leaf _ k2978_1)) (.split 3 (.leaf _ k2978_2) (.leaf _ k2978_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 2979)
      (.split 3 (.leaf _ k2979_0) (.split 1 (.leaf _ k2979_1) (.leaf _ k2979_2)))).trans <|
  (Cover.one (box := dirCellBox) (n := 2980)
      (.split 1 (.leaf _ k2980_0) (.leaf _ k2980_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 2981)
      (.split 1 (.leaf _ k2981_0) (.leaf _ k2981_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 2982)
      (.split 1 (.leaf _ k2982_0) (.leaf _ k2982_1))).trans <|
  (Cover.dir c14).trans <|
  (Cover.dir c15).trans <|
  (Cover.one (box := dirCellBox) (n := 3001)
      (.split 3 (.leaf _ k3001_0) (.leaf _ k3001_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 3002)
      (.split 3 (.leaf _ k3002_0) (.split 2 (.leaf _ k3002_1) (.leaf _ k3002_2))))

end C4.Cert.Dir076
