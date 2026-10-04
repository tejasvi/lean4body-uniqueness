module

public import C4Check

public section

/-! Cells `1742 ≤ n < 1773` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir017

theorem k1742_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1742) 3).1 2).1
      1368721973736046476602794038222589930034174114163878667411009601339404679723843708477897877180419293778327596629764336029365489).isSome = true := by
  decide +kernel

theorem k1742_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1742) 3).1 2).2
      1159440139066310971455435108023839015245906031253088823726861569407205525250587393952009587512782950339825).isSome = true := by
  decide +kernel

theorem k1742_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1742) 3).2 2).1
      21853929115185014401143684407600743876311750767789069358186638816045808657544152635835356970801294273005396915645226296603270577).isSome = true := by
  decide +kernel

theorem k1742_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1742) 3).2 2).2
      85385687553453853295578842106982526633062839128008297402145109024541963337503853772980916913753230928958150498949516356705713).isSome = true := by
  decide +kernel

theorem k1743_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1743) 3).1 2).1
      87283793631651978311182012086870846503801302754289382369774253783593701624712874474506315479667003965237208765384986434457664689).isSome = true := by
  decide +kernel

theorem k1743_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1743) 3).1 2).2
      295749694780010261285626347217088096525860194057857633865091766816314902972272498110496545159834894718753969).isSome = true := by
  decide +kernel

theorem k1743_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1743) 3).2 2).1
      18898646319050443043108980526624980914839158533750455487402629512795674825110399344705213865295255210087115569).isSome = true := by
  decide +kernel

theorem k1743_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1743) 3).2 2).2
      302404419572779205767295844890188469165853636106324628718699386169576679940187005542215606172066597632674754801).isSome = true := by
  decide +kernel

theorem k1744_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1744) 3).1 2).1
      5441560056628892530104361974487534975032248452562050959625097988920310934286091389196818538198420276444158312586104466434284337).isSome = true := by
  decide +kernel

theorem k1744_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1744) 3).1 2).2
      5441986851596062236621343386321093830226876582290621583386758798540503345171528182170497941586622467585890517136351828884446001).isSome = true := by
  decide +kernel

theorem k1744_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1744) 3).2 2).1
      255817704727648027143268911087838101965742333205089104916777129774556096530988738232658737).isSome = true := by
  decide +kernel

theorem k1744_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1744) 3).2 2).2
      5437274485132266134725292300204667543128309801495499211206835447272589328578035912857670929381208835828064654451771455099493169).isSome = true := by
  decide +kernel

theorem k1745_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1745) 3).1 2).1
      4711568233225658852168505650620466708020536548702128523177752112596910127784326447352177779009339793394223921).isSome = true := by
  decide +kernel

theorem k1745_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1745) 3).1 2).2
      15978542549225067108779310360250182778659869813350419354208032560138786618971184535292721).isSome = true := by
  decide +kernel

theorem k1745_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1745) 3).2 2).1
      15951322382024702294182643935032011038803169737161672826509962318325374195700824111674161).isSome = true := by
  decide +kernel

theorem k1745_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1745) 3).2 2).2
      15952346006329472501997108538271376900894230449389733768461894795247202910806933930101553).isSome = true := by
  decide +kernel

theorem k1746_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1746) 3).1 1).1
      287457700426405780152783154520439750001692814906847036052707199462947348184354627206962600423344576125644).isSome = true := by
  decide +kernel

theorem k1746_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1746) 3).1 1).2
      15942755027242318099681906352179915454586818320069165159082915628615180237037880021994290).isSome = true := by
  decide +kernel

theorem k1746_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1746) 3).2 2).1
      995894039251281498844737509424119838195653063861540176553423255344162512889380632288049).isSome = true := by
  decide +kernel

theorem k1746_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1746) 3).2 2).2
      248983218169016513625797565390080244081517347845738317037662698663164380549986848533564).isSome = true := by
  decide +kernel

theorem k1747_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 1747) 3).1
      86730756967908898086836870530619651097200586997410501255320290378728370809775021507715381119981138132051901919677774973996846897).isSome = true := by
  decide +kernel

theorem k1747_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 1747) 3).2
      73436299366351604934168425667143701573407190820533001241701944269831195360762130881012290511525543739677873).isSome = true := by
  decide +kernel

theorem c6 : allCells dirCell 1748 1749 [
    399621394862799179847759606547785366158049170039164618672758223393354326830439733321446786087541905560930458776163073681192509213960055234919167431] = true := by
  decide +kernel

theorem c7 : allCells dirCell 1749 1769 [
    2360388895407917617729, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    728137090514602602863538128613500094120956003] = true := by
  decide +kernel

theorem k1769_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 1769) 3).1
      21501728077518725257988475072976040001153680197639506954320998590134294660934522290766125413463293727331203620597408611020358).isSome = true := by
  decide +kernel

theorem k1769_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 1769) 3).2
      1867569964688279324805605059886203585433046087177325176588829094021182673666978397277240504877130584140106319114878426841650880364788884539715497166104466809865082310).isSome = true := by
  decide +kernel

theorem k1770_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1770) 3).1 2).1
      72466231310609562522430368309909376513617104580546937301257902844753489060614183762820133417555257081201).isSome = true := by
  decide +kernel

theorem k1770_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1770) 3).1 2).2
      72465302790378629726608804466031436232440881523099220184664618112709940617512222974166839016631949091185).isSome = true := by
  decide +kernel

theorem k1770_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1770) 3).2 2).1
      21348804793644489795562602513321494147768202853248684845254166512020149183734958545721169569360127643465169677010031744998833).isSome = true := by
  decide +kernel

theorem k1770_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1770) 3).2 2).2
      5337549425953953212660019863901061844057531956069812405163270138068398654139936967622580686220768504252079085566191220545340).isSome = true := by
  decide +kernel

theorem k1771_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1771) 3).1 2).1
      340996674972997015816027189147685749018601716387227066785757141659336218822245356269863310330088372032988396281842969866101564).isSome = true := by
  decide +kernel

theorem k1771_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1771) 3).1 2).2
      250529758734584874996501044362556234291512479589778075455839285316997924185226369524540).isSome = true := by
  decide +kernel

theorem k1771_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1771) 3).2 2).1
      21792784534756193652175638895251637023868534555450070837900914776184073273064972469416394772116510838401755238222308840919790140).isSome = true := by
  decide +kernel

theorem k1771_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1771) 3).2 2).2
      295400890489404618315922877271857448230383529158340953235608464073001432538031122943822876162959376510185713).isSome = true := by
  decide +kernel

theorem k1772_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1772) 3).1 2).1
      73753148129019543188145418108373039547710582671891831588786965259580048329052252479243010479240817023958076).isSome = true := by
  decide +kernel

theorem k1772_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1772) 3).1 2).2
      15994202678968977491306107252695729788257653516345596535583193328809174957795466139507505).isSome = true := by
  decide +kernel

theorem k1772_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1772) 3).2 2).1
      63907709168781645474060224213800543549219656328195718729484775216649359927738194880838716).isSome = true := by
  decide +kernel

theorem k1772_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1772) 3).2 2).2
      18423031479631674816444367540166339608584902570634435616606456190691771711475412344311063680370019126426684).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 1742 1773 :=
  (Cover.one (box := dirCellBox) (n := 1742)
      (.split 3 (.split 2 (.leaf _ k1742_0) (.leaf _ k1742_1)) (.split 2 (.leaf _ k1742_2) (.leaf _ k1742_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 1743)
      (.split 3 (.split 2 (.leaf _ k1743_0) (.leaf _ k1743_1)) (.split 2 (.leaf _ k1743_2) (.leaf _ k1743_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 1744)
      (.split 3 (.split 2 (.leaf _ k1744_0) (.leaf _ k1744_1)) (.split 2 (.leaf _ k1744_2) (.leaf _ k1744_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 1745)
      (.split 3 (.split 2 (.leaf _ k1745_0) (.leaf _ k1745_1)) (.split 2 (.leaf _ k1745_2) (.leaf _ k1745_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 1746)
      (.split 3 (.split 1 (.leaf _ k1746_0) (.leaf _ k1746_1)) (.split 2 (.leaf _ k1746_2) (.leaf _ k1746_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 1747)
      (.split 3 (.leaf _ k1747_0) (.leaf _ k1747_1))).trans <|
  (Cover.dir c6).trans <|
  (Cover.dir c7).trans <|
  (Cover.one (box := dirCellBox) (n := 1769)
      (.split 3 (.leaf _ k1769_0) (.leaf _ k1769_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 1770)
      (.split 3 (.split 2 (.leaf _ k1770_0) (.leaf _ k1770_1)) (.split 2 (.leaf _ k1770_2) (.leaf _ k1770_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 1771)
      (.split 3 (.split 2 (.leaf _ k1771_0) (.leaf _ k1771_1)) (.split 2 (.leaf _ k1771_2) (.leaf _ k1771_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 1772)
      (.split 3 (.split 2 (.leaf _ k1772_0) (.leaf _ k1772_1)) (.split 2 (.leaf _ k1772_2) (.leaf _ k1772_3))))

end C4.Cert.Dir017
