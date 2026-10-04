module

public import C4Check

public section

/-! Cells `2077 ≤ n < 2082` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir027

theorem k2077_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2077) 3).1 2).1 3).1
      88062689807012223069999752919855958028546904214849136714668407158559833095744880488853098699061463844482218540215296020890350833).isSome = true := by
  decide +kernel

theorem k2077_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2077) 3).1 2).1 3).2
      101356461412098059915622242136671733690231928462383718817949366974877221836425694978852131921277049364227076829043975540323752832397820128504536497).isSome = true := by
  decide +kernel

theorem k2077_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2077) 3).1 2).2 1).1
      343898245959233471059519425073520079338905153474901049844383451388757278061272968745475192578945533578489883080810539071665394).isSome = true := by
  decide +kernel

theorem k2077_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2077) 3).1 2).2 1).2
      297992638786443646209531487315679589409756709553048587096562129024560229937760286117595592113333254354007283).isSome = true := by
  decide +kernel

theorem k2077_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2077) 3).2 2).1 1).1 3).1
      15391828312211756052820592028187975577807235608207002047352746241673929072922681196).isSome = true := by
  decide +kernel

theorem k2077_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2077) 3).2 2).1 1).1 3).2
      13316709809635726814230057593969514311181485664999914183797079212).isSome = true := by
  decide +kernel

theorem k2077_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2077) 3).2 2).1 1).2
      350891485809556165945735032309319505392130903761635478235793709969336153937290281193985864736573537707539271001695107775723044018).isSome = true := by
  decide +kernel

theorem k2077_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2077) 3).2 2).2 1).1
      4646069432624182955258471370393784706219475837683573345515928033903095357107374138186115103138225968864691).isSome = true := by
  decide +kernel

theorem k2077_8 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2077) 3).2 2).2 1).2 2).1
      13330413666747444661138100051702506976874096156275395154476104876).isSome = true := by
  decide +kernel

theorem k2077_9 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2077) 3).2 2).2 1).2 2).2
      13332834071817479323728659635772415190292465240473536928495008940).isSome = true := by
  decide +kernel

theorem k2078_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2078) 3).1 2).1 1).1
      87463570796066231604544915570663639385759586405308091319191083479291170310720799669581695136921566662875881719477125288734325939).isSome = true := by
  decide +kernel

theorem k2078_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2078) 3).1 2).1 1).2
      75841845256562896345571511047910704473511065587869774804471765787438465592492763738799922673243006586781793459).isSome = true := by
  decide +kernel

theorem k2078_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2078) 3).1 2).2 1).1
      21873426342438412292178226924692707435987035551608170382310234758048702456171656473309250603120015966662601578037177247474220211).isSome = true := by
  decide +kernel

theorem k2078_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2078) 3).1 2).2 1).2
      18982837536491078223407760747117036450231255628024730385433810973559335028011045422722420549876443947761136188).isSome = true := by
  decide +kernel

theorem k2078_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2078) 3).2 2).1 1).1
      64129744016177417350898292726736092382680231502219328410522585626608387024677907950096179).isSome = true := by
  decide +kernel

theorem k2078_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2078) 3).2 2).1 1).2
      64131244444513259241345443806000671308121902867993640235808889950813451650713954571145011).isSome = true := by
  decide +kernel

theorem k2078_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2078) 3).2 2).2 1).1
      4009524034071151230777524402023290136528828994183720969093436156849404260654239670758195).isSome = true := by
  decide +kernel

theorem k2078_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2078) 3).2 2).2 1).2
      256618216043609292389121935169204374362861179331120813113367250206971329537613001737302259).isSome = true := by
  decide +kernel

theorem k2079_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2079) 3).1 2).1 1).1
      5450361796549103861168755705524534098043817663559082216805352150027737782747020017514622151420572307567912142022936995100482354).isSome = true := by
  decide +kernel

theorem k2079_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2079) 3).1 2).1 1).2
      1181401677073059226842968195318187045974669597889265551745373945618079090790440773597968574190371877310552883).isSome = true := by
  decide +kernel

theorem k2079_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2079) 3).1 2).2 1).1
      4617956519632319257363721851844146686970867753500099295969420170465733575910781449972548091415016529834956).isSome = true := by
  decide +kernel

theorem k2079_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2079) 3).1 2).2 1).2
      250344168563108372228602148032994917225390144517955388996258688660969783164343112027852).isSome = true := by
  decide +kernel

theorem k2079_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2079) 3).2 2).1 1).1
      63952865163658213475500020465682128485799582394495620217796460454317330723118767937104691).isSome = true := by
  decide +kernel

theorem k2079_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2079) 3).2 2).1 1).2
      64017453894690656506743067844959022688560216475787004378672389887063092002233229898099507).isSome = true := by
  decide +kernel

theorem k2079_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2079) 3).2 2).2 1).1
      3910237701743699276814854998708171898002947382167775677945545108948175875358544353996).isSome = true := by
  decide +kernel

theorem k2079_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2079) 3).2 2).2 1).2
      3910417912228913354585736592371480044457633669505283564485128271001528786705559575244).isSome = true := by
  decide +kernel

theorem k2080_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2080) 3).1 2).1 1).1
      54137278619700704839247434941816976076637315125071061070406696563404).isSome = true := by
  decide +kernel

theorem k2080_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2080) 3).1 2).1 1).2
      13534967282342968084721921273988145013900792925370388649671211610828).isSome = true := by
  decide +kernel

theorem k2080_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2080) 3).1 2).2 1).1
      211528881787242528291361461824506961174890282367666025757901572812).isSome = true := by
  decide +kernel

theorem k2080_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2080) 3).1 2).2 1).2
      211746881999647843264679413310119591142602823461025403648152685260).isSome = true := by
  decide +kernel

theorem k2080_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2080) 3).2 2).1 1).1
      845146548607912419066253342111139720175096528303574493132565429452).isSome = true := by
  decide +kernel

theorem k2080_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2080) 3).2 2).1 1).2
      846168594943448526491087347025057305361161618940358365397470540492).isSome = true := by
  decide +kernel

theorem k2080_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2080) 3).2 2).2 1).1
      845477381293703882461492596372498544381252906887855202669268693708).isSome = true := by
  decide +kernel

theorem k2080_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2080) 3).2 2).2 1).2
      52897180055277836849418723259338552149195602644957149405898994380).isSome = true := by
  decide +kernel

theorem k2081_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2081) 3).1 2).1
      22241291422803906715923313873725355692032365795215665615753939805048524712632533051687279136121807841641755459799609099002825732913).isSome = true := by
  decide +kernel

theorem k2081_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2081) 3).1 2).2
      4823003663096358049524827165270305669517197877063830097368844957802222642599821528305009194280724432401544311601).isSome = true := by
  decide +kernel

theorem k2081_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2081) 3).2 2).1
      5557259754743885830495345087295709961049670449538935331830387922460294661248995065134146323037300217420458069338308799336068002609).isSome = true := by
  decide +kernel

theorem k2081_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2081) 3).2 2).2
      301268476192798277387627362652726510612566577895917308743508447847104249022239271745127785929949507599351001905).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 2077 2082 :=
  (Cover.one (box := dirCellBox) (n := 2077)
      (.split 3 (.split 2 (.split 3 (.leaf _ k2077_0) (.leaf _ k2077_1)) (.split 1 (.leaf _ k2077_2) (.leaf _ k2077_3))) (.split 2 (.split 1 (.split 3 (.leaf _ k2077_4) (.leaf _ k2077_5)) (.leaf _ k2077_6)) (.split 1 (.leaf _ k2077_7) (.split 2 (.leaf _ k2077_8) (.leaf _ k2077_9)))))).trans <|
  (Cover.one (box := dirCellBox) (n := 2078)
      (.split 3 (.split 2 (.split 1 (.leaf _ k2078_0) (.leaf _ k2078_1)) (.split 1 (.leaf _ k2078_2) (.leaf _ k2078_3))) (.split 2 (.split 1 (.leaf _ k2078_4) (.leaf _ k2078_5)) (.split 1 (.leaf _ k2078_6) (.leaf _ k2078_7))))).trans <|
  (Cover.one (box := dirCellBox) (n := 2079)
      (.split 3 (.split 2 (.split 1 (.leaf _ k2079_0) (.leaf _ k2079_1)) (.split 1 (.leaf _ k2079_2) (.leaf _ k2079_3))) (.split 2 (.split 1 (.leaf _ k2079_4) (.leaf _ k2079_5)) (.split 1 (.leaf _ k2079_6) (.leaf _ k2079_7))))).trans <|
  (Cover.one (box := dirCellBox) (n := 2080)
      (.split 3 (.split 2 (.split 1 (.leaf _ k2080_0) (.leaf _ k2080_1)) (.split 1 (.leaf _ k2080_2) (.leaf _ k2080_3))) (.split 2 (.split 1 (.leaf _ k2080_4) (.leaf _ k2080_5)) (.split 1 (.leaf _ k2080_6) (.leaf _ k2080_7))))).trans <|
  (Cover.one (box := dirCellBox) (n := 2081)
      (.split 3 (.split 2 (.leaf _ k2081_0) (.leaf _ k2081_1)) (.split 2 (.leaf _ k2081_2) (.leaf _ k2081_3))))

end C4.Cert.Dir027
