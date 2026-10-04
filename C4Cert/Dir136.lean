module

public import C4Check

public section

/-! Cells `4154 ≤ n < 4186` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir136

theorem k4154_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4154) 2).1 1).1
      54062247318000300209334632922668191696161854296760938277117980195900).isSome = true := by
  decide +kernel

theorem k4154_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4154) 2).1 1).2
      3378820921211323584669953939917265681596446264406699752571497571276).isSome = true := by
  decide +kernel

theorem k4154_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4154) 2).2 1).1
      844775076006242663517577947167181230343086116568507132744233329612).isSome = true := by
  decide +kernel

theorem k4154_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4154) 2).2 1).2
      844763346064703468570777907999438896391032264583965105103292015564).isSome = true := by
  decide +kernel

theorem k4155_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4155) 2).1
      355568547421478776487101668414647643328189519183226279157023887116712351751239945680308953733999363389074599605532563626946900737084).isSome = true := by
  decide +kernel

theorem k4155_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4155) 2).2
      5556122797882221799576921744412328037870858293188413400859393180838292267086715083224570645065219138940752024521421742115213491260).isSome = true := by
  decide +kernel

theorem k4156_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4156) 2).1
      18813447741415561872401119554971129392445932916322413706605784698172498732954698510859146143266262118600326204).isSome = true := by
  decide +kernel

theorem k4156_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4156) 2).2
      254980469333685529724083774834864173018316755004576418380759889326239129726154636205440060).isSome = true := by
  decide +kernel

theorem k4157_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4157) 1).1
      863733083360494689564998721366790667109799610536175766727881245113404).isSome = true := by
  decide +kernel

theorem k4157_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4157) 1).2
      15929664748236571761029846877818665675399967960808992819189047206649749290653364574272572).isSome = true := by
  decide +kernel

theorem k4158_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4158) 1).1
      3981078421599072157776439248353427209237260611717369873623644289216027556539069410098236).isSome = true := by
  decide +kernel

theorem k4158_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4158) 1).2
      863283787902448863052656441014023149213011948350548043432566913285180).isSome = true := by
  decide +kernel

theorem k4159_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4159) 1).1
      45689542063641276073174897076843101700303928380).isSome = true := by
  decide +kernel

theorem k4159_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4159) 1).2
      13485834768764270004704027600568625466609672093156469680367357180988).isSome = true := by
  decide +kernel

theorem k4160_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4160) 1).1
      842690446204317400020011987707172860588784022127847409800166371900).isSome = true := by
  decide +kernel

theorem k4160_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4160) 1).2
      45683526020268460868843375450255628834140634172).isSome = true := by
  decide +kernel

theorem c7 : allCells dirCell 4161 4162 [
    4587549439094181892994832180698472150091862877940376743434522822837545486960352344479621863843333763074876] = true := by
  decide +kernel

theorem c8 : allCells dirCell 4162 4176 [
    51423791052367478879160408306880292789821267050065040230089681, 147561929189427280484, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0] = true := by
  decide +kernel

theorem c9 : allCells dirCell 4176 4177 [
    5505121229562269643678485473081546750378984180982430067422603276323380957060553702506534450029356510789617823203099403332216267] = true := by
  decide +kernel

theorem k4177_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4177) 3).1
      4651569184866047550532158899351211227604994506950617427328970294056005545173340347720988552071878680107826).isSome = true := by
  decide +kernel

theorem k4177_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4177) 3).2
      1056264621958801291496412403388936674638959809096329008200761320552727811384640202228785368266).isSome = true := by
  decide +kernel

theorem k4178_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4178) 2).1
      5596977283324424645299748667190241799993364018165761386205738412741387423626418413034086020999006725666549154520874807778310867763).isSome = true := by
  decide +kernel

theorem k4178_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4178) 2).2
      1185200927757069565361876590508110669604991318448599525330371825903163638501206988503639892038313031016762163).isSome = true := by
  decide +kernel

theorem k4179_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4179) 2).1 3).1
      53074182947077261094815425979342507806112541170838686504671638220).isSome = true := by
  decide +kernel

theorem k4179_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4179) 2).1 3).2
      735668996448088721519964943908950457800775680972).isSome = true := by
  decide +kernel

theorem k4179_2 : (checkBoxH dirMode depth (splitBox (dirCellBox 4179) 2).2
      5582942122585597941669032754431522369199992240780775290596738644082703934203863816906297844086213077288788417625096298148143690547).isSome = true := by
  decide +kernel

theorem k4180_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4180) 2).1 3).1
      183735444920566914235134063985161882959676163020).isSome = true := by
  decide +kernel

theorem k4180_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4180) 2).1 3).2
      734319779585436583773512254622219425894625428428).isSome = true := by
  decide +kernel

theorem k4180_2 : (checkBoxH dirMode depth (splitBox (dirCellBox 4180) 2).2
      4833631379573371052520863856849356814277584161793848848685454537082773412394915715929141901320904655322509275955).isSome = true := by
  decide +kernel

theorem k4181_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4181) 2).1 3).1
      733781658751780801952828529069873377653719548876).isSome = true := by
  decide +kernel

theorem k4181_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4181) 2).1 3).2
      211375192542170586348811551317869122431879278272476152361507079116).isSome = true := by
  decide +kernel

theorem k4181_2 : (checkBoxH dirMode depth (splitBox (dirCellBox 4181) 2).2
      19313960325413862482136650836500508226697774507655899239144500076317595711417107512222505139658801183578384174897).isSome = true := by
  decide +kernel

theorem k4182_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4182) 2).1 1).1
      844837358194370483951759781096523234794187640760535207747025576908).isSome = true := by
  decide +kernel

theorem k4182_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4182) 2).1 1).2
      211209850249666178504929597664585855487862811735231627577861325772).isSome = true := by
  decide +kernel

theorem k4182_2 : (checkBoxH dirMode depth (splitBox (dirCellBox 4182) 2).2
      1205872902353965773929599339919889745405607089825177770460250110294710036977690747780610242122785973079594646588).isSome = true := by
  decide +kernel

theorem k4183_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4183) 2).1
      1389110225665579219767146112409972212261435694996634430352862334296101280088046119110630515847822034090101264594284497239661558844).isSome = true := by
  decide +kernel

theorem k4183_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4183) 2).2
      63803550030844005213358700111035665938389734845135181186481780889896683099847260631678012).isSome = true := by
  decide +kernel

theorem k4184_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4184) 1).1
      15937229332416214717532081915659054259264607402395280115341041812934869637959491219405884).isSome = true := by
  decide +kernel

theorem k4184_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4184) 1).2
      863963742845751984884414588098281648121485301934033234159506413009980).isSome = true := by
  decide +kernel

theorem k4185_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4185) 1).1
      13493284188299187516152284111862066643198408747214862048688866507836).isSome = true := by
  decide +kernel

theorem k4185_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4185) 1).2
      3982662796419828564768139432848708607953733342968365000004326084682351631394876570778684).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 4154 4186 :=
  (Cover.one (box := dirCellBox) (n := 4154)
      (.split 2 (.split 1 (.leaf _ k4154_0) (.leaf _ k4154_1)) (.split 1 (.leaf _ k4154_2) (.leaf _ k4154_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 4155)
      (.split 2 (.leaf _ k4155_0) (.leaf _ k4155_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 4156)
      (.split 2 (.leaf _ k4156_0) (.leaf _ k4156_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 4157)
      (.split 1 (.leaf _ k4157_0) (.leaf _ k4157_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 4158)
      (.split 1 (.leaf _ k4158_0) (.leaf _ k4158_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 4159)
      (.split 1 (.leaf _ k4159_0) (.leaf _ k4159_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 4160)
      (.split 1 (.leaf _ k4160_0) (.leaf _ k4160_1))).trans <|
  (Cover.dir c7).trans <|
  (Cover.dir c8).trans <|
  (Cover.dir c9).trans <|
  (Cover.one (box := dirCellBox) (n := 4177)
      (.split 3 (.leaf _ k4177_0) (.leaf _ k4177_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 4178)
      (.split 2 (.leaf _ k4178_0) (.leaf _ k4178_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 4179)
      (.split 2 (.split 3 (.leaf _ k4179_0) (.leaf _ k4179_1)) (.leaf _ k4179_2))).trans <|
  (Cover.one (box := dirCellBox) (n := 4180)
      (.split 2 (.split 3 (.leaf _ k4180_0) (.leaf _ k4180_1)) (.leaf _ k4180_2))).trans <|
  (Cover.one (box := dirCellBox) (n := 4181)
      (.split 2 (.split 3 (.leaf _ k4181_0) (.leaf _ k4181_1)) (.leaf _ k4181_2))).trans <|
  (Cover.one (box := dirCellBox) (n := 4182)
      (.split 2 (.split 1 (.leaf _ k4182_0) (.leaf _ k4182_1)) (.leaf _ k4182_2))).trans <|
  (Cover.one (box := dirCellBox) (n := 4183)
      (.split 2 (.leaf _ k4183_0) (.leaf _ k4183_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 4184)
      (.split 1 (.leaf _ k4184_0) (.leaf _ k4184_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 4185)
      (.split 1 (.leaf _ k4185_0) (.leaf _ k4185_1)))

end C4.Cert.Dir136
