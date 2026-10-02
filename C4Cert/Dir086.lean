module

public import C4Check

public section

/-! Cells `3140 ≤ n < 3165` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir086

theorem k3140_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3140) 2).1 3).1 2).1
      1860197474878107492601392479554410700139979672485527556189211656346069012329724566909241318732270531225469489891539096614370772502822369482662969563931360034190599623).isSome = true := by
  decide +kernel

theorem k3140_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3140) 2).1 3).1 2).2 3).1
      5347375150957257594342508856956189042426749818270819036675131512998361741250990688307672352849008541269082073548837976432049).isSome = true := by
  decide +kernel

theorem k3140_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3140) 2).1 3).1 2).2 3).2
      15326287869292218514234646520430117670165164799982288214531417244663435081854868849).isSome = true := by
  decide +kernel

theorem k3140_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3140) 2).1 3).2 2).1
      72229579431672545387471022253747892017008324968999155427553377058982631607373880381206543846244172981709).isSome = true := by
  decide +kernel

theorem k3140_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3140) 2).1 3).2 2).2
      1857318065538120240829335129158956475047271199384554867299028777514505370444815753408729312766709639826453509459583654930190330954195573534608136352271574273115395527).isSome = true := by
  decide +kernel

theorem k3140_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3140) 2).2 3).1 2).1 3).1
      4644082885601392617356084272651104166327919310931477867596239384510449071719049934242780705012323355973436).isSome = true := by
  decide +kernel

theorem k3140_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3140) 2).2 3).1 2).1 3).2
      18105383269423617665711860800956489036904980284696329027849920623980591865562845520335983188555655044529).isSome = true := by
  decide +kernel

theorem k3140_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3140) 2).2 3).1 2).2 3).1
      1162292597553252437858340752175397285284443206745267268500926832626000388529397521588640649542788506441532).isSome = true := by
  decide +kernel

theorem k3140_8 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3140) 2).2 3).1 2).2 3).2
      290041370184260240616811051118094337295439440922685823549119457041227688053645973135613807147757180802876).isSome = true := by
  decide +kernel

theorem k3140_9 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3140) 2).2 3).2 2).1
      1857868593997648164933884889013115711192727844041388127896867193842761380370940399826394641888273300728961262514201225860200817525518013360851227869352165052920477127).isSome = true := by
  decide +kernel

theorem k3140_10 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3140) 2).2 3).2 2).2 3).1
      4523651321865949095951078710714692700490111851442275843550458268152998834294602530897028038688909694833).isSome = true := by
  decide +kernel

theorem k3140_11 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3140) 2).2 3).2 2).2 3).2
      15308913034552564805228097391766570103711772559627627821306067647548097251375758705).isSome = true := by
  decide +kernel

theorem k3141_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3141) 2).1 2).1
      8583123238140659245694238335889078880612205511).isSome = true := by
  decide +kernel

theorem k3141_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3141) 2).1 2).2
      85105624120693957884141979924327849874389875109465378065383067197086399049223868690746615299718077382162743460754981320450327).isSome = true := by
  decide +kernel

theorem k3141_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3141) 2).2 3).1 2).1
      288571272166524320698950852729632088392924053140851975159572337478589236885372129937982968241092490523891).isSome = true := by
  decide +kernel

theorem k3141_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3141) 2).2 3).1 2).2
      340850153723644581562236131192335173489128854823351203784602759751298860811275557037131730391277025169234801497142359233230067).isSome = true := by
  decide +kernel

theorem k3141_4 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3141) 2).2 3).2
      1853692699827353087587197025518747659177079033462512169165467773115607866163445136029347271277336281639140257397957474754215894969121231978980609156063348738667750854).isSome = true := by
  decide +kernel

theorem k3142_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3142) 2).1
      1).isSome = true := by
  decide +kernel

theorem k3142_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3142) 2).2 2).1
      2094119347798260508116194842683383188029511).isSome = true := by
  decide +kernel

theorem k3142_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3142) 2).2 2).2
      21242482941978088523089785275349738288568419801751014294382207519134904096020867678548271913522368767355155310811799218193863).isSome = true := by
  decide +kernel

theorem c3 : allCells dirCell 3143 3165 [
    845178129092275295224661045858284829175450068408092679694314160514, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1] = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 3140 3165 :=
  (Cover.one (box := dirCellBox) (n := 3140)
      (.split 2 (.split 3 (.split 2 (.leaf _ k3140_0) (.split 3 (.leaf _ k3140_1) (.leaf _ k3140_2))) (.split 2 (.leaf _ k3140_3) (.leaf _ k3140_4))) (.split 3 (.split 2 (.split 3 (.leaf _ k3140_5) (.leaf _ k3140_6)) (.split 3 (.leaf _ k3140_7) (.leaf _ k3140_8))) (.split 2 (.leaf _ k3140_9) (.split 3 (.leaf _ k3140_10) (.leaf _ k3140_11)))))).trans <|
  (Cover.one (box := dirCellBox) (n := 3141)
      (.split 2 (.split 2 (.leaf _ k3141_0) (.leaf _ k3141_1)) (.split 3 (.split 2 (.leaf _ k3141_2) (.leaf _ k3141_3)) (.leaf _ k3141_4)))).trans <|
  (Cover.one (box := dirCellBox) (n := 3142)
      (.split 2 (.leaf _ k3142_0) (.split 2 (.leaf _ k3142_1) (.leaf _ k3142_2)))).trans <|
  (Cover.dir c3)

end C4.Cert.Dir086
