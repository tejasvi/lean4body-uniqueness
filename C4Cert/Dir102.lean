module

public import C4Check

public section

/-! Cells `3284 ≤ n < 3309` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir102

theorem k3284_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3284) 2).1 3).1
      3997371561672408564995543370005262262385283923423972549227671560108873383541356625642300).isSome = true := by
  decide +kernel

theorem k3284_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3284) 2).1 3).2
      845799485277264609435606686593962543527617798713769898478373684028).isSome = true := by
  decide +kernel

theorem k3284_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3284) 2).2 3).1
      3467764434348168363018558987529987867697504249746992175690406849330236).isSome = true := by
  decide +kernel

theorem k3284_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3284) 2).2 3).2
      52877459338742422028171719757822426750145304790612225569417165884).isSome = true := by
  decide +kernel

theorem k3285_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3285) 2).1
      22247458042115339275121669154622255527291330331770581707021094232219343513566431689969506039361321713521500181545522298838895571772).isSome = true := by
  decide +kernel

theorem k3285_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 3285) 2).2
      301546029421046017941521278071094901719730642836382556970241799574344072642066697705625932050110528041505506108).isSome = true := by
  decide +kernel

theorem k3286_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3286) 1).1
      1176746074535676820129079525080768656726493448563222204817963960845583759880972761543077301013494961454513212).isSome = true := by
  decide +kernel

theorem k3286_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 3286) 1).2
      86830292371676563898078355945956872733412014997968274586433227712352796293669282409164566514626376001732488018090986160990962492).isSome = true := by
  decide +kernel

theorem k3287_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3287) 2).1
      62250463900090419908548982196675980736953960198123595399228509660750107196035728089916).isSome = true := by
  decide +kernel

theorem k3287_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 3287) 2).2
      249032000565563773377692234324047585774763476541725188822054405191582874717383093109564).isSome = true := by
  decide +kernel

theorem k3288_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3288) 3).1
      972400047011130835204053897327593836078221446029878427589029202205497092382408932412).isSome = true := by
  decide +kernel

theorem k3288_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 3288) 3).2
      210796925137130757635113193013103775261240011948675462532189961276).isSome = true := by
  decide +kernel

theorem k3289_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3289) 1).1
      52685578220209343090088884783311686145287653160334754161775950908).isSome = true := by
  decide +kernel

theorem k3289_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 3289) 1).2
      971951353570017076788584667030601551610467557078051773790744714512934876252045409340).isSome = true := by
  decide +kernel

theorem c6 : allCells dirCell 3290 3291 [
    4698777114432271495202660215655466648165245705130931790415901999328105195893652897871336948570315442443142342] = true := by
  decide +kernel

theorem c7 : allCells dirCell 3291 3292 [
    994830631104142258040320336541279696441018370918700705430136518030080688348357738721521] = true := by
  decide +kernel

theorem c8 : allCells dirCell 3292 3307 [
    15177647443046171168251247684375815288389465697420889483439307101349524267823457650,
    147556463791862678644, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] = true := by
  decide +kernel

theorem k3307_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3307) 3).1
      213291876592146923372056627130386368245388766666647762011350342).isSome = true := by
  decide +kernel

theorem k3307_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 3307) 3).2
      21776054330703019742898312222943556226073633669389694176093994110745578894506195005667991928625682270707234275715617427080646).isSome = true := by
  decide +kernel

theorem k3308_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3308) 3).1
      26188401265975876817733374771067535125104028978850920252389187803089402570958843042364581583052124750803935129202721262434229278771137854823164257734).isSome = true := by
  decide +kernel

theorem k3308_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3308) 3).2 2).1
      292355984879381644677512730681218636205896087179200910620142256624879833133836888083704912323216049427260).isSome = true := by
  decide +kernel

theorem k3308_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3308) 3).2 2).2
      990516567460715290721324147433574813954487617974036669311342776272844612713553187644).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 3284 3309 :=
  (Cover.one (box := dirCellBox) (n := 3284)
      (.split 2 (.split 3 (.leaf _ k3284_0) (.leaf _ k3284_1)) (.split 3 (.leaf _ k3284_2) (.leaf _ k3284_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 3285)
      (.split 2 (.leaf _ k3285_0) (.leaf _ k3285_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 3286)
      (.split 1 (.leaf _ k3286_0) (.leaf _ k3286_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 3287)
      (.split 2 (.leaf _ k3287_0) (.leaf _ k3287_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 3288)
      (.split 3 (.leaf _ k3288_0) (.leaf _ k3288_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 3289)
      (.split 1 (.leaf _ k3289_0) (.leaf _ k3289_1))).trans <|
  (Cover.dir c6).trans <|
  (Cover.dir c7).trans <|
  (Cover.dir c8).trans <|
  (Cover.one (box := dirCellBox) (n := 3307)
      (.split 3 (.leaf _ k3307_0) (.leaf _ k3307_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 3308)
      (.split 3 (.leaf _ k3308_0) (.split 2 (.leaf _ k3308_1) (.leaf _ k3308_2))))

end C4.Cert.Dir102
