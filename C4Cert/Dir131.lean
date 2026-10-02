module

public import C4Check

public section

/-! Cells `3873 ≤ n < 3952` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir131

theorem c0 : allCells dirCell 3873 3875 [
    975253905884584994484973050404008679585007073960093559817180894624422456850716130364,
    178933608236520758918160982918240457383592764] = true := by
  decide +kernel

theorem c1 : allCells dirCell 3875 3877 [
    206133551799599860039886189731679582659477483976409727590686012,
    206002850235531664549411399027440917700710630246282936016395580] = true := by
  decide +kernel

theorem c2 : allCells dirCell 3877 3879 [
    205902649738650906546521279376337488668924621895392588433612092,
    823303852731528325316186454752147635828003975166824897015542972] = true := by
  decide +kernel

theorem c3 : allCells dirCell 3879 3882 [
    823069583969438005379243646881841511787410229086197610111923388,
    43563695435469062198936394157974770589020, 43556357645040430754678884974760025836892] = true := by
  decide +kernel

theorem c4 : allCells dirCell 3882 3900 [
    147555664584556416836, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2388800694786792775491,
    720268306353865958348501774858592379128156978, 2807112810362337754422535569099436243996978] = true := by
  decide +kernel

theorem c5 : allCells dirCell 3900 3903 [
    2802286622355317019308885602893894226345266, 11194411264974180996469484491558927285957810,
    43684514260905364940217212768949979309660] = true := by
  decide +kernel

theorem c6 : allCells dirCell 3903 3907 [
    43649662448858730205971168201116189259356, 43622645853336341603300414143506724046684,
    43601720491348460915405150663656160200284, 43585548596004880683299385326188397727836] = true := by
  decide +kernel

theorem c7 : allCells dirCell 3907 3949 [
    147631066755536797348, 147598705035954932964, 147573952624032029332, 147555116271861330180, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 2, 2, 2, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 1] = true := by
  decide +kernel

theorem k3949_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3949) 3).1 3).1
      22671353169356681797160797230).isSome = true := by
  decide +kernel

theorem k3949_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3949) 3).1 3).2 2).1
      51211034975002829273723280116133426501005119755).isSome = true := by
  decide +kernel

theorem k3949_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3949) 3).1 3).2 2).2
      6065356479712507165657017522036002570919891899805532995966629729139413036882633703715804077777224522882428052644982029888099611).isSome = true := by
  decide +kernel

theorem k3949_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3949) 3).2 2).1
      12633279154476475707839369956111319141822163993867).isSome = true := by
  decide +kernel

theorem k3949_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3949) 3).2 2).2 3).1
      4283503215300006515242148743685564164728261328778313330539677128925346026759341648166).isSome = true := by
  decide +kernel

theorem k3949_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3949) 3).2 2).2 3).2
      16827008229078375596209924633351223295662705496555583704364189269663604280874111559110).isSome = true := by
  decide +kernel

theorem k3950_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3950) 2).1
      276060444422127908642871228922229132257752950839987863141714593524904836335761009532788850082863).isSome = true := by
  decide +kernel

theorem k3950_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3950) 2).2 3).1
      6911795434617699277303420509621268718241367987315747018657640339160692363841484265827339852804115590228922681303601808810817685471885184017761542477595).isSome = true := by
  decide +kernel

theorem k3950_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3950) 2).2 3).2 2).1
      1006548505087794440466208729558549924865042540029834195236676780553910686526584788423).isSome = true := by
  decide +kernel

theorem k3950_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3950) 2).2 3).2 2).2
      4033630503134156971887803359245428433096534241479544982815924630812802179916234106311).isSome = true := by
  decide +kernel

theorem k3951_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3951) 2).1
      3511662493042246558132737414662343726125873910932004852230958735705867).isSome = true := by
  decide +kernel

theorem k3951_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3951) 2).2 3).1
      1392656154379152753487704021539275760104134659212579174032278993077726530045480081170974064454318710190993333431110561663893814).isSome = true := by
  decide +kernel

theorem k3951_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3951) 2).2 3).2
      4679471344271712179933405515055238104663555695580125065976951923720285044811380034051814947263029450884390).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 3873 3952 :=
  (Cover.dir c0).trans <|
  (Cover.dir c1).trans <|
  (Cover.dir c2).trans <|
  (Cover.dir c3).trans <|
  (Cover.dir c4).trans <|
  (Cover.dir c5).trans <|
  (Cover.dir c6).trans <|
  (Cover.dir c7).trans <|
  (Cover.one (box := dirCellBox) (n := 3949)
      (.split 3 (.split 3 (.leaf _ k3949_0) (.split 2 (.leaf _ k3949_1) (.leaf _ k3949_2))) (.split 2 (.leaf _ k3949_3) (.split 3 (.leaf _ k3949_4) (.leaf _ k3949_5))))).trans <|
  (Cover.one (box := dirCellBox) (n := 3950)
      (.split 2 (.leaf _ k3950_0) (.split 3 (.leaf _ k3950_1) (.split 2 (.leaf _ k3950_2) (.leaf _ k3950_3))))).trans <|
  (Cover.one (box := dirCellBox) (n := 3951)
      (.split 2 (.leaf _ k3951_0) (.split 3 (.leaf _ k3951_1) (.leaf _ k3951_2))))

end C4.Cert.Dir131
