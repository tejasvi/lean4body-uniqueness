module

public import C4Check

public section

/-! Cells `2972 ≤ n < 3003` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir079

theorem c0 : allCells dirCell 2972 2973 [
    21563915347802309733848935597907740872816137409497219958211800495041895793275214531530343413613845685319134266736605629706567] = true := by
  decide +kernel

theorem k2973_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2973) 3).1
      72833936339152481115002243559673661593671473758833950156720268170349212477755184871527910710944935015666).isSome = true := by
  decide +kernel

theorem k2973_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 2973) 3).2
      343086334681699449369743021635276924531144040167769240356473821804234310451686259505986493889178318540372716588630424863208689).isSome = true := by
  decide +kernel

theorem k2974_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2974) 2).1
      4742697520195010591675192829781871072973229121163994839176416061254790417744345923726362317374343241408039155).isSome = true := by
  decide +kernel

theorem k2974_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 2974) 2).2
      4017018709475077492856512673781147052437034101633330552462259791133006867705667138210035).isSome = true := by
  decide +kernel

theorem k2975_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2975) 2).1
      1026147436307857713486456122219873845182558442809455060804282342844630265275533415435533372).isSome = true := by
  decide +kernel

theorem k2975_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 2975) 2).2
      295780092917300334564437354765336493041606860888411804858660732528718511227295527643421919166390510852045884).isSome = true := by
  decide +kernel

theorem k2976_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2976) 1).1
      15999103511525330583434539163300128534047157148673641061903173436627644519945164890897468).isSome = true := by
  decide +kernel

theorem k2976_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 2976) 1).2
      4000082056249956583150883301599033274771410924996371979601850555270454740760303817407548).isSome = true := by
  decide +kernel

theorem k2977_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2977) 1).1
      998430503872992404930507080107780538882481057702196220675852540963771082121409031781436).isSome = true := by
  decide +kernel

theorem k2977_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 2977) 1).2
      216491694967334546076557052248608634911570164055941372491707526102076).isSome = true := by
  decide +kernel

theorem k2978_0 : (checkBoxH dirMode depth (dirCellBox 2978)
      1983864663399395880323833395832504551667909995388541327853481412287794367511440029296963416158531476483225843848781395790544931732905303109861135479079443940296664311219077948).isSome = true := by
  decide +kernel

theorem c7 : allCells dirCell 2979 2980 [
    347207098760091211632320580661470750800277766917965788911937785412311552445092640691151358736521134527521205558209435902374036284] = true := by
  decide +kernel

theorem c8 : allCells dirCell 2980 2981 [
    5551561176004358476493341133011397397027418622871806712500097003056737965151327155653061204469241064273676260850581575873344815932] = true := by
  decide +kernel

theorem c9 : allCells dirCell 2981 2982 [
    248821555970092279838676964251207546651566051983947402169055253930174114224340115141436] = true := by
  decide +kernel

theorem c10 : allCells dirCell 2982 3000 [
    823022157063226855645728444142854217855493433697027315121616060,
    43558009789255629225779043042236764521564, 147546063511504337460, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0] = true := by
  decide +kernel

theorem c11 : allCells dirCell 3000 3001 [
    2840373794329723656321158775502815112711443] = true := by
  decide +kernel

theorem k3001_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3001) 3).1
      15417858930808612012510475469257514822316331319535519793188510880240006711897980273).isSome = true := by
  decide +kernel

theorem k3001_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 3001) 3).2
      72629916970036504773965004746088329814308662303432577170032302754157047125181731355265226558239971046642).isSome = true := by
  decide +kernel

theorem k3002_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3002) 2).1
      15704856982119226327927487361350030011422336787169789689795062395709307136840023130940).isSome = true := by
  decide +kernel

theorem k3002_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 3002) 2).2
      981473564879771273248016376512546855057895398059231923903354906206078396809246243900).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 2972 3003 :=
  (Cover.dir c0).trans <|
  (Cover.one (box := dirCellBox) (n := 2973)
      (.split 3 (.leaf _ k2973_0) (.leaf _ k2973_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 2974)
      (.split 2 (.leaf _ k2974_0) (.leaf _ k2974_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 2975)
      (.split 2 (.leaf _ k2975_0) (.leaf _ k2975_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 2976)
      (.split 1 (.leaf _ k2976_0) (.leaf _ k2976_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 2977)
      (.split 1 (.leaf _ k2977_0) (.leaf _ k2977_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 2978)
      (.leaf _ k2978_0)).trans <|
  (Cover.dir c7).trans <|
  (Cover.dir c8).trans <|
  (Cover.dir c9).trans <|
  (Cover.dir c10).trans <|
  (Cover.dir c11).trans <|
  (Cover.one (box := dirCellBox) (n := 3001)
      (.split 3 (.leaf _ k3001_0) (.leaf _ k3001_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 3002)
      (.split 2 (.leaf _ k3002_0) (.leaf _ k3002_1)))

end C4.Cert.Dir079
