module

public import C4Check

public section

/-! Cells `2554 ≤ n < 2583` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir053

theorem k2554_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2554) 3).1
      1402416785234644873604546946630294111374306030202268796253640265848440872583292414339623180851940860401164100837244480911526808818).isSome = true := by
  decide +kernel

theorem k2554_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 2554) 3).2
      349952091870399806015548660832495301779366794247365880364346350352207594205757731158106781166414755520547038826269658831508042556).isSome = true := by
  decide +kernel

theorem k2555_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2555) 3).1
      87348700782188720536541537361150060104703369101045025418037498987924189762620677489995331920607399910735116389407227451065316156).isSome = true := by
  decide +kernel

theorem k2555_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 2555) 3).2
      302651518151660121075334928494639374198586280514329055474819636279018100376263218009518915930580738282985632572).isSome = true := by
  decide +kernel

theorem k2556_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2556) 3).1
      18894249358916846888769748641119394753947585307698830673558468384718054205430013539818635110811599614086464316).isSome = true := by
  decide +kernel

theorem k2556_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 2556) 3).2
      255812881966870006563786068606043147491595424541742838321285805596395804191420789663267900).isSome = true := by
  decide +kernel

theorem k2557_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2557) 2).1
      15969440668515016027324117499516737373547020306338811895534169410968344834757880462916668).isSome = true := by
  decide +kernel

theorem k2557_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 2557) 2).2
      15970082390128925779209734290571430158984041818172428181131848324636661244244834667674684).isSome = true := by
  decide +kernel

theorem k2558_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2558) 1).1
      3987449272705083301186632320982618226628230906358456820878325012813561487212753376197692).isSome = true := by
  decide +kernel

theorem k2558_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 2558) 1).2
      996970650939121861371334582276313726887930900792389819792274031031819702077895510015036).isSome = true := by
  decide +kernel

theorem c5 : allCells dirCell 2559 2560 [
    88837168522846977056437165280833255997856795395060838005690899794647516137140167798888765464009102989826595762125740699533144551667] = true := by
  decide +kernel

theorem c6 : allCells dirCell 2560 2561 [
    75206304947497651556105105730532846726546523398802372341490482709653675076122894944195911435616155949102985459] = true := by
  decide +kernel

theorem c7 : allCells dirCell 2561 2562 [
    286814707987117095822836223529818806041995887277025647828334524300987711456739743522950514500351894737724] = true := by
  decide +kernel

theorem c8 : allCells dirCell 2562 2581 [
    51429400464933324107290823896411449968634282876818534259892305, 147537520512274003988, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    13423163049265829988356840514446967640675619601584038483215872519] = true := by
  decide +kernel

theorem k2581_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2581) 3).1
      15424846924028744567655288142532185411561063755584050470656099686881311424387065202).isSome = true := by
  decide +kernel

theorem k2581_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 2581) 3).2
      343079418526390618334102177840621359315482357006265407106663899350733652155621590186685967872984054831070749102285639058027762).isSome = true := by
  decide +kernel

theorem k2582_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2582) 2).1
      341772269421729345195994084268984353831512453547183963614703186685026540007092331238676629566360330481858050837283804683793651).isSome = true := by
  decide +kernel

theorem k2582_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 2582) 2).2
      4635403718850869957096145731938892196502141255433440867063780513010994643310698627517562777342118998127420).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 2554 2583 :=
  (Cover.one (box := dirCellBox) (n := 2554)
      (.split 3 (.leaf _ k2554_0) (.leaf _ k2554_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 2555)
      (.split 3 (.leaf _ k2555_0) (.leaf _ k2555_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 2556)
      (.split 3 (.leaf _ k2556_0) (.leaf _ k2556_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 2557)
      (.split 2 (.leaf _ k2557_0) (.leaf _ k2557_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 2558)
      (.split 1 (.leaf _ k2558_0) (.leaf _ k2558_1))).trans <|
  (Cover.dir c5).trans <|
  (Cover.dir c6).trans <|
  (Cover.dir c7).trans <|
  (Cover.dir c8).trans <|
  (Cover.one (box := dirCellBox) (n := 2581)
      (.split 3 (.leaf _ k2581_0) (.leaf _ k2581_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 2582)
      (.split 2 (.leaf _ k2582_0) (.leaf _ k2582_1)))

end C4.Cert.Dir053
