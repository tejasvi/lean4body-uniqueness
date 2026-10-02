module

public import C4Check

public section

/-! Cells `849 ≤ n < 932` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir003

theorem k849_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 849) 2).1
      1043727860802451792817817612511179306480923118333216721731402180663138688673349315533433031879).isSome = true := by
  decide +kernel

theorem k849_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 849) 2).2
      1043794298137294611933190541001156375460855406596741626739588259770510289759043265944515923143).isSome = true := by
  decide +kernel

theorem k850_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 850) 2).1
      15914994813064047578375396505323914233874177476556232397353011481306406285644555788022983).isSome = true := by
  decide +kernel

theorem k850_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 850) 2).2
      3979355622411836550506845602766247940721883248614431875666779051199439577805133835125959).isSome = true := by
  decide +kernel

theorem c2 : allCells dirCell 851 875 [
    44576993379088297538371284494583904101667078, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 3] = true := by
  decide +kernel

theorem k875_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 875) 3).1
      826683177802404363830144741670881983333572425119600465319810310).isSome = true := by
  decide +kernel

theorem k875_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 875) 3).2
      21248043826078505617861633086192306946315636186379141878131674317854669866331035883742267051680543735957449354004650085728838).isSome = true := by
  decide +kernel

theorem k876_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 876) 3).1 2).1
      243564620725519275347896371918727345846425054835502759157484194681885907498432206193).isSome = true := by
  decide +kernel

theorem k876_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 876) 3).1 2).2
      243603936323926676242870200545838488165954773956712662489482441252292161892208425329).isSome = true := by
  decide +kernel

theorem k876_2 : (checkBoxH dirMode depth (splitBox (dirCellBox 876) 3).2
      86837271991198706490919622268752201307980828233396596933150909056541115679421944906508723644711538853688052841115936504271032114).isSome = true := by
  decide +kernel

theorem k877_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 877) 3).1
      1044400457457774720713948975588905371025668367541587867176221830678653945955337746734421134534).isSome = true := by
  decide +kernel

theorem k877_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 877) 3).2
      4701040669575881896808405939325015269191141791311221264487726439331156360868095767536146041034527249321548594).isSome = true := by
  decide +kernel

theorem k878_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 878) 3).1
      3887291407760406911753357867415124240723652917433689224763177499451966792785663285042).isSome = true := by
  decide +kernel

theorem k878_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 878) 3).2
      15179263486146455403938573269315242798842653149485242038879068465965210591080592754).isSome = true := by
  decide +kernel

theorem c7 : allCells dirCell 879 903 [
    589898482725606158099, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3] = true := by
  decide +kernel

theorem c8 : allCells dirCell 903 904 [
    118494431381326210112359806180759748148691957900942502569294622256195919380370773214972755819857170276065776555375360068195806642255672453744573703352594103443598361735] = true := by
  decide +kernel

theorem k904_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 904) 3).1
      1358759329662091548717432270012348994287695108791560722665917633314229844604650415146337290043525913315509895838315040640017862).isSome = true := by
  decide +kernel

theorem k904_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 904) 3).2
      1177313957548934103854064940972478789318190038401265691624665202397371742271556261178217658595062143046771913).isSome = true := by
  decide +kernel

theorem k905_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 905) 3).1
      15941237613574358404803684183565249782316322260921611565488770876951713724572400946188081).isSome = true := by
  decide +kernel

theorem k905_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 905) 3).2
      248922974786791983125994290896374119609567360357227382256927168952453559243010233685809).isSome = true := by
  decide +kernel

theorem c11 : allCells dirCell 906 923 [
    99929249545216137343723556732418338977288398272873030572363170803974479022410767885951872282010463067892261140836837883011423031328179064769578439,
    2359635954239929248577, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] = true := by
  decide +kernel

theorem c12 : allCells dirCell 923 932 [
    0, 0, 0, 0, 0, 0, 0, 3,
    85003593454250351774810795129466219832474332127129352647296337794822208627990290129000367942647860608818135200284930268911367] = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 849 932 :=
  (Cover.one (box := dirCellBox) (n := 849)
      (.split 2 (.leaf _ k849_0) (.leaf _ k849_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 850)
      (.split 2 (.leaf _ k850_0) (.leaf _ k850_1))).trans <|
  (Cover.dir c2).trans <|
  (Cover.one (box := dirCellBox) (n := 875)
      (.split 3 (.leaf _ k875_0) (.leaf _ k875_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 876)
      (.split 3 (.split 2 (.leaf _ k876_0) (.leaf _ k876_1)) (.leaf _ k876_2))).trans <|
  (Cover.one (box := dirCellBox) (n := 877)
      (.split 3 (.leaf _ k877_0) (.leaf _ k877_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 878)
      (.split 3 (.leaf _ k878_0) (.leaf _ k878_1))).trans <|
  (Cover.dir c7).trans <|
  (Cover.dir c8).trans <|
  (Cover.one (box := dirCellBox) (n := 904)
      (.split 3 (.leaf _ k904_0) (.leaf _ k904_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 905)
      (.split 3 (.leaf _ k905_0) (.leaf _ k905_1))).trans <|
  (Cover.dir c11).trans <|
  (Cover.dir c12)

end C4.Cert.Dir003
