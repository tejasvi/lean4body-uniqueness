module

public import C4Check

public section

/-! Cells `2893 ≤ n < 2918` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir076

theorem k2893_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2893) 3).1
      22257469848388033085952097089075576292546802223624301998068624963944347649175453770411130134162795486534546377156698467290624356594).isSome = true := by
  decide +kernel

theorem k2893_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 2893) 3).2
      255316883287967638358846314507897003126115987688989361097261245409148190705761417251470396).isSome = true := by
  decide +kernel

theorem k2894_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2894) 3).1
      63798423668564079182679605244078893234786123558395479357393208509980025274043583458655292).isSome = true := by
  decide +kernel

theorem k2894_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 2894) 3).2
      294100109516884235039555842695266710291137104785731569524804872084557503993439927817570205063504286842567740).isSome = true := by
  decide +kernel

theorem k2895_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2895) 1).1
      15935147587013347515963620134077590819227131407082019774876216409519517929301496086871100).isSome = true := by
  decide +kernel

theorem k2895_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 2895) 1).2
      18373334588504147211712549509347363964354165299863121111302575468395854158814162911132661270688653173537852).isSome = true := by
  decide +kernel

theorem c3 : allCells dirCell 2896 2897 [
    22198619950171709121577778977743075122157955346711886405881594946964501736554217040723156883312167035347802967925146883121571229939] = true := by
  decide +kernel

theorem c4 : allCells dirCell 2897 2898 [
    22193029926623576567691392928168768895640200298516871791420522033741763666185067632912918839213614344382927584701256860664975388913] = true := by
  decide +kernel

theorem c5 : allCells dirCell 2898 2899 [
    293638390184751001762723523896568977416468415654680890649162664131717073058852804314719905692983643742892274] = true := by
  decide +kernel

theorem c6 : allCells dirCell 2899 2915 [
    15178011625561802849835942789509065796351518653317828387841609953370811300264552818,
    147550651361067063764, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] = true := by
  decide +kernel

theorem c7 : allCells dirCell 2915 2916 [
    102932683730290250387903949325439487215574549381724304233697667895456744294671123411557118487089184382412677675160932585500185922640213716228482507] = true := by
  decide +kernel

theorem k2916_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2916) 3).1
      472017540587098189809525747895228280006593637679724391694306817540964468547442071434783649790974596793073190040568068167834703580326405967963494584942235652666459590).isSome = true := by
  decide +kernel

theorem k2916_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2916) 3).2 2).1
      73119672498037598033849159474199689705770735368355315887340442255420838163860523088557130498926657918780).isSome = true := by
  decide +kernel

theorem k2916_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2916) 3).2 2).2
      209827230499754584298873659680585001908904832868740719971294524).isSome = true := by
  decide +kernel

theorem k2917_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2917) 3).1 2).1
      3949586160469384512855219684229155116118691507059461899475909837541313265639137727292).isSome = true := by
  decide +kernel

theorem k2917_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2917) 3).1 2).2
      3949774691702162308408258767303127412864837847804450975794599592650704880929112314684).isSome = true := by
  decide +kernel

theorem k2917_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2917) 3).2 2).1
      3938510820820869544063003322112106293783063469595951564517693737950238070495518380860).isSome = true := by
  decide +kernel

theorem k2917_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2917) 3).2 2).2
      3938893830295369827340302631238784777000353673692209307843618796202946647643884344124).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 2893 2918 :=
  (Cover.one (box := dirCellBox) (n := 2893)
      (.split 3 (.leaf _ k2893_0) (.leaf _ k2893_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 2894)
      (.split 3 (.leaf _ k2894_0) (.leaf _ k2894_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 2895)
      (.split 1 (.leaf _ k2895_0) (.leaf _ k2895_1))).trans <|
  (Cover.dir c3).trans <|
  (Cover.dir c4).trans <|
  (Cover.dir c5).trans <|
  (Cover.dir c6).trans <|
  (Cover.dir c7).trans <|
  (Cover.one (box := dirCellBox) (n := 2916)
      (.split 3 (.leaf _ k2916_0) (.split 2 (.leaf _ k2916_1) (.leaf _ k2916_2)))).trans <|
  (Cover.one (box := dirCellBox) (n := 2917)
      (.split 3 (.split 2 (.leaf _ k2917_0) (.leaf _ k2917_1)) (.split 2 (.leaf _ k2917_2) (.leaf _ k2917_3))))

end C4.Cert.Dir076
