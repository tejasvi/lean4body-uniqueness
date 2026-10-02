module

public import C4Check

public section

/-! Cells `2109 ≤ n < 2136` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir031

theorem k2109_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2109) 3).1
      1206136371365622824618744018385657288839945691239152851861049141373688934213367686646785472305535591293598338866).isSome = true := by
  decide +kernel

theorem k2109_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 2109) 3).2
      22237170689132958994308296622442869337666629622579804729580190448276271409559034391613121321069126848109635743176755332667896958770).isSome = true := by
  decide +kernel

theorem k2110_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2110) 3).1
      3986657301127712440793488943548424362436222652951962178397588544820246782556586134158396).isSome = true := by
  decide +kernel

theorem k2110_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 2110) 3).2
      3984686386376337277714236804927196131214471189256491759308304304804491897422038803561532).isSome = true := by
  decide +kernel

theorem k2111_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2111) 3).1
      15932706148790605670257723251819077671424514727298022143532580213319236674008341630274353).isSome = true := by
  decide +kernel

theorem k2111_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 2111) 3).2
      52704013479518083884562884137157271865565867753839058357176843324).isSome = true := by
  decide +kernel

theorem c3 : allCells dirCell 2112 2113 [
    75180576719606743387503051351890436986100234843310496203752667209517902472928720654413783631341800884054192371] = true := by
  decide +kernel

theorem c4 : allCells dirCell 2113 2131 [
    3885463419765860149253647309057060203726452436044021324711952689333024060462525301105,
    147528918345484814372, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] = true := by
  decide +kernel

theorem c5 : allCells dirCell 2131 2132 [
    849136684109129585465003917312199427861562964885966064690812707] = true := by
  decide +kernel

theorem k2132_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2132) 3).1
      18373956121899567256975952079264557142028071817978429883944958488918568355418075813586019829037900261190).isSome = true := by
  decide +kernel

theorem k2132_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 2132) 3).2
      117534244705829724417599889067203007242697273852139647161496676799435010298438209457706918743885323945583147237908446096322088116346975958589065265384668237986362866).isSome = true := by
  decide +kernel

theorem k2133_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2133) 3).1
      117105794127408153569629380198579080827222017501739228805735403182532335228692412194586547839265082363765376643804124016884458915789609339713182346576405083286762994).isSome = true := by
  decide +kernel

theorem k2133_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2133) 3).2 2).1
      3938618444140279247030354403039828518845846598111157739610775596511245844650137078012).isSome = true := by
  decide +kernel

theorem k2133_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2133) 3).2 2).2
      3847201860481840611273555843752431411034134019017858995748380547912345586843475324).isSome = true := by
  decide +kernel

theorem k2134_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2134) 2).1 3).1
      62862345166298651454860212610801288716996052139215429048009591720723853186241686096700).isSome = true := by
  decide +kernel

theorem k2134_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2134) 2).1 3).2
      62747483263848140589651638121868386916559525471373769770120012746979103377444147024700).isSome = true := by
  decide +kernel

theorem k2134_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2134) 2).2 3).1
      61403800457975230629933845154206756046319799916126774141101931848079443907893909308).isSome = true := by
  decide +kernel

theorem k2134_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2134) 2).2 3).2
      15687755590556070167419227499016799358370874131931115399327127652037723103642615534396).isSome = true := by
  decide +kernel

theorem k2135_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2135) 2).1 3).1
      15659441225976178635165002331525049882508957369328291989659718965067638667453367042876).isSome = true := by
  decide +kernel

theorem k2135_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2135) 2).1 3).2
      977548181391754831052161614407327791614965317038606233473298446217758136293457230908).isSome = true := by
  decide +kernel

theorem k2135_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2135) 2).2 3).1
      13583527041827688160648599844347534519232734542785245439191393706812).isSome = true := by
  decide +kernel

theorem k2135_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2135) 2).2 3).2
      211986225927492428812192465438009148276963437598122258427314797628).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 2109 2136 :=
  (Cover.one (box := dirCellBox) (n := 2109)
      (.split 3 (.leaf _ k2109_0) (.leaf _ k2109_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 2110)
      (.split 3 (.leaf _ k2110_0) (.leaf _ k2110_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 2111)
      (.split 3 (.leaf _ k2111_0) (.leaf _ k2111_1))).trans <|
  (Cover.dir c3).trans <|
  (Cover.dir c4).trans <|
  (Cover.dir c5).trans <|
  (Cover.one (box := dirCellBox) (n := 2132)
      (.split 3 (.leaf _ k2132_0) (.leaf _ k2132_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 2133)
      (.split 3 (.leaf _ k2133_0) (.split 2 (.leaf _ k2133_1) (.leaf _ k2133_2)))).trans <|
  (Cover.one (box := dirCellBox) (n := 2134)
      (.split 2 (.split 3 (.leaf _ k2134_0) (.leaf _ k2134_1)) (.split 3 (.leaf _ k2134_2) (.leaf _ k2134_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 2135)
      (.split 2 (.split 3 (.leaf _ k2135_0) (.leaf _ k2135_1)) (.split 3 (.leaf _ k2135_2) (.leaf _ k2135_3))))

end C4.Cert.Dir031
