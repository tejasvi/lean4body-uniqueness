module

public import C4Check

public section

/-! Cells `2052 ≤ n < 2077` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir028

theorem k2052_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2052) 3).1 2).1
      1151070641251543846044895321429913367900804941203511088043125168743452780444379581117566759039065338635212).isSome = true := by
  decide +kernel

theorem k2052_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2052) 3).1 2).2
      249617841956221963297798525670319416878882723800476247378422734730309459628781058433996).isSome = true := by
  decide +kernel

theorem k2052_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2052) 3).2 1).1
      3897168064080992766401899871112087005854481072660980086165467438856211665746283328204).isSome = true := by
  decide +kernel

theorem k2052_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2052) 3).2 1).2
      15587706644381894738790126650313064939142924295422302975562287326092758850545449945804).isSome = true := by
  decide +kernel

theorem k2053_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2053) 3).1
      86881230034354760548562649117907935148833120347339189179479787792245390494754634269523851861205283889858224406035779031018196786).isSome = true := by
  decide +kernel

theorem k2053_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 2053) 3).2
      5427011252283029261752324720805652206673451578319304223792085890692968546931919268123823001466542950126874885681464854226262834).isSome = true := by
  decide +kernel

theorem k2054_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2054) 3).1
      5424474247255846118666802866432895999298943815570378443816059551026485604217037263501904639943269117009878833103905828883520306).isSome = true := by
  decide +kernel

theorem k2054_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 2054) 3).2
      15932157868586057274892334026985204158838233669456902541520963025847585646964442457273137).isSome = true := by
  decide +kernel

theorem k2055_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2055) 2).1
      3887901585028643729127221204443111411795823869574355646230423043870006745431506622259).isSome = true := by
  decide +kernel

theorem k2055_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 2055) 2).2
      4590621212717165637069462742427040111998802021526063809682198953145831175260573325828840234030027301575475).isSome = true := by
  decide +kernel

theorem k2056_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2056) 2).1
      3886765170708131013557829804829299875001192409645070015573555804034796960537099392817).isSome = true := by
  decide +kernel

theorem k2056_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 2056) 2).2
      3887094734898207706390820596546681768331910087030562021187181184265976163249065547569).isSome = true := by
  decide +kernel

theorem c5 : allCells dirCell 2057 2075 [
    338485193461271419015976138215413035416702819073649860402492201533624675100019103801878397733182907929138552195161906893215174,
    2360751684762251565121, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3] = true := by
  decide +kernel

theorem c6 : allCells dirCell 2075 2076 [
    31163300813908791981713028071501453553794843336781832037007785176507475295141886803659540272031701043864570437041587148044653680388575737082316358102639523637509464192059] = true := by
  decide +kernel

theorem k2076_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2076) 3).1 2).1
      1355047179087736331639276307231600578382948329015218051170387293586779184607278684348613788099532448686353451962987426617713).isSome = true := by
  decide +kernel

theorem k2076_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2076) 3).1 2).2
      15537803449882367072148191203480236672934485901208153293450292547403971662497363315).isSome = true := by
  decide +kernel

theorem k2076_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2076) 3).2 2).1
      86267574981711650474117898215671008736738740377761933702136965728346752293648304670756674507117956604260494109481887929931249).isSome = true := by
  decide +kernel

theorem k2076_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2076) 3).2 2).2
      1348835907780511710330634655604789070053676865908530456579287139614029233703446503234196785646638102736512873121432165589361).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 2052 2077 :=
  (Cover.one (box := dirCellBox) (n := 2052)
      (.split 3 (.split 2 (.leaf _ k2052_0) (.leaf _ k2052_1)) (.split 1 (.leaf _ k2052_2) (.leaf _ k2052_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 2053)
      (.split 3 (.leaf _ k2053_0) (.leaf _ k2053_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 2054)
      (.split 3 (.leaf _ k2054_0) (.leaf _ k2054_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 2055)
      (.split 2 (.leaf _ k2055_0) (.leaf _ k2055_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 2056)
      (.split 2 (.leaf _ k2056_0) (.leaf _ k2056_1))).trans <|
  (Cover.dir c5).trans <|
  (Cover.dir c6).trans <|
  (Cover.one (box := dirCellBox) (n := 2076)
      (.split 3 (.split 2 (.leaf _ k2076_0) (.leaf _ k2076_1)) (.split 2 (.leaf _ k2076_2) (.leaf _ k2076_3))))

end C4.Cert.Dir028
