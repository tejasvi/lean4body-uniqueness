module

public import C4Check

public section

/-! Cells `2336 ≤ n < 2355` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir036

theorem c0 : allCells dirCell 2336 2353 [
    43578350774485033300612756605373682600540, 43556321582919213019578969815973028090204,
    147517263659930108884, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3] = true := by
  decide +kernel

theorem k2353_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2353) 1).1
      3).isSome = true := by
  decide +kernel

theorem k2353_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2353) 1).2 2).1
      7025019245504323290544230390147156104813351356932613616220825351962457055080255243732940263523919245841187258143230611551427425483970729722952166947599).isSome = true := by
  decide +kernel

theorem k2353_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2353) 1).2 2).2
      1308172450028038646683651102105559987682342419220080720816577024162257445890899279381794888057684209916980763407).isSome = true := by
  decide +kernel

theorem k2354_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2354) 3).1 2).1 3).1
      127548115546435875393455885606639137658004629188184353636811704130849015567336259404904144301283605149472986806640906810404047679878020772697077725399316294051783086922782).isSome = true := by
  decide +kernel

theorem k2354_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2354) 3).1 2).1 3).2
      126075286173259912516762536212850578205125675071775221851064603417913675315199715027287060816035964681085060139427812079141787047994343280276239016717986336015854428904478).isSome = true := by
  decide +kernel

theorem k2354_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2354) 3).1 2).2 3).1
      19542637159936436339179022984164283452630663131779676358309355113159467353279436820192415649304120765133894).isSome = true := by
  decide +kernel

theorem k2354_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2354) 3).1 2).2 3).2 2).1
      18853880852919757348429047819377782008880520700544909235956270429897590104018038314390661844595505318225).isSome = true := by
  decide +kernel

theorem k2354_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2354) 3).1 2).2 3).2 2).2
      64031206018628069605835473120135687271766706129220496735427503222855684266533907409).isSome = true := by
  decide +kernel

theorem k2354_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2354) 3).2 2).1 3).1 2).1
      21820584241730790203681878051319059636638387643496860801488182197011535665793897628310430268914278464420469571757237962318663).isSome = true := by
  decide +kernel

theorem k2354_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2354) 3).2 2).1 3).1 2).2
      296764185660092250970994147282987288563940076117561266582778150204128722669428871680027347383765072381189).isSome = true := by
  decide +kernel

theorem k2354_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2354) 3).2 2).1 3).2 2).1
      22224733691310808522264650431705745270776170343916946162087415399868231202321760615651394645649482494276865807769637378046252877).isSome = true := by
  decide +kernel

theorem k2354_8 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2354) 3).2 2).1 3).2 2).2
      21761393366010840740425672074012363078173325938576428925987111791471050709581029940574889995343566567609540512335633596891977).isSome = true := by
  decide +kernel

theorem k2354_9 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2354) 3).2 2).2 3).1 2).1
      5509683783411277793543957703593667961268137129364207511949307592092979106685356158051556314215252978708607011948082156417393).isSome = true := by
  decide +kernel

theorem k2354_10 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2354) 3).2 2).2 3).1 2).2
      4679117842943254955865569725576316722845114442583414399258575016013462274273024577254494592308858109969).isSome = true := by
  decide +kernel

theorem k2354_11 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2354) 3).2 2).2 3).2 2).1
      5455458801572160410685670742025200970680210922451214245127441207322797034984799771275852946374281457393428410058271333151089).isSome = true := by
  decide +kernel

theorem k2354_12 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2354) 3).2 2).2 3).2 2).2
      74241146825622537832769596931497539388475637178989690613174713453226767766454120284938044198465691878769).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 2336 2355 :=
  (Cover.dir c0).trans <|
  (Cover.one (box := dirCellBox) (n := 2353)
      (.split 1 (.leaf _ k2353_0) (.split 2 (.leaf _ k2353_1) (.leaf _ k2353_2)))).trans <|
  (Cover.one (box := dirCellBox) (n := 2354)
      (.split 3 (.split 2 (.split 3 (.leaf _ k2354_0) (.leaf _ k2354_1)) (.split 3 (.leaf _ k2354_2) (.split 2 (.leaf _ k2354_3) (.leaf _ k2354_4)))) (.split 2 (.split 3 (.split 2 (.leaf _ k2354_5) (.leaf _ k2354_6)) (.split 2 (.leaf _ k2354_7) (.leaf _ k2354_8))) (.split 3 (.split 2 (.leaf _ k2354_9) (.leaf _ k2354_10)) (.split 2 (.leaf _ k2354_11) (.leaf _ k2354_12))))))

end C4.Cert.Dir036
