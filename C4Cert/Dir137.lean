module

public import C4Check

public section

/-! Cells `4039 ≤ n < 4064` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir137

theorem k4039_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4039) 2).1 3).1
      288305436034041662122306064882638970891392151052330619565546481422604859077371581010344719856588255908668).isSome = true := by
  decide +kernel

theorem k4039_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4039) 2).1 3).2
      288007459568041209557564685104763938431381619942209690787270236921636971612669806224644507947096377643836).isSome = true := by
  decide +kernel

theorem k4039_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4039) 2).2 3).1
      3908645623842298500993906419091218921448970242299752789850962862397372814949008929340).isSome = true := by
  decide +kernel

theorem k4039_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4039) 2).2 3).2
      15617481451188401113422702285887111426991233626604188693600985807551759982879940528700).isSome = true := by
  decide +kernel

theorem k4040_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4040) 3).1 2).1
      206475463814303365963299388415756200835935749945358069895552316).isSome = true := by
  decide +kernel

theorem k4040_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4040) 3).1 2).2
      71967320040946783657237942286907119754347468349468790475891820669890203861708544905544224374569930454588).isSome = true := by
  decide +kernel

theorem k4040_2 : (checkBoxH dirMode depth (splitBox (dirCellBox 4040) 3).2
      339631090013498617179814444534406772523863280419018025481922385213706126985544087252880856588788254743978522756634845285807346).isSome = true := by
  decide +kernel

theorem k4041_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4041) 3).1
      339432296332488433005630149682570036422840519026716957956876795329101099441523149560589050833617069740057554257654297430422770).isSome = true := by
  decide +kernel

theorem k4041_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4041) 3).2
      339270094033772183555099822427605290188762677984558082788416047901358218117827937095248329146376741162176603516361230346712306).isSome = true := by
  decide +kernel

theorem k4042_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4042) 2).1
      1356220723337175910150411775912626293149186468634025095353854652585467057319825617816289523602228063030830850682646484280505596).isSome = true := by
  decide +kernel

theorem k4042_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4042) 2).2
      4595518708463123830534184359541325601323969227813808489984026198813665131576117345726849174575816084648188).isSome = true := by
  decide +kernel

theorem k4043_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4043) 3).1
      84734468886407750113241480886263130031954632228736566490577847689312948280924271177708562693168442726770257004205492638937340).isSome = true := by
  decide +kernel

theorem k4043_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4043) 3).2
      71757575191952289047942617227657429154708083469410098630808279608717640214931546035588517241426852920690).isSome = true := by
  decide +kernel

theorem c5 : allCells dirCell 4044 4045 [
    115284505118061571666678127517029094577475630600774694638900175231240041299978359302968325729772486110370131445145429406979411019008907083202401253152790533673154034] = true := by
  decide +kernel

theorem c6 : allCells dirCell 4045 4046 [
    1323014371884169681513576427303244481145683960032960774988672483518091746299553906033677931985036478921759087955115947104626] = true := by
  decide +kernel

theorem c7 : allCells dirCell 4046 4063 [
    51445577415976556921947043117486597238776884258259933855182482, 9447491259964758023426, 1, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    16204465406296077527836576139446313394870717637300193201022913347296158160034179261619] = true := by
  decide +kernel

theorem k4063_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4063) 3).1 2).1
      4024563897519262683498517486190638916062385147628283954466783113923447112736334993202).isSome = true := by
  decide +kernel

theorem k4063_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4063) 3).1 2).2
      15712117499923574800712916760671114671780941306609519695990818116866590781023324529).isSome = true := by
  decide +kernel

theorem k4063_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4063) 3).2 2).1
      3994567404978302746346874157909876476647801876484869706743810798017322308118339966769).isSome = true := by
  decide +kernel

theorem k4063_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4063) 3).2 2).2
      3994614072809159587634213087557775510396264812379223538355141429263268103742406842161).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 4039 4064 :=
  (Cover.one (box := dirCellBox) (n := 4039)
      (.split 2 (.split 3 (.leaf _ k4039_0) (.leaf _ k4039_1)) (.split 3 (.leaf _ k4039_2) (.leaf _ k4039_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 4040)
      (.split 3 (.split 2 (.leaf _ k4040_0) (.leaf _ k4040_1)) (.leaf _ k4040_2))).trans <|
  (Cover.one (box := dirCellBox) (n := 4041)
      (.split 3 (.leaf _ k4041_0) (.leaf _ k4041_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 4042)
      (.split 2 (.leaf _ k4042_0) (.leaf _ k4042_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 4043)
      (.split 3 (.leaf _ k4043_0) (.leaf _ k4043_1))).trans <|
  (Cover.dir c5).trans <|
  (Cover.dir c6).trans <|
  (Cover.dir c7).trans <|
  (Cover.one (box := dirCellBox) (n := 4063)
      (.split 3 (.split 2 (.leaf _ k4063_0) (.leaf _ k4063_1)) (.split 2 (.leaf _ k4063_2) (.leaf _ k4063_3))))

end C4.Cert.Dir137
