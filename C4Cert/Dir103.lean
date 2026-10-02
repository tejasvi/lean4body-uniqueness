module

public import C4Check

public section

/-! Cells `3309 ≤ n < 3317` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir103

theorem k3309_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3309) 3).1 2).1
      856131308342251214572942710156427069567346623821405785585880527420).isSome = true := by
  decide +kernel

theorem k3309_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3309) 3).1 2).2
      856205736329945134482249116314528345316203983678017417514761712188).isSome = true := by
  decide +kernel

theorem k3309_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3309) 3).2 2).1
      213439104377395444058491156362411215953892994556655704984493325372).isSome = true := by
  decide +kernel

theorem k3309_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3309) 3).2 2).2
      213469500065622256793786028646638634685919636366276855185922686012).isSome = true := by
  decide +kernel

theorem k3310_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3310) 2).1
      77650542916917012798474201703499163270281953580076584483737351514817700057983186747214555740748218048661572415731).isSome = true := by
  decide +kernel

theorem k3310_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 3310) 2).2
      77668185153330573493393503275656559889860889886339660289656837777466838958888225587819322779317301559181176074483).isSome = true := by
  decide +kernel

theorem k3311_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3311) 3).1 2).1
      1002158784046309157378362019496533059112022215883664289866952780690850988388767696895036).isSome = true := by
  decide +kernel

theorem k3311_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3311) 3).1 2).2
      11506031552729109870859730528147354644528315452).isSome = true := by
  decide +kernel

theorem k3311_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3311) 3).2 2).1
      217007743133869313569585135022668068828579460673347356448626783763516).isSome = true := by
  decide +kernel

theorem k3311_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3311) 3).2 2).2
      11491658317979141971623589427051293379085024316).isSome = true := by
  decide +kernel

theorem k3312_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3312) 3).1
      105306301751299519606968521160027200260631998542349071800493210421295143933262340237990131657035321596260975065844954832997832875895026325531748767693884).isSome = true := by
  decide +kernel

theorem k3312_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 3312) 3).2
      1683375753957904966081856016169811779533592279540814517265035992302446912121370960268743719103499661342071391392226350066975846210719145913391275932974140).isSome = true := by
  decide +kernel

theorem k3313_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3313) 2).1
      18850646087006540722260052849920116419890441065711327943872742255341181201320090593754498714125242035772310332).isSome = true := by
  decide +kernel

theorem k3313_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 3313) 2).2
      1022008741014711970185209845585879162695834093262600383884504022732328036205877586100288572).isSome = true := by
  decide +kernel

theorem k3314_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3314) 3).1
      255278805009529069561510648436378790074274864533706888252890034250043207882078582882761788).isSome = true := by
  decide +kernel

theorem k3314_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 3314) 3).2
      255169899589022202904411344444853306619574747415001094590162173048660673054835260563455036).isSome = true := by
  decide +kernel

theorem k3315_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3315) 1).1
      18377221999479417416622135981951398622022225297677719614256197599176281293101762169725372561811923560512572).isSome = true := by
  decide +kernel

theorem k3315_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 3315) 1).2
      15939388897479334783369357927147450189266903606141649767351190482451402680900631779261500).isSome = true := by
  decide +kernel

theorem c7 : allCells dirCell 3316 3317 [
    22202487437470759594405905159577451996663748430363154317416501337248339724771112172782910560006745629695635201699532534588208640243] = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 3309 3317 :=
  (Cover.one (box := dirCellBox) (n := 3309)
      (.split 3 (.split 2 (.leaf _ k3309_0) (.leaf _ k3309_1)) (.split 2 (.leaf _ k3309_2) (.leaf _ k3309_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 3310)
      (.split 2 (.leaf _ k3310_0) (.leaf _ k3310_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 3311)
      (.split 3 (.split 2 (.leaf _ k3311_0) (.leaf _ k3311_1)) (.split 2 (.leaf _ k3311_2) (.leaf _ k3311_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 3312)
      (.split 3 (.leaf _ k3312_0) (.leaf _ k3312_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 3313)
      (.split 2 (.leaf _ k3313_0) (.leaf _ k3313_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 3314)
      (.split 3 (.leaf _ k3314_0) (.leaf _ k3314_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 3315)
      (.split 1 (.leaf _ k3315_0) (.leaf _ k3315_1))).trans <|
  (Cover.dir c7)

end C4.Cert.Dir103
