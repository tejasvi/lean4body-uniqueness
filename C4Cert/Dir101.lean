module

public import C4Check

public section

/-! Cells `3279 ≤ n < 3284` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir101

theorem k3279_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3279) 3).1
      25913899090640943583209749389157463351788706124673012775859222673166981291731837096230504451255899115979773853128777554237555735885120813263029710).isSome = true := by
  decide +kernel

theorem k3279_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3279) 3).2 2).1
      348617732995949300001651073489380473404050268759554999384785806276024430988041176567208049000057353998658074828981598547965169).isSome = true := by
  decide +kernel

theorem k3279_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3279) 3).2 2).2
      18425161797013669745026391021357302376945809665746952448589272644218956213371525751342686486759259620721).isSome = true := by
  decide +kernel

theorem k3280_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3280) 3).1 2).1
      4696690672128351079520290922778719126140231184196390582946809244745057694609425598855234938768172521452785).isSome = true := by
  decide +kernel

theorem k3280_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3280) 3).1 2).2
      293635996604106903007717572560576700358254304961402970635438807053995328573850534516422300668536857023292).isSome = true := by
  decide +kernel

theorem k3280_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3280) 3).2 2).1
      19150182374663002621306159756368696602348500586386298334308970033376064233104227834346630139485144287987484913).isSome = true := by
  decide +kernel

theorem k3280_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3280) 3).2 2).2
      54977215393518983529606020329597995094265657940347087471713791521596).isSome = true := by
  decide +kernel

theorem k3281_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3281) 3).1 2).1
      76329497355243529280248012344747830991277423371911908851431387280690771967439446752825074842926626067384877884).isSome = true := by
  decide +kernel

theorem k3281_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3281) 3).1 2).2
      3423904311880454775664353826601792704519882294607622266278639027004).isSome = true := by
  decide +kernel

theorem k3281_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3281) 3).2 2).1
      297307573541228666142469302130996066658984604846427109701912719114802489078099711667167968624766587675933756).isSome = true := by
  decide +kernel

theorem k3281_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3281) 3).2 2).2
      213390652311778120092045735970041668440552992112743288868037295164).isSome = true := by
  decide +kernel

theorem k3282_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3282) 2).1 3).1
      296631580465118064807551544220903981095381381736774293819343831095085566017689193641046101062110514897026108).isSome = true := by
  decide +kernel

theorem k3282_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3282) 2).1 3).2
      4012145426170321293625421672025318991387073374714211884406839432481101880454364991896636).isSome = true := by
  decide +kernel

theorem k3282_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3282) 2).2 1).1
      16069538538825350480129531703483661465369839012539294645809075934877717417028655936240700).isSome = true := by
  decide +kernel

theorem k3282_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3282) 2).2 1).2
      16052745491875992837443851495229018118199658914126892423763476124493380457063038400745267).isSome = true := by
  decide +kernel

theorem k3283_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3283) 3).1 2).1
      16023841481669494747480288224687078816795093444594962957255982029654726877980552342977596).isSome = true := by
  decide +kernel

theorem k3283_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3283) 3).1 2).2
      4007554558849541137034352423084328196324709837904228925904044034959191915403148428885052).isSome = true := by
  decide +kernel

theorem k3283_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3283) 3).2 2).1
      4001413311411383003931620371740794855403446676587859140225119351708095966919115262508092).isSome = true := by
  decide +kernel

theorem k3283_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3283) 3).2 2).2
      4002412345179156160789770420198465157443650715641613392272122720325694871893855537249340).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 3279 3284 :=
  (Cover.one (box := dirCellBox) (n := 3279)
      (.split 3 (.leaf _ k3279_0) (.split 2 (.leaf _ k3279_1) (.leaf _ k3279_2)))).trans <|
  (Cover.one (box := dirCellBox) (n := 3280)
      (.split 3 (.split 2 (.leaf _ k3280_0) (.leaf _ k3280_1)) (.split 2 (.leaf _ k3280_2) (.leaf _ k3280_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 3281)
      (.split 3 (.split 2 (.leaf _ k3281_0) (.leaf _ k3281_1)) (.split 2 (.leaf _ k3281_2) (.leaf _ k3281_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 3282)
      (.split 2 (.split 3 (.leaf _ k3282_0) (.leaf _ k3282_1)) (.split 1 (.leaf _ k3282_2) (.leaf _ k3282_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 3283)
      (.split 3 (.split 2 (.leaf _ k3283_0) (.leaf _ k3283_1)) (.split 2 (.leaf _ k3283_2) (.leaf _ k3283_3))))

end C4.Cert.Dir101
