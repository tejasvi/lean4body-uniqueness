module

public import C4Check

public section

/-! Cells `3671 ≤ n < 3677` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir124

theorem k3671_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3671) 3).1 2).1
      74175007088897791223901887875769250664141472463932700689625448553452399156931646530035001271669967121779).isSome = true := by
  decide +kernel

theorem k3671_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3671) 3).1 2).2
      15729925982603594696108291562258640917163076088206343954137570764307514429076246897).isSome = true := by
  decide +kernel

theorem k3671_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3671) 3).2 2).1
      255894115243705765679815706400911960347857225491682888916352432992778672115592223626441).isSome = true := by
  decide +kernel

theorem k3671_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3671) 3).2 2).2
      295075658808369229401761992941879549842869578563281062435365839411004862711827608330295313697228493148988).isSome = true := by
  decide +kernel

theorem k3672_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3672) 3).1 2).1
      4693435017775401413593535957418481008164725490349490404483263435387953011970914082940701692869482914274481).isSome = true := by
  decide +kernel

theorem k3672_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3672) 3).1 2).2
      15907373119790240827162047869589681120078964107780022544414689377748496357388027675452).isSome = true := by
  decide +kernel

theorem k3672_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3672) 3).2 2).1
      299035216451171732507198401504325703856904334381507240403048080667201611896596462537662178826739961232248625).isSome = true := by
  decide +kernel

theorem k3672_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3672) 3).2 2).2
      989900601943206313150268498693129306446333868809833736210122111019884643619323083836).isSome = true := by
  decide +kernel

theorem k3673_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3673) 2).1 3).1
      18626335195630544720795116331459608187481161260990079680522991990631719644146705532080353377289358668151868).isSome = true := by
  decide +kernel

theorem k3673_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3673) 2).1 3).2
      18574283763288173181163588951609341190083570376795771492225148344562544393235871640148628632532751501179964).isSome = true := by
  decide +kernel

theorem k3673_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3673) 2).2 3).1
      855541412606421470205947427298988070475446732703411169076364753980).isSome = true := by
  decide +kernel

theorem k3673_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3673) 2).2 3).2
      18581040539627208514373133445263581743095866558991630832395594154969366483023550110456606084409144439684156).isSome = true := by
  decide +kernel

theorem k3674_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3674) 2).1 3).1
      18532059725349302698528597359712003050549408003495706709463982690024536370467105248348179285810793632185404).isSome = true := by
  decide +kernel

theorem k3674_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3674) 2).1 3).2
      4010547500897136179340305512890613903931495072317816320617986401746747572157109519142705).isSome = true := by
  decide +kernel

theorem k3674_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3674) 2).2 1).1
      62753105201364190744999591728787570394893137847965744808169424170048909303075368154060).isSome = true := by
  decide +kernel

theorem k3674_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3674) 2).2 1).2
      62741910103749870225098985053772498462005171844756245035815151419228045989669427295180).isSome = true := by
  decide +kernel

theorem k3675_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3675) 2).1 3).1
      212055468048146577181537251872724414917214811513779101063572192316).isSome = true := by
  decide +kernel

theorem k3675_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3675) 2).1 3).2
      3388712144300890804965503085184867700498834266532147835058341266236).isSome = true := by
  decide +kernel

theorem k3675_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3675) 2).2 3).1
      13574175302670112187837560328125398155253323901500384184062372035644).isSome = true := by
  decide +kernel

theorem k3675_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3675) 2).2 3).2
      45933555847944748807258596274467620887129799740).isSome = true := by
  decide +kernel

theorem k3676_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3676) 3).1 2).1
      3385330470297814921382893248061194349361874606161315820605896377148).isSome = true := by
  decide +kernel

theorem k3676_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3676) 3).1 2).2
      211656651604767747065974268372548279444313448802124730044652551228).isSome = true := by
  decide +kernel

theorem k3676_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3676) 3).2 2).1
      845645872043683251242225092596922598436342227173951255682758460220).isSome = true := by
  decide +kernel

theorem k3676_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3676) 3).2 2).2
      211475951303984633485398743443418736796639358592386754975782239292).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 3671 3677 :=
  (Cover.one (box := dirCellBox) (n := 3671)
      (.split 3 (.split 2 (.leaf _ k3671_0) (.leaf _ k3671_1)) (.split 2 (.leaf _ k3671_2) (.leaf _ k3671_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 3672)
      (.split 3 (.split 2 (.leaf _ k3672_0) (.leaf _ k3672_1)) (.split 2 (.leaf _ k3672_2) (.leaf _ k3672_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 3673)
      (.split 2 (.split 3 (.leaf _ k3673_0) (.leaf _ k3673_1)) (.split 3 (.leaf _ k3673_2) (.leaf _ k3673_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 3674)
      (.split 2 (.split 3 (.leaf _ k3674_0) (.leaf _ k3674_1)) (.split 1 (.leaf _ k3674_2) (.leaf _ k3674_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 3675)
      (.split 2 (.split 3 (.leaf _ k3675_0) (.leaf _ k3675_1)) (.split 3 (.leaf _ k3675_2) (.leaf _ k3675_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 3676)
      (.split 3 (.split 2 (.leaf _ k3676_0) (.leaf _ k3676_1)) (.split 2 (.leaf _ k3676_2) (.leaf _ k3676_3))))

end C4.Cert.Dir124
