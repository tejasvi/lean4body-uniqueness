module

public import C4Check

public section

/-! Cells `3343 ≤ n < 3372` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir105

theorem k3343_0 : (checkBoxH dirMode depth (dirCellBox 3343)
      495535794314237741176830319392410396188786024593260275775817736271142920464852146754662078448010396273729947515067335243220600734324251835679051797701162752364095251785171772).isSome = true := by
  decide +kernel

theorem c1 : allCells dirCell 3344 3345 [
    75242799698288422915691118735601805468207849544419507675897271860676778718649354147668531596754569513598436156] = true := by
  decide +kernel

theorem c2 : allCells dirCell 3345 3346 [
    1387363779060667694832872603961188100516662240495088699760366893389836254015690341849712063544030955091193697431427361305424544572] = true := by
  decide +kernel

theorem c3 : allCells dirCell 3346 3347 [
    15548395208418962581939594521274224736869920344387013592594525711523735099905691599676] = true := by
  decide +kernel

theorem c4 : allCells dirCell 3347 3349 [
    15544750811624832807039820022276748738456774240601831981024550269246515221826073737585,
    51425578852072481269767440187607654922836044074597370604963345] = true := by
  decide +kernel

theorem c5 : allCells dirCell 3349 3365 [
    147554350805491154836, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    6362479737770113125576076336916812100603169790645905306600279909938675514069397148374174024071618024526939631782453590753660307372603726897194443] = true := by
  decide +kernel

theorem k3365_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3365) 2).1
      4032396803031063742049209656682962307674198724689534263338608455651016275869603108079859).isSome = true := by
  decide +kernel

theorem k3365_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 3365) 2).2
      1007958612487465186253714478290102242949599316020336072782398965216920905995092991040689).isSome = true := by
  decide +kernel

theorem k3366_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3366) 2).1
      1028284088467399029360336669323629572755894280364718583297576674801811594002471077884817651).isSome = true := by
  decide +kernel

theorem k3366_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 3366) 2).2
      18540346962043182486040096869849406579341437318483846161633416668828872779666317358726406325721291027856444).isSome = true := by
  decide +kernel

theorem k3367_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3367) 2).1
      16032889071655718627853245367306426258739386295114746814155281093831580747851068722854972).isSome = true := by
  decide +kernel

theorem k3367_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 3367) 2).2
      1002118263763192972452694410297870509697715786530378203071566633352727884248370851822652).isSome = true := by
  decide +kernel

theorem k3368_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3368) 2).1
      999961140973950166936622756865591018353687591646871349050864253712988356458709551103036).isSome = true := by
  decide +kernel

theorem k3368_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 3368) 2).2
      1000043292219172953347992373497143635682331784175151460166668210784545945882569594846268).isSome = true := by
  decide +kernel

theorem k3369_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3369) 1).1
      216504617059181729994738437149385346912683686402026613453544437791804).isSome = true := by
  decide +kernel

theorem k3369_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 3369) 1).2
      998485879818601619719162017512535801379401754854466874210190228262308490433357432437820).isSome = true := by
  decide +kernel

theorem k3370_0 : (checkBoxH dirMode depth (dirCellBox 3370)
      107552285051474320379861474833678401906364141969144976642522222113874259433176443260551758435887749889385183188827157874975643354703647938922630720819020604).isSome = true := by
  decide +kernel

theorem k3371_0 : (checkBoxH dirMode depth (dirCellBox 3371)
      104946307317905223185601243970672337919432562624654125043426172248179296544351458780248411308086826674685850328079997750270312193877021854902524031517500).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 3343 3372 :=
  (Cover.one (box := dirCellBox) (n := 3343)
      (.leaf _ k3343_0)).trans <|
  (Cover.dir c1).trans <|
  (Cover.dir c2).trans <|
  (Cover.dir c3).trans <|
  (Cover.dir c4).trans <|
  (Cover.dir c5).trans <|
  (Cover.one (box := dirCellBox) (n := 3365)
      (.split 2 (.leaf _ k3365_0) (.leaf _ k3365_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 3366)
      (.split 2 (.leaf _ k3366_0) (.leaf _ k3366_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 3367)
      (.split 2 (.leaf _ k3367_0) (.leaf _ k3367_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 3368)
      (.split 2 (.leaf _ k3368_0) (.leaf _ k3368_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 3369)
      (.split 1 (.leaf _ k3369_0) (.leaf _ k3369_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 3370)
      (.leaf _ k3370_0)).trans <|
  (Cover.one (box := dirCellBox) (n := 3371)
      (.leaf _ k3371_0))

end C4.Cert.Dir105
