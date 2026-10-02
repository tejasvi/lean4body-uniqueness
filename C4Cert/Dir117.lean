module

public import C4Check

public section

/-! Cells `3587 ≤ n < 3589` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir117

theorem k3587_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3587) 2).1 3).1 2).1 3).1
      1005083301391311944877697046357948220184403014787581214930551491871062159422629182524).isSome = true := by
  decide +kernel

theorem k3587_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3587) 2).1 3).1 2).1 3).2
      999795906669290031156355175626868555776951988543867680364127256751229170744553208892).isSome = true := by
  decide +kernel

theorem k3587_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3587) 2).1 3).1 2).2
      357862580839645544317740926178803961011124023827777358087920683028925128441204346492676172544181889264865605329594354754477575985).isSome = true := by
  decide +kernel

theorem k3587_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3587) 2).1 3).2 2).1
      5658480931316815907151378168024273852837226264577715065468008032669889634944184298201352390378067829723915947485952283574895243505).isSome = true := by
  decide +kernel

theorem k3587_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3587) 2).1 3).2 2).2
      354772372068676597627402698417156628481864364080623517251540164072305573076826277353708160284700639947605733926226176679172501745).isSome = true := by
  decide +kernel

theorem k3587_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3587) 2).2 3).1 2).1
      89562908879414730091974154378011819593491923850030337931725441874085069327844432234324347358734583681437794976159097191843450673).isSome = true := by
  decide +kernel

theorem k3587_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3587) 2).2 3).1 2).2
      22410874599144749599934116038811555795602693934474371505659243823684429013467993227140670115156953462162429342273349656587489073).isSome = true := by
  decide +kernel

theorem k3587_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3587) 2).2 3).2 2).1
      19252848467806315562485959114432295113917145613642152868453704042575605454290597185982731415373994894536027953).isSome = true := by
  decide +kernel

theorem k3587_8 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3587) 2).2 3).2 2).2
      65284772752023716362690334465519066228270669191844895804608073442916351366053391858356017).isSome = true := by
  decide +kernel

theorem k3588_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3588) 2).1 3).1 2).1
      88077280688703047630198232463248022836480266495241904300595367651054011259090148801217995487335992760563577286411542799314790641).isSome = true := by
  decide +kernel

theorem k3588_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3588) 2).1 3).1 2).2
      4778035919634416368022968452858880380003418056574735848849921698710658669121509205694717348081210153533688049).isSome = true := by
  decide +kernel

theorem k3588_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3588) 2).1 3).2 3).1
      74421892621795153222147954521882474608695596206283560900642551838630742448377292506396664178918885549765874).isSome = true := by
  decide +kernel

theorem k3588_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3588) 2).1 3).2 3).2
      342735824047436681950157245775560112197703806199609406872835003374494325770134007468229590371235208215030180847619701893592306).isSome = true := by
  decide +kernel

theorem k3588_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3588) 2).2 3).1 2).1
      298911021893807391961876745764306092694536766202348780529054362045158331619449368933207239425548285561401585).isSome = true := by
  decide +kernel

theorem k3588_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3588) 2).2 3).1 2).2
      299171676152695834920768511765682876018249990139104566250590353483195225642713713281256907794765723604480241).isSome = true := by
  decide +kernel

theorem k3588_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3588) 2).2 3).2 1).1
      87912854434916911881277244183383698796333645703621582679033340460945584975902008988180173373547021137985043706253886692098296380).isSome = true := by
  decide +kernel

theorem k3588_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3588) 2).2 3).2 1).2
      252237447150115472443432183713651608478638078352612754905049768136832095118718602408626).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 3587 3589 :=
  (Cover.one (box := dirCellBox) (n := 3587)
      (.split 2 (.split 3 (.split 2 (.split 3 (.leaf _ k3587_0) (.leaf _ k3587_1)) (.leaf _ k3587_2)) (.split 2 (.leaf _ k3587_3) (.leaf _ k3587_4))) (.split 3 (.split 2 (.leaf _ k3587_5) (.leaf _ k3587_6)) (.split 2 (.leaf _ k3587_7) (.leaf _ k3587_8))))).trans <|
  (Cover.one (box := dirCellBox) (n := 3588)
      (.split 2 (.split 3 (.split 2 (.leaf _ k3588_0) (.leaf _ k3588_1)) (.split 3 (.leaf _ k3588_2) (.leaf _ k3588_3))) (.split 3 (.split 2 (.leaf _ k3588_4) (.leaf _ k3588_5)) (.split 1 (.leaf _ k3588_6) (.leaf _ k3588_7)))))

end C4.Cert.Dir117
