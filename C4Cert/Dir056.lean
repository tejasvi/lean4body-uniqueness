module

public import C4Check

public section

/-! Cells `2672 ≤ n < 2745` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir056

theorem c0 : allCells dirCell 2672 2673 [
    3982276434346140185477600631033101147592482773942889399808823547351651266682004232777980] = true := by
  decide +kernel

theorem c1 : allCells dirCell 2673 2694 [
    3795999139630210718472251978904844301183263278308292646433308897326351144319343996,
    43557065440284661927931441791515524302684, 147531844352322428980, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0] = true := by
  decide +kernel

theorem c2 : allCells dirCell 2694 2696 [
    51879610707375777201528267598591673944967874056003235011065427,
    1001648659682150746931755933482060197581128299408686999004999179400017175148429123875057] = true := by
  decide +kernel

theorem c3 : allCells dirCell 2696 2697 [
    15619838326819490823356574179766419537770061369580454644027682097879432595418193052476] = true := by
  decide +kernel

theorem c4 : allCells dirCell 2697 2698 [
    249547054779114108000884510123958469282575123368806029818755858180778242463384179847996] = true := by
  decide +kernel

theorem c5 : allCells dirCell 2698 2700 [
    206194238239897085423287602946871245075006702629629518802279740,
    824055826072248158822769375920732633000136021230377084614964412] = true := by
  decide +kernel

theorem c6 : allCells dirCell 2700 2702 [
    823503267564418184269957573262220203273859614631316983399412924,
    3795882994171899275322990826902718914555593152278987593727962274845391616432889212] = true := by
  decide +kernel

theorem c7 : allCells dirCell 2702 2724 [
    43556636345630918286618218964393262404956, 147531224983691652020, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 2381496380658189014595,
    15272375216934790742622187279559396484094393916719759106575249503665961265707668851] = true := by
  decide +kernel

theorem c8 : allCells dirCell 2724 2727 [
    11204468370143802997368287132805983366165682,
    51599037233337565022358399422986429324431864244497379132015986,
    43660078743982227427642673045050982596444] = true := by
  decide +kernel

theorem c9 : allCells dirCell 2727 2731 [
    43623342716365761208031985195165292161372, 43594958031750725787126039879242970436444,
    43573072115126367060755734387225446698588, 43556288644285952918429218222951063228764] = true := by
  decide +kernel

theorem c10 : allCells dirCell 2731 2744 [
    147530886334120158788, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] = true := by
  decide +kernel

theorem k2744_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2744) 1).1
      593113807537229603184715855458740861706319699150).isSome = true := by
  decide +kernel

theorem k2744_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2744) 1).2 2).1 3).1
      0).isSome = true := by
  decide +kernel

theorem k2744_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2744) 1).2 2).1 3).2 3).1
      0).isSome = true := by
  decide +kernel

theorem k2744_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2744) 1).2 2).1 3).2 3).2 3).1
      265590854625570639997300079552724620034139194561963975686165962).isSome = true := by
  decide +kernel

theorem k2744_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2744) 1).2 2).1 3).2 3).2 3).2
      26242443122358204685295424168783191636213976022961198490472283131680095258407754249482846598524794655340985409201978014410186).isSome = true := by
  decide +kernel

theorem k2744_5 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2744) 1).2 2).2
      0).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 2672 2745 :=
  (Cover.dir c0).trans <|
  (Cover.dir c1).trans <|
  (Cover.dir c2).trans <|
  (Cover.dir c3).trans <|
  (Cover.dir c4).trans <|
  (Cover.dir c5).trans <|
  (Cover.dir c6).trans <|
  (Cover.dir c7).trans <|
  (Cover.dir c8).trans <|
  (Cover.dir c9).trans <|
  (Cover.dir c10).trans <|
  (Cover.one (box := dirCellBox) (n := 2744)
      (.split 1 (.leaf _ k2744_0) (.split 2 (.split 3 (.leaf _ k2744_1) (.split 3 (.leaf _ k2744_2) (.split 3 (.leaf _ k2744_3) (.leaf _ k2744_4)))) (.leaf _ k2744_5))))

end C4.Cert.Dir056
