module

public import C4Check

public section

/-! Cells `3621 ≤ n < 3645` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir116

theorem k3621_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3621) 2).1 3).1
      339224360282272075490844864260248262211411752291333957297271604221220716234814019053963420528900192928252809047536973480555761).isSome = true := by
  decide +kernel

theorem k3621_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3621) 2).1 3).2
      21205789016127387041586691856057825395333503205678291928323838811371440656277247376368614250768790196117449038386134075268284).isSome = true := by
  decide +kernel

theorem k3621_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3621) 2).2 3).1 1).1
      243436517133197075260111072656775581630575195581320918503735235519123474229797189180).isSome = true := by
  decide +kernel

theorem k3621_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3621) 2).2 3).1 1).2
      13196793443443144054654251351121807329543772850951478554850350908).isSome = true := by
  decide +kernel

theorem k3621_4 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3621) 2).2 3).2
      84789081406602932832022270022658706899910032856943237871504219982894688200278575312556288834384634925575139325217929672875441).isSome = true := by
  decide +kernel

theorem k3622_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3622) 2).1
      7381266152123183682786403430815494687239566713431926285378111483059199646572355294440949124876086316986906823074396322718981533714206822158059134681948049909490177735).isSome = true := by
  decide +kernel

theorem k3622_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3622) 2).2 3).1
      5297935855598094524012938906908070190106702902723688969702100543244984862902090487707827123676257051368455530665178213898044).isSome = true := by
  decide +kernel

theorem k3622_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3622) 2).2 3).2
      71777494105366845462050363858764840329222784175881542016013563386808825613251451048373703927693664673201).isSome = true := by
  decide +kernel

theorem k3623_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3623) 2).1
      17944796985764949211825931006921021779548852884169020874773404029866995140079579290313705437019939517895).isSome = true := by
  decide +kernel

theorem k3623_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 3623) 2).2
      1355263740649025993727675150130022730661828700591770576102878626159500266231112416379958389484183141848916515747049738040866035).isSome = true := by
  decide +kernel

theorem c3 : allCells dirCell 3624 3625 [
    24994219516433123650578150676390551972102464536766643949163384178429354382782375930212842703074984243326367082160927849395739076951416432321587526] = true := by
  decide +kernel

theorem c4 : allCells dirCell 3625 3642 [
    44626375050785128030599830885942700726374662, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] = true := by
  decide +kernel

theorem k3642_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3642) 3).1
      34118765714487102017229121370767216799601763).isSome = true := by
  decide +kernel

theorem k3642_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3642) 3).2 2).1 3).1
      15932010345378878575541715780412709868218068344663157211556035268453916370915916145).isSome = true := by
  decide +kernel

theorem k3642_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3642) 3).2 2).1 3).2
      299027819818577118128104252112766716375436715635207845148475404513163695437862883699515669336447150376393).isSome = true := by
  decide +kernel

theorem k3642_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3642) 3).2 2).2
      22100490498992875782233177264205714108336766373258617104681340965025114785930994414862084712085994570549299921620447100337991).isSome = true := by
  decide +kernel

theorem k3643_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3643) 3).1 2).1 3).1
      76287675555044457907550031832826837336154221903828365680594251630934459644514244159770279836614920028124401).isSome = true := by
  decide +kernel

theorem k3643_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3643) 3).1 2).1 3).2
      19402576348753415495522046145780024234057969856757499998005759115311716980031979950010352573224103409133706441).isSome = true := by
  decide +kernel

theorem k3643_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3643) 3).1 2).2 3).1
      252145282570106767132812335856818041536753492001132481145224461496289865170896264561).isSome = true := by
  decide +kernel

theorem k3643_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3643) 3).1 2).2 3).2
      257302120069370968642964303932424708386267756449320011177717002431570480922609229518025).isSome = true := by
  decide +kernel

theorem k3643_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3643) 3).2 2).1 1).1
      6573596506234818825777159311765275219649289608441290422543878007449975199055036482479290119631343497280604377455081784982886009110048701872877697842).isSome = true := by
  decide +kernel

theorem k3643_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3643) 3).2 2).1 1).2
      26256388706154427311916009223335553708043656646436329545315666171032878786908668713386256920679790844827758269296583199197369805108220922806226279630).isSome = true := by
  decide +kernel

theorem k3643_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3643) 3).2 2).2 3).1
      4097179129181685983645045433273942718419520713870881612515317061387328253455984497417393).isSome = true := by
  decide +kernel

theorem k3643_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3643) 3).2 2).2 3).2
      89006371733965782639774948535241900307203745157396961081119602654027381359025910564705123998807504908577296237035709866912087217).isSome = true := by
  decide +kernel

theorem k3644_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3644) 2).1 3).1 2).1 1).1
      215356384293085072287316432127497228137144168247399532113390284492).isSome = true := by
  decide +kernel

theorem k3644_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3644) 2).1 3).1 2).1 1).2
      3971027949737888948908759803881500412962838555961149827910801548962391661887765338828).isSome = true := by
  decide +kernel

theorem k3644_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3644) 2).1 3).1 2).2 1).1
      13454897807535812406057743210630498298648112490447370412585622220).isSome = true := by
  decide +kernel

theorem k3644_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3644) 2).1 3).1 2).2 1).2
      3972399962966887831699602996190826528226014919050752863986546749111147712597873646284).isSome = true := by
  decide +kernel

theorem k3644_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3644) 2).1 3).2 2).1 1).1
      214329943495789851917463472119287171476113380544887692401170701004).isSome = true := by
  decide +kernel

theorem k3644_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3644) 2).1 3).2 2).1 1).2
      214252206690942638190158567128560465536885957221045734471540136652).isSome = true := by
  decide +kernel

theorem k3644_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3644) 2).1 3).2 2).2 1).1
      13400556692609270085788908837546245959808470144760062385344453324).isSome = true := by
  decide +kernel

theorem k3644_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3644) 2).1 3).2 2).2 1).2
      3953827700685042337858612820710717390688417183978825727035419299347077030073788259020).isSome = true := by
  decide +kernel

theorem k3644_8 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3644) 2).2 3).1 2).1
      1199798074783647352618289052908909970118682948581521091905137825234491864143374486343411248549669122872040241).isSome = true := by
  decide +kernel

theorem k3644_9 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3644) 2).2 3).1 2).2
      75075620203382656067179888467538861165367551684657765914881630333325910535317249349295036788279873449859889).isSome = true := by
  decide +kernel

theorem k3644_10 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3644) 2).2 3).2 2).1 1).1
      13404790340272680420453333158767349932435602642818900197677439692).isSome = true := by
  decide +kernel

theorem k3644_11 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3644) 2).2 3).2 2).1 1).2
      214398303193441550857201414846527619873931689224459218140089797324).isSome = true := by
  decide +kernel

theorem k3644_12 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3644) 2).2 3).2 2).2
      4782916518103620415606184111183157330837471178950407556036997205546733687329728707500581224395129837081713457).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 3621 3645 :=
  (Cover.one (box := dirCellBox) (n := 3621)
      (.split 2 (.split 3 (.leaf _ k3621_0) (.leaf _ k3621_1)) (.split 3 (.split 1 (.leaf _ k3621_2) (.leaf _ k3621_3)) (.leaf _ k3621_4)))).trans <|
  (Cover.one (box := dirCellBox) (n := 3622)
      (.split 2 (.leaf _ k3622_0) (.split 3 (.leaf _ k3622_1) (.leaf _ k3622_2)))).trans <|
  (Cover.one (box := dirCellBox) (n := 3623)
      (.split 2 (.leaf _ k3623_0) (.leaf _ k3623_1))).trans <|
  (Cover.dir c3).trans <|
  (Cover.dir c4).trans <|
  (Cover.one (box := dirCellBox) (n := 3642)
      (.split 3 (.leaf _ k3642_0) (.split 2 (.split 3 (.leaf _ k3642_1) (.leaf _ k3642_2)) (.leaf _ k3642_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 3643)
      (.split 3 (.split 2 (.split 3 (.leaf _ k3643_0) (.leaf _ k3643_1)) (.split 3 (.leaf _ k3643_2) (.leaf _ k3643_3))) (.split 2 (.split 1 (.leaf _ k3643_4) (.leaf _ k3643_5)) (.split 3 (.leaf _ k3643_6) (.leaf _ k3643_7))))).trans <|
  (Cover.one (box := dirCellBox) (n := 3644)
      (.split 2 (.split 3 (.split 2 (.split 1 (.leaf _ k3644_0) (.leaf _ k3644_1)) (.split 1 (.leaf _ k3644_2) (.leaf _ k3644_3))) (.split 2 (.split 1 (.leaf _ k3644_4) (.leaf _ k3644_5)) (.split 1 (.leaf _ k3644_6) (.leaf _ k3644_7)))) (.split 3 (.split 2 (.leaf _ k3644_8) (.leaf _ k3644_9)) (.split 2 (.split 1 (.leaf _ k3644_10) (.leaf _ k3644_11)) (.leaf _ k3644_12)))))

end C4.Cert.Dir116
