module

public import C4Check

public section

/-! Cells `4490 ≤ n < 4517` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir150

theorem k4490_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4490) 2).1
      287316412226532630083455683849057999737586189239453954397762748946515380587280220485470035525393349858108).isSome = true := by
  decide +kernel

theorem k4490_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4490) 2).2
      15576837450881614765757606028030607476090038580687197649554991015172338243114848731964).isSome = true := by
  decide +kernel

theorem k4491_0 : (checkBoxH dirMode depth (dirCellBox 4491)
      557853572136775736306581489805906720019600575511910916528194559104475330839089224011524863311769774179569274778238566011059959419629335776942998844496799155936269746462593022693550268412732).isSome = true := by
  decide +kernel

theorem k4492_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4492) 2).1
      205921779401362009006376049097496208529117516662097973384535356).isSome = true := by
  decide +kernel

theorem k4492_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4492) 2).2
      62239940830864936136995279194350159627145965217118104597763491518033505093813622264636).isSome = true := by
  decide +kernel

theorem c3 : allCells dirCell 4493 4494 [
    5420061283096755124007266547973640624265853180798497488822030306720926932335721968663264745905642528163222229217489083153466354] = true := by
  decide +kernel

theorem c4 : allCells dirCell 4494 4495 [
    84666906345277330071858233769969563955839354847553749268734766633743061369824920132978055037969584229890910018653995824673020] = true := by
  decide +kernel

theorem c5 : allCells dirCell 4495 4496 [
    5290682630876454891195110140109328299070616177676361347610345816637443916212702610264545083264683235348763023910858888042300] = true := by
  decide +kernel

theorem c6 : allCells dirCell 4496 4498 [
    242903056420006270209563925423242207428510672345172317385826713779557868456911295729,
    3794918993575594860908949691222346624505642235787231621754554029443556672149020028] = true := by
  decide +kernel

theorem c7 : allCells dirCell 4498 4511 [
    174238772024524573247580277077087312816209, 43556159343883606865573917440076321554524,
    147565126981499754724, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] = true := by
  decide +kernel

theorem c8 : allCells dirCell 4511 4512 [
    102538246891849149656934178139325629673884477192395359866662910534409240751239811451480940192047571461751100674941813181945828185659756635556505035] = true := by
  decide +kernel

theorem k4512_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4512) 3).1
      3970038974933927340588827163749611720093144504779697581729386675340426250360333702962).isSome = true := by
  decide +kernel

theorem k4512_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4512) 3).2
      64808818577064123690172702728378555407908997484715286941246663088304811802780234608168138).isSome = true := by
  decide +kernel

theorem k4513_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4513) 2).1
      4028114933846956221157496044711769271358785246322214445968189247942858533531804778220339).isSome = true := by
  decide +kernel

theorem k4513_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4513) 2).2
      4028557404136647187096506263901251725258753097640646342409311232653621277441755160365875).isSome = true := by
  decide +kernel

theorem k4514_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4514) 2).1
      16063218632541202295034594523961067878325436818344287276946556907470358455983241828879153).isSome = true := by
  decide +kernel

theorem k4514_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4514) 2).2
      1004139787531409911953447090023604730003215844937868220870752702126512352308914714145585).isSome = true := by
  decide +kernel

theorem k4515_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4515) 2).1
      4617470219470064517265770359749809844122858704096402215311985206757959274571775538557672918812230980285388).isSome = true := by
  decide +kernel

theorem k4515_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4515) 2).2
      250352809779715468046911397180118965928363885151657663250513575370571579506069725787084).isSome = true := by
  decide +kernel

theorem k4516_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4516) 2).1
      1360219822077937484763383202427618419567167477449437826379172446540311522774161893071757278025995405436068312000879955977649212).isSome = true := by
  decide +kernel

theorem k4516_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4516) 2).2
      4609273399123482063859964719317100119777571906949750232034503381312745781974531938078868373051210010014668).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 4490 4517 :=
  (Cover.one (box := dirCellBox) (n := 4490)
      (.split 2 (.leaf _ k4490_0) (.leaf _ k4490_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 4491)
      (.leaf _ k4491_0)).trans <|
  (Cover.one (box := dirCellBox) (n := 4492)
      (.split 2 (.leaf _ k4492_0) (.leaf _ k4492_1))).trans <|
  (Cover.dir c3).trans <|
  (Cover.dir c4).trans <|
  (Cover.dir c5).trans <|
  (Cover.dir c6).trans <|
  (Cover.dir c7).trans <|
  (Cover.dir c8).trans <|
  (Cover.one (box := dirCellBox) (n := 4512)
      (.split 3 (.leaf _ k4512_0) (.leaf _ k4512_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 4513)
      (.split 2 (.leaf _ k4513_0) (.leaf _ k4513_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 4514)
      (.split 2 (.leaf _ k4514_0) (.leaf _ k4514_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 4515)
      (.split 2 (.leaf _ k4515_0) (.leaf _ k4515_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 4516)
      (.split 2 (.leaf _ k4516_0) (.leaf _ k4516_1)))

end C4.Cert.Dir150
