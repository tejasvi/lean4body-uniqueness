module

public import C4Check

public section

/-! Cells `2471 ≤ n < 2496` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir049

theorem k2471_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2471) 3).1 2).1
      295482210010157226599559369370905325686075783381502880922020835274642625736742691584334639534706442159045692).isSome = true := by
  decide +kernel

theorem k2471_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2471) 3).1 2).2
      16022997596326094506011322775956360006080066908248465806854257931678335151672216533122108).isSome = true := by
  decide +kernel

theorem k2471_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2471) 3).2 2).1
      15997233378470741746805737966866176004146741505469324100526679075141908872193609540254780).isSome = true := by
  decide +kernel

theorem k2471_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2471) 3).2 2).2
      4000371490150228523158090434584187164637109533164335242306812962513439124533727030099004).isSome = true := by
  decide +kernel

theorem k2472_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2472) 3).1 1).1
      999109558704656641868847215502672845682098326452492758342214200774713058788408947454924).isSome = true := by
  decide +kernel

theorem k2472_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2472) 3).1 1).2
      62440696031301786844783816584014130663084270133461420167902448261494342794729142170572).isSome = true := by
  decide +kernel

theorem k2472_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2472) 3).2 2).1
      52841668775775677557256852210542263328162634527606140233976724540).isSome = true := by
  decide +kernel

theorem k2472_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2472) 3).2 2).2
      3993462728281187734324159842413669032626377127007011433929470416776571805871025016945724).isSome = true := by
  decide +kernel

theorem k2473_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2473) 3).1
      1390666319781127157615466485013122029559210795752893137918956041112854034440903587813635481423107632646223590335588546076132831474).isSome = true := by
  decide +kernel

theorem k2473_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 2473) 3).2
      1389846185599668468997076158927063786327238273327461406413459593837116101379965250892170515486955694564917118278147880927624491250).isSome = true := by
  decide +kernel

theorem k2474_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2474) 3).1
      294146630152315887116548704329402808899616906846552541697527020987363312331243479483326802870338361421581105).isSome = true := by
  decide +kernel

theorem k2474_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 2474) 3).2
      73505594203283741569032074570959874546001256607439812980140165793083263510729723179534593665737839491628092).isSome = true := by
  decide +kernel

theorem k2475_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2475) 3).1
      73482056104609339612094866051897094201233876427452450329317547506728738681680150901569419759193964749732924).isSome = true := by
  decide +kernel

theorem k2475_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 2475) 3).2
      4591630334165339260473053360888949792032183875645880476328889468865836276552692192930801484991483117426482).isSome = true := by
  decide +kernel

theorem k2476_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2476) 2).1
      971978159889938628840203730179669992317652981726992690075123248253696694330886814780).isSome = true := by
  decide +kernel

theorem k2476_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 2476) 2).2
      52690688418506557077727575259741001206103954955340493366188915772).isSome = true := by
  decide +kernel

theorem c6 : allCells dirCell 2477 2478 [
    1202855630222002198457276397819523576708356009373838363898088831578007240823618500961051701464059780441941290189] = true := by
  decide +kernel

theorem c7 : allCells dirCell 2478 2495 [
    971355989093093644967480413521414227104435932579401865470132216928223169055687606641,
    147544447023005782356, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] = true := by
  decide +kernel

theorem k2495_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2495) 3).1
      1008392375153866188301200160075710251709478732175617349428973476270525124815440954631).isSome = true := by
  decide +kernel

theorem k2495_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2495) 3).2 2).1
      18452264910989733146945777266757950812098736094447135741699935886423252373869089004815699875461187453297).isSome = true := by
  decide +kernel

theorem k2495_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2495) 3).2 2).2
      15655857746510483907064887222406437230804656154677413179888817483034289073497851249).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 2471 2496 :=
  (Cover.one (box := dirCellBox) (n := 2471)
      (.split 3 (.split 2 (.leaf _ k2471_0) (.leaf _ k2471_1)) (.split 2 (.leaf _ k2471_2) (.leaf _ k2471_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 2472)
      (.split 3 (.split 1 (.leaf _ k2472_0) (.leaf _ k2472_1)) (.split 2 (.leaf _ k2472_2) (.leaf _ k2472_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 2473)
      (.split 3 (.leaf _ k2473_0) (.leaf _ k2473_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 2474)
      (.split 3 (.leaf _ k2474_0) (.leaf _ k2474_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 2475)
      (.split 3 (.leaf _ k2475_0) (.leaf _ k2475_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 2476)
      (.split 2 (.leaf _ k2476_0) (.leaf _ k2476_1))).trans <|
  (Cover.dir c6).trans <|
  (Cover.dir c7).trans <|
  (Cover.one (box := dirCellBox) (n := 2495)
      (.split 3 (.leaf _ k2495_0) (.split 2 (.leaf _ k2495_1) (.leaf _ k2495_2))))

end C4.Cert.Dir049
