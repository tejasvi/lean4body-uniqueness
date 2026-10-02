module

public import C4Check

public section

/-! Cells `3560 ≤ n < 3562` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir115

theorem k3560_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3560) 2).1 3).1 2).1
      21389806599944278705404622082206176933833684259719473500048474113700470854294942697111554674104642131252240777896323610584519).isSome = true := by
  decide +kernel

theorem k3560_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3560) 2).1 3).1 2).2
      7468156027607456787387267479196760697842661831073902516746863197689026092563902050888725614346982452166664987489277730256717919615080413367170892377086558653226048973).isSome = true := by
  decide +kernel

theorem k3560_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3560) 2).1 3).2 3).1
      85537285471503096866248797999444662186854409952764928959940831607475279935831539918679465784325520757930318819104015809742278).isSome = true := by
  decide +kernel

theorem k3560_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3560) 2).1 3).2 3).2
      21346239092471388182499421567116237145036511125013588628617161244127406149307069281388341110811055710296700187389588252882374).isSome = true := by
  decide +kernel

theorem k3560_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3560) 2).2 3).1 2).1 1).1
      15770578444212309848701434468535108188287174181655382259776954777497254904138978773820).isSome = true := by
  decide +kernel

theorem k3560_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3560) 2).2 3).1 2).1 1).2
      208628639875298832564229546037147572739960311395211119050513724).isSome = true := by
  decide +kernel

theorem k3560_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3560) 2).2 3).1 2).2
      1622988610220764425929075656401177614518512239184397717350961215565463371180062375992262914677154848538707736881763052982474418007759544224602118385).isSome = true := by
  decide +kernel

theorem k3560_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3560) 2).2 3).2 2).1
      342053726618599922358081320202091118999836230231161581905980677227687972746788542390306795355547608076875318577190278181778673).isSome = true := by
  decide +kernel

theorem k3560_8 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3560) 2).2 3).2 2).2
      342335318099648703364907587491412042786116919617759612387034507856689974820665949589696869901463097314020180238817212672603377).isSome = true := by
  decide +kernel

theorem k3561_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3561) 2).1 3).1 2).1
      1331617827017224123771864170359766018012702452797705972451003591622441897110502218059656759436571877834243310116257033713137).isSome = true := by
  decide +kernel

theorem k3561_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3561) 2).1 3).1 2).2
      1332235389437799542382362881852855554226139701223565421169383612149870881339528075238182995579782004445294826095248234083825).isSome = true := by
  decide +kernel

theorem k3561_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3561) 2).1 3).2 2).1
      15265164501907990071749407566633634471157337243564749615568376548363364500536297841).isSome = true := by
  decide +kernel

theorem k3561_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3561) 2).1 3).2 2).2
      288431988191338778218885019768112875600847621388559675405511015325233161362312434082219482465412085609969).isSome = true := by
  decide +kernel

theorem k3561_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3561) 2).2 3).1 2).1
      72260176312053675768268576803614270305687058331930326398722622539041025558763414895129688614443999393009).isSome = true := by
  decide +kernel

theorem k3561_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3561) 2).2 3).1 2).2
      5336490327090001314270320561676326663394960954939771286985678480369148044178272825351277440121348265798582962752321886869308).isSome = true := by
  decide +kernel

theorem k3561_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3561) 2).2 3).2 3).1
      72182543929996963372692879507978932595201761029708953878269908279579083791635832255988921592824073385201).isSome = true := by
  decide +kernel

theorem k3561_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3561) 2).2 3).2 3).2
      62559609643442648202673449901263918684420370507081772461640454186366753507910668112625).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 3560 3562 :=
  (Cover.one (box := dirCellBox) (n := 3560)
      (.split 2 (.split 3 (.split 2 (.leaf _ k3560_0) (.leaf _ k3560_1)) (.split 3 (.leaf _ k3560_2) (.leaf _ k3560_3))) (.split 3 (.split 2 (.split 1 (.leaf _ k3560_4) (.leaf _ k3560_5)) (.leaf _ k3560_6)) (.split 2 (.leaf _ k3560_7) (.leaf _ k3560_8))))).trans <|
  (Cover.one (box := dirCellBox) (n := 3561)
      (.split 2 (.split 3 (.split 2 (.leaf _ k3561_0) (.leaf _ k3561_1)) (.split 2 (.leaf _ k3561_2) (.leaf _ k3561_3))) (.split 3 (.split 2 (.leaf _ k3561_4) (.leaf _ k3561_5)) (.split 3 (.leaf _ k3561_6) (.leaf _ k3561_7)))))

end C4.Cert.Dir115
