module

public import C4Check

public section

/-! Cells `4399 ≤ n < 4428` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir139

theorem k4399_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4399) 2).1 3).1
      365616990483913474119280096853215530357615356128389934383236704785009752825898517620067708443650419715502577010189484449165589911326).isSome = true := by
  decide +kernel

theorem k4399_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4399) 2).1 3).2 2).1
      993388107240738046872306933296977210687948744164824667419066010146311662161111479751).isSome = true := by
  decide +kernel

theorem k4399_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4399) 2).1 3).2 2).2
      63620592670186319635638966055063554094081719461240446913833603888210049967309527422855).isSome = true := by
  decide +kernel

theorem k4399_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4399) 2).2 3).1 2).1
      4729197374530041347377273944940774471271143866230304248007760439663147826821498845164225179854057711903943).isSome = true := by
  decide +kernel

theorem k4399_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4399) 2).2 3).1 2).2
      16957666084720289879449438544397317914809699531096913448296533702285).isSome = true := by
  decide +kernel

theorem k4399_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4399) 2).2 3).2 2).1
      346374473234425514503851323466853909717503874063373104717277750232270417408140941930719043472568993081376377038219060004312967).isSome = true := by
  decide +kernel

theorem k4399_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4399) 2).2 3).2 2).2
      5539673684748340779292100758617876233775469078529733637768185316358186251974307357026954596552608872004867708047501877479249801).isSome = true := by
  decide +kernel

theorem k4400_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4400) 2).1 3).1 2).1
      987913259148184640179772407541543253878433623426069172987521367036909256969878648263).isSome = true := by
  decide +kernel

theorem k4400_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4400) 2).1 3).1 2).2
      3429439672040640268036611801889155219109714502523569947975530862471).isSome = true := by
  decide +kernel

theorem k4400_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4400) 2).1 3).2
      1032258550454302367259820116174592946441409052946357383245321446146968963476369328818723382).isSome = true := by
  decide +kernel

theorem k4400_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4400) 2).2 3).1 2).1
      1196925805565498491586369214266075847206063172169455086484760298988080923062039694875169346726981803799174345).isSome = true := by
  decide +kernel

theorem k4400_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4400) 2).2 3).1 2).2
      5514678885311140394755198456236293551231051501118362860159715050474697992736773792375370073358753378045793453863758559719528329).isSome = true := by
  decide +kernel

theorem k4400_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4400) 2).2 3).2 2).1
      15769434324349250008997186009288045729111310220725952104213616726334492204292256487309).isSome = true := by
  decide +kernel

theorem k4400_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4400) 2).2 3).2 2).2
      21991075805498683661694293259454402390939425512772718615942385373575312777999018603661254516912450638345746933204350728027339569).isSome = true := by
  decide +kernel

theorem k4401_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4401) 2).1 3).1
      1005033004927123082980984808234328255519323688330076664618073377618250405304528874972726).isSome = true := by
  decide +kernel

theorem k4401_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4401) 2).1 3).2
      217574442288707109171968884429883424900959853881033560691705683537174).isSome = true := by
  decide +kernel

theorem k4401_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4401) 2).2 3).1 2).1
      213018841627218182152973428125964723587677337522492516375607059661).isSome = true := by
  decide +kernel

theorem k4401_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4401) 2).2 3).1 2).2
      311562379394155420884200539447746641044297411695305472635164512615475397554626370557837).isSome = true := by
  decide +kernel

theorem k4401_4 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4401) 2).2 3).2
      26444913450223663821974695846540404790979456852836248253100994372320995326333865692236763158309026502511972682533978027789486456352366525249317217621558).isSome = true := by
  decide +kernel

theorem k4402_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4402) 2).1
      128009939562726523534593354679979625580755810374330813091973665121403755171971335544810753709093326668274452147298667655950231423320673850143777707803).isSome = true := by
  decide +kernel

theorem k4402_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4402) 2).2 3).1
      25762833000855489915579500318991470546327678454536040458140744260332866929189688629098560173678738998545394060849168762603996838009869509218947974710).isSome = true := by
  decide +kernel

theorem k4402_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4402) 2).2 3).2
      1362521882711905306289499390443910026093156295663944352680492013999495080282223435545374999329777315909093065766467838705714633).isSome = true := by
  decide +kernel

theorem k4403_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4403) 2).1
      1468922297045069239453349952263681951991245960815491087261672635542467243285697332459374133893220744652822295).isSome = true := by
  decide +kernel

theorem k4403_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4403) 2).2 3).1
      21255562073653965088809085575939907156124798302570219239012428859396124936755418621519369859115501446045754432855145737168329).isSome = true := by
  decide +kernel

theorem k4403_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4403) 2).2 3).2
      71952033883058347305823935609799275945745889468253628427211847377314616013346386200590399686104360514801).isSome = true := by
  decide +kernel

theorem k4404_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4404) 2).1
      310986276465040283161770509014982797364295519072920599515638900857354792115354552776135).isSome = true := by
  decide +kernel

theorem k4404_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4404) 2).2 3).1
      71904306721225876774896413115565615708182836665078867244441108434995432960355016290343466178461968463089).isSome = true := by
  decide +kernel

theorem k4404_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4404) 2).2 3).2
      824963704013588661297556766220893723547131536529037589401031921).isSome = true := by
  decide +kernel

theorem k4405_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4405) 2).1
      1053507785261129947588837978626326202073964125862387122055268488647).isSome = true := by
  decide +kernel

theorem k4405_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4405) 2).2
      21194550539524555001004611107251606522801384116866032433564967288076690502926466770936143169239465138875834950535892490872263).isSome = true := by
  decide +kernel

theorem k4406_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4406) 2).1
      15198238575545966343961225196211526786034856045827410185250515963260547697923246451).isSome = true := by
  decide +kernel

theorem k4406_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4406) 2).2
      21186403091190173966866372314360156387065810175165030588193175872506077046890293273682273425441159692428713166612690912757193).isSome = true := by
  decide +kernel

theorem c8 : allCells dirCell 4407 4426 [
    18367888009513047034628438347565303212539241202543598543003928958559554314102340998998877968348311844799302,
    1662402455020696295198982, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] = true := by
  decide +kernel

theorem k4426_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4426) 3).1
      107902543398356398113555460138557265097924516429787581863569367183089027367230485694213384894182449623896820395854328405533232478558518381355643453531).isSome = true := by
  decide +kernel

theorem k4426_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4426) 3).2 2).1 3).1
      4064045115488574929513931694066864882154442051356991383006376874183409809672329059506).isSome = true := by
  decide +kernel

theorem k4426_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4426) 3).2 2).1 3).2
      4036387764270187179889273148191115675133731515641395557453466846081302096800247338801).isSome = true := by
  decide +kernel

theorem k4426_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4426) 3).2 2).2
      5627333999712905422794051978564370562322023000252760555206501850310641035066118510949766610532243945769952429856360908232362055).isSome = true := by
  decide +kernel

theorem k4427_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4427) 3).1 2).1 3).1
      257759084170383482598550328827632427297863970630309282461004206081212102696940760323718).isSome = true := by
  decide +kernel

theorem k4427_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4427) 3).1 2).1 3).2
      1026542532773588346110512597056750434040575798876641693190057709018758231857861086267014).isSome = true := by
  decide +kernel

theorem k4427_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4427) 3).1 2).2 3).1
      4020116258238147021335725285336484269797400807451270567653732398371177083274623145777).isSome = true := by
  decide +kernel

theorem k4427_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4427) 3).1 2).2 3).2
      16002924882098043835810602338873910895198601525157111656911253843934487309569580486022).isSome = true := by
  decide +kernel

theorem k4427_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4427) 3).2 2).1 2).1
      260912971297512880608235867404389995835333052989799574206358758986907545417142514015569549).isSome = true := by
  decide +kernel

theorem k4427_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4427) 3).2 2).1 2).2
      260687532303476990147711222653983837421966430374418728834198888752540634749752966685609161).isSome = true := by
  decide +kernel

theorem k4427_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4427) 3).2 2).2 2).1
      254653854480793131708031102523866638433174277788522955885898938647991598053626262156081).isSome = true := by
  decide +kernel

theorem k4427_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4427) 3).2 2).2 2).2
      63716141060102964735944125264588720348636955255223186275486087366530496165393672794929).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 4399 4428 :=
  (Cover.one (box := dirCellBox) (n := 4399)
      (.split 2 (.split 3 (.leaf _ k4399_0) (.split 2 (.leaf _ k4399_1) (.leaf _ k4399_2))) (.split 3 (.split 2 (.leaf _ k4399_3) (.leaf _ k4399_4)) (.split 2 (.leaf _ k4399_5) (.leaf _ k4399_6))))).trans <|
  (Cover.one (box := dirCellBox) (n := 4400)
      (.split 2 (.split 3 (.split 2 (.leaf _ k4400_0) (.leaf _ k4400_1)) (.leaf _ k4400_2)) (.split 3 (.split 2 (.leaf _ k4400_3) (.leaf _ k4400_4)) (.split 2 (.leaf _ k4400_5) (.leaf _ k4400_6))))).trans <|
  (Cover.one (box := dirCellBox) (n := 4401)
      (.split 2 (.split 3 (.leaf _ k4401_0) (.leaf _ k4401_1)) (.split 3 (.split 2 (.leaf _ k4401_2) (.leaf _ k4401_3)) (.leaf _ k4401_4)))).trans <|
  (Cover.one (box := dirCellBox) (n := 4402)
      (.split 2 (.leaf _ k4402_0) (.split 3 (.leaf _ k4402_1) (.leaf _ k4402_2)))).trans <|
  (Cover.one (box := dirCellBox) (n := 4403)
      (.split 2 (.leaf _ k4403_0) (.split 3 (.leaf _ k4403_1) (.leaf _ k4403_2)))).trans <|
  (Cover.one (box := dirCellBox) (n := 4404)
      (.split 2 (.leaf _ k4404_0) (.split 3 (.leaf _ k4404_1) (.leaf _ k4404_2)))).trans <|
  (Cover.one (box := dirCellBox) (n := 4405)
      (.split 2 (.leaf _ k4405_0) (.leaf _ k4405_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 4406)
      (.split 2 (.leaf _ k4406_0) (.leaf _ k4406_1))).trans <|
  (Cover.dir c8).trans <|
  (Cover.one (box := dirCellBox) (n := 4426)
      (.split 3 (.leaf _ k4426_0) (.split 2 (.split 3 (.leaf _ k4426_1) (.leaf _ k4426_2)) (.leaf _ k4426_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 4427)
      (.split 3 (.split 2 (.split 3 (.leaf _ k4427_0) (.leaf _ k4427_1)) (.split 3 (.leaf _ k4427_2) (.leaf _ k4427_3))) (.split 2 (.split 2 (.leaf _ k4427_4) (.leaf _ k4427_5)) (.split 2 (.leaf _ k4427_6) (.leaf _ k4427_7)))))

end C4.Cert.Dir139
