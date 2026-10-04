module

public import C4Check

public section

/-! Cells `847 ≤ n < 904` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir002

theorem k847_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 847) 3).1
      751342058248743064493664962125947863820349534651334).isSome = true := by
  decide +kernel

theorem k847_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 847) 3).2 2).1
      301456032696228133070030885160798125040111403620400833659129605684307735501145677550527040260424179132477591629).isSome = true := by
  decide +kernel

theorem k847_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 847) 3).2 2).2
      301531866534071842703465384554347775529853826671245496910549882437180812022780786826762571798658913129428193357).isSome = true := by
  decide +kernel

theorem k848_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 848) 3).1 2).1 1).1
      15570886243998022965701792429683314071188299681197344135331246221025614041231584630599).isSome = true := by
  decide +kernel

theorem k848_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 848) 3).1 2).1 1).2
      1179535141823969275767825485478945694150275189954840437220005844099663505803813570171050026852998011791836814).isSome = true := by
  decide +kernel

theorem k848_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 848) 3).1 2).2 1).1
      15573496762195711529456350707260087423803555354383496336995270567690366846446324854599).isSome = true := by
  decide +kernel

theorem k848_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 848) 3).1 2).2 1).2
      3987702097765993746901866275693225956334147609467119361521138983161289455239043086271687).isSome = true := by
  decide +kernel

theorem k848_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 848) 3).2 2).1 1).1
      248973277764168938555761741696596200074143207962622895705916149399465987073412293889422).isSome = true := by
  decide +kernel

theorem k848_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 848) 3).2 2).1 1).2
      996377469366238629119240534556419718618358689549498004559652799881970555965811527611186).isSome = true := by
  decide +kernel

theorem k848_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 848) 3).2 2).2 1).1
      15935974546269186662981918158938446225098377247461637622363348939078160100871447339771534).isSome = true := by
  decide +kernel

theorem k848_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 848) 3).2 2).2 1).2
      996511755769088063264305143471323731556165531962946482030988605018664227840946530513714).isSome = true := by
  decide +kernel

theorem k849_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 849) 2).1 3).1 1).1
      995636185547886843077227421842679651905944167487078025398839435368905778907353287324466).isSome = true := by
  decide +kernel

theorem k849_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 849) 2).1 3).1 1).2
      995984277873940790952549577046469075344155320831589254633410771397034974291992526025522).isSome = true := by
  decide +kernel

theorem k849_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 849) 2).1 3).2 1).1
      52669931955389100789694276365485585430369559742441753397709887395).isSome = true := by
  decide +kernel

theorem k849_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 849) 2).1 3).2 1).2
      210787386099243585043695699034457764919652992688259776977567019916).isSome = true := by
  decide +kernel

theorem k849_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 849) 2).2 3).1 1).1
      995705413007702141173736570416985539365943683883214015101459297035898294545894782628658).isSome = true := by
  decide +kernel

theorem k849_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 849) 2).2 3).1 1).2
      996078342737081842792293364711147075779273172032630663274254414024961444359232171897650).isSome = true := by
  decide +kernel

theorem k849_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 849) 2).2 3).2 1).1
      52670282786588758186904795851451467239818838228630331019036530595).isSome = true := by
  decide +kernel

theorem k849_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 849) 2).2 3).2 1).2
      13502849932615750791847463986956405703381413462686548325748569633585).isSome = true := by
  decide +kernel

theorem k850_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 850) 2).1 3).1
      15920574294722060571984571316888484495804708928414618632102607654033547863772213407323337).isSome = true := by
  decide +kernel

theorem k850_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 850) 2).1 3).2
      822870105532719025290145555330490296998063245774660357619560081).isSome = true := by
  decide +kernel

theorem k850_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 850) 2).2 3).1
      3984177897908696570132130444138043723578834499315133803972378955663791977296792441640137).isSome = true := by
  decide +kernel

theorem k850_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 850) 2).2 3).2
      822857866257920509579640391599477804201114368804620230617123217).isSome = true := by
  decide +kernel

theorem c4 : allCells dirCell 851 875 [
    2853389743518768818495556469061664876892550174, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 3] = true := by
  decide +kernel

theorem k875_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 875) 3).1
      751818148496755931242014924649615688363062431073222).isSome = true := by
  decide +kernel

theorem k875_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 875) 3).2 2).1
      1179423796000464277449056385362340007909946635215441581847521084294192835233293842772095032959993733181657165).isSome = true := by
  decide +kernel

theorem k875_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 875) 3).2 2).2
      18414580352891788684373314399729096551131411084862493437213147781660509721380464251339635013715584357691661).isSome = true := by
  decide +kernel

theorem k876_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 876) 3).1 2).1 1).1
      3894001490577511446610616725932791569332625805851785678239470972399968771246128264263).isSome = true := by
  decide +kernel

theorem k876_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 876) 3).1 2).1 1).2
      62320537393306309299652764228996887470413049978545775059345730497241430840713230506803).isSome = true := by
  decide +kernel

theorem k876_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 876) 3).1 2).2 1).1
      243408001182612696103906492940515282295863010659363272454092031239351971942942490995).isSome = true := by
  decide +kernel

theorem k876_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 876) 3).1 2).2 1).2
      15583125909335976761902154844786524906462117948839167445395463209745679490781861238579).isSome = true := by
  decide +kernel

theorem k876_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 876) 3).2 2).1 1).1
      62266281678279996119080656897088262621326743204388855879630753569765985014107951160115).isSome = true := by
  decide +kernel

theorem k876_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 876) 3).2 2).1 1).2
      249122891449509493963380092661981345797188113948594642094615563588698974255404946578659).isSome = true := by
  decide +kernel

theorem k876_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 876) 3).2 2).2 1).1
      3896301201079953618891665133757052911101896079965467714672112438992041732606146336563).isSome = true := by
  decide +kernel

theorem k876_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 876) 3).2 2).2 1).2
      996862365879963462279753902006765015837088456917505798777088199960349136859988986262321).isSome = true := by
  decide +kernel

theorem k877_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 877) 3).1 2).1 1).1
      997258014479310143803878696405227644524879776293108406045368233959950767674744263766833).isSome = true := by
  decide +kernel

theorem k877_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 877) 3).1 2).1 1).2
      996166377147492660984110723399851212720833377844938744837887889808175149403242013225778).isSome = true := by
  decide +kernel

theorem k877_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 877) 3).1 2).2 1).1
      995954813885057343149593766068836270204972876513325198639491018901638876075688042263345).isSome = true := by
  decide +kernel

theorem k877_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 877) 3).1 2).2 1).2
      997312081511912673583898808664365095171601460895321440149425305579535630491623280177969).isSome = true := by
  decide +kernel

theorem k877_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 877) 3).2 2).1 1).1
      972005256594037078822671541746999408666355548003737664297553532648219184229166094243).isSome = true := by
  decide +kernel

theorem k877_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 877) 3).2 2).1 1).2
      52755758522342230588797744816834701587688820099745533348795989196).isSome = true := by
  decide +kernel

theorem k877_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 877) 3).2 2).2 1).1
      13172987437021722523198175375860639637181862479204797958076044515).isSome = true := by
  decide +kernel

theorem k877_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 877) 3).2 2).2 1).2
      972414536399049630151387492840749764857572391542903054941004410638844573895416970444).isSome = true := by
  decide +kernel

theorem k878_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 878) 3).1 2).1
      15919902582066793995657140888683181862580178716472848245930811428354141721348341140632781).isSome = true := by
  decide +kernel

theorem k878_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 878) 3).1 2).2
      15920257532076074677932714831501840862470140548734016738360148611894555449155341475025221).isSome = true := by
  decide +kernel

theorem k878_2 : (checkBoxH dirMode depth (splitBox (dirCellBox 878) 3).2
      21686466357329371852579691812435661564090759807319854010117934043906582635900778651057513131310137123349790262545895029109616966).isSome = true := by
  decide +kernel

theorem c9 : allCells dirCell 879 903 [
    178283005796447075681805550450776416435373086, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 3] = true := by
  decide +kernel

theorem k903_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 903) 3).1
      13553692711685678017423675998457671047475051233588800344054089450438).isSome = true := by
  decide +kernel

theorem k903_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 903) 3).2 2).1
      4604637440035202801352924250652485511180407206961185838919612245704135071080207132498737629247934665239821).isSome = true := by
  decide +kernel

theorem k903_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 903) 3).2 2).2
      249616565001367888467017504617379523097314522826928080620486755478335043307050433616141).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 847 904 :=
  (Cover.one (box := dirCellBox) (n := 847)
      (.split 3 (.leaf _ k847_0) (.split 2 (.leaf _ k847_1) (.leaf _ k847_2)))).trans <|
  (Cover.one (box := dirCellBox) (n := 848)
      (.split 3 (.split 2 (.split 1 (.leaf _ k848_0) (.leaf _ k848_1)) (.split 1 (.leaf _ k848_2) (.leaf _ k848_3))) (.split 2 (.split 1 (.leaf _ k848_4) (.leaf _ k848_5)) (.split 1 (.leaf _ k848_6) (.leaf _ k848_7))))).trans <|
  (Cover.one (box := dirCellBox) (n := 849)
      (.split 2 (.split 3 (.split 1 (.leaf _ k849_0) (.leaf _ k849_1)) (.split 1 (.leaf _ k849_2) (.leaf _ k849_3))) (.split 3 (.split 1 (.leaf _ k849_4) (.leaf _ k849_5)) (.split 1 (.leaf _ k849_6) (.leaf _ k849_7))))).trans <|
  (Cover.one (box := dirCellBox) (n := 850)
      (.split 2 (.split 3 (.leaf _ k850_0) (.leaf _ k850_1)) (.split 3 (.leaf _ k850_2) (.leaf _ k850_3)))).trans <|
  (Cover.dir c4).trans <|
  (Cover.one (box := dirCellBox) (n := 875)
      (.split 3 (.leaf _ k875_0) (.split 2 (.leaf _ k875_1) (.leaf _ k875_2)))).trans <|
  (Cover.one (box := dirCellBox) (n := 876)
      (.split 3 (.split 2 (.split 1 (.leaf _ k876_0) (.leaf _ k876_1)) (.split 1 (.leaf _ k876_2) (.leaf _ k876_3))) (.split 2 (.split 1 (.leaf _ k876_4) (.leaf _ k876_5)) (.split 1 (.leaf _ k876_6) (.leaf _ k876_7))))).trans <|
  (Cover.one (box := dirCellBox) (n := 877)
      (.split 3 (.split 2 (.split 1 (.leaf _ k877_0) (.leaf _ k877_1)) (.split 1 (.leaf _ k877_2) (.leaf _ k877_3))) (.split 2 (.split 1 (.leaf _ k877_4) (.leaf _ k877_5)) (.split 1 (.leaf _ k877_6) (.leaf _ k877_7))))).trans <|
  (Cover.one (box := dirCellBox) (n := 878)
      (.split 3 (.split 2 (.leaf _ k878_0) (.leaf _ k878_1)) (.leaf _ k878_2))).trans <|
  (Cover.dir c9).trans <|
  (Cover.one (box := dirCellBox) (n := 903)
      (.split 3 (.leaf _ k903_0) (.split 2 (.leaf _ k903_1) (.leaf _ k903_2))))

end C4.Cert.Dir002
