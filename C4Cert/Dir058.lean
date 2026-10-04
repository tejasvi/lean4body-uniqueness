module

public import C4Check

public section

/-! Cells `2748 ≤ n < 2773` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir058

theorem k2748_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2748) 2).1 3).1 2).1 1).1 3).1
      18129685553602516566076537986857056133985814941392174436435490002871123934852826477484748301417991778674).isSome = true := by
  decide +kernel

theorem k2748_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2748) 2).1 3).1 2).1 1).1 3).2
      51956809953826216799416387019722391913776189149851262408202092).isSome = true := by
  decide +kernel

theorem k2748_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2748) 2).1 3).1 2).1 1).2
      25224698761398898286534015501114620992763769278551908071386920657396457174288834749709964443190603207686052812444897802171767314693028532636071367).isSome = true := by
  decide +kernel

theorem k2748_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2748) 2).1 3).1 2).2 3).1 1).1
      983184300712679900035731715234363852596750073946503013664004801653306626936785435820).isSome = true := by
  decide +kernel

theorem k2748_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2748) 2).1 3).1 2).2 3).1 1).2
      72524294679553776314744510696397275457177970329043648251662030448534055316050536001873309975089096553708).isSome = true := by
  decide +kernel

theorem k2748_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2748) 2).1 3).1 2).2 3).2 1).1
      4528489714206858482417990294285745018448483830879465018586501905386780013102340406501434002024147935084).isSome = true := by
  decide +kernel

theorem k2748_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2748) 2).1 3).1 2).2 3).2 1).2
      207846194582790316620056521620463936163016227483897101685120428).isSome = true := by
  decide +kernel

theorem k2748_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2748) 2).1 3).2 2).1 1).1
      18069227408405079178120210441254603312078494552415183456698161854914736552017036122235295111879166162375).isSome = true := by
  decide +kernel

theorem k2748_8 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2748) 2).1 3).2 2).1 1).2
      61207561926725515415053782786832818335083954175504763145159548978132475400657830215).isSome = true := by
  decide +kernel

theorem k2748_9 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2748) 2).1 3).2 2).2 1).1
      21336149085641003448335609892551546505088410289743566046520724616257283304000226071222453180546901970025516761956334263885235).isSome = true := by
  decide +kernel

theorem k2748_10 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2748) 2).1 3).2 2).2 1).2
      72272367824525656743640478521674331369284372601621478209736418638801817058898276719435614232892259524019).isSome = true := by
  decide +kernel

theorem k2748_11 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2748) 2).2 3).1 2).1 3).1 1).1
      63008346803011179916666895342367194585169013850111051508250307869934627640307371580211).isSome = true := by
  decide +kernel

theorem k2748_12 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2748) 2).2 3).1 2).1 3).1 1).2
      245947275109268070184710898188512600248459495570000959305365114835265622619765439916).isSome = true := by
  decide +kernel

theorem k2748_13 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2748) 2).2 3).1 2).1 3).2 1).1
      245609307287924458284327404525619259996899361549145803495519981928021533403668504364).isSome = true := by
  decide +kernel

theorem k2748_14 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2748) 2).2 3).1 2).1 3).2 1).2
      245538338158144414179749148489835929399630275096459604757842005160987384090761723308).isSome = true := by
  decide +kernel

theorem k2748_15 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2748) 2).2 3).1 2).2 3).1 1).1
      1008107071367458585777774129226695770234289882553660778045632544453484495775956778457907).isSome = true := by
  decide +kernel

theorem k2748_16 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2748) 2).2 3).1 2).2 3).1 1).2
      1162537234818059593958667840150074066902538818862960491667331093858236303004124167335874678740873234480300).isSome = true := by
  decide +kernel

theorem k2748_17 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2748) 2).2 3).1 2).2 3).2 1).1
      213214813133801695905210892217385270367082706592133063081711202092).isSome = true := by
  decide +kernel

theorem k2748_18 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2748) 2).2 3).1 2).2 3).2 1).2
      13319131563188319219772472105286324781529643978520857233323556012).isSome = true := by
  decide +kernel

theorem k2748_19 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2748) 2).2 3).2 2).1 1).1
      1612802494251633943773948706802416703555565065112211658711119339994137185795642961715198824253972833505156384681119549272319452291768252752682245327).isSome = true := by
  decide +kernel

theorem k2748_20 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2748) 2).2 3).2 2).1 1).2
      21338395591084360557759956477050983141727205789833831044785010072740286855902133598011838198659456770976485836837805886365107).isSome = true := by
  decide +kernel

theorem k2748_21 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2748) 2).2 3).2 2).2 1).1 3).1
      245442077164240040848624818472706412875631751851058585040904048010336757295443566380).isSome = true := by
  decide +kernel

theorem k2748_22 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2748) 2).2 3).2 2).2 1).1 3).2
      3321978125475658494593615605806910048047134583053753512093966124).isSome = true := by
  decide +kernel

theorem k2748_23 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2748) 2).2 3).2 2).2 1).2
      25205525360761128741367993987125130228271680901729041343777956228582352036862609524498919780461044294377337631478179596490083611880886153208495539).isSome = true := by
  decide +kernel

theorem k2749_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2749) 2).1 2).1
      2360872167869444341788523954699336923355341450455425026279734154705689149669013031924397629993963117032937239).isSome = true := by
  decide +kernel

theorem k2749_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2749) 2).1 2).2 3).1
      1855849939315624364487286606899278879100338240492888449393528291603918286718381571804271685091981296479614492191537446904263585796084220846700810882748539321452488141).isSome = true := by
  decide +kernel

theorem k2749_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2749) 2).1 2).2 3).2
      244274031586857666305915601785833453831690025175867386577237186300692125407246256709).isSome = true := by
  decide +kernel

theorem k2749_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2749) 2).2 3).1 2).1 3).1
      21318694223514542784110880887876228440124810484119588783477329488733071068839642409293251830400878343046914083647168035118513).isSome = true := by
  decide +kernel

theorem k2749_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2749) 2).2 3).1 2).1 3).2
      61139190090714872558050326316886211496790198533162715715789497500820882342509835697).isSome = true := by
  decide +kernel

theorem k2749_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2749) 2).2 3).1 2).2 3).1
      1156156226661317913294087667726546470029357631952780527019089524424449382910822733825926005614696687033521).isSome = true := by
  decide +kernel

theorem k2749_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2749) 2).2 3).1 2).2 3).2
      4620552448713861780306396380959163140517011172719859889769173761762395265656723472380177711832650418057905).isSome = true := by
  decide +kernel

theorem k2749_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2749) 2).2 3).2 2).1
      6279365601642889732263896907317197611498113554054867330061250953739491877125466416513013028500348590157123102052369488635571011728175087955264965).isSome = true := by
  decide +kernel

theorem k2749_8 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2749) 2).2 3).2 2).2 1).1
      18029375013472330005777486672155475967955825680112904822441179540905919946282252095936159368893799292339).isSome = true := by
  decide +kernel

theorem k2749_9 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2749) 2).2 3).2 2).2 1).2
      15268405090207163557815127199029389415739094813960726281725246102623543736952899955).isSome = true := by
  decide +kernel

theorem k2750_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2750) 2).1
      388672757829918947850405638).isSome = true := by
  decide +kernel

theorem k2750_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2750) 2).2 2).1
      788700317074557491625701829205499034898990691658876262126909168520956210311725565528885063197627259971015).isSome = true := by
  decide +kernel

theorem k2750_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2750) 2).2 2).2 3).1
      85028025810015101245276945759967334994413654490140219515123608744980305006585966883436269806105365284662207867723839330153713).isSome = true := by
  decide +kernel

theorem k2750_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2750) 2).2 2).2 3).2
      15242824332100983738083017654992387392676612519564647027429442765541199713512549745).isSome = true := by
  decide +kernel

theorem c3 : allCells dirCell 2751 2773 [
    382185350446579384485760380567920384782977553405446, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0] = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 2748 2773 :=
  (Cover.one (box := dirCellBox) (n := 2748)
      (.split 2 (.split 3 (.split 2 (.split 1 (.split 3 (.leaf _ k2748_0) (.leaf _ k2748_1)) (.leaf _ k2748_2)) (.split 3 (.split 1 (.leaf _ k2748_3) (.leaf _ k2748_4)) (.split 1 (.leaf _ k2748_5) (.leaf _ k2748_6)))) (.split 2 (.split 1 (.leaf _ k2748_7) (.leaf _ k2748_8)) (.split 1 (.leaf _ k2748_9) (.leaf _ k2748_10)))) (.split 3 (.split 2 (.split 3 (.split 1 (.leaf _ k2748_11) (.leaf _ k2748_12)) (.split 1 (.leaf _ k2748_13) (.leaf _ k2748_14))) (.split 3 (.split 1 (.leaf _ k2748_15) (.leaf _ k2748_16)) (.split 1 (.leaf _ k2748_17) (.leaf _ k2748_18)))) (.split 2 (.split 1 (.leaf _ k2748_19) (.leaf _ k2748_20)) (.split 1 (.split 3 (.leaf _ k2748_21) (.leaf _ k2748_22)) (.leaf _ k2748_23)))))).trans <|
  (Cover.one (box := dirCellBox) (n := 2749)
      (.split 2 (.split 2 (.leaf _ k2749_0) (.split 3 (.leaf _ k2749_1) (.leaf _ k2749_2))) (.split 3 (.split 2 (.split 3 (.leaf _ k2749_3) (.leaf _ k2749_4)) (.split 3 (.leaf _ k2749_5) (.leaf _ k2749_6))) (.split 2 (.leaf _ k2749_7) (.split 1 (.leaf _ k2749_8) (.leaf _ k2749_9)))))).trans <|
  (Cover.one (box := dirCellBox) (n := 2750)
      (.split 2 (.leaf _ k2750_0) (.split 2 (.leaf _ k2750_1) (.split 3 (.leaf _ k2750_2) (.leaf _ k2750_3))))).trans <|
  (Cover.dir c3)

end C4.Cert.Dir058
