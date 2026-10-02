module

public import C4Check

public section

/-! Cells `1967 ≤ n < 1994` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir023

theorem k1967_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 1967) 2).1
      11453246106406893940879632451487619709557313986).isSome = true := by
  decide +kernel

theorem k1967_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1967) 2).2 2).1
      243573690839681290442197903481828245660201910184851301392213122578752334674730823751).isSome = true := by
  decide +kernel

theorem k1967_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1967) 2).2 2).2
      71889722768422392765704292104664892048763334132004909981157737405308751817283278414952922254335144564167).isSome = true := by
  decide +kernel

theorem c1 : allCells dirCell 1968 1991 [
    3376991654462904096656114774991861177322993910690269536040164458882, 1, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3] = true := by
  decide +kernel

theorem k1991_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 1991) 3).1
      1211386440256817373841281756604650541879375165160770369256379168901225266146745052202782159418945992590705038).isSome = true := by
  decide +kernel

theorem k1991_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1991) 3).2 2).1
      88475769696949749841412647408262470267965770974560130177693491883528182288500733293901417508207106638385874042665267478124590107).isSome = true := by
  decide +kernel

theorem k1991_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1991) 3).2 2).2
      63618553252859277394630602407053509595588367474481697737996963808401685744940733498503).isSome = true := by
  decide +kernel

theorem k1992_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1992) 3).1 2).1 3).1
      21540968495930081106055080099111823892598548287413361361029475065228068918108787963884091249918941626379071761552913975459142).isSome = true := by
  decide +kernel

theorem k1992_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1992) 3).1 2).1 3).2
      21492911967117032371681739484492137519845022330371233800153294991461918456582173190201270757448144122935037144423533595743305).isSome = true := by
  decide +kernel

theorem k1992_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1992) 3).1 2).2 3).1
      247638702174437018656579845035178137792174746563142518317122102537041455483752541521).isSome = true := by
  decide +kernel

theorem k1992_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1992) 3).1 2).2 3).2
      72906766588080692792634925790453792881916725869267748008895664123381569825586618584979006950024268224881).isSome = true := by
  decide +kernel

theorem k1992_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1992) 3).2 2).1 3).1
      251871739372146813469368011871895959296068139283515094298285531397990690027252112088649).isSome = true := by
  decide +kernel

theorem k1992_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1992) 3).2 2).1 3).2
      18554857730011737976004340721397422008188549018170312346312640544290416265800345733933480639318698990788017).isSome = true := by
  decide +kernel

theorem k1992_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1992) 3).2 2).2 3).1
      18188382344055817144911699891148872864401477099808625991391686596650320979068174348968375210555434386801).isSome = true := by
  decide +kernel

theorem k1992_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1992) 3).2 2).2 3).2
      251823365837756907214979544830016701706501393916276496954125977353449009909179253465413).isSome = true := by
  decide +kernel

theorem k1993_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1993) 3).1 2).1 3).1
      18530435230157048431132002325081952397656399684755104751408268929482319443501202964297220323383020831268017).isSome = true := by
  decide +kernel

theorem k1993_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1993) 3).1 2).1 3).2
      4627291460051144792297606653583735672881292017086209715965287202322121887147303618232355826966575725401905).isSome = true := by
  decide +kernel

theorem k1993_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1993) 3).1 2).2 3).1
      1005800367434630576100682729682529113842819707817947277150155488962681810757841671377605).isSome = true := by
  decide +kernel

theorem k1993_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1993) 3).1 2).2 3).2
      3924021483471794255080470785168094966521451779616881538122151451451289094620220512049).isSome = true := by
  decide +kernel

theorem k1993_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1993) 3).2 2).1 3).1
      4622881146642168549675971907557062702575870949341294881867179620473662665148245297979601127067137010161457).isSome = true := by
  decide +kernel

theorem k1993_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1993) 3).2 2).1 3).2
      1154956977809209588866447343572232385651787723570972661300885346781122941114765787015770470594165633750833).isSome = true := by
  decide +kernel

theorem k1993_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1993) 3).2 2).2 1).1
      3919028049132620150347032179811540087528902902628241348123285470465825784217192666930).isSome = true := by
  decide +kernel

theorem k1993_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1993) 3).2 2).2 1).2
      3916387425009626318649585916165072077364475278617316745994621942429138315596641523507).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 1967 1994 :=
  (Cover.one (box := dirCellBox) (n := 1967)
      (.split 2 (.leaf _ k1967_0) (.split 2 (.leaf _ k1967_1) (.leaf _ k1967_2)))).trans <|
  (Cover.dir c1).trans <|
  (Cover.one (box := dirCellBox) (n := 1991)
      (.split 3 (.leaf _ k1991_0) (.split 2 (.leaf _ k1991_1) (.leaf _ k1991_2)))).trans <|
  (Cover.one (box := dirCellBox) (n := 1992)
      (.split 3 (.split 2 (.split 3 (.leaf _ k1992_0) (.leaf _ k1992_1)) (.split 3 (.leaf _ k1992_2) (.leaf _ k1992_3))) (.split 2 (.split 3 (.leaf _ k1992_4) (.leaf _ k1992_5)) (.split 3 (.leaf _ k1992_6) (.leaf _ k1992_7))))).trans <|
  (Cover.one (box := dirCellBox) (n := 1993)
      (.split 3 (.split 2 (.split 3 (.leaf _ k1993_0) (.leaf _ k1993_1)) (.split 3 (.leaf _ k1993_2) (.leaf _ k1993_3))) (.split 2 (.split 3 (.leaf _ k1993_4) (.leaf _ k1993_5)) (.split 1 (.leaf _ k1993_6) (.leaf _ k1993_7)))))

end C4.Cert.Dir023
