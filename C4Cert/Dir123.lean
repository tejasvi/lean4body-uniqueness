module

public import C4Check

public section

/-! Cells `3647 ≤ n < 3671` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir123

theorem k3647_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3647) 2).1 3).1
      13558157978218367692848371427651045400570887780728891303202907956028).isSome = true := by
  decide +kernel

theorem k3647_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3647) 2).1 3).2
      15617132120920424247832909057426634366063762795198008156469319435023418371839391945532).isSome = true := by
  decide +kernel

theorem k3647_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3647) 2).2 3).1
      3391277614610765788795213037887425785268386939861452743338196714300).isSome = true := by
  decide +kernel

theorem k3647_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3647) 2).2 3).2
      13549168063767218528668028989165112735837684985738213178483645817660).isSome = true := by
  decide +kernel

theorem k3648_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3648) 3).1 2).1
      15603138784438101726476942812630084672857202853519036087541952971543769050246882513724).isSome = true := by
  decide +kernel

theorem k3648_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3648) 3).1 2).2
      3384098518463800385340522555847896887477803496300067260179945562940).isSome = true := by
  decide +kernel

theorem k3648_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3648) 3).2 2).1
      15591939069612025471179930830443638870403357155427908574547819402694090452484614509372).isSome = true := by
  decide +kernel

theorem k3648_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3648) 3).2 2).2
      15597006008413928488327776898433669788965166816018303836978977736800839854437132915516).isSome = true := by
  decide +kernel

theorem k3649_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3649) 2).1 3).1
      62333206698027103289223169848415221296662378630960495784737069401947152703842949221180).isSome = true := by
  decide +kernel

theorem k3649_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3649) 2).1 3).2
      206160822940393630937201748997467661574248554451391990471875900).isSome = true := by
  decide +kernel

theorem k3649_2 : (checkBoxH dirMode depth (splitBox (dirCellBox 3649) 2).2
      410281277430784961648881892197839551658713624762985142846835725380550139123326949275400593162994392131049002503722531481659470837889337863418830163772).isSome = true := by
  decide +kernel

theorem k3650_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3650) 3).1
      339169482902198155463016364380830347011191409953551665745933395266754652146760393530023328653281537015908753675153001465869554).isSome = true := by
  decide +kernel

theorem k3650_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 3650) 3).2
      339052835626971853101800230295689016007626546641679766455429289296448005604769294355887648892015931214160971983559120497505522).isSome = true := by
  decide +kernel

theorem k3651_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3651) 3).1
      1148357937718075396003881556880691486804891965203278468478801092210317646150896260708706690394437449632572).isSome = true := by
  decide +kernel

theorem k3651_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 3651) 3).2
      1148094942712298359042588109684860620924989445169205471647197462010451605253110698770355654544254989978428).isSome = true := by
  decide +kernel

theorem k3652_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3652) 2).1
      3797685738259658620343043286966361718160175172119823723848907206473265998838521212).isSome = true := by
  decide +kernel

theorem k3652_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 3652) 2).2
      5293397502976866041331323106933023321202047267622096055583585246123475848852233535192758997721561987240437527868211977508668).isSome = true := by
  decide +kernel

theorem c6 : allCells dirCell 3653 3654 [
    84667548558497152478241514757122186922684731448050092296554790414663218633535834599388554970562390568891083922148525045654982] = true := by
  decide +kernel

theorem c7 : allCells dirCell 3654 3656 [
    17925074983613211174250455375579488036238469860232100653173340308899364627374410596009805697167858476402,
    51433924008594439157973151963867423516767378657670697940120338] = true := by
  decide +kernel

theorem c8 : allCells dirCell 3656 3671 [
    2361401466450965657922, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    219928029657562672080148703409359108663681730578162261341599375475] = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 3647 3671 :=
  (Cover.one (box := dirCellBox) (n := 3647)
      (.split 2 (.split 3 (.leaf _ k3647_0) (.leaf _ k3647_1)) (.split 3 (.leaf _ k3647_2) (.leaf _ k3647_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 3648)
      (.split 3 (.split 2 (.leaf _ k3648_0) (.leaf _ k3648_1)) (.split 2 (.leaf _ k3648_2) (.leaf _ k3648_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 3649)
      (.split 2 (.split 3 (.leaf _ k3649_0) (.leaf _ k3649_1)) (.leaf _ k3649_2))).trans <|
  (Cover.one (box := dirCellBox) (n := 3650)
      (.split 3 (.leaf _ k3650_0) (.leaf _ k3650_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 3651)
      (.split 3 (.leaf _ k3651_0) (.leaf _ k3651_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 3652)
      (.split 2 (.leaf _ k3652_0) (.leaf _ k3652_1))).trans <|
  (Cover.dir c6).trans <|
  (Cover.dir c7).trans <|
  (Cover.dir c8)

end C4.Cert.Dir123
