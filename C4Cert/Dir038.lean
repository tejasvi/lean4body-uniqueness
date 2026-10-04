module

public import C4Check

public section

/-! Cells `2383 ≤ n < 2384` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir038

theorem k2383_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2383) 3).1 2).1 3).1 3).1 2).1
      103201956753440969708045296171781827269297135915003541239279028819114610969175014946590267783809653577950133646364246636519365488140378655231322437).isSome = true := by
  decide +kernel

theorem k2383_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2383) 3).1 2).1 3).1 3).1 2).2
      350414465265259247097149652104853762343387399265436854735087575936372657490854441188489495270964468877071910477872504698702661).isSome = true := by
  decide +kernel

theorem k2383_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2383) 3).1 2).1 3).1 3).2 2).1
      102904446940680273124366059944062667713293600325283287694782192817890651238163625966412319767280618251609617012928142618182607971538415993349372997).isSome = true := by
  decide +kernel

theorem k2383_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2383) 3).1 2).1 3).1 3).2 2).2
      1397423456692908698413468598712802726843308722704807020051251163321467698497885733016987903872963878260414099032205366654057285).isSome = true := by
  decide +kernel

theorem k2383_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2383) 3).1 2).1 3).2 2).1 3).1 1).1
      15613644448358737009969132244122702999453622227475920074069628193250541176470871410).isSome = true := by
  decide +kernel

theorem k2383_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2383) 3).1 2).1 3).2 2).1 3).1 1).2
      249505791264842245742732841361477642299745744262452432583912124799582350753108950444).isSome = true := by
  decide +kernel

theorem k2383_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2383) 3).1 2).1 3).2 2).1 3).2 1).1
      62259092448924747226424308876130012068297346928074547069634196126782524285567250801).isSome = true := by
  decide +kernel

theorem k2383_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2383) 3).1 2).1 3).2 2).1 3).2 1).2
      13492095011232581665665276590499998674024120954223579016080227500).isSome = true := by
  decide +kernel

theorem k2383_8 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2383) 3).1 2).1 3).2 2).2 3).1
      22298801323052820359910153773817799292805422689845602460204044006755593010250631358856999189387936395128356916395104893435255109).isSome = true := by
  decide +kernel

theorem k2383_9 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2383) 3).1 2).1 3).2 2).2 3).2
      4830058503558069353024510484979372835159213758719309699336668717017162372055544763388030339166102648238595505).isSome = true := by
  decide +kernel

theorem k2383_10 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2383) 3).1 2).2 3).1 2).1 1).1
      62815416305181237101650934056233323391396858367876871325130227789109976102354865523).isSome = true := by
  decide +kernel

theorem k2383_11 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2383) 3).1 2).2 3).1 2).1 1).2
      4114152787691360442287653641199562719641732485318516576320996105960165946841458423735539).isSome = true := by
  decide +kernel

theorem k2383_12 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2383) 3).1 2).2 3).1 2).2 1).1
      213470496705120039173231466258464287745288817596417517751299857).isSome = true := by
  decide +kernel

theorem k2383_13 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2383) 3).1 2).2 3).1 2).2 1).2
      1032199139366281852269976439283172338184576800272467526163310977513176169344454650655986).isSome = true := by
  decide +kernel

theorem k2383_14 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2383) 3).1 2).2 3).2 3).1 2).1
      349019495550895867705132405843401882896048652536436634759978004667754276477606795042605447855551028635222708619096441195240773).isSome = true := by
  decide +kernel

theorem k2383_15 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2383) 3).1 2).2 3).2 3).1 2).2
      250817308555265792166085149615257117271806726581880984792748177887071393342451107185).isSome = true := by
  decide +kernel

theorem k2383_16 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2383) 3).1 2).2 3).2 3).2 2).1
      87050197171940457873088189663875333853249707919551716649609125816696480147455148977034886340567638644624891484130194911165765).isSome = true := by
  decide +kernel

theorem k2383_17 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2383) 3).1 2).2 3).2 3).2 2).2
      16011676998169137107881609136163048201299874253070805280265603884310139293343190604209).isSome = true := by
  decide +kernel

theorem k2383_18 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2383) 3).2 2).1 3).1 2).1 1).1
      1633042234146509255146226719736388823267652364109875186853963396887653373387923700600045177300364411898305357082203661566544351713883238883013445063).isSome = true := by
  decide +kernel

theorem k2383_19 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2383) 3).2 2).1 3).1 2).1 1).2
      88469219699018652263752881282517419449112445949133286886831320675633444657814130267769085107921373714836905689841050468780440755).isSome = true := by
  decide +kernel

theorem k2383_20 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2383) 3).2 2).1 3).1 2).2 1).1
      21646306233045445569377946512575413999301246113433661038885275198840754967218410303479231592650085611092592769766328846343603).isSome = true := by
  decide +kernel

theorem k2383_21 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2383) 3).2 2).1 3).1 2).2 1).2
      354701363423602485263698832932823451192559752527358730289873896508471481117151827392656102635539110208928902153588723763828587697).isSome = true := by
  decide +kernel

theorem k2383_22 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2383) 3).2 2).1 3).2 2).1 1).1
      22056902156104019283923493605111553255927448326558567682034728280670220863483029592612095014760864912383745991824284297947640499).isSome = true := by
  decide +kernel

theorem k2383_23 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2383) 3).2 2).1 3).2 2).1 1).2
      1199067373363160394995052414421243652128673252987953587107777564320886604124720053368133053975339408000704305).isSome = true := by
  decide +kernel

theorem k2383_24 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2383) 3).2 2).1 3).2 2).2 1).1
      345091719801115412690401020463780744070368897284145138121616057539823316103329155346093364617762025151595477304152782882823603).isSome = true := by
  decide +kernel

theorem k2383_25 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2383) 3).2 2).1 3).2 2).2 1).2
      22092643439837816694003111217123101329278129371630897560526741293108262246833851978708005280011064347940542026524996957617151793).isSome = true := by
  decide +kernel

theorem k2383_26 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2383) 3).2 2).2 3).1 2).1 1).1
      21708656952739312595261370099381313844927734926624801310209326730776012092752879499139636323436229109926607545147141908159922).isSome = true := by
  decide +kernel

theorem k2383_27 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2383) 3).2 2).2 3).1 2).1 1).2
      4810043398693340603863524063433899173733973822334759957063369662883468915607052790824198130416139046034176435).isSome = true := by
  decide +kernel

theorem k2383_28 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2383) 3).2 2).2 3).1 2).2 1).1
      1177853587787337116952527439885806917427245265386740266945041166391541853121218187080004303612033600061837).isSome = true := by
  decide +kernel

theorem k2383_29 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2383) 3).2 2).2 3).1 2).2 1).2
      18838155220051465070030058825055493036306891844382127537894789081854219594155321696243188597443806547670700).isSome = true := by
  decide +kernel

theorem k2383_30 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2383) 3).2 2).2 3).2 3).1 2).1
      1383898329718558802541405176805073300287965250925909873578940963942259130911587491997464057435771979465570626659190195608903089).isSome = true := by
  decide +kernel

theorem k2383_31 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2383) 3).2 2).2 3).2 3).1 2).2
      18777291363079675314520349650273515118907078589994024422724686402500259524401426255929886093554843333844401).isSome = true := by
  decide +kernel

theorem k2383_32 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2383) 3).2 2).2 3).2 3).2 1).1
      1016498655157422946061255896509614544712662152288122528372458526186375516183633344688818).isSome = true := by
  decide +kernel

theorem k2383_33 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2383) 3).2 2).2 3).2 3).2 1).2
      299916054442209683438743814206420454614517924171679278128025452024528647362363898780653506362918815007341746).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 2383 2384 :=
  (Cover.one (box := dirCellBox) (n := 2383)
      (.split 3 (.split 2 (.split 3 (.split 3 (.split 2 (.leaf _ k2383_0) (.leaf _ k2383_1)) (.split 2 (.leaf _ k2383_2) (.leaf _ k2383_3))) (.split 2 (.split 3 (.split 1 (.leaf _ k2383_4) (.leaf _ k2383_5)) (.split 1 (.leaf _ k2383_6) (.leaf _ k2383_7))) (.split 3 (.leaf _ k2383_8) (.leaf _ k2383_9)))) (.split 3 (.split 2 (.split 1 (.leaf _ k2383_10) (.leaf _ k2383_11)) (.split 1 (.leaf _ k2383_12) (.leaf _ k2383_13))) (.split 3 (.split 2 (.leaf _ k2383_14) (.leaf _ k2383_15)) (.split 2 (.leaf _ k2383_16) (.leaf _ k2383_17))))) (.split 2 (.split 3 (.split 2 (.split 1 (.leaf _ k2383_18) (.leaf _ k2383_19)) (.split 1 (.leaf _ k2383_20) (.leaf _ k2383_21))) (.split 2 (.split 1 (.leaf _ k2383_22) (.leaf _ k2383_23)) (.split 1 (.leaf _ k2383_24) (.leaf _ k2383_25)))) (.split 3 (.split 2 (.split 1 (.leaf _ k2383_26) (.leaf _ k2383_27)) (.split 1 (.leaf _ k2383_28) (.leaf _ k2383_29))) (.split 3 (.split 2 (.leaf _ k2383_30) (.leaf _ k2383_31)) (.split 1 (.leaf _ k2383_32) (.leaf _ k2383_33)))))))

end C4.Cert.Dir038
