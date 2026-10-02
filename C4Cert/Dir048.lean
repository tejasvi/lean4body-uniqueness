module

public import C4Check

public section

/-! Cells `2467 ≤ n < 2471` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir048

theorem k2467_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2467) 3).1 3).1
      18704154019082963482502328555438735243311003890387869681017625022181781493146889733635936799794113049158).isSome = true := by
  decide +kernel

theorem k2467_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2467) 3).1 3).2
      21962477052488773724596437199835656070707692842614683445042641439455731676956046403828634751354031062737546705690135699613126).isSome = true := by
  decide +kernel

theorem k2467_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2467) 3).2 3).1
      476245884603376730387419871984304499777451692574712574199978903405914857535515293440340747026198469066388069226944247412654198286677181720996313889806593460151936454).isSome = true := by
  decide +kernel

theorem k2467_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2467) 3).2 3).2 2).1
      18445463469353563790311474542940208628902609451017642359568474344197503236774897568883413293922843624817).isSome = true := by
  decide +kernel

theorem k2467_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2467) 3).2 3).2 2).2
      3907637185902539439706800840313299314470180298795135795283501227039303288580889980).isSome = true := by
  decide +kernel

theorem k2468_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2468) 3).1 2).1 1).1
      3888598544787933486651936042589466794109571649177792043908236681498882647897955708).isSome = true := by
  decide +kernel

theorem k2468_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2468) 3).1 2).1 1).2
      254745694281514497725887838634711905239678472740057054963294927104305631289871175191804).isSome = true := by
  decide +kernel

theorem k2468_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2468) 3).1 2).2
      25599252909484046113234013321695850445224257234978203813122743309022301913415213906483887239244350172896632793864956068836588651518616526852290033).isSome = true := by
  decide +kernel

theorem k2468_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2468) 3).2 2).1 1).1
      15845732460307453715503694134786553838422848561353528572835135187443288271724249339708).isSome = true := by
  decide +kernel

theorem k2468_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2468) 3).2 2).1 1).2
      3961030464369652129369021286569260123184456400407732282139540804461155048831007053628).isSome = true := by
  decide +kernel

theorem k2468_5 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2468) 3).2 2).2
      6520418264433616956245514831098018377915926585537297567253744694195482071106805902816702236449008908005651370402952270735247252337343492881801138929).isSome = true := by
  decide +kernel

theorem k2469_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2469) 3).1 2).1
      415551863037785283402929775587236670057015365976954614195517682176482220901394708273224698603200179668376373903890242305847187073569372874463721754428).isSome = true := by
  decide +kernel

theorem k2469_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2469) 3).1 2).2
      352083471720386284469582329614517537834007197123172279241504790800977347208112035656814612291151621304820131818023417324971586801).isSome = true := by
  decide +kernel

theorem k2469_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2469) 3).2 2).1
      25893429252703731517821882767074453297853907176168338910520747753909276607927953684828368516232235426634605556303466451776236471007330132785188647740).isSome = true := by
  decide +kernel

theorem k2469_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2469) 3).2 2).2
      87765058354581751389115329003989039898478881502012842969431761966112030564538890313424083338740007623138344256999215971463672636).isSome = true := by
  decide +kernel

theorem k2470_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2470) 3).1 2).1
      303577607247337487088965055478736235288923444390673967026022617539306083659764553052143043642775950708772422460).isSome = true := by
  decide +kernel

theorem k2470_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2470) 3).1 2).2
      350206041620401135714977654088072997089936900590120214049646653072542759327974243618435024857842496460817676880183786874991485756).isSome = true := by
  decide +kernel

theorem k2470_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2470) 3).2 2).1
      5459292227841056954849905261363564984047739034499267258321983594143479703367631942427082364861572532654805669293201524073495612).isSome = true := by
  decide +kernel

theorem k2470_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2470) 3).2 2).2
      18947193390006236833014891950362368465364071888817942360526600558709012657032197760721092711871943367533249340).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 2467 2471 :=
  (Cover.one (box := dirCellBox) (n := 2467)
      (.split 3 (.split 3 (.leaf _ k2467_0) (.leaf _ k2467_1)) (.split 3 (.leaf _ k2467_2) (.split 2 (.leaf _ k2467_3) (.leaf _ k2467_4))))).trans <|
  (Cover.one (box := dirCellBox) (n := 2468)
      (.split 3 (.split 2 (.split 1 (.leaf _ k2468_0) (.leaf _ k2468_1)) (.leaf _ k2468_2)) (.split 2 (.split 1 (.leaf _ k2468_3) (.leaf _ k2468_4)) (.leaf _ k2468_5)))).trans <|
  (Cover.one (box := dirCellBox) (n := 2469)
      (.split 3 (.split 2 (.leaf _ k2469_0) (.leaf _ k2469_1)) (.split 2 (.leaf _ k2469_2) (.leaf _ k2469_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 2470)
      (.split 3 (.split 2 (.leaf _ k2470_0) (.leaf _ k2470_1)) (.split 2 (.leaf _ k2470_2) (.leaf _ k2470_3))))

end C4.Cert.Dir048
