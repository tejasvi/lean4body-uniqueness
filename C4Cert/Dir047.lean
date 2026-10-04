module

public import C4Check

public section

/-! Cells `2469 ≤ n < 2473` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir047

theorem k2469_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2469) 3).1 2).1 3).1 1).1
      13378677370235516333786981599687876717492916351031341015640931756).isSome = true := by
  decide +kernel

theorem k2469_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2469) 3).1 2).1 3).1 1).2
      63168754395446575059257570577083416723689862207661260126158306276647455757956372486716).isSome = true := by
  decide +kernel

theorem k2469_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2469) 3).1 2).1 3).2 1).1
      2895575550795814117367999628222665933711602348).isSome = true := by
  decide +kernel

theorem k2469_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2469) 3).1 2).1 3).2 1).2
      3418358062512660221274430008528468030003038642745747905237055173180).isSome = true := by
  decide +kernel

theorem k2469_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2469) 3).1 2).2 1).1
      4767809741655816298166346127118462817620005794396219899032086116635080995268903726905794079283903093071799987).isSome = true := by
  decide +kernel

theorem k2469_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2469) 3).1 2).2 1).2
      305120778776443180834442240496672336255396738280669315850119422322502287682005603377365654286341536329197132019).isSome = true := by
  decide +kernel

theorem k2469_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2469) 3).2 2).1 1).1 3).1
      46260518286951089305355968102190882487960793660).isSome = true := by
  decide +kernel

theorem k2469_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2469) 3).2 2).1 1).1 3).2
      53263407846169551551039385043574276259124472413217997772237945916).isSome = true := by
  decide +kernel

theorem k2469_8 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2469) 3).2 2).1 1).2 3).1
      54606382401401698803442852249846849894279052677535736065005428929084).isSome = true := by
  decide +kernel

theorem k2469_9 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2469) 3).2 2).1 1).2 3).2
      3408544524829907377041497921525299111684155761741348320337509334076).isSome = true := by
  decide +kernel

theorem k2469_10 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2469) 3).2 2).2 1).1
      264079451236726827091208652837956091077601120645238853693646806039777547363456739977589147890).isSome = true := by
  decide +kernel

theorem k2469_11 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2469) 3).2 2).2 1).2
      264060827477144825053786668546119705771136145553758216083379346411295593219390714932098746610).isSome = true := by
  decide +kernel

theorem k2470_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2470) 3).1 2).1 1).1 3).1
      3404449632403877038656183906673828117673379903733845739925750856764).isSome = true := by
  decide +kernel

theorem k2470_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2470) 3).1 2).1 1).1 3).2
      53148701020796800027791987539995080709045619497316934431763983420).isSome = true := by
  decide +kernel

theorem k2470_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2470) 3).1 2).1 1).2 3).1
      3404153971496586665476889073406641981312577487510664504636544826428).isSome = true := by
  decide +kernel

theorem k2470_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2470) 3).1 2).1 1).2 3).2
      11532011063995446617730561474017345697599384636).isSome = true := by
  decide +kernel

theorem k2470_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2470) 3).1 2).2 1).1
      5608832945109479763373044113079341821787175554945760667896559499737806229120786184859670337215829462374632065806186656739655872754).isSome = true := by
  decide +kernel

theorem k2470_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2470) 3).1 2).2 1).2
      6465389655073508757233145657406781036431982740465814768122014143209052004267407966151277833407405326282063004674975347962140362989549241441219050556).isSome = true := by
  decide +kernel

theorem k2470_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2470) 3).2 2).1 1).1
      18926909316719313978964357200310115615615201743032103062564125297513084865851525162451013316468177828304223027).isSome = true := by
  decide +kernel

theorem k2470_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2470) 3).2 2).1 1).2
      4731469856960922661342983825503865757932866673210047222309296479498833771889022917818382318724602416642751283).isSome = true := by
  decide +kernel

theorem k2470_8 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2470) 3).2 2).2 1).1
      1027454786545234349504003837078646587954421813919823298914717294077045905106444054516920563).isSome = true := by
  decide +kernel

theorem k2470_9 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2470) 3).2 2).2 1).2
      4736076672874127656937603123362896150274189854023524072384202545718774078168619311435060607323712325567691836).isSome = true := by
  decide +kernel

theorem k2471_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2471) 3).1 2).1 1).1
      349138947354499174475756790845512748515081630048951909207234506355584171888366949259609888419929206148738072083790528483895489484).isSome = true := by
  decide +kernel

theorem k2471_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2471) 3).1 2).1 1).2
      87281072303269560796593086055957137740501383306135171070006647782834275020585807264520239979930554806547676139739729534589023180).isSome = true := by
  decide +kernel

theorem k2471_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2471) 3).1 2).2 1).1
      1001376769201969485000756214496325376509693000640881749428651010551361658294740406685388).isSome = true := by
  decide +kernel

theorem k2471_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2471) 3).1 2).2 1).2
      16020586193646653953959865027661974499125365658819176115743500413070868090605098694915020).isSome = true := by
  decide +kernel

theorem k2471_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2471) 3).2 2).1 1).1
      73764752895193948634705986823200837488196108640146960780929029926565094419715245548891831267800654414817996).isSome = true := by
  decide +kernel

theorem k2471_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2471) 3).2 2).1 1).2
      999734238962453662353053774391364907645715703506478408426866326433771130341295078206156).isSome = true := by
  decide +kernel

theorem k2471_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2471) 3).2 2).2 1).1
      847948863775375702551101567747193436396791141283041902174223719116).isSome = true := by
  decide +kernel

theorem k2471_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2471) 3).2 2).2 1).2
      1000066988373947513925178925212279639995893003569839736298607382155915481962850360861644).isSome = true := by
  decide +kernel

theorem k2472_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2472) 3).1 2).1 1).1
      62424102851208722425016045672236288773684550220860398682297544254870891625879040936652).isSome = true := by
  decide +kernel

theorem k2472_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2472) 3).1 2).1 1).2
      3901507671156416634907185734695257139263901864580415449590552291559960550643764550348).isSome = true := by
  decide +kernel

theorem k2472_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2472) 3).1 2).2 1).1
      211751880534205810523427764189269100082164455714309442116060170956).isSome = true := by
  decide +kernel

theorem k2472_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2472) 3).1 2).2 1).2
      3387893721651166556995122496392205449544356426527723866127597347788).isSome = true := by
  decide +kernel

theorem k2472_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2472) 3).2 2).1 1).1
      211321406116585057889406919051071064067706750999661803014115019468).isSome = true := by
  decide +kernel

theorem k2472_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2472) 3).2 2).1 1).2
      3898426166846032915256711306308910439816779446256838710003077375426649114981384575692).isSome = true := by
  decide +kernel

theorem k2472_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2472) 3).2 2).2 1).1
      211381582925590755628589925366610663751313220047805156045146801100).isSome = true := by
  decide +kernel

theorem k2472_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2472) 3).2 2).2 1).2
      845460919986816187856475558047452981145142691153335689531162045132).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 2469 2473 :=
  (Cover.one (box := dirCellBox) (n := 2469)
      (.split 3 (.split 2 (.split 3 (.split 1 (.leaf _ k2469_0) (.leaf _ k2469_1)) (.split 1 (.leaf _ k2469_2) (.leaf _ k2469_3))) (.split 1 (.leaf _ k2469_4) (.leaf _ k2469_5))) (.split 2 (.split 1 (.split 3 (.leaf _ k2469_6) (.leaf _ k2469_7)) (.split 3 (.leaf _ k2469_8) (.leaf _ k2469_9))) (.split 1 (.leaf _ k2469_10) (.leaf _ k2469_11))))).trans <|
  (Cover.one (box := dirCellBox) (n := 2470)
      (.split 3 (.split 2 (.split 1 (.split 3 (.leaf _ k2470_0) (.leaf _ k2470_1)) (.split 3 (.leaf _ k2470_2) (.leaf _ k2470_3))) (.split 1 (.leaf _ k2470_4) (.leaf _ k2470_5))) (.split 2 (.split 1 (.leaf _ k2470_6) (.leaf _ k2470_7)) (.split 1 (.leaf _ k2470_8) (.leaf _ k2470_9))))).trans <|
  (Cover.one (box := dirCellBox) (n := 2471)
      (.split 3 (.split 2 (.split 1 (.leaf _ k2471_0) (.leaf _ k2471_1)) (.split 1 (.leaf _ k2471_2) (.leaf _ k2471_3))) (.split 2 (.split 1 (.leaf _ k2471_4) (.leaf _ k2471_5)) (.split 1 (.leaf _ k2471_6) (.leaf _ k2471_7))))).trans <|
  (Cover.one (box := dirCellBox) (n := 2472)
      (.split 3 (.split 2 (.split 1 (.leaf _ k2472_0) (.leaf _ k2472_1)) (.split 1 (.leaf _ k2472_2) (.leaf _ k2472_3))) (.split 2 (.split 1 (.leaf _ k2472_4) (.leaf _ k2472_5)) (.split 1 (.leaf _ k2472_6) (.leaf _ k2472_7)))))

end C4.Cert.Dir047
