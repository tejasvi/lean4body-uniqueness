module

public import C4Check

public section

/-! Cells `2384 ≤ n < 2385` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir039

theorem k2384_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2384) 3).1 2).1 3).1 2).1 1).1
      18632373929868906138142498519397144463368245776387197435093531407682847789524683394387235135146078033509555).isSome = true := by
  decide +kernel

theorem k2384_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2384) 3).1 2).1 3).1 2).1 1).2
      1010161625525696704177826132659758730903330987956881113076437785929241071069824345283377).isSome = true := by
  decide +kernel

theorem k2384_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2384) 3).1 2).1 3).1 2).2 1).1
      74614482986946417632156362158624046718110340041567512043614921905553842804540699341247345470157209326681267).isSome = true := by
  decide +kernel

theorem k2384_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2384) 3).1 2).1 3).1 2).2 1).2
      64722712392471577821539886282642513950888545165867013165460286851618034878771634621722417).isSome = true := by
  decide +kernel

theorem k2384_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2384) 3).1 2).1 3).2 2).1 1).1
      62996182554718068873065537701982401560173860386907344581203931094916722731489921817395).isSome = true := by
  decide +kernel

theorem k2384_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2384) 3).1 2).1 3).2 2).1 1).2
      1162435220078570843556678241830866753773403187815465265211394329861965042325383320026468410910727355593676).isSome = true := by
  decide +kernel

theorem k2384_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2384) 3).1 2).1 3).2 2).2 1).1
      63056682676681082919166751307498798878929724051325712129645749595243770342244666530611).isSome = true := by
  decide +kernel

theorem k2384_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2384) 3).1 2).1 3).2 2).2 1).2
      15768628259337571486232305941351981072750013510003862908763201256871113867768145234892).isSome = true := by
  decide +kernel

theorem k2384_8 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2384) 3).1 2).2 3).1 2).1 1).1
      63333083083388290180870235714744669159568191724381085119048948830848553850435388464307).isSome = true := by
  decide +kernel

theorem k2384_9 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2384) 3).1 2).2 3).1 2).1 1).2
      4679771597820716118616245092629007757660477393572883996840042203064603082486528172308294639277140575338284).isSome = true := by
  decide +kernel

theorem k2384_10 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2384) 3).1 2).2 3).1 2).2 1).1
      63339296486968194973575002998383480587298221191770005689017895322744092837945206922419).isSome = true := by
  decide +kernel

theorem k2384_11 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2384) 3).1 2).2 3).1 2).2 1).2
      292298156366590780306330463338880639202568259556157313984376104512748678543020109421581287382188935708460).isSome = true := by
  decide +kernel

theorem k2384_12 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2384) 3).1 2).2 3).2 2).1 1).1
      252598635328868964675649904505145116007770169745095443592599116001364166879267189054257).isSome = true := by
  decide +kernel

theorem k2384_13 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2384) 3).1 2).2 3).2 2).1 1).2
      291213480655915351241033084924457116741633735198750627787063517536829910029844667005734188981899573451724).isSome = true := by
  decide +kernel

theorem k2384_14 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2384) 3).1 2).2 3).2 2).2 1).1
      63212089960925964889216610215670795410119782534289395421251669650319472356381125170993).isSome = true := by
  decide +kernel

theorem k2384_15 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2384) 3).1 2).2 3).2 2).2 1).2
      3950446501101764236061054442404299505811740398772641760285128652137788000703008436012).isSome = true := by
  decide +kernel

theorem k2384_16 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2384) 3).2 2).1 3).1 1).1 2).1
      62889230091444145155042470799257435579104766652990896919185929145239182616913725184819).isSome = true := by
  decide +kernel

theorem k2384_17 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2384) 3).2 2).1 3).1 1).1 2).2
      62938533668388562862002465148176098289873074642975386475563487142390954458262056950579).isSome = true := by
  decide +kernel

theorem k2384_18 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2384) 3).2 2).1 3).1 1).2 2).1
      72526940533742998616950050607563147140051822166543176755763913054646728315055574959332745117019381128908).isSome = true := by
  decide +kernel

theorem k2384_19 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2384) 3).2 2).1 3).1 1).2 2).2
      983759163663049507961754316961939176499418780671150017622215793838914212421393342156).isSome = true := by
  decide +kernel

theorem k2384_20 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2384) 3).2 2).1 3).2 1).1
      21948704766568079984548102066532238005263029723647006307037308243601745448087204694769370162944096158217987968231582185095027506).isSome = true := by
  decide +kernel

theorem k2384_21 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2384) 3).2 2).1 3).2 1).2
      21942582857323245551813308162224576561537799641759796252050270115799106217970693225172980521987524835475212524584521072970780466).isSome = true := by
  decide +kernel

theorem k2384_22 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2384) 3).2 2).2 3).1 2).1 1).1
      984887948372130876933911049629932271903531797210341364365460919636593350354352828108).isSome = true := by
  decide +kernel

theorem k2384_23 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2384) 3).2 2).2 3).1 2).1 1).2
      984643151230833762167361006354366294872459673538957258998839057635011676269363224268).isSome = true := by
  decide +kernel

theorem k2384_24 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2384) 3).2 2).2 3).1 2).2 1).1
      213751768186892354285082444846169501001369691583914411323385802540).isSome = true := by
  decide +kernel

theorem k2384_25 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2384) 3).2 2).2 3).1 2).2 1).2
      53419490849456046988216520746257106642327140158077673004421705420).isSome = true := by
  decide +kernel

theorem k2384_26 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2384) 3).2 2).2 3).2 1).1
      76110121461537996987759945355555496583731633192652058078626627921353008455551513264859727477840519783180095282).isSome = true := by
  decide +kernel

theorem k2384_27 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2384) 3).2 2).2 3).2 1).2
      1403890922607258723132890429483292139271580394009455777306303290872731267913867238851307348059188834469933153864367130432975104818).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 2384 2385 :=
  (Cover.one (box := dirCellBox) (n := 2384)
      (.split 3 (.split 2 (.split 3 (.split 2 (.split 1 (.leaf _ k2384_0) (.leaf _ k2384_1)) (.split 1 (.leaf _ k2384_2) (.leaf _ k2384_3))) (.split 2 (.split 1 (.leaf _ k2384_4) (.leaf _ k2384_5)) (.split 1 (.leaf _ k2384_6) (.leaf _ k2384_7)))) (.split 3 (.split 2 (.split 1 (.leaf _ k2384_8) (.leaf _ k2384_9)) (.split 1 (.leaf _ k2384_10) (.leaf _ k2384_11))) (.split 2 (.split 1 (.leaf _ k2384_12) (.leaf _ k2384_13)) (.split 1 (.leaf _ k2384_14) (.leaf _ k2384_15))))) (.split 2 (.split 3 (.split 1 (.split 2 (.leaf _ k2384_16) (.leaf _ k2384_17)) (.split 2 (.leaf _ k2384_18) (.leaf _ k2384_19))) (.split 1 (.leaf _ k2384_20) (.leaf _ k2384_21))) (.split 3 (.split 2 (.split 1 (.leaf _ k2384_22) (.leaf _ k2384_23)) (.split 1 (.leaf _ k2384_24) (.leaf _ k2384_25))) (.split 1 (.leaf _ k2384_26) (.leaf _ k2384_27))))))

end C4.Cert.Dir039
