module

public import C4Check

public section

/-! Cells `2775 ≤ n < 2776` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir061

theorem k2775_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2775) 2).1 3).1 3).1 2).1 3).1 1).1
      4011184128822625840483674999912158429481257902601643400441226019487714070608941148588).isSome = true := by
  decide +kernel

theorem k2775_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2775) 2).1 3).1 3).1 2).1 3).1 1).2
      13902962716792466709140359876813660467493336813442550394446694828604).isSome = true := by
  decide +kernel

theorem k2775_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2775) 2).1 3).1 3).1 2).1 3).2 1).1
      63986285075022028866949291193777484488472540237269491526317114856523646637051598994604).isSome = true := by
  decide +kernel

theorem k2775_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2775) 2).1 3).1 3).1 2).1 3).2 1).2
      55460278520122765600076605946923790223312946959845255043209378656828).isSome = true := by
  decide +kernel

theorem k2775_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2775) 2).1 3).1 3).1 2).2 1).1 2).1
      868234374546553093878107653618250408093622259854489998814732376499).isSome = true := by
  decide +kernel

theorem k2775_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2775) 2).1 3).1 3).1 2).2 1).1 2).2
      13606125889626692530896241529610243099626803179062190623246876076).isSome = true := by
  decide +kernel

theorem k2775_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2775) 2).1 3).1 3).1 2).2 1).2 3).1
      870930091580247899830506977926880057227737723064783736981585131180).isSome = true := by
  decide +kernel

theorem k2775_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2775) 2).1 3).1 3).1 2).2 1).2 3).2
      217067320377391183623133330614329735977320752777615299349157765804).isSome = true := by
  decide +kernel

theorem k2775_8 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2775) 2).1 3).1 3).2 2).1 3).1 1).1
      63827974130582020249140724095586847162593128348727055844493177091165379455445733572396).isSome = true := by
  decide +kernel

theorem k2775_9 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2775) 2).1 3).1 3).2 2).1 3).1 1).2
      255149284480789093117686536786843966232502885908083442997268431571534184409464175063612).isSome = true := by
  decide +kernel

theorem k2775_10 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2775) 2).1 3).1 3).2 2).1 3).2 1).1
      3979768276749774085060753928826247308201904828686821576296684542275301636194128326444).isSome = true := by
  decide +kernel

theorem k2775_11 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2775) 2).1 3).1 3).2 2).1 3).2 1).2
      862402208296122131144068744667798399051184155284902620039214906428).isSome = true := by
  decide +kernel

theorem k2775_12 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2775) 2).1 3).1 3).2 2).2 3).1 1).1
      54162374560733921467441026042115425625068052595573067568361371820).isSome = true := by
  decide +kernel

theorem k2775_13 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2775) 2).1 3).1 3).2 2).2 3).1 1).2
      216508625073808079714161356426941309614561528030476659137554407996).isSome = true := by
  decide +kernel

theorem k2775_14 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2775) 2).1 3).1 3).2 2).2 3).2 1).1
      54034838050483686836259225542263723510781633476990244449996372140).isSome = true := by
  decide +kernel

theorem k2775_15 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2775) 2).1 3).1 3).2 2).2 3).2 1).2
      3456362368515855390959858064807205502246358586664423884651224363580).isSome = true := by
  decide +kernel

theorem k2775_16 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2775) 2).1 3).2 3).1 2).1 1).1 3).1
      3971757604517187469432824428331595188121652252376825220343099870447461909495123767084).isSome = true := by
  decide +kernel

theorem k2775_17 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2775) 2).1 3).2 3).1 2).1 1).1 3).2
      13433039529307489582396863142115218739647557226414270129307741996).isSome = true := by
  decide +kernel

theorem k2775_18 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2775) 2).1 3).2 3).1 2).1 1).2 2).1
      3438198212504829881463480877466672607481695496827316620090471726140).isSome = true := by
  decide +kernel

theorem k2775_19 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2775) 2).1 3).2 3).1 2).1 1).2 2).2
      3441101940137995916053284748278869075546664805777833985467844770876).isSome = true := by
  decide +kernel

theorem k2775_20 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2775) 2).1 3).2 3).1 2).2 1).1
      16654651178485729427079026408022201291461378271342184260661603075883414980803963443220954291).isSome = true := by
  decide +kernel

theorem k2775_21 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2775) 2).1 3).2 3).1 2).2 1).2 1).1
      861473970892796804163907223194165025066872742293558065571945102396).isSome = true := by
  decide +kernel

theorem k2775_22 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2775) 2).1 3).2 3).1 2).2 1).2 1).2
      861195757189728939072818747283485263296181142828628952820278475836).isSome = true := by
  decide +kernel

theorem k2775_23 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2775) 2).1 3).2 3).2 2).1 1).1
      258981613493351086849839657207833372022421186831752678034701869201157262123548618322947891).isSome = true := by
  decide +kernel

theorem k2775_24 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2775) 2).1 3).2 3).2 2).1 1).2
      1061501392406348809144316998156796071017510650092655421956376235602803712865054271095514319090).isSome = true := by
  decide +kernel

theorem k2775_25 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2775) 2).1 3).2 3).2 2).2 1).1
      88538921159626617791883467762455909605051315645826443430039837007910481999482643362247875261679488152815046052168953055168527153).isSome = true := by
  decide +kernel

theorem k2775_26 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2775) 2).1 3).2 3).2 2).2 1).2
      6525818230013472938384243869433627116008913633622404404166795254935016233520214933224086626950617286292954628974653732270046349228267200795377466428).isSome = true := by
  decide +kernel

theorem k2775_27 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2775) 2).2 3).1 3).1 2).1 1).1
      75844113308530583260658408401298179899791218496858105516657550219161301880626188202143010104696948225844915).isSome = true := by
  decide +kernel

theorem k2775_28 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2775) 2).2 3).1 3).1 2).1 1).2
      1051824024001894259534028202693343783288609212443994791569258294662042438206658173204929203).isSome = true := by
  decide +kernel

theorem k2775_29 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2775) 2).2 3).1 3).1 2).2 1).1
      257877151805227520991069601518618978320403945192077559499590068298724518264678385034930).isSome = true := by
  decide +kernel

theorem k2775_30 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2775) 2).2 3).1 3).1 2).2 1).2
      1028847489636502101554606370184925658519821498371258371358778063355611503795849991136947).isSome = true := by
  decide +kernel

theorem k2775_31 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2775) 2).2 3).1 3).2 2).1 1).1
      1206889381680254751422927987401403425821635506369538309296092529944057389521927562169068598546633853988366003).isSome = true := by
  decide +kernel

theorem k2775_32 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2775) 2).2 3).1 3).2 2).1 1).2 2).1
      216536533362509136952608894325516354054326442795987815762641805884).isSome = true := by
  decide +kernel

theorem k2775_33 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2775) 2).2 3).1 3).2 2).1 1).2 2).2
      2936681369614385027553824075697796168147700284).isSome = true := by
  decide +kernel

theorem k2775_34 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2775) 2).2 3).1 3).2 2).2 1).1
      75664195600405234635186458867494465741729719343480431625078930511954964971085206091048781325379450175321004).isSome = true := by
  decide +kernel

theorem k2775_35 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2775) 2).2 3).1 3).2 2).2 1).2
      4203725244823943739645055673749751494624198508716666839843496122894551680132152820215969457).isSome = true := by
  decide +kernel

theorem k2775_36 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2775) 2).2 3).2 3).1 2).1 1).1
      1043890524226631753746044118878151206446146835043843404490276435146436246268620332782419122).isSome = true := by
  decide +kernel

theorem k2775_37 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2775) 2).2 3).2 3).1 2).1 1).2 2).1
      46746991892247490203628173219098832120347816508).isSome = true := by
  decide +kernel

theorem k2775_38 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2775) 2).2 3).2 3).1 2).1 1).2 2).2
      11696108965524029850668041074223178542480876092).isSome = true := by
  decide +kernel

theorem k2775_39 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2775) 2).2 3).2 3).1 2).2 1).1
      16325070544440364555379000580096913818634677213857462131570144551582443481517506276221617).isSome = true := by
  decide +kernel

theorem k2775_40 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2775) 2).2 3).2 3).1 2).2 1).2
      1043293380250873756076159041993809067965694679431112269728011476808394118164202402311186675).isSome = true := by
  decide +kernel

theorem k2775_41 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2775) 2).2 3).2 3).2 2).1 1).1
      1039010061415176168941914099113365967456810824431472763456427455005227041922586582868130995).isSome = true := by
  decide +kernel

theorem k2775_42 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2775) 2).2 3).2 3).2 2).1 1).2
      66454868414470366076413378031616393644818595479370541295156908448026033130577900368217698547).isSome = true := by
  decide +kernel

theorem k2775_43 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2775) 2).2 3).2 3).2 2).2 1).1
      1016758030827026277981238628534104748179270587805551805422959872490510316958020823413308).isSome = true := by
  decide +kernel

theorem k2775_44 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2775) 2).2 3).2 3).2 2).2 1).2
      1199757966616042979178531196962480510177124990901866660403389271656327803198645886406782492925532787433009724).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 2775 2776 :=
  (Cover.one (box := dirCellBox) (n := 2775)
      (.split 2 (.split 3 (.split 3 (.split 2 (.split 3 (.split 1 (.leaf _ k2775_0) (.leaf _ k2775_1)) (.split 1 (.leaf _ k2775_2) (.leaf _ k2775_3))) (.split 1 (.split 2 (.leaf _ k2775_4) (.leaf _ k2775_5)) (.split 3 (.leaf _ k2775_6) (.leaf _ k2775_7)))) (.split 2 (.split 3 (.split 1 (.leaf _ k2775_8) (.leaf _ k2775_9)) (.split 1 (.leaf _ k2775_10) (.leaf _ k2775_11))) (.split 3 (.split 1 (.leaf _ k2775_12) (.leaf _ k2775_13)) (.split 1 (.leaf _ k2775_14) (.leaf _ k2775_15))))) (.split 3 (.split 2 (.split 1 (.split 3 (.leaf _ k2775_16) (.leaf _ k2775_17)) (.split 2 (.leaf _ k2775_18) (.leaf _ k2775_19))) (.split 1 (.leaf _ k2775_20) (.split 1 (.leaf _ k2775_21) (.leaf _ k2775_22)))) (.split 2 (.split 1 (.leaf _ k2775_23) (.leaf _ k2775_24)) (.split 1 (.leaf _ k2775_25) (.leaf _ k2775_26))))) (.split 3 (.split 3 (.split 2 (.split 1 (.leaf _ k2775_27) (.leaf _ k2775_28)) (.split 1 (.leaf _ k2775_29) (.leaf _ k2775_30))) (.split 2 (.split 1 (.leaf _ k2775_31) (.split 2 (.leaf _ k2775_32) (.leaf _ k2775_33))) (.split 1 (.leaf _ k2775_34) (.leaf _ k2775_35)))) (.split 3 (.split 2 (.split 1 (.leaf _ k2775_36) (.split 2 (.leaf _ k2775_37) (.leaf _ k2775_38))) (.split 1 (.leaf _ k2775_39) (.leaf _ k2775_40))) (.split 2 (.split 1 (.leaf _ k2775_41) (.leaf _ k2775_42)) (.split 1 (.leaf _ k2775_43) (.leaf _ k2775_44)))))))

end C4.Cert.Dir061
