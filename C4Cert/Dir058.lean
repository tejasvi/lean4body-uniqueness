module

public import C4Check

public section

/-! Cells `2746 ≤ n < 2747` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir058

theorem k2746_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2746) 3).1 2).1 3).1 2).1 3).1
      26975054177416826968135844440212128049791506071486469026361731303664436709291493265014611293652826695527031349811521014855514610338396776540965668297).isSome = true := by
  decide +kernel

theorem k2746_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2746) 3).1 2).1 3).1 2).1 3).2
      6699796654322343722096505090172026665282407548991185846584373313485153548606663620931032181976430705274336761115307110077001640490679928694719911369).isSome = true := by
  decide +kernel

theorem k2746_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2746) 3).1 2).1 3).1 2).2 1).1
      5740101663858614994688815359869562718970860455652676491533125883621934255457378765300455142743388964799947646283836313347412722).isSome = true := by
  decide +kernel

theorem k2746_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2746) 3).1 2).1 3).1 2).2 1).2 3).1
      223525778861073598062099716804503191429042296739633714306759513916).isSome = true := by
  decide +kernel

theorem k2746_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2746) 3).1 2).1 3).1 2).2 1).2 3).2
      48107853323734254812119021614347674646306507580).isSome = true := by
  decide +kernel

theorem k2746_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2746) 3).1 2).1 3).2 2).1 3).1
      1444662450681690401150705409306810752673246128677228919487830531541569684153617378842178739561866256687301409035923245369663059185).isSome = true := by
  decide +kernel

theorem k2746_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2746) 3).1 2).1 3).2 2).1 3).2
      22455223560389183343594302658969084613700591980795001417366711266498905983698478035539025584022843196504615341257975648992583089).isSome = true := by
  decide +kernel

theorem k2746_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2746) 3).1 2).1 3).2 2).2 1).1
      354298900066887274546623358794982749385558118985557281117362873073496700104465437736566199038858746811235377291338866918520050).isSome = true := by
  decide +kernel

theorem k2746_8 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2746) 3).1 2).1 3).2 2).2 1).2 2).1
      54928961220912920563588151109634605874807981447335563883901744700).isSome = true := by
  decide +kernel

theorem k2746_9 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2746) 3).1 2).1 3).2 2).2 1).2 2).2
      55049385358117479726291886882129700658336873124655399855972546108).isSome = true := by
  decide +kernel

theorem k2746_10 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2746) 3).1 2).2 3).1 2).1 1).1
      26479477421464757032200085987176598830035857727474449229972564388501689887102778741324470600857750806071986993460138800764193488374479607004231155).isSome = true := by
  decide +kernel

theorem k2746_11 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2746) 3).1 2).2 3).1 2).1 1).2
      4210844139959437076382218799762918943794016939936682564054411570959618641403059087250163).isSome = true := by
  decide +kernel

theorem k2746_12 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2746) 3).1 2).2 3).1 2).2 1).1
      22593776173041954826923915921297537340754976354383290798656646511290865573858920692557388599178237771942175572224647809037564).isSome = true := by
  decide +kernel

theorem k2746_13 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2746) 3).1 2).2 3).1 2).2 1).2
      265402249606296255642913807602323126388323252706714401583340605970408315772380777575666).isSome = true := by
  decide +kernel

theorem k2746_14 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2746) 3).1 2).2 3).2 1).1 2).1
      77134901928207535630470615246138701359479649246286508266433209526317674498945022364488456269242545717212402).isSome = true := by
  decide +kernel

theorem k2746_15 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2746) 3).1 2).2 3).2 1).1 2).2
      1204992011159168992280532714621775301751355709841524869463792045781698499119550133093551194060603784324595).isSome = true := by
  decide +kernel

theorem k2746_16 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2746) 3).1 2).2 3).2 1).2 2).1
      16707548600402461975721541607803997589689175576128212325361486734573932984889780774344946).isSome = true := by
  decide +kernel

theorem k2746_17 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2746) 3).1 2).2 3).2 1).2 2).2
      65492183688387538799236627957030879340650067814454027580814202748276006653925683520754).isSome = true := by
  decide +kernel

theorem k2746_18 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2746) 3).2 2).1 2).1 3).1 1).1
      1180843870836338747745213654388890230968825743472012399443220136698152271915025524333478872757878933052851).isSome = true := by
  decide +kernel

theorem k2746_19 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2746) 3).2 2).1 2).1 3).1 1).2 2).1
      54217779202532915040403428883390012867297012567258264935650947644).isSome = true := by
  decide +kernel

theorem k2746_20 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2746) 3).2 2).1 2).1 3).1 1).2 2).2
      54322916243127547355961480632448701403248639609935746791886942780).isSome = true := by
  decide +kernel

theorem k2746_21 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2746) 3).2 2).1 2).1 3).2 1).1
      63671549062405169560237226341321653129321027344558818896935253757563270977847378336947).isSome = true := by
  decide +kernel

theorem k2746_22 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2746) 3).2 2).1 2).1 3).2 1).2
      254421550303371373597432884217090027601265602824688414963035511624594077266126458150067).isSome = true := by
  decide +kernel

theorem k2746_23 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2746) 3).2 2).1 2).2 3).1 1).1
      21940830043192300204371972462100195933045976249629273148268559548529795381385291319022788404503153487638259716327415648181682).isSome = true := by
  decide +kernel

theorem k2746_24 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2746) 3).2 2).1 2).2 3).1 1).2
      75938153606156574160535241853261527617820897203707029628787227861959973744864459148931975682177104802204220).isSome = true := by
  decide +kernel

theorem k2746_25 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2746) 3).2 2).1 2).2 3).2 1).1
      15986501757003346592076223872858426890285434448681974935612630352963211433041539232428).isSome = true := by
  decide +kernel

theorem k2746_26 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2746) 3).2 2).1 2).2 3).2 1).2
      4082215847307341754463491791514416076078758959859663282328181129309134029039845256884467).isSome = true := by
  decide +kernel

theorem k2746_27 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2746) 3).2 2).2 3).1 2).1 1).1
      16158039342354637376805874757613783570781521765105392089070537788239878634687478844220).isSome = true := by
  decide +kernel

theorem k2746_28 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2746) 3).2 2).2 3).1 2).1 1).2
      1031304593133392131274205599873229743498188740882309812460813414100883853260160468557235).isSome = true := by
  decide +kernel

theorem k2746_29 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2746) 3).2 2).2 3).1 2).2 1).1
      16216275012441482980879892598951313037622142069559960108157884760131686874665115440956).isSome = true := by
  decide +kernel

theorem k2746_30 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2746) 3).2 2).2 3).1 2).2 1).2
      219475457682965754876070735663123202207750477485396546790255743804).isSome = true := by
  decide +kernel

theorem k2746_31 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2746) 3).2 2).2 3).2 2).1 1).1
      1002554308526892756913628413681020035588568467553638810104839479658704508384392377916).isSome = true := by
  decide +kernel

theorem k2746_32 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2746) 3).2 2).2 3).2 2).1 1).2
      16019497183286356607129879146431091791566580265520172811226397506767285715090773242428).isSome = true := by
  decide +kernel

theorem k2746_33 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2746) 3).2 2).2 3).2 2).2 1).1
      1005397889043873477910664908671853637939481143112948419455544326044216276009479435836).isSome = true := by
  decide +kernel

theorem k2746_34 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2746) 3).2 2).2 3).2 2).2 1).2
      54455366056980854911881479640424668732574396695398871716134778428).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 2746 2747 :=
  (Cover.one (box := dirCellBox) (n := 2746)
      (.split 3 (.split 2 (.split 3 (.split 2 (.split 3 (.leaf _ k2746_0) (.leaf _ k2746_1)) (.split 1 (.leaf _ k2746_2) (.split 3 (.leaf _ k2746_3) (.leaf _ k2746_4)))) (.split 2 (.split 3 (.leaf _ k2746_5) (.leaf _ k2746_6)) (.split 1 (.leaf _ k2746_7) (.split 2 (.leaf _ k2746_8) (.leaf _ k2746_9))))) (.split 3 (.split 2 (.split 1 (.leaf _ k2746_10) (.leaf _ k2746_11)) (.split 1 (.leaf _ k2746_12) (.leaf _ k2746_13))) (.split 1 (.split 2 (.leaf _ k2746_14) (.leaf _ k2746_15)) (.split 2 (.leaf _ k2746_16) (.leaf _ k2746_17))))) (.split 2 (.split 2 (.split 3 (.split 1 (.leaf _ k2746_18) (.split 2 (.leaf _ k2746_19) (.leaf _ k2746_20))) (.split 1 (.leaf _ k2746_21) (.leaf _ k2746_22))) (.split 3 (.split 1 (.leaf _ k2746_23) (.leaf _ k2746_24)) (.split 1 (.leaf _ k2746_25) (.leaf _ k2746_26)))) (.split 3 (.split 2 (.split 1 (.leaf _ k2746_27) (.leaf _ k2746_28)) (.split 1 (.leaf _ k2746_29) (.leaf _ k2746_30))) (.split 2 (.split 1 (.leaf _ k2746_31) (.leaf _ k2746_32)) (.split 1 (.leaf _ k2746_33) (.leaf _ k2746_34)))))))

end C4.Cert.Dir058
