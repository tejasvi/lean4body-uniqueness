module

public import C4Check

public section

/-! Cells `2747 ≤ n < 2748` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir059

theorem k2747_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2747) 2).1 3).1 2).1 3).1 1).1
      3963517034292774994866174610774360587405412486690513114680198069550929428689072592691).isSome = true := by
  decide +kernel

theorem k2747_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2747) 2).1 3).1 2).1 3).1 1).2
      15862896632655472755133537126856584833794519869771472629500125677900033944349478090300).isSome = true := by
  decide +kernel

theorem k2747_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2747) 2).1 3).1 2).1 3).2 1).1
      247150506100821105631992808963800757361407452416232683715208220928064956453094907692).isSome = true := by
  decide +kernel

theorem k2747_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2747) 2).1 3).1 2).1 3).2 1).2
      18229053647989044022625173268430899102908072045713931123337336828468710132961385782476471760808853732780).isSome = true := by
  decide +kernel

theorem k2747_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2747) 2).1 3).1 2).2 3).1 1).1
      248562936197243246568711596808899549805033428434620693090327913187754902536433655596).isSome = true := by
  decide +kernel

theorem k2747_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2747) 2).1 3).1 2).2 3).1 1).2
      215375025811580544946712835841294294889147264058896329544287373884).isSome = true := by
  decide +kernel

theorem k2747_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2747) 2).1 3).1 2).2 3).2 1).1
      247616380985679239156501718089489349231488599783638292829102543535008071672246263596).isSome = true := by
  decide +kernel

theorem k2747_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2747) 2).1 3).1 2).2 3).2 1).2
      247463694415929470319945391467621617392325269748958520043468744760085444202560322988).isSome = true := by
  decide +kernel

theorem k2747_8 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2747) 2).1 3).2 2).1 3).1
      4655306632374702850816984514252093871749208166417457195234374436075841331254026960227522130603455266255537).isSome = true := by
  decide +kernel

theorem k2747_9 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2747) 2).1 3).2 2).1 3).2
      21426828074620821694965847764848112126910538395609854587960580293385873609502880697398015068190404142607646246014602159414705).isSome = true := by
  decide +kernel

theorem k2747_10 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2747) 2).1 3).2 2).2 3).1
      343952038046505081808963065213330485590717501184712541625492004844094415900825667705859039111696012035794736216368781284727985).isSome = true := by
  decide +kernel

theorem k2747_11 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2747) 2).1 3).2 2).2 3).2
      1162633288013997954979019975245324806387182172218808177188143149674382498026594182447741389993420967206065).isSome = true := by
  decide +kernel

theorem k2747_12 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2747) 2).2 3).1 3).1 2).1 1).1
      13505570649064328780740613388424940436447921913626735896507808940).isSome = true := by
  decide +kernel

theorem k2747_13 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2747) 2).2 3).1 3).1 2).1 1).2
      53980717614689947638544975500586196681809944818154784962524869180).isSome = true := by
  decide +kernel

theorem k2747_14 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2747) 2).2 3).1 3).1 2).2 1).1
      54147592476407491475244178471011092905856828324853748362834735788).isSome = true := by
  decide +kernel

theorem k2747_15 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2747) 2).2 3).1 3).1 2).2 1).2
      11732895281153434428861825494839877058368500284).isSome = true := by
  decide +kernel

theorem k2747_16 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2747) 2).2 3).1 3).2 2).1
      5660152186636134522063564445437442214991748201978590108759216196328290693011975600499261649356459793064104469015678064269298364657).isSome = true := by
  decide +kernel

theorem k2747_17 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2747) 2).2 3).1 3).2 2).2
      1418042936605670911450029022937632210262573192146310229293731785944639955353193500052349969241919248565718847568034916547706846385).isSome = true := by
  decide +kernel

theorem k2747_18 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2747) 2).2 3).2 2).1 3).1
      19108894053733091664611798805490298522608336393739446774009392747648969490686987072877947746754189269989191921).isSome = true := by
  decide +kernel

theorem k2747_19 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2747) 2).2 3).2 2).1 3).2
      1164103848341769675401651407872404836363358814885816591936978413105377561604478384510693948073804157705393).isSome = true := by
  decide +kernel

theorem k2747_20 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2747) 2).2 3).2 2).2 3).1
      5650945879658054944785887797487127095550509861637753527534809723011496408234549479479372567241673615887606653899146651535346626801).isSome = true := by
  decide +kernel

theorem k2747_21 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2747) 2).2 3).2 2).2 3).2
      16166037598277793667641864806735463522001963076087212281352185067390354431007925628989681).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 2747 2748 :=
  (Cover.one (box := dirCellBox) (n := 2747)
      (.split 2 (.split 3 (.split 2 (.split 3 (.split 1 (.leaf _ k2747_0) (.leaf _ k2747_1)) (.split 1 (.leaf _ k2747_2) (.leaf _ k2747_3))) (.split 3 (.split 1 (.leaf _ k2747_4) (.leaf _ k2747_5)) (.split 1 (.leaf _ k2747_6) (.leaf _ k2747_7)))) (.split 2 (.split 3 (.leaf _ k2747_8) (.leaf _ k2747_9)) (.split 3 (.leaf _ k2747_10) (.leaf _ k2747_11)))) (.split 3 (.split 3 (.split 2 (.split 1 (.leaf _ k2747_12) (.leaf _ k2747_13)) (.split 1 (.leaf _ k2747_14) (.leaf _ k2747_15))) (.split 2 (.leaf _ k2747_16) (.leaf _ k2747_17))) (.split 2 (.split 3 (.leaf _ k2747_18) (.leaf _ k2747_19)) (.split 3 (.leaf _ k2747_20) (.leaf _ k2747_21))))))

end C4.Cert.Dir059
