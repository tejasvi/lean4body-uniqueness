module

public import C4Check

public section

/-! Cells `2382 ≤ n < 2383` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir037

theorem k2382_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2382) 3).1 2).1 3).1
      5940905158851634131835603870317749737701218308211947648545974227240988608835718788922731404302272723838664869573371906452797211078).isSome = true := by
  decide +kernel

theorem k2382_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2382) 3).1 2).1 3).2 2).1
      5712364628546324110517362183501661075638637829905085085408106860540308238782674571771698503724699206925227923256190456782234695).isSome = true := by
  decide +kernel

theorem k2382_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2382) 3).1 2).1 3).2 2).2
      19402788159203825510075617394004526905557385337580373111680842547488872082824289155430311187110298064341773).isSome = true := by
  decide +kernel

theorem k2382_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2382) 3).1 2).2 3).1
      19726668078583146501481746922981350391265095836716111804481945638849505801199525806182514101523677768791110).isSome = true := by
  decide +kernel

theorem k2382_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2382) 3).1 2).2 3).2
      1698163075630129447094392814239000052967083297266414814875342298006639549143001669524857870434689750795121281057936910120635881876954447758641974797).isSome = true := by
  decide +kernel

theorem k2382_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2382) 3).2 2).1 3).1 2).1 3).1
      18819473314134644373007232950282468404911701491807164305228166051214832927298450997713226438568886949329).isSome = true := by
  decide +kernel

theorem k2382_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2382) 3).2 2).1 3).1 2).1 3).2
      1198879144136664368683896850825538087792065330643695105233374684340502819014545186488045908924169981852933).isSome = true := by
  decide +kernel

theorem k2382_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2382) 3).2 2).1 3).1 2).2 3).1
      63861167088391708570704398242598383366902445504928768048447635253467004012049415441).isSome = true := by
  decide +kernel

theorem k2382_8 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2382) 3).2 2).1 3).1 2).2 3).2
      18775047412060876429946466035065772145882201070912305051974696136914823014072616036200610204693844427153).isSome = true := by
  decide +kernel

theorem k2382_9 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2382) 3).2 2).1 3).2 2).1 3).1
      4770832980059342828254072865114067472209361943389274923747982752256763096174810601197106743698759076034821).isSome = true := by
  decide +kernel

theorem k2382_10 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2382) 3).2 2).1 3).2 2).1 3).2
      1217068412930184468383382695111078371284860585782017954208892781332358892595897338143935069641575419415742025).isSome = true := by
  decide +kernel

theorem k2382_11 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2382) 3).2 2).1 3).2 2).2 3).1
      64900023494005502283490623495245676721487840521473662333732892312032904941613356052741).isSome = true := by
  decide +kernel

theorem k2382_12 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2382) 3).2 2).1 3).2 2).2 3).2
      4764888743876603786083494956336137172525782138415235898498767109451747763645519848656605816146095642336625).isSome = true := by
  decide +kernel

theorem k2382_13 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2382) 3).2 2).2 3).1 1).1
      47013929870082096037334196138499469629603078).isSome = true := by
  decide +kernel

theorem k2382_14 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2382) 3).2 2).2 3).1 1).2 2).1
      5561774065537090901946702023063464547615622500056743167265382336771163296915964936315334163902191843176522519684266838065229).isSome = true := by
  decide +kernel

theorem k2382_15 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2382) 3).2 2).2 3).1 1).2 2).2
      4708647396488907508934966180714858780991872296038157497383952143671751294721170515654389186287295511923).isSome = true := by
  decide +kernel

theorem k2382_16 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2382) 3).2 2).2 3).2 2).1 1).1
      53652118252830132013474552998480329594612735970864851763605201).isSome = true := by
  decide +kernel

theorem k2382_17 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2382) 3).2 2).2 3).2 2).1 1).2
      76390506550307023931399954449350800803686702832893780417491235410282660431739168083017409183380354096539123).isSome = true := by
  decide +kernel

theorem k2382_18 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2382) 3).2 2).2 3).2 2).2
      30747091761113524900501198894635546285751572846078985868675234740374019541009359537683322523857172589003947888207695910914660830713676538063289347962609895449371321933).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 2382 2383 :=
  (Cover.one (box := dirCellBox) (n := 2382)
      (.split 3 (.split 2 (.split 3 (.leaf _ k2382_0) (.split 2 (.leaf _ k2382_1) (.leaf _ k2382_2))) (.split 3 (.leaf _ k2382_3) (.leaf _ k2382_4))) (.split 2 (.split 3 (.split 2 (.split 3 (.leaf _ k2382_5) (.leaf _ k2382_6)) (.split 3 (.leaf _ k2382_7) (.leaf _ k2382_8))) (.split 2 (.split 3 (.leaf _ k2382_9) (.leaf _ k2382_10)) (.split 3 (.leaf _ k2382_11) (.leaf _ k2382_12)))) (.split 3 (.split 1 (.leaf _ k2382_13) (.split 2 (.leaf _ k2382_14) (.leaf _ k2382_15))) (.split 2 (.split 1 (.leaf _ k2382_16) (.leaf _ k2382_17)) (.leaf _ k2382_18))))))

end C4.Cert.Dir037
