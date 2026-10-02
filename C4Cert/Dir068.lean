module

public import C4Check

public section

/-! Cells `2804 ≤ n < 2806` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir068

theorem k2804_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2804) 3).1 3).1 2).1 2).1
      3964501652471481747733689967014622401833541721011243752503222086628443553887925293884).isSome = true := by
  decide +kernel

theorem k2804_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2804) 3).1 3).1 2).1 2).2
      860411640866604595015355280302805869238593835146284860457681933116).isSome = true := by
  decide +kernel

theorem k2804_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2804) 3).1 3).1 2).2 1).1
      53851706574412235109924697020796562371041543453023990380736411196).isSome = true := by
  decide +kernel

theorem k2804_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2804) 3).1 3).1 2).2 1).2
      215311627870813655780566246738010969235167331279047329673071022908).isSome = true := by
  decide +kernel

theorem k2804_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2804) 3).1 3).2 2).1
      4893883205295601094524237317116654514523105078824068756239513738604327472242230112346411562876879972916721600753).isSome = true := by
  decide +kernel

theorem k2804_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2804) 3).1 3).2 2).2 1).1
      53698250979341873897351637507088892354539196185694464554639423036).isSome = true := by
  decide +kernel

theorem k2804_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2804) 3).1 3).2 2).2 1).2
      53679979782866188497984752373042164849867316482311844322475374140).isSome = true := by
  decide +kernel

theorem k2804_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2804) 3).2 2).1 3).1
      1407529585760940908025584593192986409395217222161889931197272169152165285284828314470757434601684936675617068713102383451916857585).isSome = true := by
  decide +kernel

theorem k2804_8 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2804) 3).2 2).1 3).2
      1404875558373624409576237945514171223723520602927257929440852650549549757693673074918462398795501914330836608505253554316632256753).isSome = true := by
  decide +kernel

theorem k2804_9 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2804) 3).2 2).2 3).1
      88135520752513456913336807500310933471329422043509812657288754746069413469159292826170552655824030294309575045604083854785459004).isSome = true := by
  decide +kernel

theorem k2804_10 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2804) 3).2 2).2 3).2
      4767303515589018030238439750189747381869343773226742587087729429819062963353412430332621068009248277393253180).isSome = true := by
  decide +kernel

theorem k2805_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2805) 2).1 3).1 1).1
      1028971491605641772012909858937465697391592993164471491666358679136508125887940511208239347).isSome = true := by
  decide +kernel

theorem k2805_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2805) 2).1 3).1 1).2
      1187179444218469783627870953938408090505724725781040142807697661217601331922880553899458569139165449044881980).isSome = true := by
  decide +kernel

theorem k2805_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2805) 2).1 3).2 1).1
      1002683178160822491362548385135507992682097948290819881364064227336177254564886634404659).isSome = true := by
  decide +kernel

theorem k2805_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2805) 2).1 3).2 1).2
      1183414668435782151750775156079144133360881648185971886071847783158558944592240632489586819099990722580181235).isSome = true := by
  decide +kernel

theorem k2805_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2805) 2).2 3).1 1).1
      297218313068706442383031820573017764354633844573434104739735260292488655227371216880755719220473388059655228).isSome = true := by
  decide +kernel

theorem k2805_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2805) 2).2 3).1 1).2
      1006685556275134397507562219877833858469394348603766230289200071742392579705658909457468).isSome = true := by
  decide +kernel

theorem k2805_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2805) 2).2 3).2 1).1
      4016753910552606689890244653690617529148289291411985256323918792453304237318898431343676).isSome = true := by
  decide +kernel

theorem k2805_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2805) 2).2 3).2 1).2
      1003987992899081225039251509203317871892418845586900717547813872870916207985982551880252).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 2804 2806 :=
  (Cover.one (box := dirCellBox) (n := 2804)
      (.split 3 (.split 3 (.split 2 (.split 2 (.leaf _ k2804_0) (.leaf _ k2804_1)) (.split 1 (.leaf _ k2804_2) (.leaf _ k2804_3))) (.split 2 (.leaf _ k2804_4) (.split 1 (.leaf _ k2804_5) (.leaf _ k2804_6)))) (.split 2 (.split 3 (.leaf _ k2804_7) (.leaf _ k2804_8)) (.split 3 (.leaf _ k2804_9) (.leaf _ k2804_10))))).trans <|
  (Cover.one (box := dirCellBox) (n := 2805)
      (.split 2 (.split 3 (.split 1 (.leaf _ k2805_0) (.leaf _ k2805_1)) (.split 1 (.leaf _ k2805_2) (.leaf _ k2805_3))) (.split 3 (.split 1 (.leaf _ k2805_4) (.leaf _ k2805_5)) (.split 1 (.leaf _ k2805_6) (.leaf _ k2805_7)))))

end C4.Cert.Dir068
