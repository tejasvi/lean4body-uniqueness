module

public import C4Check

public section

/-! Cells `3139 ≤ n < 3140` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir085

theorem k3139_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3139) 2).1 3).1 2).1 3).1 1).1
      73100107723436376794414138293151239267050422064308522318644790398613228059594150968824427002842960090940).isSome = true := by
  decide +kernel

theorem k3139_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3139) 2).1 3).1 2).1 3).1 1).2
      15832125912609054657626988734806150891888741906952614952133384898063993395421090271985).isSome = true := by
  decide +kernel

theorem k3139_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3139) 2).1 3).1 2).1 3).2
      1623576482758433818293140245599473990647557482783001250359167683214776148314773683952495227335995181072845576632283561340710617799180809756811326705).isSome = true := by
  decide +kernel

theorem k3139_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3139) 2).1 3).1 2).2 3).1 1).1
      860907505218540396279222386120011092768246523624427141106061232956).isSome = true := by
  decide +kernel

theorem k3139_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3139) 2).1 3).1 2).2 3).1 1).2
      73200929916287155715186874909957187940457760174848878168391946062540623074652862801452283878448469366588).isSome = true := by
  decide +kernel

theorem k3139_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3139) 2).1 3).1 2).2 3).2 1).1
      15822673449784227960907195722421143878663122228093616730093610514408308228428253842236).isSome = true := by
  decide +kernel

theorem k3139_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3139) 2).1 3).1 2).2 3).2 1).2
      209284186583689418302516496529829980813374888408370610251914556).isSome = true := by
  decide +kernel

theorem k3139_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3139) 2).1 3).2 2).1 3).1
      6330189749990885288254746965543561832610728050901986699190370996959233289344462070158122269781462491772688519714541395078032330237349645149631729).isSome = true := by
  decide +kernel

theorem k3139_8 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3139) 2).1 3).2 2).1 3).2
      6318890114572425041711591185356110985715993109234407183860217515529607829696483790767301671705898261464482450750668540879992070835984253312398577).isSome = true := by
  decide +kernel

theorem k3139_9 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3139) 2).1 3).2 2).2 3).1
      343436314644107162839722716432232807093213724937964494581044730173184866559444407805504626141994789372400069018463417759790321).isSome = true := by
  decide +kernel

theorem k3139_10 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3139) 2).1 3).2 2).2 3).2
      1370891711700159169642902860286561379199861921278454999059605054675237047549587204631272852066939944196172741264475697874564337).isSome = true := by
  decide +kernel

theorem k3139_11 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3139) 2).2 3).1 2).1 3).1 1).1
      215765488610177951537093999149306270919406957632338792846089245500).isSome = true := by
  decide +kernel

theorem k3139_12 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3139) 2).2 3).1 2).1 3).1 1).2
      994333887971965328320691417151396785398176870982661569031186714364344813405824480828).isSome = true := by
  decide +kernel

theorem k3139_13 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3139) 2).2 3).1 2).1 3).2
      88334560612867245332789077952268120345410502191332987894968565892622461805686620929901376359452907121887315770240572441794959601).isSome = true := by
  decide +kernel

theorem k3139_14 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3139) 2).2 3).1 2).2 3).1 1).1
      54082980233099627890525460901128112576581925208017972574852347452).isSome = true := by
  decide +kernel

theorem k3139_15 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3139) 2).2 3).1 2).2 3).1 1).2
      996722454427855459743249812529757718112606113311234304455657299627182521613552055868).isSome = true := by
  decide +kernel

theorem k3139_16 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3139) 2).2 3).1 2).2 3).2
      22130288456963047991632352622261187883696130595082850091507097353423586383936439043837502955989402897491921990147477948545358065).isSome = true := by
  decide +kernel

theorem k3139_17 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3139) 2).2 3).2 2).1 3).1
      343957270949280730075313135842146038255371151038228192843721981967473095127970942880384792221557876475118729513661742322382065).isSome = true := by
  decide +kernel

theorem k3139_18 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3139) 2).2 3).2 2).1 3).2
      18599888830799097950584184260628354334713958011412998536093514096960082714238732333506985140345342486666673).isSome = true := by
  decide +kernel

theorem k3139_19 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3139) 2).2 3).2 2).2 3).1
      74711624669785527913298586560704997400802134015820810062073576229619748529180020757689466658981256821372145).isSome = true := by
  decide +kernel

theorem k3139_20 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3139) 2).2 3).2 2).2 3).2
      16154834407960019574393255815270735271831691206649898002077609632874501423060724826141937).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 3139 3140 :=
  (Cover.one (box := dirCellBox) (n := 3139)
      (.split 2 (.split 3 (.split 2 (.split 3 (.split 1 (.leaf _ k3139_0) (.leaf _ k3139_1)) (.leaf _ k3139_2)) (.split 3 (.split 1 (.leaf _ k3139_3) (.leaf _ k3139_4)) (.split 1 (.leaf _ k3139_5) (.leaf _ k3139_6)))) (.split 2 (.split 3 (.leaf _ k3139_7) (.leaf _ k3139_8)) (.split 3 (.leaf _ k3139_9) (.leaf _ k3139_10)))) (.split 3 (.split 2 (.split 3 (.split 1 (.leaf _ k3139_11) (.leaf _ k3139_12)) (.leaf _ k3139_13)) (.split 3 (.split 1 (.leaf _ k3139_14) (.leaf _ k3139_15)) (.leaf _ k3139_16))) (.split 2 (.split 3 (.leaf _ k3139_17) (.leaf _ k3139_18)) (.split 3 (.leaf _ k3139_19) (.leaf _ k3139_20))))))

end C4.Cert.Dir085
