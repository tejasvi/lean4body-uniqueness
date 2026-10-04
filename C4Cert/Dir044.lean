module

public import C4Check

public section

/-! Cells `2439 ≤ n < 2441` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir044

theorem k2439_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2439) 3).1 3).1 2).1 2).1
      18676801662105065915562830102512983307939784180959142743221699519809328908266277759033484743962219182449).isSome = true := by
  decide +kernel

theorem k2439_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2439) 3).1 3).1 2).1 2).2
      15811676505070306176345995849350203451313905596449410801080745551525872468720759153).isSome = true := by
  decide +kernel

theorem k2439_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2439) 3).1 3).1 2).2
      22071235100426419819342050938080545745043345564443726582782709425038691886573236588761127177168111847409132374933507400381257).isSome = true := by
  decide +kernel

theorem k2439_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2439) 3).1 3).2 2).1 2).1
      18574051841342111847604245057546047109559999119482824222577554309887107158543638544487277138144682185073).isSome = true := by
  decide +kernel

theorem k2439_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2439) 3).1 3).2 2).1 2).2
      18582455456811830235041584536574805974838803831454667732244333176068592261816128837280629489560016988529).isSome = true := by
  decide +kernel

theorem k2439_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2439) 3).1 3).2 2).2 1).1
      3938646134604768578847692199080326255055602100733661932024895888420882300193824124).isSome = true := by
  decide +kernel

theorem k2439_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2439) 3).1 3).2 2).2 1).2
      4648476431011147763051605511790582373316372936974007398384169003946497226075344512499708449675252209138).isSome = true := by
  decide +kernel

theorem k2439_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2439) 3).2 2).1 3).1 1).1
      4625282867925335880011780278162048170125852362833930358310879658163946839937924143851389368751611860466).isSome = true := by
  decide +kernel

theorem k2439_8 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2439) 3).2 2).1 3).1 1).2
      1026586917733628626234178544213115126020267516467486073180186239993824218689668581790450).isSome = true := by
  decide +kernel

theorem k2439_9 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2439) 3).2 2).1 3).2 2).1
      63872856302609554115145428826838613037447999786993629112555775579874108891629414474993).isSome = true := by
  decide +kernel

theorem k2439_10 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2439) 3).2 2).1 3).2 2).2
      15976973457728466322329067759053336056145610828659418239136238924676225859395410270641).isSome = true := by
  decide +kernel

theorem k2439_11 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2439) 3).2 2).2 3).1 1).1
      15682795789458128808454217795355121236941054982425453744541108124373687538589088114).isSome = true := by
  decide +kernel

theorem k2439_12 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2439) 3).2 2).2 3).1 1).2
      16051899059390497860153240036403068225637791804575655390568775772447931394988457948412).isSome = true := by
  decide +kernel

theorem k2439_13 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2439) 3).2 2).2 3).2 1).1
      4610400693227146805146319145472910382316489667751740889911358263713894442613176291002463845554335340018).isSome = true := by
  decide +kernel

theorem k2439_14 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2439) 3).2 2).2 3).2 1).2
      1023355708451181629741919372272945569354281634501215587608553486508899587034893787960050).isSome = true := by
  decide +kernel

theorem k2440_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2440) 3).1 2).1 3).1 1).1
      15927160598319948109094031687887151971711090091929768650283586401580629042577381616050).isSome = true := by
  decide +kernel

theorem k2440_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2440) 3).1 2).1 3).1 1).2
      63693266998604998424215384689335446070021730588401027172927377925692538888622982407858).isSome = true := by
  decide +kernel

theorem k2440_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2440) 3).1 2).1 3).2 2).1
      74929135784426677694813090197349744781376381286830881457782772553580214491608678221240643816846716154453425).isSome = true := by
  decide +kernel

theorem k2440_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2440) 3).1 2).1 3).2 2).2
      15877450395832300401785782437808052676789561830772454354289218560022587983153209448881).isSome = true := by
  decide +kernel

theorem k2440_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2440) 3).1 2).2 3).1 1).1
      63744283545753103116233190755288098851000553223147708411275083031462411401929361679601).isSome = true := by
  decide +kernel

theorem k2440_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2440) 3).1 2).2 3).1 1).2
      15936387194242558710191926155879825080652845119375562241023374250575719950505331808690).isSome = true := by
  decide +kernel

theorem k2440_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2440) 3).1 2).2 3).2 1).1
      15891498501982799602984637908675165201234482912625752999544931337088862891327314942780).isSome = true := by
  decide +kernel

theorem k2440_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2440) 3).1 2).2 3).2 1).2
      3972638536281813275190678480830296677787583808305394754501728434655706601646782798258).isSome = true := by
  decide +kernel

theorem k2440_8 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2440) 3).2 2).1 3).1 1).1
      1013804101915288997675322571770237672953439831018646692382576516844819150286984525476530).isSome = true := by
  decide +kernel

theorem k2440_9 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2440) 3).2 2).1 3).1 1).2
      299176866498624946042040258818534315313787669877783667575557496174497394046422931196432114490793405028213426).isSome = true := by
  decide +kernel

theorem k2440_10 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2440) 3).2 2).1 3).2 1).1
      16194228410841347943829548337119165060423373701334038311325340025019256321287742065835186).isSome = true := by
  decide +kernel

theorem k2440_11 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2440) 3).2 2).1 3).2 1).2
      64768726575753103421070533638305540180443074403116009212942414285897271005934939695316146).isSome = true := by
  decide +kernel

theorem k2440_12 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2440) 3).2 2).2 3).1 1).1
      3436759673428130641511610761777829335481842624371209448976914656492).isSome = true := by
  decide +kernel

theorem k2440_13 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2440) 3).2 2).2 3).1 1).2
      15851029000340024516094461570655511410828134754010964239620992421887684900376758348210).isSome = true := by
  decide +kernel

theorem k2440_14 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2440) 3).2 2).2 3).2 1).1
      13720590364077593353923633139283081468008328998098448053880125289138).isSome = true := by
  decide +kernel

theorem k2440_15 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2440) 3).2 2).2 3).2 1).2
      252989099686841105682171743542497988821115979652644248828759321469177084814578212133436).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 2439 2441 :=
  (Cover.one (box := dirCellBox) (n := 2439)
      (.split 3 (.split 3 (.split 2 (.split 2 (.leaf _ k2439_0) (.leaf _ k2439_1)) (.leaf _ k2439_2)) (.split 2 (.split 2 (.leaf _ k2439_3) (.leaf _ k2439_4)) (.split 1 (.leaf _ k2439_5) (.leaf _ k2439_6)))) (.split 2 (.split 3 (.split 1 (.leaf _ k2439_7) (.leaf _ k2439_8)) (.split 2 (.leaf _ k2439_9) (.leaf _ k2439_10))) (.split 3 (.split 1 (.leaf _ k2439_11) (.leaf _ k2439_12)) (.split 1 (.leaf _ k2439_13) (.leaf _ k2439_14)))))).trans <|
  (Cover.one (box := dirCellBox) (n := 2440)
      (.split 3 (.split 2 (.split 3 (.split 1 (.leaf _ k2440_0) (.leaf _ k2440_1)) (.split 2 (.leaf _ k2440_2) (.leaf _ k2440_3))) (.split 3 (.split 1 (.leaf _ k2440_4) (.leaf _ k2440_5)) (.split 1 (.leaf _ k2440_6) (.leaf _ k2440_7)))) (.split 2 (.split 3 (.split 1 (.leaf _ k2440_8) (.leaf _ k2440_9)) (.split 1 (.leaf _ k2440_10) (.leaf _ k2440_11))) (.split 3 (.split 1 (.leaf _ k2440_12) (.leaf _ k2440_13)) (.split 1 (.leaf _ k2440_14) (.leaf _ k2440_15))))))

end C4.Cert.Dir044
