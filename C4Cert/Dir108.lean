module

public import C4Check

public section

/-! Cells `3559 ≤ n < 3560` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir108

theorem k3559_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3559) 2).1 3).1 2).1 3).1 2).1
      75289303901813412741583014460059760815083106908863592761874896726983251138746143424466951888391039979453617).isSome = true := by
  decide +kernel

theorem k3559_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3559) 2).1 3).1 2).1 3).1 2).2
      301429337485081597103020732118760504657691173932489427278726935016693476568716083497194061005586944306543793).isSome = true := by
  decide +kernel

theorem k3559_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3559) 2).1 3).1 2).1 3).2 2).1
      74937020549581414688334109820907256878861413668075365922206924332680730956389982331304584213021295691297457).isSome = true := by
  decide +kernel

theorem k3559_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3559) 2).1 3).1 2).1 3).2 2).2
      75022642427274351004465871012994807831404925356177926353367032692466293183645968573480587950722194773474481).isSome = true := by
  decide +kernel

theorem k3559_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3559) 2).1 3).1 2).2 3).1 2).1
      301820984686130145899856308208785412400111069547205789016167777828329379230184747904776885601182065494686897).isSome = true := by
  decide +kernel

theorem k3559_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3559) 2).1 3).1 2).2 3).1 2).2
      1208192441221505373291595297008034746305718814025269174923732833301078885260154208817243340676748577076772017).isSome = true := by
  decide +kernel

theorem k3559_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3559) 2).1 3).1 2).2 3).2 2).1
      75093638432774231120051530753743764750158506347987022673692189788134380755919534642906796176208728191237297).isSome = true := by
  decide +kernel

theorem k3559_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3559) 2).1 3).1 2).2 3).2 2).2
      75163114777476265173237130452120002133929907919005755013910700223025858511115339497666402925374791963212977).isSome = true := by
  decide +kernel

theorem k3559_8 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3559) 2).1 3).2 2).1 3).1 1).1
      344787907165033183499304139395988350382675984071939608874048384860236675789208717389971491926185953094230556532056011493992113).isSome = true := by
  decide +kernel

theorem k3559_9 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3559) 2).1 3).2 2).1 3).1 1).2
      247282237132202088409725634947051130893761187831798346273583210632456385047850710386).isSome = true := by
  decide +kernel

theorem k3559_10 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3559) 2).1 3).2 2).1 3).2 1).1
      4659052107049510431749027402451217952309814475337175407886343011923182333482502020285214327293204594728369).isSome = true := by
  decide +kernel

theorem k3559_11 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3559) 2).1 3).2 2).1 3).2 1).2
      15416740827481864498650111209118856824330642884785005172507723639242159356853814642).isSome = true := by
  decide +kernel

theorem k3559_12 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3559) 2).1 3).2 2).2 3).1 1).1
      306874565540863086616829090558409187355799323300813275986836816326318371617985420016440661813879056946038203078).isSome = true := by
  decide +kernel

theorem k3559_13 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3559) 2).1 3).2 2).2 3).1 1).2
      63415087620025867308478042504402849440670840222568009149174250904965185037573952920754).isSome = true := by
  decide +kernel

theorem k3559_14 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3559) 2).1 3).2 2).2 3).2 1).1
      4666692280638399320743783163725016810968300852059078582815918965502550659454634561580920640548888529755570).isSome = true := by
  decide +kernel

theorem k3559_15 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3559) 2).1 3).2 2).2 3).2 1).2
      856633932743832026565570463641111668808131288253493823764279169714).isSome = true := by
  decide +kernel

theorem k3559_16 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3559) 2).2 3).1 2).1 3).1 2).1
      16394843211362865572108062465382056215587459824348462645819793481197845773977463480201009).isSome = true := by
  decide +kernel

theorem k3559_17 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3559) 2).2 3).1 2).1 3).1 2).2
      1025630761312381757324474292694751902109350019908564696489454820487088312688871213210417).isSome = true := by
  decide +kernel

theorem k3559_18 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3559) 2).2 3).1 2).1 3).2 1).1
      1205572915387069955153511805753057729624450090103382056949615838937873327124847647485136409737277479740603570).isSome = true := by
  decide +kernel

theorem k3559_19 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3559) 2).2 3).1 2).1 3).2 1).2
      63777664262760106900928392719923126939990561618150223811699729256959022002643818208434).isSome = true := by
  decide +kernel

theorem k3559_20 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3559) 2).2 3).1 2).2 3).1 1).1
      1028260136580078624162246395623989330376707522143625487408813712599523996736696181955378).isSome = true := by
  decide +kernel

theorem k3559_21 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3559) 2).2 3).1 2).2 3).1 1).2
      1027360097175983545848576505364363985356472569678958135875480201976392443907915637693234).isSome = true := by
  decide +kernel

theorem k3559_22 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3559) 2).2 3).1 2).2 3).2 1).1
      1022798464577557796177337314220944976719983404910688482372663590898674959747794801367858).isSome = true := by
  decide +kernel

theorem k3559_23 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3559) 2).2 3).1 2).2 3).2 1).2
      63876456741753822985490257410304372895428030656428226152939675365198838309599016409906).isSome = true := by
  decide +kernel

theorem k3559_24 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3559) 2).2 3).2 2).1 3).1 1).1
      76813657796532466942763518197425329718951202098860956828898827381166120632440992594115312058539903555955424433).isSome = true := by
  decide +kernel

theorem k3559_25 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3559) 2).2 3).2 2).1 3).1 1).2
      63514046636990510849643068003494999075907934664175207756854946464324667999309451844786).isSome = true := by
  decide +kernel

theorem k3559_26 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3559) 2).2 3).2 2).1 3).2 1).1
      1013390563434789239093622620848629729685171799075141066301392597316109055384265721739442).isSome = true := by
  decide +kernel

theorem k3559_27 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3559) 2).2 3).2 2).1 3).2 1).2
      3955287782829325939451320456824599450231782355625367859719680647788938152206056944300).isSome = true := by
  decide +kernel

theorem k3559_28 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3559) 2).2 3).2 2).2 3).1 1).1
      63630800466407239061374755493013370667214890563305463822155534817689365236269851717420).isSome = true := by
  decide +kernel

theorem k3559_29 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3559) 2).2 3).2 2).2 3).1 1).2
      15901806342685976238532796925610548884042240687420372267462037039550222907821636672690).isSome = true := by
  decide +kernel

theorem k3559_30 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3559) 2).2 3).2 2).2 3).2 1).1
      3962802385469804660434832481874917387802369444365050791811173918409684684747335757612).isSome = true := by
  decide +kernel

theorem k3559_31 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3559) 2).2 3).2 2).2 3).2 1).2
      214699322096937115177962406466880904933859034022723944994042133676).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 3559 3560 :=
  (Cover.one (box := dirCellBox) (n := 3559)
      (.split 2 (.split 3 (.split 2 (.split 3 (.split 2 (.leaf _ k3559_0) (.leaf _ k3559_1)) (.split 2 (.leaf _ k3559_2) (.leaf _ k3559_3))) (.split 3 (.split 2 (.leaf _ k3559_4) (.leaf _ k3559_5)) (.split 2 (.leaf _ k3559_6) (.leaf _ k3559_7)))) (.split 2 (.split 3 (.split 1 (.leaf _ k3559_8) (.leaf _ k3559_9)) (.split 1 (.leaf _ k3559_10) (.leaf _ k3559_11))) (.split 3 (.split 1 (.leaf _ k3559_12) (.leaf _ k3559_13)) (.split 1 (.leaf _ k3559_14) (.leaf _ k3559_15))))) (.split 3 (.split 2 (.split 3 (.split 2 (.leaf _ k3559_16) (.leaf _ k3559_17)) (.split 1 (.leaf _ k3559_18) (.leaf _ k3559_19))) (.split 3 (.split 1 (.leaf _ k3559_20) (.leaf _ k3559_21)) (.split 1 (.leaf _ k3559_22) (.leaf _ k3559_23)))) (.split 2 (.split 3 (.split 1 (.leaf _ k3559_24) (.leaf _ k3559_25)) (.split 1 (.leaf _ k3559_26) (.leaf _ k3559_27))) (.split 3 (.split 1 (.leaf _ k3559_28) (.leaf _ k3559_29)) (.split 1 (.leaf _ k3559_30) (.leaf _ k3559_31)))))))

end C4.Cert.Dir108
