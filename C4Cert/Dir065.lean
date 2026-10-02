module

public import C4Check

public section

/-! Cells `2777 ≤ n < 2780` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir065

theorem k2777_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2777) 2).1 3).1 3).1 1).1
      245087005472367601843300553835834641478376955461834019140845195912199841465146761004).isSome = true := by
  decide +kernel

theorem k2777_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2777) 2).1 3).1 3).1 1).2
      61267950724586022686338496229407896067663231973300176608748847143725116950872219500).isSome = true := by
  decide +kernel

theorem k2777_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2777) 2).1 3).1 3).2
      21836976231007866825746473405163774432275738091933069085985859925682069861513665815094672148821843091595178283052835424467776754).isSome = true := by
  decide +kernel

theorem k2777_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2777) 2).1 3).2 1).1
      62561890689506298152448997579746994172823979169329296662855023305483998592982555778227).isSome = true := by
  decide +kernel

theorem k2777_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2777) 2).1 3).2 1).2
      85208610563321289988985925817578296467031467649521049321619318368044925468194905530765879332047649009804824769478180071634162).isSome = true := by
  decide +kernel

theorem k2777_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2777) 2).2 3).1 3).1
      1400764830245970890503294635695862757897713932158835509784519746497700428859611614566188383295149797380311520099404412296128086844).isSome = true := by
  decide +kernel

theorem k2777_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2777) 2).2 3).1 3).2
      6453029486638650363386277985657829950452836089555671718783518348727357525120684078026645997280933677976673907859529242653183910681710990457376326460).isSome = true := by
  decide +kernel

theorem k2777_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2777) 2).2 3).2 3).1
      16037749286097014361565226602709461234943314504900420337283508117590771103541803964854513).isSome = true := by
  decide +kernel

theorem k2777_8 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2777) 2).2 3).2 3).2
      250372745933701133918133835993819218364801672004535895600754339187884431009810667892977).isSome = true := by
  decide +kernel

theorem k2778_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2778) 2).1 3).1 1).1
      18021339588819498478438017504384876651158704542782793069535406371741997455701680009444167519709158280562).isSome = true := by
  decide +kernel

theorem k2778_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2778) 2).1 3).1 1).2
      4504971205780424467256624584799104471459961222392243076511964933618941481826822472230498868368765878642).isSome = true := by
  decide +kernel

theorem k2778_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2778) 2).1 3).2
      25086423753249660532420306039320287102733322261319022440345769922331475643398458379531417875096525767371696402308789835576813787522954686414800329).isSome = true := by
  decide +kernel

theorem k2778_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2778) 2).2 3).1 1).1
      3909083033865337639283197097375475570507200494415414113492590122962927998717245387324).isSome = true := by
  decide +kernel

theorem k2778_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2778) 2).2 3).1 1).2
      288427514366667933414339754487169531881144395537003577613054826167536518768865850569312530630633896530748).isSome = true := by
  decide +kernel

theorem k2778_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2778) 2).2 3).2 1).1
      15617607411182688740481677302957354938706487633775710516888196433920275337506392097708).isSome = true := by
  decide +kernel

theorem k2778_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2778) 2).2 3).2 1).2
      18007910096021770948435559278890128757866491818349230787243676799332475135469359631323587105552200021362).isSome = true := by
  decide +kernel

theorem k2779_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2779) 2).1 3).1
      21234321397623173874100072748880686847492904730567037837184905335869759015743367849311200816950837439000419002294287127428425).isSome = true := by
  decide +kernel

theorem k2779_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2779) 2).1 3).2
      15225380010772810266501591959863668263624794799591364157268213097481510221425273201).isSome = true := by
  decide +kernel

theorem k2779_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2779) 2).2 3).1
      84957029029675537586733162462223643373271328204530590864702084360219607758596114059592480703306700471679746409273808097533361).isSome = true := by
  decide +kernel

theorem k2779_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2779) 2).2 3).2
      21226308566280701006609490388987417277316106534479349726950745135596258169313448891671555161638795971534555672187472585186737).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 2777 2780 :=
  (Cover.one (box := dirCellBox) (n := 2777)
      (.split 2 (.split 3 (.split 3 (.split 1 (.leaf _ k2777_0) (.leaf _ k2777_1)) (.leaf _ k2777_2)) (.split 1 (.leaf _ k2777_3) (.leaf _ k2777_4))) (.split 3 (.split 3 (.leaf _ k2777_5) (.leaf _ k2777_6)) (.split 3 (.leaf _ k2777_7) (.leaf _ k2777_8))))).trans <|
  (Cover.one (box := dirCellBox) (n := 2778)
      (.split 2 (.split 3 (.split 1 (.leaf _ k2778_0) (.leaf _ k2778_1)) (.leaf _ k2778_2)) (.split 3 (.split 1 (.leaf _ k2778_3) (.leaf _ k2778_4)) (.split 1 (.leaf _ k2778_5) (.leaf _ k2778_6))))).trans <|
  (Cover.one (box := dirCellBox) (n := 2779)
      (.split 2 (.split 3 (.leaf _ k2779_0) (.leaf _ k2779_1)) (.split 3 (.leaf _ k2779_2) (.leaf _ k2779_3))))

end C4.Cert.Dir065
