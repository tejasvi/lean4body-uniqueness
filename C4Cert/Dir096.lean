module

public import C4Check

public section

/-! Cells `3222 ≤ n < 3224` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir096

theorem k3222_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3222) 3).1 3).1
      632370888868863576397933678240026970520235964399312782974080070).isSome = true := by
  decide +kernel

theorem k3222_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3222) 3).1 3).2
      89937879857857733096210167654392283149873919538131503627465587275256982298945834694078154874117512362357295147362604842644934).isSome = true := by
  decide +kernel

theorem k3222_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3222) 3).2 2).1 3).1
      22294606728448445544353306191200128709472051022306811297273996678467785871857728340849095750308342588825168559327933202908617).isSome = true := by
  decide +kernel

theorem k3222_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3222) 3).2 2).1 3).2
      354098626764345053857870025498054713282695791018466013436231300591236758870491364376804623242079840651946555065094734138668273).isSome = true := by
  decide +kernel

theorem k3222_4 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3222) 3).2 2).2
      1928652658821115070588833864778102024591169267432442272119261025007784177498784502771253120339958572123244796661132792044268600423662969167028865845624037530231014855).isSome = true := by
  decide +kernel

theorem k3223_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3223) 3).1 2).1 2).1
      1400765837470999449280260069995284186602206840105766564626617937151035041774576999644498090741868361601204112171233695436731635).isSome = true := by
  decide +kernel

theorem k3223_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3223) 3).1 2).1 2).2
      1189507260721442616388383334016279090937156924507206689587425370611324996477291191331841887639046095461809).isSome = true := by
  decide +kernel

theorem k3223_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3223) 3).1 2).2 3).1
      352179643465102927955137204394581785355718365620738422760272914775759337159473516053843650095261190272308610478487073990735089).isSome = true := by
  decide +kernel

theorem k3223_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3223) 3).1 2).2 3).2
      87610809862095366482074402567081772033172549493884148896873503337536302437655859487664335525330666339313471368988241684165873).isSome = true := by
  decide +kernel

theorem k3223_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3223) 3).2 2).1 2).1
      1425062459482400627584907169783285009244677670304817771873490740249156434063578405142027734627129597961057041681248635689050583868).isSome = true := by
  decide +kernel

theorem k3223_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3223) 3).2 2).1 2).2
      19319157703236929774658947878118121927130394526853795412710752364489397665076409623747967386884565100238850289).isSome = true := by
  decide +kernel

theorem k3223_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3223) 3).2 2).2 2).1
      255795827097069239255942480430444282435605542398450625757777842564825118900656065835697).isSome = true := by
  decide +kernel

theorem k3223_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3223) 3).2 2).2 2).2
      63998674684156217059138137116294272276890741201000877815859448354201711733014145782588).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 3222 3224 :=
  (Cover.one (box := dirCellBox) (n := 3222)
      (.split 3 (.split 3 (.leaf _ k3222_0) (.leaf _ k3222_1)) (.split 2 (.split 3 (.leaf _ k3222_2) (.leaf _ k3222_3)) (.leaf _ k3222_4)))).trans <|
  (Cover.one (box := dirCellBox) (n := 3223)
      (.split 3 (.split 2 (.split 2 (.leaf _ k3223_0) (.leaf _ k3223_1)) (.split 3 (.leaf _ k3223_2) (.leaf _ k3223_3))) (.split 2 (.split 2 (.leaf _ k3223_4) (.leaf _ k3223_5)) (.split 2 (.leaf _ k3223_6) (.leaf _ k3223_7)))))

end C4.Cert.Dir096
