module

public import C4Check

public section

/-! Cells `2860 ≤ n < 2864` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir073

theorem k2860_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2860) 3).1 2).1 1).1
      3979739278091653235768070753930197447845779567006233478404743465402300442798802327356).isSome = true := by
  decide +kernel

theorem k2860_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2860) 3).1 2).1 1).2
      3978225841109686100481473102774605743748955228860723962868080041528320429424849179452).isSome = true := by
  decide +kernel

theorem k2860_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2860) 3).1 2).2
      5680361016262170328125856110483579580093188902990698629985483758229620424922659059929021548876688919022856553938441484100147246321).isSome = true := by
  decide +kernel

theorem k2860_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2860) 3).2 2).1 1).1
      214643874790507165276625272301728207148063027128705794841178002236).isSome = true := by
  decide +kernel

theorem k2860_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2860) 3).2 2).1 1).2
      214623327188353688790650872434550931674361755842491489588257093180).isSome = true := by
  decide +kernel

theorem k2860_5 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2860) 3).2 2).2
      6518703984530634876920444879087286020654835019505111018566836809114639170371427649330345986667537721497429962072546662335975236812214608202504277820).isSome = true := by
  decide +kernel

theorem k2861_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2861) 3).1 2).1
      19525183619233511701606622958730567012133233148032242013774270780122673160128438325162084346660525057929197341937).isSome = true := by
  decide +kernel

theorem k2861_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2861) 3).1 2).2
      19083413055424999557384326799254115748900986750511443500163399427606317049877106805361000152489432843623936828).isSome = true := by
  decide +kernel

theorem k2861_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2861) 3).2 2).1
      4221521659015163715736101864687775646319597717967074619522117170352086137656517337806758463729).isSome = true := by
  decide +kernel

theorem k2861_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2861) 3).2 2).2
      19028026267704675568274879227602936323108013257257039467659253254087061628680992253193206832426397432398295868).isSome = true := by
  decide +kernel

theorem k2862_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2862) 3).1 2).1
      4113322108295820044026298287092480711905662550639966833838533909715700656961603998822941500).isSome = true := by
  decide +kernel

theorem k2862_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2862) 3).1 2).2
      1186326711718476855933168083856969382335302723971956803571773762500718613795718979654141576325769408634889020).isSome = true := by
  decide +kernel

theorem k2862_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2862) 3).2 2).1
      295899181336755416016096212165093406186285520253481299679082397084884655962578874065731966590451963514911804).isSome = true := by
  decide +kernel

theorem k2862_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2862) 3).2 2).2
      1026979794041386790030863078902442136818344175688368650542410729586292554537994698655515452).isSome = true := by
  decide +kernel

theorem k2863_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2863) 3).1 2).1
      64056869773855828737935297397403449508354450880328403199355741051130138870734486093610044).isSome = true := by
  decide +kernel

theorem k2863_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2863) 3).1 2).2
      16021119481987661287129894319128627443779680397407822871429636574327058867234589103012924).isSome = true := by
  decide +kernel

theorem k2863_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2863) 3).2 2).1
      63981169092945418953932706862292357783409961576384424002282061244884060853322359778753596).isSome = true := by
  decide +kernel

theorem k2863_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2863) 3).2 2).2
      16002036849339896474428488779410134260128798834436072153232376561231308857798438365740092).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 2860 2864 :=
  (Cover.one (box := dirCellBox) (n := 2860)
      (.split 3 (.split 2 (.split 1 (.leaf _ k2860_0) (.leaf _ k2860_1)) (.leaf _ k2860_2)) (.split 2 (.split 1 (.leaf _ k2860_3) (.leaf _ k2860_4)) (.leaf _ k2860_5)))).trans <|
  (Cover.one (box := dirCellBox) (n := 2861)
      (.split 3 (.split 2 (.leaf _ k2861_0) (.leaf _ k2861_1)) (.split 2 (.leaf _ k2861_2) (.leaf _ k2861_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 2862)
      (.split 3 (.split 2 (.leaf _ k2862_0) (.leaf _ k2862_1)) (.split 2 (.leaf _ k2862_2) (.leaf _ k2862_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 2863)
      (.split 3 (.split 2 (.leaf _ k2863_0) (.leaf _ k2863_1)) (.split 2 (.leaf _ k2863_2) (.leaf _ k2863_3))))

end C4.Cert.Dir073
