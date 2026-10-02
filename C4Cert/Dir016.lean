module

public import C4Check

public section

/-! Cells `1665 ≤ n < 1713` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir016

theorem c0 : allCells dirCell 1665 1685 [
    2360564832656126759745, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    13424722841606593992274666241655648524578719210461775118644596835] = true := by
  decide +kernel

theorem k1685_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 1685) 3).1
      21490310774869875815072317152201692518116888029516089817922112079779730547950782733821687659725079342798197378906677685134150).isSome = true := by
  decide +kernel

theorem k1685_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1685) 3).2 2).1
      72564370269494199196918544514529704626318885368732947489238885875524272988656665127987713299252163173745).isSome = true := by
  decide +kernel

theorem k1685_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1685) 3).2 2).2
      15374050049692214644105704130378110602365373031795338039868100525243938202047684977).isSome = true := by
  decide +kernel

theorem k1686_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1686) 3).1 2).1
      18101038888904836848185352487370829504127230593846185520574616959170964988547012200143292689914077474161).isSome = true := by
  decide +kernel

theorem k1686_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1686) 3).1 2).2
      18106582209144310914189287285678805217099941324590415692449516502091148333155178303749705870942888907121).isSome = true := by
  decide +kernel

theorem k1686_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1686) 3).2 2).1
      62656873232818674594095853166869510711667467558848872101250488641664705495524043807921).isSome = true := by
  decide +kernel

theorem k1686_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1686) 3).2 2).2
      289139248877898890031597844263749825206941210892658787127086756086023832006646134693787198176926862136124).isSome = true := by
  decide +kernel

theorem k1687_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1687) 3).1 2).1
      977732764383848434094943396553039603321773573163748229277587826302094303923449723964).isSome = true := by
  decide +kernel

theorem k1687_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1687) 3).1 2).2
      3911584495817376199810829957160887971481971338349993993016640158269922069945857103665).isSome = true := by
  decide +kernel

theorem k1687_2 : (checkBoxH dirMode depth (splitBox (dirCellBox 1687) 3).2
      89197027023366830843501762726525855465462185959456164354990937306246621983905495243397036268171734940252618173153986913482803835122).isSome = true := by
  decide +kernel

theorem k1688_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 1688) 3).1
      87027516063616459358662511229278221552177701363963842648604436389657806161849639338353701824061006849895354696634197999382646578).isSome = true := by
  decide +kernel

theorem k1688_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 1688) 3).2
      18857389205990751155179116025453492370683317827798261554595479995937349839522334208024589044995629452850138930).isSome = true := by
  decide +kernel

theorem k1689_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 1689) 3).1
      75348554285606889848009634857683364499838993303898354968906419586334929241298262719913503356101986529203130162).isSome = true := by
  decide +kernel

theorem k1689_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 1689) 3).2
      75311059103829671937822231370207370467878471568023299243916086796098789930419721995559608235442184092816569138).isSome = true := by
  decide +kernel

theorem k1690_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 1690) 3).1
      3984627035980700149465384314058657997459605899920528418140002151876478878158940903666482).isSome = true := by
  decide +kernel

theorem k1690_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 1690) 3).2
      248939824156855005986746962160223066102071983270343470545104729841392390959502964044748).isSome = true := by
  decide +kernel

theorem k1691_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 1691) 3).1
      62213621202032847173893661504741567310185168056802958804508318335655970627705906091825).isSome = true := by
  decide +kernel

theorem k1691_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 1691) 3).2
      210725018778786503685150696129229060109837478593225330402851601468).isSome = true := by
  decide +kernel

theorem c8 : allCells dirCell 1692 1712 [
    338482158088516629626682155909928251025582545400177434671326548254918284654983513872094485051299255585394971096616230914489925,
    2360497955963295117633, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] = true := by
  decide +kernel

theorem c9 : allCells dirCell 1712 1713 [
    839415289449574184666793039935364676842078519530580950320486179] = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 1665 1713 :=
  (Cover.dir c0).trans <|
  (Cover.one (box := dirCellBox) (n := 1685)
      (.split 3 (.leaf _ k1685_0) (.split 2 (.leaf _ k1685_1) (.leaf _ k1685_2)))).trans <|
  (Cover.one (box := dirCellBox) (n := 1686)
      (.split 3 (.split 2 (.leaf _ k1686_0) (.leaf _ k1686_1)) (.split 2 (.leaf _ k1686_2) (.leaf _ k1686_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 1687)
      (.split 3 (.split 2 (.leaf _ k1687_0) (.leaf _ k1687_1)) (.leaf _ k1687_2))).trans <|
  (Cover.one (box := dirCellBox) (n := 1688)
      (.split 3 (.leaf _ k1688_0) (.leaf _ k1688_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 1689)
      (.split 3 (.leaf _ k1689_0) (.leaf _ k1689_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 1690)
      (.split 3 (.leaf _ k1690_0) (.leaf _ k1690_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 1691)
      (.split 3 (.leaf _ k1691_0) (.leaf _ k1691_1))).trans <|
  (Cover.dir c8).trans <|
  (Cover.dir c9)

end C4.Cert.Dir016
