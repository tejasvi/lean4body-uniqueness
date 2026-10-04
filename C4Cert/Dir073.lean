module

public import C4Check

public section

/-! Cells `2891 ≤ n < 2917` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir073

theorem k2891_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2891) 3).1 2).1 1).1
      4006502334827737659245714956208005764220107059469466673966772865560171558547709261298748).isSome = true := by
  decide +kernel

theorem k2891_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2891) 3).1 2).1 1).2
      4010114334732771235990959493027862058038194540474744045425814003558850264866719248727100).isSome = true := by
  decide +kernel

theorem k2891_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2891) 3).1 2).2 1).1
      3394554533203298694497005945854220104635545272650004699279737535548).isSome = true := by
  decide +kernel

theorem k2891_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2891) 3).1 2).2 1).2
      1001908441549169511146041338132731706215176145124472952880535900646614891190627979803708).isSome = true := by
  decide +kernel

theorem k2891_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2891) 3).2 2).1 1).1
      54225589331164725283278823017532688045586299939226854245252086293452).isSome = true := by
  decide +kernel

theorem k2891_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2891) 3).2 2).1 1).2
      867591904434077715602618958621165840744094923691900140516825105120316).isSome = true := by
  decide +kernel

theorem k2891_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2891) 3).2 2).2 1).1
      848459460885508294568444849698551573142350442273905313560881740860).isSome = true := by
  decide +kernel

theorem k2891_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2891) 3).2 2).2 1).2
      3390184780615855911449606710092035003107958160522728011090041191484).isSome = true := by
  decide +kernel

theorem k2892_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2892) 3).1 2).1 1).1
      846467417549487183052740630895567661237366384422320628306024555468).isSome = true := by
  decide +kernel

theorem k2892_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2892) 3).1 2).1 1).2
      11745653781763882135157249980277597377228582894652).isSome = true := by
  decide +kernel

theorem k2892_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2892) 3).1 2).2 1).1
      846662784102577269837053054110194062660240129040941156057074328524).isSome = true := by
  decide +kernel

theorem k2892_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2892) 3).1 2).2 1).2
      734319177284906010583329746894479363520825867324).isSome = true := by
  decide +kernel

theorem k2892_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2892) 3).2 2).1 1).1
      845744686571398637770010098635539897741848096707876315024274187212).isSome = true := by
  decide +kernel

theorem k2892_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2892) 3).2 2).1 1).2
      3382731803534210570564359147162157509893193075056275372393370938428).isSome = true := by
  decide +kernel

theorem k2892_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2892) 3).2 2).2 1).1
      183409308006358087136148543351065823034509927372).isSome = true := by
  decide +kernel

theorem k2892_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2892) 3).2 2).2 1).2
      845891736310863983721004801638301723040699869269847459568562879548).isSome = true := by
  decide +kernel

theorem k2893_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2893) 3).1 2).1
      89049230402261008934168012428875799862363936463833623220842912402968556776936346416692409360375809979858909794391957909389433322556).isSome = true := by
  decide +kernel

theorem k2893_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2893) 3).1 2).2 1).1
      183279079137194200572217755813674618920682431436).isSome = true := by
  decide +kernel

theorem k2893_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2893) 3).1 2).2 1).2
      52830512992941616410882852225280103574128423152312117160428069836).isSome = true := by
  decide +kernel

theorem k2893_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2893) 3).2 2).1
      75347457510643483584779050434681074861812096290334180708278134165999501554321168022603434368958527547540757297).isSome = true := by
  decide +kernel

theorem k2893_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2893) 3).2 2).2 1).1
      183171767179527884195602103643540865762901926860).isSome = true := by
  decide +kernel

theorem k2893_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2893) 3).2 2).2 1).2
      2862255492219131083670110587523886060822567628).isSome = true := by
  decide +kernel

theorem k2894_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2894) 3).1 2).1
      1176764990973371470682900929420751068392646571781196781737219692598021287937118950259687045923434043743616060).isSome = true := by
  decide +kernel

theorem k2894_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2894) 3).1 2).2
      15950016321361243678821810498329477368305880199828438807884249151411066294112665843153980).isSome = true := by
  decide +kernel

theorem k2894_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2894) 3).2 2).1
      3985395489719930922083965380803357453602182890940409430424794755498423809119003268037692).isSome = true := by
  decide +kernel

theorem k2894_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2894) 3).2 2).2
      249121924238892403398401483818825383285960006864137796983892598890982583023909513608252).isSome = true := by
  decide +kernel

theorem k2895_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2895) 3).1 1).1
      62253305495861196345792526942735094073749488615388614688526838592145328022305432914636).isSome = true := by
  decide +kernel

theorem k2895_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2895) 3).1 1).2
      3892963890340728714180044384157151389102743157972912176398589513800872523882214972108).isSome = true := by
  decide +kernel

theorem k2895_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2895) 3).2 1).1
      210859547759858078308974213943027796748099626674315278501212048076).isSome = true := by
  decide +kernel

theorem k2895_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2895) 3).2 1).2
      3889972233454884791548349668186852641604845409632838535717691359545535102058648558284).isSome = true := by
  decide +kernel

theorem k2896_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2896) 3).1 2).1
      13182522097122811955088277479636558267808518442050637081783790652).isSome = true := by
  decide +kernel

theorem k2896_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2896) 3).1 2).2
      15556353642122896753602329661323653913544713732177779512463321757531720564669729844284).isSome = true := by
  decide +kernel

theorem k2896_2 : (checkBoxH dirMode depth (splitBox (dirCellBox 2896) 3).2
      86713319881744782683811495210234755754485150117070380069240522512018668367761040580289053244257930216404795760349685323520265009).isSome = true := by
  decide +kernel

theorem k2897_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2897) 3).1
      63691842923396384695683962918579485825484709391537954681426916190024145483172075978214193).isSome = true := by
  decide +kernel

theorem k2897_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 2897) 3).2
      63683200513105754767783210183994630125661946856092115986571026448749218040993837670148913).isSome = true := by
  decide +kernel

theorem k2898_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2898) 3).1
      248731878238899150249540736347381649867773752948605698872758762298308945858892495017777).isSome = true := by
  decide +kernel

theorem k2898_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 2898) 3).2
      3886179038398578930697555964175755881480934723332253806679137986678605367451655739185).isSome = true := by
  decide +kernel

theorem c8 : allCells dirCell 2899 2915 [
    1147043254786263568344083003311360450465281607714885829214322371440750003781104351242186494276354496709705,
    2360914088131415608641, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] = true := by
  decide +kernel

theorem c9 : allCells dirCell 2915 2916 [
    1683863578214701401251303575107050835589586594778991594773245895362509176788684285074068389938217596644701599439524396820577854149776284634172344697935] = true := by
  decide +kernel

theorem k2916_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2916) 3).1 2).1
      346461581929032432066650154592593937732256026077064273048295123689733877298705563324271668424899628842525966533475152266360049).isSome = true := by
  decide +kernel

theorem k2916_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2916) 3).1 2).2
      1353013656940096139320784872568672345229147175195798290521705096006904738188482813376525425553090603052283336980128501704051).isSome = true := by
  decide +kernel

theorem k2916_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2916) 3).2 2).1 2).1
      3959787559324440876200112904485267853090780690073459547295580092798372366381143806780).isSome = true := by
  decide +kernel

theorem k2916_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2916) 3).2 2).1 2).2
      3963602999127601793316663646275831769955552804620284840926495927595698066106904728380).isSome = true := by
  decide +kernel

theorem k2916_4 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2916) 3).2 2).2
      345239051627339003386780085383195779158809043438441489825343275748210939100842070728745166347481475062250707431429393163842801).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 2891 2917 :=
  (Cover.one (box := dirCellBox) (n := 2891)
      (.split 3 (.split 2 (.split 1 (.leaf _ k2891_0) (.leaf _ k2891_1)) (.split 1 (.leaf _ k2891_2) (.leaf _ k2891_3))) (.split 2 (.split 1 (.leaf _ k2891_4) (.leaf _ k2891_5)) (.split 1 (.leaf _ k2891_6) (.leaf _ k2891_7))))).trans <|
  (Cover.one (box := dirCellBox) (n := 2892)
      (.split 3 (.split 2 (.split 1 (.leaf _ k2892_0) (.leaf _ k2892_1)) (.split 1 (.leaf _ k2892_2) (.leaf _ k2892_3))) (.split 2 (.split 1 (.leaf _ k2892_4) (.leaf _ k2892_5)) (.split 1 (.leaf _ k2892_6) (.leaf _ k2892_7))))).trans <|
  (Cover.one (box := dirCellBox) (n := 2893)
      (.split 3 (.split 2 (.leaf _ k2893_0) (.split 1 (.leaf _ k2893_1) (.leaf _ k2893_2))) (.split 2 (.leaf _ k2893_3) (.split 1 (.leaf _ k2893_4) (.leaf _ k2893_5))))).trans <|
  (Cover.one (box := dirCellBox) (n := 2894)
      (.split 3 (.split 2 (.leaf _ k2894_0) (.leaf _ k2894_1)) (.split 2 (.leaf _ k2894_2) (.leaf _ k2894_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 2895)
      (.split 3 (.split 1 (.leaf _ k2895_0) (.leaf _ k2895_1)) (.split 1 (.leaf _ k2895_2) (.leaf _ k2895_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 2896)
      (.split 3 (.split 2 (.leaf _ k2896_0) (.leaf _ k2896_1)) (.leaf _ k2896_2))).trans <|
  (Cover.one (box := dirCellBox) (n := 2897)
      (.split 3 (.leaf _ k2897_0) (.leaf _ k2897_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 2898)
      (.split 3 (.leaf _ k2898_0) (.leaf _ k2898_1))).trans <|
  (Cover.dir c8).trans <|
  (Cover.dir c9).trans <|
  (Cover.one (box := dirCellBox) (n := 2916)
      (.split 3 (.split 2 (.leaf _ k2916_0) (.leaf _ k2916_1)) (.split 2 (.split 2 (.leaf _ k2916_2) (.leaf _ k2916_3)) (.leaf _ k2916_4))))

end C4.Cert.Dir073
