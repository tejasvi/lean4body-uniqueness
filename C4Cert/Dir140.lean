module

public import C4Check

public section

/-! Cells `4428 ≤ n < 4437` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir140

theorem k4428_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4428) 2).1 3).1 2).1
      5517308072119580845601424263726638627300533178114953927406903583279202306418468691444502831080708010187969971953421396674910089).isSome = true := by
  decide +kernel

theorem k4428_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4428) 2).1 3).1 2).2
      18701129968587185204479675483280916428376857866646205020148081682662922568177945676773362898564119220575025).isSome = true := by
  decide +kernel

theorem k4428_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4428) 2).1 3).2 2).1
      298169312733408083341288299449161316111578275577940453654592524066721215178415687763800579614816280522484529).isSome = true := by
  decide +kernel

theorem k4428_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4428) 2).1 3).2 2).2
      18624125021491436733264322866701915539195796443803790245070039671577048019736838131916740482702420262378289).isSome = true := by
  decide +kernel

theorem k4428_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4428) 2).2 3).1 2).1
      259499465776085508589910873146628592623659632758035712118834779401600536006221909635910857).isSome = true := by
  decide +kernel

theorem k4428_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4428) 2).2 3).1 2).2
      253678917742663463578431370128049389469663793100675516713402822013728776946885783548721).isSome = true := by
  decide +kernel

theorem k4428_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4428) 2).2 3).2 2).1
      74524163373672686557783162846816706911809768092924915047501597859876584726422956058257594699156095182953265).isSome = true := by
  decide +kernel

theorem k4428_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4428) 2).2 3).2 2).2
      74618721708469555706158583564091685263912882810232087484351915515151078375908382366316386908159189769902897).isSome = true := by
  decide +kernel

theorem k4429_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4429) 2).1 3).1 2).1
      18587983898689028940244505025271194908581049945509110414403893012171719007111874144034564333352774218930993).isSome = true := by
  decide +kernel

theorem k4429_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4429) 2).1 3).1 2).2
      18579055472886030181333391734241683915964163689131354804541747313944729553388783795391914061311148285090609).isSome = true := by
  decide +kernel

theorem k4429_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4429) 2).1 3).2 2).1
      62759229039661585441439882619325730614910735698277960121787509449813922431236244609841).isSome = true := by
  decide +kernel

theorem k4429_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4429) 2).1 3).2 2).2
      62786266376716855572996233075789949905882154059783263634558166742505156478083380648753).isSome = true := by
  decide +kernel

theorem k4429_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4429) 2).2 3).1 2).1
      18571952111296939059108088757577975947496561538487836018510188903647436731155769242394421001372161388436273).isSome = true := by
  decide +kernel

theorem k4429_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4429) 2).2 3).1 2).2
      4031422480220374943621675033942802712494435957665248666770781586814018411188032504229425).isSome = true := by
  decide +kernel

theorem k4429_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4429) 2).2 3).2 2).1
      62807422923039222627902010598174022819563205348956239545498129046217183702133372197681).isSome = true := by
  decide +kernel

theorem k4429_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4429) 2).2 3).2 2).2
      251305098858675280734031511488890116025731380477636901832568896942387655356771412056881).isSome = true := by
  decide +kernel

theorem k4430_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4430) 2).1 3).1 2).1
      848935619460940727888549270256497685500805444247738974326311443633).isSome = true := by
  decide +kernel

theorem k4430_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4430) 2).1 3).1 2).2
      979136385234898053839013537502804977228377133141457861539333962588037407878077323057).isSome = true := by
  decide +kernel

theorem k4430_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4430) 2).1 3).2 1).1
      62576047199236109742314476293518381193341761856914904675326197435475614289417505168562).isSome = true := by
  decide +kernel

theorem k4430_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4430) 2).1 3).2 1).2
      3312060868723958354775382557387918883109443725950109548203948402).isSome = true := by
  decide +kernel

theorem k4430_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4430) 2).2 3).1 1).1
      250840476847783906202711696404356787894386837590424499680367289792290541223365272034098).isSome = true := by
  decide +kernel

theorem k4430_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4430) 2).2 3).1 1).2
      3918602165851571021418370571292644973268361675884299493609620087926524660359508563762).isSome = true := by
  decide +kernel

theorem k4430_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4430) 2).2 3).2 1).1
      3914910060905257034451052057993544482657443889797383463054337856746552912587827664690).isSome = true := by
  decide +kernel

theorem k4430_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4430) 2).2 3).2 1).2
      978066752644787385369624468753444329865710825587903521781576384591806179220225193442).isSome = true := by
  decide +kernel

theorem k4431_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4431) 2).1 3).1 1).1
      18013481501231071110235071141850469627176247008475695750500179146091038299948014132696158593633476246956).isSome = true := by
  decide +kernel

theorem k4431_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 4431) 2).1 3).1 1).2
      206956022520888461534911555281552563564197361453544917343034796).isSome = true := by
  decide +kernel

theorem k4431_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4431) 2).1 3).2
      84984138280227012351106376982388829821389145957536178244656689817756507690155668691302916044182856533672722012438583588517553).isSome = true := by
  decide +kernel

theorem k4431_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4431) 2).2 3).1
      5576372969268141080149035644939709232508766494493474617421243099132719062552521645520059831489115840068928648829999264408989957297).isSome = true := by
  decide +kernel

theorem k4431_4 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4431) 2).2 3).2
      5440422129209392620008376201239839686817744455746545999208149766368482880999653001949961453686287938006458918620268401613206193).isSome = true := by
  decide +kernel

theorem k4432_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4432) 2).1 3).1
      71925291158521116677946323290520916336318249731030176704145248548432556862701214778370330439531252637105).isSome = true := by
  decide +kernel

theorem k4432_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4432) 2).1 3).2
      17970987340764920029343904038764759802550607522366704922277163432799293290072734866489069413415570529713).isSome = true := by
  decide +kernel

theorem k4432_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4432) 2).2 3).1
      21234746240052906372038916108740138350732531464183117808173796655646745065779562250008516066016533555501253637265817745710513).isSome = true := by
  decide +kernel

theorem k4432_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4432) 2).2 3).2
      21221200805520942828189728325075010472437271639448949107367009821462831613980709459737550717146632004470843849967184760823217).isSome = true := by
  decide +kernel

theorem k4433_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4433) 2).1 3).1
      17962465962327198630891560089544720685468910430538673657718433933846657865095798078470026430959775866289).isSome = true := by
  decide +kernel

theorem k4433_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4433) 2).1 3).2
      243342955089876193642124135997838421530584971974272704436769438453961765382339269873).isSome = true := by
  decide +kernel

theorem k4433_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4433) 2).2 3).1
      71863135270785870989347867845250423543913494236407228225616953920525021694685626140263591730270395981233).isSome = true := by
  decide +kernel

theorem k4433_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 4433) 2).2 3).2
      17958680567776569558583204728738208904100682859312785638727464802144011358270545798309032385266228616625).isSome = true := by
  decide +kernel

theorem k4434_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4434) 2).1
      461413903389546483431441779894438335642833727238551632833177526389826325678470370138000959453331026868728234816081517100707083066387142464751529516131047220493563335).isSome = true := by
  decide +kernel

theorem k4434_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4434) 2).2
      100059762939485402513877491568938941645970765795599799459054693065557759311408731534312401791191624273435774477097201400802104950834443631388482803).isSome = true := by
  decide +kernel

theorem k4435_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4435) 2).1
      5294260131097804758514279600068624814632679649229569209759715662768216514573072701407760527882982523875058510283605912155633).isSome = true := by
  decide +kernel

theorem k4435_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4435) 2).2
      115313637603142124299811492777310166525584564045437483381370467550446590657416103874087438226651715191528235562964795493799982189284920243395935305709522514321438195).isSome = true := by
  decide +kernel

theorem k4436_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 4436) 2).1
      15190673841052283214160591485571776231235615674736837230073300261357742815033460081).isSome = true := by
  decide +kernel

theorem k4436_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 4436) 2).2
      1562202755723864505847155554311146086008738931471663970040781346331274848014475024639910860657519394146414863129153437153320386765740155463366129).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 4428 4437 :=
  (Cover.one (box := dirCellBox) (n := 4428)
      (.split 2 (.split 3 (.split 2 (.leaf _ k4428_0) (.leaf _ k4428_1)) (.split 2 (.leaf _ k4428_2) (.leaf _ k4428_3))) (.split 3 (.split 2 (.leaf _ k4428_4) (.leaf _ k4428_5)) (.split 2 (.leaf _ k4428_6) (.leaf _ k4428_7))))).trans <|
  (Cover.one (box := dirCellBox) (n := 4429)
      (.split 2 (.split 3 (.split 2 (.leaf _ k4429_0) (.leaf _ k4429_1)) (.split 2 (.leaf _ k4429_2) (.leaf _ k4429_3))) (.split 3 (.split 2 (.leaf _ k4429_4) (.leaf _ k4429_5)) (.split 2 (.leaf _ k4429_6) (.leaf _ k4429_7))))).trans <|
  (Cover.one (box := dirCellBox) (n := 4430)
      (.split 2 (.split 3 (.split 2 (.leaf _ k4430_0) (.leaf _ k4430_1)) (.split 1 (.leaf _ k4430_2) (.leaf _ k4430_3))) (.split 3 (.split 1 (.leaf _ k4430_4) (.leaf _ k4430_5)) (.split 1 (.leaf _ k4430_6) (.leaf _ k4430_7))))).trans <|
  (Cover.one (box := dirCellBox) (n := 4431)
      (.split 2 (.split 3 (.split 1 (.leaf _ k4431_0) (.leaf _ k4431_1)) (.leaf _ k4431_2)) (.split 3 (.leaf _ k4431_3) (.leaf _ k4431_4)))).trans <|
  (Cover.one (box := dirCellBox) (n := 4432)
      (.split 2 (.split 3 (.leaf _ k4432_0) (.leaf _ k4432_1)) (.split 3 (.leaf _ k4432_2) (.leaf _ k4432_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 4433)
      (.split 2 (.split 3 (.leaf _ k4433_0) (.leaf _ k4433_1)) (.split 3 (.leaf _ k4433_2) (.leaf _ k4433_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 4434)
      (.split 2 (.leaf _ k4434_0) (.leaf _ k4434_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 4435)
      (.split 2 (.leaf _ k4435_0) (.leaf _ k4435_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 4436)
      (.split 2 (.leaf _ k4436_0) (.leaf _ k4436_1)))

end C4.Cert.Dir140
