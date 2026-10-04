module

public import C4Check

public section

/-! Cells `2412 ≤ n < 2414` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir042

theorem k2412_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2412) 3).1 2).1 3).1 3).1 2).1
      1015665704300973928535449948366688645844132337030613564833318130699796806893339198976689).isSome = true := by
  decide +kernel

theorem k2412_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2412) 3).1 2).1 3).1 3).1 2).2
      13776792607870062864721233356071617239155110609569551021814262782385).isSome = true := by
  decide +kernel

theorem k2412_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2412) 3).1 2).1 3).1 3).2 2).1
      253538413536490842085299238794988073302408256708246757427146075238783896733781544885425).isSome = true := by
  decide +kernel

theorem k2412_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2412) 3).1 2).1 3).1 3).2 2).2
      1015127325740377895914313268365591902129937458200263449750655023006177962883951375774385).isSome = true := by
  decide +kernel

theorem k2412_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2412) 3).1 2).1 3).2 2).1 1).1
      13414497032121330371435413910116341806386458909799577634911911084).isSome = true := by
  decide +kernel

theorem k2412_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2412) 3).1 2).1 3).2 2).1 1).2
      3954100532163718265622636605785856250797230369327415720139929754554215204573255528236).isSome = true := by
  decide +kernel

theorem k2412_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2412) 3).1 2).1 3).2 2).2 1).1
      13412784002486430487087355141952131164100976604799694502446595244).isSome = true := by
  decide +kernel

theorem k2412_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2412) 3).1 2).1 3).2 2).2 1).2
      13408697419227797625275986058498315484368064361447792812823768876).isSome = true := by
  decide +kernel

theorem k2412_8 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2412) 3).1 2).2 3).1 2).1
      88596107423708470957235156315131390778442065084313335079706658586269162881238069869677174020341437388276149965366509312739239601).isSome = true := by
  decide +kernel

theorem k2412_9 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2412) 3).1 2).2 3).1 2).2
      75099098938586065299931982474711984965186489163377640523117749371568272591747460373188827722904571786337713).isSome = true := by
  decide +kernel

theorem k2412_10 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2412) 3).1 2).2 3).2 2).1
      353304952411277427729704531832744126566535541280902871787192619618149819939278898830392453400889182397101213307630082325489483185).isSome = true := by
  decide +kernel

theorem k2412_11 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2412) 3).1 2).2 3).2 2).2
      74862588441866923278606789657362410959995994793000216152939929172409334013917992655568709165031710654094769).isSome = true := by
  decide +kernel

theorem k2412_12 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2412) 3).2 2).1 3).1 2).1 1).1
      3349297643057280976712915640028848217594979609319043991335231276).isSome = true := by
  decide +kernel

theorem k2412_13 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2412) 3).2 2).1 3).1 2).1 1).2
      53464969530455330033213559935244512025012523515384548730434075436).isSome = true := by
  decide +kernel

theorem k2412_14 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2412) 3).2 2).1 3).1 2).2
      352186685699549962521506957463818642403238888636710633642312055130560529404701307341100558698006835716761541568268666363329477809).isSome = true := by
  decide +kernel

theorem k2412_15 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2412) 3).2 2).1 3).2 2).1
      19041004206075408707931107089877365557450954869153261694476762329124304813881794692021991804468172788599140145).isSome = true := by
  decide +kernel

theorem k2412_16 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2412) 3).2 2).1 3).2 2).2
      76196249375906774122654637493093316555121972897493793538087541755748087371542024134300321798914721702234127537).isSome = true := by
  decide +kernel

theorem k2412_17 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2412) 3).2 2).2 3).1 2).1
      88117224906891168668435485988807690737558088462747116176329944130628883621637683790621199453289532227485449305470759879629700273).isSome = true := by
  decide +kernel

theorem k2412_18 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2412) 3).2 2).2 3).1 2).2
      19119487950285086289489057781853615415775566082282698904084933748605943054510250067123191933314409734580073137).isSome = true := by
  decide +kernel

theorem k2412_19 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2412) 3).2 2).2 3).2 2).1
      88025761454765579774421639251661116759597091564144532164398202515584000610053803639647128747316351348031631243063920016479583409).isSome = true := by
  decide +kernel

theorem k2412_20 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2412) 3).2 2).2 3).2 2).2
      19080182337335419293212014414773631625493833066678676426857252785010665269989882605989549097156562711584799921).isSome = true := by
  decide +kernel

theorem k2413_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2413) 3).1 2).1 3).1 1).1
      1031172428747054007474888123034380978371892680345682403994728450528060115585784138875490098).isSome = true := by
  decide +kernel

theorem k2413_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2413) 3).1 2).1 3).1 1).2
      4027159658357602171855099681306929556418507532766150163376581582867607378073179583781682).isSome = true := by
  decide +kernel

theorem k2413_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2413) 3).1 2).1 3).2 1).1
      74197770302992055196533585075289077123448940249599183342476348618886671441511612370468945117946445183703858).isSome = true := by
  decide +kernel

theorem k2413_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2413) 3).1 2).1 3).2 1).2
      16085897800758287753808646717410873833026317001194447909723171279090298999239483840912178).isSome = true := by
  decide +kernel

theorem k2413_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2413) 3).1 2).2 3).1 1).1
      21963096522805306209030127266676330706909673538170184214789845353934698568213103099275799259918618127809471162869144721869397810).isSome = true := by
  decide +kernel

theorem k2413_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2413) 3).1 2).2 3).1 1).2
      19046794051254431340239650793234768573213872953701025547453236126656981605984856284388455521974786770140213042).isSome = true := by
  decide +kernel

theorem k2413_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2413) 3).1 2).2 3).2 1).1
      1007614807244364664261809407348154462310881614320110667748387096190042840206722224200498).isSome = true := by
  decide +kernel

theorem k2413_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2413) 3).1 2).2 3).2 1).2
      16102172047292783475298539823628792373574963576932239108934934400761893333632987862244146).isSome = true := by
  decide +kernel

theorem k2413_8 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2413) 3).2 2).1 1).1 3).1
      1185683190836031694569539697305383269822232691124710412099525981298972340323877522811937061117773897647119154).isSome = true := by
  decide +kernel

theorem k2413_9 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2413) 3).2 2).1 1).1 3).2
      5462151350872588426172907245522016558904490698531225103892882309836120035318256272638680490138140265789955995439795086928763698).isSome = true := by
  decide +kernel

theorem k2413_10 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2413) 3).2 2).1 1).2 3).1
      257061239644266602438337914036885763784661086183904306308632231023921798943564940918250290).isSome = true := by
  decide +kernel

theorem k2413_11 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2413) 3).2 2).1 1).2 3).2
      16048842168272769744793460447234431518603069164531858459101391783536209861450926198987570).isSome = true := by
  decide +kernel

theorem k2413_12 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2413) 3).2 2).2 3).1 1).1
      1005235232103954241843038742358222868649382041865596741532400627034829615070295870774066).isSome = true := by
  decide +kernel

theorem k2413_13 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2413) 3).2 2).2 3).1 1).2
      1005065672652892476293226178919195302391191962693047706084484803976639467392332429105970).isSome = true := by
  decide +kernel

theorem k2413_14 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2413) 3).2 2).2 3).2 1).1
      1003864361685099648722828271559854116339329537735324796004483067061112597371511215959756).isSome = true := by
  decide +kernel

theorem k2413_15 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2413) 3).2 2).2 3).2 1).2
      1003913822044792303683770359298206308296906008206826156351737883427109270050155683224370).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 2412 2414 :=
  (Cover.one (box := dirCellBox) (n := 2412)
      (.split 3 (.split 2 (.split 3 (.split 3 (.split 2 (.leaf _ k2412_0) (.leaf _ k2412_1)) (.split 2 (.leaf _ k2412_2) (.leaf _ k2412_3))) (.split 2 (.split 1 (.leaf _ k2412_4) (.leaf _ k2412_5)) (.split 1 (.leaf _ k2412_6) (.leaf _ k2412_7)))) (.split 3 (.split 2 (.leaf _ k2412_8) (.leaf _ k2412_9)) (.split 2 (.leaf _ k2412_10) (.leaf _ k2412_11)))) (.split 2 (.split 3 (.split 2 (.split 1 (.leaf _ k2412_12) (.leaf _ k2412_13)) (.leaf _ k2412_14)) (.split 2 (.leaf _ k2412_15) (.leaf _ k2412_16))) (.split 3 (.split 2 (.leaf _ k2412_17) (.leaf _ k2412_18)) (.split 2 (.leaf _ k2412_19) (.leaf _ k2412_20)))))).trans <|
  (Cover.one (box := dirCellBox) (n := 2413)
      (.split 3 (.split 2 (.split 3 (.split 1 (.leaf _ k2413_0) (.leaf _ k2413_1)) (.split 1 (.leaf _ k2413_2) (.leaf _ k2413_3))) (.split 3 (.split 1 (.leaf _ k2413_4) (.leaf _ k2413_5)) (.split 1 (.leaf _ k2413_6) (.leaf _ k2413_7)))) (.split 2 (.split 1 (.split 3 (.leaf _ k2413_8) (.leaf _ k2413_9)) (.split 3 (.leaf _ k2413_10) (.leaf _ k2413_11))) (.split 3 (.split 1 (.leaf _ k2413_12) (.leaf _ k2413_13)) (.split 1 (.leaf _ k2413_14) (.leaf _ k2413_15))))))

end C4.Cert.Dir042
