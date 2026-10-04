module

public import C4Check

public section

/-! Cells `3224 ≤ n < 3226` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir092

theorem k3224_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3224) 3).1 2).1 2).1 3).1
      260282955499253578618777481622948736786601583067136836728549013022717721014789401710293233).isSome = true := by
  decide +kernel

theorem k3224_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3224) 3).1 2).1 2).1 3).2
      1038213400224844041390175417649518695374704797896427051800704547907007910558698061455356145).isSome = true := by
  decide +kernel

theorem k3224_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3224) 3).1 2).1 2).2 1).1
      4157757029984029149167113030234458054214568795360961928705264821678525038574853838778790131).isSome = true := by
  decide +kernel

theorem k3224_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3224) 3).1 2).1 2).2 1).2
      16232586079987532786051436319272982492608221352146127878962570934844176957894657251371827).isSome = true := by
  decide +kernel

theorem k3224_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3224) 3).1 2).2 2).1 1).1
      1039983761121742469083380679540344513900506706656245927794329421965223727658363565529201843).isSome = true := by
  decide +kernel

theorem k3224_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3224) 3).1 2).2 2).1 1).2
      1015116303261793436942559947336621629648469969119529738637568936444478615639098153868083).isSome = true := by
  decide +kernel

theorem k3224_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3224) 3).1 2).2 2).2 1).1
      63589817825037096879899685533443415333722660953073136881530785301023658091097433111612).isSome = true := by
  decide +kernel

theorem k3224_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3224) 3).1 2).2 2).2 1).2
      254256429050736737337141747404901512926659564848854585295212173922685775040832952122428).isSome = true := by
  decide +kernel

theorem k3224_8 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3224) 3).2 2).1 2).1 1).1 3).1
      743326028565988168819043060046918131510911614012).isSome = true := by
  decide +kernel

theorem k3224_9 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3224) 3).2 2).1 2).1 1).1 3).2
      46369419831116136736140364799570875408690162748).isSome = true := by
  decide +kernel

theorem k3224_10 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3224) 3).2 2).1 2).1 1).2
      64594325503488058169905306050429952853683357274742969255569732034519447503643481799551795).isSome = true := by
  decide +kernel

theorem k3224_11 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3224) 3).2 2).1 2).2 1).1
      14355102933881673087711416843486027671025970944309841937235624643412816115).isSome = true := by
  decide +kernel

theorem k3224_12 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3224) 3).2 2).1 2).2 1).2
      1009944019774888584668687157488788663473926443510643479077130131070084417566268840581939).isSome = true := by
  decide +kernel

theorem k3224_13 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3224) 3).2 2).2 2).1 1).1
      16564351094534136186237591699649919209625730221884780616908230403876074903561613025030303987).isSome = true := by
  decide +kernel

theorem k3224_14 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3224) 3).2 2).2 2).1 1).2
      1010499391056969391178671283254805581675251561624029887585452029330487217384317496695603).isSome = true := by
  decide +kernel

theorem k3224_15 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3224) 3).2 2).2 2).2 1).1
      63278488705743901271061982757168580952821355535227403425458528890341071092692220230716).isSome = true := by
  decide +kernel

theorem k3224_16 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3224) 3).2 2).2 2).2 1).2
      63254105641815251380460347325936030793267663112784265723296740823445416976351357251276).isSome = true := by
  decide +kernel

theorem k3225_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3225) 3).1 2).1 2).1 1).1
      1055200621718001258975741775026894909524167713191197437343172895510052831956833670791106900211).isSome = true := by
  decide +kernel

theorem k3225_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3225) 3).1 2).1 2).1 1).2
      3574549752541831164780931871444242360573164873370658399835314810785034483).isSome = true := by
  decide +kernel

theorem k3225_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3225) 3).1 2).1 2).2 1).1
      57221454174380590348518799688968476594993337428216402995480919100276322547).isSome = true := by
  decide +kernel

theorem k3225_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3225) 3).1 2).1 2).2 1).2
      223469548696827052972971162490514518703771218233970559515413387140295475).isSome = true := by
  decide +kernel

theorem k3225_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3225) 3).1 2).2 2).1 1).1
      297552058275318346059146569163253490618942885583539655997775581440127096231017735186440653909335322484587580).isSome = true := by
  decide +kernel

theorem k3225_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3225) 3).1 2).2 2).1 1).2
      1006963595778202077932811401192183566413416663440075697653758824227249331403729096514355).isSome = true := by
  decide +kernel

theorem k3225_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3225) 3).1 2).2 2).2 1).1
      1008582755005300926380678439528112493458621209735276531907234301030584529943604708031548).isSome = true := by
  decide +kernel

theorem k3225_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3225) 3).1 2).2 2).2 1).2
      54659859516815839503859681650770793882658580577275181231646854033100).isSome = true := by
  decide +kernel

theorem k3225_8 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3225) 3).2 2).1 2).1 1).1
      4111655300278555179861799345856147120848103209355276420905559354591870641680234435953684723).isSome = true := by
  decide +kernel

theorem k3225_9 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3225) 3).2 2).1 2).1 1).2
      1004165826853801271089177366649888356287480026549334665819619841466719740437477977748028).isSome = true := by
  decide +kernel

theorem k3225_10 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3225) 3).2 2).1 2).2 1).1
      296592735438624618649888076170106519294169598230260533506810902530910533811684255947961531663474207401425980).isSome = true := by
  decide +kernel

theorem k3225_11 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3225) 3).2 2).1 2).2 1).2
      54511021851863534004589157439274720990746110760819720494166213590076).isSome = true := by
  decide +kernel

theorem k3225_12 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3225) 3).2 2).2 2).1 1).1
      1005303144628843252252476664423209884010998782829829940484637519077035392033126239550524).isSome = true := by
  decide +kernel

theorem k3225_13 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3225) 3).2 2).2 2).1 1).2
      62816006272114500904706749321931668660090875466985444471936122676212551909772787301436).isSome = true := by
  decide +kernel

theorem k3225_14 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3225) 3).2 2).2 2).2 1).1
      1005661380342178258318288827518742867085685566820403259077244064381800777834973760371772).isSome = true := by
  decide +kernel

theorem k3225_15 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3225) 3).2 2).2 2).2 1).2
      3406394159256460817835694403172712164733417198067876184417225194556).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 3224 3226 :=
  (Cover.one (box := dirCellBox) (n := 3224)
      (.split 3 (.split 2 (.split 2 (.split 3 (.leaf _ k3224_0) (.leaf _ k3224_1)) (.split 1 (.leaf _ k3224_2) (.leaf _ k3224_3))) (.split 2 (.split 1 (.leaf _ k3224_4) (.leaf _ k3224_5)) (.split 1 (.leaf _ k3224_6) (.leaf _ k3224_7)))) (.split 2 (.split 2 (.split 1 (.split 3 (.leaf _ k3224_8) (.leaf _ k3224_9)) (.leaf _ k3224_10)) (.split 1 (.leaf _ k3224_11) (.leaf _ k3224_12))) (.split 2 (.split 1 (.leaf _ k3224_13) (.leaf _ k3224_14)) (.split 1 (.leaf _ k3224_15) (.leaf _ k3224_16)))))).trans <|
  (Cover.one (box := dirCellBox) (n := 3225)
      (.split 3 (.split 2 (.split 2 (.split 1 (.leaf _ k3225_0) (.leaf _ k3225_1)) (.split 1 (.leaf _ k3225_2) (.leaf _ k3225_3))) (.split 2 (.split 1 (.leaf _ k3225_4) (.leaf _ k3225_5)) (.split 1 (.leaf _ k3225_6) (.leaf _ k3225_7)))) (.split 2 (.split 2 (.split 1 (.leaf _ k3225_8) (.leaf _ k3225_9)) (.split 1 (.leaf _ k3225_10) (.leaf _ k3225_11))) (.split 2 (.split 1 (.leaf _ k3225_12) (.leaf _ k3225_13)) (.split 1 (.leaf _ k3225_14) (.leaf _ k3225_15))))))

end C4.Cert.Dir092
