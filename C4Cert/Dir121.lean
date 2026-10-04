module

public import C4Check

public section

/-! Cells `3707 ≤ n < 3734` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir121

theorem k3707_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3707) 3).1 1).1
      54012437310495475224270333072334637342092658910317240480176516414524).isSome = true := by
  decide +kernel

theorem k3707_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3707) 3).1 1).2
      62273663974185551881173831533285274570591852626000719171794967108499832826571469470780).isSome = true := by
  decide +kernel

theorem k3707_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3707) 3).2 2).1
      3374726731818888446636390910769084976193967937591897624289960772412).isSome = true := by
  decide +kernel

theorem k3707_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3707) 3).2 2).2
      13499566449803434035269186564711654354966737627191944664907829656636).isSome = true := by
  decide +kernel

theorem k3708_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3708) 3).1
      77048573495519902633154521502143227003695974009928086388351930652522138173188486119756401203106627692348845715698).isSome = true := by
  decide +kernel

theorem k3708_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 3708) 3).2
      1203993161302095913624035278315480534709182619299427670152248711970312516844057917191511884135517666379214156017).isSome = true := by
  decide +kernel

theorem k3709_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3709) 3).1
      1175515062487790992566912488547406007897970298478230883207253722165083982916232266494822369219914457270107196).isSome = true := by
  decide +kernel

theorem k3709_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 3709) 3).2
      1175054002064855981653536960813087693717297191530957775246723620175836101037515071241754881817234561426046012).isSome = true := by
  decide +kernel

theorem k3710_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 3710) 1).1
      18356431685792628180597348219951994659325047598554154633067333100728898862326015704748461059831182933834812).isSome = true := by
  decide +kernel

theorem k3710_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 3710) 1).2
      1174881446027609570113506652779455270344841588228133716189035255349675043629523515700248229012989917652676850).isSome = true := by
  decide +kernel

theorem c4 : allCells dirCell 3711 3712 [
    22186649476402272736996128004441687833357118637013475508793549054697649814864298617458492164389289666069198312956587246072431440115] = true := by
  decide +kernel

theorem c5 : allCells dirCell 3712 3713 [
    5546149627235322870788119793008749814976664530497373647325352390919069355449579397426738245295001753149177722119121806002983661809] = true := by
  decide +kernel

theorem c6 : allCells dirCell 3713 3727 [
    3885353352150902360043115826925077394623781473777877917795229120738438184202610796913,
    147559797236305877780, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] = true := by
  decide +kernel

theorem c7 : allCells dirCell 3727 3728 [
    18858674835901219925725808836954815777778397088540805344706961620215805214154088756196211035676960152831495] = true := by
  decide +kernel

theorem k3728_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3728) 3).1 2).1
      63607845437572178054510280906636149354753431141766322284169285527353477248194935741618).isSome = true := by
  decide +kernel

theorem k3728_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3728) 3).1 2).2
      15509101217201581707262955753757336096783554167008668310290815319824286565744679281).isSome = true := by
  decide +kernel

theorem k3728_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3728) 3).2 2).1
      3954676807695739716392014529462526635878687454240413785096333378708835361275268192049).isSome = true := by
  decide +kernel

theorem k3728_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3728) 3).2 2).2
      247168062062775787179282076194194348079445636248698374118535396423605874374189997868).isSome = true := by
  decide +kernel

theorem k3729_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3729) 3).1 2).1
      74552091318785670532548832126691415426991361485689114370027727531127921378863477654014892538322079983180593).isSome = true := by
  decide +kernel

theorem k3729_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3729) 3).1 2).2
      15786801943650952501600542285751303939533524479679674783234602708625239377953694521137).isSome = true := by
  decide +kernel

theorem k3729_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3729) 3).2 2).1
      1189726191477712405848474455966188748527766813885798618780346779587173115610327438825242093192001694038874929).isSome = true := by
  decide +kernel

theorem k3729_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3729) 3).2 2).2
      1161449603580254642526031302067967000180307936738447216295490742086769156426498637542224244741187087201228).isSome = true := by
  decide +kernel

theorem k3730_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3730) 2).1 3).1
      75974673318627066891765832428351451039177166835516834708787423211822771965574870294567307805212563327983147825).isSome = true := by
  decide +kernel

theorem k3730_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3730) 2).1 3).2
      1399118421301229447093591521847338543323643843949244512377609277027199974723026516399288391900070188379537144345787666932960211916).isSome = true := by
  decide +kernel

theorem k3730_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3730) 2).2 3).1
      18552595566101115682796327505271765418686054972159580056854733715895993859366307652936550300900083971339212).isSome = true := by
  decide +kernel

theorem k3730_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3730) 2).2 3).2
      64249836145734355377950517855754466802785751787705139602844770619237518319149704523930417).isSome = true := by
  decide +kernel

theorem k3731_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3731) 2).1 3).1
      4846561347577722808149501498908827758275486129950553764044644153731546876590634664705121517573686328444227365681).isSome = true := by
  decide +kernel

theorem k3731_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3731) 2).1 3).2
      4727374761488020804229733705657463913744079157569105018849453683112198900781270763880631516770564816921994188).isSome = true := by
  decide +kernel

theorem k3731_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3731) 2).2 3).1
      1183485322107920737505108893735237097801521316653572931237937780246818279363316564238867454444195869541704652).isSome = true := by
  decide +kernel

theorem k3731_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3731) 2).2 3).2
      295508687090847053910690477239503206940328998971444740108128876287796007239686856752011291757824041811747788).isSome = true := by
  decide +kernel

theorem k3732_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3732) 2).1 3).1
      4722418799118190245114949589826891377323668215528290344982551277517519251692775540887073487376586260794195004).isSome = true := by
  decide +kernel

theorem k3732_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3732) 2).1 3).2
      87038840722324048835572488105926423464508810514447854938313553014005155506171218838252876719962476166479868746267194489908640828).isSome = true := by
  decide +kernel

theorem k3732_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3732) 2).2 3).1
      16002365506218119648256103149547335608786870696453137598274630859736065774623779796755404).isSome = true := by
  decide +kernel

theorem k3732_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3732) 2).2 3).2
      1179772110761346059712564552510439092818813594993973221542286847410699066561231009510324140516874110748474428).isSome = true := by
  decide +kernel

theorem k3733_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3733) 2).1 3).1
      63898409933887522245060555331445960353093259277119059158815394257139853775711721058090044).isSome = true := by
  decide +kernel

theorem k3733_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3733) 2).1 3).2
      865445599644534662243678738529912415728463886851592831690268516170812).isSome = true := by
  decide +kernel

theorem k3733_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3733) 2).2 3).1
      15976710292264985299743754391818305616795252530078291227258475860643395864075376586800188).isSome = true := by
  decide +kernel

theorem k3733_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3733) 2).2 3).2
      54099487680321683058253062628714419610445245191345682668688307010620).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 3707 3734 :=
  (Cover.one (box := dirCellBox) (n := 3707)
      (.split 3 (.split 1 (.leaf _ k3707_0) (.leaf _ k3707_1)) (.split 2 (.leaf _ k3707_2) (.leaf _ k3707_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 3708)
      (.split 3 (.leaf _ k3708_0) (.leaf _ k3708_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 3709)
      (.split 3 (.leaf _ k3709_0) (.leaf _ k3709_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 3710)
      (.split 1 (.leaf _ k3710_0) (.leaf _ k3710_1))).trans <|
  (Cover.dir c4).trans <|
  (Cover.dir c5).trans <|
  (Cover.dir c6).trans <|
  (Cover.dir c7).trans <|
  (Cover.one (box := dirCellBox) (n := 3728)
      (.split 3 (.split 2 (.leaf _ k3728_0) (.leaf _ k3728_1)) (.split 2 (.leaf _ k3728_2) (.leaf _ k3728_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 3729)
      (.split 3 (.split 2 (.leaf _ k3729_0) (.leaf _ k3729_1)) (.split 2 (.leaf _ k3729_2) (.leaf _ k3729_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 3730)
      (.split 2 (.split 3 (.leaf _ k3730_0) (.leaf _ k3730_1)) (.split 3 (.leaf _ k3730_2) (.leaf _ k3730_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 3731)
      (.split 2 (.split 3 (.leaf _ k3731_0) (.leaf _ k3731_1)) (.split 3 (.leaf _ k3731_2) (.leaf _ k3731_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 3732)
      (.split 2 (.split 3 (.leaf _ k3732_0) (.leaf _ k3732_1)) (.split 3 (.leaf _ k3732_2) (.leaf _ k3732_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 3733)
      (.split 2 (.split 3 (.leaf _ k3733_0) (.leaf _ k3733_1)) (.split 3 (.leaf _ k3733_2) (.leaf _ k3733_3))))

end C4.Cert.Dir121
