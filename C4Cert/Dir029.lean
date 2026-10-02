module

public import C4Check

public section

/-! Cells `2077 ≤ n < 2083` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir029

theorem k2077_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2077) 3).1 2).1
      343765176558070060269839833042148254659273809202016709651619625510384767679465502051029296251323868656727294207564381301863665).isSome = true := by
  decide +kernel

theorem k2077_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2077) 3).1 2).2
      343898322714302788077932851015475567514813849816648567770970190265557883177013259125994675994135957988178956645756284292134129).isSome = true := by
  decide +kernel

theorem k2077_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2077) 3).2 2).1
      342546382827271853299735267195395009438122047839413334741915228495765931108713442597747938352834462748131167589477203906753779).isSome = true := by
  decide +kernel

theorem k2077_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2077) 3).2 2).2
      5358585767963216931514834388470791315764986409698656580392960270661825163690183144939391613222004583613340454159722600716092).isSome = true := by
  decide +kernel

theorem k2078_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2078) 3).1 2).1
      4744168207889186228993645103529014839654116234932237826157740751976466815173065862369870986020295705804261617).isSome = true := by
  decide +kernel

theorem k2078_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2078) 3).1 2).2
      289752255797409107636434541499149945559927950933771880709017221296814370940561392511894934488437522682684).isSome = true := by
  decide +kernel

theorem k2078_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2078) 3).2 2).1
      302976650696696036045051948276527030822468296292763976953010537479096304735525856760330820891815948336439455985).isSome = true := by
  decide +kernel

theorem k2078_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2078) 3).2 2).2
      15673955395262507139618472575469319819076752867921648770054166737425372838232656954172).isSome = true := by
  decide +kernel

theorem k2079_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2079) 3).1 2).1
      1181923241772341581403931791187377786424068448820654413975366289428350536735193864131276924857763563285822524).isSome = true := by
  decide +kernel

theorem k2079_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2079) 3).1 2).2
      978241036926258297883361806778673304188343228435783021517628461856061145260752731196).isSome = true := by
  decide +kernel

theorem k2079_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2079) 3).2 2).1
      295091780014191978850516989782575851215068184800947453390003528115819189677675256967263353213637213559667772).isSome = true := by
  decide +kernel

theorem k2079_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2079) 3).2 2).2
      52948323943153691899347214733615545477740801279562923811561880636).isSome = true := by
  decide +kernel

theorem k2080_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2080) 3).1 1).1
      4607235513691468307145730841916412160826524874192220844088636269636808243083122828214428007379730324861900).isSome = true := by
  decide +kernel

theorem k2080_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2080) 3).1 1).2
      999090572507340154597862070715010441842960047700880600343461925686573510160991907558348).isSome = true := by
  decide +kernel

theorem k2080_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2080) 3).2 1).1
      15595055555795419968746362164374511341312861059201816636341740255611679778386759631820).isSome = true := by
  decide +kernel

theorem k2080_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2080) 3).2 1).2
      15595990077563066695122484501800375986803244922242482480028369161414039655402954015692).isSome = true := by
  decide +kernel

theorem k2081_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2081) 3).1
      88985945283264851231842538461212513106464999641422597354478358745770443200748840003448479717043400035885361645179063954216431947570).isSome = true := by
  decide +kernel

theorem k2081_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 2081) 3).2
      1020806670527829218103808119575467224761111323582210832654428524011407942510064750382845746).isSome = true := by
  decide +kernel

theorem k2082_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2082) 3).1
      255078775327424658198881711975199517293787735327080693870172539751228629924445307618667314).isSome = true := by
  decide +kernel

theorem k2082_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 2082) 3).2
      996006094960164997948537239860655037004997379005819411041047084574135748079509394518833).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 2077 2083 :=
  (Cover.one (box := dirCellBox) (n := 2077)
      (.split 3 (.split 2 (.leaf _ k2077_0) (.leaf _ k2077_1)) (.split 2 (.leaf _ k2077_2) (.leaf _ k2077_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 2078)
      (.split 3 (.split 2 (.leaf _ k2078_0) (.leaf _ k2078_1)) (.split 2 (.leaf _ k2078_2) (.leaf _ k2078_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 2079)
      (.split 3 (.split 2 (.leaf _ k2079_0) (.leaf _ k2079_1)) (.split 2 (.leaf _ k2079_2) (.leaf _ k2079_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 2080)
      (.split 3 (.split 1 (.leaf _ k2080_0) (.leaf _ k2080_1)) (.split 1 (.leaf _ k2080_2) (.leaf _ k2080_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 2081)
      (.split 3 (.leaf _ k2081_0) (.leaf _ k2081_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 2082)
      (.split 3 (.leaf _ k2082_0) (.leaf _ k2082_1)))

end C4.Cert.Dir029
