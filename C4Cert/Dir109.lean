module

public import C4Check

public section

/-! Cells `3529 ≤ n < 3530` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir109

theorem k3529_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3529) 3).1 2).1 3).1 2).1
      118079136337756173726167666499050812554785034907606768383489187571258367485798432806542428354706013132715298126070943542602300040990630459810715010151).isSome = true := by
  decide +kernel

theorem k3529_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3529) 3).1 2).1 3).1 2).2
      128801903742270993988407832772666896914242093832862470004624181589672532717657564507536095208891836115875023219976541010718850804190333541764929325).isSome = true := by
  decide +kernel

theorem k3529_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3529) 3).1 2).1 3).2 2).1
      8385335910200745364126506257820956130954944854976317468792785742268052238712647952528780549668780175638385878946565430776969958251212217929439223106310543836580634416935).isSome = true := by
  decide +kernel

theorem k3529_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3529) 3).1 2).1 3).2 2).2
      1773626915634412954198434901526817646170892852752183600707687360182290967596636450926268301209880531280256524689720952378830575417).isSome = true := by
  decide +kernel

theorem k3529_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3529) 3).1 2).2 3).1 3).1
      5439486819663700164846656799100820385692070294258779277153886669800117636065109770362656952616485403939094).isSome = true := by
  decide +kernel

theorem k3529_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3529) 3).1 2).2 3).1 3).2
      463434674821667234213232303773769709235904123521239020538671616804442236673780670368322898231298176394349348536436496571079993765683292764677425430).isSome = true := by
  decide +kernel

theorem k3529_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3529) 3).1 2).2 3).2 2).1 1).1
      111905533134383558280557682302530473004549853337279051786336273241831223446537814425939523599092187285729206182551418791614753389729886598039696883).isSome = true := by
  decide +kernel

theorem k3529_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3529) 3).1 2).2 3).2 2).1 1).2
      201318493070029164176368190317028465014166322).isSome = true := by
  decide +kernel

theorem k3529_8 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3529) 3).1 2).2 3).2 2).2 1).1
      20122586205964146217438705659433717072550240756319859346346253410107212691261241983741869277429375325555).isSome = true := by
  decide +kernel

theorem k3529_9 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3529) 3).1 2).2 3).2 2).2 1).2
      68090053232272251969126094209084096553977355493138400996718305698813503734911725939).isSome = true := by
  decide +kernel

theorem k3529_10 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3529) 3).2 2).1 2).1 3).1
      79735403808079336320051549846702875925662641982397858135499956609022015430039413655852978145393165813126934).isSome = true := by
  decide +kernel

theorem k3529_11 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3529) 3).2 2).1 2).1 3).2
      78038841594139373715311853197095661723966410935905744452833760272926948697572862490018978972075220491982614).isSome = true := by
  decide +kernel

theorem k3529_12 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3529) 3).2 2).1 2).2 3).1
      20240240770306670646119322531560005905326474122155994788717223196081457592482227925930777).isSome = true := by
  decide +kernel

theorem k3529_13 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3529) 3).2 2).1 2).2 3).2
      314088463215797520627141600701527443809408734812261515061826408276029738087830324762805168432217742971115286).isSome = true := by
  decide +kernel

theorem k3529_14 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3529) 3).2 2).2 3).1 2).1
      24322253088214469590750862520791854753836727183761442799137680125905455863818049798627412520122925664139739151879010878819746280137).isSome = true := by
  decide +kernel

theorem k3529_15 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3529) 3).2 2).2 3).1 2).2 1).1
      17133941837219619370281558499602398992932388251944103942333023070104642903747755990194).isSome = true := by
  decide +kernel

theorem k3529_16 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3529) 3).2 2).2 3).1 2).2 1).2
      16693523197178277326437859707030400955780596830741406458586743196092065370061205874).isSome = true := by
  decide +kernel

theorem k3529_17 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3529) 3).2 2).2 3).2 2).1
      372078312825556037864224729010288790731360784373926899253861620821211110733132857946564761775443735842873556080937001286839145241).isSome = true := by
  decide +kernel

theorem k3529_18 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3529) 3).2 2).2 3).2 2).2 1).1
      4195004233346349691491552354261162892906103829343465367477882549035409714631477139250).isSome = true := by
  decide +kernel

theorem k3529_19 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3529) 3).2 2).2 3).2 2).2 1).2
      16356226113465454105426855561191084913191058875758325477040779852705664027649474930).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 3529 3530 :=
  (Cover.one (box := dirCellBox) (n := 3529)
      (.split 3 (.split 2 (.split 3 (.split 2 (.leaf _ k3529_0) (.leaf _ k3529_1)) (.split 2 (.leaf _ k3529_2) (.leaf _ k3529_3))) (.split 3 (.split 3 (.leaf _ k3529_4) (.leaf _ k3529_5)) (.split 2 (.split 1 (.leaf _ k3529_6) (.leaf _ k3529_7)) (.split 1 (.leaf _ k3529_8) (.leaf _ k3529_9))))) (.split 2 (.split 2 (.split 3 (.leaf _ k3529_10) (.leaf _ k3529_11)) (.split 3 (.leaf _ k3529_12) (.leaf _ k3529_13))) (.split 3 (.split 2 (.leaf _ k3529_14) (.split 1 (.leaf _ k3529_15) (.leaf _ k3529_16))) (.split 2 (.leaf _ k3529_17) (.split 1 (.leaf _ k3529_18) (.leaf _ k3529_19)))))))

end C4.Cert.Dir109
