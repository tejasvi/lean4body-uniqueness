module

public import C4Check

public section

/-! Cells `2413 ≤ n < 2417` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir044

theorem k2413_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2413) 3).1 2).1 1).1
      251380863590075675641531883688150962021768169731748329369319577087959431105525788548275).isSome = true := by
  decide +kernel

theorem k2413_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2413) 3).1 2).1 1).2
      257339322190747898025804233016853440786931859222676371597545056775534857064034487131254579).isSome = true := by
  decide +kernel

theorem k2413_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2413) 3).1 2).2 1).1
      251632349302657409348356842078478549211199203857323985154931589406361295424220666551475).isSome = true := by
  decide +kernel

theorem k2413_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2413) 3).1 2).2 1).2
      297282534714363263033078824291158381344015501858738385630869478160598197716774542713213644496936546898082876).isSome = true := by
  decide +kernel

theorem k2413_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2413) 3).2 2).1 1).1
      1157228131712039401441594843790743137024867226723335052964993916409608013075802847987169704151799792759756).isSome = true := by
  decide +kernel

theorem k2413_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2413) 3).2 2).1 1).2
      1156986921638150985124910314522926415597346250669474607163865730204236180086398006864036360847807322354636).isSome = true := by
  decide +kernel

theorem k2413_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2413) 3).2 2).2 3).1
      62810915270169738624132092915580845125598024554976970205395642484856310023009185503025).isSome = true := by
  decide +kernel

theorem k2413_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2413) 3).2 2).2 3).2
      62735390053640500750413332613773241783260927171592839470059717577511566571674074453809).isSome = true := by
  decide +kernel

theorem k2414_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2414) 3).1 2).1 1).1
      15652624994302287713362579256054323499227633640861361981272645863243233624264762412748).isSome = true := by
  decide +kernel

theorem k2414_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 2414) 3).1 2).1 1).2
      13254633239519359360389276548260753682322752046901586357751598028).isSome = true := by
  decide +kernel

theorem k2414_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2414) 3).1 2).2
      349267070361935346937479920733490006633878896159802729391205890465934887926990357681497270499526130140211126598635471698358914865).isSome = true := by
  decide +kernel

theorem k2414_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2414) 3).2 2).1
      25720386811594721401794370439974674526869977915843426097854024121234771748621703470745935018558451056965533950449368714649480900839156474012587478833).isSome = true := by
  decide +kernel

theorem k2414_4 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2414) 3).2 2).2
      21793997869333989148820959045541126893895023236403057324270985640066547837861716462673944482407975942142149707247734600363268913).isSome = true := by
  decide +kernel

theorem k2415_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2415) 2).1 3).1
      401440807693830835234901194800775395049894606370838903822189770213618602240425541040505114658103703493267957838678585688164391411938900629244935228).isSome = true := by
  decide +kernel

theorem k2415_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2415) 2).1 3).2
      15597611904932283133438379866210964471896272523849608911599309441447974959334295918385).isSome = true := by
  decide +kernel

theorem k2415_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2415) 2).2 3).1
      21767141946078810359981693994597237025345380330045514733648662065174223372518145764058481238745561587358497598468712375657028401).isSome = true := by
  decide +kernel

theorem k2415_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2415) 2).2 3).2
      1359312687020575723849843356670839571647245016417661224059861897311661310337855655404698701691811085946995881900659816807127857).isSome = true := by
  decide +kernel

theorem k2416_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2416) 2).1 3).1
      3897246107940278210146960689303190886802584171476308853305320007387781212566342464060).isSome = true := by
  decide +kernel

theorem k2416_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2416) 2).1 3).2
      15578801878071138014078339485633983673971481632674462095414694987497658604932960786225).isSome = true := by
  decide +kernel

theorem k2416_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2416) 2).2 3).1
      974672589788396100857250765771671086537879533528926810767901090424942773952386530364).isSome = true := by
  decide +kernel

theorem k2416_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2416) 2).2 3).2
      974027680319622749739034051428649065055153377435763827266567275453608536216870681660).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 2413 2417 :=
  (Cover.one (box := dirCellBox) (n := 2413)
      (.split 3 (.split 2 (.split 1 (.leaf _ k2413_0) (.leaf _ k2413_1)) (.split 1 (.leaf _ k2413_2) (.leaf _ k2413_3))) (.split 2 (.split 1 (.leaf _ k2413_4) (.leaf _ k2413_5)) (.split 3 (.leaf _ k2413_6) (.leaf _ k2413_7))))).trans <|
  (Cover.one (box := dirCellBox) (n := 2414)
      (.split 3 (.split 2 (.split 1 (.leaf _ k2414_0) (.leaf _ k2414_1)) (.leaf _ k2414_2)) (.split 2 (.leaf _ k2414_3) (.leaf _ k2414_4)))).trans <|
  (Cover.one (box := dirCellBox) (n := 2415)
      (.split 2 (.split 3 (.leaf _ k2415_0) (.leaf _ k2415_1)) (.split 3 (.leaf _ k2415_2) (.leaf _ k2415_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 2416)
      (.split 2 (.split 3 (.leaf _ k2416_0) (.leaf _ k2416_1)) (.split 3 (.leaf _ k2416_2) (.leaf _ k2416_3))))

end C4.Cert.Dir044
