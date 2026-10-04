module

public import C4Check

public section

/-! Cells `1966 ≤ n < 1993` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir021

theorem k1966_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1966) 2).1 2).1
      114544296920817932442296782330008739106462414279).isSome = true := by
  decide +kernel

theorem k1966_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1966) 2).1 2).2
      29612931025123038273109891804315770698217609533341447310641938884888370317170539412089007114664713190452077780651135604101929490744145033425849715747971030597560276759).isSome = true := by
  decide +kernel

theorem k1966_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1966) 2).2 3).1 2).1
      73861435083774966966481808988994169743596157713435693420996640247570309106745192131934884038619000362857677).isSome = true := by
  decide +kernel

theorem k1966_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1966) 2).2 3).1 2).2
      4094657104895144763197565077648505089943693943186653343782015215026430079859023816924416909).isSome = true := by
  decide +kernel

theorem k1966_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1966) 2).2 3).2 2).1
      243919354085619105275184380904793245463731249566353708909583301480908466466065088909).isSome = true := by
  decide +kernel

theorem k1966_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1966) 2).2 3).2 2).2
      998875922217874329451347186982703475483900215041764554355849298616141135514974010488013).isSome = true := by
  decide +kernel

theorem k1967_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 1967) 2).1
      272652038).isSome = true := by
  decide +kernel

theorem k1967_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1967) 2).2 2).1
      729224683101776309660888509889486028691300277969450366486165492130962950809727133127).isSome = true := by
  decide +kernel

theorem k1967_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1967) 2).2 2).2
      25049912341436823615736098266540341955757044244966101434202637703819733086516987485717245363724053437451675976804083546094500504295032191615522503).isSome = true := by
  decide +kernel

theorem c2 : allCells dirCell 1968 1991 [
    8040104673560088506718166275453147389214879389190, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 3] = true := by
  decide +kernel

theorem k1991_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 1991) 3).1
      1301413736731645774251965420112677341679717455345232005988927241939357755157137009037094067159528328952511041212838286).isSome = true := by
  decide +kernel

theorem k1991_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1991) 3).2 2).1 3).1
      1418969760962489701237990639608816002766684148120781791166847491022678424310069128830147737941556053558938443893194137590004859334).isSome = true := by
  decide +kernel

theorem k1991_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 1991) 3).2 2).1 3).2 2).1
      63302577802063484529294423188243743613742801468093934482644677769434187226791018038417).isSome = true := by
  decide +kernel

theorem k1991_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 1991) 3).2 2).1 3).2 2).2
      15847164280060872113248739242052464797847436180699925613104259719853949035636663801617).isSome = true := by
  decide +kernel

theorem k1991_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1991) 3).2 2).2 3).1
      18847273227523584401592986457696266996117195191637442286626306713050366361304215193216619420990969942242374).isSome = true := by
  decide +kernel

theorem k1991_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1991) 3).2 2).2 3).2
      26173323952980113461845766844460193090503213954806176214560764348757785549226713713409561467817208246272560221057521685581065906970547870838078790854).isSome = true := by
  decide +kernel

theorem k1992_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 1992) 3).1 2).1 3).1 2).1
      22015863386779887407072342335688526684688950496066983171971337969414656545787571840464550983640864846646780354052615508280940293).isSome = true := by
  decide +kernel

theorem k1992_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 1992) 3).1 2).1 3).1 2).2
      74622171446644768181629613792446805038316639060674303835967319292112401638142286023771173136096770293060869).isSome = true := by
  decide +kernel

theorem k1992_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 1992) 3).1 2).1 3).2 2).1
      103742529221218212557456501545804999932696725563008098038905955344309493226116512909497730508385691323027694929670657239040974609410700630453894566725).isSome = true := by
  decide +kernel

theorem k1992_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 1992) 3).1 2).1 3).2 2).2
      6490343574595188971666232226270470227771806418580707091630860854711538995101853316625543510486865499762192111224431480906498184001937764885224494661).isSome = true := by
  decide +kernel

theorem k1992_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 1992) 3).1 2).2 3).1 2).1
      74707655561769569699081946751094949839848137257166374054473127963484237422360351696525163804465931233978629).isSome = true := by
  decide +kernel

theorem k1992_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 1992) 3).1 2).2 3).1 2).2
      18697346033301656997929283879880556717958629890821214974788496201590881874031732280471992612001502081363205).isSome = true := by
  decide +kernel

theorem k1992_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 1992) 3).1 2).2 3).2 2).1
      6496797435810508708772731170888676886912760167674409986010215328610931556457693058035321008627972429963981447156241523920498839109222180659480629317).isSome = true := by
  decide +kernel

theorem k1992_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 1992) 3).1 2).2 3).2 2).2
      6503063758585163409652929056958944743902508903268604773667594836500178571466376165422937669730217186048237251354582242510624467978696017074598849605).isSome = true := by
  decide +kernel

theorem k1992_8 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 1992) 3).2 2).1 3).1 1).1
      1867237277700455345449182279122145288962732364018587021858764659422872174013659186470769315073063484150399352453937033623284919802354237680966446903173212068660233678).isSome = true := by
  decide +kernel

theorem k1992_9 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 1992) 3).2 2).1 3).1 1).2 2).1
      245872793657797737634653283270637030141797859199991450845068485864561718883819936716).isSome = true := by
  decide +kernel

theorem k1992_10 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 1992) 3).2 2).1 3).1 1).2 2).2
      3936716079593209704976152771925281436449795325970642892133656514389688801843949213489).isSome = true := by
  decide +kernel

theorem k1992_11 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 1992) 3).2 2).1 3).2 1).1
      6469361270398750541981005389584186918623112241479522768990981365166015537231963161570204595359726286084149582451197020321428646847151564493488133582).isSome = true := by
  decide +kernel

theorem k1992_12 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 1992) 3).2 2).1 3).2 1).2
      6474963469577752767504584098139046530187141394842220567450913282406169440620243494897662620682177693805657779549746525355434096234360069961742626610).isSome = true := by
  decide +kernel

theorem k1992_13 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 1992) 3).2 2).2 3).1 1).1
      6352749515750383210943534166639164299294685197006775698458834104084531647381953987978248469684056852022889567051768962925762714911613403345237454).isSome = true := by
  decide +kernel

theorem k1992_14 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 1992) 3).2 2).2 3).1 1).2 2).1
      246529840603243402906354542124891267413674290359365373004076654118863337210890379052).isSome = true := by
  decide +kernel

theorem k1992_15 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 1992) 3).2 2).2 3).1 1).2 2).2
      985994271225018668561437959841915441732688823401099494605021083797224390090110631084).isSome = true := by
  decide +kernel

theorem k1992_16 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 1992) 3).2 2).2 3).2 1).1 2).1
      61477153473970331902348373614605387475182557350827516066727823378075383811058054513).isSome = true := by
  decide +kernel

theorem k1992_17 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 1992) 3).2 2).2 3).2 1).1 2).2
      15382464934393398237923144483661268801772906888284947889052860797372466084943585132).isSome = true := by
  decide +kernel

theorem k1992_18 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 1992) 3).2 2).2 3).2 1).2 2).1
      61468357685243549440933952853249892252198471494859823115658631110546434072644016076).isSome = true := by
  decide +kernel

theorem k1992_19 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 1992) 3).2 2).2 3).2 1).2 2).2
      246050648724582580307913733347310627953599890196205294233974785877908119284560125740).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 1966 1993 :=
  (Cover.one (box := dirCellBox) (n := 1966)
      (.split 2 (.split 2 (.leaf _ k1966_0) (.leaf _ k1966_1)) (.split 3 (.split 2 (.leaf _ k1966_2) (.leaf _ k1966_3)) (.split 2 (.leaf _ k1966_4) (.leaf _ k1966_5))))).trans <|
  (Cover.one (box := dirCellBox) (n := 1967)
      (.split 2 (.leaf _ k1967_0) (.split 2 (.leaf _ k1967_1) (.leaf _ k1967_2)))).trans <|
  (Cover.dir c2).trans <|
  (Cover.one (box := dirCellBox) (n := 1991)
      (.split 3 (.leaf _ k1991_0) (.split 2 (.split 3 (.leaf _ k1991_1) (.split 2 (.leaf _ k1991_2) (.leaf _ k1991_3))) (.split 3 (.leaf _ k1991_4) (.leaf _ k1991_5))))).trans <|
  (Cover.one (box := dirCellBox) (n := 1992)
      (.split 3 (.split 2 (.split 3 (.split 2 (.leaf _ k1992_0) (.leaf _ k1992_1)) (.split 2 (.leaf _ k1992_2) (.leaf _ k1992_3))) (.split 3 (.split 2 (.leaf _ k1992_4) (.leaf _ k1992_5)) (.split 2 (.leaf _ k1992_6) (.leaf _ k1992_7)))) (.split 2 (.split 3 (.split 1 (.leaf _ k1992_8) (.split 2 (.leaf _ k1992_9) (.leaf _ k1992_10))) (.split 1 (.leaf _ k1992_11) (.leaf _ k1992_12))) (.split 3 (.split 1 (.leaf _ k1992_13) (.split 2 (.leaf _ k1992_14) (.leaf _ k1992_15))) (.split 1 (.split 2 (.leaf _ k1992_16) (.leaf _ k1992_17)) (.split 2 (.leaf _ k1992_18) (.leaf _ k1992_19)))))))

end C4.Cert.Dir021
