module

public import C4Check

public section

/-! Cells `2443 ≤ n < 2467` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir047

theorem k2443_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2443) 3).1 2).1
      5445963584479507457012402158154397426234107612268077747018376101705490300238315968925647437842572347264031161183207420516416572).isSome = true := by
  decide +kernel

theorem k2443_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2443) 3).1 2).2
      295381061557123925232225265316391571362175960373937317526420869512674707373688201331772074679360234961976380).isSome = true := by
  decide +kernel

theorem k2443_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2443) 3).2 2).1
      5439885686958410951494159336290860832721613375377284611287351814694523594964343673288862130965369049793477890273080872168897596).isSome = true := by
  decide +kernel

theorem k2443_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2443) 3).2 2).2
      294977823567753343505390603511617557317180794232819381478464133587102786933226041230625630754976389074205756).isSome = true := by
  decide +kernel

theorem k2444_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2444) 3).1 2).1
      62387069183016023189493068014032713216448037615443649796000110904958456801280283425852).isSome = true := by
  decide +kernel

theorem k2444_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2444) 3).1 2).2
      294702890116009576037744310898212330541204055446641601046124153309339950483297925833632540944646614446455868).isSome = true := by
  decide +kernel

theorem k2444_2 : (checkBoxH dirMode depth (splitBox (dirCellBox 2444) 3).2
      89008855830418218255086010166519314247719363274108494943141402258033989867502809172702597918543666637092992378880515942097762840818).isSome = true := by
  decide +kernel

theorem k2445_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2445) 3).1
      88954180428344018760944412111687884957311918683206364347546281481729079943550026278765823369428052240867109583984406611821165998322).isSome = true := by
  decide +kernel

theorem k2445_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 2445) 3).2
      102498849864449804523722382174647500923470643564712288280757389113064610226040820067061527532575948034001694181249171096457543344987517735694328028361).isSome = true := by
  decide +kernel

theorem k2446_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2446) 3).1
      21696634863957867571442534927942265730124118430382127901459893718518655918094375582992141565451438472316324966232424885122358065).isSome = true := by
  decide +kernel

theorem k2446_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 2446) 3).2
      18373579218798330215936434534377566974402596511342165162072034056820970653456536967203629477883346081902834).isSome = true := by
  decide +kernel

theorem k2447_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2447) 2).1
      62212318772538471832390668845550336346513829729547367919701170186872344224756698995891).isSome = true := by
  decide +kernel

theorem k2447_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 2447) 2).2
      3888645098701396347379761978228782455513794739253156365295503820736807253470275442483).isSome = true := by
  decide +kernel

theorem k2448_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2448) 2).1
      971890720125997049338900357803577119624967593549946610649376406919343327744759887053).isSome = true := by
  decide +kernel

theorem k2448_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 2448) 2).2
      3887142419528419650950836606127140944692948357753554933285425930029762657700536145715).isSome = true := by
  decide +kernel

theorem c6 : allCells dirCell 2449 2450 [
    24982458370398747705619237082001756605477737190284567937365666385303142424827417929375044769722831682872224685221895293786152921063045301593798130] = true := by
  decide +kernel

theorem c7 : allCells dirCell 2450 2466 [
    71677793239230100369772917210788288423770076507356771705675379053501927646165719002470017191211161333062,
    2360870524377592167745, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] = true := by
  decide +kernel

theorem c8 : allCells dirCell 2466 2467 [
    885028928550228856751069011991194445189869088738145107040039886963] = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 2443 2467 :=
  (Cover.one (box := dirCellBox) (n := 2443)
      (.split 3 (.split 2 (.leaf _ k2443_0) (.leaf _ k2443_1)) (.split 2 (.leaf _ k2443_2) (.leaf _ k2443_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 2444)
      (.split 3 (.split 2 (.leaf _ k2444_0) (.leaf _ k2444_1)) (.leaf _ k2444_2))).trans <|
  (Cover.one (box := dirCellBox) (n := 2445)
      (.split 3 (.leaf _ k2445_0) (.leaf _ k2445_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 2446)
      (.split 3 (.leaf _ k2446_0) (.leaf _ k2446_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 2447)
      (.split 2 (.leaf _ k2447_0) (.leaf _ k2447_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 2448)
      (.split 2 (.leaf _ k2448_0) (.leaf _ k2448_1))).trans <|
  (Cover.dir c6).trans <|
  (Cover.dir c7).trans <|
  (Cover.dir c8)

end C4.Cert.Dir047
