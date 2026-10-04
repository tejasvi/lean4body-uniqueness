module

public import C4Check

public section

/-! Cells `2580 ≤ n < 2613` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir052

theorem c0 : allCells dirCell 2580 2581 [
    15847031104793197375642149390042523281706900572984200347493292724512072859407639594503] = true := by
  decide +kernel

theorem k2581_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2581) 3).1
      468212933500385722600093881592938962745792049546768486809268277926011090774859391182866303211106278993622292651516558898652794230798751585336719513485996739201799622).isSome = true := by
  decide +kernel

theorem k2581_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2581) 3).2 2).1
      72659475726506760766509645649753642451054123526667953208341847154278716743157253376974582270603807938364).isSome = true := by
  decide +kernel

theorem k2581_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2581) 3).2 2).2
      61537878085695211157171695961478298906493782062232361675823022449940861479400363836).isSome = true := by
  decide +kernel

theorem k2582_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2582) 3).1 2).1
      3928183825545217735006424889786558970939670321007903211490820949661891928918989460284).isSome = true := by
  decide +kernel

theorem k2582_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2582) 3).1 2).2
      3929857801022711896734279462279151360474148891464980887703532722998048588437384581948).isSome = true := by
  decide +kernel

theorem k2582_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2582) 3).2 2).1
      251052795075491114390570732857246640283108270848186753481885284243600563482713466546748).isSome = true := by
  decide +kernel

theorem k2582_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2582) 3).2 2).2
      212643620515290429629528501177369699805934222585714779853514328636).isSome = true := by
  decide +kernel

theorem k2583_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2583) 3).1 2).1
      18496736309672505183258396766224794523747667240867117574920325257234999388277930423509874021007137641055036).isSome = true := by
  decide +kernel

theorem k2583_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2583) 3).1 2).2
      13588560580667709888600877324635582604457737211145304878186643833660).isSome = true := by
  decide +kernel

theorem k2583_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2583) 3).2 2).1
      4005454503499768670318875495075772470311850071299497779643399439147364801299319478010684).isSome = true := by
  decide +kernel

theorem k2583_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2583) 3).2 2).2
      15647004880595300622971831673935392114672694852516062400395966681318400160033910144060).isSome = true := by
  decide +kernel

theorem k2584_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2584) 3).1 2).1
      250075428556215012776981376457733264157715957863723516178238021807251366107976436661308).isSome = true := by
  decide +kernel

theorem k2584_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2584) 3).1 2).2
      54224321984387361075583723871806639087100286200386079843570305645628).isSome = true := by
  decide +kernel

theorem k2584_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2584) 3).2 2).1
      867197572283957037081407946165030214855957121218127511869189565234236).isSome = true := by
  decide +kernel

theorem k2584_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2584) 3).2 2).2
      13543894651786324218752549172008813645962687121455075654677466758204).isSome = true := by
  decide +kernel

theorem k2585_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2585) 2).1 3).1
      216510732864508041115995587253867404527167811720237482338176681589820).isSome = true := by
  decide +kernel

theorem k2585_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2585) 2).1 3).2
      54091732597331127279218820047394759374004978272215095011128816909372).isSome = true := by
  decide +kernel

theorem k2585_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2585) 2).2 1).1
      216430703131710816030445376174708143990091113963655243610616324897852).isSome = true := by
  decide +kernel

theorem k2585_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2585) 2).2 1).2
      216559154326881464669048149527194997427314732161709102331801014844476).isSome = true := by
  decide +kernel

theorem k2586_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2586) 3).1 1).1
      216228084414121675954609616801883363032983497478201408430515671481404).isSome = true := by
  decide +kernel

theorem k2586_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2586) 3).1 1).2
      54063271590354595416935698781424620411377706557184854277114740030524).isSome = true := by
  decide +kernel

theorem k2586_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2586) 3).2 2).1
      13514706976120773322142153187722688496516338361761846798554211171388).isSome = true := by
  decide +kernel

theorem k2586_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2586) 3).2 2).2
      13509112170238619077139811844260884446452881782719671766406370475068).isSome = true := by
  decide +kernel

theorem k2587_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2587) 1).1
      261058885831819697121429300973358490597376518361870222604327890163217923270659210884775473395).isSome = true := by
  decide +kernel

theorem k2587_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 2587) 1).2
      4177509364632235527414956733914074531655724670621539774957602457141446514441467494895478960371).isSome = true := by
  decide +kernel

theorem k2588_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2588) 3).1
      255020901485664348941893062017690187064623500353237386282496642962872933182791509293510897).isSome = true := by
  decide +kernel

theorem k2588_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 2588) 3).2
      995410485466191200968746167522192497082468442987204960193692825666707011433753633381553).isSome = true := by
  decide +kernel

theorem k2589_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2589) 1).1
      242916032031863782963938748730129119944786950364833079863442708809120746081755723324).isSome = true := by
  decide +kernel

theorem k2589_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 2589) 1).2
      15548412157489810305338910323270600289415761999299847727994468460896606220928528403004).isSome = true := by
  decide +kernel

theorem c10 : allCells dirCell 2590 2609 [
    17918117639988322628687808452881062818991833210299643588211256431190230951414829659003095527727199132017,
    147535623167559666820, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 38505763857393403020307] = true := by
  decide +kernel

theorem k2609_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2609) 3).1
      15418789246463707727164452777962787583645688885119015331019621550904104185718440306).isSome = true := by
  decide +kernel

theorem k2609_1 : (checkBoxH dirMode depth (splitBox (dirCellBox 2609) 3).2
      342982285173560574671215795241029496642988152732477300287623401676732421854332257399223511270467432945173742210903808883651826).isSome = true := by
  decide +kernel

theorem k2610_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 2610) 3).1
      5473817113592060857396975208582478862846872134992006327326956525500656935760004575613791874048506534713579653338531961874369778).isSome = true := by
  decide +kernel

theorem k2610_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2610) 3).2 2).1
      212636706778137129596974600849504597508641109001361554157403097660).isSome = true := by
  decide +kernel

theorem k2610_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2610) 3).2 2).2
      53156062540997408332014302059993494330135675147526261321299784252).isSome = true := by
  decide +kernel

theorem k2611_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2611) 2).1 3).1
      53081540764667838497490841977517514971945521623841336282304606780).isSome = true := by
  decide +kernel

theorem k2611_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2611) 2).1 3).2
      53014653292648363235108616985946519551586404623556192041936731196).isSome = true := by
  decide +kernel

theorem k2611_2 : (checkBoxH dirMode depth (splitBox (dirCellBox 2611) 2).2
      1395805393416590447370558481665635167067709450157402003941499009624975796344221014296926274362490603904617174939111774041200259315).isSome = true := by
  decide +kernel

theorem k2612_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2612) 2).1 3).1
      3389160458049384958680230217416323576691676908764582169451310136380).isSome = true := by
  decide +kernel

theorem k2612_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2612) 2).1 3).2
      216712715234655090172889848887508104206806907942759238168960289946684).isSome = true := by
  decide +kernel

theorem k2612_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2612) 2).2 1).1
      13549920951923981537649939348402323508068657543786463844502997515324).isSome = true := by
  decide +kernel

theorem k2612_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 2612) 2).2 1).2
      54203317797650689897863405143378239922737444869676844130167510219836).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 2580 2613 :=
  (Cover.dir c0).trans <|
  (Cover.one (box := dirCellBox) (n := 2581)
      (.split 3 (.leaf _ k2581_0) (.split 2 (.leaf _ k2581_1) (.leaf _ k2581_2)))).trans <|
  (Cover.one (box := dirCellBox) (n := 2582)
      (.split 3 (.split 2 (.leaf _ k2582_0) (.leaf _ k2582_1)) (.split 2 (.leaf _ k2582_2) (.leaf _ k2582_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 2583)
      (.split 3 (.split 2 (.leaf _ k2583_0) (.leaf _ k2583_1)) (.split 2 (.leaf _ k2583_2) (.leaf _ k2583_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 2584)
      (.split 3 (.split 2 (.leaf _ k2584_0) (.leaf _ k2584_1)) (.split 2 (.leaf _ k2584_2) (.leaf _ k2584_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 2585)
      (.split 2 (.split 3 (.leaf _ k2585_0) (.leaf _ k2585_1)) (.split 1 (.leaf _ k2585_2) (.leaf _ k2585_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 2586)
      (.split 3 (.split 1 (.leaf _ k2586_0) (.leaf _ k2586_1)) (.split 2 (.leaf _ k2586_2) (.leaf _ k2586_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 2587)
      (.split 1 (.leaf _ k2587_0) (.leaf _ k2587_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 2588)
      (.split 3 (.leaf _ k2588_0) (.leaf _ k2588_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 2589)
      (.split 1 (.leaf _ k2589_0) (.leaf _ k2589_1))).trans <|
  (Cover.dir c10).trans <|
  (Cover.one (box := dirCellBox) (n := 2609)
      (.split 3 (.leaf _ k2609_0) (.leaf _ k2609_1))).trans <|
  (Cover.one (box := dirCellBox) (n := 2610)
      (.split 3 (.leaf _ k2610_0) (.split 2 (.leaf _ k2610_1) (.leaf _ k2610_2)))).trans <|
  (Cover.one (box := dirCellBox) (n := 2611)
      (.split 2 (.split 3 (.leaf _ k2611_0) (.leaf _ k2611_1)) (.leaf _ k2611_2))).trans <|
  (Cover.one (box := dirCellBox) (n := 2612)
      (.split 2 (.split 3 (.leaf _ k2612_0) (.leaf _ k2612_1)) (.split 1 (.leaf _ k2612_2) (.leaf _ k2612_3))))

end C4.Cert.Dir052
