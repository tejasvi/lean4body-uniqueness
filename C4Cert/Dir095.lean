module

public import C4Check

public section

/-! Cells `3254 ≤ n < 3260` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir095

theorem k3254_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3254) 2).1 3).1 1).1 2).1
      3400503413132720952422563886593568180765949392699006642567586692156).isSome = true := by
  decide +kernel

theorem k3254_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3254) 2).1 3).1 1).1 2).2
      3401772986775683734261499208701491226272848495592578532906448501820).isSome = true := by
  decide +kernel

theorem k3254_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3254) 2).1 3).1 1).2 2).1
      849983574533683553309915507075594468451269271921930411807203966012).isSome = true := by
  decide +kernel

theorem k3254_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3254) 2).1 3).1 1).2 2).2
      850291886155166557577449966169685334775537566658317326761494101052).isSome = true := by
  decide +kernel

theorem k3254_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3254) 2).1 3).2 1).1
      89474833811070440833889857526982435945790812021827077378882566954513148790566241210731500214766714999335330040025772056685294042172).isSome = true := by
  decide +kernel

theorem k3254_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3254) 2).1 3).2 1).2
      25787314547895192497111272895823992007062246890149886655431238986252637501424967509966610378795338392848869549513306109879687103145656152161963801660).isSome = true := by
  decide +kernel

theorem k3254_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3254) 2).2 3).1 1).1 2).1
      850711953334310043675861489922507677891653482450178721300977499196).isSome = true := by
  decide +kernel

theorem k3254_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3254) 2).2 3).1 1).1 2).2
      11530743007082562292601599182764771222358256700).isSome = true := by
  decide +kernel

theorem k3254_8 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3254) 2).2 3).1 1).2
      18971673878788619571466869238717852137792988633072104813397093682512792108112872246605591924920413515084823346).isSome = true := by
  decide +kernel

theorem k3254_9 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3254) 2).2 3).2 1).1
      4734666668256526334351159493806145661039527234674758554562174218888231507156206559953285662416731860505508924).isSome = true := by
  decide +kernel

theorem k3254_10 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3254) 2).2 3).2 1).2
      87328268366793594428187062997760040233680945572994276049564093170459994814874121226463182686185753621054340651599644869932137532).isSome = true := by
  decide +kernel

theorem k3255_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3255) 2).1 3).1 1).1
      348678394535180336728571349294903590763529026871794935819612658184292582031408205420437506785556643538815932240731051134022302780).isSome = true := by
  decide +kernel

theorem k3255_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3255) 2).1 3).1 1).2
      262308682072338676930587945096828184486436858795348862850788479880126855752956885991371294962).isSome = true := by
  decide +kernel

theorem k3255_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3255) 2).1 3).2 1).1
      62533351268969760734057764652394040811984128386904861813638008412455536540121506364476).isSome = true := by
  decide +kernel

theorem k3255_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3255) 2).1 3).2 1).2
      999498735453529928833524018495839511024913553182117679442955580194041547995450231484988).isSome = true := by
  decide +kernel

theorem k3255_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3255) 2).2 3).1 1).1
      4727360469986512740145528615659966247303327951984815480938104625858726658357640952344648311444248915232865340).isSome = true := by
  decide +kernel

theorem k3255_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3255) 2).2 3).1 1).2
      18483813870026361591239355147700229820674296239484542035580185832966586005618601498798407695437695249398844).isSome = true := by
  decide +kernel

theorem k3255_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3255) 2).2 3).2 1).1
      62497706758583345017784040925683357269385545455243740265160065131668936468697144212540).isSome = true := by
  decide +kernel

theorem k3255_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3255) 2).2 3).2 1).2
      3390839915444457068086363914128313291648328884243313319535487859772).isSome = true := by
  decide +kernel

theorem k3256_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3256) 2).1 3).1 1).1
      15604054772232315049697476025998255629972396330525588860929167008447450808461924613180).isSome = true := by
  decide +kernel

theorem k3256_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3256) 2).1 3).1 1).2
      998620011057121985517157581646375684746176112992941512080185973823962243814892437500476).isSome = true := by
  decide +kernel

theorem k3256_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3256) 2).1 3).2 1).1
      52830298075712412489329778130042980662083078507237795330112470076).isSome = true := by
  decide +kernel

theorem k3256_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3256) 2).1 3).2 1).2
      52827106708921797451884642676500782366833882609432204120926057020).isSome = true := by
  decide +kernel

theorem k3256_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3256) 2).2 3).1 1).1
      13537505095752754589248422923287065477898371194772338023978694261820).isSome = true := by
  decide +kernel

theorem k3256_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3256) 2).2 3).1 1).2
      54202102625989501204425503124848820338665239548886347585339403203132).isSome = true := by
  decide +kernel

theorem k3256_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3256) 2).2 3).2 1).1
      3381799468750880288330768583757855706042965786679552781302180789308).isSome = true := by
  decide +kernel

theorem k3256_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 3256) 2).2 3).2 1).2
      13527208627679286064998133525703661071807203731009457690229878485564).isSome = true := by
  decide +kernel

theorem k3257_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3257) 2).1 3).1
      5560215183629630233854407036942028710598998150579816283134761118103326739292977698653677582427549539616738063253098727403315130609).isSome = true := by
  decide +kernel

theorem k3257_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3257) 2).1 3).2
      347378415706770922534336118597258627112581695671662001522596502748577244784824496891324948154787225494215497376791666215991888444).isSome = true := by
  decide +kernel

theorem k3257_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3257) 2).2 3).1
      1205969761793057801918323997045887559158069015551275436902262711661306308403550168453264283816076653259186172145).isSome = true := by
  decide +kernel

theorem k3257_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3257) 2).2 3).2
      75335754634366889600030900672121110738154900111882112511709019319351961637366427246110773635609850090736042812).isSome = true := by
  decide +kernel

theorem k3258_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3258) 2).1 3).1
      1177537010643945292553375905049156619611752544473222411367949669290234627589172837907676057288629510332608753).isSome = true := by
  decide +kernel

theorem k3258_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3258) 2).1 3).2
      3891359359357392336185676896476797868558436152231934585283997527513960074259536933436).isSome = true := by
  decide +kernel

theorem k3258_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3258) 2).2 3).1
      75304498331563604030744642936685145290667681721325343909658753054424640433713177063938762552870165014937322300).isSome = true := by
  decide +kernel

theorem k3258_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3258) 2).2 3).2
      4596942700531758619150716099771862516897872006826661873133408057209628668462548506797169709250401166357052).isSome = true := by
  decide +kernel

theorem k3259_0 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3259) 2).1 3).1
      15561257618012650409744958825752466424631929973913722177694034439578141008448173099580).isSome = true := by
  decide +kernel

theorem k3259_1 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3259) 2).1 3).2
      15557740237903141264117763360946873769251637357408491601387753756088315075823113062972).isSome = true := by
  decide +kernel

theorem k3259_2 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3259) 2).2 3).1
      3892656661360221339599083526732904858242898811986239677961563038492467921219556340284).isSome = true := by
  decide +kernel

theorem k3259_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 3259) 2).2 3).2
      3889796622085161261372918697793226227628894101413653353940590881236546874169110164028).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 3254 3260 :=
  (Cover.one (box := dirCellBox) (n := 3254)
      (.split 2 (.split 3 (.split 1 (.split 2 (.leaf _ k3254_0) (.leaf _ k3254_1)) (.split 2 (.leaf _ k3254_2) (.leaf _ k3254_3))) (.split 1 (.leaf _ k3254_4) (.leaf _ k3254_5))) (.split 3 (.split 1 (.split 2 (.leaf _ k3254_6) (.leaf _ k3254_7)) (.leaf _ k3254_8)) (.split 1 (.leaf _ k3254_9) (.leaf _ k3254_10))))).trans <|
  (Cover.one (box := dirCellBox) (n := 3255)
      (.split 2 (.split 3 (.split 1 (.leaf _ k3255_0) (.leaf _ k3255_1)) (.split 1 (.leaf _ k3255_2) (.leaf _ k3255_3))) (.split 3 (.split 1 (.leaf _ k3255_4) (.leaf _ k3255_5)) (.split 1 (.leaf _ k3255_6) (.leaf _ k3255_7))))).trans <|
  (Cover.one (box := dirCellBox) (n := 3256)
      (.split 2 (.split 3 (.split 1 (.leaf _ k3256_0) (.leaf _ k3256_1)) (.split 1 (.leaf _ k3256_2) (.leaf _ k3256_3))) (.split 3 (.split 1 (.leaf _ k3256_4) (.leaf _ k3256_5)) (.split 1 (.leaf _ k3256_6) (.leaf _ k3256_7))))).trans <|
  (Cover.one (box := dirCellBox) (n := 3257)
      (.split 2 (.split 3 (.leaf _ k3257_0) (.leaf _ k3257_1)) (.split 3 (.leaf _ k3257_2) (.leaf _ k3257_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 3258)
      (.split 2 (.split 3 (.leaf _ k3258_0) (.leaf _ k3258_1)) (.split 3 (.leaf _ k3258_2) (.leaf _ k3258_3)))).trans <|
  (Cover.one (box := dirCellBox) (n := 3259)
      (.split 2 (.split 3 (.leaf _ k3259_0) (.leaf _ k3259_1)) (.split 3 (.leaf _ k3259_2) (.leaf _ k3259_3))))

end C4.Cert.Dir095
