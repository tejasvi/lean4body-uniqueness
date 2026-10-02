module

public import C4Check

public section

/-! Cells `1964 ≤ n < 1967` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir022

theorem k1964_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1964) 2).1 3).1 2).1
      342216738229613223887784955328916925187909078690935756977148108345239764698178973452303389470378357310938155454790915706148935).isSome = true := by
  decide +kernel

theorem k1964_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1964) 2).1 3).1 2).2
      1159768021067600441977074114705100533716558243849633256052644734937612171494888672311305026034829253384007).isSome = true := by
  decide +kernel

theorem k1964_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1964) 2).1 3).2 2).1
      1184515990168685045823838372146035941699512907591073668486385656024980295349407338240712058447188496538854855).isSome = true := by
  decide +kernel

theorem k1964_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1964) 2).1 3).2 2).2
      1612730810875325483800050725309138192322451749156788498110189969805833259390425582124208607694836804495679943860341911871673955423129627261555385799).isSome = true := by
  decide +kernel

theorem k1964_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1964) 2).2 3).1 3).1
      21490654714770347288797194624582011841861274257064141293671620474839622126757576763295391940211776003519789169235165093361478).isSome = true := by
  decide +kernel

theorem k1964_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1964) 2).2 3).1 3).2
      4651438250944411683402125601662457037429745682000832203367034439131184418681335539737933027692933288573766).isSome = true := by
  decide +kernel

theorem k1964_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1964) 2).2 3).2 3).1
      18555084392352186900600144318970594061550133022040114896662705336899550015674771460982290969952129561560901).isSome = true := by
  decide +kernel

theorem k1964_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1964) 2).2 3).2 3).2
      87498839890198900420768408635821294711300277047969181971852165423034209768024091247809856724320351860403711964694673496279975373).isSome = true := by
  decide +kernel

theorem k1965_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1965) 2).1 3).1 2).1
      1363704041220682509829811947165465453453077434314340850485114779614218582811838351836211183979847489686293970220213052971848397).isSome = true := by
  decide +kernel

theorem k1965_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1965) 2).1 3).1 2).2
      16029291298162333558039690923077469208556113400174174808007212402714553007128147372274893).isSome = true := by
  decide +kernel

theorem k1965_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1965) 2).1 3).2 2).1
      61095143978166379669711490272115077697020787126607016567404654329395974208378563397).isSome = true := by
  decide +kernel

theorem k1965_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1965) 2).1 3).2 2).2
      1153961342446126605085155114462458764981513823091609242739284463863036407256982883231418298253902031217869).isSome = true := by
  decide +kernel

theorem k1965_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1965) 2).2 3).1 2).1
      16033269521623290279066297429552678695856359894901977323143668752811779805317469911487693).isSome = true := by
  decide +kernel

theorem k1965_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1965) 2).2 3).1 2).2
      1184222410824215511772005553818049973661487925252684197782716069371052042101052899744506194876650161381450957).isSome = true := by
  decide +kernel

theorem k1965_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1965) 2).2 3).2 2).1
      250159764215599462774122861185171748022825597406127093664887084482319212687722681358129).isSome = true := by
  decide +kernel

theorem k1965_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1965) 2).2 3).2 2).2
      3911649013680965941743476501263517306925977469657597833491636799028271281101728749361).isSome = true := by
  decide +kernel

theorem k1966_0 : (checkBoxH dirMode depth (splitBox (dirCellBox 1966) 2).1
      30323641369705396798684131705967263345865690872958851771296520764614501052088250317043098190892182132528723491325544610461317438218773465619449139872380190394098861453598).isSome = true := by
  decide +kernel

theorem k1966_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1966) 2).2 3).1 2).1
      15260729574343644972316883945556937582665482423869646138349455526245805468778945905).isSome = true := by
  decide +kernel

theorem k1966_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (dirCellBox 1966) 2).2 3).1 2).2
      15622965111068523008555612015511964064991997333549388497391475767249111911573407553331).isSome = true := by
  decide +kernel

theorem k1966_3 : (checkBoxH dirMode depth (splitBox (splitBox (dirCellBox 1966) 2).2 3).2
      1851368216695472848325693899800680915503132434722966132095666337445108535189840808549180988647850690540944304424869573735666551554995767242746737502395489590204417478).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 1964 1967 :=
  (Cover.one (box := dirCellBox) (n := 1964)
      (.split 2 (.split 3 (.split 2 (.leaf _ k1964_0) (.leaf _ k1964_1)) (.split 2 (.leaf _ k1964_2) (.leaf _ k1964_3))) (.split 3 (.split 3 (.leaf _ k1964_4) (.leaf _ k1964_5)) (.split 3 (.leaf _ k1964_6) (.leaf _ k1964_7))))).trans <|
  (Cover.one (box := dirCellBox) (n := 1965)
      (.split 2 (.split 3 (.split 2 (.leaf _ k1965_0) (.leaf _ k1965_1)) (.split 2 (.leaf _ k1965_2) (.leaf _ k1965_3))) (.split 3 (.split 2 (.leaf _ k1965_4) (.leaf _ k1965_5)) (.split 2 (.leaf _ k1965_6) (.leaf _ k1965_7))))).trans <|
  (Cover.one (box := dirCellBox) (n := 1966)
      (.split 2 (.leaf _ k1966_0) (.split 3 (.split 2 (.leaf _ k1966_1) (.leaf _ k1966_2)) (.leaf _ k1966_3))))

end C4.Cert.Dir022
