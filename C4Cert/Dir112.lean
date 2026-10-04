module

public import C4Check

public section

/-! Cells `3588 ≤ n < 3590` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir112

theorem k3588_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3588) 2).1 3).1 2).1 3).1 1).1
      3955653184672997345972057060057887182859104886313044038302164200970485142180121243436).isSome = true := by
  decide +kernel

theorem k3588_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 3588) 2).1 3).1 2).1 3).1 1).2
      3348938662112206752425184528001233015229553723723687630626774828).isSome = true := by
  decide +kernel

theorem k3588_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3588) 2).1 3).1 2).1 3).2
      87952634760822693801877601726860311192543020007832273108549608237622059882260939493412775271527072941542278158002021317954075825).isSome = true := by
  decide +kernel

theorem k3588_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3588) 2).1 3).1 2).2 3).1
      353061635720371860223496045890173467091010150169152960084058709934059681338034524834752426461148925583873934106308367573542366385).isSome = true := by
  decide +kernel

theorem k3588_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3588) 2).1 3).1 2).2 3).2
      352151248193613263832772501841370631938945677877436264802351533669790533034757211227951343542094061180514781682127329612540525745).isSome = true := by
  decide +kernel

theorem k3588_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3588) 2).1 3).2 2).1 3).1
      76129399679599685043763807561917301090341432761347475903692801765324219641793982776570273260445589190583120561).isSome = true := by
  decide +kernel

theorem k3588_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3588) 2).1 3).2 2).1 3).2
      1369281330285046684726310666698765922783507214917193337025930504592472638453048882464175214047387680068066208367083308968410545).isSome = true := by
  decide +kernel

theorem k3588_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3588) 2).1 3).2 2).2 3).1
      87847172891839933830644718736982914366024319054970612573925717100331383157210572475180042211780967299797735835253441330536873137).isSome = true := by
  decide +kernel

theorem k3588_8 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3588) 2).1 3).2 2).2 3).2
      257669557998524861406143686702295911671299444403771918775802911443161950110569420265222833).isSome = true := by
  decide +kernel

theorem k3588_9 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3588) 2).2 3).1 2).1 3).1
      4788798022171959924715163174258171085146277879387884846179252672208173390755994284284336366493304281116539697).isSome = true := by
  decide +kernel

theorem k3588_10 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3588) 2).2 3).1 2).1 3).2
      76430479151476785743191987088729600506621615099413358709650487464755165052145482787600357891668648274133446897).isSome = true := by
  decide +kernel

theorem k3588_11 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3588) 2).2 3).1 2).2 3).1
      4059906509729690874031508273779215616574324475164744859991992929470519170074464848603953).isSome = true := by
  decide +kernel

theorem k3588_12 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3588) 2).2 3).1 2).2 3).2
      4048974665659047430554374039299154590025276384204364671644146198958924509428535068617521).isSome = true := by
  decide +kernel

theorem k3588_13 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3588) 2).2 3).2 2).1 3).1
      87920431926143069457717061166226944703184291484311252098619345608245954952782654065152725011562881928199452553902291690890820785).isSome = true := by
  decide +kernel

theorem k3588_14 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3588) 2).2 3).2 2).1 3).2
      21938260514090427184089860725917692979309937739771505049483054854395987814434802688904993936373885514726490485365037874173017265).isSome = true := by
  decide +kernel

theorem k3588_15 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3588) 2).2 3).2 2).2 3).1
      16158759948865490248228177264395097063826516388755856051972899196216452656056266724552497).isSome = true := by
  decide +kernel

theorem k3588_16 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3588) 2).2 3).2 2).2 3).2
      4759951885937816694912834917456152860275409425285383721627987087366906456945184947871191985721313222992457969).isSome = true := by
  decide +kernel

theorem k3589_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3589) 2).1 3).1 2).1 3).1
      85456611361292936843094529975745795366578091024959244446467906325113874599471944944947877379943960410982158467449012603943345).isSome = true := by
  decide +kernel

theorem k3589_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3589) 2).1 3).1 2).1 3).2
      4626989841617215138516997761714162788890868017242164717619518822312030521552603299347457848834393476210097).isSome = true := by
  decide +kernel

theorem k3589_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3589) 2).1 3).1 2).2 3).1
      4019922406377051715414176438169041707534087660772294467831775532473309609704266956923569).isSome = true := by
  decide +kernel

theorem k3589_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3589) 2).1 3).1 2).2 3).2
      85402783610831538668444874034992942563249395936258635180731534453202450677353865917062295576041356611668278275050057664657841).isSome = true := by
  decide +kernel

theorem k3589_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3589) 2).1 3).2 2).1 3).1
      250614342191449075607968278229674796199228034066162606346044993622488941679500593016380).isSome = true := by
  decide +kernel

theorem k3589_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3589) 2).1 3).2 2).1 3).2
      977947905178594134294701661432406855805228418834691969063642147697911281655051737521).isSome = true := by
  decide +kernel

theorem k3589_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3589) 2).1 3).2 2).2 3).1
      4625346765631501959069107080411815893892090923194764030053074318772500094456046531759101852571569934555708).isSome = true := by
  decide +kernel

theorem k3589_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3589) 2).1 3).2 2).2 3).2
      3913500943538248887178910774384963072139241059244548608200283007246442574953821772209).isSome = true := by
  decide +kernel

theorem k3589_8 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3589) 2).2 3).1 2).1 3).1
      16090367316140363998760369752321535946469835280302631706810892101397210415182097976753329).isSome = true := by
  decide +kernel

theorem k3589_9 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3589) 2).2 3).1 2).1 3).2
      4017078837978491425560344501073400741815511895234399998041934577118304067439512094368433).isSome = true := by
  decide +kernel

theorem k3589_10 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3589) 2).2 3).1 2).2 3).1
      1189163969065156687384562178439879617309767461068911538855591488426747416969074491825623442223833041865142513).isSome = true := by
  decide +kernel

theorem k3589_11 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3589) 2).2 3).1 2).2 3).2
      4019424046491693867844249443280469625724858022185312940699345407699510529850535309835441).isSome = true := by
  decide +kernel

theorem k3589_12 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3589) 2).2 3).2 2).1 1).1
      4010278101790495224457572987565568490617366215042414863409863345151680190540195844973235).isSome = true := by
  decide +kernel

theorem k3589_13 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3589) 2).2 3).2 2).1 1).2
      244817854451524653063770061275843784354516778315638530791342734222840757067510807980).isSome = true := by
  decide +kernel

theorem k3589_14 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3589) 2).2 3).2 2).2 1).1
      4011202754426525910970869207970337666639062773974219101780119703687367962970521191938227).isSome = true := by
  decide +kernel

theorem k3589_15 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 3589) 2).2 3).2 2).2 1).2
      250639624815596664353736085661821891639668330367403199490751892693032114289614755290291).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 3588 3590 :=
  (Cover.one (box := dirCellBox) (n := 3588)
      (.split 2 (.split 3 (.split 2 (.split 3 (.split 1 (.leaf _ k3588_0) (.leaf _ k3588_1)) (.leaf _ k3588_2)) (.split 3 (.leaf _ k3588_3) (.leaf _ k3588_4))) (.split 2 (.split 3 (.leaf _ k3588_5) (.leaf _ k3588_6)) (.split 3 (.leaf _ k3588_7) (.leaf _ k3588_8)))) (.split 3 (.split 2 (.split 3 (.leaf _ k3588_9) (.leaf _ k3588_10)) (.split 3 (.leaf _ k3588_11) (.leaf _ k3588_12))) (.split 2 (.split 3 (.leaf _ k3588_13) (.leaf _ k3588_14)) (.split 3 (.leaf _ k3588_15) (.leaf _ k3588_16)))))).trans <|
  (Cover.one (box := dirCellBox) (n := 3589)
      (.split 2 (.split 3 (.split 2 (.split 3 (.leaf _ k3589_0) (.leaf _ k3589_1)) (.split 3 (.leaf _ k3589_2) (.leaf _ k3589_3))) (.split 2 (.split 3 (.leaf _ k3589_4) (.leaf _ k3589_5)) (.split 3 (.leaf _ k3589_6) (.leaf _ k3589_7)))) (.split 3 (.split 2 (.split 3 (.leaf _ k3589_8) (.leaf _ k3589_9)) (.split 3 (.leaf _ k3589_10) (.leaf _ k3589_11))) (.split 2 (.split 1 (.leaf _ k3589_12) (.leaf _ k3589_13)) (.split 1 (.leaf _ k3589_14) (.leaf _ k3589_15))))))

end C4.Cert.Dir112
