module

public import C4Check

public section

/-! Cells `2775 ≤ n < 2776` of the direct grid: `decide +kernel` checks that `checkBoxH` succeeds
on each light cell, and on each piece of a heavy one, with its hint. -/

set_option Elab.async false

namespace C4.Cert.Dir063

theorem k2775_0 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2775) 2).1 3).1 3).1 2).1 1).1
      54293392827223738139680298755572107579916575824863721278684102060).isSome = true := by
  decide +kernel

theorem k2775_1 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (splitBox (dirCellBox 2775) 2).1 3).1 3).1 2).1 1).2
      11758564008318504548406865288053937647100873276).isSome = true := by
  decide +kernel

theorem k2775_2 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2775) 2).1 3).1 3).1 2).2
      19397468339569877078646163336083909500805060911384670590329185134979590673359861904324468545110344099175757041).isSome = true := by
  decide +kernel

theorem k2775_3 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2775) 2).1 3).1 3).2 2).1
      1232337376260737108993414567545060822481520246811869462276733759559232751079019419535408984036716516871483290289).isSome = true := by
  decide +kernel

theorem k2775_4 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2775) 2).1 3).1 3).2 2).2
      1205578384058797289785980282320674995221868006731338549768225930320598582929031852769534799441717503809969585).isSome = true := by
  decide +kernel

theorem k2775_5 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2775) 2).1 3).2 3).1 2).1
      4795074878354545779341097198107946559167088440201542155023750177160511803972103581888046614281573571587633393).isSome = true := by
  decide +kernel

theorem k2775_6 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2775) 2).1 3).2 3).1 2).2
      4165718419086835580264167414123444945286839160928038694993498816215183640986987822672365809).isSome = true := by
  decide +kernel

theorem k2775_7 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2775) 2).1 3).2 3).2 1).1
      4055721390839519904867493894800769815718719975779572655531964108246226833261043776909554).isSome = true := by
  decide +kernel

theorem k2775_8 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2775) 2).1 3).2 3).2 1).2
      1037152727192839413687410493543217752614403966182194020277791652626714402457068715709035068).isSome = true := by
  decide +kernel

theorem k2775_9 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2775) 2).2 3).1 3).1 2).1
      16463487659443526010565979022073164701682740008446322504895724564674116118255459192906993).isSome = true := by
  decide +kernel

theorem k2775_10 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2775) 2).2 3).1 3).1 2).2
      64412658353693887066315485746195370853907588517925235284064642656413073176953110226161).isSome = true := by
  decide +kernel

theorem k2775_11 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2775) 2).2 3).1 3).2 2).1
      4832374255271575041400172356719355801731262574875296321989819347217132744204292616879486047284679488823139761).isSome = true := by
  decide +kernel

theorem k2775_12 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2775) 2).2 3).1 3).2 2).2
      256261513468189658736943730935734500619879810432926591593495719107245411264087678347697).isSome = true := by
  decide +kernel

theorem k2775_13 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2775) 2).2 3).2 3).1 2).1
      260731839357974988347670279094382714030540348027239430416195567410862966492737446555513521).isSome = true := by
  decide +kernel

theorem k2775_14 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2775) 2).2 3).2 3).1 2).2
      255155941021259486398932514650160243936180034973054426443537712604076869430783885431612).isSome = true := by
  decide +kernel

theorem k2775_15 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2775) 2).2 3).2 3).2 2).1
      259834875432339194043309419699808277070846884958843534542689362164159178770383132139548913).isSome = true := by
  decide +kernel

theorem k2775_16 : (checkBoxH dirMode depth (splitBox (splitBox (splitBox (splitBox (dirCellBox 2775) 2).2 3).2 3).2 2).2
      15889901019797390458811285809776260401316894728522583825810517756658052927743084450620).isSome = true := by
  decide +kernel

theorem cover : Cover dirMode dirCellBox 2775 2776 :=
  (Cover.one (box := dirCellBox) (n := 2775)
      (.split 2 (.split 3 (.split 3 (.split 2 (.split 1 (.leaf _ k2775_0) (.leaf _ k2775_1)) (.leaf _ k2775_2)) (.split 2 (.leaf _ k2775_3) (.leaf _ k2775_4))) (.split 3 (.split 2 (.leaf _ k2775_5) (.leaf _ k2775_6)) (.split 1 (.leaf _ k2775_7) (.leaf _ k2775_8)))) (.split 3 (.split 3 (.split 2 (.leaf _ k2775_9) (.leaf _ k2775_10)) (.split 2 (.leaf _ k2775_11) (.leaf _ k2775_12))) (.split 3 (.split 2 (.leaf _ k2775_13) (.leaf _ k2775_14)) (.split 2 (.leaf _ k2775_15) (.leaf _ k2775_16))))))

end C4.Cert.Dir063
